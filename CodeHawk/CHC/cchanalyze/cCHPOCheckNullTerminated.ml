(* =============================================================================
   CodeHawk C Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2005-2019 Kestrel Technology LLC
   Copyright (c) 2020-2024 Henny B. Sipma
   Copyright (c) 2024      Aarno Labs LLC

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to deal
   in the Software without restriction, including without limitation the rights
   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
   copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in all
   copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
   SOFTWARE.
   ============================================================================= *)

(* chlib *)
open CHLanguage
open CHNumerical

(* chutil *)
open CHPrettyUtil

(* xprlib *)
open XprTypes
open XprToPretty

(* cchlib *)
open CCHBasicTypes
open CCHTypesToPretty

(* cchpre *)
open CCHMemoryBase
open CCHPreTypes
open CCHProofObligation

(* cchanalyze *)
open CCHAnalysisTypes

let x2p = xpr_formatter#pr_expr
let p2s = pretty_to_string
let x2s x = p2s (x2p x)
let e2s e = p2s (exp_to_pretty e)


class null_terminated_checker_t
        (poq: po_query_int)
        (e: exp)
        (invs: invariant_int list) =
object (self)

  method private memref_to_string (memref: memory_reference_int) =
    "memory base: " ^ (p2s (memory_base_to_pretty memref#get_base))

  (* ----------------------------- safe ------------------------------------- *)

  method private memref_implies_safe
                   (invindex: int)
                   (memref:memory_reference_int):(dependencies_t * string) option =
    match memref#get_base with
    | CStringLiteral _ ->
       let deps = DLocal [invindex] in
       let msg = "value is address of a string literal" in
       Some (deps, msg)
    | CBaseVar v -> self#xpr_implies_safe invindex (XVar v)
    | CStackAddress stackvar when poq#env#is_local_variable stackvar ->
       let (vinfo,offset) = poq#env#get_local_variable stackvar in
       let _ =
         poq#set_diagnostic_arg 1 ("address of stack variable: " ^ vinfo.vname) in
       begin
         match (vinfo.vtype, offset) with
         | (TArray (_, Some (Const (CInt (len64, _, _))), _), NoOffset) ->
            let vinfovalues = poq#get_vinfo_offset_values vinfo in
            let _ = poq#set_vinfo_diagnostic_invariants vinfo in
            List.fold_left (fun acc (inv,offset) ->
                match acc with
                | Some _ -> acc
                | _ ->
                   match offset with
                   | Index (Const (CInt (i64, _, _)), NoOffset) ->
                      let arraylen = mkNumericalFromInt64 len64 in
                      let indexval = mkNumericalFromInt64 i64 in
                      if indexval#lt arraylen then
                        begin
                          match inv#expr with
                          | Some (XConst (IntConst n))
                               when n#equal numerical_zero ->
                             let deps = DLocal [invindex; inv#index] in
                             let msg =
                               Printf.sprintf
                                 "null value was set in array %s at offset: %s"
                                 vinfo.vname
                                 indexval#toString in
                             Some (deps, msg)
                          | Some x ->
                             let argmsg =
                               Printf.sprintf
                                 ("stack array with length %s; value set at index "
                                  ^^ "%s is: %s")
                                 arraylen#toString
                                 indexval#toString
                                 (x2s x) in
                             begin
                               poq#set_diagnostic_arg 1 argmsg;
                               None
                             end
                          | _ ->
                             let argmsg =
                               Printf.sprintf
                                 ("stack array with length: %s and some value at "
                                  ^^ "index %s: %s")
                                 arraylen#toString
                                 indexval#toString
                                 (p2s inv#toPretty) in
                             begin
                               poq#set_diagnostic_arg 1 argmsg;
                               None
                             end
                        end
                      else
                        let argmsg =
                          Printf.sprintf
                            ("stack array with length: %s and value set at index: "
                             ^^ "%s (outside array)")
                            arraylen#toString
                            indexval#toString in
                        begin
                          poq#set_diagnostic_arg 1 argmsg;
                          None
                        end
                   | _ -> None) None vinfovalues
         | _ -> None
       end
    | _ -> None

  method private var_implies_safe (invindex: int) (v: variable_t) =
    let result =
      if poq#env#is_memory_address v then
        let memref = poq#env#get_memory_reference v in
        let _ =
          poq#set_diagnostic_arg
            1 ("memory variable: "  ^ (self#memref_to_string memref)) in
        self#memref_implies_safe invindex memref
      else
        None in
    match result with
    | Some result -> Some result
    | _ ->
       if poq#env#is_function_return_value v then
         let callee = poq#env#get_callvar_callee v in
         begin
           poq#set_diagnostic_arg
             1 ("function return value from: " ^ callee.vname);
           None
         end
       else
         None

  method private xpr_implies_safe
                   (invindex: int) (x: xpr_t): (dependencies_t * string) option =
    match x with
    | XVar v -> self#var_implies_safe invindex v
    | _ -> None

  method private xprlist_implies_safe (invindex: int) (l: xpr_t list) =
    match l with
    | [] -> None
    | h::tl ->
       match self#xpr_implies_safe invindex h with
       | None ->
          let _ =
            poq#set_diagnostic_arg
              1 ("first alternative breaks the chain: " ^ (x2s h)) in
          None
       | Some r ->
          List.fold_left (fun acc x ->
              match acc with
              | None -> None
              | Some (deps, msg) ->
                 begin
                   match self#xpr_implies_safe invindex x with
                   | Some (d, m) ->
                      let deps = join_dependencies deps d in
                      let msg = msg ^ "; " ^ m in
                      Some (deps, msg)
                   | _ ->
                      let _ =
                        poq#set_diagnostic_arg
                          1 ("xpr alternative breaks the chain: " ^ (x2s x)) in
                      None
                 end) (Some r) tl

  method private regions_implies_safe (invindex: int) (symlist: symbol_t list) =
    match symlist with
    | [] -> None
    | _ ->
       let memregmgr = poq#env#get_variable_manager#memregmgr in
       let msgs =
         List.map (fun s ->
             p2s (memregmgr#get_memory_region s#getSeqNumber)#toPretty) symlist in
       begin
         poq#set_diagnostic_arg 1 (String.concat "; " msgs);
         None
       end

  method private inv_implies_safe (inv: invariant_int) =
    let r = None in
    let r =
      match r with
      | Some _ -> r
      | _ ->
         match inv#lower_bound_xpr with
         | Some x -> self#xpr_implies_safe inv#index x
         | _ -> None in
    let r =
      match r with
      | Some _ -> r
      | _ ->
         match inv#get_fact with
         | NonRelationalFact (_, FRegionSet symlist) ->
            self#regions_implies_safe inv#index symlist
         | _ -> None in
    let r =
      match r with
      | Some _ -> r
      | _ ->
         match inv#expr with
         | Some x -> self#xpr_implies_safe inv#index x
         | _ -> None in
    let r =
      match r with
      | Some _ -> r
      | _ ->
         match inv#lower_bound_xpr_alternatives with
         | None | Some [] -> None
         | Some l -> self#xprlist_implies_safe inv#index l in
    r

  method check_safe =
    match invs with
    | [] ->
       begin
         poq#set_diagnostic ("no invariants found for " ^ (e2s e));
         false
       end
    | _ ->
       List.fold_left (fun acc inv ->
           acc ||
             match self#inv_implies_safe inv with
             | Some (deps,msg) ->
                begin
                  poq#record_safe_result deps msg;
                  true
                end
             | _ -> false) false invs

  (* ----------------------- violation -------------------------------------- *)
  method check_violation = false
  (* ----------------------- delegation ------------------------------------- *)
  method check_delegation = false
end


let check_null_terminated (poq: po_query_int) (e: exp) =
  let invs = poq#get_invariants 1 in
  let _ = poq#set_diagnostic_invariants 1 in
  let _ =
    poq#set_key_diagnostic
      "DomainRef:string:null-termination" "ability to track null-terminator" in
  let checker = new null_terminated_checker_t poq e invs in
  checker#check_safe || checker#check_violation || checker#check_delegation
