(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2026  Aarno Labs LLC

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

(* chutil *)
open CHLogger

(* bchlib *)
open BCHLibTypes
open BCHLocation

(* bchlibarm32 *)
open BCHARMAssemblyInstructions
open BCHARMOpcodeRecords
open BCHARMDisassemblyUtils
open BCHARMPredicateTest
open BCHARMTranslationUtil
open BCHARMTypes


module LF = CHOnlineCodeSet.LanguageFactory

let p2s = CHPrettyUtil.pretty_to_string

(* ------------------------------------------------------------------ cmdstate_t
   Data structure and associated functions for the collection of commands inside
   a basic block. The data structure allows for a refinement of the otherwise
   linear sequence of commands, to enable a representation of predicated
   instructions that result in increased precision of analysis results, due to
   the collection of instructions with equal predicate in separate branches,
   rather than having a single branch instruction per predicated instruction
   with intervening joins.
 *)


type setter_key_t = {
    sk_testloc: ctxt_iaddress_t;
    sk_testtestloc: ctxt_iaddress_t option
  }

type fragment_t = {
    fr_key: setter_key_t;
    fr_opencc: arm_opcode_cc_t;    (* the cc that defines "then" *)
    fr_openerloc: location_int; (* location of first instr in fragment *)
    fr_thenbucket: cmd_t list;  (* starts with thentest, grows by append *)
    fr_elsebucket: cmd_t list   (* starts with elsetest *)
  }

type cmdstate_t = {
    cs_flat: cmd_t list;           (* closed-out cmds, in order *)
    cs_open: fragment_t option     (* at most one open fragement *)
  }


let setter_key_to_string (key: setter_key_t) =
  match key.sk_testtestloc with
  | Some a -> "skey:(" ^ key.sk_testloc ^ ", " ^ a ^ ")"
  | _ -> "skey:" ^ key.sk_testloc


let get_setter_key
      (finfo: function_info_int)
      (testloc: location_int)
      (testinstr: arm_assembly_instruction_int): setter_key_t =
  let sk_testtestloc =
    if is_opcode_conditional testinstr#get_opcode then
      match get_associated_test_instr finfo testloc#ci with
      | Some (testtestloc, _) -> Some testtestloc#ci
      | None ->
         let _ =
           log_error_result
             ~tag:"get_setter_key:Unable to get test-test-loc"
             ~msg:testloc#ci
             __FILE__ __LINE__
             [testinstr#toString] in
         None
    else
      None in
  {sk_testloc = testloc#ci; sk_testtestloc}


let get_setter_key_at
      (finfo: function_info_int)
      (ctxtiaddr: ctxt_iaddress_t)
    : (setter_key_t * arm_assembly_instruction_int * location_int) option =
  match get_associated_test_instr finfo ctxtiaddr with
  | None -> None
  | Some (testloc, testinstr) ->
     Some (get_setter_key finfo testloc testinstr, testinstr, testloc)


let cmdstate_start: cmdstate_t = {cs_flat = []; cs_open = None}


(* Close cs_open (if any) into one BRANCH appended to cs_flat *)
let cmdstate_flush (finfo: function_info_int) (cs: cmdstate_t): cmdstate_t =
  match cs.cs_open with
  | None -> cs
  | Some fr ->
     let frozenAsserts = get_frozen_asserts finfo fr.fr_openerloc#ci in
     let openerinvop = get_invariant_operation fr.fr_openerloc in
     let branch =
       BRANCH [LF.mkCode fr.fr_thenbucket; LF.mkCode fr.fr_elsebucket] in
     {cs_flat = cs.cs_flat @ frozenAsserts @ [openerinvop; branch]; cs_open = None}


(* Extend cmdstate with the cmds for an unconditional / condition-covered
   instruction: closes any open fragment, and appends the already wrapped
   unit cmds *)
let cmdstate_append_linear
      (finfo: function_info_int) (cs: cmdstate_t) (unit_cmds: cmd_t list): cmdstate_t =
  let cs = cmdstate_flush finfo cs in
  {cs with cs_flat = cs.cs_flat @ unit_cmds}


let cmdstate_append_predicated
      (finfo: function_info_int)
      (cs: cmdstate_t)
      ~(key: setter_key_t)
      ~(cc: arm_opcode_cc_t)
      ~(openerloc: location_int)
      ~(thentest: cmd_t list)
      ~(elsetest: cmd_t list)
      ~(unit_cmds: cmd_t list): cmdstate_t =
  let _ =
    log_diagnostics_result
      ~tag:"cmdstate_append_predicated"
      ~msg:openerloc#ci
      __FILE__ __LINE__
      ["key: " ^ (setter_key_to_string key);
       "thentest: " ^ (p2s (chif_cmds_to_pretty thentest))] in
  match cs.cs_open with
  | Some fr when fr.fr_key = key && cc = fr.fr_opencc ->
     {cs with cs_open =
                Some {fr with fr_thenbucket = fr.fr_thenbucket @ unit_cmds}}
  | Some fr when fr.fr_key = key && Some cc = get_inverse_cc fr.fr_opencc ->
     {cs with cs_open =
                Some {fr with fr_elsebucket = fr.fr_elsebucket @ unit_cmds}}
  | Some fr when fr.fr_openerloc#ci = key.sk_testloc
                 && (cc = fr.fr_opencc || Some cc = get_inverse_cc fr.fr_opencc) ->
     let frozenAsserts = get_frozen_asserts finfo fr.fr_openerloc#ci in
     let openerinvop = get_invariant_operation fr.fr_openerloc in
     let cs = {cs_flat = cs.cs_flat @ frozenAsserts @ [openerinvop]; cs_open = None} in
     if cc = fr.fr_opencc then
       {cs with cs_open =
                  Some {fr_key = key; fr_opencc = cc; fr_openerloc = openerloc;
                        fr_thenbucket = thentest @ fr.fr_thenbucket @ unit_cmds;
                        fr_elsebucket = elsetest}}
     else
       {cs with cs_open =
                  Some {fr_key = key; fr_opencc = fr.fr_opencc;
                        fr_openerloc = openerloc;
                        fr_thenbucket = thentest @ fr.fr_thenbucket;
                        fr_elsebucket = elsetest @ unit_cmds}}
  | _ ->
     let cs = cmdstate_flush finfo cs in
     (* elsebucket is set to [], to avoid adding an ASSERT that must be weakened
        later, as in CMP / CMPNE / BNE *)
     {cs with
       cs_open =
         Some {fr_key = key;
               fr_opencc = cc;
               fr_openerloc = openerloc;
               fr_thenbucket = thentest @ unit_cmds;
               fr_elsebucket = []}}


(* Block end (no terminating conditional branch): flush and linearlize for
   package transaction *)
let cmdstate_finish (finfo: function_info_int) (cs: cmdstate_t): cmd_t list =
  (cmdstate_flush finfo cs).cs_flat


(* Terminator hookup: if the terminator's own setter_key_t matches the still
   open fragment, hand the fragment's buckets to make_condtiion instead of
   flushing them into an intra-block BRANCH; otherwise close the branch first.*)
let cmdstate_take_for_terminator
      (finfo: function_info_int)
      (cs: cmdstate_t)
      ~(key: setter_key_t)
      ~(cc: arm_opcode_cc_t): cmd_t list * cmd_t list * cmd_t list =
  match cs.cs_open with
  | Some fr when fr.fr_key = key && cc = fr.fr_opencc ->
     let frozenAsserts = get_frozen_asserts finfo fr.fr_openerloc#ci in
     let openerinvop = get_invariant_operation fr.fr_openerloc in
     (cs.cs_flat @ frozenAsserts @ [openerinvop], fr.fr_thenbucket, fr.fr_elsebucket)

  | Some fr when fr.fr_key = key && Some cc = get_inverse_cc fr.fr_opencc ->
     let frozenAsserts = get_frozen_asserts finfo fr.fr_openerloc#ci in
     let openerinvop = get_invariant_operation fr.fr_openerloc in
     (cs.cs_flat @ frozenAsserts @ [openerinvop], fr.fr_elsebucket, fr.fr_thenbucket)

  | Some fr when fr.fr_openerloc#ci = key.sk_testloc
                 && (cc = fr.fr_opencc || Some cc = get_inverse_cc fr.fr_opencc) ->
     let frozenAsserts = get_frozen_asserts finfo fr.fr_openerloc#ci in
     let openerinvop = get_invariant_operation fr.fr_openerloc in
     let _ =
       log_diagnostics_result
         ~tag:"cmdstate_take_for_terminator"
         ~msg:fr.fr_openerloc#ci
         __FILE__ __LINE__
         ["thenbucket: " ^ (p2s (chif_cmds_to_pretty fr.fr_thenbucket));
          "elsebucket: " ^ (p2s (chif_cmds_to_pretty fr.fr_elsebucket))] in
     if cc = fr.fr_opencc then
       (cs.cs_flat @ frozenAsserts @ [openerinvop], fr.fr_thenbucket, fr.fr_elsebucket)
     else
       (cs.cs_flat @ frozenAsserts @ [openerinvop], fr.fr_elsebucket, fr.fr_thenbucket)
  | _ ->
     (cmdstate_finish finfo cs, [], [])


let package_terminator_transactions
      (finfo: function_info_int)
      (blocklabel: symbol_t)
      (cmds: cmd_t list)
      (thencode: cmd_t list)
      (elsecode: cmd_t list)
    : (cmd_t
       * (symbol_t * cmd_t list) option
       * (symbol_t * cmd_t list) option) =
  let cnstAssigns = finfo#env#end_transaction in
  let cmds = List.filter (fun cmd -> match cmd with SKIP -> false | _ -> true) cmds in
  let transaction = TRANSACTION (blocklabel, LF.mkCode (cnstAssigns @ cmds), None) in
  let mk cl suffix =
    match cl with
    | [] -> None
    | _ ->
       let cl = List.filter (fun c -> match c with SKIP -> false | _ -> true) cl in
       let label =
         let atts = blocklabel#getAttributes in
         let atts = if suffix = "" then atts else atts @ [suffix] in
         new symbol_t ~atts blocklabel#getBaseName in
       Some (label, [TRANSACTION (label, LF.mkCode (cnstAssigns @ cl), None)]) in
  (transaction, mk thencode "thenbucket", mk elsecode "elsebucket")


let append_predicated_instruction
      (finfo: function_info_int)
      (cmdstate: cmdstate_t)
      ~(instr: arm_assembly_instruction_int)
      ~(loc: location_int)
      ~(cc: arm_opcode_cc_t)
      ~(build_unit:(cmd_t list -> cmd_t list))
      ~(cmds: cmd_t list): cmdstate_t =
  let ctxtiaddr = loc#ci in
  let frozenAsserts = get_frozen_asserts finfo ctxtiaddr in
  let default newcmds =
    let invop = get_invariant_operation loc in
    let newcmds = frozenAsserts @ (invop :: (build_unit newcmds)) in
    cmdstate_append_linear finfo cmdstate newcmds in

  if instr#is_condition_covered then
    default cmds

  else
    match get_associated_test_instr finfo ctxtiaddr with
    | Some (testloc, testinstr) ->
       let (_, tests) =
         make_instr_local_tests
           ~condloc:loc ~testloc ~condinstr:instr ~testinstr in
       if has_false_condition_context ctxtiaddr then
         (match tests with
          | Some (_, elsetest) -> default elsetest
          | _ -> default [])
       else if has_true_condition_context ctxtiaddr then
         (match tests with
          | Some (thentest, _) -> default (thentest @ cmds)
          | _ -> default cmds)
       else
         let key = get_setter_key finfo testloc testinstr in
         let (thentest, elsetest) =
           match tests with
           | Some (t, e) -> (t, e)
           | _ -> ([], []) in
         (match cmdstate.cs_open with
          | Some fr when (fr.fr_key = key)
                         && (cc = fr.fr_opencc
                             || get_inverse_cc fr.fr_opencc = Some cc) ->
             let invop = get_invariant_operation loc in
             let unit_cmds = frozenAsserts @ (invop :: (build_unit cmds)) in
             let fmem =
               {fmem_openerloc = fr.fr_openerloc;
                fmem_bucket = if cc = fr.fr_opencc then FragThen else FragElse} in
             begin
               finfo#set_fragment_membership ctxtiaddr fmem;
               cmdstate_append_predicated
                 finfo cmdstate
                 ~key ~cc ~openerloc:fr.fr_openerloc ~thentest:[] ~elsetest:[] ~unit_cmds
             end

          | Some fr when (fr.fr_openerloc#ci = key.sk_testloc)
                         && (cc = fr.fr_opencc
                             || get_inverse_cc fr.fr_opencc = Some cc) ->
             let unit_cmds = frozenAsserts @ (build_unit cmds) in
             let fmem =
               {fmem_openerloc = loc;
                fmem_bucket = if cc = fr.fr_opencc then FragThen else FragElse} in
             begin
               finfo#set_fragment_membership ctxtiaddr fmem;
               cmdstate_append_predicated
                 finfo cmdstate ~key ~cc ~openerloc:loc ~thentest ~elsetest ~unit_cmds
             end

          | _ ->
             let unit_cmds = frozenAsserts @ (build_unit cmds) in
             let fmem = {fmem_openerloc = loc; fmem_bucket = FragThen} in
             begin
               finfo#set_fragment_membership ctxtiaddr fmem;
               cmdstate_append_predicated
                 finfo cmdstate ~key ~cc ~openerloc:loc ~thentest ~elsetest ~unit_cmds
             end)
    | _ ->
       if has_false_condition_context ctxtiaddr then
         default []
       else if has_true_condition_context ctxtiaddr then
         default cmds
       else
         let _ =
           log_diagnostics_result
             ~tag:"append_predicated_instruction:no associated test"
             ~msg:ctxtiaddr
             __FILE__ __LINE__
             [] in
         default [BRANCH [LF.mkCode cmds; LF.mkCode [SKIP]]]
