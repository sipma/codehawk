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

(* xprlib *)
open Xprt
open XprTypes
open XprUtil
open Xsimplify

(* bchlib *)
open BCHFloc
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMAssemblyInstructions
open BCHARMConditionalExpr
open BCHARMOpcodeRecords
open BCHARMTestSupport
open BCHARMTranslationUtil
open BCHARMTypes

module LF = CHOnlineCodeSet.LanguageFactory
module TR = CHTraceResult

let p2s = CHPrettyUtil.pretty_to_string
(* other useful functions for printing debug messages
let x2p = XprToPretty.xpr_formatter#pr_expr
let x2s x = p2s (x2p x)
 *)

let make_conditional_predicate
      ~(condinstr: arm_assembly_instruction_int)
      ~(testinstr: arm_assembly_instruction_int)
      ~(condloc: location_int)
      ~(testloc: location_int) =
  let testfloc = get_floc testloc in
  let get_default_conditional_expr () =
    arm_conditional_expr
      ~condopc:condinstr#get_opcode
      ~testopc:testinstr#get_opcode
      ~condloc:condloc
      ~testloc:testloc in
  if is_opcode_conditional testinstr#get_opcode then
    let finfo = testfloc#f in
    match get_associated_test_instr finfo testloc#ci with
    | Some (testtestloc , testtestinstr) ->
       arm_conditional_conditional_expr
         ~condopc:condinstr#get_opcode
         ~testopc:testinstr#get_opcode
         ~testtestopc: testtestinstr#get_opcode
         ~condloc
         ~testloc
         ~testtestloc
    | _ ->
       get_default_conditional_expr ()
  else
    get_default_conditional_expr ()


let make_instr_local_tests
    ~(condinstr:arm_assembly_instruction_int)
    ~(testinstr:arm_assembly_instruction_int)
    ~(condloc:location_int)
    ~(testloc:location_int) =
  let testfloc = get_floc testloc in
  let condfloc = get_floc condloc in
  let env = testfloc#f#env in
  let reqN () = env#mk_num_temp in
  let reqC i = env#request_num_constant i in
  let (frozenVars, optboolxpr, _) =
    make_conditional_predicate ~condinstr ~testinstr ~condloc ~testloc in
  let convert_to_chif expr =
    let (cmds, bxpr) = xpr_to_boolexpr reqN reqC expr in
    cmds @ [ASSERT bxpr] in
  let convert_to_assert eexpr =
    let expr = simplify_xpr eexpr in
    let vars = variables_in_expr expr in
    let varssize = List.length vars in
    let xprs =
      if varssize = 1 then
	let var = List.hd vars in
	let extxprs = condfloc#inv#get_external_exprs var in
	let extxprs =
          List.map (fun e -> substitute_expr (fun _ -> e) expr) extxprs in
	expr :: extxprs
      else if varssize = 2 then
	let varlist = vars in
	let var1 = List.nth varlist 0 in
	let var2 = List.nth varlist 1 in
	let extxprs1 = condfloc#inv#get_external_exprs var1 in
	let extxprs2 = condfloc#inv#get_external_exprs var2 in
	let xprs = List.concat
	  (List.map
	     (fun e1 ->
	       List.map
		 (fun e2 ->
		   substitute_expr
                     (fun w -> if w#equal var1 then e1 else e2) expr)
		 extxprs2)
	     extxprs1) in
	expr :: xprs
      else
	[expr] in
    List.concat (List.map convert_to_chif xprs) in
  let make_asserts exprs =
    List.concat (List.map convert_to_assert exprs) in
  let make_branch_assert exprs =
    let commands = List.map convert_to_assert exprs in
    [BRANCH (List.map LF.mkCode commands)] in
  let make_assert expr = convert_to_assert expr in
  let make_test_code expr =
    if is_conjunction expr then
      let conjuncts = get_conjuncts expr in
      make_asserts conjuncts
    else if is_disjunction expr then
      let disjuncts = get_disjuncts expr in
      make_branch_assert disjuncts
    else
      make_assert expr in
  match optboolxpr with
    Some bbxpr ->
     let bxpr = simplify_xpr bbxpr in
     let thencode = make_test_code bxpr in
     let elsecode = make_test_code (simplify_xpr (XOp (XLNot, [bxpr]))) in
     (frozenVars, Some (thencode, elsecode))
  | _ ->
     (frozenVars, None)


let make_tests
    ~(condinstr:arm_assembly_instruction_int)
    ~(testinstr:arm_assembly_instruction_int)
    ~(condloc:location_int)
    ~(testloc:location_int) =
  let testfloc = get_floc testloc in
  let condfloc = get_floc condloc in
  let env = testfloc#f#env in
  let reqN () = env#mk_num_temp in
  let reqC i = env#request_num_constant i in
  let (frozenVars, optboolxpr, _) =
    make_conditional_predicate ~condinstr ~testinstr ~condloc ~testloc in

  let _ =
    if testsupport#requested_arm_conditional_expr then
      testsupport#submit_arm_conditional_expr condinstr testinstr optboolxpr in

  let convert_to_chif ?(high=true) expr =
    let vars = variables_in_expr expr in
    let varscmds =
      if high then
        condfloc#get_vardef_commands ~usehigh:vars condloc#ci
      else
        condfloc#get_vardef_commands ~use:vars condloc#ci in
    let (cmds, bxpr) = xpr_to_boolexpr reqN reqC expr in
    cmds @ varscmds @ [ASSERT bxpr] in
  let convert_to_assert expr  =
    let vars = variables_in_expr expr in
    let varssize = List.length vars in
    let xprs =
      if varssize = 1 then
	let var = List.hd vars in
	let extxprs = condfloc#inv#get_external_exprs var in
	let extxprs =
          List.map (fun e -> substitute_expr (fun _ -> e) expr) extxprs in
        match extxprs with
        | [] -> [expr]
        | _ -> extxprs
      else if varssize = 2 then
	let varlist = vars in
	let var1 = List.nth varlist 0 in
	let var2 = List.nth varlist 1 in
	let extxprs1 = condfloc#inv#get_external_exprs var1 in
	let extxprs2 = condfloc#inv#get_external_exprs var2 in
	let xprs = List.concat
	  (List.map
	     (fun e1 ->
	       List.map
		 (fun e2 ->
		   substitute_expr
                     (fun w -> if w#equal var1 then e1 else e2) expr)
		 extxprs2)
	     extxprs1) in
	expr :: xprs
      else
	[expr] in
    let _ =
      if testsupport#requested_chif_conditionxprs then
        testsupport#submit_chif_conditionxprs condinstr testinstr xprs in
    let basic_asserts = convert_to_chif ~high:false (List.hd xprs) in
    let rewritten_asserts = List.concat (List.map convert_to_chif (List.tl xprs)) in
    basic_asserts @ rewritten_asserts in

  let make_asserts exprs =
    let _ = env#start_transaction in
    let commands = List.concat (List.map convert_to_assert exprs) in
    let const_assigns = env#end_transaction in
    const_assigns @ commands in
  let make_branch_assert exprs =
    let _ = env#start_transaction in
    let commands = List.map convert_to_assert exprs in
    let branch = BRANCH (List.map LF.mkCode commands) in
    let const_assigns = env#end_transaction in
    const_assigns @ [branch] in
  let make_assert expr =
    let _ = env#start_transaction in
    let commands = convert_to_assert expr in
    let const_assigns = env#end_transaction in
    const_assigns @ commands in
  let make_test_code expr =
    if is_conjunction expr then
      let conjuncts = get_conjuncts expr in
      make_asserts conjuncts
    else if is_disjunction expr then
      let disjuncts = get_disjuncts expr in
      make_branch_assert disjuncts
    else
      make_assert expr in
  match optboolxpr with
    Some bbxpr ->
     let bxpr = simplify_xpr bbxpr in
     let thencode = make_test_code bxpr in
     let elsecode = make_test_code (simplify_xpr (XOp (XLNot, [bxpr]))) in
     (frozenVars, Some (thencode, elsecode))
  | _ -> (frozenVars, None)


(* Returns the CHIF code for a conditional branch instruction that
   incorporates the full condition as part of the instruction (i.e. no
   dependency on a separate test instruction), such as CBZ or CBNZ.

   The CHIF code consists of a tuple of two sequences of CHIF commands.
   The first sequence is the CHIF for the then test, the second sequence
   is the CHIF for the else test.

   If the condition cannot be converted to CHIF SKIP commands are
   returned, that is, the conditional branch is effectively turned into
   a nondeterminstic branch.
 *)
let make_local_tests
      (condinstr: arm_assembly_instruction_int)
      (condloc: location_int): (cmd_t list * cmd_t list) =
  let floc = get_floc condloc in
  let env = floc#f#env in
  let reqN () = env#mk_num_temp in
  let reqC i = env#request_num_constant i in
  let boolxpr_r =
    match condinstr#get_opcode with
    | CompareBranchZero (op, _) ->
       TR.tmap
         ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
         (fun x -> XOp (XEq, [x; zero_constant_expr]))
         (op#to_expr floc)
    | CompareBranchNonzero (op, _) ->
       TR.tmap
         ~msg:(__FILE__ ^ ":" ^ (string_of_int __LINE__))
         (fun x -> XOp (XNe, [x; zero_constant_expr]))
         (op#to_expr floc)
    | _ ->
       Error [__FILE__ ^ ":" ^ (string_of_int __LINE__) ^ ": "
              ^ "Unexpected condition: " ^ (p2s condinstr#toPretty)] in

  let convert_to_chif expr =
    let vars = variables_in_expr expr in
    let defcmds = floc#get_vardef_commands ~usehigh:vars floc#l#ci in
    let (cmds, bxpr) = xpr_to_boolexpr reqN reqC expr in
    cmds @ defcmds @ [ASSERT bxpr] in
  let make_assert x =
    let _ = env#start_transaction in
    let commands = convert_to_chif x in
    let const_assigns = env#end_transaction in
    const_assigns @ commands in
  TR.tfold
    ~ok:(fun boolxpr ->
      let thencode = make_assert boolxpr in
      let elsecode = make_assert (simplify_xpr (XOp (XLNot, [boolxpr]))) in
      (thencode, elsecode))
    ~error:(fun e ->
      begin
        log_error_result __FILE__ __LINE__ e;
        ([SKIP], [SKIP])
      end)
    boolxpr_r


let make_local_condition
      (condinstr: arm_assembly_instruction_int)
      (condloc: location_int)
      (blocklabel: symbol_t)
      (thenaddr: ctxt_iaddress_t)
      (elseaddr: ctxt_iaddress_t) =
  let thenlabel = make_code_label thenaddr in
  let elselabel = make_code_label elseaddr in
  let (thentest, elsetest) = make_local_tests condinstr condloc in
  let make_node_and_label testcode tgtaddr modifier =
    let src = condloc#i in
    let nextlabel = make_code_label ~src ~modifier tgtaddr in
    let transaction = TRANSACTION (nextlabel, LF.mkCode testcode, None) in
    (nextlabel, [transaction]) in
  let (thentestlabel, thennode) =
    make_node_and_label thentest thenaddr "then" in
  let (elsetestlabel, elsenode) =
    make_node_and_label elsetest elseaddr "else" in
  let thenedges =
    [(blocklabel, thentestlabel); (thentestlabel, thenlabel)] in
  let elseedges =
    [(blocklabel, elsetestlabel); (elsetestlabel, elselabel) ] in
  ([(thentestlabel, thennode); (elsetestlabel, elsenode)], thenedges @ elseedges)


let make_condition
      ?(thencode: (symbol_t * cmd_t list) option)
      ?(elsecode: (symbol_t * cmd_t list) option)
      ~(condinstr:arm_assembly_instruction_int)
      ~(testinstr:arm_assembly_instruction_int)
      ~(condloc:location_int)
      ~(testloc:location_int)
      ~(blocklabel:symbol_t)
      ~(thenaddr:ctxt_iaddress_t)
      ~(elseaddr:ctxt_iaddress_t)
      () =
  let thenlabel = make_code_label thenaddr in
  let elselabel = make_code_label elseaddr in
  let (frozenVars, tests) =
    make_tests ~condloc ~testloc ~condinstr ~testinstr in
  match tests with
    Some (thentest, elsetest) ->
      let make_node_and_label testcode tgtaddr modifier =
	let src = condloc#i in
	let nextlabel = make_code_label ~src ~modifier tgtaddr in
	let testcode =
          testcode
          @ (match frozenVars with
             | [] -> []
             | _ -> [ABSTRACT_VARS frozenVars]) in
	let transaction = TRANSACTION (nextlabel, LF.mkCode testcode, None) in
        (nextlabel, [transaction]) in
      let (thentestlabel, thennode) =
	make_node_and_label thentest thenaddr "then" in
      let (elsetestlabel, elsenode) =
	make_node_and_label elsetest elseaddr "else" in
      let thenbucket =
        match thencode with
        | Some (label, cmds) ->
           [(label, [TRANSACTION (label, LF.mkCode cmds, None)])]
        | _ -> [] in
      let elsebucket =
        match elsecode with
        | Some (label, cmds) ->
           [(label, [TRANSACTION (label, LF.mkCode cmds, None)])]
        | _ -> [] in
      let thenedges =
        match thenbucket with
        | [(thenbucketlabel, _)] ->
	   [(blocklabel, thenbucketlabel);
            (thenbucketlabel, thentestlabel);
            (thentestlabel, thenlabel)]
        | _ ->
           [(blocklabel, thentestlabel); (thentestlabel, thenlabel)] in
      let elseedges =
        match elsebucket with
        | [(elsebucketlabel, _)] ->
           [(blocklabel, elsebucketlabel);
            (elsebucketlabel, elsetestlabel);
            (elsetestlabel, elselabel)]
        | _ ->
	   [(blocklabel, elsetestlabel); (elsetestlabel, elselabel) ] in
      (thenbucket @ elsebucket @ [(thentestlabel, thennode); (elsetestlabel, elsenode)],
       thenedges @ elseedges)
  | _ ->
     let abstractlabel =
       make_code_label ~modifier:"abstract" testloc#ci in
     let trcode =
       match frozenVars with
       | [] -> [SKIP]
       | _ -> [ABSTRACT_VARS frozenVars] in
     let transaction =
       TRANSACTION (abstractlabel, LF.mkCode trcode, None) in
     let edges = [
         (blocklabel, abstractlabel);
         (abstractlabel, thenlabel);
	 (abstractlabel, elselabel)] in
     ([(abstractlabel, [transaction])], edges)
