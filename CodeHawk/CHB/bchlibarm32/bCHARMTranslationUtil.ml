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
open CHPretty

(* bchlib *)
open BCHLibTypes
open BCHLocation


module LF = CHOnlineCodeSet.LanguageFactory


let make_code_label
      ?(src:doubleword_int option)
      ?(modifier:string option)
      (address:ctxt_iaddress_t): symbol_t =
  let name =
    if address = "exit" || address = "?" then
      "exit"
    else
      "pc_" ^ address in
  let atts = match modifier with
    | Some s -> [s]
    | _ -> [] in
  let atts =
    if address = "?" then
      "unresolved-jump" :: atts
    else
      atts in
  let atts = match src with
    | Some s -> s#to_fixed_length_hex_string :: atts | _ -> atts in
  ctxt_string_to_symbol name ~atts address


let get_invariant_label ?(bwd=false) (loc:location_int) =
  if bwd then
    ctxt_string_to_symbol "bwd_invariant" loc#ci
  else
    ctxt_string_to_symbol "invariant" loc#ci


let get_invariant_operation (loc: location_int): cmd_t =
  let invlabel = get_invariant_label loc in
  OPERATION {op_name = invlabel; op_args = []}


let package_transaction
      (finfo:function_info_int) (label:symbol_t) (cmds:cmd_t list) =
  let cmds =
    List.filter
      (fun cmd -> match cmd with SKIP -> false | _ -> true) cmds in
  let cnstAssigns = finfo#env#end_transaction in
  TRANSACTION (label, LF.mkCode (cnstAssigns @ cmds), None)


let get_frozen_asserts
      (finfo: function_info_int) (ctxtiaddr: ctxt_iaddress_t): cmd_t list =
  List.map (fun (v, fv) -> ASSERT (EQ (v, fv)))
    (finfo#get_test_variables ctxtiaddr)


let chif_cmds_to_pretty (cmds: cmd_t list): pretty_t =
  pretty_print_list cmds (command_to_pretty 0) "[" "; " "]"
