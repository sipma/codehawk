(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2021-2026  Aarno Labs LLC

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
open CHOnlineCodeSet

(* bchlib *)
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMTypes


type setter_key_t = {
    sk_testloc: ctxt_iaddress_t;
    sk_testtestloc: ctxt_iaddress_t option
  }

type fragment_t = {
    fr_key: setter_key_t;
    fr_opencc: arm_opcode_cc_t; (* the cc that defines "then" *)
    fr_thenbucket: cmd_t list;  (* starts with thentest, grows by append *)
    fr_elsebucket: cmd_t list   (* starts with elsetest *)
  }

type cmdstate_t = {
    cs_flat: cmd_t list;           (* closed-out cmds, in order *)
    cs_open: fragment_t option     (* at most one open fragement *)
  }


val translate_arm_instruction:
  funloc:location_int
  -> codepc:arm_code_pc_int
  -> blocklabel:symbol_t
  -> cmdstate:cmdstate_t
  -> ((symbol_t
       * (code_t, 'a) command_t list) list
      * (symbol_t * symbol_t) list
      * cmdstate_t)


val translate_arm_assembly_function: arm_assembly_function_int -> unit
