(* =============================================================================
   CodeHawk Binary Analyzer
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2021-2024  Aarno Labs, LLC

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

(* bchlib *)
open BCHLibTypes


val disassemble_arm_section: doubleword_int -> string -> unit

val disassemble_arm_sections: unit -> unit


(** Set block markers in the assembly instructions. Only used externally
    in the unit tests. *)
val set_block_boundaries: unit -> unit


(** Record the call targets based on call instructions. Only used externally
    in the unit tests. *)
val record_call_targets_arm: unit -> unit

val collect_function_entry_points: unit -> doubleword_int list


(** Associate condition codes in test instructions to condition code
    used by conditional instructions. Only used externally in the unit
    tests *)
val associate_condition_code_users: unit -> unit


(** Constructs functions starting from function entry points found.

    The default value of the optional argument [construct_all_functions]
    is [false]. This is relevant only in the case when only a limited
    number of functions are being analyzed (as specifified on the
    commandline with [fns_included]. By default only those functions
    are constructed. If [construct_all_functions] is [true] then
    functions for all function entry points are constructed.*)
val construct_functions_arm: ?construct_all_functions:bool -> unit -> unit
