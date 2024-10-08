(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2020 Kestrel Technology LLC
   Copyright (c) 2021      Henny Sipma
   Copyright (c) 2021-2024 Aarno Labs LLC

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

(* bchlibmips32 *)
open BCHMIPSTypes


(** [make_mips_assembly_function faddr blocks successors] creates a new
    assembly function with function address faddr, basic blocks [blocks],
    and context addresses of successor blocks [successors]. **)
val make_mips_assembly_function:
  doubleword_int
  -> mips_assembly_block_int list
  -> (ctxt_iaddress_t * ctxt_iaddress_t) list
  -> mips_assembly_function_int


(** [inline_blocks_mips_assembly_function baddrs fn] creates a new
    assembly function that is identical to the [fn] except that the
    basic blocks starting with an address in [baddrs] are contextualized
    in the context of their predecessor block.

    The purpose of this contextualization is to create limited path
    sensitivity to avoid that a premature join loses the context of
    an assignment. For example, if a joint successor makes an assignment
    based on a value that is individually set by its two predecessoors,
    after the join the connection cannot be made to the originating
    path. Inlining blocks delays the join until after the assignment. *)
val inline_blocks_mips_assembly_function:
  doubleword_int list  (* addresses of blocks to be inlined *)
  -> mips_assembly_function_int    (* original function *)
  -> mips_assembly_function_int    (* new instance *)
