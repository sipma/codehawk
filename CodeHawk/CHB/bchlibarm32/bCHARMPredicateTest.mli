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

(* xprlib *)
open XprTypes

(* bchlib *)
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMTypes

(** Functions to construct the branch conditions for conditional jumps and
    predicated instructions *)


(** Given a condition instruction (e.g., BEQ) with its location and a test
    instruction (e.g., CMP) with its location, [make_conditional_predicate]
    returns a tuple consisting of:
    - a list of temporary variables created to preserve the (frozen) values
      at the test location [testloc] for the location of the conditional,
      [condloc].
    - the predicate that expresses the joint condition of test and condition
      code, e.g., CMP X, Y with EQ produces X = Y.
    - a list of the operands used in the creation of the predicate, to be used
      in determining use location in def-use analysis.

    Side effect:
    If a predicate expression can be constructed, that expression is registered
    with the [floc] for the condition location, from where it can be retrieved
    later for xdata reporting. The pairs of register variables with their
    associated frozen values are registered with [floc] for the test location.
 *)
val make_conditional_predicate:
  condinstr:arm_assembly_instruction_int
  -> testinstr:arm_assembly_instruction_int
  -> condloc:location_int
  -> testloc:location_int
  -> (variable_t list * xpr_t option * arm_operand_int list)


(** [make_instr_local_tests] calls [make_conditional_predicate] to create a
    predicate expression (with the same side effect as above) and converts
    the predicate expression to CHIF code: one set of asserts for the then
    branch and one set of asserts for the else branch. The list of frozen
    variables created by [make_conditional_predicate] is returned as well.

    CHIF asserts are limited to atomic conditions like X op Y (e.g., X < Y),
    and thus expressions must be decomposed. At present there is only one
    level of decomposition into disjuncts and conjuncts. Disjuncts give rise
    to BRANCH constructs (which in practice do not strengthen the downstream
    invariant due to their immediate join) and conjuncts, which individually
    strengthen the downstream invariant. More complex expressions are not
    currently represented, and result in RANDOM asserts.

    [make_instr_local_tests] is only used for predicated instructions other
    than branch instructions.
 *)
val make_instr_local_tests:
  condinstr:arm_assembly_instruction_int
  -> testinstr:arm_assembly_instruction_int
  -> condloc:location_int
  -> testloc:location_int
  -> variable_t list * (cmd_t list * cmd_t list) option


(** [make_local_condition instr loc label thenaddr elseaddr] returns
    a list of CFG nodes and edges for a conditional jump instruction, [instr]
    that incorporates the full condition as part of the instruction itself
    (i.e., there is no dependency on a separate test instruction), such as
    CBZ (CompareBranchZer) or CBNZ).

    Two CFG nodes are created: a 'then' node with the then-test and an 'else'
    node with the else-test. Four CFG edges are created: (1) from block label
    [label] to thennode, (2) from block label [label] to elsenode, (3) from
    thennode to the CFG jump target address, [thenaddr], and (4) from elsenode
    to the CFG fall-through address, [elseaddr].
 *)
val make_local_condition:
  arm_assembly_instruction_int
  -> location_int
  -> symbol_t
  -> ctxt_iaddress_t
  -> ctxt_iaddress_t
  -> ((symbol_t * cmd_t list) list) * (symbol_t * symbol_t) list


(** Returns the control-flow graph nodes and edges of a conditional branch or an
    IfThen instruction that is handled with full control flow rather than with an
    aggregate. It applies to conditional branches in which the test is performed
    by a separate instruction (the test instruction) and the branch condition
    is determined by the combination of the test instruction and the condition
    code that is part of the branch instruction (or IfThen).

    If a conditional predicate for the branch can be synthesized and converted into
    CHIF, a 'then node' with the then-test and an 'else node' with the else-test
    are created. In both nodes the temporary variables that were created to carry
    the frozen values are abstracted to avoid unnecessary propagation of variables
    that will never be used again. Four edges are created: (1) from block-label
    to thenblock, (2) from thenblock to the cfg target jump address, (3) from
    block-label to elseblock, and (4) from elseblock to the cfg fall-through
    instruction.

    If a conditional predicate for the branch cannot be constructed the control flow
    components created represent a non-deterministic branch. One node is
    constructed, to abstract the temporary variables created by the attempt to
    create a condition. Three edges are created: (1) from block-label to the new
    node, (2) from the new node to the cfg target jump address, and (3) from the new
    node to the cfg fall-through instruction.

    The optional arguments [thencode] and [elsecode] are prefixed to the code in
    the thenblock and elseblock, resp. This code is the code generated for
    predicated instructions that precede the jump and whose predicate coincides
    with the respective predicates for the thenblock and elseblock. This code
    is transferred from the source block to the thenblock/elseblock, prefixing
    the thentest/elsetest code. The generation of the [thencode] and [elsecode]
    is managed by [bCHPredicatedFragment].
*)
val make_condition:
  ?thencode:(symbol_t * cmd_t list)
  -> ?elsecode:(symbol_t * cmd_t list)
  -> condinstr:arm_assembly_instruction_int
  -> testinstr:arm_assembly_instruction_int
  -> condloc:location_int
  -> testloc:location_int
  -> blocklabel:symbol_t
  -> thenaddr:ctxt_iaddress_t
  -> elseaddr:ctxt_iaddress_t
  -> unit
  -> ((symbol_t * cmd_t list) list) * (symbol_t * symbol_t) list
