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

(* bchlib *)
open BCHLibTypes

(* bchlibarm32 *)
open BCHARMTypes


(** Data structure and associated functions for the collection of predicated
    instructions into positive and negative branches within a basic block.

    The data structure allows for a refinement of the otherwise linear
    sequence of commands in a basic block, into internal branches with
    sequences of instructions with the same polarity to avoid joins after every
    predicated instruction.

    Sequences of code split by polarity are called fragments. Fragments are
    constructed incrementally during translation, one instruction at a time,
    their bucket selected by the polarity of the instruction relative to the
    polarity of the opener instruction (the first instruction after the test
    instruction.

    {b Example 1:}

    The basic block

    {v
    0x1e0ec  00 00 56 e3       CMP          R6, #0
    0x1e0f0  01 b0 8b 02       ADDEQ        R11, R11, #1
    0x1e0f4  06 b0 a0 11       MOVNE        R11, R6
    0x1e0f8  02 80 a0 11       MOVNE        R8, R2
    0x1e0fc  00 00 55 e3       CMP          R5, #0
    0x1e100  04 30 85 10       ADDNE        R3, R5, R4
    0x1e104  00 60 a0 13       MOVNE        R6, #0
    0x1e108  05 60 a0 01       MOVEQ        R6, R5
    0x1e10c  20 20 a0 13       MOVNE        R2, #0x20
    0x1e110  01 20 43 15       STRBNE       R2, [R3,-#1]
    v}

    would give rise to two fragments within one basic block:

    {v
    fragment 1:
      setter_key: 0x1e0ec, None
      opencc    : EQ
      thenbucket: [0x1e0f0]
      elsebucket: [0x1e0f4; 0x1e0f8]

    fragment 2:
      setter_key: 0x1e0fc, None
      opencc    : NE
      thenbucket: [0x1e100; 0x1e104; 0x1010c; 0x1e110]
      elsebucket: [0x1e108]
    v}

    If a basic block containing one or more fragments ends in a conditional
    jump with the same setter_key as the last fragment, as in, e.g.,

    {b Example 2:}

    {v
    0x1e2c0  00 20 a0 e3       MOV          R2, #0
    0x1e2c4  02 00 56 e1       CMP          R6, R2
    0x1e2c8  00 20 c3 e5       STRB         R2, [R3]
    0x1e2cc  06 70 a0 11       MOVNE        R7, R6
    0x1e2d0  06 b0 a0 11       MOVNE        R11, R6
    0x1e2d4  e8 ff ff 0a       BEQ          0x1e27c
    v}

    the branch instruction is hoisted just before the opener location (in this
    example just before 0x1e2cc) and the then bucket and else bucket of the
    fragment are, conceptually, added to the respective successor blocks,
    according to their polarity. In the above example, the instructions at
    0x1e2cc and 0x1e2d0 are added to the else block, that is, the block starting
    at 0x1e2d8, effectively connecting the instruction at 0x1e2cc directly to
    the then block. Note that there is no join between 0x1e2d0 and 0x1e2d4 in
    this case.
 *)

(** location of the test instruction of a fragment. If the test instruction itself
    is predicated (e.g., CMPNE), the [sk_testtestloc] contains the location of the
    test associated with that predicate, otherwise this field is [None].

    Note that the chain of test instructions is limited to two instructions.
 *)
type setter_key_t = {
    sk_testloc: ctxt_iaddress_t;
    sk_testtestloc: ctxt_iaddress_t option
  }

(** data structure that represents a sequence of predicated instructions that all
    depend on the same test instruction (or test instructions, in case of a chained
    test instruction). The openerloc is the location of the first instruction
    after the test (or tests), whose condition code (fr_opencc) determines the
    polarity of the thenbucket. The thenbucket and elsebucket contain the commands
    associated with the predicated instructions of the respective polarity.
 *)
type fragment_t = {
    fr_key: setter_key_t;
    fr_opencc: arm_opcode_cc_t;    (* the cc that defines "then" *)
    fr_openerloc: location_int; (* location of first instr in fragment *)
    fr_thenbucket: cmd_t list;  (* starts with thentest, grows by append *)
    fr_elsebucket: cmd_t list   (* starts with elsetest *)
  }

(** data structure that captures the current state of the translation, with at
    most one open fragment; cs_flat contains all closed_out commands, in order,
    including both unpredicated instructions and fragments of predicated
    instructions now closed.
 *)
type cmdstate_t = {
    cs_flat: cmd_t list;
    cs_open: fragment_t option
  }


(** [get_setter_key finfo testloc testinstr] returns a setter_key with the
    address of [testloc]. If the instruction [testinstr] at [testloc] is
    itself predicated, the function will attempt to retrieve the location of
    the test instruction for that predicated. If successful, this location
    will be added as sk_testtestloc. If not successful, the location will be
    set to [None] and a message is added to the error log.
 *)
val get_setter_key:
  function_info_int
  -> location_int
  -> arm_assembly_instruction_int
  -> setter_key_t


(** [get_setter_key_at finfo addr] returns the setter key that is associated
    with the predicated instruction at [addr], together with the test instruction
    and location of the test instruction. [None] is returned if no associated
    test instruction can be found.
 *)
val get_setter_key_at:
  function_info_int
  -> ctxt_iaddress_t
  -> (setter_key_t * arm_assembly_instruction_int * location_int) option


(** constant cmdstate_t object with cs_flat empty and cs_open [None].*)
val cmdstate_start: cmdstate_t


(** Closes cs_open (if any) into one BRANCH and adds it to cs_flat. Returns
    a new cmdstate_t object with the updated cs_flat, and cs_open set to
    [None].
 *)
val cmdstate_flush: function_info_int -> cmdstate_t -> cmdstate_t


(** [cmdstate_append_linear finfo cmdstate cmds] flushes [cmdstate], adds
    the [cmds] for a non-predicated instruction (or a predicated instruction
    that is part of an aggregate) to cs_flat, and returns the updated [cmdstate].
 *)
val cmdstate_append_linear:
  function_info_int -> cmdstate_t -> cmd_t list -> cmdstate_t


(** [cmdstate_append_predicated] adds a predicated instruction to [cmdstate].
    - If [cmdstate] does not have an open fragment (cs_open is [None]), a new
    fragment is created with the given [key], [cc], and openerloc, and the
    [thentest] and [unit_cmds] are added to the thenbucket.
    - If an open fragment with the same key and cc flavor as the opencc (the cc
    are the same or each other inverse), the [unit_cmds] are added to the
    thenbucket if cc equals opencc, and to the elsebucket otherwise.
    - If an open fragment exists whose openerloc is the same as the testloc of
    the instruction to be added (i.e., the openerloc of the open fragment
    belongs to a predicated test instruction), the openerloc of the open fragment
    is changed to the location of the instruction to be added and the opencc is
    set to the cc of the new instruction.
 *)
val cmdstate_append_predicated:
  function_info_int
  -> cmdstate_t
  -> key:setter_key_t
  -> cc:arm_opcode_cc_t
  -> openerloc:location_int
  -> thentest:cmd_t list
  -> elsetest:cmd_t list
  -> unit_cmds:cmd_t list
  -> cmdstate_t


(** flushes the [cmdstate] and returns the linearized command list from cs_flat
    from the resulting cmdstate. [cmdstate_finish] is called at the end of a
    basic block without terminating conditional branch.
 *)
val cmdstate_finish: function_info_int -> cmdstate_t -> cmd_t list



val cmdstate_take_for_terminator:
  function_info_int
  -> cmdstate_t
  -> key:setter_key_t
  -> cc:arm_opcode_cc_t
  -> cmd_t list * cmd_t list * cmd_t list


val package_terminator_transactions:
  function_info_int
  -> symbol_t
  -> cmd_t list
  -> cmd_t list
  -> cmd_t list
  -> (cmd_t
      * (symbol_t * cmd_t list) option
      * (symbol_t * cmd_t list) option)


val append_predicated_instruction:
  function_info_int
  -> cmdstate_t
  -> instr:arm_assembly_instruction_int
  -> loc:location_int
  -> cc: arm_opcode_cc_t
  -> build_unit:(cmd_t list -> cmd_t list)
  -> cmds:cmd_t list
  -> cmdstate_t
