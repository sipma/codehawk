(* =============================================================================
   CodeHawk Unit Testing Framework
   Author: Henny Sipma
   Adapted from: Kaputt (https://kaputt.x9c.fr/index.html)
   ------------------------------------------------------------------------------
   The MIT License (MIT)

   Copyright (c) 2024-2025  Aarno Labs LLC

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
open CHNumerical

(* bchlib *)
open BCHBCFiles
open BCHBCTypes
open BCHDoubleword
open BCHFunctionData
open BCHLibTypes

(* bchcil *)
open BCHParseCilFile


module M = BCHMemoryReference

module TR = CHTraceResult
module TS = TCHTestSuite
module XBA = TCHBchlibAssertion


let testname = "bCHMemoryReferenceTest"
let lastupdated = "2025-01-06"


let mk_maximal_memory_offset_test () =
  begin

    parse_cil_file ~removeUnused:false "decompose_array_address.i";
    ignore
       (functions_data#add_function (TR.tget_ok (string_to_doubleword "0x1d6bfc")));
    let compinfo = bcfiles#get_compinfo_by_name "x44_struct_t" in
    let structty = TComp (compinfo.bckey, []) in

    TS.new_testsuite
      (testname ^ "_mk_maximal_memory_offset_test") lastupdated;

    TS.add_simple_test
      ~title:"struct-1"
      (fun () ->
        XBA.equal_memory_offset
          ~expected: (FieldOffset (("field0", compinfo.bckey), NoOffset))
          ~received: (M.mk_maximal_memory_offset numerical_zero structty)
          ());

    TS.add_simple_test
      ~title:"struct-4"
      (fun () ->
        XBA.equal_memory_offset
          ~expected: (FieldOffset (("field4", compinfo.bckey), NoOffset))
          ~received: (M.mk_maximal_memory_offset (mkNumerical 4) structty)
          ());

    TS.add_simple_test
      ~title:"struct-8"
      (fun () ->
        let suboffset = ConstantOffset (numerical_zero, NoOffset) in
        XBA.equal_memory_offset
          ~expected: (FieldOffset (("buffer", compinfo.bckey), suboffset))
          ~received: (M.mk_maximal_memory_offset (mkNumerical 8) structty)
          ());

    TS.add_simple_test
      ~title:"struct-20"
      (fun () ->
        let suboffset = ConstantOffset (mkNumerical 12, NoOffset) in
        XBA.equal_memory_offset
          ~expected: (FieldOffset (("buffer", compinfo.bckey), suboffset))
          ~received: (M.mk_maximal_memory_offset (mkNumerical 20) structty)
          ());

    TS.add_simple_test
      ~title:"invalid"
      (fun () ->
        XBA.equal_memory_offset
          ~expected: UnknownOffset
          ~received: (M.mk_maximal_memory_offset (mkNumerical 80) structty)
          ());

    TS.launch_tests ()
  end


let () =
  begin
    TS.new_testfile testname lastupdated;
    mk_maximal_memory_offset_test ();
    TS.exit_file ()
  end
