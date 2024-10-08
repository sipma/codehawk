(* =============================================================================
   CodeHawk Binary Analyzer 
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2023-2024  Aarno Labs LLC

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
open CHPretty

(* chutil *)
open CHXmlDocument

(* bchlib *)
open BCHBasicTypes
open BCHByteUtilities
open BCHDoubleword
open BCHStreamWrapper

(* bchlibelf *)
open BCHDwarfTypes
open BCHDwarfUtils
open BCHELFSection
open BCHELFTypes

module TR = CHTraceResult


class elf_debug_loc_section_t (s: string): elf_debug_loc_section_int =
object (self)

  val mutable ch = make_pushback_stream ~little_endian:true s
     
  inherit elf_raw_section_t s wordzero

  method initstream (offset: int) =
    begin
      ch <- make_pushback_stream ~little_endian:true s;
      ch#skip_bytes offset
    end

  method get_loclist (index: int) =
    if index < 0 || index >= String.length s then
      raise
        (BCH_failure
           (LBLOCK [STR "debug_loc: string index out of bounds: "; INT index]))
    else
      begin
        self#initstream index;
        LocationList self#get_location_list
      end

  method private read_single_location_description (size: int) =
    let dwexpr = read_dwarf_expression ch size in
    SimpleLocation dwexpr

  method get_location_list =
    let more_entries = ref true in
    let loclistentries = ref [] in
    let start_addr = ref ch#read_doubleword in
    let end_addr = ref ch#read_doubleword in
    begin
      while !more_entries do
        if !start_addr#equal wordzero && !end_addr#equal wordzero then
          more_entries := false
        else
          begin
            (if !start_addr#equal wordmax then
               loclistentries :=
                 (LocBaseAddressSelectionEntry !end_addr) :: !loclistentries
             else
               let size = ch#read_ui16 in
               let desc = self#read_single_location_description size in
               let entry = {
                   lle_start_address = !start_addr;
                   lle_end_address = !end_addr;
                   lle_location = desc
                 } in
               loclistentries := (LocationListEntry entry) :: !loclistentries);
            start_addr := ch#read_doubleword;
            end_addr := ch#read_doubleword
          end
      done;
      List.rev !loclistentries
    end

end


let mk_elf_debug_loc_section (s: string) (_h: elf_section_header_int) =
  new elf_debug_loc_section_t s


let read_xml_elf_debug_loc_section (node: xml_element_int) =
  let s = read_xml_raw_data (node#getTaggedChild "hex-data") in
  new elf_debug_loc_section_t s
