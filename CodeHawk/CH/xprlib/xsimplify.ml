(* =============================================================================
   CodeHawk Analyzer Infrastructure Utilities
   Author: Henny Sipma
   ------------------------------------------------------------------------------
   The MIT License (MIT)
 
   Copyright (c) 2005-2019 Kestrel Technology LLC

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

open Big_int_Z

(* chlib *)
open CHCommon
open CHNumerical   
open CHPretty

(* chutil *)
open CHLogger

(* xprlib *)
open XprTypes
open Xprt
open XprToPretty

exception XSimplificationProblem of CHPretty.pretty_t

let xpr_to_pretty e = xpr_printer#pr_expr e

type e_struct_t =
  | SConst of numerical_t
  | SRange of numerical_t * numerical_t
  | SLBRange of numerical_t
  | SUBRange of numerical_t
  | SRScalar of xop_t * xpr_t * numerical_t
  | SLScalar of xop_t * numerical_t * xpr_t
  | Unreduced

let get_struct expr =
  match expr with
  | XConst (IntConst n) -> 
     SConst n
  | XOp (XNumRange, [XConst (IntConst lb) ; XConst (IntConst ub) ]) ->
     SRange (lb, ub)
  | XOp (XNumRange, [XConst (IntConst lb) ; _ ]) ->
     SLBRange lb
  | XOp (XNumRange, [ _ ; XConst (IntConst ub)]) ->
     SUBRange ub
  | XOp (XNumJoin, [XConst (IntConst i1) ; XConst (IntConst i2) ]) ->
     if i1#equal i2 then SConst i1
     else if i1#lt i2 then SRange (i1, i2)
     else SRange (i2, i1)
  | XOp (op, [e1 ; e2]) ->
     begin 
       match (get_const e1, get_const e2) with
	 (Some c1, Some c2) -> 
	 begin
	   chlog#add "unreduced constants in simplification"
                     (LBLOCK [ xpr_to_pretty expr ]) ;
	   Unreduced
	 end
       (*		  raise (CSimplificationProblem
							(LBLOCK [STR "unsimplified constants: "; s ]))   *)
       | (Some c1, _ ) -> SLScalar (op, c1, e2)
       | (_, Some c2 ) -> SRScalar (op, e1, c2)
       | _ -> Unreduced
     end
  | _ -> Unreduced


let divides x y = 
  if x#equal numerical_zero then false
  else (mkNumerical_big (mod_big_int y#getNum x#getNum))#equal numerical_zero

let pos_num x = x#gt numerical_zero
let neg_num x = x#lt numerical_zero
let zero_num x = x#equal numerical_zero

let rec sim_expr (m:bool) (e:xpr_t):(bool * xpr_t) =
  match e with
  | XOp (XNeg, [e1]) ->
     let (m,s) = sim_expr m e1 in reduce_neg m s
  | XOp (XLNot, [e1]) ->
     let (m,s) = sim_expr m e1 in reduce_logical_not m s
  | XOp ( op, [e1 ; e2] ) ->
     let (m1,s1) = sim_expr m e1 in
     let (m2,s2) = sim_expr m e2 in
     let m = m1 || m2 in
     begin
       match op with
       | XPlus -> reduce_plus m s1 s2
       | XMinus -> reduce_minus m s1 s2
       | XMult -> reduce_mult m s1 s2
       | XDiv -> reduce_div m s1 s2
       | XMod -> reduce_mod m s1 s2
       | XLt -> reduce_lt m s1 s2
       | XLe -> reduce_le m s1 s2
       | XGt -> reduce_gt m s1 s2
       | XGe -> reduce_ge m s1 s2
       | XEq -> reduce_eq m s1 s2
       | XNe -> reduce_ne m s1 s2
       | XBOr -> reduce_bor m s1 s2
       | XLOr -> reduce_or m s1 s2
       | XShiftlt -> reduce_shiftleft m s1 s2
       | XShiftrt -> reduce_shiftright m s1 s2
       | XBAnd -> reduce_bitwiseand m s1 s2
       | XDisjoint -> reduce_disjoint m s1 s2
       | XSubset -> reduce_subset m s1 s2
       | XNumJoin -> reduce_binary_numjoin m s1 s2
       | Xf "max" -> reduce_max m s1 s2
       | _ -> (m, XOp (op, [s1 ; s2]))
     end
  | XOp (Xf "max", l) -> reduce_max_list m l
  | XOp (XNumJoin, l) ->
     reduce_numjoin m l
  | XAttr (d, x) ->
     let (m,s) = sim_expr m x in
     (m, XAttr (d,s))
  | _ -> (m, e)

and reduce_neg m e1 =
  let default () = (m, XOp (XNeg, [ e1 ])) in
  match e1 with
  | XConst (IntConst num) -> (true, XConst (IntConst num#neg))
  | _ -> default ()
       
and reduce_max m e1 e2 =
  let default () = (m, XOp (Xf "max", [ e1 ; e2 ])) in 
  match (e1,e2) with
  | (XConst (IntConst num1), XConst (IntConst num2)) ->
     if num1#geq num2 then
       (true, e1)
     else 
       (true, e2)
  | _ -> default ()

and reduce_max_list m l =
  let default () = (m, XOp (Xf "max", l)) in
  match l with
  | [] -> default ()
  | [x] -> (true, x)
  | _ ->
     let result =
       List.fold_left (fun acc x ->
           match (acc,x) with
           | (XConst (IntConst nmax),XConst (IntConst n)) ->
              if n#gt nmax then x else acc
           | _ -> random_constant_expr) (List.hd l) (List.tl l) in
     match result with
     | XConst (IntConst _) -> (true, result)
     | _ -> default ()
              
	
and reduce_plus m e1 e2 =
  let default () = (m, XOp (XPlus, [e1 ; e2])) in
  let ne n = num_constant_expr n in
  let nr n1 n2 = XOp (XNumRange, [ num_constant_expr n1 ; num_constant_expr n2]) in
  let rs op args = sim_expr true (XOp (op, args)) in
  if is_zero e1 then (true, e2)                           (* x + 0 = x *)
  else if is_zero e2 then (true, e1)                      (* 0 + x = x *)
  else if is_random e1 then (true, random_constant_expr)
  else if is_random e2 then (true, random_constant_expr)
  else
    match (e1,e2) with
    | (x, XOp (XMinus, [y ; z]))                                     (* x + (y-x) ~> y *)
         when syntactically_equal x z -> (true, y)
    | (XOp (XMinus, [y ; x]), z) when syntactically_equal x z ->
       (true, y)                                                      (* (y-x) + x ~> y *)

    | (XOp (XPlus, [ x ; y ]), XOp (XMinus, [ z ; t ])) when syntactically_equal y t ->
       rs XPlus [ x ; z]                               (*  (x + y) + (z - y)  ~> x + z  *)
      
    | _ ->
       match (get_struct e1, get_struct e2) with
	 (SConst a, SConst b) -> 
	 (true, ne (a#add b))                                                  (* a + b *)
	 
       | (SConst c, SRange(a,b))
	 | (SRange(a,b), SConst c) ->                           (* [a,b] + c = [a+c,b+c] *)
	  (true, nr (a#add c) (b#add c)) 
	 
       | (SLBRange a, SLBRange b) ->                       (* [a,_] + [b,_] ~> [(a+b),_] *)
	  (true, XOp (XNumRange, [ne (a#add b) ; unknown_int_constant_expr]))
	 
       | (SLBRange a, SRange(b,c))                         (* [a,_] + [b,c] ~> [(a+b),_] *)
	 | (SRange(b,c), SLBRange a) ->                      
	  (true, XOp (XNumRange, [ne (a#add b) ; unknown_int_constant_expr]))
	 
       | (SConst a, SLBRange b) ->                             (* a + [b,_] ~> [(a+b),_] *)
	  (true, XOp (XNumRange, [ne (a#add b) ; unknown_int_constant_expr]))
	 
       | (_ , SConst b) when b#lt numerical_zero ->
	  let nb = b#mult (mkNumerical (-1)) in
	  (true, XOp (XMinus, [e1 ; ne nb]))                        (* a + (-b) -> a - b *)
	  
       | (_, SLScalar (XMult, b, x)) when b#equal (mkNumerical (-1))  ->
	  rs XMinus [ e1 ; x ]                                  (* y + (-1 * x) -> y - x *)
	 
       | (SLScalar (XMult, b, x), _) when b#equal (mkNumerical (-1))  ->
	  rs XMinus [ e2 ; x ]                                  (* (-1 * x) + y -> y - x *)
	 
       | (SConst a, SLScalar (XPlus, b, x))                               (* a + (b + x) *)
	 | (SConst a, SRScalar (XPlus, x, b))                             (* a + (x + b) *)
	 | (SLScalar (XPlus, a, x), SConst b)                             (* (a + x) + b *)
	 | (SRScalar (XPlus, x, a), SConst b) ->                          (* (x + a) + b *)
	  rs XPlus [ x ; ne (a#add b) ]                                  (* ~> x + (a+b) *)
	 
       | (SConst a, SLScalar (XMinus, b, x))                              (* a + (b - x) *)
	 | (SLScalar (XMinus, b, x), SConst a) ->                         (* (b - x) + a *)
	  rs XMinus [ ne (a#add b) ; x]                                  (* ~> (a+b) - x *)
	 
       | (SConst a, SRScalar (XMinus, x, b))                              (* a + (x - b) *)
	 | (SRScalar (XMinus, x, b), SConst a) ->                         (* (x - b) + a *)
	  rs XPlus [x ; ne (a#sub b)]                                    (* ~> x + (a-b) *)
	 
       | (SLScalar (XMinus, a, x), _) ->                                  (* (a - x) + y *)
	  rs XPlus [ XOp (XMinus, [ e2 ; x ]) ; ne a ]                 (* ~> (y - x) + a *)

       | (SRScalar (XMinus, x, a), _) ->                                  (* (x - a) + y *)
	  rs XMinus [ XOp (XPlus, [ x ; e2 ]) ; ne a ]                 (* -> (x + y) - a *)

       | (_ , SLScalar(XMinus, a, x)) ->                                  (* y + (a - x) *)
	  rs XPlus [ XOp (XMinus, [ e1 ; x ]); ne a ]                  (* ~> (x - y) + a *)

       | (_ , SRScalar (XMinus, x, a)) ->                                 (* y + (x - a) *)
	  rs XMinus [ XOp (XPlus, [ e1 ; x ]) ; ne a ]                 (* ~> (y + x) - a *)

       | (SLScalar (XPlus, a, x), _)                                      (* (a + x) + y *)
	 | (SRScalar (XPlus, x, a), _) ->                                 (* (x + a) + y *)
	  rs XPlus [ XOp (XPlus, [ x ; e2 ]) ; ne a ]                  (* ~> (x + y) + a *)

       | (_, SLScalar (XPlus, a, x))                                      (* y + (a + x) *)
	 | (_, SRScalar (XPlus, x, a)) ->                                 (* y + (x + a) *)
	  rs XPlus [ XOp (XPlus, [ e1 ; x ]) ; ne a ]                  (* ~> (x + y) + a *)

       | (SRScalar (XMult, x, a), _)
	 | (SLScalar (XMult, a, x), _) when a#equal (mkNumerical (-1)) ->
	  rs XMinus [ e2 ; x ]                                  (* (-1 * x) + z ~> z - x *)

       | (_, SRScalar (XMult, x, a))
	 | (_, SLScalar (XMult, a, x)) when a#equal (mkNumerical (-1)) ->
	  rs XMinus [ e1 ; x ]                                  (* z + (-1 * x) ~> z - x *)
	 
       | (SLScalar (XMult, a, XVar u), 
	  SLScalar (XMult, b, XVar v)) ->
	  if u#equal v                                              (* (a * u) + (b * u) *)
	  then
	    sim_expr true (XOp (XMult, [ ne (a#add b) ; XVar u]))        (* ~> (a+b) * u *)
	  else
	    default ()
	 
       | _ -> default ()

and reduce_minus m e1 e2 = 
  let default = (m, XOp (XMinus, [e1 ; e2])) in
  let ne n = num_constant_expr n in   
  let rs op args = sim_expr true (XOp (op, args)) in
  if is_zero e2 then (true, e1)                           (* x - 0 = x *)
  else if syntactically_equal e1 e2 
  then
    (true, zero_constant_expr)                            (* x - x = 0 *)
  else if is_random e1 then (true, random_constant_expr)
  else if is_random e2 then (true, random_constant_expr)
  else
    match (e1, e2) with
    | (XOp (XPlus, [ee1 ; ee2]), ee3) when syntactically_equal ee1 ee3 ->  (* (x+y)-x ~> y *)
       sim_expr true ee2
    | (XOp (XPlus, [ee1 ; XVar v1]), XVar v2) when v1#equal v2 ->          (* (x+y)-y -> x *)
       sim_expr true ee1
    | (XOp (XMinus, [XVar v1; ee2]), XVar v2) when v1#equal v2 ->         (* (x-y)-x -> -y *)
       sim_expr true (XOp (XNeg, [ee2]))
      
    | (XOp (XPlus, [ XOp (XPlus, [ XVar v1 ; ee1 ]) ; ee2 ]), XVar v2) when v1#equal v2 ->
       sim_expr true (XOp  (XPlus, [ ee1 ; ee2 ]))                 (* ((x+y)+z) - x -> y+z *)
    | (XOp (XPlus, [ XOp (XPlus, [ ee1 ; XVar v1 ]) ; ee2 ]), XVar v2) when v1#equal v2 ->
       sim_expr true (XOp (XPlus, [ ee1 ; ee2 ]))                  (* ((x+y)+z) - y -> x+z *)
    | (XOp (XPlus, [ XOp (XMinus, [ XVar v1 ; ee1 ]) ; ee2 ]), XVar v2) when v1#equal v2 ->
       sim_expr true (XOp (XPlus, [ XOp (XNeg, [ ee1 ]) ; ee2 ])) (* ((x-y)+z) - x -> -y+z *)
    | (XOp (XPlus, [ ee1 ; XOp (XPlus, [ ee2 ; XVar v1 ])]), XVar v2) when v1#equal v2 ->
       sim_expr true (XOp (XPlus, [ ee1 ; ee2 ]))                  (* (x+(y+z)) - z -> x+y *)
      
    | (XOp (XMinus, [ XOp (XPlus, [ XVar v1 ; ee1 ]) ; ee2 ]), XVar v2) when v1#equal v2 ->
       sim_expr true (XOp (XMinus, [ ee1 ; ee2 ]))                 (* ((x+y)-z) - x -> y-z *)
    | (XOp (XMinus, [ XOp (XPlus, [ ee1 ; XVar v1 ]) ; ee2 ]), XVar v2) when v1#equal v2 ->
       sim_expr true (XOp (XMinus, [ ee1 ; ee2 ]))                 (* ((x+y)-z) - y -> x-z *)
    | _ ->
       match (get_struct e1, get_struct e2) with
       | (SConst a, SConst b) ->                                                  (* a - b *)
	  (true, ne (a#sub b))    
	 
       | (SLBRange a, SConst b) ->                             (* [a,_] - b  ~>  [(a-b),_] *)
	  (true, XOp (XNumRange, [ ne (a#sub b) ; unknown_int_constant_expr]))
         
       | (SConst a, SLScalar (XPlus, b, x))                                 (* a - (b + x) *)
	 | (SConst a, SRScalar (XPlus, x, b))                               (* a - (x + b) *)
	 | (SLScalar (XMinus, a, x), SConst b) ->                           (* (a - x) - b *)
	  rs XMinus [ ne (a#sub b) ; x ]                                   (* ~> (a-b) - x *)
	 
       | (SLScalar (XPlus, a, x), SConst b)                                 (* (a + x) - b *)
	 | (SRScalar (XPlus, x, a), SConst b)                               (* (x + a) - b *)
	 | (SConst a, SLScalar (XMinus, b, x)) ->                           (* a - (b - x) *)
	  rs XPlus [ x ; ne (a#sub b) ]                                    (* ~> x + (a-b) *)
	 
       | (SConst a, SRScalar (XMinus, x, b)) ->                             (* a - (x - b) *)
	  rs XMinus [ ne (a#add b) ; x ]                                   (* ~> (a+b) - x *)
	 
       | (SRScalar (XMinus, x, a), SConst b) ->                             (* (x - a) - b *)
	  rs XMinus [ x ; ne (a#add b) ]                                   (* ~> x - (a+b) *)
         
       | (SLScalar (XPlus, a, x), _)                                        (* (a + x) - y *)
	 | (SRScalar (XPlus, x, a), _) ->                                   (* (x + a) - y *)
	  rs XPlus [ XOp (XMinus, [ x ; e2 ]) ; ne a ]                   (* ~> (x - y) + a *)
         
       | (SRScalar (XMinus, x, a), _) ->                                    (* (x - a) - y *)
	  rs XMinus [ XOp (XMinus, [ x ; e2 ]) ; ne a ]                  (* ~> (x - y) - a *)

       | (_, SRScalar (XPlus, x, a))
	 | (_, SLScalar (XPlus, a, x)) ->                                   (* y - (a + x) *)
	  rs XMinus [ XOp (XMinus, [ e1 ; x ]) ; ne a ]                  (* ~> (y - x) - a *)

       | (_, SLScalar (XMinus, a, x)) ->                                    (* y - (a - x) *)
	  rs XMinus [ XOp (XPlus, [ e1 ; x ]) ; ne a ]                   (* ~> (y + x) - a *)

       | (_, SRScalar (XMinus, x, a)) ->                                    (* y - (x - a) *)
	  rs XPlus [ XOp (XMinus, [ e1 ; x ]) ; ne a ]                   (* ~> (y - x) + a *)

       | (_, SRScalar (XMult, x, a))                                       (* y - (-1 * x) *)
	 | (_, SLScalar (XMult, a, x)) when a#equal (mkNumerical (-1)) ->
	  rs XPlus [ e1 ; x ]                                                  (* ~> y + x *)

       | (SLScalar (XMult, a, XVar u), 
	  SLScalar (XMult, b, XVar v)) ->
	  if u#equal v                                                (* (a * u) - (b * u) *)
	  then
	    rs XMult [ ne (a#sub b) ; XVar u ]                             (* ~> (a-b) * u *)
	  else
	    default
       | _ -> 
	  default 
				
and reduce_mult m e1 e2 = 
  let default = (m, XOp (XMult, [e1 ; e2])) in
  let ne n = num_constant_expr n in
  let rs op args = sim_expr true (XOp (op, args)) in
  if (is_zero e1) || (is_zero e2)
  then
    (true, zero_constant_expr)                            (* x * 0 = 0 * x = 0 *)
  else if is_one e1
  then
    (true, e2)                                                    (* 1 * x = x *)
  else if is_one e2
  then
    (true, e1)                                                    (* x * 1 = x *)
  else if is_random e1 then (true, random_constant_expr)
  else if is_random e2 then (true, random_constant_expr)
  else
    match (get_struct e1, get_struct e2) with
    | (SConst a, SConst b) ->                                         (* a * b *)
       (true, ne (a#mult b))

    | (SRange (a,b), SConst c) ->                                 (* [a,b] * c *)
       rs XNumRange [ne (a#mult c); ne (b#mult c)]             (* ~> [a*c,b*c] *)
      
    | (SLBRange a, SConst c) ->                                   (* [a,_] * c *)
       rs XNumRange [ ne (a#mult c); unknown_int_constant_expr ]  (* ~> [a*c,> *)
      
    | (SRScalar (XMinus, x, a), SConst b) ->                    (* (x - a) * b *)
       let p = XOp (XMult, [ num_constant_expr b ; x ]) in                     
       rs XMinus [ p ; ne (a#mult b) ]                       (* ~> (b*x - a*b) *)

    | (SConst a, SRScalar (XMinus, x, b)) ->                     (* a * (x -b) *)
       let p = XOp (XMult, [ num_constant_expr a  ; x ]) in
       rs XMinus [ p ; ne (a#mult b) ]                       (* -> (a*x - a*b) *)
       
    | (SConst a, SLScalar (XPlus, b, x)) ->     (* a * (b + x)  -> a * x + a*b *)
       rs XPlus [ (XOp (XMult, [ ne a ; x ])) ; ne (a#mult b) ]
    | (SConst a, SLScalar (XMult, b, x))                        (* a * (b * x) *)
      | (SConst a, SRScalar (XMult, x ,b))                      (* a * (x * b) *)
      | (SLScalar (XMult, b, x), SConst a)                      (* (b * x) * a *)
      | (SRScalar (XMult, x, b), SConst a) ->                   (* (x * b) * a *)
       rs XMult [ne (a#mult b) ; x]                            (* ~> (a*b) * x *)
      
    | (SConst a, SLScalar (XDiv, b, x))                         (* a * (b / x) *)
      | (SLScalar (XDiv, a, x), SConst b) ->                    (* (a / x) * b *)
       rs XDiv [ne (a#mult b) ; x]                             (* ~> (a*b) / x *)
      
    | (SConst a, SRScalar (XDiv, x, b))                         (* a * (x / b) *)
      | (SRScalar (XDiv, x, b), SConst a)                       (* (x / b) * a *)
	 when divides b a ->
       rs XMult [ne (a#div b) ; x]                             (* ~> (a/b) * x *)

    | (_, SConst a) -> rs XMult [ e2 ; e1 ]                  (* x * a -> a * x *)
      
    | _ -> default
	 
				
and reduce_div m e1 e2 = 
  let default = (m, XOp (XDiv, [e1 ; e2])) in
  let ne n = num_constant_expr n in
  let rs op args = sim_expr true (XOp (op, args)) in
  if (is_zero e1)
  then
    (true, zero_constant_expr)                                          (* 0 / x = 0 *)
  else if is_one e2
  then
    (true, e1)                                                          (* x / 1 = x *)
  else if is_zero e2
  then default                                                  (* x / 0 ~~> warning *)
  else
    match (e1,e2) with
    | (XOp (XPlus, [ ee1 ; ee2 ]), c) when is_intconst c ->          (*  (x + y)/c -> x/c + y/c *)
       sim_expr true (XOp (XPlus, [ XOp (XDiv, [ ee1 ; c ]) ; XOp (XDiv, [ ee2 ; c ]) ]))
    | _ ->
       match (get_struct e1, get_struct e2) with
	 (SConst a, SConst b) ->                                              (* a/b *)
	 (true, ne (a#div b)) 
       | (SLScalar (XMult, a, x), SConst b)                            (* (a * x)/b  *)             
	 | (SRScalar (XMult, x, a), SConst b)                          (* (x * a)/b  *)
	    when divides b a ->
	  rs XMult [ ne (a#div b) ; x ]                              (* ~> (a/b) * x *)
	 
       | _ -> default
	    
and reduce_mod m e1 e2 = 
  let default = (m, XOp (XMod, [e1 ; e2])) in
  let ne n = num_constant_expr n in
  if (is_zero e1)
  then
    (true, zero_constant_expr)                            (* 0 % x = 0 *)
  else if is_one e2
  then
    (true, zero_constant_expr)                            (* x % 1 = 0 *)
  else if is_zero e2
  then default                                            (* x % 0 ~~> warning *)
  else
    match (get_struct e1, get_struct e2) with
    | (SConst a, SConst b) ->                             (* a%b *)
       let result = mkNumerical_big (mod_big_int a#getNum b#getNum) in
       (true, ne result)
    | (_, SConst b) when b#geq numerical_zero ->
       let ub = b#sub numerical_one in
       (true, XOp (XNumRange, [ zero_constant_expr ; num_constant_expr ub ]))
    | _ -> default


and reduce_lt m e1 e2 = 
  let default = (m, XOp (XLt, [e1 ; e2])) in
  let ne n = num_constant_expr n in
  let be b = (true, XConst (BoolConst b)) in
  let rand = (true, XConst (XRandom)) in
  let rs op args = sim_expr true (XOp (op, args)) in

  match (e1,e2) with
    (XVar v, XOp (XPlus, [ XVar w ; XConst (IntConst n) ])) 
       when v#equal w && n#gt numerical_zero ->
    be true

  | (XVar v, XOp (XPlus, [ XVar w  ; e' ])) 
       when v#equal w ->
     (true, XOp ( XGt, [ e' ; zero_constant_expr ]))

  | _ ->
     match (get_struct e1, get_struct e2) with
     | (SConst a, SConst b) ->                             (* a < b *)
        be (a#lt b)

     | (SRange(a,b), SConst c) ->                          (* [a,b] < c *)
	if b#lt c then be true                               (* b <  c ~> true  *)
	else if a#geq c then be false                        (* a >= c ~> false *)
	else rand                                            (*  ~> ? *)

     | (SConst c, SRange(a,b)) ->                          (* c < [a,b] *)
	if c#lt a then be true                               (* c <  a ~> true  *)
        else if c#geq b then be false                        (* c >= b ~> false *)
	else rand                                            (*  ~> ? *)
       
     | (SConst a, SLScalar (XPlus, b, x))                  (* a < b + x *)
       | (SConst a, SRScalar (XPlus, x ,b))                  (* a < x + b *)
       | (SLScalar (XMinus, a, x), SConst b) ->              (* a - x < b *)
	rs XGt [x ; ne (a#sub b)]                                 (* ~> x > (a-b) *)

     | (SRScalar (XMinus, x, a), SConst b) ->              (* x + a < b *)
	rs XLt [ x ; ne (a#add b) ]                               (* ~> x < (a+b) *)

     | (SConst a, SLScalar (XMinus, b, x))                 (* a < b - x *)
       | (SLScalar (XPlus, a, x), SConst b)                  (* a + x < b *)
       | (SRScalar (XPlus, x, a), SConst b) ->               (* x + a < b *)
	rs XLt [x ; ne (b#sub a)]                                 (* ~> x < (b-a) *)

     | (SConst a, SRScalar (XMinus, x, b)) ->              (* a < x - b *)
	rs XGt [x ; ne (a#add b)]                                 (* ~> x > (a+b) *)

     | (SConst a, SLScalar (XMult, b, x))                  (* a < b * x *)
       | (SConst a, SRScalar (XMult, x, b))                  (* a < x * b *)
	  when divides b a ->
	let op = if neg_num b then XLt else XGt in                (* b < 0 ~> [ < ] *)
	rs op [x ; ne (a#div b)]                                (* ~> x [<|>] a/b *)

     | (SLScalar (XMult, a, x), SConst b)                  (* a * x < b *)
       | (SRScalar (XMult, x, a), SConst b)                  (* x * a < b *)
	  when divides a b ->
	let op = if neg_num a then XGt else XLt in                (* a < 0 ~> [ > ] *)
	rs op [x ; ne (b#div a)]                                (* ~> x [<|>] b/a *)

     | (SConst a, SRScalar (XDiv, x, b)) ->                (* a < x / b *)
	if zero_num b                                     (* b=0 ~~> warning *)
	then default 
	else
	  let op = if neg_num b then XLt else XGt in              (* b < 0 ~> [ < ] *)
	  rs op [x ; ne (a#mult b)]                             (* ~> x [<|>] a*b *)
     | _ -> default

and reduce_le m e1 e2 = 
  let default = (m, XOp (XLe, [e1 ; e2])) in
  let ne n = num_constant_expr n in
  let be b = (true,XConst (BoolConst b)) in
  let rand = (true,XConst XRandom) in
  let rs op args = sim_expr true (XOp (op, args)) in
  if syntactically_equal e1 e2 then
    be true
  else
    match (e1,e2) with
    | (XOp (XPlus, [x ; y]), z) when syntactically_equal y z ->
       rs XLe [ x ; zero_constant_expr]                     (* (x+y) <= y ~> x <= 0 *)
    | (XOp (XPlus, [e; XVar v]), XOp (XPlus, [XVar w ; e'])) when v#equal w  ->
       rs XLe [ e ; e' ]                                (* (x+v) <= (v+y) ~> x <= y *)
    | (XOp (XPlus, [el ; x]), XOp (XPlus, [er ; y])) when syntactically_equal el er ->
       rs XLe [ x ; y ]                                 (* (e+x) <= (e+y) ~> x <= y *)
    | (XOp (XMinus, [ ee1 ; ee2 ]), ee3) when syntactically_equal ee1 ee3 ->
       rs XGe [ ee2 ; zero_constant_expr ]                 (* (x-y) <= x  ~> y >= 0 *)
    | _ ->  

       match (get_struct e1, get_struct e2) with
	 
       | (SConst a, SConst b) ->                             (* a <= b *)
	  be (a#leq b)
	 
       | (SRange(a,b), SConst c) ->                          (* [a,b] <= c *)
	  if b#leq c then be true                              (* b <= c ~> true  *)
	  else if a#gt c then be false                         (* a >  c ~> false *)
	  else rand                                            (*  ~> ? *)

       | (SConst a, SLBRange b) ->                           (* a <= [b,_] *)
	  if a#leq b then be true                               (* a <= b ~> true *)
	  else rand                                             (*  ~> ? *)
	 
       | (SConst c, SRange(a,b)) ->                          (* c <= [a,b] *)
	  if c#leq a then be true                              (* c <= a ~> true  *)
	  else if c#gt b then be false                         (* c > b  ~> false *)
	  else rand                                            (*  ~> ? *)
	 
       | (SUBRange b, SConst c) ->                             (* [_,b] <= c *)
	  if b#leq c then be true                              (* b <= c ~> true *)
	  else rand                                            (*  ~> ? *)
	 
       | (SLBRange a, SConst c) ->                           (* [a,_] <= c *)
	  if a#gt c then be false                              (* a > c ~> false *)
	  else rand                                            (*  ~> ? *)
	 
       | (SConst a, SLScalar (XPlus, b, x))                  (* a <= b + x *)
	 | (SConst a, SRScalar (XPlus, x, b))                  (* a <= x + b *)
	 | (SLScalar (XMinus, a, x), SConst b) ->              (* a - x <= b *)
	  rs XGe [x ; ne (a#sub b)]                                (* ~> x >= (a-b) *)
	 
       | (SRScalar (XPlus,x,a), SRScalar (XPlus,y,b)) ->     (* x + a <= y + b *)
	  if a#equal b then        
	    rs XLe [ x ; y ]                                       (* a=b ~> x <= y *)
	  else
	    rs XLe [ XOp (XMinus, [x;y]) ; ne (b#sub a)]           (* ~> x-y <= b-a *)
	 
       | (SConst a, SLScalar (XMinus, b, x))                 (* a <= b - x *)
	 | (SLScalar (XPlus, a, x), SConst b)                  (* a + x <= b *)
	 | (SRScalar (XPlus, x, a), SConst b) ->               (* x + a <= b *)
	  rs XLe [x ; ne (b#sub a)]                                 (* ~> x <= (b-a) *)
	 
       | (SConst a, SRScalar (XMinus, x, b)) ->              (* a <= x - b *)
	  rs XGe [x ; ne (a#add b)]                                 (* ~> x >= (a+b) *)
	 
       | (SLScalar (XMinus, a, x),                           (* a - x <= y + b *)
	  SRScalar (XPlus, y, b))
	 | (SLScalar (XMinus, a, x),                           (* a - x <= b + y *)
	    SLScalar (XPlus, b, y)) ->
	  rs XGe [ XOp (XPlus, [x;y]) ; ne (a#sub b)]               (* ~> x+y >= (a-b) *)
	 
       | (SConst a, SLScalar (XMult, b, x))                  (* a <= b * x *)
	 | (SConst a, SRScalar (XMult, x, b))                  (* a <= x * b *)
	    when divides b a ->
	  let op = if neg_num b then XLe else XGe in                (* b < 0 ~> [ <= ] *)
	  rs op [x ; ne (a#div b)]                                (* ~> x [<=|>=] a/b *)
	  
       | (SConst a, SRScalar (XDiv, x, b)) ->                (* a <= x / b *)
	  if zero_num b                                     (* b=0 ~~> warning *)
	  then default
	  else
	    let op = if neg_num b then XLe else XGe in            (* b < 0 ~> [ <= ] *)
	    rs op [x ; ne (a#mult b)]                           (* ~> x [ <=|>= ] a*b *)
       | _ -> default
	    
and reduce_gt m e1 e2 = 
  let default = (m, XOp (XGt, [e1 ; e2])) in
  let ne n = num_constant_expr n in
  let be b = (true,XConst (BoolConst b)) in
  let rand = (true,XConst XRandom) in
  let rs op args = sim_expr true (XOp (op, args)) in
  match (get_struct e1, get_struct e2) with
  | (SConst a, SConst b) ->                             (* a > b *)
     be (a#gt b)

  | (SRange(a,b), SConst c) ->                          (* [a,b] > c *)
     if a#gt c then be true                               (* a >  c ~> true  *)
     else if b#leq c then be false                        (* b <= c ~> false *)
     else rand                                            (*  ~> ? *)

  | (SLBRange a, SConst c) ->                           (* [a,_] > c *)
     if a#gt c then be true                               (* a > c ~> true *)
     else rand                                            (*  ~> ? *)

  | (SConst c, SRange(a,b)) ->                          (* c > [a,b] *)
     if c#gt b then be true                               (* c >  b ~> true  *)
     else if c#leq a then be false                        (* c <= a ~> false *)
     else rand                                            (*  ~> ? *)

  | (SConst a, SLScalar (XPlus, b, x))                  (* a > b + x *)
    | (SConst a, SRScalar (XPlus, x, b))                  (* a > x + b *)
    | (SLScalar (XMinus, a, x), SConst b) ->              (* a - x > b *)
     rs XLt [x ; ne (a#sub b)]                                 (* ~> x < (a-b) *)

  | (SConst a, SLScalar (XMinus, b, x))                 (* a > b - x *)
    | (SLScalar (XPlus, a, x), SConst b)                  (* a + x > b *)
    | (SRScalar (XPlus, x, a), SConst b) ->               (* x + a > b *)
     rs XGt [x ; ne (b#sub a)]                                 (* ~> x > (b-a) *)

  | (SConst a, SRScalar (XMinus, x, b)) ->              (* a > x - b *)
     rs XLt [x ; ne (a#add b)]                                 (* ~> x < (a+b) *)

  | (SConst a, SLScalar (XMult, b, x))                  (* a > b * x *)
    | (SConst a, SRScalar (XMult, x, b))                  (* a > x * b *)
       when divides b a ->
     let op = if neg_num b then XGt else XLt in                (* b < 0 ~> [ > ] *)
     rs op [x ; ne (a#div b)]                                (* ~> x [<|>] a/b *)

  | (SConst a, SRScalar (XDiv, x, b)) ->                (* a > x / b *)
     if zero_num b                                     (* b=0 ~~> warning *)
     then default
     else
       let op = if neg_num b then XGt else XLt in              (* b < 0 ~> [ > ] *)
       rs op [x ; ne (a#mult b)]                             (* ~> x [<|>] a*b *)
  | _ -> default

and reduce_ge m e1 e2 = 
  let default = (m, XOp (XGe, [e1 ; e2])) in
  let ne n = num_constant_expr n in
  let be b = (true,XConst (BoolConst b)) in
  let rand = (true,XConst XRandom) in
  let rs op args = sim_expr true (XOp (op, args)) in
  match (e1, e2) with
    (XVar v1, XVar v2) when v1#equal v2 ->
    (true, XConst (BoolConst true))                       (* x >= x *)
  | (XOp (XPlus, [XVar x ; XConst (IntConst i) ]), XVar y) 
    | (XOp (XPlus, [XConst (IntConst i) ; XVar x ]), XVar y) when x#equal y ->
     (true, XConst (BoolConst (i#geq numerical_zero)))     (* x + i >= x ~> i >= 0 *)
  | (XVar x, XOp (XPlus, [ XConst (IntConst i) ; XVar y])) 
    | (XVar x, XOp (XPlus, [ XVar y ; XConst (IntConst i)])) when x#equal y ->
     (true, XConst (BoolConst (i#leq numerical_zero)))     (* x >= i + x -> i <= 0 *)
  | _ ->
     match (get_struct e1, get_struct e2) with
     | (SConst a, SConst b) ->                             (* a >= b *)
	be (a#geq b)

     | (SRange(a,b), SConst c) ->                          (* [a,b] >= c *)
	if a#geq c then be true 
	else if b#lt c then be false
	else rand

     | (SLBRange a, SConst c) ->
	if a#geq c then be true
	else rand

     | (SConst a, SLScalar (XPlus, b, x))                  (* a >= b + x *)
       | (SConst a, SRScalar (XPlus, x, b))                  (* a >= x + b *)
       | (SLScalar (XMinus, a, x), SConst b) ->              (* a - x >= b *)
	rs XLe [x ; ne (a#sub b)]                                 (* ~> x <= (a-b) *)

     | (SRScalar (XMinus, x, a), SConst b) ->              (* x - a >= b *)
	rs XGe [x ; ne (a#add b)]                                 (* ~> x >= (a+b) *)

     | (SConst a, SLScalar (XMinus, b, x))                 (* a >= b - x *)
       | (SLScalar (XPlus, a, x), SConst b)                  (* a + x >= b *)
       | (SRScalar (XPlus, x, a), SConst b) ->               (* x + a >= b *)
	rs XGe [x ; ne (b#sub a)]                                 (* ~> x >= (b-a) *)

     | (SConst a, SRScalar (XMinus, x, b)) ->              (* a >= x - b *)
	rs XLe [x ; ne (a#add b)]                                 (* ~> x <= (a+b) *)

     | (SConst a, SLScalar (XMult, b, x))                  (* a >= b * x *)
       | (SConst a, SRScalar (XMult, x, b))                  (* a >= x * b *)
	  when divides b a ->
	let op = if neg_num b then XGe else XLe in              (* b < 0 ~> [ >= ] *)
	rs op [x ; ne (a#div b)]                              (* ~> x [<=|>=] a/b *)

     | (SLScalar (XMult, b, x), SConst a)                   (* b * x >= a *)
       | (SRScalar (XMult, x, b), SConst a)                   (* x * b >= a *)
	  when divides b a ->
	let op = if neg_num b then XLe else XGe in
	rs op [ x ; ne (a#div b)]

     | (SConst a, SRScalar (XDiv, x, b)) ->                (* a >= x / b *)
	if zero_num b                                     (* b=0 ~~> warning *)
	then default
	else
	  let op = if neg_num b then XGe else XLe in            (* b < 0 ~> [ >= ] *)
	  rs op [x ; ne (a#mult b)]                           (* ~> x [ <=|>= ] a*b *)

     | (SRScalar (XDiv, x, a), SConst b)                    (* x/a >= 0 with a > 0 ~~> x >= 0 *)
	  when zero_num b && a#gt numerical_zero ->
	rs XGe [ x ; ne b ]
       
     | _ -> default


and reduce_eq m e1 e2 = 
  let default = (m, XOp (XEq, [e1 ; e2])) in
  let ne n = num_constant_expr n in
  let be b = XConst (BoolConst b) in
  let rs op args = sim_expr true (XOp (op, args)) in
  match (get_struct e1, get_struct e2) with
  | (SConst a, SConst b) ->                             (* a = b *)
     (true, be (a#equal b))
    
  | (SConst a, SLScalar (XPlus, b, x))                  (* a = b + x *)
    | (SConst a, SRScalar (XPlus, x, b))                  (* a = x + b *)
    | (SLScalar (XMinus, a, x), SConst b) ->              (* a - x = b *)
     rs XEq [x ; ne (a#sub b)]                                 (* ~> x = a-b *)

  | (SConst a, SLScalar (XMinus, b, x))                 (* a = b - x *)
    | (SLScalar (XPlus, a, x), SConst b)                  (* a + x = b *)
    | (SRScalar (XPlus, x, a), SConst b) ->               (* x + a = b *)
     rs XEq [x ; ne (b#sub a)]                                 (* ~> x = b-a *)

  | (SConst a, SRScalar (XMinus, x, b))                 (* a = x - b *)
    | (SRScalar (XMinus, x, a), SConst b) ->              (* x - a = b *)
     rs XEq [x ; ne (a#add b)]                                 (* ~> x = a+b *)

  | (SConst a, SLScalar (XMult, b, x))                  (* a = b * x *)
    | (SConst a, SRScalar (XMult, x, b))                  (* a = x * b *)
    | (SLScalar (XMult, b, x), SConst a)                  (* b * x = a *)
    | (SRScalar (XMult, x, b), SConst a) ->               (* x * b = a *)
     if zero_num a && zero_num b
     then (true, be true)                                 (* a=0, b=0  ~~> true *)
     else if zero_num b
     then (true, be false)                                (* a<>0, b=0 ~~> false *)
     else 
       rs XEq [x ; ne (a#div b)]                          (* b<>0 ~~> x = a/b *)

  | (SConst a, SRScalar (XDiv, x, b))                   (* a = x / b *)
    | (SRScalar (XDiv, x, b), SConst a) ->                (* x / b = a *)
     if zero_num b
     then default                                      (* b=0 ~~> warning *)
     else
       rs XEq [x ; ne (a#div b) ]                    (* b<>0 ~~> x = a/b *)

  | _ -> default

and reduce_ne m e1 e2 = 
  let default = (m, XOp (XNe, [e1 ; e2])) in
  let ne n = num_constant_expr n in
  let be b = XConst (BoolConst b) in
  let rs op args = sim_expr true (XOp (op, args)) in
  match (get_struct e1, get_struct e2) with
  | (SConst a, SConst b) ->                                         (* a /= b *)
     (true, be (not (a#equal b)))

  | (SConst a, SLScalar (XPlus, b, x))                          (* a /= b + x *)
    | (SConst a, SRScalar (XPlus, x, b))                        (* a /= x + b *)
    | (SLScalar (XMinus, a, x), SConst b) ->                    (* a - x /= b *)
     rs XNe [x ; ne (a#sub b)]                                 (* ~> x /= a-b *)

  | _ ->
     match (e1,get_struct e2) with                         
     | (XOp (XLt, _), SConst a)
       | (XOp (XGt, _), SConst a)
       | (XOp (XLe, _), SConst a)
       | (XOp (XGe, _), SConst a) when zero_num a ->           (* (x1 op x2) <> 0 *)
        (true, e1)                                                (* -> (x1 op x2) *)

     | _ -> default


and reduce_logical_not m e =
  let default = (m, XOp (XLNot, [e])) in
  if is_true e then (true, false_constant_expr)
  else if is_false e then (true, true_constant_expr)
  else if is_random e then (true, random_constant_expr)
  else match e with
  | XOp (XLNot, [e1]) -> (true, e1)
  | XOp (XLAnd, [ e1 ; e2 ]) -> 
      (true, XOp (XLOr, [ XOp (XLNot, [e1]) ; XOp (XLNot, [e2]) ]))
  | XOp (XLOr,  [ e1 ; e2 ]) ->
      (true, XOp (XLAnd, [ XOp (XLNot, [e1]) ; XOp (XLNot, [e2]) ]))
  | XOp (XGe, [ e1 ; e2 ]) -> (true, XOp (XLt, [ e1 ; e2 ]))
  | XOp (XGt, [ e1 ; e2 ]) -> (true, XOp (XLe, [ e1 ; e2 ]))
  | XOp (XLe, [ e1 ; e2 ]) -> (true, XOp (XGt, [ e1 ; e2 ]))
  | XOp (XLt, [ e1 ; e2 ]) -> (true, XOp (XGe, [ e1 ; e2 ]))
  | XOp (XEq, [ e1 ; e2 ]) -> (true, XOp (XNe, [ e1 ; e2 ]))
  | XOp (XNe, [ e1 ; e2 ]) -> (true, XOp (XEq, [ e1 ; e2 ]))
  | _ -> default

and reduce_bor m e1 e2 =
  let default = (m, XOp (XBOr, [e1 ; e2])) in
  if is_zero e1 then (true, e2)
  else if is_zero e2 then (true, e1)
  else default

and reduce_or m e1 e2 =
  let default = (m, XOp (XLOr, [e1 ; e2])) in
  if is_true e1 || is_true e2 then (true, true_constant_expr)
  else if is_false e1 then (true, e2)
  else if is_false e2 then (true, e1)
  else match (e1,e2) with
       | (XConst XRandom, XOp (XLOr, [XConst XRandom; b]))
         | (XConst XRandom, XOp (XLOr, [b; XConst XRandom]))
         | (XOp (XLOr, [XConst XRandom; b]), XConst XRandom)
         | (XOp (XLOr, [b; XConst XRandom]), XConst XRandom) ->
	  (true, XOp (XLOr, [b ; XConst XRandom]))
       | (XOp (XLe, [ x ; XOp (XNumJoin, [ y ; z ]) ]),
	  XOp (XSubset, [ s ; t ])) 
	    when (is_zero y) ->
	  (true, XOp (XLe, [ x ; z]))
       | _ ->
	  default

and reduce_bitwiseand m e1 e2 =
  let default = (m, XOp (XBAnd, [ e1 ; e2 ])) in
  let ne n = num_constant_expr n in
  try
    match get_struct e2 with
    | SConst b ->
       if b#is_zero then
         (true, ne numerical_zero)
       else
         default
    | _ -> default
  with
  | CHFailure p ->
     begin
       chlog#add "simplification"
                 (LBLOCK [ STR "bitwise and:" ; xpr_to_pretty e1 ; STR ", " ;
                           xpr_to_pretty e2 ; STR ": " ; p ]) ;
       default
     end

and reduce_shiftleft m e1 e2 =
  let default = (m, XOp (XShiftlt, [e1 ; e2])) in
  let ne n = num_constant_expr n in
  try
    match (get_struct e1, get_struct e2) with
    | (SConst a, SConst b) ->
       if b#is_zero then (true,e1)
       else if b#lt numerical_zero || b#geq (mkNumerical 32)
       then default
       else
         (try
            let ai = a#toInt in
            let bi = b#toInt in
            let shifted = ai lsl bi in
            (true, ne (mkNumerical shifted))
          with
            Failure _ -> default)
    | _ -> default
  with
  | CHFailure p ->
     begin
       chlog#add "simplification"
                 (LBLOCK [ STR "reduce shift left: " ; xpr_to_pretty e1 ; STR ", " ;
                           xpr_to_pretty e2 ; STR ": " ; p ]) ;
       default
     end

and reduce_shiftright m e1 e2 =
  let default = (m, XOp (XShiftrt, [ e1 ; e2])) in
  let ne n = num_constant_expr n in
  let ni i = num_constant_expr (mkNumerical i) in
  try
    match (get_struct e1, get_struct e2) with
    | (SConst a, SConst b) ->
       if b#is_zero then (true,e1)
       else if b#lt numerical_zero || b#geq (mkNumerical 32)
       then default
       else if a#lt numerical_zero
       then default
       else
         (try
            let ai = a#toInt in
            let bi = b#toInt in
            let shifted = ai lsr bi in
            (true, ne (mkNumerical shifted))
          with
            Failure _ -> default)
    | (_, SConst b) ->
       if b#is_zero then (true, e1)
       else if b#lt numerical_zero || b#geq (mkNumerical 32)
       then default
       else
         (try
            let bi = b#toInt in
            match bi with
            | 1 -> (true, XOp (XDiv, [ e1; ni 2 ]))
            | 2 -> (true, XOp (XDiv, [ e1; ni 4 ]))
            | 3 -> (true, XOp (XDiv, [ e1; ni 8 ]))
            | 4 -> (true, XOp (XDiv, [ e1; ni 16 ]))
            | _ -> default
          with
            Failure _ -> default)
    | _ -> default
  with
  | CHFailure p ->
     begin
       chlog#add "simplification"
                 (LBLOCK [ STR "reduce shift right: " ; xpr_to_pretty e1 ; STR ", " ;
                           xpr_to_pretty e2 ; STR ": " ; p ]) ;
       default
     end
         
and reduce_disjoint m e1 e2 =
  let default = (m, XOp (XDisjoint,  [ e1 ; e2])) in
  let be b = XConst (BoolConst b) in
  match (e1,e2) with
  | (XConst XUnknownSet, _ ) 
    | (_, XConst XUnknownSet ) -> default
  | (XConst c1, XConst c2) ->
     begin
       match (c1, c2) with
       | (SymSet [s1], SymSet [s2]) -> 
	  (true, be (not (s1#equal s2)))
       | (SymSet [s1], SymSet s2) 
	 | (SymSet s2, SymSet [s1]) ->
	  let v = not (List.exists (fun s -> s1#equal s) s2) in
	  if v
	  then
	    (true, be v)   (* if it is disjoint, is it certain to be disjoint *)
	  else
	    if (List.length s2) = 1 
	    then           (* if there is only one element, it is as above *)
	      (true, be v)  
	    else           (* s2 may be an over approximation, no certainty *)
	      default
       | (SymSet s1, SymSet s2) ->
	  let v = 
	    (List.for_all
	       (fun s -> not (List.exists (fun s' -> s#equal s') s2)) s1) in
	  if v
	  then
	    (true, be v)
	  else if (List.length s1) = 1 && (List.length s2) = 1
	  then
	    (true, be v)
	  else
	    default
       | _ -> default
     end
  | _ -> default

and reduce_subset m e1 e2 =
  let default = (m, XOp (XSubset, [ e1 ; e2 ])) in
  let be b = XConst (BoolConst b) in
  match (e1,e2) with
  | (XConst XUnknownSet, _)
    | (_, XConst XUnknownSet) -> default
  | (XConst c1, XConst c2) ->
     begin
       match (c1,c2) with
	 (SymSet [s1], SymSet [s2]) -> (true, be (s1#equal s2))
       | (SymSet [s1], SymSet s2) ->
	  let v = List.exists (fun s' -> s1#equal s') s2 in
	  (true, be v)
       | _ -> default
     end
  | _ -> default


and reduce_binary_numjoin m s1 s2 =
  let default = (m, XOp (XNumJoin, [s1 ; s2])) in
    if syntactically_equal s1 s2 then (true,s1) else default

and reduce_numjoin m l =
  let rec remove_duplicates l =
    match l with
    | [] -> []
    | h :: tl ->
       let rest = remove_duplicates tl in
       if List.exists (fun e -> syntactically_equal h e) rest then
	 rest
       else
	 h :: rest in
  let rl = remove_duplicates l in
  match l with
    [] -> failwith "Empty list in NumJoin"
  | [p] -> (true,p)
  | _ ->
     let m = ((List.length rl < List.length l) || m) in
     (m, XOp (XNumJoin, rl))

let simplify_expr expr:(bool * xpr_t) = 
  try
    sim_expr false expr
  with
      XSimplificationProblem p ->
	begin
	  ch_error_log#add "simplification problem" (LBLOCK [ p ]) ;
	  raise (XSimplificationProblem p)
	end

let simplify_xpr expr = let (_, s) = simplify_expr expr in s

  
let rec simple_sim_expr expr =

  let sim_reduce_plus e1 e2 =
    if is_zero e1 then e2
    else if is_zero e2 then e1
    else XOp (XPlus, [e1 ; e2]) in
  let sim_reduce_minus e1 e2 =
    if is_zero e2 then e1
    else XOp (XMinus, [e1 ; e2]) in
  let sim_reduce_mult e1 e2 =
    if is_zero e1 || is_zero e2 then zero_constant_expr
    else if is_one e1           then e2
    else if is_one e2           then e1
    else XOp (XMult, [e1 ; e2]) in
  let sim_reduce_div e1 e2 =
    if is_zero e1      then zero_constant_expr
    else if is_one e2  then e1
    else XOp (XDiv, [e1 ; e2]) in
  let sim_reduce_mod e1 e2 =
    if is_zero e1 || is_one e2 then zero_constant_expr
    else XOp (XMod, [e1 ; e2]) in
    
  match expr with
    | XOp ( op, [e1 ; e2] ) ->
	let s1 = simple_sim_expr e1 in
	let s2 = simple_sim_expr e2 in
	  begin
	    match op with
		XPlus -> sim_reduce_plus s1 s2
	      | XMinus -> sim_reduce_minus s1 s2
	      | XMult -> sim_reduce_mult s1 s2
	      | XDiv -> sim_reduce_div s1 s2
	      | XMod -> sim_reduce_mod s1 s2
	      | _ -> XOp (op, [s1 ; s2])
	  end
    | _ -> expr


let simple_simplify_expr expr:xpr_t = simple_sim_expr expr
      

