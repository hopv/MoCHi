(*
 *  CSIsat is an interpolating decision procedure for LA + EUF.
 *  This file is part of CSIsat. 
 *
 *  Copyright (C) 2007-2008  Dirk Beyer and Damien Zufferey.
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *
 *  CSIsat web page:
 *    http://www.cs.sfu.ca/~dbeyer/CSIsat/
 *)

(** *)

open   CsisatAst
(**/**)
module AstUtil     = CsisatAstUtil
module Message     = CsisatMessage
module Utils       = CsisatUtils
module SatLI       = CsisatSatLI
module SatPL       = CsisatSatPL
module SatUIF      = CsisatSatUIF
module LIUtils     = CsisatLIUtils
module NelsonOppen = CsisatNelsonOppen
module Interpolate = CsisatInterpolate
module FociParse   = CsisatFociParse
module FociPrinter = CsisatFociPrinter
module FociLex     = CsisatFociLex
(**/**)

let parse str =
  let lexbuf = Lexing.from_string str in
    FociParse.main FociLex.token lexbuf

let test_unsat_core () =
  let t1 = Eq( Application( "f", [ Application( "f", [Application( "f", [ Application( "f", [ Application( "f", [Variable "a"])])])])]), Variable "a") in
  let t2 = Eq( Application( "f", [ Application( "f", [ Application( "f", [Variable "a"])])]), Variable "a") in
  let t3 = Not( Eq ( Application ("f", [Variable "a"]), Variable "a")) in
  let t4 = ( Eq ( Variable "a", Variable "a")) in
  let f = And [t1;t2;t3;t4] in
  let core = NelsonOppen.unsat_core_for_convex_theory SatUIF.is_uif_sat f in
    Message.print Message.Normal (lazy("formula is "^(AstUtil.print f)));
    Message.print Message.Normal (lazy("unsat core is "^(AstUtil.print core)))

let test_split () =
  let t1 = Leq (Constant 1.0, Variable "x") in
  let t2 = Leq (Variable "x", Constant 2.0) in
  let t3 = Not (Eq (Application ("f",[Variable "x"]) , Application ("f",[Constant 1.0]))) in
  let t4 = Not (Eq (Application ("f",[Variable "x"]) , Application ("f",[Constant 2.0]))) in
  let f1 = And [t1;t2;t3;t4] in
  let t5 = Eq (Application ("f",[Variable "x"]) , Sum [Variable "x"; Variable "y"]) in
  let t6 = Leq (Variable "x", Sum [Variable "y"; Variable "z"]) in
  let t7 = Leq (Sum [Variable "x"; Variable "z"], Variable "y") in
  let t8 = Eq (Variable "y", Constant 1.0) in
  let f2 = And [t5;t6;t7;t8;t4] in
  let (uif1,li1,shared1,def1) = AstUtil.split_formula_LI_UIF f1 in
    Message.print Message.Normal (lazy("formula is "^(AstUtil.print f1)));
    Message.print Message.Normal (lazy("uif is "^(AstUtil.print (And uif1))));
    Message.print Message.Normal (lazy("li  is "^(AstUtil.print (And li1))));
    Message.print Message.Normal (lazy("shared vars are "^(Utils.string_list_cat ", " (List.map AstUtil.print_expr shared1))));
    Message.print Message.Normal (lazy("definitions are "^(Utils.string_list_cat ", " (List.map (fun (x,y) -> AstUtil.print (Eq (x,y))) def1))));
  let (uif2,li2,shared2,def2) = AstUtil.split_formula_LI_UIF f2 in
    Message.print Message.Normal (lazy("formula is "^(AstUtil.print f2)));
    Message.print Message.Normal (lazy("uif is "^(AstUtil.print (And uif2))));
    Message.print Message.Normal (lazy("li  is "^(AstUtil.print (And li2))));
    Message.print Message.Normal (lazy("shared vars are "^(Utils.string_list_cat ", " (List.map AstUtil.print_expr shared2))));
    Message.print Message.Normal (lazy("definitions are "^(Utils.string_list_cat ", " (List.map (fun (x,y) -> AstUtil.print (Eq (x,y))) def2))))

let test_sat_li () =
  let f1 =
    AstUtil.simplify ( List.hd (parse "& [ ~ <= 0 z  <= x z <= y x <= y 0 <= 0 + [ x y ] ]" )) in
  let f2 =
    AstUtil.simplify ( List.hd ( parse "& [  <= z 0  <= x z <= y x <= y 0 <= 0 + [ x y ] ]" )) in
  let f3 =
    AstUtil.simplify ( List.hd ( parse "& [  <= 0 x <= 0 y  <= 2 x <= 2 y <= + [ x y ] 3 ]" )) in
  let f4 =
    AstUtil.simplify ( List.hd ( parse "& [ <= 1 + [ x y ] <= -1 + [ x * -1 y]  ]" )) in
    Message.print Message.Normal (lazy("sat li for: "^(AstUtil.print f1)));
    if SatLI.is_li_sat f1 then
         Message.print Message.Normal (lazy "SAT")
    else Message.print Message.Normal (lazy "UNSAT");
    Message.print Message.Normal (lazy("sat li for: "^(AstUtil.print f2)));
    if SatLI.is_li_sat f2 then
         Message.print Message.Normal (lazy "SAT")
    else Message.print Message.Normal (lazy "UNSAT");
    Message.print Message.Normal (lazy("sat li for: "^(AstUtil.print f3)));
    if SatLI.is_li_sat f3 then
         Message.print Message.Normal (lazy "SAT")
    else Message.print Message.Normal (lazy "UNSAT");
    Message.print Message.Normal (lazy("sat li for: "^(AstUtil.print f4)));
    if SatLI.is_li_sat f4 then
         Message.print Message.Normal (lazy "SAT")
    else Message.print Message.Normal (lazy "UNSAT")

let test_unsat_liuif () =
  (*[f(x) > 0, x = y], [f(y) =< 0] *)
  let f1 = AstUtil.simplify (List.hd (parse
          "& [ ~ <= f [ x ] 0  = x y <= f [ y ] 0 ]"
     )) in
  (*[f(a) = b+5, f(f(a)) >= b+1], [f(c) = d+4, d = b+1, f(f(c)) < b+1]*)
  let f2 = AstUtil.simplify (List.hd (parse
          "& [ = f [ a ] + [ b 5 ]  <= + [ b 1 ] f [ f [ a ] ]  = f [ c ] + [ d 4 ] = d + [ b 1 ] ~ <= + [ b 1 ] f [ f [ c] ] ]"
     )) in
  (*[f(x, z) >= 1, x = y+1, z =< a, z >= b], [f(y+1, z) =< 0, a =< z, b >= z]*)
  let f3 = List.hd (parse
          "& [ <= 1 f [ x z ]  = x + [ y 1 ]  <= z a <= b z  <= f [ + [ y 1 ] z ] 0 <= a z <= z b ]"
     ) in
  (*[f(x, z) >= 1, x = y+1, z = a, z = b], [f(y+1, z) =< 0, ]*)
  let f4 = List.hd (parse
          "& [ <= 1 f [ x z ]  = x + [ y 1 ]  = z a = b z  <= f [ + [ y 1 ] z ] 0 ]"
     ) in
  (*[a =< b, a >= c, f(a) =< 1], [b =< d, c >= d, f(d) >= 2]*)
  let f5 = List.hd (parse
          "& [ <= a b  <= c a <= f [ a ] 1 <= b d <= d c <= 2 f [ d ] ]"
     ) in
  (*[f(x) >= 1], [f(y) =< -1, x =< y, x >= y]*)
  let f6 = List.hd (parse
          "& [ <= 1 f [ x ]  <= f [ y ] -1 <= y x <= x y ]"
     ) in
  (*[f(x) = 0, f(y) = 1], [x = y]*)
  let f7 = List.hd (parse
          "& [ = f [ x ] 0 = f [ y ] 1 = x y ]"
     ) in
  (*[f(x+a)=p, f(y+b) = q, a = b, p-q+z = 1], [x = y, z = 0]*)
  let f8 = List.hd (parse
          "& [ = p f [ + [ x a ] ] = q f [ + [ y b ] ] = a b = 1 + [ p * -1 q z ] = x y = z 0 ]"
     ) in
  (*[f(x+a) = p, f(y+b) = q, a = b, f(p+c) = s, f(q+d) = t, c = d, s-t+z = 1], [x = y, z = 0]*)
  let f9 = List.hd (parse
          "& [ = p f [ + [ x a ] ] = q f [ + [ y b ] ] = a b = s f [ + [ p c ] ] = t f [ + [ q d ] ] = c d = 1 + [ s * -1 t z ] = x y = z 0 ]"
     ) in
  (*[x = y], [f(x) = 1, f(a) = 0, y = a]*)
  let f10 = List.hd (parse
          "& [ = x y = f [ x ] 1 = f [ a ] 0 = y a ]"
     ) in
  (*[x =< p, x >= q, f(x) = 0], [p =< y, q >= y, f(y) = 1]*)
  let f11 = List.hd (parse
          "& [ <= x p <= q x = f [ x ] 0 <= p y <= y q = f [ y ] 1 ]"
     ) in
  let f12 = AstUtil.simplify (List.hd (parse
          "& [ = g[a] + [ c 5 ] <= + [ c 1 ] f [ g [ a ] ] = h [ b ] + [ d 4 ] = d + [ c 1 ] ~<= + [ c 1 ] f [ h [ b ] ] ]"
     )) in
  let test f =
    Message.print Message.Normal (lazy("sat li+uif for: "^(AstUtil.print f)));
    if NelsonOppen.is_liuif_sat f then Message.print Message.Normal (lazy "SAT")
    else Message.print Message.Normal (lazy "UNSAT")
  in
   List.iter test [f1;f2;f3;f4;f5;f6;f7;f8;f9;f10;f11;f12]

let test_implied () =
  let f1 = AstUtil.simplify ( List.hd (parse
          "& [ <= x y  <= y x ]"
     )) in
    if SatLI.is_eq_implied f1 (Eq (Variable "x", Variable "y")) then
         Message.print Message.Normal (lazy "OK")
    else Message.print Message.Normal (lazy "ERROR");
  let f2 = AstUtil.simplify ( List.hd (parse
          "& [ <= z y  <= y x ]"
     )) in
    if SatLI.is_eq_implied f2 (Eq (Variable "x", Variable "y")) then
         Message.print Message.Normal (lazy "OK")
    else Message.print Message.Normal (lazy "ERROR")

let test_bool_t () =
  let f1 = AstUtil.cnf (AstUtil.simplify (List.hd (parse
          "& [ = f [ a ] + [ b 5 ]  <= + [ b 1 ] f [ f [ a ] ]  = f [ c ] + [ d 4 ] = d + [ b 1 ] ~ <= + [ b 1 ] f [ f [ c] ] ]"
     ))) in
  let f2 = AstUtil.cnf (AstUtil.simplify (List.hd (parse
          "& [ | [ = x 2 ~= y 1 ] | [ = y 1 ~= x 2 ] ~<= x 2 ]"
     ))) in
  let test f =
    Message.print Message.Normal (lazy("sat PL for: "^(AstUtil.print f)));
    if SatPL.is_sat f then Message.print Message.Normal (lazy "SAT")
    else Message.print Message.Normal (lazy "UNSAT")
  in
    test f1;
    test f2

let test_unsat_EUF () =
  let f = AstUtil.simplify ( List.hd (parse
      "& [ ~= f2[c_5] f2[c_6] = c_0 f1[c_3 c_0] = c_1 f1[c_0 c_3]  = f1[c_0 c_3] f1[c_3 c_0] = c_1 f1[c_0 c_4] = c_5 f1[c_4 c_0]  = f1[c_0 c_4] f1[c_4 c_0] = c_0 f1[c_6 c_0] = c_6 f1[c_6 c_1] ]"
     )) in
   assert (not (SatUIF.is_uif_sat f))


let tests_ronuding () = 
  let expr = Leq(Sum [Coeff (-.0.4, Variable "x"); Coeff (0.4, Variable "y")], Constant (-.2.0)) in
    Message.print Message.Normal (lazy (AstUtil.print (LIUtils.round_coeff expr)))


let test_find_common_li () =
  let f1 = AstUtil.simplify ( List.hd (parse
          "& [ <= 0 + [ y * -1 x 1 ]  <= + [y 1] x ]"
     )) in
  let common = SatLI.find_common_expr f1 (Variable "x") [Variable "y"] [] in
    Message.print Message.Normal (lazy("common is: "^(AstUtil.print_expr common)))


let interpolate_and_test a b =
  try
    Message.print Message.Debug (lazy("interpolant for "^(AstUtil.print a)^" and "^(AstUtil.print b)));
    let it = Interpolate.interpolate_with_proof a b in
      Message.print Message.Normal (lazy(FociPrinter.print_foci [it]));
      if (SatPL.is_sat (AstUtil.simplify (And[ a ; Not it]))) then Message.print Message.Error (lazy "FAILURE: A |= I");
      if (SatPL.is_sat (AstUtil.simplify (And[ it ; b]))) then Message.print Message.Error (lazy "FAILURE: I /\\ B")
  with SAT_FORMULA f ->
    Message.print Message.Error (lazy("Satisfiable: "^(FociPrinter.print_foci [f])))

