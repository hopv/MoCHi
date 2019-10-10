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

open   CsisatAst
open   CsisatGlobal
  (**/**)
module Message     = CsisatMessage
module AstUtil     = CsisatAstUtil
module Utils       = CsisatUtils
module OrdSet      = CsisatOrdSet
module SatPL       = CsisatSatPL
module LIUtils     = CsisatLIUtils
module NelsonOppen = CsisatNelsonOppen
module Interpolate = CsisatInterpolate
module FociPrinter = CsisatFociPrinter
module FociParse   = CsisatFociParse
module FociLex     = CsisatFociLex
module InfixLex    = CsisatInfixLex
module InfixParse  = CsisatInfixParse
module DimacsLex   = CsisatDimacsLex
module DimacsParse = CsisatDimacsParse
  (**/**)

let print_fct = ref FociPrinter.print_foci

let interpolate_string s =
  CsisatLIUtils.set_solver "simplex";
  let lst =
    let lexbuf = Lexing.from_string s in
      print_fct := AstUtil.print_infix;
      InfixParse.main InfixLex.token lexbuf
  in
  let it a b = 
    try
      let it =
        AstUtil.simplify (LIUtils.round_coeff (Interpolate.interpolate_with_proof a b))
      in
        !print_fct [it];
    with SAT_FORMULA f ->
      "Satisfiable: "^(!print_fct [f])
  in
    if (List.length lst) = 2 then
      begin
        let a = List.hd lst in
        let b = List.hd (List.tl lst) in
          it a b
      end
    else
      begin
        if List.length lst < 2 then 
          begin
            "Interpolation is for 2 or more formula. Only "^
              (string_of_int (List.length lst))^
              " formula found.\n"^
	      "If you only want to check satisfiability, run with option '-sat'."
          end
        else
          begin
            try
              let its =
                List.map
                  (fun x -> AstUtil.simplify ( LIUtils.round_coeff x))
                  (Interpolate.interpolate_with_one_proof lst)
              in
                String.concat "\n" (List.map (fun it -> !print_fct [it]) its);
            with SAT_FORMULA f ->
              "Satisfiable: "^(!print_fct [f])
          end
      end

let () =
  Callback.register "interpolate_string" interpolate_string
