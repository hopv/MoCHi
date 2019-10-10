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

(** Parsing of argument + configuration variables *)
open CsisatGlobal

let set_syntax str = match str with
  | "foci" -> syntax := SyntaxFoci
  | "infix" -> syntax := SyntaxInfix
  | "dimacs" -> syntax := SyntaxDimacs
  | _ -> failwith ("Unknown syntax: "^str)

let options = 
  [
    ("-debug", Arg.Unit CsisatMessage.enable_debug,
      "Print debug information.");
    ("-check", Arg.Unit (fun () -> check := true),
      "Check the computed interpolant.");
    ("-sat", Arg.Unit (fun () -> sat_only := true),
      "Check for satisfiability only (no interplolation).\n     Writes only \"satisfiable\" or \"unsatisfiable\" to stdout.");
    ("-LAsolver", Arg.String CsisatLIUtils.set_solver,
      "Choose the LA solver to use.\n    Options: simplex, simplex_wo_presolve, interior, exact (default: simplex_wo_presolve).\n    WARNING: exact solver integration is still experimental.");
    ("-syntax", Arg.String set_syntax,
      "Choose the syntax to use.\n    Options: foci, infix (default: try foci first then infix if it fail).");
    ("-round", Arg.Unit (fun () -> round := true),
      "Try to round the coefficient to integer values. WARNING: still experimental.");
    ("-int", Arg.Unit (fun () -> integer_heuristics := true),
      "Apply heuristics to solve over integers. This is not sound, neither complete in general.");
    ("-noAssert", Arg.Unit (fun () -> assert_disable := true),
      "Disable runtime checks.")
  ]

let usage = (
  "CSIsat is an open-source interpolating decision procedure for LA+EUF.\n"^
  "Version 1.2 (Rev Unversioned directory, Build 2018-05-22T23:38:15).\n\n"^
  "Reads the query from stdin and writes the answer to stdout.\n\n"^
  "If the input formula is satisfiable,\n CSIsat writes \"Satisfiable: <formula>\" on stderr.\n"^
  "'formula' implies the conjunction of the two input formula.\n"^
  "Otherwise it writes an interpolant to stdout.\n"
)

let _ = Arg.parse options (fun _ -> ()) usage
