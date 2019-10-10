(* ========================================================================= *)
(* Initialize theorem proving example code.                                  *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

#load "nums.cma";;                                     (* For Ocaml 3.06     *)

if let v = String.sub Sys.ocaml_version 0 4 in v >= "3.10"
then (Topdirs.dir_directory "+camlp5";
      Topdirs.dir_load Format.std_formatter "camlp5o.cma")
else (Topdirs.dir_load Format.std_formatter "camlp4o.cma");;

type dummy_interactive = START_INTERACTIVE | END_INTERACTIVE;;
#use "initialization.ml";;
#use "Quotexpander.ml";;
#use "atp_interactive.ml";;
