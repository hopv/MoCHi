(* ========================================================================= *)
(* Load in theorem proving example code.                                     *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

#load "nums.cma";;                                     (* For Ocaml 3.06     *)

if let v = String.sub Sys.ocaml_version 0 4 in v >= "3.10"
then (Topdirs.dir_directory "+camlp5";
      Topdirs.dir_load Format.std_formatter "camlp5o.cma")
else (Topdirs.dir_load Format.std_formatter "camlp4o.cma");;

(* ------------------------------------------------------------------------- *)
(* Dummy so we can just do #use.                                             *)
(* ------------------------------------------------------------------------- *)

type dummy_interactive = START_INTERACTIVE | END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Various small tweaks to OCAML's default state.                            *)
(* ------------------------------------------------------------------------- *)

#use "initialization.ml";;

(* ------------------------------------------------------------------------- *)
(* Use the quotation expander.                                               *)
(* ------------------------------------------------------------------------- *)

#use "Quotexpander.ml";;

(* ------------------------------------------------------------------------- *)
(* Basic background.                                                         *)
(* ------------------------------------------------------------------------- *)

#use "lib.ml";;              (* Utility functions                            *)
#use "intro.ml";;            (* Trivial example from the introduction        *)

(* ------------------------------------------------------------------------- *)
(* General type of formulas, parser and printer (used for prop and FOL).     *)
(* ------------------------------------------------------------------------- *)

#use "formulas.ml";;

(* ------------------------------------------------------------------------- *)
(* Propositional logic.                                                      *)
(* ------------------------------------------------------------------------- *)

#use "prop.ml";;             (* Basic propositional logic stuff              *)
#use "propexamples.ml";;     (* Generate tautologies                         *)
#use "defcnf.ml";;           (* Definitional CNF                             *)
#use "dp.ml";;               (* Davis-Putnam procedure                       *)
#use "stal.ml";;             (* Stalmarck's algorithm                        *)
#use "bdd.ml";;              (* Binary decision diagrams                     *)

(* ------------------------------------------------------------------------- *)
(* First order logic.                                                        *)
(* ------------------------------------------------------------------------- *)

#use "fol.ml";;              (* Basic first order logic stuff                *)
#use "skolem.ml";;           (* Prenex and Skolem normal forms               *)
#use "herbrand.ml";;         (* Herbrand theorem and mechanization           *)
#use "unif.ml";;             (* Unification algorithm                        *)
#use "tableaux.ml";;         (* Tableaux                                     *)
#use "resolution.ml";;       (* Resolution                                   *)
#use "prolog.ml";;           (* Horn clauses and Prolog                      *)
#use "meson.ml";;            (* MESON-type model elimination                 *)
#use "skolems.ml";;          (* Skolemizing a set of formulas (theoretical)  *)

(* ------------------------------------------------------------------------- *)
(* Equality handling.                                                        *)
(* ------------------------------------------------------------------------- *)

#use "equal.ml";;            (* Naive equality axiomatization                *)
#use "cong.ml";;             (* Congruence closure                           *)
#use "rewrite.ml";;          (* Rewriting                                    *)
#use "order.ml";;            (* Simple term orderings including LPO          *)
#use "completion.ml";;       (* Completion                                   *)
#use "eqelim.ml";;           (* Equality elimination: Brand xform etc.       *)
#use "paramodulation.ml";;   (* Paramodulation.                              *)

(* ------------------------------------------------------------------------- *)
(* Decidable problems.                                                       *)
(* ------------------------------------------------------------------------- *)

#use "decidable.ml";;        (* Some decidable subsets of first-order logic  *)
#use "qelim.ml";;            (* Quantifier elimination basics                *)
#use "cooper.ml";;           (* Cooper's algorithm for Presburger arith.     *)
#use "complex.ml";;          (* Complex quantifier elimination               *)
#use "real.ml";;             (* Real quantifier elimination                  *)
#use "grobner.ml";;          (* Grobner bases                                *)
#use "geom.ml";;             (* Geometry theorem proving                     *)
#use "interpolation.ml";;    (* Constructive Craig/Robinson interpolation    *)
#use "combining.ml";;        (* Combined decision procedure                  *)

(* ------------------------------------------------------------------------- *)
(* Interactive theorem proving.                                              *)
(* ------------------------------------------------------------------------- *)

#use "lcf.ml";;              (* LCF-style system for first-order logic       *)
#use "lcfprop.ml";;          (* Propositional logic by inference             *)
#use "folderived.ml";;       (* First-order specialization etc.              *)
#use "lcffol.ml";;           (* LCF implementation of first-order tableaux   *)
#use "tactics.ml";;          (* Tactics and Mizar-style proofs               *)

(* ------------------------------------------------------------------------- *)
(* Limitations.                                                              *)
(* ------------------------------------------------------------------------- *)

#use "limitations.ml";;      (* Various Goedelian-type stuff                 *)
