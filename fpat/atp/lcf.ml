(* ========================================================================= *)
(* LCF-style basis for Tarski-style Hilbert system of first order logic.     *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Basic first order deductive system.                                       *)
(*                                                                           *)
(* This is based on Tarski's trick for avoiding use of a substitution        *)
(* primitive. It seems about the simplest possible system we could use.      *)
(*                                                                           *)
(*  if |- p ==> q and |- p then |- q                                         *)
(*  if |- p then |- forall x. p                                              *)
(*                                                                           *)
(*  |- p ==> (q ==> p)                                                       *)
(*  |- (p ==> q ==> r) ==> (p ==> q) ==> (p ==> r)                           *)
(*  |- ((p ==> false) ==> false) ==> p                                       *)
(*  |- (forall x. p ==> q) ==> (forall x. p) ==> (forall x. q)               *)
(*  |- p ==> forall x. p                            [x not free in p]        *)
(*  |- exists x. x = t                              [x not free in t]        *)
(*  |- t = t                                                                 *)
(*  |- s1 = t1 ==> ... ==> sn = tn ==> f(s1,..,sn) = f(t1,..,tn)             *)
(*  |- s1 = t1 ==> ... ==> sn = tn ==> P(s1,..,sn) ==> P(t1,..,tn)           *)
(*                                                                           *)
(*  |- (p <=> q) ==> p ==> q                                                 *)
(*  |- (p <=> q) ==> q ==> p                                                 *)
(*  |- (p ==> q) ==> (q ==> p) ==> (p <=> q)                                 *)
(*  |- true <=> (false ==> false)                                            *)
(*  |- ~p <=> (p ==> false)                                                  *)
(*  |- p /\ q <=> (p ==> q ==> false) ==> false                              *)
(*  |- p \/ q <=> ~(~p /\ ~q)                                                *)
(*  |- (exists x. p) <=> ~(forall x. ~p)                                     *)
(* ------------------------------------------------------------------------- *)

module type Proofsystem =
   sig type thm
       val modusponens : thm -> thm -> thm
       val gen : string -> thm -> thm
       val axiom_addimp : fol formula -> fol formula -> thm
       val axiom_distribimp :
            fol formula -> fol formula -> fol formula -> thm
       val axiom_doubleneg : fol formula -> thm
       val axiom_allimp : string -> fol formula -> fol formula -> thm
       val axiom_impall : string -> fol formula -> thm
       val axiom_existseq : string -> term -> thm
       val axiom_eqrefl : term -> thm
       val axiom_funcong : string -> term list -> term list -> thm
       val axiom_predcong : string -> term list -> term list -> thm
       val axiom_iffimp1 : fol formula -> fol formula -> thm
       val axiom_iffimp2 : fol formula -> fol formula -> thm
       val axiom_impiff : fol formula -> fol formula -> thm
       val axiom_true : thm
       val axiom_not : fol formula -> thm
       val axiom_and : fol formula -> fol formula -> thm
       val axiom_or : fol formula -> fol formula -> thm
       val axiom_exists : string -> fol formula -> thm
       val concl : thm -> fol formula
   end;;

(* ------------------------------------------------------------------------- *)
(* Auxiliary functions.                                                      *)
(* ------------------------------------------------------------------------- *)

let rec occurs_in s t =
  s = t or
  match t with
    Var y -> false
  | Fn(f,args) -> exists (occurs_in s) args;;

let rec free_in t fm =
  match fm with
    False|True -> false
  | Atom(R(p,args)) -> exists (occurs_in t) args
  | Not(p) -> free_in t p
  | And(p,q)|Or(p,q)|Imp(p,q)|Iff(p,q) -> free_in t p or free_in t q
  | Forall(y,p)|Exists(y,p) -> not(occurs_in (Var y) t) & free_in t p;;

(* ------------------------------------------------------------------------- *)
(* Implementation of the abstract data type of theorems.                     *)
(* ------------------------------------------------------------------------- *)

module Proven : Proofsystem =
  struct
    type thm = fol formula
    let modusponens pq p =
      match pq with
        Imp(p',q) when p = p' -> q
      | _ -> failwith "modusponens"
    let gen x p = Forall(x,p)
    let axiom_addimp p q = Imp(p,Imp(q,p))
    let axiom_distribimp p q r =
      Imp(Imp(p,Imp(q,r)),Imp(Imp(p,q),Imp(p,r)))
    let axiom_doubleneg p = Imp(Imp(Imp(p,False),False),p)
    let axiom_allimp x p q =
      Imp(Forall(x,Imp(p,q)),Imp(Forall(x,p),Forall(x,q)))
    let axiom_impall x p =
      if not (free_in (Var x) p) then Imp(p,Forall(x,p))
      else failwith "axiom_impall: variable free in formula"
    let axiom_existseq x t =
      if not (occurs_in (Var x) t) then Exists(x,mk_eq (Var x) t)
      else failwith "axiom_existseq: variable free in term"
    let axiom_eqrefl t = mk_eq t t
    let axiom_funcong f lefts rights =
       itlist2 (fun s t p -> Imp(mk_eq s t,p)) lefts rights
               (mk_eq (Fn(f,lefts)) (Fn(f,rights)))
    let axiom_predcong p lefts rights =
       itlist2 (fun s t p -> Imp(mk_eq s t,p)) lefts rights
               (Imp(Atom(R(p,lefts)),Atom(R(p,rights))))
    let axiom_iffimp1 p q = Imp(Iff(p,q),Imp(p,q))
    let axiom_iffimp2 p q = Imp(Iff(p,q),Imp(q,p))
    let axiom_impiff p q = Imp(Imp(p,q),Imp(Imp(q,p),Iff(p,q)))
    let axiom_true = Iff(True,Imp(False,False))
    let axiom_not p = Iff(Not p,Imp(p,False))
    let axiom_and p q = Iff(And(p,q),Imp(Imp(p,Imp(q,False)),False))
    let axiom_or p q = Iff(Or(p,q),Not(And(Not(p),Not(q))))
    let axiom_exists x p = Iff(Exists(x,p),Not(Forall(x,Not p)))
    let concl c = c
  end;;

(* ------------------------------------------------------------------------- *)
(* A printer for theorems.                                                   *)
(* ------------------------------------------------------------------------- *)

include Proven;;

let print_thm th =
  open_box 0;
  print_string "|-"; print_space();
  open_box 0; print_formula print_atom (concl th); close_box();
  close_box();;

#install_printer print_thm;;
