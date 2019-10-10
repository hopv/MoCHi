(* ========================================================================= *)
(* Introduction to quantifier elimination.                                   *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Lift procedure given literal modifier, formula normalizer, and a  basic   *)
(* elimination procedure for existential formulas with conjunctive body.     *)
(* ------------------------------------------------------------------------- *)

let qelim bfn x p =
  let cjs = conjuncts p in
  let ycjs,ncjs = partition (mem x ** fv) cjs in
  if ycjs = [] then p else
  let q = bfn (Exists(x,list_conj ycjs)) in
  itlist mk_and ncjs q;;

let lift_qelim afn nfn qfn =
  let rec qelift vars fm =
    match fm with
    | Atom(R(_,_)) -> afn vars fm
    | Not(p) -> Not(qelift vars p)
    | And(p,q) -> And(qelift vars p,qelift vars q)
    | Or(p,q) -> Or(qelift vars p,qelift vars q)
    | Imp(p,q) -> Imp(qelift vars p,qelift vars q)
    | Iff(p,q) -> Iff(qelift vars p,qelift vars q)
    | Forall(x,p) -> Not(qelift vars (Exists(x,Not p)))
    | Exists(x,p) ->
          let djs = disjuncts(nfn(qelift (x::vars) p)) in
          list_disj(map (qelim (qfn vars) x) djs)
    | _ -> fm in
  fun fm -> simplify(qelift (fv fm) (miniscope fm));;

(* ------------------------------------------------------------------------- *)
(* Cleverer (proposisional) NNF with conditional and literal modification.   *)
(* ------------------------------------------------------------------------- *)

let cnnf lfn =
  let rec cnnf fm =
    match fm with
      And(p,q) -> And(cnnf p,cnnf q)
    | Or(p,q) -> Or(cnnf p,cnnf q)
    | Imp(p,q) -> Or(cnnf(Not p),cnnf q)
    | Iff(p,q) -> Or(And(cnnf p,cnnf q),And(cnnf(Not p),cnnf(Not q)))
    | Not(Not p) -> cnnf p
    | Not(And(p,q)) -> Or(cnnf(Not p),cnnf(Not q))
    | Not(Or(And(p,q),And(p',r))) when p' = negate p ->
         Or(cnnf (And(p,Not q)),cnnf (And(p',Not r)))
    | Not(Or(p,q)) -> And(cnnf(Not p),cnnf(Not q))
    | Not(Imp(p,q)) -> And(cnnf p,cnnf(Not q))
    | Not(Iff(p,q)) -> Or(And(cnnf p,cnnf(Not q)),
                          And(cnnf(Not p),cnnf q))
    | _ -> lfn fm in
  simplify ** cnnf ** simplify;;

(* ------------------------------------------------------------------------- *)
(* Initial literal simplifier and intermediate literal modifier.             *)
(* ------------------------------------------------------------------------- *)

let lfn_dlo fm =
  match fm with
    Not(Atom(R("<",[s;t]))) -> Or(Atom(R("=",[s;t])),Atom(R("<",[t;s])))
  | Not(Atom(R("=",[s;t]))) -> Or(Atom(R("<",[s;t])),Atom(R("<",[t;s])))
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Simple example of dense linear orderings; this is the base function.      *)
(* ------------------------------------------------------------------------- *)

let dlobasic fm =
  match fm with
    Exists(x,p) ->
      let cjs = subtract (conjuncts p) [Atom(R("=",[Var x;Var x]))] in
      try let eqn = find is_eq cjs in
          let s,t = dest_eq eqn in
          let y = if s = Var x then t else s in
          list_conj(map (subst (x |=> y)) (subtract cjs [eqn]))
      with Failure _ ->
          if mem (Atom(R("<",[Var x;Var x]))) cjs then False else
          let lefts,rights =
            partition (fun (Atom(R("<",[s;t]))) -> t = Var x) cjs in
          let ls = map (fun (Atom(R("<",[l;_]))) -> l) lefts
          and rs = map (fun (Atom(R("<",[_;r]))) -> r) rights in
          list_conj(allpairs (fun l r -> Atom(R("<",[l;r]))) ls rs)
  | _ -> failwith "dlobasic";;

(* ------------------------------------------------------------------------- *)
(* Overall quelim procedure.                                                 *)
(* ------------------------------------------------------------------------- *)

let afn_dlo vars fm =
  match fm with
    Atom(R("<=",[s;t])) -> Not(Atom(R("<",[t;s])))
  | Atom(R(">=",[s;t])) -> Not(Atom(R("<",[s;t])))
  | Atom(R(">",[s;t])) -> Atom(R("<",[t;s]))
  | _ -> fm;;

let quelim_dlo =
  lift_qelim afn_dlo (dnf ** cnnf lfn_dlo) (fun v -> dlobasic);;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
quelim_dlo <<forall x y. exists z. z < x /\ z < y>>;;

quelim_dlo <<exists z. z < x /\ z < y>>;;

quelim_dlo <<exists z. x < z /\ z < y>>;;

quelim_dlo <<(forall x. x < a ==> x < b)>>;;

quelim_dlo <<forall a b. (forall x. x < a ==> x < b) <=> a <= b>>;;

quelim_dlo <<forall a b. (forall x. x < a <=> x < b) <=> a = b>>;;

quelim_dlo <<exists x y z. forall u.
                 x < x \/ ~x < u \/ (x < y /\ y < z /\ ~x < z)>>;;

(* ------------------------------------------------------------------------- *)
(* More tests (not in the text).                                             *)
(* ------------------------------------------------------------------------- *)

time quelim_dlo <<forall x. exists y. x < y>>;;

time quelim_dlo <<forall x y z. x < y /\ y < z ==> x < z>>;;

time quelim_dlo <<forall x y. x < y \/ (x = y) \/ y < x>>;;

time quelim_dlo <<exists x y. x < y /\ y < x>>;;

time quelim_dlo <<forall x y. exists z. z < x /\ x < y>>;;

time quelim_dlo <<exists z. z < x /\ x < y>>;;

time quelim_dlo <<forall x y. exists z. z < x /\ z < y>>;;

time quelim_dlo <<forall x y. x < y ==> exists z. x < z /\ z < y>>;;

time quelim_dlo
  <<forall x y. ~(x = y) ==> exists u. u < x /\ (y < u \/ x < y)>>;;

time quelim_dlo <<exists x. x = x>>;;

time quelim_dlo <<exists x. x = x /\ x = y>>;;

time quelim_dlo <<exists z. x < z /\ z < y>>;;

time quelim_dlo <<exists z. x <= z /\ z <= y>>;;

time quelim_dlo <<exists z. x < z /\ z <= y>>;;

time quelim_dlo <<forall x y z. exists u. u < x /\ u < y /\ u < z>>;;

time quelim_dlo <<forall y. x < y /\ y < z ==> w < z>>;;

time quelim_dlo <<forall x y. x < y>>;;

time quelim_dlo <<exists z. z < x /\ x < y>>;;

time quelim_dlo <<forall a b. (forall x. x < a ==> x < b) <=> a <= b>>;;

time quelim_dlo <<forall x. x < a ==> x < b>>;;

time quelim_dlo <<forall x. x < a ==> x <= b>>;;

time quelim_dlo <<forall a b. exists x. ~(x = a) \/ ~(x = b) \/ (a = b)>>;;

time quelim_dlo <<forall x y. x <= y \/ x > y>>;;

time quelim_dlo <<forall x y. x <= y \/ x < y>>;;
END_INTERACTIVE;;
