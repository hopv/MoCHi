(* ========================================================================= *)
(* Special procedures for decidable subsets of first order logic.            *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(***
meson <<forall x. p(x)>>;;
tab <<forall x. p(x)>>;;
 ***)

(* ------------------------------------------------------------------------- *)
(* Resolution does actually terminate with failure in simple cases!          *)
(* ------------------------------------------------------------------------- *)

(***
resolution <<forall x. p(x)>>;;
 ***)

(* ------------------------------------------------------------------------- *)
(* The Los example; see how Skolemized form has no non-nullary functions.    *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let los =
 <<(forall x y z. P(x,y) /\ P(y,z) ==> P(x,z)) /\
   (forall x y z. Q(x,y) /\ Q(y,z) ==> Q(x,z)) /\
   (forall x y. P(x,y) ==> P(y,x)) /\
   (forall x y. P(x,y) \/ Q(x,y))
   ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))>>;;
skolemize(Not los);;

(* ------------------------------------------------------------------------- *)
(* The old DP procedure works.                                               *)
(* ------------------------------------------------------------------------- *)

davisputnam los;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* However, we can just form all the ground instances.                       *)
(* ------------------------------------------------------------------------- *)

let aedecide fm =
  let sfm = skolemize(Not fm) in
  let fvs = fv sfm
  and cnsts,funcs = partition (fun (_,ar) -> ar = 0) (functions sfm) in
  if funcs <> [] then failwith "Not decidable" else
  let consts = if cnsts = [] then ["c",0] else cnsts in
  let cntms = map (fun (c,_) -> Fn(c,[])) consts in
  let alltuples = groundtuples cntms [] 0 (length fvs) in
  let cjs = simpcnf sfm in
  let grounds = map
   (fun tup -> image (image (subst (fpf fvs tup))) cjs) alltuples in
  not(dpll(unions grounds));;

(* ------------------------------------------------------------------------- *)
(* In this case it's quicker.                                                *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
aedecide los;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Show how we need to do PNF transformation with care.                      *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let fm = <<(forall x. p(x)) \/ (exists y. p(y))>>;;

pnf fm;;

(* ------------------------------------------------------------------------- *)
(* Also the group theory problem.                                            *)
(* ------------------------------------------------------------------------- *)

aedecide
 <<(forall x. P(1,x,x)) /\ (forall x. P(x,x,1)) /\
   (forall u v w x y z.
        P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
   ==> forall a b c. P(a,b,c) ==> P(b,a,c)>>;;

aedecide
 <<(forall x. P(x,x,1)) /\
   (forall u v w x y z.
        P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
   ==> forall a b c. P(a,b,c) ==> P(b,a,c)>>;;

(* ------------------------------------------------------------------------- *)
(* A bigger example.                                                         *)
(* ------------------------------------------------------------------------- *)

aedecide
 <<(exists x. P(x)) /\ (exists x. G(x))
   ==> ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
        (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* The following, however, doesn't work with aedecide.                       *)
(* ------------------------------------------------------------------------- *)

(*** This is p18

aedecide <<exists y. forall x. P(y) ==> P(x)>>;;

davisputnam <<exists y. forall x. P(y) ==> P(x)>>;;

 ***)

(* ------------------------------------------------------------------------- *)
(* Simple-minded miniscoping procedure.                                      *)
(* ------------------------------------------------------------------------- *)

let separate x cjs =
  let yes,no = partition (mem x ** fv) cjs in
  if yes = [] then list_conj no
  else if no = [] then Exists(x,list_conj yes)
  else And(Exists(x,list_conj yes),list_conj no);;

let rec pushquant x p =
  if not (mem x (fv p)) then p else
  let djs = purednf(nnf p) in
  list_disj (map (separate x) djs);;

let rec miniscope fm =
  match fm with
    Not p -> Not(miniscope p)
  | And(p,q) -> And(miniscope p,miniscope q)
  | Or(p,q) -> Or(miniscope p,miniscope q)
  | Forall(x,p) -> Not(pushquant x (Not(miniscope p)))
  | Exists(x,p) -> pushquant x (miniscope p)
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
miniscope(nnf <<exists y. forall x. P(y) ==> P(x)>>);;

let fm = miniscope(nnf
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>);;

pnf(nnf fm);;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Stronger version of "aedecide" similar to Wang's classic procedure.       *)
(* ------------------------------------------------------------------------- *)

let wang fm = aedecide(miniscope(nnf(simplify fm)));;

(* ------------------------------------------------------------------------- *)
(* It works well on simple monadic formulas.                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
wang
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;

(* ------------------------------------------------------------------------- *)
(* But not on this one!                                                      *)
(* ------------------------------------------------------------------------- *)

pnf(nnf(miniscope(nnf
 <<((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
    ((exists x. P(x)) <=> (forall y. P(y))))>>)));;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Checking classic Aristotelean syllogisms.                                 *)
(* ------------------------------------------------------------------------- *)

let atom p x = Atom(R(p,[Var x]));;

let premiss_A (p,q) = Forall("x",Imp(atom p "x",atom q "x"))
and premiss_E (p,q) = Forall("x",Imp(atom p "x",Not(atom q "x")))
and premiss_I (p,q) = Exists("x",And(atom p "x",atom q "x"))
and premiss_O (p,q) = Exists("x",And(atom p "x",Not(atom q "x")));;

let anglicize_premiss fm =
  match fm with
    Forall(_,Imp(Atom(R(p,_)),Atom(R(q,_)))) ->  "all "^p^" are "^q
  | Forall(_,Imp(Atom(R(p,_)),Not(Atom(R(q,_))))) ->  "no "^p^" are "^q
  | Exists(_,And(Atom(R(p,_)),Atom(R(q,_)))) ->  "some "^p^" are "^q
  | Exists(_,And(Atom(R(p,_)),Not(Atom(R(q,_))))) ->
        "some "^p^" are not "^q;;

let anglicize_syllogism (Imp(And(t1,t2),t3)) =
  "If " ^ anglicize_premiss t1 ^ " and " ^ anglicize_premiss t2 ^
  ", then " ^ anglicize_premiss t3;;

let all_possible_syllogisms =
  let sylltypes = [premiss_A; premiss_E; premiss_I; premiss_O] in
  let prems1 = allpairs (fun x -> x) sylltypes ["M","P"; "P","M"]
  and prems2 = allpairs (fun x -> x) sylltypes ["S","M"; "M","S"]
  and prems3 = allpairs (fun x -> x) sylltypes ["S","P"] in
  allpairs mk_imp (allpairs mk_and prems1 prems2) prems3;;

START_INTERACTIVE;;
let all_valid_syllogisms = filter aedecide all_possible_syllogisms;;

length all_valid_syllogisms;;

map anglicize_syllogism all_valid_syllogisms;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* We can "fix" the traditional list by assuming nonemptiness.               *)
(* ------------------------------------------------------------------------- *)

let all_possible_syllogisms' =
  let p =
    <<(exists x. P(x)) /\ (exists x. M(x)) /\ (exists x. S(x))>> in
  map (fun t -> Imp(p,t)) all_possible_syllogisms;;

START_INTERACTIVE;;
let all_valid_syllogisms' = filter aedecide all_possible_syllogisms';;

length all_valid_syllogisms';;

map (anglicize_syllogism ** consequent) all_valid_syllogisms';;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Decide a formula on all models of size n.                                 *)
(* ------------------------------------------------------------------------- *)

let rec alltuples n l =
  if n = 0 then [[]] else
  let tups = alltuples (n - 1) l in
  allpairs (fun h t -> h::t) l tups;;

let allmappings dom ran =
  itlist (fun p -> allpairs (valmod p) ran) dom [undef];;

let alldepmappings dom ran =
  itlist (fun (p,n) -> allpairs (valmod p) (ran n)) dom [undef];;

let allfunctions dom n = allmappings (alltuples n dom) dom;;

let allpredicates dom n = allmappings (alltuples n dom) [false;true];;

let decide_finite n fm =
  let funcs = functions fm and preds = predicates fm and dom = 1--n in
  let fints = alldepmappings funcs (allfunctions dom)
  and pints = alldepmappings preds (allpredicates dom) in
  let interps = allpairs (fun f p -> dom,f,p) fints pints in
  let fm' = generalize fm in
  forall (fun md -> holds md undefined fm') interps;;

(* ------------------------------------------------------------------------- *)
(* Decision procedure in principle for formulas with finite model property.  *)
(* ------------------------------------------------------------------------- *)

let limmeson n fm =
  let cls = simpcnf(specialize(pnf fm)) in
  let rules = itlist ((@) ** contrapositives) cls [] in
  mexpand rules [] False (fun x -> x) (undefined,n,0);;

let limited_meson n fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (limmeson n ** list_conj) (simpdnf fm1);;

let decide_fmp fm =
  let rec test n =
    try limited_meson n fm; true with Failure _ ->
    if decide_finite n fm then test (n + 1) else false in
  test 1;;

START_INTERACTIVE;;
decide_fmp
 <<(forall x y. R(x,y) \/ R(y,x)) ==> forall x. R(x,x)>>;;

decide_fmp
 <<(forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)) ==> forall x. R(x,x)>>;;

(*** This fails to terminate: has countermodels, but only infinite ones
decide_fmp
 <<~((forall x. ~R(x,x)) /\
     (forall x. exists z. R(x,z)) /\
     (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))>>;;
****)
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Semantic decision procedure for the monadic fragment.                     *)
(* ------------------------------------------------------------------------- *)

let decide_monadic fm =
  let funcs = functions fm and preds = predicates fm in
  let monadic,other = partition (fun (_,ar) -> ar = 1) preds in
  if funcs <> [] or exists (fun (_,ar) -> ar > 1) other
  then failwith "Not in the monadic subset" else
  let n = funpow (length monadic) (( * ) 2) 1 in
  decide_finite n fm;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
decide_monadic
 <<((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
    ((exists x. forall y. Q(x) <=> Q(y)) <=>
   ((exists x. P(x)) <=> (forall y. P(y))))>>;;

(**** This is not feasible
decide_monadic
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;
 ****)
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Little auxiliary results for failure of finite model property.            *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;

(*** Our claimed equivalences are indeed correct ***)

meson
 <<(exists x y z. forall u.
        R(x,x) \/ ~R(x,u) \/ (R(x,y) /\ R(y,z) /\ ~R(x,z))) <=>
   ~((forall x. ~R(x,x)) /\
     (forall x. exists z. R(x,z)) /\
     (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))>>;;

meson
 <<(exists x. forall y. exists z. R(x,x) \/ ~R(x,y) \/ (R(y,z) /\ ~R(x,z))) <=>
   ~((forall x. ~R(x,x)) /\
     (forall x. exists y. R(x,y) /\ forall z. R(y,z) ==> R(x,z)))>>;;

(*** The second formula implies the first ***)

meson
<<~((forall x. ~R(x,x)) /\
    (forall x. exists y. R(x,y) /\ forall z. R(y,z) ==> R(x,z)))
  ==> ~((forall x. ~R(x,x)) /\
        (forall x. exists z. R(x,z)) /\
        (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z)))>>;;
END_INTERACTIVE;;
