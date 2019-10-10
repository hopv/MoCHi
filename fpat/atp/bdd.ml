(* ========================================================================= *)
(* Binary decision diagrams (BDDs) using complement edges.                   *)
(*                                                                           *)
(* In practice one would use hash tables, but we use abstract finite         *)
(* partial functions here. They might also look nicer imperatively.          *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

type bddnode = prop * int * int;;

(* ------------------------------------------------------------------------- *)
(* A BDD contains a variable order, unique and computed table.               *)
(* ------------------------------------------------------------------------- *)

type bdd = Bdd of ((bddnode,int)func * (int,bddnode)func * int) *
                  (prop->prop->bool);;

let print_bdd (Bdd((unique,uback,n),ord)) =
  print_string ("<BDD with "^(string_of_int n)^" nodes>");;

#install_printer print_bdd;;

(* ------------------------------------------------------------------------- *)
(* Map a BDD node back to its components.                                    *)
(* ------------------------------------------------------------------------- *)

let expand_node (Bdd((_,expand,_),_)) n =
  if n >= 0 then tryapplyd expand n (P"",1,1)
  else let (p,l,r) = tryapplyd expand (-n) (P"",1,1) in (p,-l,-r);;

(* ------------------------------------------------------------------------- *)
(* Lookup or insertion if not there in unique table.                         *)
(* ------------------------------------------------------------------------- *)

let lookup_unique (Bdd((unique,expand,n),ord) as bdd) node =
  try bdd,apply unique node with Failure _ ->
  Bdd(((node|->n) unique,(n|->node) expand,n+1),ord),n;;

(* ------------------------------------------------------------------------- *)
(* Produce a BDD node (old or new).                                          *)
(* ------------------------------------------------------------------------- *)

let mk_node bdd (s,l,r) =
  if l = r then bdd,l
  else if l >= 0 then lookup_unique bdd (s,l,r)
  else let bdd',n = lookup_unique bdd (s,-l,-r) in bdd',-n;;

(* ------------------------------------------------------------------------- *)
(* Create a new BDD with a given ordering.                                   *)
(* ------------------------------------------------------------------------- *)

let mk_bdd ord = Bdd((undefined,undefined,2),ord);;

(* ------------------------------------------------------------------------- *)
(* Extract the ordering field of a BDD.                                      *)
(* ------------------------------------------------------------------------- *)

let order (Bdd(_,ord)) p1 p2 = (p2 = P"" & p1 <> P"") or ord p1 p2;;

(* ------------------------------------------------------------------------- *)
(* Threading state through.                                                  *)
(* ------------------------------------------------------------------------- *)

let thread s g (f1,x1) (f2,x2) =
  let s',y1 = f1 s x1 in let s'',y2 = f2 s' x2 in g s'' (y1,y2);;

(* ------------------------------------------------------------------------- *)
(* Perform an AND operation on BDDs, maintaining canonicity.                 *)
(* ------------------------------------------------------------------------- *)

let rec bdd_and (bdd,comp as bddcomp) (m1,m2) =
  if m1 = -1 or m2 = -1 then bddcomp,-1
  else if m1 = 1 then bddcomp,m2 else if m2 = 1 then bddcomp,m1 else
  try bddcomp,apply comp (m1,m2) with Failure _ ->
  try  bddcomp,apply comp (m2,m1) with Failure _ ->
  let (p1,l1,r1) = expand_node bdd m1
  and (p2,l2,r2) = expand_node bdd m2 in
  let (p,lpair,rpair) =
      if p1 = p2 then p1,(l1,l2),(r1,r2)
      else if order bdd p1 p2 then p1,(l1,m2),(r1,m2)
      else p2,(m1,l2),(m1,r2) in
  let (bdd',comp'),(lnew,rnew) =
    thread bddcomp (fun s z -> s,z) (bdd_and,lpair) (bdd_and,rpair) in
  let bdd'',n = mk_node bdd' (p,lnew,rnew) in
  (bdd'',((m1,m2) |-> n) comp'),n;;

(* ------------------------------------------------------------------------- *)
(* The other binary connectives.                                             *)
(* ------------------------------------------------------------------------- *)

let bdd_or bdc (m1,m2) = let bdc1,n = bdd_and bdc (-m1,-m2) in bdc1,-n;;

let bdd_imp bdc (m1,m2) = bdd_or bdc (-m1,m2);;

let bdd_iff bdc (m1,m2) =
  thread bdc bdd_or (bdd_and,(m1,m2)) (bdd_and,(-m1,-m2));;

(* ------------------------------------------------------------------------- *)
(* Formula to BDD conversion.                                                *)
(* ------------------------------------------------------------------------- *)

let rec mkbdd (bdd,comp as bddcomp) fm =
  match fm with
    False -> bddcomp,-1
  | True -> bddcomp,1
  | Atom(s) -> let bdd',n = mk_node bdd (s,1,-1) in (bdd',comp),n
  | Not(p) -> let bddcomp',n = mkbdd bddcomp p in bddcomp',-n
  | And(p,q) -> thread bddcomp bdd_and (mkbdd,p) (mkbdd,q)
  | Or(p,q) -> thread bddcomp bdd_or (mkbdd,p) (mkbdd,q)
  | Imp(p,q) -> thread bddcomp bdd_imp (mkbdd,p) (mkbdd,q)
  | Iff(p,q) -> thread bddcomp bdd_iff (mkbdd,p) (mkbdd,q);;

(* ------------------------------------------------------------------------- *)
(* Tautology checking using BDDs.                                            *)
(* ------------------------------------------------------------------------- *)

let bddtaut fm = snd(mkbdd (mk_bdd (<),undefined) fm) = 1;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
bddtaut (mk_adder_test 4 2);;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Towards a more intelligent treatment of "definitions".                    *)
(* ------------------------------------------------------------------------- *)

let dest_nimp fm = match fm with Not(p) -> p,False | _ -> dest_imp fm;;

let rec dest_iffdef fm =
  match fm with
    Iff(Atom(x),r) | Iff(r,Atom(x)) -> x,r
  | _ -> failwith "not a defining equivalence";;

let restore_iffdef (x,e) fm = Imp(Iff(Atom(x),e),fm);;

let suitable_iffdef defs (x,q) =
  let fvs = atoms q in not (exists (fun (x',_) -> mem x' fvs) defs);;

let rec sort_defs acc defs fm =
  try let (x,e) = find (suitable_iffdef defs) defs in
      let ps,nonps = partition (fun (x',_) -> x' = x) defs in
      let ps' = subtract ps [x,e] in
      sort_defs ((x,e)::acc) nonps (itlist restore_iffdef ps' fm)
  with Failure _ -> rev acc,itlist restore_iffdef defs fm;;

(* ------------------------------------------------------------------------- *)
(* Improved setup.                                                           *)
(* ------------------------------------------------------------------------- *)

let rec mkbdde sfn (bdd,comp as bddcomp) fm =
  match fm with
    False -> bddcomp,-1
  | True -> bddcomp,1
  | Atom(s) -> (try bddcomp,apply sfn s with Failure _ ->
                let bdd',n = mk_node bdd (s,1,-1) in (bdd',comp),n)
  | Not(p) -> let bddcomp',n = mkbdde sfn bddcomp p in bddcomp',-n
  | And(p,q) -> thread bddcomp bdd_and (mkbdde sfn,p) (mkbdde sfn,q)
  | Or(p,q) -> thread bddcomp bdd_or (mkbdde sfn,p) (mkbdde sfn,q)
  | Imp(p,q) -> thread bddcomp bdd_imp (mkbdde sfn,p) (mkbdde sfn,q)
  | Iff(p,q) -> thread bddcomp bdd_iff (mkbdde sfn,p) (mkbdde sfn,q);;

let rec mkbdds sfn bdd defs fm =
  match defs with
    [] -> mkbdde sfn bdd fm
  | (p,e)::odefs -> let bdd',b = mkbdde sfn bdd e in
                    mkbdds ((p |-> b) sfn) bdd' odefs fm;;

let ebddtaut fm =
  let l,r = try dest_nimp fm with Failure _ -> True,fm in
  let eqs,noneqs = partition (can dest_iffdef) (conjuncts l) in
  let defs,fm' = sort_defs [] (map dest_iffdef eqs)
                              (itlist mk_imp noneqs r) in
  snd(mkbdds undefined (mk_bdd (<),undefined) defs fm') = 1;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
ebddtaut (prime 101);;

ebddtaut (mk_adder_test 9 5);;
END_INTERACTIVE;;
