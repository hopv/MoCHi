(* ========================================================================= *)
(* Backchaining procedure for Horn clauses, and toy Prolog implementation.   *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Rename a rule.                                                            *)
(* ------------------------------------------------------------------------- *)

let renamerule k (asm,c) =
  let fvs = fv(list_conj(c::asm)) in
  let n = length fvs in
  let vvs = map (fun i -> "_" ^ string_of_int i) (k -- (k+n-1)) in
  let inst = subst(fpf fvs (map (fun x -> Var x) vvs)) in
  (map inst asm,inst c),k+n;;

(* ------------------------------------------------------------------------- *)
(* Basic prover for Horn clauses based on backchaining with unification.     *)
(* ------------------------------------------------------------------------- *)

let rec backchain rules n k env goals =
  match goals with
    [] -> env
  | g::gs ->
     if n = 0 then failwith "Too deep" else
     tryfind (fun rule ->
        let (a,c),k' = renamerule k rule in
        backchain rules (n - 1) k' (unify_literals env (c,g)) (a @ gs))
     rules;;

let hornify cls =
  let pos,neg = partition positive cls in
  if length pos > 1 then failwith "non-Horn clause"
  else (map negate neg,if pos = [] then False else hd pos);;

let hornprove fm =
  let rules = map hornify (simpcnf(skolemize(Not(generalize fm)))) in
  deepen (fun n -> backchain rules n 0 undefined [False],n) 0;;

(* ------------------------------------------------------------------------- *)
(* A Horn example.                                                           *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let p32 = hornprove
 <<(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
   (forall x. Q(x) /\ H(x) ==> J(x)) /\
   (forall x. R(x) ==> H(x))
   ==> (forall x. P(x) /\ R(x) ==> J(x))>>;;

(* ------------------------------------------------------------------------- *)
(* A non-Horn example.                                                       *)
(* ------------------------------------------------------------------------- *)

(****************

hornprove <<(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)>>;;

**********)
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Parsing rules in a Prolog-like syntax.                                    *)
(* ------------------------------------------------------------------------- *)

let parserule s =
  let c,rest =
    parse_formula (parse_infix_atom,parse_atom) [] (lex(explode s)) in
  let asm,rest1 =
    if rest <> [] & hd rest = ":-"
    then parse_list ","
          (parse_formula (parse_infix_atom,parse_atom) []) (tl rest)
    else [],rest in
  if rest1 = [] then (asm,c) else failwith "Extra material after rule";;

(* ------------------------------------------------------------------------- *)
(* Prolog interpreter: just use depth-first search not iterative deepening.  *)
(* ------------------------------------------------------------------------- *)

let simpleprolog rules gl =
  backchain (map parserule rules) (-1) 0 undefined [parse gl];;

(* ------------------------------------------------------------------------- *)
(* Ordering example.                                                         *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let lerules = ["0 <= X"; "S(X) <= S(Y) :- X <= Y"];;

simpleprolog lerules "S(S(0)) <= S(S(S(0)))";;

(*** simpleprolog lerules "S(S(0)) <= S(0)";;
 ***)

let env = simpleprolog lerules "S(S(0)) <= X";;
apply env "X";;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* With instantiation collection to produce a more readable result.          *)
(* ------------------------------------------------------------------------- *)

let prolog rules gl =
  let i = solve(simpleprolog rules gl) in
  mapfilter (fun x -> Atom(R("=",[Var x; apply i x]))) (fv(parse gl));;

(* ------------------------------------------------------------------------- *)
(* Example again.                                                            *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
prolog lerules "S(S(0)) <= X";;

(* ------------------------------------------------------------------------- *)
(* Append example, showing symmetry between inputs and outputs.              *)
(* ------------------------------------------------------------------------- *)

let appendrules =
  ["append(nil,L,L)"; "append(H::T,L,H::A) :- append(T,L,A)"];;

prolog appendrules "append(1::2::nil,3::4::nil,Z)";;

prolog appendrules "append(1::2::nil,Y,1::2::3::4::nil)";;

prolog appendrules "append(X,3::4::nil,1::2::3::4::nil)";;

prolog appendrules "append(X,Y,1::2::3::4::nil)";;

(* ------------------------------------------------------------------------- *)
(* However this way round doesn't work.                                      *)
(* ------------------------------------------------------------------------- *)

(***
 *** prolog appendrules "append(X,3::4::nil,X)";;
 ***)

(* ------------------------------------------------------------------------- *)
(* A sorting example (from Lloyd's "Foundations of Logic Programming").      *)
(* ------------------------------------------------------------------------- *)

let sortrules =
 ["sort(X,Y) :- perm(X,Y),sorted(Y)";
  "sorted(nil)";
  "sorted(X::nil)";
  "sorted(X::Y::Z) :- X <= Y, sorted(Y::Z)";
  "perm(nil,nil)";
  "perm(X::Y,U::V) :- delete(U,X::Y,Z), perm(Z,V)";
  "delete(X,X::Y,Y)";
  "delete(X,Y::Z,Y::W) :- delete(X,Z,W)";
  "0 <= X";
  "S(X) <= S(Y) :- X <= Y"];;

prolog sortrules
  "sort(S(S(S(S(0))))::S(0)::0::S(S(0))::S(0)::nil,X)";;

(* ------------------------------------------------------------------------- *)
(* Yet with a simple swap of the first two predicates...                     *)
(* ------------------------------------------------------------------------- *)

let badrules =
 ["sort(X,Y) :- sorted(Y), perm(X,Y)";
  "sorted(nil)";
  "sorted(X::nil)";
  "sorted(X::Y::Z) :- X <= Y, sorted(Y::Z)";
  "perm(nil,nil)";
  "perm(X::Y,U::V) :- delete(U,X::Y,Z), perm(Z,V)";
  "delete(X,X::Y,Y)";
  "delete(X,Y::Z,Y::W) :- delete(X,Z,W)";
  "0 <= X";
  "S(X) <= S(Y) :- X <= Y"];;

(*** This no longer works

prolog badrules
  "sort(S(S(S(S(0))))::S(0)::0::S(S(0))::S(0)::nil,X)";;

 ***)
END_INTERACTIVE;;                           
