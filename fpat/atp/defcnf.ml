(* ========================================================================= *)
(* Definitional CNF.                                                         *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

START_INTERACTIVE;;
cnf <<p <=> (q <=> r)>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Make a stylized variable and update the index.                            *)
(* ------------------------------------------------------------------------- *)

let mkprop n = Atom(P("p_"^(string_of_num n))),n +/ Int 1;;

(* ------------------------------------------------------------------------- *)
(* Core definitional CNF procedure.                                          *)
(* ------------------------------------------------------------------------- *)

let rec maincnf (fm,defs,n as trip) =
  match fm with
    And(p,q) -> defstep mk_and (p,q) trip
  | Or(p,q) -> defstep mk_or (p,q) trip
  | Iff(p,q) -> defstep mk_iff (p,q) trip
  | _ -> trip

and defstep op (p,q) (fm,defs,n) =
  let fm1,defs1,n1 = maincnf (p,defs,n) in
  let fm2,defs2,n2 = maincnf (q,defs1,n1) in
  let fm' = op fm1 fm2 in
  try (fst(apply defs2 fm'),defs2,n2) with Failure _ ->
  let v,n3 = mkprop n2 in (v,(fm'|->(v,Iff(v,fm'))) defs2,n3);;

(* ------------------------------------------------------------------------- *)
(* Make n large enough that "v_m" won't clash with s for any m >= n          *)
(* ------------------------------------------------------------------------- *)

let max_varindex pfx =
  let m = String.length pfx in
  fun s n ->
    let l = String.length s in
    if l <= m or String.sub s 0 m <> pfx then n else
    let s' = String.sub s m (l - m) in
    if forall numeric (explode s') then max_num n (num_of_string s')
    else n;;

(* ------------------------------------------------------------------------- *)
(* Overall definitional CNF.                                                 *)
(* ------------------------------------------------------------------------- *)

let mk_defcnf fn fm =
  let fm' = nenf fm in
  let n = Int 1 +/ overatoms (max_varindex "p_" ** pname) fm' (Int 0) in
  let (fm'',defs,_) = fn (fm',undefined,n) in
  let deflist = map (snd ** snd) (graph defs) in
  unions(simpcnf fm'' :: map simpcnf deflist);;

let defcnf fm = list_conj(map list_disj(mk_defcnf maincnf fm));;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
defcnf <<(p \/ (q /\ ~r)) /\ s>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Version tweaked to exploit initial structure.                             *)
(* ------------------------------------------------------------------------- *)

let subcnf sfn op (p,q) (fm,defs,n) =
  let fm1,defs1,n1 = sfn(p,defs,n) in
  let fm2,defs2,n2 = sfn(q,defs1,n1) in (op fm1 fm2,defs2,n2);;

let rec orcnf (fm,defs,n as trip) =
  match fm with
    Or(p,q) -> subcnf orcnf mk_or (p,q) trip
  | _ -> maincnf trip;;

let rec andcnf (fm,defs,n as trip) =
  match fm with
    And(p,q) -> subcnf andcnf mk_and (p,q) trip
  | _ -> orcnf trip;;

let defcnfs fm = mk_defcnf andcnf fm;;

let defcnf fm = list_conj (map list_disj (defcnfs fm));;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
defcnf <<(p \/ (q /\ ~r)) /\ s>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Version that guarantees 3-CNF.                                            *)
(* ------------------------------------------------------------------------- *)

let rec andcnf3 (fm,defs,n as trip) =
  match fm with
    And(p,q) -> subcnf andcnf3 mk_and (p,q) trip
  | _ -> maincnf trip;;

let defcnf3 fm = list_conj (map list_disj(mk_defcnf andcnf3 fm));;
