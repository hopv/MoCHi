(* ========================================================================= *)
(* Simple implementation of Stalmarck's algorithm.                           *)
(*                                                                           *)
(* NB! This algorithm is patented for commercial use (not that a toy version *)
(* like this would actually be useful in practice).                          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Triplet transformation, using functions defined earlier.                  *)
(* ------------------------------------------------------------------------- *)

let triplicate fm =
  let fm' = nenf fm in
  let n = Int 1 +/ overatoms (max_varindex "p_" ** pname) fm' (Int 0) in
  let (p,defs,_) = maincnf (fm',undefined,n) in
  p,map (snd ** snd) (graph defs);;

(* ------------------------------------------------------------------------- *)
(* Automatically generate triggering rules to save writing them out.         *)
(* ------------------------------------------------------------------------- *)

let atom lit = if negative lit then negate lit else lit;;

let rec align (p,q) =
  if atom p < atom q then align (q,p) else
  if negative p then (negate p,negate q) else (p,q);;

let equate2 (p,q) eqv = equate (negate p,negate q) (equate (p,q) eqv);;

let rec irredundant rel eqs =
  match eqs with
    [] -> []
  | (p,q)::oth ->
      if canonize rel p = canonize rel q then irredundant rel oth
      else insert (p,q) (irredundant (equate2 (p,q) rel) oth);;

let consequences (p,q as peq) fm eqs =
  let follows(r,s) = tautology(Imp(And(Iff(p,q),fm),Iff(r,s))) in
  irredundant (equate2 peq unequal) (filter follows eqs);;

let triggers fm =
  let poslits = insert True (map (fun p -> Atom p) (atoms fm)) in
  let lits = union poslits (map negate poslits) in
  let pairs = allpairs (fun p q -> p,q) lits lits in
  let npairs = filter (fun (p,q) -> atom p <> atom q) pairs in
  let eqs = setify(map align npairs) in
  let raw = map (fun p -> p,consequences p fm eqs) eqs in
  filter (fun (p,c) -> c <> []) raw;;

(* ------------------------------------------------------------------------- *)
(* An example.                                                               *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
triggers <<p <=> (q /\ r)>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Precompute and instantiate triggers for standard triplets.                *)
(* ------------------------------------------------------------------------- *)

let trigger =
  let [trig_and; trig_or; trig_imp; trig_iff] = map triggers
      [<<p <=> q /\ r>>; <<p <=> q \/ r>>;
       <<p <=> (q ==> r)>>; <<p <=> (q <=> r)>>]
  and p = <<p>> and q = <<q>> and r = <<r>>
  and ddnegate fm = match fm with Not(Not p) -> p | _ -> fm in
  let inst_fn [x;y;z] =
    let subfn = fpf [P"p"; P"q"; P"r"] [x; y; z] in
    ddnegate ** psubst subfn in
  let inst2_fn i (p,q) = align(inst_fn i p,inst_fn i q) in
  let instn_fn i (a,c) = inst2_fn i a,map (inst2_fn i) c in
  let inst_trigger = map ** instn_fn in
  function (Iff(x,And(y,z))) -> inst_trigger [x;y;z] trig_and
         | (Iff(x,Or(y,z))) -> inst_trigger [x;y;z] trig_or
         | (Iff(x,Imp(y,z))) -> inst_trigger [x;y;z] trig_imp
         | (Iff(x,Iff(y,z))) -> inst_trigger [x;y;z] trig_iff;;

(* ------------------------------------------------------------------------- *)
(* Compute a function mapping each variable/true to relevant triggers.       *)
(* ------------------------------------------------------------------------- *)

let relevance trigs =
  let insert_relevant p trg f = (p |-> insert trg (tryapplyl f p)) f in
  let insert_relevant2 ((p,q),_ as trg) f =
    insert_relevant p trg (insert_relevant q trg f) in
  itlist insert_relevant2 trigs undefined;;

(* ------------------------------------------------------------------------- *)
(* Merging of equiv classes and relevancies.                                 *)
(* ------------------------------------------------------------------------- *)

let equatecons (p0,q0) (eqv,rfn as erf) =
  let p = canonize eqv p0 and q = canonize eqv q0 in
  if p = q then [],erf else
  let p' = canonize eqv (negate p0) and q' = canonize eqv (negate q0) in
  let eqv' = equate2(p,q) eqv
  and sp_pos = tryapplyl rfn p and sp_neg = tryapplyl rfn p'
  and sq_pos = tryapplyl rfn q and sq_neg = tryapplyl rfn q' in
  let rfn' =
    (canonize eqv' p |-> union sp_pos sq_pos)
    ((canonize eqv' p' |-> union sp_neg sq_neg) rfn) in
  let nw = union (intersect sp_pos sq_pos) (intersect sp_neg sq_neg) in
  itlist (union ** snd) nw [],(eqv',rfn');;

(* ------------------------------------------------------------------------- *)
(* Zero-saturation given an equivalence/relevance and new assignments.       *)
(* ------------------------------------------------------------------------- *)

let rec zero_saturate erf assigs =
  match assigs with
    [] -> erf
  | (p,q)::ts -> let news,erf' = equatecons (p,q) erf in
                 zero_saturate erf' (union ts news);;

(* ------------------------------------------------------------------------- *)
(* Zero-saturate then check for contradictoriness.                           *)
(* ------------------------------------------------------------------------- *)

let zero_saturate_and_check erf trigs =
  let (eqv',rfn' as erf') = zero_saturate erf trigs in
  let vars = filter positive (equated eqv') in
  if exists (fun x -> canonize eqv' x = canonize eqv' (Not x)) vars
  then snd(equatecons (True,Not True) erf') else erf';;

(* ------------------------------------------------------------------------- *)
(* Now we can quickly test for contradiction.                                *)
(* ------------------------------------------------------------------------- *)

let truefalse pfn = canonize pfn (Not True) = canonize pfn True;;

(* ------------------------------------------------------------------------- *)
(* Iterated equivalening over a set.                                         *)
(* ------------------------------------------------------------------------- *)

let rec equateset s0 eqfn =
  match s0 with
    a::(b::s2 as s1) -> equateset s1 (snd(equatecons (a,b) eqfn))
  | _ -> eqfn;;

(* ------------------------------------------------------------------------- *)
(* Intersection operation on equivalence classes and relevancies.            *)
(* ------------------------------------------------------------------------- *)

let rec inter els (eq1,_ as erf1) (eq2,_ as erf2) rev1 rev2 erf =
  match els with
    [] -> erf
  | x::xs ->
      let b1 = canonize eq1 x and b2 = canonize eq2 x in
      let s1 = apply rev1 b1 and s2 = apply rev2 b2 in
      let s = intersect s1 s2 in
      inter (subtract xs s) erf1 erf2 rev1 rev2 (equateset s erf);;

(* ------------------------------------------------------------------------- *)
(* Reverse the equivalence mappings.                                         *)
(* ------------------------------------------------------------------------- *)

let reverseq domain eqv =
  let al = map (fun x -> x,canonize eqv x) domain in
  itlist (fun (y,x) f -> (x |-> insert y (tryapplyl f x)) f)
         al undefined;;

(* ------------------------------------------------------------------------- *)
(* Special intersection taking contradictoriness into account.               *)
(* ------------------------------------------------------------------------- *)

let stal_intersect (eq1,_ as erf1) (eq2,_ as erf2) erf =
  if truefalse eq1 then erf2 else if truefalse eq2 then erf1 else
  let dom1 = equated eq1 and dom2 = equated eq2 in
  let comdom = intersect dom1 dom2 in
  let rev1 = reverseq dom1 eq1 and rev2 = reverseq dom2 eq2 in
  inter comdom erf1 erf2 rev1 rev2 erf;;

(* ------------------------------------------------------------------------- *)
(* General n-saturation for n >= 1                                           *)
(* ------------------------------------------------------------------------- *)

let rec saturate n erf assigs allvars =
  let (eqv',_ as erf') = zero_saturate_and_check erf assigs in
  if n = 0 or truefalse eqv' then erf' else
  let (eqv'',_ as erf'') = splits n erf' allvars allvars in
  if eqv'' = eqv' then erf'' else saturate n erf'' [] allvars

and splits n (eqv,_ as erf) allvars vars =
  match vars with
    [] -> erf
  | p::ovars ->
        if canonize eqv p <> p then splits n erf allvars ovars else
        let erf0 = saturate (n - 1) erf [p,Not True] allvars
        and erf1 = saturate (n - 1) erf [p,True] allvars in
        let (eqv',_ as erf') = stal_intersect erf0 erf1 erf in
        if truefalse eqv' then erf' else splits n erf' allvars ovars;;

(* ------------------------------------------------------------------------- *)
(* Saturate up to a limit.                                                   *)
(* ------------------------------------------------------------------------- *)

let rec saturate_upto vars n m trigs assigs =
  if n > m then failwith("Not "^(string_of_int m)^"-easy") else
   (print_string("*** Starting "^(string_of_int n)^"-saturation");
    print_newline();
    let (eqv,_) = saturate n (unequal,relevance trigs) assigs vars in
    truefalse eqv or saturate_upto vars (n + 1) m trigs assigs);;

(* ------------------------------------------------------------------------- *)
(* Overall function.                                                         *)
(* ------------------------------------------------------------------------- *)

let stalmarck fm =
  let include_trig (e,cqs) f = (e |-> union cqs (tryapplyl f e)) f in
  let fm' = psimplify(Not fm) in
  if fm' = False then true else if fm' = True then false else
  let p,triplets = triplicate fm' in
  let trigfn = itlist (itlist include_trig ** trigger)
                      triplets undefined
  and vars = map (fun p -> Atom p) (unions(map atoms triplets)) in
  saturate_upto vars 0 2 (graph trigfn) [p,True];;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
time stalmarck (mk_adder_test 6 3);;
END_INTERACTIVE;;
