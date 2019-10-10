(* ========================================================================= *)
(* Simple congruence closure.                                                *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

let rec subterms tm =
  match tm with
    Fn(f,args) -> itlist (union ** subterms) args [tm]
  | _ -> [tm];;

(* ------------------------------------------------------------------------- *)
(* Test whether subterms are congruent under an equivalence.                 *)
(* ------------------------------------------------------------------------- *)

let congruent eqv (s,t) =
  match (s,t) with
    Fn(f,a1),Fn(g,a2) -> f = g & forall2 (equivalent eqv) a1 a2
  | _ -> false;;

(* ------------------------------------------------------------------------- *)
(* Merging of terms, with congruence closure.                                *)
(* ------------------------------------------------------------------------- *)

let rec emerge (s,t) (eqv,pfn) =
  let s' = canonize eqv s and t' = canonize eqv t in
  if s' = t' then (eqv,pfn) else
  let sp = tryapplyl pfn s' and tp = tryapplyl pfn t' in
  let eqv' = equate (s,t) eqv in
  let st' = canonize eqv' s' in
  let pfn' = (st' |-> union sp tp) pfn in
  itlist (fun (u,v) (eqv,pfn) ->
                if congruent eqv (u,v) then emerge (u,v) (eqv,pfn)
                else eqv,pfn)
         (allpairs (fun u v -> (u,v)) sp tp) (eqv',pfn');;

(* ------------------------------------------------------------------------- *)
(* Satisfiability of conjunction of ground equations and inequations.        *)
(* ------------------------------------------------------------------------- *)

let predecessors t pfn =
  match t with
    Fn(f,a) -> itlist (fun s f -> (s |-> insert t (tryapplyl f s)) f)
                      (setify a) pfn
  | _ -> pfn;;

let ccsatisfiable fms =
  let pos,neg = partition positive fms in
  let eqps = map dest_eq pos and eqns = map (dest_eq ** negate) neg in
  let lrs = map fst eqps @ map snd eqps @ map fst eqns @ map snd eqns in
  let pfn = itlist predecessors (unions(map subterms lrs)) undefined in
  let eqv,_ = itlist emerge eqps (unequal,pfn) in
  forall (fun (l,r) -> not(equivalent eqv l r)) eqns;;

(* ------------------------------------------------------------------------- *)
(* Validity checking a universal formula.                                    *)
(* ------------------------------------------------------------------------- *)

let ccvalid fm =
  let fms = simpdnf(askolemize(Not(generalize fm))) in
  not (exists ccsatisfiable fms);;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
ccvalid <<f(f(f(f(f(c))))) = c /\ f(f(f(c))) = c
          ==> f(c) = c \/ f(g(c)) = g(f(c))>>;;

ccvalid <<f(f(f(f(c)))) = c /\ f(f(c)) = c ==> f(c) = c>>;;

(* ------------------------------------------------------------------------- *)
(* For debugging. Maybe I will incorporate into a prettyprinter one day.     *)
(* ------------------------------------------------------------------------- *)

(**********

let showequiv ptn =
  let fn = reverseq (equated ptn) ptn in
  map (apply fn) (dom fn);;

 **********)

END_INTERACTIVE;;
