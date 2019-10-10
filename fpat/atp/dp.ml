(* ========================================================================= *)
(* The Davis-Putnam and Davis-Putnam-Loveland-Logemann procedures.           *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The DP procedure.                                                         *)
(* ------------------------------------------------------------------------- *)

let one_literal_rule clauses =
  let u = hd (find (fun cl -> length cl = 1) clauses) in
  let u' = negate u in
  let clauses1 = filter (fun cl -> not (mem u cl)) clauses in
  image (fun cl -> subtract cl [u']) clauses1;;

let affirmative_negative_rule clauses =
  let neg',pos = partition negative (unions clauses) in
  let neg = image negate neg' in
  let pos_only = subtract pos neg and neg_only = subtract neg pos in
  let pure = union pos_only (image negate neg_only) in
  if pure = [] then failwith "affirmative_negative_rule" else
  filter (fun cl -> intersect cl pure = []) clauses;;

let resolve_on p clauses =
  let p' = negate p and pos,notpos = partition (mem p) clauses in
  let neg,other = partition (mem p') notpos in
  let pos' = image (filter (fun l -> l <> p)) pos
  and neg' = image (filter (fun l -> l <> p')) neg in
  let res0 = allpairs union pos' neg' in
  union other (filter (non trivial) res0);;

let resolution_blowup cls l =
  let m = length(filter (mem l) cls)
  and n = length(filter (mem (negate l)) cls) in
  m * n - m - n;;

let resolution_rule clauses =
  let pvs = filter positive (unions clauses) in
  let p = minimize (resolution_blowup clauses) pvs in
  resolve_on p clauses;;

(* ------------------------------------------------------------------------- *)
(* Overall procedure.                                                        *)
(* ------------------------------------------------------------------------- *)

let rec dp clauses =
  if clauses = [] then true else if mem [] clauses then false else
  try dp (one_literal_rule clauses) with Failure _ ->
  try dp (affirmative_negative_rule clauses) with Failure _ ->
  dp(resolution_rule clauses);;

(* ------------------------------------------------------------------------- *)
(* Davis-Putnam satisfiability tester and tautology checker.                 *)
(* ------------------------------------------------------------------------- *)

let dpsat fm = dp(defcnfs fm);;

let dptaut fm = not(dpsat(Not fm));;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
tautology(prime 11);;

dptaut(prime 11);;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* The same thing but with the DPLL procedure.                               *)
(* ------------------------------------------------------------------------- *)

let posneg_count cls l =                         
  let m = length(filter (mem l) cls)                 
  and n = length(filter (mem (negate l)) cls) in
  m + n;;                                  

let rec dpll clauses =       
  if clauses = [] then true else if mem [] clauses then false else
  try dpll(one_literal_rule clauses) with Failure _ ->
  try dpll(affirmative_negative_rule clauses) with Failure _ ->
  let pvs = filter positive (unions clauses) in
  let p = maximize (posneg_count clauses) pvs in
  dpll (insert [p] clauses) or dpll (insert [negate p] clauses);;
                                                     
let dpllsat fm = dpll(defcnfs fm);;

let dplltaut fm = not(dpllsat(Not fm));;                   

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
dplltaut(prime 11);;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Iterative implementation with explicit trail instead of recursion.        *)
(* ------------------------------------------------------------------------- *)

type trailmix = Guessed | Deduced;;

let unassigned =
  let litabs p = match p with Not q -> q | _ -> p in
  fun cls trail -> subtract (unions(image (image litabs) cls))
                            (image (litabs ** fst) trail);;

let rec unit_subpropagate (cls,fn,trail) =
  let cls' = map (filter ((not) ** defined fn ** negate)) cls in
  let uu = function [c] when not(defined fn c) -> [c] | _ -> failwith "" in
  let newunits = unions(mapfilter uu cls') in
  if newunits = [] then (cls',fn,trail) else
  let trail' = itlist (fun p t -> (p,Deduced)::t) newunits trail
  and fn' = itlist (fun u -> (u |-> ())) newunits fn in
  unit_subpropagate (cls',fn',trail');;

let unit_propagate (cls,trail) =
  let fn = itlist (fun (x,_) -> (x |-> ())) trail undefined in
  let cls',fn',trail' = unit_subpropagate (cls,fn,trail) in cls',trail';;

let rec backtrack trail =
  match trail with
    (p,Deduced)::tt -> backtrack tt
  | _ -> trail;;

let rec dpli cls trail =
  let cls',trail' = unit_propagate (cls,trail) in
  if mem [] cls' then
    match backtrack trail with
      (p,Guessed)::tt -> dpli cls ((negate p,Deduced)::tt)
    | _ -> false
  else
      match unassigned cls trail' with
        [] -> true
      | ps -> let p = maximize (posneg_count cls') ps in
              dpli cls ((p,Guessed)::trail');;

let dplisat fm = dpli (defcnfs fm) [];;

let dplitaut fm = not(dplisat(Not fm));;

(* ------------------------------------------------------------------------- *)
(* With simple non-chronological backjumping and learning.                   *)
(* ------------------------------------------------------------------------- *)

let rec backjump cls p trail =
  match backtrack trail with
    (q,Guessed)::tt ->
        let cls',trail' = unit_propagate (cls,(p,Guessed)::tt) in
        if mem [] cls' then backjump cls p tt else trail
  | _ -> trail;;

let rec dplb cls trail =
  let cls',trail' = unit_propagate (cls,trail) in
  if mem [] cls' then
    match backtrack trail with
      (p,Guessed)::tt ->
        let trail' = backjump cls p tt in
        let declits = filter (fun (_,d) -> d = Guessed) trail' in
        let conflict = insert (negate p) (image (negate ** fst) declits) in
        dplb (conflict::cls) ((negate p,Deduced)::trail')
    | _ -> false
  else
    match unassigned cls trail' with
      [] -> true
    | ps -> let p = maximize (posneg_count cls') ps in
            dplb cls ((p,Guessed)::trail');;

let dplbsat fm = dplb (defcnfs fm) [];;

let dplbtaut fm = not(dplbsat(Not fm));;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
dplitaut(prime 101);;
dplbtaut(prime 101);;
END_INTERACTIVE;;
