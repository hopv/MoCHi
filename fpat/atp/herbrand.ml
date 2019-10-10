(* ========================================================================= *)
(* Relation between FOL and propositonal logic; Herbrand theorem.            *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Propositional valuation.                                                  *)
(* ------------------------------------------------------------------------- *)

let pholds d fm = eval fm (fun p -> d(Atom p));;

(* ------------------------------------------------------------------------- *)
(* Get the constants for Herbrand base, adding nullary one if necessary.     *)
(* ------------------------------------------------------------------------- *)

let herbfuns fm =
  let cns,fns = partition (fun (_,ar) -> ar = 0) (functions fm) in
  if cns = [] then ["c",0],fns else cns,fns;;

(* ------------------------------------------------------------------------- *)
(* Enumeration of ground terms and m-tuples, ordered by total fns.           *)
(* ------------------------------------------------------------------------- *)

let rec groundterms cntms funcs n =
  if n = 0 then cntms else
  itlist (fun (f,m) l -> map (fun args -> Fn(f,args))
                             (groundtuples cntms funcs (n - 1) m) @ l)
          funcs []

and groundtuples cntms funcs n m =
  if m = 0 then if n = 0 then [[]] else [] else
  itlist (fun k l -> allpairs (fun h t -> h::t)
                       (groundterms cntms funcs k)
                       (groundtuples cntms funcs (n - k) (m - 1)) @ l)
         (0 -- n) [];;

(* ------------------------------------------------------------------------- *)
(* Iterate modifier "mfn" over ground terms till "tfn" fails.                *)
(* ------------------------------------------------------------------------- *)

let rec herbloop mfn tfn fl0 cntms funcs fvs n fl tried tuples =
  print_string(string_of_int(length tried)^" ground instances tried; "^
               string_of_int(length fl)^" items in list");
  print_newline();
  match tuples with
    [] -> let newtups = groundtuples cntms funcs n (length fvs) in
          herbloop mfn tfn fl0 cntms funcs fvs (n + 1) fl tried newtups
  | tup::tups ->
          let fl' = mfn fl0 (subst(fpf fvs tup)) fl in
          if not(tfn fl') then tup::tried else
          herbloop mfn tfn fl0 cntms funcs fvs n fl' (tup::tried) tups;;

(* ------------------------------------------------------------------------- *)
(* Hence a simple Gilmore-type procedure.                                    *)
(* ------------------------------------------------------------------------- *)

let gilmore_loop =
  let mfn djs0 ifn djs =
    filter (non trivial) (distrib (image (image ifn) djs0) djs) in
  herbloop mfn (fun djs -> djs <> []);;

let gilmore fm =
  let sfm = skolemize(Not(generalize fm)) in
  let fvs = fv sfm and consts,funcs = herbfuns sfm in
  let cntms = image (fun (c,_) -> Fn(c,[])) consts in
  length(gilmore_loop (simpdnf sfm) cntms funcs fvs 0 [[]] [] []);;

(* ------------------------------------------------------------------------- *)
(* First example and a little tracing.                                       *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
gilmore <<exists x. forall y. P(x) ==> P(y)>>;;

let sfm = skolemize(Not <<exists x. forall y. P(x) ==> P(y)>>);;

(* ------------------------------------------------------------------------- *)
(* Quick example.                                                            *)
(* ------------------------------------------------------------------------- *)

let p24 = gilmore
 <<~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x))
   ==> (exists x. P(x) /\ R(x))>>;;

(* ------------------------------------------------------------------------- *)
(* Slightly less easy example.                                               *)
(* ------------------------------------------------------------------------- *)

let p45 = gilmore
 <<(forall x. P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))
              ==> (forall y. G(y) /\ H(x,y) ==> R(y))) /\
   ~(exists y. L(y) /\ R(y)) /\
   (exists x. P(x) /\ (forall y. H(x,y) ==> L(y)) /\
                      (forall y. G(y) /\ H(x,y) ==> J(x,y)))
   ==> (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Apparently intractable example.                                           *)
(* ------------------------------------------------------------------------- *)

(**********

let p20 = gilmore
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;

 **********)

(* ------------------------------------------------------------------------- *)
(* The Davis-Putnam procedure for first order logic.                         *)
(* ------------------------------------------------------------------------- *)

let dp_mfn cjs0 ifn cjs = union (image (image ifn) cjs0) cjs;;

let dp_loop = herbloop dp_mfn dpll;;

let davisputnam fm =
  let sfm = skolemize(Not(generalize fm)) in
  let fvs = fv sfm and consts,funcs = herbfuns sfm in
  let cntms = image (fun (c,_) -> Fn(c,[])) consts in
  length(dp_loop (simpcnf sfm) cntms funcs fvs 0 [] [] []);;

(* ------------------------------------------------------------------------- *)
(* Show how much better than the Gilmore procedure this can be.              *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let p20 = davisputnam
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Try to cut out useless instantiations in final result.                    *)
(* ------------------------------------------------------------------------- *)

let rec dp_refine cjs0 fvs dunno need =
  match dunno with
    [] -> need
  | cl::dknow ->
      let mfn = dp_mfn cjs0 ** subst ** fpf fvs in
      let need' =
       if dpll(itlist mfn (need @ dknow) []) then cl::need else need in
      dp_refine cjs0 fvs dknow need';;

let dp_refine_loop cjs0 cntms funcs fvs n cjs tried tuples =
  let tups = dp_loop cjs0 cntms funcs fvs n cjs tried tuples in
  dp_refine cjs0 fvs tups [];;

(* ------------------------------------------------------------------------- *)
(* Show how few of the instances we really need. Hence unification!          *)
(* ------------------------------------------------------------------------- *)

let davisputnam' fm =
  let sfm = skolemize(Not(generalize fm)) in
  let fvs = fv sfm and consts,funcs = herbfuns sfm in
  let cntms = image (fun (c,_) -> Fn(c,[])) consts in
  length(dp_refine_loop (simpcnf sfm) cntms funcs fvs 0 [] [] []);;

START_INTERACTIVE;;
let p36 = davisputnam'
 <<(forall x. exists y. P(x,y)) /\
   (forall x. exists y. G(x,y)) /\
   (forall x y. P(x,y) \/ G(x,y)
                ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
   ==> (forall x. exists y. H(x,y))>>;;

let p29 = davisputnam'
 <<(exists x. P(x)) /\ (exists x. G(x)) ==>
   ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))>>;;
END_INTERACTIVE;;
