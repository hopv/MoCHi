(* ========================================================================= *)
(* Geometry theorem proving.                                                 *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* List of geometric properties with their coordinate translations.          *)
(* ------------------------------------------------------------------------- *)

let coordinations =
  ["collinear", (** Points 1, 2 and 3 lie on a common line **)
   <<(1_x - 2_x) * (2_y - 3_y) = (1_y - 2_y) * (2_x - 3_x)>>;
   "parallel", (** Lines (1,2) and (3,4) are parallel **)
    <<(1_x - 2_x) * (3_y - 4_y) = (1_y - 2_y) * (3_x - 4_x)>>;
   "perpendicular", (** Lines (1,2) and (3,4) are perpendicular **)
   <<(1_x - 2_x) * (3_x - 4_x) + (1_y - 2_y) * (3_y - 4_y) = 0>>;
   "lengths_eq", (** Lines (1,2) and (3,4) have the same length **)
   <<(1_x - 2_x)^2 + (1_y - 2_y)^2 = (3_x - 4_x)^2 + (3_y - 4_y)^2>>;
   "is_midpoint", (** Point 1 is the midpoint of line (2,3) **)
   <<2 * 1_x = 2_x + 3_x /\ 2 * 1_y = 2_y + 3_y>>;
   "is_intersection", (** Lines (2,3) and (4,5) meet at point 1 **)
   <<(1_x - 2_x) * (2_y - 3_y) = (1_y - 2_y) * (2_x - 3_x) /\
     (1_x - 4_x) * (4_y - 5_y) = (1_y - 4_y) * (4_x - 5_x)>>;
   "=", (** Points 1 and 2 are the same **)
   <<(1_x = 2_x) /\ (1_y = 2_y)>>];;

(* ------------------------------------------------------------------------- *)
(* Convert formula into coordinate form.                                     *)
(* ------------------------------------------------------------------------- *)

let coordinate = onatoms
  (fun (R(a,args)) ->
    let xtms,ytms = unzip
     (map (fun (Var v) -> Var(v^"_x"),Var(v^"_y")) args) in
    let xs = map (fun n -> string_of_int n^"_x") (1--length args)
    and ys = map (fun n -> string_of_int n^"_y") (1--length args) in
    subst (fpf (xs @ ys) (xtms @ ytms)) (assoc a coordinations));;

(* ------------------------------------------------------------------------- *)
(* Trivial example.                                                          *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
coordinate <<collinear(a,b,c) ==> collinear(b,a,c)>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Verify equivalence under rotation.                                        *)
(* ------------------------------------------------------------------------- *)

let invariant (x',y') ((s:string),z) =
  let m n f =
    let x = string_of_int n^"_x" and y = string_of_int n^"_y" in
    let i = fpf ["x";"y"] [Var x;Var y] in
    (x |-> tsubst i x') ((y |-> tsubst i y') f) in
  Iff(z,subst(itlist m (1--5) undefined) z);;

let invariant_under_translation = invariant (<<|x + X|>>,<<|y + Y|>>);;

START_INTERACTIVE;;
forall (grobner_decide ** invariant_under_translation) coordinations;;
END_INTERACTIVE;;

let invariant_under_rotation fm =
  Imp(<<s^2 + c^2 = 1>>,
      invariant (<<|c * x - s * y|>>,<<|s * x + c * y|>>) fm);;

START_INTERACTIVE;;
forall (grobner_decide ** invariant_under_rotation) coordinations;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* And show we can always invent such a transformation to zero a y:          *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
real_qelim
 <<forall x y. exists s c. s^2 + c^2 = 1 /\ s * x + c * y = 0>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Choose one point to be the origin and rotate to zero another y coordinate *)
(* ------------------------------------------------------------------------- *)

let originate fm =
  let a::b::ovs = fv fm in
  subst (fpf [a^"_x"; a^"_y"; b^"_y"] [zero; zero; zero])
        (coordinate fm);;

(* ------------------------------------------------------------------------- *)
(* Other interesting invariances.                                            *)
(* ------------------------------------------------------------------------- *)

let invariant_under_scaling fm =
  Imp(<<~(A = 0)>>,invariant(<<|A * x|>>,<<|A * y|>>) fm);;

let invariant_under_shearing = invariant(<<|x + b * y|>>,<<|y|>>);;

START_INTERACTIVE;;
forall (grobner_decide ** invariant_under_scaling) coordinations;;

partition (grobner_decide ** invariant_under_shearing) coordinations;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* One from "Algorithms for Computer Algebra"                                *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
(grobner_decide ** originate)
 <<is_midpoint(m,a,c) /\ perpendicular(a,c,m,b)
   ==> lengths_eq(a,b,b,c)>>;;

(* ------------------------------------------------------------------------- *)
(* Parallelogram theorem (Chou's expository example at the start).           *)
(* ------------------------------------------------------------------------- *)

(grobner_decide ** originate)
 <<parallel(a,b,d,c) /\ parallel(a,d,b,c) /\
   is_intersection(e,a,c,b,d)
   ==> lengths_eq(a,e,e,c)>>;;

(grobner_decide ** originate)
 <<parallel(a,b,d,c) /\ parallel(a,d,b,c) /\
   is_intersection(e,a,c,b,d) /\ ~collinear(a,b,c)
   ==> lengths_eq(a,e,e,c)>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Reduce p using triangular set, collecting degenerate conditions.          *)
(* ------------------------------------------------------------------------- *)

let rec pprove vars triang p degens =
  if p = zero then degens else
  match triang with
    [] -> (mk_eq p zero)::degens
  | (Fn("+",[c;Fn("*",[Var x;_])]) as q)::qs ->
        if x <> hd vars then
          if mem (hd vars) (fvt p)
          then itlist (pprove vars triang) (coefficients vars p) degens
          else pprove (tl vars) triang p degens
        else
          let k,p' = pdivide vars p q in
          if k = 0 then pprove vars qs p' degens else
          let degens' = Not(mk_eq (head vars q) zero)::degens in
          itlist (pprove vars qs) (coefficients vars p') degens';;

(* ------------------------------------------------------------------------- *)
(* Triangulate a set of polynomials.                                         *)
(* ------------------------------------------------------------------------- *)

let rec triangulate vars consts pols =
  if vars = [] then pols else
  let cns,tpols = partition (is_constant vars) pols in
  if cns <> [] then triangulate vars (cns @ consts) tpols else
  if length pols <= 1 then pols @ triangulate (tl vars) [] consts else
  let n = end_itlist min (map (degree vars) pols) in
  let p = find (fun p -> degree vars p = n) pols in
  let ps = subtract pols [p] in
  triangulate vars consts (p::map (fun q -> snd(pdivide vars q p)) ps);;

(* ------------------------------------------------------------------------- *)
(* Trivial version of Wu's method based on repeated pseudo-division.         *)
(* ------------------------------------------------------------------------- *)

let wu fm vars zeros =
  let gfm0 = coordinate fm in
  let gfm = subst(itlist (fun v -> v |-> zero) zeros undefined) gfm0 in
  if not (set_eq vars (fv gfm)) then failwith "wu: bad parameters" else
  let ant,con = dest_imp gfm in
  let pols = map (lhs ** polyatom vars) (conjuncts ant)
  and ps = map (lhs ** polyatom vars) (conjuncts con) in
  let tri = triangulate vars [] pols in
  itlist (fun p -> union(pprove vars tri p [])) ps [];;

(* ------------------------------------------------------------------------- *)
(* Simson's theorem.                                                         *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let simson =
 <<lengths_eq(o,a,o,b) /\
   lengths_eq(o,a,o,c) /\
   lengths_eq(o,a,o,d) /\
   collinear(e,b,c) /\
   collinear(f,a,c) /\
   collinear(g,a,b) /\
   perpendicular(b,c,d,e) /\
   perpendicular(a,c,d,f) /\
   perpendicular(a,b,d,g)
   ==> collinear(e,f,g)>>;;

let vars =
 ["g_y"; "g_x"; "f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x"; "c_y"; "c_x";
  "b_y"; "b_x"; "o_x"]
and zeros = ["a_x"; "a_y"; "o_y"];;

wu simson vars zeros;;

(* ------------------------------------------------------------------------- *)
(* Try without special coordinates.                                          *)
(* ------------------------------------------------------------------------- *)

wu simson (vars @ zeros) [];;

(* ------------------------------------------------------------------------- *)
(* Pappus (Chou's figure 6).                                                 *)
(* ------------------------------------------------------------------------- *)

let pappus =
 <<collinear(a1,b2,d) /\
   collinear(a2,b1,d) /\
   collinear(a2,b3,e) /\
   collinear(a3,b2,e) /\
   collinear(a1,b3,f) /\
   collinear(a3,b1,f)
   ==> collinear(d,e,f)>>;;

let vars = ["f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x";
            "b3_y"; "b2_y"; "b1_y"; "a3_x"; "a2_x"; "a1_x"]
and zeros = ["a1_y"; "a2_y"; "a3_y"; "b1_x"; "b2_x"; "b3_x"];;

wu pappus vars zeros;;

(* ------------------------------------------------------------------------- *)
(* The Butterfly (figure 9).                                                 *)
(* ------------------------------------------------------------------------- *)

(****
let butterfly =
 <<lengths_eq(b,o,a,o) /\ lengths_eq(c,o,a,o) /\ lengths_eq(d,o,a,o) /\
   collinear(a,e,c) /\ collinear(d,e,b) /\
   perpendicular(e,f,o,e) /\
   collinear(a,f,d) /\ collinear(f,e,g) /\ collinear(b,c,g)
   ==> is_midpoint(e,f,g)>>;;

let vars = ["g_y"; "g_x"; "f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "c_y";
            "b_y"; "d_x"; "c_x"; "b_x"; "a_x"]
and zeros = ["a_y"; "o_x"; "o_y"];;

 **** This one is costly (too big for laptop, but doable in about 300M)
 **** However, it gives exactly the same degenerate conditions as Chou

wu butterfly vars zeros;;

 ****
 ****)
END_INTERACTIVE;;

(*** Other examples removed from text

(* ------------------------------------------------------------------------- *)
(* Centroid (Chou, example 142).                                             *)
(* ------------------------------------------------------------------------- *)

(grobner_decide ** originate)
 <<is_midpoint(d,b,c) /\ is_midpoint(e,a,c) /\
   is_midpoint(f,a,b) /\ is_intersection(m,b,e,a,d)
   ==> collinear(c,f,m)>>;;

****)
