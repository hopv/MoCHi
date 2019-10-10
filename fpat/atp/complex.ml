(* ========================================================================= *)
(* Complex quantifier elimination (by simple divisibility a la Tarski).      *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Basic arithmetic operations on canonical polynomials.                     *)
(* ------------------------------------------------------------------------- *)

let rec poly_add vars pol1 pol2 =
  match (pol1,pol2) with
   (Fn("+",[c; Fn("*",[Var x; p])]),Fn("+",[d; Fn("*",[Var y; q])])) ->
        if earlier vars x y then poly_ladd vars pol2 pol1
        else if earlier vars y x then poly_ladd vars pol1 pol2 else
        let e = poly_add vars c d and r = poly_add vars p q in
        if r = zero then e else Fn("+",[e; Fn("*",[Var x; r])])
    | (_,Fn("+",_)) -> poly_ladd vars pol1 pol2
    | (Fn("+",_),pol2) -> poly_ladd vars pol2 pol1
    | _ -> numeral2 (+/) pol1 pol2
and poly_ladd vars =
  fun pol1 (Fn("+",[d; Fn("*",[Var y; q])])) ->
        Fn("+",[poly_add vars pol1 d; Fn("*",[Var y; q])]);;

let rec poly_neg =
  function (Fn("+",[c; Fn("*",[Var x; p])])) ->
                Fn("+",[poly_neg c; Fn("*",[Var x; poly_neg p])])
         | n -> numeral1 minus_num n;;

let poly_sub vars p q = poly_add vars p (poly_neg q);;

let rec poly_mul vars pol1 pol2 =
  match (pol1,pol2) with
   (Fn("+",[c; Fn("*",[Var x; p])]),Fn("+",[d; Fn("*",[Var y; q])])) ->
        if earlier vars x y then poly_lmul vars pol2 pol1
        else poly_lmul vars pol1 pol2
  | (Fn("0",[]),_) | (_,Fn("0",[])) -> zero
  | (_,Fn("+",_)) -> poly_lmul vars pol1 pol2
  | (Fn("+",_),_) -> poly_lmul vars pol2 pol1
  | _ -> numeral2 ( */ ) pol1 pol2
and poly_lmul vars =
  fun pol1 (Fn("+",[d; Fn("*",[Var y; q])])) ->
        poly_add vars (poly_mul vars pol1 d)
                     (Fn("+",[zero;
                              Fn("*",[Var y; poly_mul vars pol1 q])]));;

let poly_pow vars p n = funpow n (poly_mul vars p) (Fn("1",[]));;

let poly_div vars p q = poly_mul vars p (numeral1((//) (Int 1)) q);;

let poly_var x = Fn("+",[zero; Fn("*",[Var x; Fn("1",[])])]);;

(* ------------------------------------------------------------------------- *)
(* Convert term into canonical polynomial representative.                    *)
(* ------------------------------------------------------------------------- *)

let rec polynate vars tm =
  match tm with
    Var x -> poly_var x
  | Fn("-",[t]) -> poly_neg (polynate vars t)
  | Fn("+",[s;t]) -> poly_add vars (polynate vars s) (polynate vars t)
  | Fn("-",[s;t]) -> poly_sub vars (polynate vars s) (polynate vars t)
  | Fn("*",[s;t]) -> poly_mul vars (polynate vars s) (polynate vars t)
  | Fn("/",[s;t]) -> poly_div vars (polynate vars s) (polynate vars t)
  | Fn("^",[p;Fn(n,[])]) ->
                     poly_pow vars (polynate vars p) (int_of_string n)
  | _ -> if is_numeral tm then tm else failwith "lint: unknown term";;

(* ------------------------------------------------------------------------- *)
(* Do likewise for atom so the RHS is zero.                                  *)
(* ------------------------------------------------------------------------- *)

let polyatom vars fm =
  match fm with
    Atom(R(a,[s;t])) -> Atom(R(a,[polynate vars (Fn("-",[s;t]));zero]))
  | _ -> failwith "polyatom: not an atom";;

(* ------------------------------------------------------------------------- *)
(* Sanity check.                                                             *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
polyatom ["w"; "x"; "y"; "z"]
  <<((w + x)^4 + (w + y)^4 + (w + z)^4 +
     (x + y)^4 + (x + z)^4 + (y + z)^4 +
     (w - x)^4 + (w - y)^4 + (w - z)^4 +
     (x - y)^4 + (x - z)^4 + (y - z)^4) / 6 =
    (w^2 + x^2 + y^2 + z^2)^2>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Useful utility functions for polynomial terms.                            *)
(* ------------------------------------------------------------------------- *)

let rec coefficients vars =
  function Fn("+",[c; Fn("*",[Var x; q])]) when x = hd vars ->
                c::(coefficients vars q)
         | p -> [p];;

let degree vars p = length(coefficients vars p) - 1;;

let is_constant vars p = degree vars p = 0;;

let head vars p = last(coefficients vars p);;

let rec behead vars =
  function Fn("+",[c; Fn("*",[Var x; p])]) when x = hd vars ->
        let p' = behead vars p in
        if p' = zero then c else Fn("+",[c; Fn("*",[Var x; p'])])
  | _ -> zero;;

(* ------------------------------------------------------------------------- *)
(* Get the constant multiple of the "maximal" monomial (implicit lex order)  *)
(* ------------------------------------------------------------------------- *)

let rec poly_cmul k p =
  match p with
    Fn("+",[c; Fn("*",[Var x; q])]) ->
        Fn("+",[poly_cmul k c; Fn("*",[Var x; poly_cmul k q])])
  | _ -> numeral1 (fun m -> k */ m) p;;

let rec headconst p =
  match p with
    Fn("+",[c; Fn("*",[Var x; q])]) -> headconst q
  | Fn(n,[]) -> dest_numeral p;;

(* ------------------------------------------------------------------------- *)
(* Make a polynomial monic and return negativity flag for head constant      *)
(* ------------------------------------------------------------------------- *)

let monic p =
  let h = headconst p in
  if h =/ Int 0 then p,false else poly_cmul (Int 1 // h) p,h </ Int 0;;

(* ------------------------------------------------------------------------- *)
(* Pseudo-division of s by p; head coefficient of p assumed nonzero.         *)
(* Returns (k,r) so that a^k s = p q + r for some q, deg(r) < deg(p).        *)
(* Optimized only for the trivial case of equal head coefficients; no GCDs.  *)
(* ------------------------------------------------------------------------- *)

let pdivide =
  let shift1 x p = Fn("+",[zero; Fn("*",[Var x; p])]) in
  let rec pdivide_aux vars a n p k s =
    if s = zero then (k,s) else
    let b = head vars s and m = degree vars s in
    if m < n then (k,s) else
    let p' = funpow (m - n) (shift1 (hd vars)) p in
    if a = b then pdivide_aux vars a n p k (poly_sub vars s p')
    else pdivide_aux vars a n p (k+1)
          (poly_sub vars (poly_mul vars a s) (poly_mul vars b p')) in
  fun vars s p -> pdivide_aux vars (head vars p) (degree vars p) p 0 s;;

(* ------------------------------------------------------------------------- *)
(* Datatype of signs.                                                        *)
(* ------------------------------------------------------------------------- *)

type sign = Zero | Nonzero | Positive | Negative;;

let swap swf s =
  if not swf then s else
  match s with
    Positive -> Negative
  | Negative -> Positive
  | _ -> s;;

(* ------------------------------------------------------------------------- *)
(* Lookup and asserting of polynomial sign, modulo constant multiples.       *)
(* Note that we are building in a characteristic-zero assumption here.       *)
(* ------------------------------------------------------------------------- *)

let findsign sgns p =
  try let p',swf = monic p in swap swf (assoc p' sgns)
  with Failure _ -> failwith "findsign";;

let assertsign sgns (p,s) =
  if p = zero then if s = Zero then sgns else failwith "assertsign" else
  let p',swf = monic p in
  let s' = swap swf s in
  let s0 = try assoc p' sgns with Failure _ -> s' in
  if s' = s0 or s0 = Nonzero & (s' = Positive or s' = Negative)
  then (p',s')::(subtract sgns [p',s0]) else failwith "assertsign";;

(* ------------------------------------------------------------------------- *)
(* Deduce or case-split over zero status of polynomial.                      *)
(* ------------------------------------------------------------------------- *)

let split_zero sgns pol cont_z cont_n =
  try let z = findsign sgns pol in
      (if z = Zero then cont_z else cont_n) sgns
  with Failure "findsign" ->
      let eq = Atom(R("=",[pol; zero])) in
      Or(And(eq,cont_z (assertsign sgns (pol,Zero))),
         And(Not eq,cont_n (assertsign sgns (pol,Nonzero))));;

(* ------------------------------------------------------------------------- *)
(* Whether a polynomial is nonzero in a context.                             *)
(* ------------------------------------------------------------------------- *)

let poly_nonzero vars sgns pol =
  let cs = coefficients vars pol in
  let dcs,ucs = partition (can (findsign sgns)) cs in
  if exists (fun p -> findsign sgns p <> Zero) dcs then True
  else if ucs = [] then False else
  end_itlist mk_or (map (fun p -> Not(mk_eq p zero)) ucs);;

(* ------------------------------------------------------------------------- *)
(* Non-divisibility of q by p.                                               *)
(* ------------------------------------------------------------------------- *)

let rec poly_nondiv vars sgns p s =
  let _,r = pdivide vars s p in poly_nonzero vars sgns r;;

(* ------------------------------------------------------------------------- *)
(* Main reduction for exists x. all eqs = 0 and all neqs =/= 0, in context.  *)
(* ------------------------------------------------------------------------- *)

let rec cqelim vars (eqs,neqs) sgns =
  try let c = find (is_constant vars) eqs in
     (try let sgns' = assertsign sgns (c,Zero)
          and eqs' = subtract eqs [c] in
          And(mk_eq c zero,cqelim vars (eqs',neqs) sgns')
      with Failure "assertsign" -> False)
  with Failure _ ->
     if eqs = [] then list_conj(map (poly_nonzero vars sgns) neqs) else
     let n = end_itlist min (map (degree vars) eqs) in
     let p = find (fun p -> degree vars p = n) eqs in
     let oeqs = subtract eqs [p] in
     split_zero sgns (head vars p)
       (cqelim vars (behead vars p::oeqs,neqs))
       (fun sgns' ->
          let cfn s = snd(pdivide vars s p) in
          if oeqs <> [] then cqelim vars (p::(map cfn oeqs),neqs) sgns'
          else if neqs = [] then True else
          let q = end_itlist (poly_mul vars) neqs in
          poly_nondiv vars sgns' p (poly_pow vars q (degree vars p)));;

(* ------------------------------------------------------------------------- *)
(* Basic complex quantifier elimination on actual existential formula.       *)
(* ------------------------------------------------------------------------- *)

let init_sgns = [Fn("1",[]),Positive; Fn("0",[]),Zero];;

let basic_complex_qelim vars (Exists(x,p)) =
  let eqs,neqs = partition (non negative) (conjuncts p) in
  cqelim (x::vars) (map lhs eqs,map (lhs ** negate) neqs) init_sgns;;

(* ------------------------------------------------------------------------- *)
(* Full quantifier elimination.                                              *)
(* ------------------------------------------------------------------------- *)

let complex_qelim =
  simplify ** evalc **
  lift_qelim polyatom (dnf ** cnnf (fun x -> x) ** evalc)
             basic_complex_qelim;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
complex_qelim
 <<forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 1 = 0>>;;

complex_qelim
 <<forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + c = 0>>;;

complex_qelim
 <<forall c.
     (forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + c = 0)
     <=> c = 1>>;;

complex_qelim
 <<forall a b c x y.
      a * x^2 + b * x + c = 0 /\ a * y^2 + b * y + c = 0 /\ ~(x = y)
      ==> a * x * y = c /\ a * (x + y) + b = 0>>;;

(* ------------------------------------------------------------------------- *)
(* More tests, not in the main text.                                         *)
(* ------------------------------------------------------------------------- *)

let polytest tm = time (polynate (fvt tm)) tm;;

let lagrange_4 = polytest
 <<|(((x1^2) + (x2^2) + (x3^2) + (x4^2)) *
     ((y1^2) + (y2^2) + (y3^2) + (y4^2))) -
    ((((((x1*y1) - (x2*y2)) - (x3*y3)) - (x4*y4))^2)  +
     (((((x1*y2) + (x2*y1)) + (x3*y4)) - (x4*y3))^2)  +
     (((((x1*y3) - (x2*y4)) + (x3*y1)) + (x4*y2))^2)  +
     (((((x1*y4) + (x2*y3)) - (x3*y2)) + (x4*y1))^2))|>>;;

let lagrange_8 = polytest
 <<|((p1^2 + q1^2 + r1^2 + s1^2 + t1^2 + u1^2 + v1^2 + w1^2) *
     (p2^2 + q2^2 + r2^2 + s2^2 + t2^2 + u2^2 + v2^2 + w2^2)) -
     ((p1 * p2 - q1 * q2 - r1 * r2 - s1 * s2 - t1 * t2 - u1 * u2 - v1 * v2 - w1* w2)^2 +
      (p1 * q2 + q1 * p2 + r1 * s2 - s1 * r2 + t1 * u2 - u1 * t2 - v1 * w2 + w1* v2)^2 +
      (p1 * r2 - q1 * s2 + r1 * p2 + s1 * q2 + t1 * v2 + u1 * w2 - v1 * t2 - w1* u2)^2 +
      (p1 * s2 + q1 * r2 - r1 * q2 + s1 * p2 + t1 * w2 - u1 * v2 + v1 * u2 - w1* t2)^2 +
      (p1 * t2 - q1 * u2 - r1 * v2 - s1 * w2 + t1 * p2 + u1 * q2 + v1 * r2 + w1* s2)^2 +
      (p1 * u2 + q1 * t2 - r1 * w2 + s1 * v2 - t1 * q2 + u1 * p2 - v1 * s2 + w1* r2)^2 +
      (p1 * v2 + q1 * w2 + r1 * t2 - s1 * u2 - t1 * r2 + u1 * s2 + v1 * p2 - w1* q2)^2 +
      (p1 * w2 - q1 * v2 + r1 * u2 + s1 * t2 - t1 * s2 - u1 * r2 + v1 * q2 + w1* p2)^2)|>>;;

let liouville = polytest
 <<|6 * (x1^2 + x2^2 + x3^2 + x4^2)^2 -
    (((x1 + x2)^4 + (x1 + x3)^4 + (x1 + x4)^4 +
      (x2 + x3)^4 + (x2 + x4)^4 + (x3 + x4)^4) +
     ((x1 - x2)^4 + (x1 - x3)^4 + (x1 - x4)^4 +
      (x2 - x3)^4 + (x2 - x4)^4 + (x3 - x4)^4))|>>;;

let fleck = polytest
 <<|60 * (x1^2 + x2^2 + x3^2 + x4^2)^3 -
    (((x1 + x2 + x3)^6 + (x1 + x2 - x3)^6 +
      (x1 - x2 + x3)^6 + (x1 - x2 - x3)^6 +
      (x1 + x2 + x4)^6 + (x1 + x2 - x4)^6 +
      (x1 - x2 + x4)^6 + (x1 - x2 - x4)^6 +
      (x1 + x3 + x4)^6 + (x1 + x3 - x4)^6 +
      (x1 - x3 + x4)^6 + (x1 - x3 - x4)^6 +
      (x2 + x3 + x4)^6 + (x2 + x3 - x4)^6 +
      (x2 - x3 + x4)^6 + (x2 - x3 - x4)^6) +
     2 * ((x1 + x2)^6 + (x1 - x2)^6 +
          (x1 + x3)^6 + (x1 - x3)^6 +
          (x1 + x4)^6 + (x1 - x4)^6 +
          (x2 + x3)^6 + (x2 - x3)^6 +
          (x2 + x4)^6 + (x2 - x4)^6 +
          (x3 + x4)^6 + (x3 - x4)^6) +
     36 * (x1^6 + x2^6 + x3^6 + x4^6))|>>;;

let hurwitz = polytest
 <<|5040 * (x1^2 + x2^2 + x3^2 + x4^2)^4 -
    (6 * ((x1 + x2 + x3 + x4)^8 +
          (x1 + x2 + x3 - x4)^8 +
          (x1 + x2 - x3 + x4)^8 +
          (x1 + x2 - x3 - x4)^8 +
          (x1 - x2 + x3 + x4)^8 +
          (x1 - x2 + x3 - x4)^8 +
          (x1 - x2 - x3 + x4)^8 +
          (x1 - x2 - x3 - x4)^8) +
     ((2 * x1 + x2 + x3)^8 +
      (2 * x1 + x2 - x3)^8 +
      (2 * x1 - x2 + x3)^8 +
      (2 * x1 - x2 - x3)^8 +
      (2 * x1 + x2 + x4)^8 +
      (2 * x1 + x2 - x4)^8 +
      (2 * x1 - x2 + x4)^8 +
      (2 * x1 - x2 - x4)^8 +
      (2 * x1 + x3 + x4)^8 +
      (2 * x1 + x3 - x4)^8 +
      (2 * x1 - x3 + x4)^8 +
      (2 * x1 - x3 - x4)^8 +
      (2 * x2 + x3 + x4)^8 +
      (2 * x2 + x3 - x4)^8 +
      (2 * x2 - x3 + x4)^8 +
      (2 * x2 - x3 - x4)^8 +
      (x1 + 2 * x2 + x3)^8 +
      (x1 + 2 * x2 - x3)^8 +
      (x1 - 2 * x2 + x3)^8 +
      (x1 - 2 * x2 - x3)^8 +
      (x1 + 2 * x2 + x4)^8 +
      (x1 + 2 * x2 - x4)^8 +
      (x1 - 2 * x2 + x4)^8 +
      (x1 - 2 * x2 - x4)^8 +
      (x1 + 2 * x3 + x4)^8 +
      (x1 + 2 * x3 - x4)^8 +
      (x1 - 2 * x3 + x4)^8 +
      (x1 - 2 * x3 - x4)^8 +
      (x2 + 2 * x3 + x4)^8 +
      (x2 + 2 * x3 - x4)^8 +
      (x2 - 2 * x3 + x4)^8 +
      (x2 - 2 * x3 - x4)^8 +
      (x1 + x2 + 2 * x3)^8 +
      (x1 + x2 - 2 * x3)^8 +
      (x1 - x2 + 2 * x3)^8 +
      (x1 - x2 - 2 * x3)^8 +
      (x1 + x2 + 2 * x4)^8 +
      (x1 + x2 - 2 * x4)^8 +
      (x1 - x2 + 2 * x4)^8 +
      (x1 - x2 - 2 * x4)^8 +
      (x1 + x3 + 2 * x4)^8 +
      (x1 + x3 - 2 * x4)^8 +
      (x1 - x3 + 2 * x4)^8 +
      (x1 - x3 - 2 * x4)^8 +
      (x2 + x3 + 2 * x4)^8 +
      (x2 + x3 - 2 * x4)^8 +
      (x2 - x3 + 2 * x4)^8 +
      (x2 - x3 - 2 * x4)^8) +
     60 * ((x1 + x2)^8 + (x1 - x2)^8 +
           (x1 + x3)^8 + (x1 - x3)^8 +
           (x1 + x4)^8 + (x1 - x4)^8 +
           (x2 + x3)^8 + (x2 - x3)^8 +
           (x2 + x4)^8 + (x2 - x4)^8 +
           (x3 + x4)^8 + (x3 - x4)^8) +
     6 * ((2 * x1)^8 + (2 * x2)^8 + (2 * x3)^8 + (2 * x4)^8))|>>;;

let schur = polytest
 <<|22680 * (x1^2 + x2^2 + x3^2 + x4^2)^5 -
    (9 * ((2 * x1)^10 +
          (2 * x2)^10 +
          (2 * x3)^10 +
          (2 * x4)^10) +
     180 * ((x1 + x2)^10 + (x1 - x2)^10 +
            (x1 + x3)^10 + (x1 - x3)^10 +
            (x1 + x4)^10 + (x1 - x4)^10 +
            (x2 + x3)^10 + (x2 - x3)^10 +
            (x2 + x4)^10 + (x2 - x4)^10 +
            (x3 + x4)^10 + (x3 - x4)^10) +
     ((2 * x1 + x2 + x3)^10 +
      (2 * x1 + x2 - x3)^10 +
      (2 * x1 - x2 + x3)^10 +
      (2 * x1 - x2 - x3)^10 +
      (2 * x1 + x2 + x4)^10 +
      (2 * x1 + x2 - x4)^10 +
      (2 * x1 - x2 + x4)^10 +
      (2 * x1 - x2 - x4)^10 +
      (2 * x1 + x3 + x4)^10 +
      (2 * x1 + x3 - x4)^10 +
      (2 * x1 - x3 + x4)^10 +
      (2 * x1 - x3 - x4)^10 +
      (2 * x2 + x3 + x4)^10 +
      (2 * x2 + x3 - x4)^10 +
      (2 * x2 - x3 + x4)^10 +
      (2 * x2 - x3 - x4)^10 +
      (x1 + 2 * x2 + x3)^10 +
      (x1 + 2 * x2 - x3)^10 +
      (x1 - 2 * x2 + x3)^10 +
      (x1 - 2 * x2 - x3)^10 +
      (x1 + 2 * x2 + x4)^10 +
      (x1 + 2 * x2 - x4)^10 +
      (x1 - 2 * x2 + x4)^10 +
      (x1 - 2 * x2 - x4)^10 +
      (x1 + 2 * x3 + x4)^10 +
      (x1 + 2 * x3 - x4)^10 +
      (x1 - 2 * x3 + x4)^10 +
      (x1 - 2 * x3 - x4)^10 +
      (x2 + 2 * x3 + x4)^10 +
      (x2 + 2 * x3 - x4)^10 +
      (x2 - 2 * x3 + x4)^10 +
      (x2 - 2 * x3 - x4)^10 +
      (x1 + x2 + 2 * x3)^10 +
      (x1 + x2 - 2 * x3)^10 +
      (x1 - x2 + 2 * x3)^10 +
      (x1 - x2 - 2 * x3)^10 +
      (x1 + x2 + 2 * x4)^10 +
      (x1 + x2 - 2 * x4)^10 +
      (x1 - x2 + 2 * x4)^10 +
      (x1 - x2 - 2 * x4)^10 +
      (x1 + x3 + 2 * x4)^10 +
      (x1 + x3 - 2 * x4)^10 +
      (x1 - x3 + 2 * x4)^10 +
      (x1 - x3 - 2 * x4)^10 +
      (x2 + x3 + 2 * x4)^10 +
      (x2 + x3 - 2 * x4)^10 +
      (x2 - x3 + 2 * x4)^10 +
      (x2 - x3 - 2 * x4)^10) +
     9 * ((x1 + x2 + x3 + x4)^10 +
          (x1 + x2 + x3 - x4)^10 +
          (x1 + x2 - x3 + x4)^10 +
          (x1 + x2 - x3 - x4)^10 +
          (x1 - x2 + x3 + x4)^10 +
          (x1 - x2 + x3 - x4)^10 +
          (x1 - x2 - x3 + x4)^10 +
          (x1 - x2 - x3 - x4)^10))|>>;;

let complex_qelim_all = time complex_qelim ** generalize;;

time complex_qelim <<exists x. x + 2 = 3>>;;

time complex_qelim <<exists x. x^2 + a = 3>>;;

time complex_qelim <<exists x. x^2 + x + 1 = 0>>;;

time complex_qelim <<exists x. x^2 + x + 1 = 0 /\ x^3 + x^2 + 1 = 0>>;;

time complex_qelim <<exists x. x^2 + 1 = 0 /\ x^4 + x^3 + x^2 + x = 0>>;;

time complex_qelim <<forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 1 = 0>>;;

time complex_qelim <<forall a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0>>;;

time complex_qelim <<exists a x. a^2 = 2 /\ x^2 + a * x + 1 = 0 /\ ~(x^4 + 2 = 0)>>;;

time complex_qelim <<exists x. a^2 = 2 /\ x^2 + a * x + 1 = 0 /\ ~(x^4 + 2 = 0)>>;;

time complex_qelim <<forall x. x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0>>;;

time complex_qelim <<forall a. a^2 = 2 /\ x^2 + a * x + 1 = 0 ==> x^4 + 2 = 0>>;;

time complex_qelim <<exists a b c x y.
        a * x^2 + b * x + c = 0 /\
        a * y^2 + b * y + c = 0 /\
        ~(x = y) /\
        ~(a * x * y = c)>>;;

(*** This works by a combination with grobner_decide but seems slow like this:

complex_qelim
 <<forall a b c x y.
      ~(a = 0) /\
      (forall z. a * z^2 + b * z + c = 0 <=> z = x) /\ x = y
      ==> a * x * y = c /\ a * (x + y) + b = 0>>;;

 *** and w/o the condition, it's false I think

complex_qelim
 <<forall a b c x y.
      (forall z. a * z^2 + b * z + c = 0 <=> z = x \/ z = y)
      ==> a * x * y = c /\ a * (x + y) + b = 0>>;;

 *** because the following is!

 ***)

complex_qelim
 <<forall a b c x.
        (forall z. a * z^2 + b * z + c = 0 <=> z = x)
        ==> a * x * x = c /\ a * (x + x) + b = 0>>;;

(*** In fact we have this, tho' I don't know if that's interesting ***)

complex_qelim
 <<forall x y.
    (forall a b c. (a * x^2 + b * x + c = 0) /\
                   (a * y^2 + b * y + c = 0)
                   ==> (a * x * y = c) /\ (a * (x + y) + b = 0))
    <=> ~(x = y)>>;;

time complex_qelim
 <<forall y_1 y_2 y_3 y_4.
     (y_1 = 2 * y_3) /\
     (y_2 = 2 * y_4) /\
     (y_1 * y_3 = y_2 * y_4)
     ==> (y_1^2 = y_2^2)>>;;

time complex_qelim
 <<forall x y. x^2 = 2 /\ y^2 = 3
         ==> (x * y)^2 = 6>>;;

time complex_qelim
 <<forall x a. (a^2 = 2) /\ (x^2 + a * x + 1 = 0)
         ==> (x^4 + 1 = 0)>>;;

time complex_qelim
 <<forall a x. (a^2 = 2) /\ (x^2 + a * x + 1 = 0)
         ==> (x^4 + 1 = 0)>>;;

time complex_qelim
 <<~(exists a x y. (a^2 = 2) /\
             (x^2 + a * x + 1 = 0) /\
             (y * (x^4 + 1) + 1 = 0))>>;;

time complex_qelim <<forall x. exists y. x^2 = y^3>>;;

time complex_qelim
 <<forall x y z a b. (a + b) * (x - y + z) - (a - b) * (x + y + z) =
               2 * (b * x + b * z - a * y)>>;;

time complex_qelim
 <<forall a b. ~(a = b) ==> exists x y. (y * x^2 = a) /\ (y * x^2 + x = b)>>;;

time complex_qelim
 <<forall a b c x y. (a * x^2 + b * x + c = 0) /\
               (a * y^2 + b * y + c = 0) /\
               ~(x = y)
               ==> (a * x * y = c) /\ (a * (x + y) + b = 0)>>;;

time complex_qelim
 <<~(forall a b c x y. (a * x^2 + b * x + c = 0) /\
                 (a * y^2 + b * y + c = 0)
                 ==> (a * x * y = c) /\ (a * (x + y) + b = 0))>>;;

time complex_qelim
 <<forall y_1 y_2 y_3 y_4.
     (y_1 = 2 * y_3) /\
     (y_2 = 2 * y_4) /\
     (y_1 * y_3 = y_2 * y_4)
     ==> (y_1^2 = y_2^2)>>;;

time complex_qelim
 <<forall a1 b1 c1 a2 b2 c2.
        ~(a1 * b2 = a2 * b1)
        ==> exists x y. (a1 * x + b1 * y = c1) /\ (a2 * x + b2 * y = c2)>>;;

(* ------------------------------------------------------------------------- *)
(* This seems harder, so see how many quantifiers are feasible.              *)
(* ------------------------------------------------------------------------- *)

time complex_qelim
 <<(a * x^2 + b * x + c = 0) /\
  (a * y^2 + b * y + c = 0) /\
  (forall z. (a * z^2 + b * z + c = 0)
       ==> (z = x) \/ (z = y))
  ==> (a * x * y = c) /\ (a * (x + y) + b = 0)>>;;

time complex_qelim
 <<forall y. (a * x^2 + b * x + c = 0) /\
            (a * y^2 + b * y + c = 0) /\
            (forall z. (a * z^2 + b * z + c = 0)
                       ==> (z = x) \/ (z = y))
            ==> (a * x * y = c) /\ (a * (x + y) + b = 0)>>;;

(**** feasible but lengthy?

time complex_qelim
 <<forall x y. (a * x^2 + b * x + c = 0) /\
              (a * y^2 + b * y + c = 0) /\
              (forall z. (a * z^2 + b * z + c = 0)
                         ==> (z = x) \/ (z = y))
              ==> (a * x * y = c) /\ (a * (x + y) + b = 0)>>;;

time complex_qelim
 <<forall c x y. (a * x^2 + b * x + c = 0) /\
              (a * y^2 + b * y + c = 0) /\
              (forall z. (a * z^2 + b * z + c = 0)
                         ==> (z = x) \/ (z = y))
              ==> (a * x * y = c) /\ (a * (x + y) + b = 0)>>;;

 ************)

(********* This seems too hard

time complex_qelim
 <<forall a b c x y. (a * x^2 + b * x + c = 0) /\
               (a * y^2 + b * y + c = 0) /\
               (forall z. (a * z^2 + b * z + c = 0)
                    ==> (z = x) \/ (z = y))
               ==> (a * x * y = c) /\ (a * (x + y) + b = 0)>>;;

 **************)

time complex_qelim
 <<~(forall x1 y1 x2 y2 x3 y3.
      exists x0 y0. (x1 - x0)^2 + (y1 - y0)^2 = (x2 - x0)^2 + (y2 - y0)^2 /\
                    (x2 - x0)^2 + (y2 - y0)^2 = (x3 - x0)^2 + (y3 - y0)^2)>>;;

time complex_qelim
 <<forall a b c.
      (exists x y. (a * x^2 + b * x + c = 0) /\
             (a * y^2 + b * y + c = 0) /\
             ~(x = y)) <=>
      (a = 0) /\ (b = 0) /\ (c = 0) \/
      ~(a = 0) /\ ~(b^2 = 4 * a * c)>>;;

time complex_qelim
 <<~(forall x1 y1 x2 y2 x3 y3 x0 y0 x0' y0'.
        (x1 - x0)^2 + (y1 - y0)^2 =
        (x2 - x0)^2 + (y2 - y0)^2 /\
        (x2 - x0)^2 + (y2 - y0)^2 =
        (x3 - x0)^2 + (y3 - y0)^2 /\
        (x1 - x0')^2 + (y1 - y0')^2 =
        (x2 - x0')^2 + (y2 - y0')^2 /\
        (x2 - x0')^2 + (y2 - y0')^2 =
        (x3 - x0')^2 + (y3 - y0')^2
        ==> x0 = x0' /\ y0 = y0')>>;;

time complex_qelim
 <<forall a b c.
        a * x^2 + b * x + c = 0 /\
        a * y^2 + b * y + c = 0 /\
        ~(x = y)
        ==> a * (x + y) + b = 0>>;;

time complex_qelim
 <<forall a b c.
        (a * x^2 + b * x + c = 0) /\
        (2 * a * y^2 + 2 * b * y + 2 * c = 0) /\
        ~(x = y)
        ==> (a * (x + y) + b = 0)>>;;

complex_qelim_all
 <<~(y_1 = 2 * y_3 /\
    y_2 = 2 * y_4 /\
    y_1 * y_3 = y_2 * y_4 /\
    (y_1^2 - y_2^2) * z = 1)>>;;

time complex_qelim <<forall y_1 y_2 y_3 y_4.
       (y_1 = 2 * y_3) /\
       (y_2 = 2 * y_4) /\
       (y_1 * y_3 = y_2 * y_4)
       ==> (y_1^2 = y_2^2)>>;;

(************

complex_qelim_all
 <<~((c^2 = a^2 + b^2) /\
     (c^2 = x0^2 + (y0 - b)^2) /\
     (y0 * t1 = a + x0) /\
     (y0 * t2 = a - x0) /\
     ((1 - t1 * t2) * t = t1 + t2) /\
     (u * (b * t - a) = 1) /\
     (v1 * a + v2 * x0 + v3 * y0 = 1))>>;;

complex_qelim_all
 <<(c^2 = a^2 + b^2) /\
   (c^2 = x0^2 + (y0 - b)^2) /\
   (y0 * t1 = a + x0) /\
   (y0 * t2 = a - x0) /\
   ((1 - t1 * t2) * t = t1 + t2) /\
   (~(a = 0) \/ ~(x0 = 0) \/ ~(y0 = 0))
   ==> (b * t = a)>>;;

*********)

complex_qelim_all
 <<(x1 = u3) /\
  (x1 * (u2 - u1) = x2 * u3) /\
  (x4 * (x2 - u1) = x1 * (x3 - u1)) /\
  (x3 * u3 = x4 * u2) /\
  ~(u1 = 0) /\
  ~(u3 = 0)
  ==> (x3^2 + x4^2 = (u2 - x3)^2 + (u3 - x4)^2)>>;;

complex_qelim_all
 <<(u1 * x1 - u1 * u3 = 0) /\
  (u3 * x2 - (u2 - u1) * x1 = 0) /\
  (x1 * x4 - (x2 - u1) * x3 - u1 * x1 = 0) /\
  (u3 * x4 - u2 * x3 = 0) /\
  ~(u1 = 0) /\
  ~(u3 = 0)
  ==> (2 * u2 * x4 + 2 * u3 * x3 - u3^2 - u2^2 = 0)>>;;

complex_qelim_all
 <<(y1 * y3 + x1 * x3 = 0) /\
  (y3 * (y2 - y3) + (x2 - x3) * x3 = 0) /\
  ~(x3 = 0) /\
  ~(y3 = 0)
  ==> (y1 * (x2 - x3) = x1 * (y2 - y3))>>;;

(**********

complex_qelim_all
 <<(2 * u2 * x2 + 2 * u3 * x1 - u3^2 - u2^2 = 0) /\
  (2 * u1 * x2 - u1^2 = 0) /\
  (-(x3^2) + 2 * x2 * x3 + 2 * u4 * x1 - u4^2 = 0) /\
  (u3 * x5 + (-(u2) + u1) * x4 - u1 * u3 = 0) /\
  ((u2 - u1) * x5 + u3 * x4 + (-(u2) + u1) * x3 - u3 * u4 = 0) /\
  (u3 * x7 - u2 * x6 = 0) /\
  (u2 * x7 + u3 * x6 - u2 * x3 - u3 * u4 = 0) /\
  ~(4 * u1 * u3 = 0) /\
  ~(2 * u1 = 0) /\
  ~(-(u3^2) - u2^2 + 2 * u1 * u2 - u1^2 = 0) /\
  ~(u3 = 0) /\
  ~(-(u3^2) - u2^2 = 0) /\
  ~(u2 = 0)
  ==> (x4 * x7 + (-(x5) + x3) * x6 - x3 * x4 = 0)>>;;

time complex_qelim
 <<exists c.
    (p1 = ai^2 * (b + c)^2 - c * b * (c + b - a) * (c + b + a)) /\
    (p2 = ae^2 * (c - b)^2 - c * b * (a + b - c) * (a - b + a)) /\
    (p3 = be^2 * (c - a)^2 - a * c * (a + b - c) * (c + b - a))>>;;

time complex_qelim
 <<exists b c.
    (p1 = ai^2 * (b + c)^2 - c * b * (c + b - a) * (c + b + a)) /\
    (p2 = ae^2 * (c - b)^2 - c * b * (a + b - c) * (a - b + a)) /\
    (p3 = be^2 * (c - a)^2 - a * c * (a + b - c) * (c + b - a))>>;;

*********)

time complex_qelim <<forall y.
         a * x^2 + b * x + c = 0 /\
         a * y^2 + b * y + c = 0 /\
         ~(x = y)
         ==> a * x * y = c /\ a * (x + y) + b = 0>>;;

complex_qelim_all
 <<a * x^2 + b * x + c = 0 /\
    a * y^2 + b * y + c = 0 /\
    ~(x = y)
    ==> a * x * y = c /\ a * (x + y) + b = 0>>;;

(* ------------------------------------------------------------------------- *)
(* The Colmerauer example.                                                   *)
(* ------------------------------------------------------------------------- *)

(********* This works, but is quite slow. And it's false! Presumably we
           actually need to use ordering properties associated with absolute
           values

let colmerauer = complex_qelim_all
 <<(x_1 + x_3  = (x_2) \/ x_1 + x_3  = -(x_2)) /\
   (x_2 + x_4  = (x_3) \/ x_2 + x_4  = -(x_3)) /\
   (x_3 + x_5  = (x_4) \/ x_3 + x_5  = -(x_4)) /\
   (x_4 + x_6  = (x_5) \/ x_4 + x_6  = -(x_5)) /\
   (x_5 + x_7  = (x_6) \/ x_5 + x_7  = -(x_6)) /\
   (x_6 + x_8  = (x_7) \/ x_6 + x_8  = -(x_7)) /\
   (x_7 + x_9  = (x_8) \/ x_7 + x_9  = -(x_8)) /\
   (x_8 + x_10 = (x_9) \/ x_8 + x_10 = -(x_9)) /\
   (x_9 + x_11 = (x_10) \/ x_9 + x_11 = -(x_10))
   ==> x_1 = x_10 /\ x_2 = x_11>>;;

 ***********)

(* ------------------------------------------------------------------------- *)
(* Checking resultants from Maple.                                           *)
(* ------------------------------------------------------------------------- *)

(*** interface(prettyprint=0);
     resultant(a * x^2 + b * x + c, 2 * a * x + b,x);
 ***)

time complex_qelim
<<forall a b c.
   (exists x. a * x^2 + b * x + c = 0 /\ 2 * a * x + b = 0) \/ (a = 0) <=>
   (4*a^2*c-b^2*a = 0)>>;;

time complex_qelim
<<forall a b c d e.
  (exists x. a * x^2 + b * x + c = 0 /\ d * x + e = 0) \/
   a = 0 /\ d = 0 <=> d^2*c-e*d*b+a*e^2 = 0>>;;

time complex_qelim
<<forall a b c d e f.
   (exists x. a * x^2 + b * x + c = 0 /\ d * x^2 + e * x + f = 0) \/
   (a = 0) /\ (d = 0) <=>
   d^2*c^2-2*d*c*a*f+a^2*f^2-e*d*b*c-e*b*a*f+a*e^2*c+f*d*b^2 = 0>>;;

(**** No hope for this one I think

time complex_qelim
<<forall a b c d e f g.
  (exists x. a * x^3 + b * x^2 + c * x + d = 0 /\ e * x^2 + f * x + g = 0) \/
  (a = 0) /\ (e = 0) <=>
  e^3*d^2+3*e*d*g*a*f-2*e^2*d*g*b-g^2*a*f*b+g^2*e*b^2-f*e^2*c*d+f^2*c*g*a-f*e*c*
  g*b+f^2*e*b*d-f^3*a*d+g*e^2*c^2-2*e*c*a*g^2+a^2*g^3 = 0>>;;

 ****)

(* ------------------------------------------------------------------------- *)
(* Some trigonometric addition formulas (checking stuff from Maple).         *)
(* ------------------------------------------------------------------------- *)

time complex_qelim
  <<forall x y. x^2 + y^2 = 1 ==> (2 * y^2 - 1)^2 + (2 * x * y)^2 = 1>>;;

(* ------------------------------------------------------------------------- *)
(* The examples from my thesis.                                              *)
(* ------------------------------------------------------------------------- *)

time complex_qelim <<forall s c. s^2 + c^2 = 1
      ==> 2 * s - (2 * s * c * c - s^3) = 3 * s^3>>;;

time complex_qelim <<forall u v.
  -((((9 * u^8) * v) * v - (u * u^9)) * 128) -
     (((7 * u^6) * v) * v - (u * u^7)) * 144 -
     (((5 * u^4) * v) * v - (u * u^5)) * 168 -
     (((3 * u^2) * v) * v - (u * u^3)) * 210 -
     (v * v - (u * u)) * 315 + 315 - 1280 * u^10 =
   (-(1152) * u^8 - 1008 * u^6 - 840 * u^4 - 630 * u^2 - 315) *
   (u^2 + v^2 - 1)>>;;

time complex_qelim <<forall u v.
        u^2 + v^2 = 1
        ==> (((9 * u^8) * v) * v - (u * u^9)) * 128 +
            (((7 * u^6) * v) * v - (u * u^7)) * 144 +
            (((5 * u^4) * v) * v - (u * u^5)) * 168 +
            (((3 * u^2) * v) * v - (u * u^3)) * 210 +
            (v * v - (u * u)) * 315 + 1280 * u^10 = 315>>;;

(* ------------------------------------------------------------------------- *)
(* Deliberately silly examples from Poizat's model theory book (6.6).        *)
(* ------------------------------------------------------------------------- *)

time complex_qelim <<exists z. x * z^87 + y * z^44 + 1 = 0>>;;

time complex_qelim <<forall u. exists v. x * (u + v^2)^2 + y * (u + v^2) + z = 0>>;;

(* ------------------------------------------------------------------------- *)
(* Actually prove simple equivalences.                                       *)
(* ------------------------------------------------------------------------- *)

time complex_qelim <<forall x y. (exists z. x * z^87 + y * z^44 + 1 = 0)
                  <=> ~(x = 0) \/ ~(y = 0)>>;;

time complex_qelim <<forall x y z. (forall u. exists v.
                         x * (u + v^2)^2 + y * (u + v^2) + z = 0)
                    <=> ~(x = 0) \/ ~(y = 0) \/ z = 0>>;;

(* ------------------------------------------------------------------------- *)
(* Invertibility of 2x2 matrix in terms of nonzero determinant.              *)
(* ------------------------------------------------------------------------- *)

time complex_qelim <<exists w x y z. (a * w + b * y = 1) /\
                      (a * x + b * z = 0) /\
                      (c * w + d * y = 0) /\
                      (c * x + d * z = 1)>>;;

time complex_qelim <<forall a b c d.
        (exists w x y z. (a * w + b * y = 1) /\
                         (a * x + b * z = 0) /\
                         (c * w + d * y = 0) /\
                         (c * x + d * z = 1))
        <=> ~(a * d = b * c)>>;;

(* ------------------------------------------------------------------------- *)
(* Inspired by Cardano's formula for a cubic. Not all complex cbrts work.    *)
(* ------------------------------------------------------------------------- *)

time complex_qelim
 <<forall m n x u t cu ct.
   t - u = n /\ 27 * t * u = m^3 /\
   ct^3 = t /\ cu^3 = u /\
   x = ct - cu
   ==> x^3 + m * x = n>>;;

time complex_qelim
 <<forall m n x u t.
   t - u = n /\ 27 * t * u = m^3
   ==> exists ct cu. ct^3 = t /\ cu^3 = u /\
                     (x = ct - cu ==> x^3 + m * x = n)>>;;

(* ------------------------------------------------------------------------- *)
(* SOS in rational functions for Motzkin polynomial (dehomogenized).         *)
(* Of course these are just trivial normalization, nothing deep.             *)
(* ------------------------------------------------------------------------- *)

time complex_qelim
 <<forall x y z.
    (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
     x^2 * y^2 * (x^2 + y^2 + 1) * (x^2 + y^2 - 2)^2 + (x^2 - y^2)^2>>;;

time complex_qelim
 <<forall x y z.
    (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
    x^2 * y^2 * x^2  * (x^2 + y^2 - 2)^2 +
    x^2 * y^2 * y^2 * (x^2 + y^2 - 2)^2 +
    x^2 * y^2 * (x^2 + y^2 - 2)^2 +
    (x^2 - y^2)^2>>;;

time complex_qelim
 <<forall x y z.
    (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
    x^4 * y^2 * (x^2 + y^2 - 2)^2 +
    x^2 * y^4 * (x^2 + y^2 - 2)^2 +
    x^2 * y^2 * (x^2 + y^2 - 2)^2 +
    (x^2 - y^2)^2>>;;

time complex_qelim
 <<forall x y z.
    (x^2 + y^2)^2 * (1 + x^4 * y^2 + x^2 * y^4 - 3 * x^2 * y^2) =
    (x^2 * y * (x^2 + y^2 - 2))^2 +
    (x * y^2 * (x^2 + y^2 - 2))^2 +
    (x * y * (x^2 + y^2 - 2))^2 +
    (x^2 - y^2)^2>>;;

(* ------------------------------------------------------------------------- *)
(* A cute bilinear identity -- see ch14 of Rajwade's "Squares" for more.     *)
(* ------------------------------------------------------------------------- *)

polytest
<<|(x_1^2 + x_2^2 + x_3^2 + x_4^2 + x_5^2 + x_6^2 + x_7^2 + x_8^2 + x_9^2) *
   (y_1^2 + y_2^2 + y_3^2 + y_4^2 + y_5^2 + y_6^2 + y_7^2 + y_8^2 +
    y_9^2 + y_10^2 + y_11^2 + y_12^2 + y_13^2 + y_14^2 + y_15^2 + y_16^2) -
   ((0 + x_1 * y_1 + x_2 * y_2 + x_3 * y_3 + x_4 * y_4 + x_5 * y_5 + x_6 * y_6 + x_7 * y_7 + x_8 * y_8 + x_9 * y_9)^2 +
    (0 - x_2 * y_1 + x_1 * y_2 + x_4 * y_3 - x_3 * y_4 + x_6 * y_5 - x_5 * y_6 - x_8 * y_7 + x_7 * y_8 + x_9 * y_10)^2 +
    (0 - x_3 * y_1 - x_4 * y_2 + x_1 * y_3 + x_2 * y_4 + x_7 * y_5 + x_8 * y_6 - x_5 * y_7 - x_6 * y_8 + x_9 * y_11)^2 +
    (0 - x_4 * y_1 + x_3 * y_2 - x_2 * y_3 + x_1 * y_4 + x_8 * y_5 - x_7 * y_6 + x_6 * y_7 - x_5 * y_8 + x_9 * y_12)^2 +
    (0 - x_5 * y_1 - x_6 * y_2 - x_7 * y_3 - x_8 * y_4 + x_1 * y_5 + x_2 * y_6 + x_3 * y_7 + x_4 * y_8 + x_9 * y_13)^2 +
    (0 - x_6 * y_1 + x_5 * y_2 - x_8 * y_3 + x_7 * y_4 - x_2 * y_5 + x_1 * y_6 - x_4 * y_7 + x_3 * y_8 + x_9 * y_14)^2 +
    (0 - x_7 * y_1 + x_8 * y_2 + x_5 * y_3 - x_6 * y_4 - x_3 * y_5 + x_4 * y_6 + x_1 * y_7 - x_2 * y_8 + x_9 * y_15)^2 +
    (0 - x_8 * y_1 - x_7 * y_2 + x_6 * y_3 + x_5 * y_4 - x_4 * y_5 - x_3 * y_6 + x_2 * y_7 + x_1 * y_8 + x_9 * y_16)^2 +
    (0 - x_9 * y_1 + x_1 * y_9 - x_2 * y_10 - x_3 * y_11 - x_4 * y_12 - x_5 * y_13 - x_6 * y_14 - x_7 * y_15 - x_8 * y_16)^2 +
    (0 - x_9 * y_2 + x_2 * y_9 + x_1 * y_10 - x_4 * y_11 + x_3 * y_12 - x_6 * y_13 + x_5 * y_14 + x_8 * y_15 - x_7 * y_16)^2 +
    (0 - x_9 * y_3 + x_3 * y_9 + x_4 * y_10 + x_1 * y_11 - x_2 * y_12 - x_7 * y_13 - x_8 * y_14 + x_5 * y_15 + x_6 * y_16)^2 +
    (0 - x_9 * y_4 + x_4 * y_9 - x_3 * y_10 + x_2 * y_11 + x_1 * y_12 - x_8 * y_13 + x_7 * y_14 - x_6 * y_15 + x_5 * y_16)^2 +
    (0 - x_9 * y_5 + x_5 * y_9 + x_6 * y_10 + x_7 * y_11 + x_8 * y_12 + x_1 * y_13 - x_2 * y_14 - x_3 * y_15 - x_4 * y_16)^2 +
    (0 - x_9 * y_6 + x_6 * y_9 - x_5 * y_10 + x_8 * y_11 - x_7 * y_12 + x_2 * y_13 + x_1 * y_14 + x_4 * y_15 - x_3 * y_16)^2 +
    (0 - x_9 * y_7 + x_7 * y_9 - x_8 * y_10 - x_5 * y_11 + x_6 * y_12 + x_3 * y_13 - x_4 * y_14 + x_1 * y_15 + x_2 * y_16)^2 +
    (0 - x_9 * y_8 + x_8 * y_9 + x_7 * y_10 - x_6 * y_11 - x_5 * y_12 + x_4 * y_13 + x_3 * y_14 - x_2 * y_15 + x_1 * y_16)^2)|>>;;

(* ------------------------------------------------------------------------- *)
(* This is essentially the Cauchy-Riemann conditions for a differential.     *)
(* ------------------------------------------------------------------------- *)

time complex_qelim
  <<forall x y. (a * x + b * y = u * x - v * y) /\
                (c * x + d * y = u * y + v * x)
                ==> (a = d)>>;;

time complex_qelim
  <<forall a b c d.
      (forall x y. (a * x + b * y = u * x - v * y) /\
                   (c * x + d * y = u * y + v * x))
                   ==> (a = d) /\ (b = -(c))>>;;

time complex_qelim
  <<forall a b c d.
        (exists u v. forall x y. (a * x + b * y = u * x - v * y) /\
                                 (c * x + d * y = u * y + v * x))
        <=> (a = d) /\ (b = -(c))>>;;

(* ------------------------------------------------------------------------- *)
(* Finding non-trivial perpendiculars to lines.                              *)
(* ------------------------------------------------------------------------- *)

complex_qelim
  <<forall x1 y1 x2 y2. exists a b.
      ~(a = 0 /\ b = 0) /\ a * x1 + b * y1 = 0 /\ a * x2 + b * y2 = 0>>;;

END_INTERACTIVE;;
