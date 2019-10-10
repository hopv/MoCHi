(* ========================================================================= *)
(* Grobner basis algorithm.                                                  *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Operations on monomials.                                                  *)
(* ------------------------------------------------------------------------- *)

let mmul (c1,m1) (c2,m2) = (c1*/c2,map2 (+) m1 m2);;

let mdiv =
  let index_sub n1 n2 = if n1 < n2 then failwith "mdiv" else n1-n2 in
  fun (c1,m1) (c2,m2) -> (c1//c2,map2 index_sub m1 m2);;

let mlcm (c1,m1) (c2,m2) = (Int 1,map2 max m1 m2);;

(* ------------------------------------------------------------------------- *)
(* Monomial ordering.                                                        *)
(* ------------------------------------------------------------------------- *)

let morder_lt m1 m2 =
  let n1 = itlist (+) m1 0 and n2 = itlist (+) m2 0 in
  n1 < n2 or n1 = n2 & lexord(>) m1 m2;;

(* ------------------------------------------------------------------------- *)
(* Arithmetic on canonical multivariate polynomials.                         *)
(* ------------------------------------------------------------------------- *)

let mpoly_mmul cm pol = map (mmul cm) pol;;

let mpoly_neg = map (fun (c,m) -> (minus_num c,m));;

let mpoly_const vars c =
  if c =/ Int 0 then [] else [c,map (fun k -> 0) vars];;

let mpoly_var vars x =
  [Int 1,map (fun y -> if y = x then 1 else 0) vars];;

let rec mpoly_add l1 l2 =
  match (l1,l2) with
    ([],l2) -> l2
  | (l1,[]) -> l1
  | ((c1,m1)::o1,(c2,m2)::o2) ->
        if m1 = m2 then
          let c = c1+/c2 and rest = mpoly_add o1 o2 in
          if c =/ Int 0 then rest else (c,m1)::rest
        else if morder_lt m2 m1 then (c1,m1)::(mpoly_add o1 l2)
        else (c2,m2)::(mpoly_add l1 o2);;

let mpoly_sub l1 l2 = mpoly_add l1 (mpoly_neg l2);;

let rec mpoly_mul l1 l2 =
  match l1 with
    [] -> []
  | (h1::t1) -> mpoly_add (mpoly_mmul h1 l2) (mpoly_mul t1 l2);;

let mpoly_pow vars l n =
  funpow n (mpoly_mul l) (mpoly_const vars (Int 1));;

let mpoly_inv p =
  match p with 
    [(c,m)] when forall (fun i -> i = 0) m -> [(Int 1 // c),m]
  | _ -> failwith "mpoly_inv: non-constant polynomial";;

let mpoly_div p q = mpoly_mul p (mpoly_inv q);;

(* ------------------------------------------------------------------------- *)
(* Convert formula into canonical form.                                      *)
(* ------------------------------------------------------------------------- *)

let rec mpolynate vars tm =
  match tm with
    Var x -> mpoly_var vars x
  | Fn("-",[t]) -> mpoly_neg (mpolynate vars t)
  | Fn("+",[s;t]) -> mpoly_add (mpolynate vars s) (mpolynate vars t)
  | Fn("-",[s;t]) -> mpoly_sub (mpolynate vars s) (mpolynate vars t)
  | Fn("*",[s;t]) -> mpoly_mul (mpolynate vars s) (mpolynate vars t)
  | Fn("/",[s;t]) -> mpoly_div (mpolynate vars s) (mpolynate vars t)
  | Fn("^",[t;Fn(n,[])]) ->
                mpoly_pow vars (mpolynate vars t) (int_of_string n)
  | _ -> mpoly_const vars (dest_numeral tm);;

let mpolyatom vars fm =
  match fm with
    Atom(R("=",[s;t])) -> mpolynate vars (Fn("-",[s;t]))
  | _ -> failwith "mpolyatom: not an equation";;

(* ------------------------------------------------------------------------- *)
(* Reduce monomial cm by polynomial pol, returning replacement for cm.       *)
(* ------------------------------------------------------------------------- *)

let reduce1 cm pol =
  match pol with
    [] -> failwith "reduce1"
  | hm::cms -> let c,m = mdiv cm hm in mpoly_mmul (minus_num c,m) cms;;

(* ------------------------------------------------------------------------- *)
(* Try this for all polynomials in a basis.                                  *)
(* ------------------------------------------------------------------------- *)

let reduceb cm pols = tryfind (reduce1 cm) pols;;

(* ------------------------------------------------------------------------- *)
(* Reduction of a polynomial (always picking largest monomial possible).     *)
(* ------------------------------------------------------------------------- *)

let rec reduce pols pol =
  match pol with
    [] -> []
  | cm::ptl -> try reduce pols (mpoly_add (reduceb cm pols) ptl)
               with Failure _ -> cm::(reduce pols ptl);;

(* ------------------------------------------------------------------------- *)
(* Compute S-polynomial of two polynomials.                                  *)
(* ------------------------------------------------------------------------- *)

let spoly pol1 pol2 =
  match (pol1,pol2) with
    ([],p) -> []
  | (p,[]) -> []
  | (m1::ptl1,m2::ptl2) ->
        let m = mlcm m1 m2 in
        mpoly_sub (mpoly_mmul (mdiv m m1) ptl1)
                  (mpoly_mmul (mdiv m m2) ptl2);;

(* ------------------------------------------------------------------------- *)
(* Grobner basis algorithm.                                                  *)
(* ------------------------------------------------------------------------- *)

let rec grobner basis pairs =
  print_string(string_of_int(length basis)^" basis elements and "^
               string_of_int(length pairs)^" pairs");
  print_newline();
  match pairs with
    [] -> basis
  | (p1,p2)::opairs ->
        let sp = reduce basis (spoly p1 p2) in
        if sp = [] then grobner basis opairs
        else if forall (forall ((=) 0) ** snd) sp then [sp] else
        let newcps = map (fun p -> p,sp) basis in
        grobner (sp::basis) (opairs @ newcps);;

(* ------------------------------------------------------------------------- *)
(* Overall function.                                                         *)
(* ------------------------------------------------------------------------- *)

let groebner basis = grobner basis (distinctpairs basis);;

(* ------------------------------------------------------------------------- *)
(* Use the Rabinowitsch trick to eliminate inequations.                      *)
(* That is, replace p =/= 0 by exists v. 1 - v * p = 0                       *)
(* ------------------------------------------------------------------------- *)

let rabinowitsch vars v p =
   mpoly_sub (mpoly_const vars (Int 1))
             (mpoly_mul (mpoly_var vars v) p);;

(* ------------------------------------------------------------------------- *)
(* Universal complex number decision procedure based on Grobner bases.       *)
(* ------------------------------------------------------------------------- *)

let grobner_trivial fms =
  let vars0 = itlist (union ** fv) fms []
  and eqs,neqs = partition positive fms in
  let rvs = map (fun n -> variant ("_"^string_of_int n) vars0)
                (1--length neqs) in
  let vars = vars0 @ rvs in
  let poleqs = map (mpolyatom vars) eqs
  and polneqs = map (mpolyatom vars ** negate) neqs in
  let pols = poleqs @ map2 (rabinowitsch vars) rvs polneqs in
  reduce (groebner pols) (mpoly_const vars (Int 1)) = [];;

let grobner_decide fm =
  let fm1 = specialize(prenex(nnf(simplify fm))) in
  forall grobner_trivial (simpdnf(nnf(Not fm1)));;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
grobner_decide
  <<a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 1 = 0>>;;

grobner_decide
  <<a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 2 = 0>>;;

grobner_decide
  <<(a * x^2 + b * x + c = 0) /\
   (a * y^2 + b * y + c = 0) /\
   ~(x = y)
   ==> (a * x * y = c) /\ (a * (x + y) + b = 0)>>;;

(* ------------------------------------------------------------------------- *)
(* Compare with earlier procedure.                                           *)
(* ------------------------------------------------------------------------- *)

let fm =
  <<(a * x^2 + b * x + c = 0) /\
    (a * y^2 + b * y + c = 0) /\
    ~(x = y)
    ==> (a * x * y = c) /\ (a * (x + y) + b = 0)>> in
time complex_qelim (generalize fm),time grobner_decide fm;;

(* ------------------------------------------------------------------------- *)
(* More tests.                                                               *)
(* ------------------------------------------------------------------------- *)

time grobner_decide  <<a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 1 = 0>>;;

time grobner_decide  <<a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 2 = 0>>;;

time grobner_decide <<(a * x^2 + b * x + c = 0) /\
      (a * y^2 + b * y + c = 0) /\
      ~(x = y)
      ==> (a * x * y = c) /\ (a * (x + y) + b = 0)>>;;

time grobner_decide
 <<(y_1 = 2 * y_3) /\
  (y_2 = 2 * y_4) /\
  (y_1 * y_3 = y_2 * y_4)
  ==> (y_1^2 = y_2^2)>>;;

time grobner_decide
 <<(x1 = u3) /\
  (x1 * (u2 - u1) = x2 * u3) /\
  (x4 * (x2 - u1) = x1 * (x3 - u1)) /\
  (x3 * u3 = x4 * u2) /\
  ~(u1 = 0) /\
  ~(u3 = 0)
  ==> (x3^2 + x4^2 = (u2 - x3)^2 + (u3 - x4)^2)>>;;

time grobner_decide
 <<(u1 * x1 - u1 * u3 = 0) /\
  (u3 * x2 - (u2 - u1) * x1 = 0) /\
  (x1 * x4 - (x2 - u1) * x3 - u1 * x1 = 0) /\
  (u3 * x4 - u2 * x3 = 0) /\
  ~(u1 = 0) /\
  ~(u3 = 0)
  ==> (2 * u2 * x4 + 2 * u3 * x3 - u3^2 - u2^2 = 0)>>;;

(*** Checking resultants (in one direction) ***)

time grobner_decide
<<a * x^2 + b * x + c = 0 /\ 2 * a * x + b = 0
 ==> 4*a^2*c-b^2*a = 0>>;;

time grobner_decide
<<a * x^2 + b * x + c = 0 /\ d * x + e = 0
 ==> d^2*c-e*d*b+a*e^2 = 0>>;;


time grobner_decide
<<a * x^2 + b * x + c = 0 /\ d * x^2 + e * x + f = 0
 ==> d^2*c^2-2*d*c*a*f+a^2*f^2-e*d*b*c-e*b*a*f+a*e^2*c+f*d*b^2 = 0>>;;

(****** Seems a bit too lengthy?

time grobner_decide
<<a * x^3 + b * x^2 + c * x + d = 0 /\ e * x^2 + f * x + g = 0
 ==>
e^3*d^2+3*e*d*g*a*f-2*e^2*d*g*b-g^2*a*f*b+g^2*e*b^2-f*e^2*c*d+f^2*c*g*a-f*e*c*
g*b+f^2*e*b*d-f^3*a*d+g*e^2*c^2-2*e*c*a*g^2+a^2*g^3 = 0>>;;

 ********)

(********** Works correctly, but it's lengthy

time grobner_decide
 << (x1 - x0)^2 + (y1 - y0)^2 =
   (x2 - x0)^2 + (y2 - y0)^2 /\
   (x2 - x0)^2 + (y2 - y0)^2 =
   (x3 - x0)^2 + (y3 - y0)^2 /\
   (x1 - x0')^2 + (y1 - y0')^2 =
   (x2 - x0')^2 + (y2 - y0')^2 /\
   (x2 - x0')^2 + (y2 - y0')^2 =
   (x3 - x0')^2 + (y3 - y0')^2
   ==> x0 = x0' /\ y0 = y0'>>;;

       **** Corrected with non-isotropy conditions; even lengthier

time grobner_decide
 <<(x1 - x0)^2 + (y1 - y0)^2 =
  (x2 - x0)^2 + (y2 - y0)^2 /\
  (x2 - x0)^2 + (y2 - y0)^2 =
  (x3 - x0)^2 + (y3 - y0)^2 /\
  (x1 - x0')^2 + (y1 - y0')^2 =
  (x2 - x0')^2 + (y2 - y0')^2 /\
  (x2 - x0')^2 + (y2 - y0')^2 =
  (x3 - x0')^2 + (y3 - y0')^2 /\
  ~((x1 - x0)^2 + (y1 - y0)^2 = 0) /\
  ~((x1 - x0')^2 + (y1 - y0')^2 = 0)
  ==> x0 = x0' /\ y0 = y0'>>;;

        *** Maybe this is more efficient? (No?)

time grobner_decide
 <<(x1 - x0)^2 + (y1 - y0)^2 = d /\
  (x2 - x0)^2 + (y2 - y0)^2 = d /\
  (x3 - x0)^2 + (y3 - y0)^2 = d /\
  (x1 - x0')^2 + (y1 - y0')^2 = e /\
  (x2 - x0')^2 + (y2 - y0')^2 = e /\
  (x3 - x0')^2 + (y3 - y0')^2 = e /\
  ~(d = 0) /\ ~(e = 0)
  ==> x0 = x0' /\ y0 = y0'>>;;

***********)

(* ------------------------------------------------------------------------- *)
(* Inversion of homographic function (from Gosper's CF notes).               *)
(* ------------------------------------------------------------------------- *)

time grobner_decide
 <<y * (c * x + d) = a * x + b ==> x * (c * y - a) = b - d * y>>;;

(* ------------------------------------------------------------------------- *)
(* Manual "sums of squares" for 0 <= a /\ a <= b ==> a^3 <= b^3.             *)
(* ------------------------------------------------------------------------- *)

time complex_qelim
 <<forall a b c d e.
     a = c^2 /\ b = a + d^2 /\ (b^3 - a^3) * e^2 + 1 = 0
     ==> (a * d * e)^2 + (c^2 * d * e)^2 + (c * d^2 * e)^2 + (b * d * e)^2 + 1 =
        0>>;;

time grobner_decide
  <<a = c^2 /\ b = a + d^2 /\ (b^3 - a^3) * e^2 + 1 = 0
    ==> (a * d * e)^2 + (c^2 * d * e)^2 + (c * d^2 * e)^2 + (b * d * e)^2 + 1 =
        0>>;;

(* ------------------------------------------------------------------------- *)
(* Special case of a = 1, i.e. 1 <= b ==> 1 <= b^3                           *)
(* ------------------------------------------------------------------------- *)

time complex_qelim
 <<forall b d e.
     b = 1 + d^2 /\ (b^3 - 1) * e^2 + 1 = 0
     ==> 2 * (d * e)^2 + (d^2 * e)^2 + (b * d * e)^2 + 1 = 0>>;;

time grobner_decide
  <<b = 1 + d^2 /\ (b^3 - 1) * e^2 + 1 = 0
    ==> 2 * (d * e)^2 + (d^2 * e)^2 + (b * d * e)^2 + 1 =  0>>;;

(* ------------------------------------------------------------------------- *)
(* Converse, 0 <= a /\ a^3 <= b^3 ==> a <= b                                 *)
(*                                                                           *)
(* This derives b <= 0, but not a full solution.                             *)
(* ------------------------------------------------------------------------- *)

time grobner_decide
 <<a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0
   ==> c^2 * b + a^2 + b^2 + (e * d)^2 = 0>>;;

(* ------------------------------------------------------------------------- *)
(* Here are further steps towards a solution, step-by-step.                  *)
(* ------------------------------------------------------------------------- *)

time grobner_decide
 <<a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0
   ==> c^2 * b = -(a^2 + b^2 + (e * d)^2)>>;;

time grobner_decide
 <<a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0
   ==> c^6 * b^3 = -(a^2 + b^2 + (e * d)^2)^3>>;;

time grobner_decide
 <<a = c^2 /\ b^3 = a^3 + d^2 /\ (b - a) * e^2 + 1 = 0
   ==> c^6 * (c^6 + d^2) + (a^2 + b^2 + (e * d)^2)^3 = 0>>;;

(* ------------------------------------------------------------------------- *)
(* A simpler one is ~(x < y /\ y < x), i.e. x < y ==> x <= y.                *)
(*                                                                           *)
(* Yet even this isn't completed!                                            *)
(* ------------------------------------------------------------------------- *)

time grobner_decide
 <<(y - x) * s^2 = 1 /\ (x - y) * t^2 = 1 ==> s^2 + t^2 = 0>>;;

(* ------------------------------------------------------------------------- *)
(* Inspired by Cardano's formula for a cubic. This actually works worse than *)
(* with naive quantifier elimination (of course it's false...)               *)
(* ------------------------------------------------------------------------- *)

(******

time grobner_decide
 <<t - u = n /\ 27 * t * u = m^3 /\
   ct^3 = t /\ cu^3 = u /\
   x = ct - cu
   ==> x^3 + m * x = n>>;;

***********)

END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* For looking at things it's nice to map back to normal term.               *)
(* ------------------------------------------------------------------------- *)

(*****

let term_of_varpow vars (x,k) =
  if k = 1 then Var x else Fn("^",[Var x; mk_numeral(Int k)]);;

let term_of_varpows vars lis =
  let tms = filter (fun (a,b) -> b <> 0) (zip vars lis) in
  end_itlist (fun s t -> Fn("*",[s;t])) (map (term_of_varpow vars) tms);;

let term_of_monomial vars (c,m) =
  if forall (fun x -> x = 0) m then mk_numeral c
  else if c =/ Int 1 then term_of_varpows vars m
  else Fn("*",[mk_numeral c; term_of_varpows vars m]);;

let term_of_poly vars pol =
  end_itlist (fun s t -> Fn("+",[s;t])) (map (term_of_monomial vars) pol);;

let grobner_basis vars pols =
  map (term_of_poly vars) (groebner (map (mpolyatom vars) pols));;

*****)
