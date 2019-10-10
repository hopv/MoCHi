open Util
open Combinator
open Term

(** Linear expressions with integer term coefficients *)

module Coeff = struct
  type t = Term.t
  let make = IntTerm.make
  let to_int _ = assert false
  let pr = Term.pr
  let zero = IntTerm.zero
  let one = IntTerm.one
  let (=) = IntTerm.equiv
  let (>) = IntTerm.(>)
  let (+) = IntTerm.add
  let ( * ) = IntTerm.mul
  let (/) = IntTerm.div
  let simplify = CunTerm.poly_simplify
  let gcd _ = IntTerm.one
end
include LinExp.Make(Coeff)

let of_term =
  CunTerm.fold
    (object
      method fvar x ts =
        if ts <> [] then invalid_arg "LinTermIntExp.of_term"
        else if Idnt.is_coeff x then [], Term.mk_var x
        else [Coeff.make 1, x], Coeff.make 0
      method funit () = invalid_arg "LinTermIntExp.of_term"
      method ftrue () = invalid_arg "LinTermIntExp.of_term"
      method ffalse () = invalid_arg "LinTermIntExp.of_term"
      method fint n = [], Coeff.make n
      method fbigint n =
        try [], Coeff.make (Big_int_Z.int_of_big_int n)
        with Failure("int_of_big_int") -> invalid_arg "LinTermIntExp.of_term"
      method frational _ _ = invalid_arg "LinTermIntExp.of_term"
      method freal _ = invalid_arg "LinTermIntExp.of_term"
      method fstring _ = invalid_arg "LinTermIntExp.of_term"
      method fneg ty r =
        if Type.is_int_unknown ty then neg r
        else invalid_arg "LinTermIntExp.of_term"
      method fadd ty r1 r2 =
        if Type.is_int_unknown ty then add r1 r2
        else invalid_arg "LinTermIntExp.of_term"
      method fsub ty r1 r2 =
        if Type.is_int_unknown ty then add r1 (neg r2)
        else invalid_arg "LinTermIntExp.of_term"
      method fmul ty r1 r2 =
        if Type.is_int_unknown ty then mul r1 r2
        else invalid_arg "LinTermIntExp.of_term"
      method fdiv ty r1 r2 = invalid_arg "LinTermIntExp.of_term"
      method fmax ty r1 r2 = invalid_arg "LinTermIntExp.of_term"
      method fmin ty r1 r2 = invalid_arg "LinTermIntExp.of_term"
      method fmod r1 r2 = invalid_arg "LinTermIntExp.of_term"
      method ftuple _ _ = invalid_arg "LinTermIntExp.of_term"
      method fproj _ _ _ = invalid_arg "LinTermIntExp.of_term"
      method fkon _ _ _ = invalid_arg "LinTermIntExp.of_term"
      method faccessor _ _ _ _ = invalid_arg "LinTermIntExp.of_term"
      method fufun _ _ _ = invalid_arg "LinTermIntExp.of_term"
      method fsempty ty = invalid_arg "LinTermIntExp.of_term"
      method fsadd ty r1 r2 = invalid_arg "LinTermIntExp.of_term"
      method fsunion ty r1 r2 = invalid_arg "LinTermIntExp.of_term"
      method fsintersect ty r1 r2 = invalid_arg "LinTermIntExp.of_term"
      method fsdiff ty r1 r2 = invalid_arg "LinTermIntExp.of_term"
      method fscomplement ty r = invalid_arg "LinTermIntExp.of_term"
      method farray n rs = invalid_arg "LinTermIntExp.of_term"
      method faget a n = invalid_arg "LinTermIntExp.of_term"
      method faset a n m e = invalid_arg "LinTermIntExp.of_term"
      method fcoerce ty t = invalid_arg "LinTermIntExp.of_term"
      method fformula _ = invalid_arg "LinTermIntExp.of_term"
    end)

let term_of (nxs, n) =
  (if IntTerm.equiv n (Coeff.make 0) then [] else [n])
  @ List.map
    (fun (n, x) ->
       if IntTerm.equiv n (Coeff.make 0) then assert false
       else if IntTerm.equiv n (Coeff.make 1) then Term.mk_var x
       else Coeff.( * ) n (Term.mk_var x))
    nxs
  |> IntTerm.sum

(** @require not (is_zero (nxs, n))
    @ensure the result does not contain IntTerm.one *)
let factorize2 (nxs, n) =
  try
    let cpolxs =
      nxs
      |> List.map (fun (n, x) -> n, Some(x))
      |> List.cons (n, None)
      |> List.map
        (fun (n, xopt) ->
           n |> CunTerm.to_poly_int_exp |> PolyIntExp.gcd_coeff,
           xopt)
    in
    let pol = snd (fst (List.hd cpolxs)) in
    let cxs =
      List.map
        (fun ((c, pol'), xopt) ->
           if PolyIntExp.equiv pol pol' then c, xopt
           else if PolyIntExp.equiv pol (PolyIntExp.neg pol') then -c, xopt
           else raise Not_found (*give up*))
        cpolxs
    in
    let d = Integer.gcd_list (List.map fst cxs) in
    let d = if d = 0 then 1 else d in
    let nxs, ns =
      cxs
      |> List.map (fun (c, xopt) -> c / d, xopt)
      |> List.partition_map
        (function (c, None) -> `R(c) | (c, Some(x)) -> `L(c, x))
    in
    let t = IntTerm.of_lin_exp (nxs, List.fold_left (+) 0 ns) in
    (if d = 1 then [] else [Coeff.make d])
    @ IntTerm.factorize pol
    @ if IntTerm.equiv t (Coeff.make 1) then [] else [t]
  with Not_found ->
    (nxs, n)
    |> term_of
    |> CunTerm.to_poly_int_exp
    |> IntTerm.factorize


(*val simplify_full : t -> t*)
let simplify_full t =
  try IntTerm.of_lin_exp (CunTerm.to_lin_int_exp t)
  with
  | Invalid_argument _ ->
    try term_of (of_term t) with Invalid_argument _ ->
      IntTerm.of_poly_exp (CunTerm.to_poly_int_exp t)
