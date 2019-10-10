open Util
open Combinator

(** Linear expressions *)

module Make = functor (Coeff : Coeff.COEFF) -> struct
  (** @invariant all the linear expressions are normalized *)
  type t = (Coeff.t * Idnt.t) list * Coeff.t

  (** {6 Printers} *)

  let pr ppf (nxs, n) =
    let open Coeff in
    begin
      match nxs with
      | [] -> ()
      | (n, x) :: nxs ->
         begin
           if n = make 1 then
             Format.fprintf ppf "%a" Idnt.pr x
           else if n = make (-1) then
             Format.fprintf ppf "-%a" Idnt.pr x
           else if n = make 0 then
             assert false
           else
             Format.fprintf ppf "%a %a" pr n Idnt.pr x
         end;
         List.iter
           (fun (n, x) ->
            if n > make 0 then
              begin
                Format.fprintf ppf " + ";
                (if not (n = make 1) then
                   Format.fprintf ppf "%a " pr n);
                Format.fprintf ppf "%a" Idnt.pr x
              end
            else if make 0 > n then
              begin
                Format.fprintf ppf " - ";
                (if make (-1) * n <> make 1 then
                   Format.fprintf ppf "%a " pr (make (-1) * n));
                Format.fprintf ppf "%a" Idnt.pr x
              end
            else if n = make 0 then
              assert false
            else
              Format.fprintf ppf " + %a %a" pr n Idnt.pr x)
           nxs
    end;
    if n > make 0 then
      begin
        (if nxs <> [] then Format.fprintf ppf " + ");
        Format.fprintf ppf "%a" pr n
      end
    else if make 0 > n then
      begin
        (if nxs <> [] then Format.fprintf ppf " - ");
        Format.fprintf ppf "%a" pr (make (-1) * n)
      end
    else if n = make 0 then
      ()
    else
      begin
        (if nxs <> [] then Format.fprintf ppf " + ");
        Format.fprintf ppf "%a" pr n
      end

  (** {6 Auxiliary constructors} *)

  let of_int n = [], Coeff.make n

  let normalize (nxs, n) =
    let open Coeff in
    List.classify
      (fun (_, x1) (_, x2) -> Idnt.equiv x1 x2)
      nxs
    |> List.map
      (function
        | (n, x) :: nxs ->
          simplify (List.fold_left (+) n (List.map fst nxs)),
          x
        | _ -> assert false)
    |> List.filter (fun (n, _) -> not (n = make 0)),
    simplify n

  let mul_coeff m (nxs, n) =
    let open Coeff in
    normalize (List.map (fun (n, x) -> m * n, x) nxs, m * n)

  let neg (nxs, n) =
    let open Coeff in
    mul_coeff (make (-1)) (nxs, n)

  let add (nxs1, n1) (nxs2, n2) =
    let open Coeff in
    normalize (nxs1 @ nxs2, n1 + n2)

  let mul (nxs1, n1) (nxs2, n2) =
    if nxs1 = [] then
      mul_coeff n1 (nxs2, n2)
    else if nxs2 = [] then
      mul_coeff n2 (nxs1, n1)
    else
      begin
        (*Format.printf
          "%a * %a is non-linear@,"
          pr (nxs1, n1)
          pr (nxs2, n2);*)
        invalid_arg "LinExp.mul"
      end

  let map_coeff f (nxs, n) =
    List.map (fun (n, x) -> f n, x) nxs, f n

  (** {6 Inspectors} *)

  let fvs (nxs, n) = List.map snd nxs

  let is_zero (nxs, n) =
    nxs = []
    && let open Coeff in
       n = make 0

  let coeffs (nxs, n) = n :: List.map fst nxs

  let const (_, n) = n

  let coeff (nxs, _) x =
    List.find_map
      (fun (n, y) -> if Idnt.equiv x y then Some(n) else None)
      nxs

  let coeff_zero = Coeff.zero

  let equiv (nxs1, n1) (nxs2, n2) =
    let open Coeff in
    (*let xs1 = List.sort (List.map snd nxs1) in
    let xs2 = List.sort (List.map snd nxs2) in
    xs1 = xs2 &&*)
    let xs1 = List.map snd nxs1 in
    let xs2 = List.map snd nxs2 in
    Set_.equiv xs1 xs2
    && (List.for_all
          (fun x ->
           coeff (nxs1, n1) x = coeff (nxs2, n2) x)
          xs1)
    && n1 = n2

  let factorize lin =
    let open Coeff in
    lin |> coeffs |> gcd
    |> fun m ->
       if m = make 0 then
         make 1, lin
       else
         try
           m, map_coeff (fun n -> n / m) lin
         with Invalid_argument _ ->
           make 1, lin
end
