open Util
open Combinator
open Term

(** Polynomial expressions *)

module Make = functor (Coeff : Coeff.COEFF) -> struct
  (** @invariant all the polynomial expressions are normalized *)
  module M = MonoExp.Make(Coeff)
  type t = M.t list

  (** {6 Auxiliary constructors} *)

  (* val of_int : int -> t *)
  let of_int n = [M.of_int n]

  (* val zero : t *)
  let zero = []
  (* val one : t *)
  let one = [1, []]

  (** {6 Printers} *)

  (* val pr : Format.formatter -> t -> unit *)
  let pr ppf pol =
    match pol with
    | [] -> Format.fprintf ppf "0"
    | tm :: tms ->
       Format.fprintf ppf "%a" M.pr tm;
       let open Coeff in
       List.iter
         (fun (n, xs) ->
          if n > Coeff.make 0 then
            begin
              Format.fprintf ppf " + ";
              Format.fprintf ppf "%a" M.pr (n, xs)
            end
          else if n < Coeff.make 0 then
            begin
              Format.fprintf ppf " - ";
              Format.fprintf ppf "%a" M.pr (Coeff.make (-1) * n, xs)
            end
          else
            assert false)
         tms
  (*Format.fprintf ppf (List.pr M.pr " + ") pol*)

  (** {6 Inspectors} *)

  (* val is_zero : t -> bool *)
  let is_zero pol = pol = []
  (* val is_one : t -> bool *)
  let is_one pol =
    match pol with
    | [1, []] -> true
    | _ -> false

  (* val coeff : t -> Idnt.t list -> int *)
  let coeff pol xs =
    List.find_map
      (fun (n, ys) -> if xs = ys then Some(n) else None)
      pol

  (* val equiv : t -> t -> bool *)
  let equiv pol1 pol2 =
    let xss1 = List.map snd pol1 in
    let xss2 = List.map snd pol2 in
    Set_.equiv xss1 xss2
    && List.for_all (fun xs -> coeff pol1 xs = coeff pol2 xs) xss1

  (* val (>) : t -> t -> bool *)
  let (>) pol1 pol2 =
    let xss1 = List.map snd pol1 in
    let xss2 = List.map snd pol2 in
    Set_.equiv xss1 xss2
    && List.for_all (fun xs -> coeff pol1 xs > coeff pol2 xs) xss1

  (* val (<) : t -> t -> bool *)
  let (<) pol1 pol2 =
    let xss1 = List.map snd pol1 in
    let xss2 = List.map snd pol2 in
    Set_.equiv xss1 xss2
    && List.for_all (fun xs -> coeff pol1 xs < coeff pol2 xs) xss1

  (** {6 Operators} *)

  (* val normalize : t -> t *)
  let normalize pol =
    let pol = List.map M.normalize pol in
    List.filter
      (fun (n, _) -> not (n = Coeff.make 0))
      (List.map
         (function
           | (n, xs) :: tms ->
              let open Coeff in
              List.fold_left (+) n (List.map fst tms), xs
           | _ -> assert false)
         (List.classify
            (fun (_, xs1) (_, xs2) -> xs1 = xs2)
            pol))

  (* val mul_coeff : int -> t -> t *)
  let mul_coeff m pol =
    normalize (List.map (M.mul_coeff m) pol)

  (* val neg : t -> t *)
  let neg pol =
    mul_coeff (Coeff.make (-1)) pol

  (* val add : t -> t -> t *)
  let add pol1 pol2 =
    normalize (pol1 @ pol2)

  (* val mul : t -> t -> t *)
  let mul pol1 pol2 =
    let open Coeff in
    normalize
      (Vector.multiply
         (fun (n1, xs1) (n2, xs2) -> n1 * n2, xs1 @ xs2)
         pol1
         pol2)

  (* val div : t -> t -> t *)
  let div pol1 pol2 = assert false
  (*Division_by_zero*)

  (** @require not (is_zero pol) *)
  (* val gcd_coeff : t -> int * t *)
  let gcd_coeff pol =
    let n = Integer.gcd_list (List.map fst pol) in
    if n <> 0 then
      n, List.map (fun (m, x) -> m / n, x) pol
    else
      1, pol

  (** @require not (is_zero pol) *)
  (* val gcd_vars : t -> Idnt.t list * t *)
  let gcd_vars pol =
    match List.map snd pol with
    | [] ->
       assert false
    | xs :: xss ->
       let xs =
         List.fold_left Bag.inter xs xss
       in
       xs,
       List.map
         (fun (n, ys) -> n, Bag.diff ys xs)
         pol

  (* val div_gcd : t -> t *)
  let div_gcd pol = pol |> gcd_coeff |> snd
end 
