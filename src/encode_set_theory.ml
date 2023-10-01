open Util
open CEGAR_syntax
open CEGAR_util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let rec col_app c t =
  match t with
  | Const _ -> []
  | Var _ -> []
  | App(App(Const c', t1), t2) when c = c' ->
      assert (col_app c t1 = []);
      assert (col_app c t2 = []);
      [t1,t2]
  | App(t1, t2) -> col_app c t1 @@@ col_app c t2
  | _ -> Format.fprintf !Flag.Print.target "%a@." CEGAR_print.term t; assert false

(* forall x. x ∉ ∅ *)
let theory_empty t =
  let t' =
    col_app MemSet t
    |> List.map (fun (x,_) -> Term.(not (mem x empty)))
    |> make_ands
  in
  Term.(t' && t)

(* forall z, X, Y. z ∈ X ∧ X ⊆ Y => z ∈ Y *)
let theory_subset t =
  let subsets = col_app Subset t in
  let mems = col_app MemSet t in
  let t' =
    let aux x y (z,_) = Term.((mem z x && subset x y) => mem z y) in
    make_ands @@ List.flatten_map (fun (x,y) -> List.map (aux x y) mems) subsets
  in
  Term.(t' && t)

(* forall x. x ∈ {x} ∪ X *)
let theory_add t =
  let t' =
    col_app AddSet t
    |> List.map (fun (x,y) -> Term.(mem x (addset x y)))
    |> make_ands
  in
  Term.(t' && t)

let decomp_lin _ = assert false

(* forall a, b. ∅ = {ax+b | x ∈ ∅} *)
(* forall a, b, y, X. {ay+b} ∪ {ax+b | x ∈ X} = {ax+b | x ∈ {y} ∪ X} *)
let theory_linear t =
  let adds = col_app AddSet t in
  let coeffs = List.filter_map (fun (z,x) -> decomp_lin z |> Option.map (fun c -> c, z, x)) adds in
  let t1 = make_ands @@ List.map (fun ((a,_,b),_,_) -> Term.(empty = linset a b empty)) coeffs in
  let t2 = make_ands @@ List.map (fun ((a,y,b),z,x) -> Term.(addset z (linset a b x) = linset a b (addset y x))) coeffs in
  Term.(t1 && t2 && t)

let add t =
  t
  |> theory_empty
  |> theory_subset
  |> theory_add
  |*> theory_linear
