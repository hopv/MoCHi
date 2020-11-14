open Util
open Combinator

let (@@@) = List.rev_append

let rec col_app uf t =
  let col_apps acc ts = List.fold_left (fun acc t -> acc @@@ col_app uf t) acc ts in
  match Term.fun_args t with
  | Const(x), ts when x = uf -> col_apps [ts] ts
  | Const _, ts
  | Var _, ts -> col_apps [] ts
  | _ -> invalid_arg ("not supported in SetTheory.col_app: " ^ Printer.string_of Term.pr t)
let col_app uf phi = col_app uf (Formula.term_of phi)

let empty =
  Const.UFun
    (Type.mk_const (TypConst.Ext "set"),
     Idnt.make "empty")
let mem =
  Const.UFun
    (Type.(mk_fun [mk_int; mk_const (TypConst.Ext "set"); mk_bool]),
     Idnt.make "mem")
let add =
  Const.UFun
    (Type.(mk_fun [mk_int; mk_const (TypConst.Ext "set"); mk_const (TypConst.Ext "set")]),
     Idnt.make "add")
let subset =
  Const.UFun
    (Type.(mk_fun [mk_int; mk_const (TypConst.Ext "set"); mk_bool]),
     Idnt.make "subset")

let mk_mem x y = Formula.mk_atom mem [x; y]
let mk_add x y = Term.mk_app (Const add) [x; y]
let mk_subset x y = Formula.mk_atom subset [x; y]

(* forall x. x ∉ ∅ *)
let theory_empty phi =
  col_app mem phi
  |> List.map (function [x;_] -> Formula.bnot (mk_mem x (Const empty)) | _ -> assert false)
  |> Formula.band

(* forall z, X, Y. z ∈ X ∧ X ⊆ Y => z ∈ Y *)
let theory_subset phi =
  let subsets = col_app subset phi in
  let mems = col_app mem phi in
  let aux x y = function
    | [z;_] -> Formula.(imply (band [mk_mem z x; mk_subset x y]) (mk_mem z y))
    | _ -> assert false
  in
  Formula.band @@ List.concat_map (function [x;y] -> List.map (aux x y) mems | _ -> assert false) subsets

(* forall x. x ∈ {x} ∪ X *)
let theory_add phi =
  col_app add phi
  |> List.map (function [x;y] -> mk_mem x (mk_add x y) | _ -> assert false)
  |> Formula.band

(*
let decomp_lin _ = assert false

(* forall a, b. ∅ = {ax+b | x ∈ ∅} *)
(* forall a, b, y, X. {ay+b} ∪ {ax+b | x ∈ X} = {ax+b | x ∈ {y} ∪ X} *)
let theory_linear t =
  let adds = col_app add t in
  let coeffs = List.filter_map (fun (z,x) -> decomp_lin z |> Option.map (fun c -> c, z, x)) adds in
  let t1 = Formula.band @@ List.map (fun ((a,_,b),_,_) -> Term.(empty = linset a b empty)) coeffs in
  let t2 = Formula.band @@ List.map (fun ((a,y,b),z,x) -> Term.(addset z (linset a b x) = linset a b (addset y x))) coeffs in
  Formula.mk_and t1 t2
 *)

let theory phi =
  [theory_empty; theory_subset; theory_add]
  |> List.map (fun f -> f phi)
  |> Formula.band
let add_theory phi = Formula.mk_and (theory phi) phi


let wrap_smt_prover solver =
  object
    method initialize = solver#initialize
    method finalize = solver#finalize
    method is_valid tenv phi = solver#is_valid tenv (Formula.imply (theory phi) phi)
    method is_sat tenv phi = solver#is_sat tenv (add_theory phi)
    method implies tenv phi1 phi2 =
      let phi = theory (Formula.band (phi1@phi2)) in
      solver#implies tenv (phi::phi1) phi2
    method solve tenv phi = solver#solve tenv (add_theory phi)
  end

let wrap_ip ip =
  fun p phi1 phi2 ->
    let phi3 = theory (Formula.mk_and phi1 phi2) in
    let phi1' = Formula.mk_and phi3 phi1 in
    ip p phi1' phi2
