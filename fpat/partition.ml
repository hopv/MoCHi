open Util
open Combinator

(** Set partitions *)

let top s = [s]
let bot s = List.map (fun e -> [e]) s

let meet ps1 ps2 =
  Vector.multiply Set_.inter ps1 ps2
  |> List.unique ~cmp:Set_.equiv
  |> List.filter ((<>) [])

(* this may not return a correct partition
  [join {{1,2},{3,4}} {{2,3},{1,4}}] returns
  [{{1,2,3},{1,2,4},{2,3,4},{1,3,4}}]
 *)
let join ps1 ps2 =
  Vector.multiply Set_.union ps1 ps2
  |> List.unique ~cmp:Set_.equiv
  |> List.filter ((<>) [])


let label_of_ij i j =
  Idnt.make ("x_" ^ string_of_int i ^ "_" ^ string_of_int j)
let ij_of_label label =
  assert (String.starts_with label "x_");
  try
    String.split (String.sub label 2 (String.length label - 2)) "_"
    |> Pair.lift int_of_string
  with ExtString.Invalid_string -> assert false

let find_decomp xss phi =
  if SMTProver.is_sat_dyn phi then
    let obj = Idnt.make "obj" in
    let constr =
      let xs = Formula.fvs phi |> List.unique |> List.map Term.mk_var in
      [phi;
       xs |> List.map (IntFormula.leq IntTerm.zero) |> Formula.band;
       xs |> IntTerm.sum |> IntFormula.eq (Term.mk_var obj)]
      |> Formula.band
    in
    (* @todo use omega or nuZ instead *)
    let s = SMTProver.find_min_sat_dyn constr obj in
    List.mapi (fun i ->
        List.mapi (fun j _ -> List.assocD 0 (label_of_ij i j) s, j)
        >> List.classify (comp2 (=) fst fst)
        >> List.map (List.map snd))
      xss
    |> Option.return
  else None

let refute_constr_of =
  List.mapi
    (fun i ->
       Combination.comb2
       >> (List.map
             (Pair.lift (label_of_ij i >> Term.mk_var)
              >> uncurry2 IntFormula.neq))
       >> Formula.bor)
  >> Formula.bor
