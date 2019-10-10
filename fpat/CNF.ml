open Util
open Combinator
open Formula

type t = Clause.t list

(** {6 Inspectors} *)

let to_clauses = id
let to_conjunction = List.map (Clause.formula_of)
let to_formula = to_conjunction >> Conjunction.formula_of

(** {6 Printers} *)

let pr ppf = to_formula >> Format.fprintf ppf "%a" Formula.pr

(** {6 Auxiliary constructors} *)

let of_formula =
  Formula.fold
    (object
      method fatom atm = fun b ->
        if b then
          [[ atm |> Literal.of_atom ]]
        else
          [[ atm |> Literal.of_atom |> Literal.bnot ]]
      method ftrue () = fun b ->
        if b then
          []
        else
          [[]]
      method ffalse () = fun b ->
        if b then
          [[]]
        else
          []
      method fnot r = fun b ->
        r (not b)
      method fand r1 r2 = fun b ->
        if b then
          r1 b @ r2 b
        else
          Vector.multiply (@) (r1 b) (r2 b)
      method for_ r1 r2 = fun b ->
        if b then
          Vector.multiply (@) (r1 b) (r2 b)
        else
          r1 b @ r2 b
      method fimply r1 r2 = fun b ->
        if b then
          Vector.multiply (@) (r1 (not b)) (r2 b)
        else
          r1 (not b) @ r2 b
      method fiff r1 r2 = fun b ->
        if b then
          Vector.multiply (@) (r1 (not b)) (r2 b)
          @ Vector.multiply (@) (r2 (not b)) (r1 b)
        else
          Vector.multiply (@) (r1 b) (r2 b)
          @ Vector.multiply (@) (r1 (not b)) (r2 (not b))
      method fforall _ _ = fun b ->
        raise (Global.NotImplemented "CNF.of_formula")
      method fexists tenv r = fun b ->
        if b then
          [[Formula.exists [tenv] (r b |> to_formula) |> Literal.of_formula]]
        else
          raise (Global.NotImplemented "CNF.of_formula")
    end)
let of_formula phi = of_formula phi true
let of_formula =
  Logger.log_block1
    "CNF.of_formula"
    ~before:(Logger.printf "input: %a@," Formula.pr)
    ~after:(Logger.printf "output: %a" pr)
    of_formula

let of_formula_loose =
  Formula.para
    (object
      method fatom atm = fun b ->
        if b then
          [[ atm |> Literal.of_atom ]]
        else
          [[ atm |> Literal.of_atom |> Literal.bnot ]]
      method ftrue () = fun b ->
        if b then
          []
        else
          [[]]
      method ffalse () = fun b ->
        if b then
          [[]]
        else
          []
      method fnot phi r = fun b ->
        if b then
          let rs =
            if Formula.fpvs_strict phi = [] then
              [[phi |> Literal.of_formula |> Literal.bnot]]
            else
              r (not b)
          in
          rs
        else
          let rs =
            if Formula.fpvs_strict phi = [] then
              [[phi |> Literal.of_formula]]
            else
              r (not b)
          in
          rs
      method fand phi1 r1 phi2 r2 = fun b ->
        if b then
          let rs1 =
            if Formula.fpvs_strict phi1 = [] then
              [[phi1 |> Literal.of_formula]]
            else
              r1 b
          in
          let rs2 =
            if Formula.fpvs_strict phi2 = [] then
              [[phi2 |> Literal.of_formula]]
            else
              r2 b
          in
          rs1 @ rs2
        else
          let rs1 =
            if Formula.fpvs_strict phi1 = [] then
              [[phi1 |> Literal.of_formula |> Literal.bnot]]
            else
              r1 b
          in
          let rs2 =
            if Formula.fpvs_strict phi2 = [] then
              [[phi2 |> Literal.of_formula |> Literal.bnot]]
            else
              r2 b
          in
          Vector.multiply (@) rs1 rs2
      method for_ phi1 r1 phi2 r2 = fun b ->
        if b then
          let rs1 =
            if Formula.fpvs_strict phi1 = [] then
              [[phi1 |> Literal.of_formula]]
            else
              r1 b
          in
          let rs2 =
            if Formula.fpvs_strict phi2 = [] then
              [[phi2 |> Literal.of_formula]]
            else
              r2 b
          in
          Vector.multiply (@) rs1 rs2
        else
          let rs1 =
            if Formula.fpvs_strict phi1 = [] then
              [[phi1 |> Literal.of_formula |> Literal.bnot]]
            else
              r1 b
          in
          let rs2 =
            if Formula.fpvs_strict phi2 = [] then
              [[phi2 |> Literal.of_formula |> Literal.bnot]]
            else
              r2 b
          in
          rs1 @ rs2
      method fimply phi1 r1 phi2 r2 = fun b ->
        if b then
          let rs1 =
            if Formula.fpvs_strict phi1 = [] then
              [[phi1 |> Literal.of_formula |> Literal.bnot]]
            else
              r1 (not b)
          in
          let rs2 =
            if Formula.fpvs_strict phi2 = [] then
              [[phi2 |> Literal.of_formula]]
            else
              r2 b
          in
          Vector.multiply (@) rs1 rs2
        else
          let rs1 =
            if Formula.fpvs_strict phi1 = [] then
              [[phi1 |> Literal.of_formula]]
            else
              r1 (not b)
          in
          let rs2 =
            if Formula.fpvs_strict phi2 = [] then
              [[phi2 |> Literal.of_formula |> Literal.bnot]]
            else
              r2 b
          in
          rs1 @ rs2
      method fiff phi1 r1 phi2 r2 = fun b ->
        if b then
          let rs11 =
            if Formula.fpvs_strict phi1 = [] then
              [[phi1 |> Literal.of_formula |> Literal.bnot]]
            else
              r1 (not b)
          in
          let rs21 =
            if Formula.fpvs_strict phi2 = [] then
              [[phi2 |> Literal.of_formula]]
            else
              r2 b
          in
          let rs12 =
            if Formula.fpvs_strict phi1 = [] then
              [[phi1 |> Literal.of_formula]]
            else
              r1 b
          in
          let rs22 =
            if Formula.fpvs_strict phi2 = [] then
              [[phi2 |> Literal.of_formula |> Literal.bnot]]
            else
              r2 (not b)
          in
          Vector.multiply (@) rs11 rs21
          @ Vector.multiply (@) rs21 rs22
        else
          let rs11 =
            if Formula.fpvs_strict phi1 = [] then
              [[phi1 |> Literal.of_formula]]
            else
              r1 b
          in
          let rs21 =
            if Formula.fpvs_strict phi2 = [] then
              [[phi2 |> Literal.of_formula]]
            else
              r2 b
          in
          let rs12 =
            if Formula.fpvs_strict phi1 = [] then
              [[phi1 |> Literal.of_formula |> Literal.bnot]]
            else
              r1 (not b)
          in
          let rs22 =
            if Formula.fpvs_strict phi2 = [] then
              [[phi2 |> Literal.of_formula |> Literal.bnot]]
            else
              r2 (not b)
          in
          Vector.multiply (@) rs11 rs21
          @ Vector.multiply (@) rs12 rs22
      method fforall tenv phi r = fun b ->
        if b then
          [[Formula.forall [tenv] phi |> Literal.of_formula]]
        else
          [[Formula.forall [tenv] phi |> Formula.bnot |> Literal.of_formula]]
        (*raise (Global.NotImplemented "CNF.of_formula_loose")*)
      method fexists tenv phi r = fun b ->
        if b then (* for existentially quantified HCCSs *)
          let rs =
            if Formula.fpvs_strict phi = [] then
              [[phi |> Literal.of_formula]]
            else
              r b
          in
          [[Formula.exists [tenv] (rs |> to_formula) |> Literal.of_formula]]
        else
          begin
            if Formula.fpvs_strict phi = [] then
              [[phi |> Literal.of_formula |> Literal.bnot]]
            else
              r b
          end
    end)
let of_formula_loose phi = of_formula_loose phi true

(** {6 Morphisms} *)

let map_clause f = List.map f
let map_literal f = map_clause (List.map f)
