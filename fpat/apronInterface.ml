open Util
open Combinator

(** Interface to APRON *)

(* disequality is supported by expressions
   but x>y || x<y is not allowed

   disequality is not supported by abstract domains

   how widening handles neq?
   it must be handled disjunctively

   why true is returned as the convex hull of x = -1 || x=0 /\ y=0?
   why not -1 <= x <= 0? *)
       
(*let manpk = Ppl.manager_alloc_strict ()*)
let manpk = Polka.manager_alloc_strict ()
(*let maneq = Polka.manager_alloc_equalities ()*)

let mk_expr env (nxs, n) =
  let expr = Apron.Linexpr1.make env in
  Apron.Linexpr1.set_array
    expr
    (Array.of_list
       (List.map
          (fun (n, x) ->
           Apron.Coeff.s_of_int n,
           Apron.Var.of_string (Idnt.serialize x))
          nxs))
    (Some (Apron.Coeff.s_of_int n));
  expr

let linconstr_of env phi =
  let c, (nxs, n) =
    try
      LinIntRel.of_formula phi
    with
    | Invalid_argument(_) ->
      match phi |> Formula.term_of |> Term.fun_args with
      | Term.Const(Const.True), [] ->
        Const.Eq(Type.mk_int), ([], 0)
      | Term.Const(Const.False), [] ->
        Const.Eq(Type.mk_int), ([], 1)
      | _ ->
        Format.printf
          "Boolean and unit variables are not supported: %a@,"
          Formula.pr phi;
        assert false
  in
  let expr = mk_expr env (nxs, n) in
  let mexpr = mk_expr env (LinIntExp.neg (nxs, n)) in
  match c with
  | Const.Lt(ty) ->
     Apron.Lincons1.make mexpr Apron.Lincons1.SUP
  | Const.Gt(ty) ->
     Apron.Lincons1.make expr Apron.Lincons1.SUP
  | Const.Leq(ty) ->
     Apron.Lincons1.make mexpr Apron.Lincons1.SUPEQ
  | Const.Geq(ty) ->
     Apron.Lincons1.make expr Apron.Lincons1.SUPEQ
  | Const.Eq(ty) ->
     Apron.Lincons1.make expr Apron.Lincons1.EQ
  | Const.Neq(ty) ->
     Apron.Lincons1.make expr Apron.Lincons1.DISEQ
  | _ -> assert false

let int_of_coeff n =
  if Apron.Coeff.is_scalar n then
    match n with
    | Apron.Coeff.Scalar(s) ->
       let str = Apron.Scalar.to_string s in
        (*Format.printf "%s@," str;*)
        (int_of_float (float_of_string str))
    | _ -> assert false
  else
    assert false

let of_linconstr c =
  let nxs = ref [] in
  Apron.Lincons1.iter
    (fun n x ->
     nxs := (int_of_coeff n, Idnt.deserialize (Apron.Var.to_string x))
            :: !nxs)
    c;
  !nxs
  |> List.fold_left
       (fun t (n, x) ->
        if n = 0 then
          t
        else
          let t' =
            if n = 1 then
              Term.mk_var x
            else
              IntTerm.mul (IntTerm.make n) (Term.mk_var x)
          in
          match t with
          | Term.Const(Const.Int(m)) when m = 0 -> t'
          | _ -> IntTerm.add t t')
       (IntTerm.make (int_of_coeff (Apron.Lincons1.get_cst c)))
  |> match Apron.Lincons1.get_typ c with
     | Apron.Lincons1.SUP ->
        flip IntFormula.gt IntTerm.zero
     | Apron.Lincons1.SUPEQ ->
        flip IntFormula.geq IntTerm.zero
     | Apron.Lincons1.EQ ->
        flip IntFormula.eq IntTerm.zero
     | Apron.Lincons1.DISEQ ->
        flip IntFormula.neq IntTerm.zero
     | _ -> assert false

let of_linconstrs cs =
  List.init
    (Apron.Lincons1.array_length cs)
    (Apron.Lincons1.array_get cs
     >> of_linconstr)
  |> Formula.band

let polyhedron_of env phi =
  phi
  |> DNF.of_formula
  |> DNF.map_literal CunLiteral.simplify
  |> DNF.cubes_of
  |> List.map Cube.conjunction_of
  |> if_ ((=) []) (const [[Formula.mk_false]]) id
  |> List.map
    (fun phis ->
       let phis =
         phis
         |> if_ ((=) []) (const [Formula.mk_true]) id
       in
       let tab =
         phis
         |> List.length
         |> Apron.Lincons1.array_make env
       in
       phis
       |> List.iteri
         (fun i phi ->
            phi
            |> linconstr_of env
            |> Logger.pprintf "linconstr: %a@ " Apron.Lincons1.print
            |> Apron.Lincons1.array_set tab i);
       Apron.Abstract1.of_lincons_array manpk env tab)
  |> Logger.pprintf "APRON input: %a@ " (List.pr Apron.Abstract1.print ",@ ")
  |> Array.of_list
  |> Apron.Abstract1.join_array manpk
  |> Logger.pprintf "APRON output: %a@ " Apron.Abstract1.print
let polyhedron_of =
  Logger.log_block2
    "ApronInterface.polyhedron_of"
    polyhedron_of

let widen2 t1 t2 = Apron.Abstract1.widening manpk t1 t2


let convex_hull phi =
  let env =
    phi
    |> Formula.fvs
    |> List.unique
    |> List.map (Idnt.serialize >> Apron.Var.of_string)
    |> Array.of_list
    |> flip Apron.Environment.make [||]
  in
  phi
  |> CunFormula.elim_unit
  |> List.return
  |> CunFormula.case_analysis_boolean
       FormulaSimplifier.simplify
       (List.elem_of_singleton
        >> polyhedron_of env
        >> Apron.Abstract1.to_lincons_array manpk
        >> of_linconstrs)
let convex_hull =
  Logger.log_block1
    "ApronInterface.convex_hull"
    convex_hull

let widen phis =
  let env =
    phis
    |> List.concat_map Formula.fvs
    |> List.unique
    |> List.map (Idnt.serialize >> Apron.Var.of_string)
    |> Array.of_list
    |> flip Apron.Environment.make [||]
  in
  phis
  |> List.map CunFormula.elim_unit
  |> CunFormula.case_analysis_boolean
    FormulaSimplifier.simplify
    (List.map (polyhedron_of env)
     >> List.non_nil_list_of
     >> Logger.pprintf
       "poly: %a@,"
       (List.pr Apron.Abstract1.print ",@ ")
     >> uncurry_list1 (List.fold_left widen2)
     >> Logger.pprintf
       "widen_in: %a@ "
       Apron.Abstract1.print
     >> Apron.Abstract1.to_lincons_array manpk
     >> of_linconstrs
     >> Logger.pprintf "widen_out: %a" Formula.pr)
let widen =
  Logger.log_block1
    "ApronInterface.widen"
    ~before:(Logger.printf "input: %a@," (List.pr Formula.pr ",@ "))
    ~after:(Logger.printf "output: %a" Formula.pr)
    widen


let _ =
  Polyhedron.ext_convex_hull := convex_hull;
  Polyhedron.ext_widen_list := widen

