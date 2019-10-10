open Util
open Mochi_util
open CEGAR_syntax
open CEGAR_type
open CEGAR_print
open CEGAR_util
open Fpat.Combinator

module F = Fpat
module CS = CEGAR_syntax
module CU = CEGAR_util
module S = Syntax

module String = F.Util.String
module List = F.Util.List
module Array = F.Util.Array

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let rec conv_typ ty =
  match ty with
  | TBase(TUnit, _) -> F.Type.mk_unit
  | TBase(TInt, _) -> F.Type.mk_int
  | TBase(TBool, _) -> F.Type.mk_bool
  | TBase(TAbst "string", _) -> F.Type.mk_string
  | TBase(TAbst "float", _) -> F.Type.mk_real
  | TBase(TAbst s, _) ->
     F.Type.mk_const (F.TypConst.Ext s)
  | TFun(ty1,tmp) ->
     let ty2 = tmp (Const True) in
     F.Type.mk_fun [conv_typ ty1; conv_typ ty2]
  | TApp(TConstr (TFixPred _), ty) -> conv_typ ty
  | _ ->
     Format.eprintf "%a@." CEGAR_print.typ ty;
     assert false

let conv_const c =
  match c with
  | Bottom -> F.Const.Bot
  | Unit -> F.Const.Unit
  | True -> F.Const.True
  | False -> F.Const.False
  | And -> F.Const.And
  | Or -> F.Const.Or
  | Not -> F.Const.Not
  | Lt -> F.Const.Lt F.Type.mk_int
  | Gt -> F.Const.Gt F.Type.mk_int
  | Leq -> F.Const.Leq F.Type.mk_int
  | Geq -> F.Const.Geq F.Type.mk_int
  | EqUnit -> F.Const.Eq F.Type.mk_unit
  | EqBool -> F.Const.Eq F.Type.mk_bool
  | EqInt -> F.Const.Eq F.Type.mk_int
  | CmpPoly(typ,"=") ->
     F.Const.Eq (F.Type.mk_const (F.TypConst.Ext typ))
  | CmpPoly(typ,"<>") ->
     F.Const.Neq (F.Type.mk_const (F.TypConst.Ext typ))
  | CmpPoly(typ,"<") ->
     F.Const.Lt (F.Type.mk_const (F.TypConst.Ext typ))
  | CmpPoly(typ,">") ->
     F.Const.Gt (F.Type.mk_const (F.TypConst.Ext typ))
  | CmpPoly(typ,"<=") ->
     F.Const.Leq (F.Type.mk_const (F.TypConst.Ext typ))
  | CmpPoly(typ,">=") ->
     F.Const.Geq (F.Type.mk_const (F.TypConst.Ext typ))
  | Int(n) -> F.Const.Int(n)
  | Rand(TInt, _) -> F.Const.RandInt
  | Rand(typ, _) -> unsupported @@ Format.asprintf "Rand[%a]" CEGAR_print.typ_base typ
  | Add -> F.Const.Add F.Type.mk_int
  | Sub -> F.Const.Sub F.Type.mk_int
  | Mul -> F.Const.Mul F.Type.mk_int
  | Div -> F.Const.Div F.Type.mk_int
  | Mod -> F.Const.Mod
  | Char c -> F.Const.Int (int_of_char c)
  | String s -> F.Const.String s
  | Float r -> F.Const.Real r
  | Int32 n -> F.Const.Int (Int32.to_int n)
  | Int64 n -> F.Const.Int (Int64.to_int n)
  | Nativeint n -> F.Const.Int (Nativeint.to_int n)
  | CPS_result ->
     F.Const.UFun
       (F.Type.mk_const (F.TypConst.Ext "X"),
        F.Idnt.make "end")
  | Proj(n,i) -> assert false
  | Tuple n -> assert false
  | CmpPoly (_, _) -> assert false
  | Temp s -> assert false
  | If  -> assert false
  | Label _ -> assert false
  | TreeConstr (_, _) -> assert false

let conv_var x =
  if F.RefTypInfer.is_parameter x || is_extra_coeff_name x then
    F.Idnt.mk_coeff x
  else
    F.Idnt.make x

let rec conv_term env t =
  match t with
  | App(App(App(Const(If), t1), Const(True)), Const(False)) ->
     conv_term env t1
  | Const(Rand(TInt, Some n)) ->
      let typs,_ = decomp_rand_typ @@ assoc_renv n env in
      let typs' = List.map conv_typ typs in
      F.Term.mk_const @@ F.Const.ReadInt (F.Idnt.make @@ make_randint_name n, typs')
  | Const(Rand(_, Some _)) -> assert false
  | Const(c) ->
     F.Term.mk_const (conv_const c)
  | Var(x) ->
      F.Term.mk_var @@ conv_var x
  | App(t1, t2) -> F.Term.mk_app (conv_term env t1) [conv_term env t2]
  | Fun _ -> assert false
  | Let _ -> assert false

let conv_formula = conv_term [] |- F.Formula.of_term

let rec of_typ typ =
  match Type.elim_tattr typ with
  | Type.TBase Type.TUnit -> F.Type.mk_unit
  | Type.TBase Type.TInt -> F.Type.mk_int
  | Type.TBase Type.TBool -> F.Type.mk_bool
  | Type.TFun(x,typ) -> F.Type.mk_fun [of_typ @@ Id.typ x; of_typ typ]
  | Type.TData "string" -> F.Type.mk_string
  | Type.TTuple xs -> assert false
  | _ ->
      Format.eprintf "FpatInterface of_typ: %a@." Print.typ typ;
      assert false

let rec of_term t =
  match S.desc t with
  | S.Const S.Unit -> F.Term.mk_const @@ F.Const.Unit
  | S.Const S.True -> F.Term.mk_const @@ F.Const.True
  | S.Const S.False -> F.Term.mk_const @@ F.Const.False
  | S.Const (S.Int n) -> F.Term.mk_const @@ F.Const.Int n
  | S.Const (S.String s) -> F.Term.mk_const @@ F.Const.String s
  | S.Var x -> F.Term.mk_var @@ F.Idnt.make @@ Id.to_string ~plain:false x
  | S.Not t1 -> F.Term.mk_app (F.Term.mk_const F.Const.Not) [of_term t1]
  | S.BinOp(op, t1, t2) ->
      let op' =
        match op with
        | S.Eq ->
            begin
              match Type.elim_tattr @@ S.typ t1 with
              | Type.TBase Type.TUnit -> F.Const.Eq F.Type.mk_unit
              | Type.TBase Type.TInt -> F.Const.Eq F.Type.mk_int
              | Type.TBase Type.TBool -> F.Const.Eq F.Type.mk_bool
              | typ when typ = Type.typ_unknown -> F.Const.Eq F.Type.mk_int
              | typ ->
                  Format.eprintf "t1.S.typ: %a@." Print.typ typ;
                  unsupported "FpatInterface.of_term"
            end
        | S.Lt -> F.Const.Lt F.Type.mk_int
        | S.Gt -> F.Const.Gt F.Type.mk_int
        | S.Leq -> F.Const.Leq F.Type.mk_int
        | S.Geq -> F.Const.Geq F.Type.mk_int
        | S.And -> F.Const.And
        | S.Or -> F.Const.Or
        | S.Add -> F.Const.Add F.Type.mk_int
        | S.Sub -> F.Const.Sub F.Type.mk_int
        | S.Mult -> F.Const.Mul F.Type.mk_int
        | S.Div -> F.Const.Div F.Type.mk_int
      in
      F.Term.mk_app (F.Term.mk_const op') [of_term t1; of_term t2]
  | S.App({S.desc=S.Var p}, ts) when S.PredVar.is_pvar p  -> (* for predicate variables *)
      let ts' =
        ts
        |> List.map @@ Pair.add_right @@ of_typ -| S.typ
        |> List.map @@ Pair.map_fst of_term
      in
      F.Pva.make (F.Idnt.make @@ Id.to_string ~plain:false p) ts'
      |> F.Pva.to_formula
      |> F.Formula.term_of
  | desc ->
      Format.eprintf "desc: %a@." Print.desc desc;
      unsupported "FpatInterface.of_term"

let inv_const c =
  match c with
  | F.Const.Unit -> Unit
  | F.Const.True -> True
  | F.Const.False -> False
  | F.Const.And -> And
  | F.Const.Or -> Or
  | F.Const.Not -> Not
  | F.Const.Lt ty when F.Type.is_int ty -> Lt
  | F.Const.Gt ty when F.Type.is_int ty -> Gt
  | F.Const.Leq ty when F.Type.is_int ty -> Leq
  | F.Const.Geq ty when F.Type.is_int ty -> Geq
  | F.Const.Eq ty when F.Type.is_unit ty -> EqUnit
  | F.Const.Eq ty when F.Type.is_bool ty -> EqBool
  | F.Const.Eq ty when F.Type.is_int ty -> EqInt
  | F.Const.Int(n) -> Int(n)
  | F.Const.RandInt -> Rand(TInt, None)
  | F.Const.Add ty when F.Type.is_int ty -> Add
  | F.Const.Sub ty when F.Type.is_int ty -> Sub
  | F.Const.Mul ty when F.Type.is_int ty -> Mul
  | F.Const.Div ty when F.Type.is_int ty -> Div
  | F.Const.Eq ty when F.Type.is_ext ty ->
     F.Type.let_ext ty (fun typ -> CmpPoly(typ,"="))
  | F.Const.Neq ty when F.Type.is_ext ty ->
     F.Type.let_ext ty (fun typ -> CmpPoly(typ,"<>"))
  | F.Const.Lt ty when F.Type.is_ext ty ->
     F.Type.let_ext ty (fun typ -> CmpPoly(typ,"<"))
  | F.Const.Gt ty when F.Type.is_ext ty ->
     F.Type.let_ext ty (fun typ -> CmpPoly(typ,">"))
  | F.Const.Leq ty when F.Type.is_ext ty ->
     F.Type.let_ext ty (fun typ -> CmpPoly(typ,"<="))
  | F.Const.Geq ty when F.Type.is_ext ty ->
     F.Type.let_ext ty (fun typ -> CmpPoly(typ,">="))
  | F.Const.String s -> String s
  | F.Const.Real r -> Float r
  | F.Const.UFun(ty, x)
       when F.Idnt.string_of x = "end"
            && F.Type.is_ext ty && F.Type.let_ext ty ((=) "X") ->
     CPS_result
  | F.Const.Iff -> EqBool
  | F.Const.Mod -> Mod
  | _ -> Format.eprintf "%s@." (F.Const.string_of c); assert false

let rec inv_term t =
  match t with
  | F.Term.Const(c) -> Const(inv_const c)
  | F.Term.Var(x) -> Var(F.Idnt.string_of x)
  | F.Term.App(F.Term.App(t1, t2), t3) ->
     (match t1 with
      | F.Term.Const(F.Const.Neq (ty)) when F.Type.is_unit ty ->
         App(Const(Not), App(App(Const(EqUnit), inv_term t2), inv_term t3))
      | F.Term.Const(F.Const.Neq (ty)) when F.Type.is_bool ty ->
         App(Const(Not), App(App(Const(EqBool), inv_term t2), inv_term t3))
      | F.Term.Const(F.Const.Neq (ty)) when F.Type.is_int ty ->
         App(Const(Not), App(App(Const(EqInt), inv_term t2), inv_term t3))
      | _ ->
         App(App(inv_term t1, inv_term t2), inv_term t3))
  | F.Term.App(t1, t2) -> App(inv_term t1, inv_term t2)
  | F.Term.Binder(_, _, _) -> assert false

let inv_formula t = t |> F.Formula.term_of |> inv_term


let conv_event e = (***)
  match e with
  | Event(x) ->
    if x <> "fail" && Flag.Method.(!mode <> FairNonTermination) then
      warning "fpat does not support general events.";
    F.Term.mk_const (F.Const.Event(x))
  | Branch(_) -> assert false

let conv_fdef typs (f, args, guard, events, body) =
  { F.Fdef.name = f;
    F.Fdef.args = List.map (F.Idnt.make >> F.Pattern.mk_var) args;
    F.Fdef.guard = conv_formula guard;
    F.Fdef.body =
      List.fold_right
        (fun e t ->
          let t' =
            if e <> Event "fail" && Flag.Method.(List.mem !mode  [FairTermination; FairNonTermination]) then
              t
            else
              F.Term.mk_const F.Const.Unit in
          F.Term.mk_app
            (conv_event e)
            [t'])
        events (conv_term typs body) } (***)

let inv_fdef fdef =
  fdef.F.Fdef.name,
  fdef.F.Fdef.args,
  inv_formula fdef.F.Fdef.guard,
  [],
  inv_term fdef.F.Fdef.body

let conv_prog prog =
  let typs = prog.CEGAR_syntax.env in
  let fdefs = prog.CEGAR_syntax.defs in
  let main = prog.CEGAR_syntax.main in
  { F.Prog.fdefs =
      List.map (conv_fdef typs) fdefs;
    F.Prog.types =
      List.map (fun (x, ty) -> F.Idnt.make x, conv_typ ty) typs;
    F.Prog.main = main }

let rec inv_abst_type aty =
  match aty with
  | F.AbsType.Base(F.TypConst.Ext("X"), x, ts) ->
      TBase(TAbst("X"), fun s -> [])
  | F.AbsType.Base(b, x, ts) ->
      let x = F.Idnt.string_of x in
      let base =
        let open F.TypConst in
        match b with
        | Ext id -> TAbst id
        | Unit -> TUnit
        | Bool -> TBool
        | Int -> TInt
        | Real -> TAbst "float"
        | String -> TAbst "string"
        | _ ->
            Format.eprintf "%a@." F.AbsType.pr aty;
            assert false
      in
      TBase(base, fun s -> List.map (subst x s -| inv_formula) ts)
  | F.AbsType.Fun(aty1, aty2) ->
      let x =
        if F.AbsType.is_base aty1 then
          F.Idnt.string_of (F.AbsType.bv_of aty1)
        else
          "_dummy"
      in
      TFun(inv_abst_type aty1, subst_typ x -$- (inv_abst_type aty2))


let is_cp prog =
  prog
  |> conv_prog
  |> F.RefTypInfer.is_cut_point

let make_def_randint prog f =
  if CEGAR_syntax.is_randint_var f then
    []
  else
    let argss = List.filter_map (fun (g, args, _, _, _) -> if f = g then Some args else None) prog.defs in
    let n = List.length argss in
    List.make (3 - n) (f, List.hd argss, Const True, [Event "fail"], Const Unit)

let trans fair_cond cexs prog =
  let fs = List.map fst prog.env in
  let defs =
    if fair_cond then (* TODO: ad-hoc fix, remove after Fpat is fixed *)
      prog.defs @ List.concat_map (make_def_randint prog) fs
    else
      prog.defs
  in
  let prog = conv_prog {prog with defs} in
  let cexs =
    if fair_cond then (* TODO: ad-hoc fix, remove after Fpat is fixed *)
      List.map (Util.List.snoc -$- 2) cexs
    else
      cexs
  in
  cexs, prog

let infer solver labeled is_cp cexs ext_cexs prog =
  let fair_cond = Flag.Method.(!mode = FairNonTermination || !verify_ref_typ) in
  let cexs,prog = trans fair_cond cexs prog in
  let env = F.AbsTypInfer.refine ~solver prog labeled is_cp cexs false ext_cexs in
  Flag.Log.Time.parameter_inference := !Flag.Log.Time.parameter_inference +. !F.EAHCCSSolver.elapsed_time;
  List.map (Pair.map F.Idnt.base inv_abst_type) env

(* TODO: merge with infer *)
let infer_with_ext
    (labeled: string list)
    (is_cp: F.Idnt.t -> bool)
    (cexs: int list list)
    (ext_cexs: ((F.Idnt.t * F.Pred.t list) list) list)
    (prog: CEGAR_syntax.prog)
  =
  Verbose.printf "labeled %a@." (Util.List.print Format.pp_print_string) labeled;
  Verbose.printf "cexs %a@." (Util.List.print @@ Util.List.print Format.pp_print_int) cexs;
  let pr ppf (tenv, phi) =
    Verbose.fprintf ppf "(%a).%a" F.TypEnv.pr tenv F.Formula.pr phi
  in
  Verbose.printf "ext_cexs %a@." (Util.List.print @@ Util.List.print (fun fm (x,p) -> Format.fprintf fm "%a, %a" F.Idnt.pr x (Util.List.print pr) p)) ext_cexs;

  let fair_cond = Flag.Method.(!mode = FairNonTermination) in
  let cexs,prog = trans fair_cond cexs prog in

  Verbose.printf "@[<v>BEGIN refinement:@,  %a@," F.Prog.pr prog;
  let old_split_eq = !F.AbsType.split_equalities in
  let old_eap = !F.AbsType.extract_atomic_predicates in
  let old_chc_solver = F.HCCSSolver.get_dyn () in
  F.AbsType.split_equalities := true;
  F.AbsType.extract_atomic_predicates := true;
  F.HCCSSolver.link_dyn
    (fst -| fst -| F.AEHCCSSolver.solve
        (F.EAHCCSSolver.solve [] [] [] F.BwIPHCCSSolver.solve));
  let env = F.AbsTypInfer.refine prog labeled is_cp cexs true ext_cexs in
  F.AbsType.split_equalities := old_split_eq;
  F.AbsType.extract_atomic_predicates := old_eap;
  F.HCCSSolver.link_dyn old_chc_solver;
  Verbose.printf "END refinement@,@]";

  Flag.Log.Time.parameter_inference := !Flag.Log.Time.parameter_inference +. !F.EAHCCSSolver.elapsed_time;
  List.map (Pair.map F.Idnt.base inv_abst_type) env


(** TODO: move the following codes to another file *)

let gen_id =
  let cnt = ref 0 in
  fun () -> cnt := !cnt + 1; string_of_int !cnt

let rec trans_type typ =
  let xs, tyret = Type.decomp_tfun typ in
  let xs' =
    List.flatten
      (List.map
         (fun x ->
          let x' = trans_id x in
          (match x'.Id.typ with
           | Type.TFun(_, _)
           | Type.TTuple _(* ToDo: fix it *) ->
              F.Util.List.unfold
                (fun i ->
                 if i < !F.RefTypInfer.number_of_extra_params then
                   Some(Id.new_var ~name:"ex" Type.Ty.int, i + 1)
                 else
                   None)
                0
           | _ ->
              []) @ [x'])
         xs)
  in
  List.fold_right (fun x ty -> Type.TFun(x,ty)) xs' tyret
and trans_id x = Id.map_typ trans_type x

let of_desc t = assert false (* @todo translate FPAT term to S.term *)

let insert_extra_param t =
  let tmp = Time.get() in
  F.RefTypInfer.masked_params := [];
  let rec aux rfs bvs exs t =
    let desc =
      match t.S.desc with
      | S.End_of_definitions -> S.End_of_definitions
      | S.Const c -> S.Const c
      | S.Var y -> S.Var (trans_id y)
      | S.Fun(y, t1) ->
         let y' = trans_id y in
         let ys =
           match y'.Id.typ with
           | Type.TFun(_, _)
           | Type.TTuple _(* ToDo: fix it *) ->
              F.Util.List.unfold
                (fun i ->
                 if i < !F.RefTypInfer.number_of_extra_params then
                   Some(Id.new_var ~name:("ex" ^ gen_id ()) Type.Ty.int, i + 1)
                 else
                   None)
                0
           | _ ->
              []
         in
         let ys' = ys @ [y'] in
         let rfs =
           match rfs with
           | [] -> assert false
           | (f, xxs, recursive)::rfs' ->
              (f, xxs @ [y', ys], recursive)::rfs' in
         let f, _ =
           List.fold_left
             (fun (f, ty) y ->
              (fun t ->
               f {S.desc=S.Fun(y, t); S.typ=ty; S.attr=[]}),
              match ty with Type.TFun(_, ty') -> ty' | _ -> assert false)
             ((fun t -> t), trans_type t.S.typ)
             ys'
         in
         let bvs, exs =
           (if true then
              bvs @ ys'
            else
              bvs @ [y']),
           exs @ ys
         in
         (f (aux rfs bvs exs t1)).S.desc
      | S.App(t1, ts) ->
         (match t1.S.desc with S.App(_, _) -> assert false | _ -> ());
         let t1' = aux rfs bvs exs t1 in
         let recursive, xss =
           match t1'.S.desc with
           | S.Var(f) ->
              (try
                  let _, xxss, _ =
                    List.find
                      (fun (f', _, recursive) -> recursive && Id.(f' = f))
                      rfs
                  in
                  (Debug.printf "rec: %a@." Print.term t1');
                  let xxss =
                    List.take (List.length ts) xxss
                  in
                  true,
                  List.map2
                    (fun t (x, xs) ->
                     match t.S.typ with
                     | Type.TFun(_, _)
                     | Type.TTuple _(* ToDo: fix it *) ->
                        (match t.S.desc with
                         | S.Var(y) when Id.(x = y) ->
                             Debug.printf "arg %a of %a not changed@," Print.id x Print.id f;
                             xs
                         | _ -> [])
                     | _ -> [])
                    ts xxss
                with Not_found ->
                  Debug.printf "non_rec: %a@." Print.term t1';
                  false, [])
           | _ ->
               Debug.printf "non_rec: %a@." Print.term t1';
               false, []
         in
         let ts' = List.map (aux rfs bvs exs) ts in
         let tss =
           List.mapi
             (fun i t ->
              match t.S.typ with
              | Type.TFun(_, _)
              | Type.TTuple _(* ToDo: fix it *) ->
                 let bvs =
                   bvs
                   |> List.filter (fun x -> x.Id.typ = Type.Ty.int)
                   |> List.map (Id.to_string ~plain:false >> F.Idnt.make)
                 in
                 let exs = List.map (Id.to_string ~plain:false >> F.Idnt.make) exs in
                 F.RefTypInfer.new_params
                   (if recursive then
                      Some(F.Util.List.nth xss i
                           |> List.map (Id.to_string ~plain:false >> F.Idnt.make))
                    else
                      None)
                   bvs exs
                 |> List.map of_desc
              | _ -> [])
             ts'
         in
         let ts'' =
           List.flatten
             (List.map2 (fun ts t -> ts @ [t]) tss ts')
         in
         S.App(t1', ts'')
      | S.If(t1, t2, t3) ->
         S.If(aux rfs bvs exs t1, aux rfs bvs exs t2, aux rfs bvs exs t3)
      | S.Local(S.Decl_type decls, t2) -> S.Local(S.Decl_type decls, aux rfs bvs exs t2)
      | S.Local(S.Decl_let bindings, t2) ->
         let bvs' =
           bvs @ List.map fst bindings
         in
         let aux' (f,t) =
           let f' = trans_id f in
           (* mutual recursion and binding partial applied functions are not supported
              let rfs' = (if flag = Flag.Nonrecursive then [] else List.map (fun (f, _, _) -> Id.to_string f) bindings) @ rfs in
            *)
           f', aux rfs bvs' exs t
         in
         let bindings' = List.map aux' bindings in
         S.Local
           (S.Decl_let bindings',
            aux rfs
                (bvs @
                   List.map
                     fst
                     bindings')
                exs t2)
      | S.BinOp(op, t1, t2) -> S.BinOp(op, aux rfs bvs exs t1, aux rfs bvs exs t2)
      | S.Not t1 -> S.Not (aux rfs bvs exs t1)
      | S.Event(s,b) -> S.Event(s,b)
      | S.Record fields -> S.Record (List.map (Pair.map_snd @@ aux rfs bvs exs) fields)
      | S.Field(t1,s) -> S.Field(aux rfs bvs exs t1,s)
      | S.SetField(t1,s,t2) -> S.SetField(aux rfs bvs exs t1,s,aux rfs bvs exs t2)
      | S.Nil -> S.Nil
      | S.Cons(t1,t2) ->
         S.Cons(aux rfs bvs exs t1, aux rfs bvs exs t2)
      | S.Constr(s,ts) ->
         S.Constr(s, List.map (aux rfs bvs exs) ts)
      | S.Match(t1,pats) ->
         let aux' (pat, t) =
           (* ToDo: need to update pat!? *)
           pat,
           aux rfs (bvs @ S.get_bv_pat pat) exs t
         in
         S.Match(aux rfs bvs exs t1, List.map aux' pats)
      | S.Raise t -> S.Raise (aux rfs bvs exs t)
      | S.TryWith(t1,t2) -> S.TryWith(aux rfs bvs exs t1, aux rfs bvs exs t2)
      | S.Tuple ts -> S.Tuple (List.map (aux rfs bvs exs) ts)
      | S.Proj(i,t) -> S.Proj(i, aux rfs bvs exs t)
      | S.Bottom -> S.Bottom
      | S.Label(info,t) -> S.Label(info, aux rfs bvs exs t)
      | S.Ref t -> S.Ref(aux rfs bvs exs t)
      | S.Deref t -> S.Deref(aux rfs bvs exs t)
      | S.SetRef(t1,t2) ->
         S.SetRef(aux rfs bvs exs t1, aux rfs bvs exs t2)
      | S.TNone -> S.TNone
      | S.TSome t -> S.TSome(aux rfs bvs exs t)
      | S.Module decls -> unsupported "insert_extra_param Module"
    in
    {t with S.desc}
  in
  let res = aux [] [] [] t in
  let _ = Time.add tmp Flag.Log.Time.parameter_inference in
  res

let instantiate_param prog =
  let tmp = Time.get() in
  let typs = prog.CEGAR_syntax.env in
  let fdefs = prog.CEGAR_syntax.defs in
  let main = prog.CEGAR_syntax.main in
  (if !F.RefTypInfer.prev_sol = [] then
     F.RefTypInfer.init_sol (conv_prog prog));
  let map =
    List.map
      (fun (x, t) ->
       F.Idnt.string_of x, inv_term t)
      !F.RefTypInfer.prev_sol
  in
  let res =
    typs,
    List.map
      (fun (f, args, guard, events, body) ->
       (f,
        args,
        CEGAR_util.subst_map map guard,
        events,
        CEGAR_util.subst_map map body))
      fdefs,
    main
  in
  Time.add tmp Flag.Log.Time.parameter_inference;
  res





let simplify_term t =
(*
  if false then
  let _, t = CEGAR_trans.trans_term {S.desc = t; S.typ = Type.TBool } in
  let t = conv_formula t in
  let t = F.FormulaSimplifier.simplify t in
  let t = inv_formula t in
  (CEGAR_trans.trans_inv_term t).S.desc
  else
 *)
  t

let simplify_term p =
  { p with S.desc = simplify_term p.S.desc }

let compute_strongest_post prog ce ext_cex =
  F.RankFunInfer.compute_strongest_post (conv_prog prog) ce ext_cex


let implies = F.SMTProver.implies_dyn
let is_sat = F.SMTProver.is_sat_dyn
let is_valid t = implies [F.Formula.of_term @@ F.Term.mk_const F.Const.True] [t]
let is_valid_forall_exists xs ys cond p =
  let open Fpat in
  let aux x = Idnt.make x, Type.mk_int in
  let p' =
    Formula.forall (List.map aux xs) @@
      Formula.exists (List.map aux ys) @@
        Formula.imply (Formula.band @@ List.map conv_formula cond) @@
          conv_formula p
  in
  SMTProver.is_valid_dyn p'

let conv_pred (env: CEGAR_syntax.env) (p: CEGAR_syntax.t) =
  let env = env
  |> List.filter (is_base -| snd)
  |> List.map (F.Pair.map F.Idnt.make conv_typ) in
  let phi = conv_formula p in
  ((env, phi) : F.Pred.t)

let trans_ext (renv : (int * CEGAR_syntax.env) list) (map : (int * (CEGAR_syntax.t -> CEGAR_syntax.t list)) list) (n, bs) =
  let r = make_randint_name n in
  let env = List.assoc n renv in
  let new_var = Var(r) in
  let abst_preds = (List.assoc n map) new_var in
  let rand_var = conv_var r in
  let add_pred acc p = function
    | Positive -> make_and p acc
    | Negative -> make_and (make_not p) acc
    | Do_not_Care -> acc
  in
  let ext_abstraction = List.map (List.fold_left2 add_pred (Const True) abst_preds) bs in
  let preds_sequence = List.map (conv_pred env) ext_abstraction in
  rand_var, preds_sequence


let parse_arg arg =
  let args = Array.of_list @@ "FPAT" :: Util.String.split_blanc arg in
  let usage = "Options for FPAT are:" in
  try
    Arg.parse_argv ~current:(ref 0) args (Arg.align F.FPATConfig.arg_spec) ignore usage
  with
  | Arg.Bad s
  | Arg.Help s -> Format.printf "%s" s; exit 0


let to_hcs constrs =
  let to_formula (pre,ant) =
    let pre' = List.map (Fpat.Formula.of_term -| of_term) pre in
    let ant' = Fpat.Formula.of_term @@ of_term ant in
    Fpat.HCCS.of_formula pre' ant'
  in
  Util.List.flatten_map to_formula constrs
