open Util
module RT = CEGAR_ref_type
module IT = Inter_type
module AT = CEGAR_type
module CS = CEGAR_syntax

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let ref_base_of_abs_base = function
  | AT.TUnit -> RT.Unit
  | AT.TInt -> RT.Int
  | AT.TBool -> RT.Bool
  | AT.TAbst s -> RT.Abst s

let rec simple typ =
  match typ with
  | AT.TBase(base,_) when base = AT.typ_result_base -> AT.TBase(AT.TUnit, fun _ -> [])
  | AT.TBase(base,_) -> AT.TBase(base, fun _ -> [])
  | AT.TConstr _ -> unsupported "CEGAR_type.remove_pred: TConstr"
  | AT.TApp _ -> unsupported "CEGAR_type.remove_pred: TApp"
  | AT.TFun(typ1, typ2) -> AT.TFun(simple typ1, simple -| typ2)

let rec ref_of_inter env cond atyp ityp =
  match atyp,ityp with
  | _, IT.Inter ityps ->
      let rtyps = List.map (ref_of_inter env cond atyp) ityps in
      RT.Inter(simple atyp, rtyps)
  | AT.TFun(AT.TBase(b,ps), atyp2), _ ->
      let x = CS.new_id "x" in
      let ps' = ps (CS.Var x) in
      let ityps,ityp' = IT.decomp_fun (List.length ps') ityp in
      let env' = (x,AT.TBase(b,fun _ -> []))::env in
      let b' = ref_base_of_abs_base b in
      let aux p ityp =
        let is_true ityp =
          if !Flag.ModelCheck.church_encode then
            match ityp with
            | IT.Fun(IT.Base _, IT.Fun(IT.Inter [], IT.Base _)) -> true
            | _ -> false
          else
            ityp = IT.Base IT.True
        in
        let is_false ityp =
          if !Flag.ModelCheck.church_encode then
            match ityp with
            | IT.Fun(IT.Inter [], IT.Fun(IT.Base _, IT.Base _)) -> true
            | _ -> false
          else
            ityp = IT.Base IT.False
        in
        if is_true ityp then
          [p]
        else if is_false ityp then
          [CS.make_not p]
        else if ityp = IT.Inter [] then
          []
        else
          (Format.eprintf "%a@." IT.print ityp; assert false)
      in
      let ts = List.rev_flatten @@ List.map2 aux ps' ityps in
      let p = List.fold_left CS.make_and (CS.Const CS.True) ts in
      let cond' = p::cond in
      let p' = CEGAR_util.normalize_bool_term p in
      let rtyp = ref_of_inter env' cond' (atyp2 (CS.Var x)) ityp' in
      RT.Fun(x, RT.Base(b',x,p'), rtyp)
  | AT.TFun(atyp1,atyp2), IT.Fun(ityp1,ityp2) ->
      let x = CS.new_id "x" in
      let rtyp1 = ref_of_inter env cond atyp1 ityp1 in
      let rtyp2 = ref_of_inter env cond (atyp2 (CS.Var x)) ityp2 in
      RT.Fun(x, rtyp1, rtyp2)
  | AT.TBase(AT.TUnit, _), IT.Base (IT.State _) ->
      RT.Base(RT.Unit, "", CS.Const CS.True)
  | AT.TBase(base, _), IT.Base (IT.State _) when base = AT.typ_result_base ->
      RT.Base(RT.Unit, "", CS.Const CS.True)
  | _ -> Format.eprintf "atyp:%a@.ityp:%a@." CEGAR_print.typ atyp IT.print ityp; assert false

let ref_of_inter atyp ityp =
  let r = ref_of_inter [] [] atyp ityp in
  Debug.printf "atyp:%a@.ityp:%a@." CEGAR_print.typ atyp IT.print ityp;
  Debug.printf "r:%a@.@." RT.print r;
  r
