open Util
open Combinator

type elem = Idnt.t * Pred.t
type t = elem list

(** {6 Printers} *)

let pr_elem ppf (p, (tenv, phi)) =
  Format.fprintf
    ppf
    "@[<hov2>%a =@ %a@]"
    PredVar.pr (PredVar.make p tenv)
    Formula.pr phi

let pr ppf psub =
  Format.fprintf ppf "@[<hv>%a@]" (List.pr pr_elem "@,") psub

(** {6 Inspectors} *)

let args_of p psub = List.assoc p psub |> fst

let fvs_elem (_, pred) = Pred.fvs pred
let fvs psub = List.concat_map fvs_elem psub

let coeffs_elem (_, pred) = Pred.coeffs pred
let coeffs psub = List.concat_map coeffs_elem psub

let pvs psub = List.map fst psub

let lookup psub atm =
  psub
  |> List.filter (fst >> (=) (Pva.idnt_of atm))
  |> List.map snd
  |> List.map (flip Pred.apply (Pva.args_of atm))
  |> Formula.bor
let lookup =
  Logger.log_block2
        "PredSubst.lookup"
    lookup

let lookup_and psub atm =
  psub
  |> List.filter (fst >> (=) (Pva.idnt_of atm))
  |> List.map snd
  |> List.map (flip Pred.apply (Pva.args_of atm))
  |> Formula.band
let lookup_and =
  Logger.log_block2
        "PredSubst.lookup_and"
    lookup_and

let lookup_fresh psub atm =
  psub
  |> List.filter (fst >> (=) (Pva.idnt_of atm))
  |> (if_ ((=) [])
        (fun _ -> raise Not_found)
        (List.map (snd >> Pred.fresh)))
  |> List.map (flip Pred.apply (Pva.args_of atm))
  |> Formula.bor
let lookup_fresh =
  Logger.log_block2
        "PredSubst.lookup_fresh"
    lookup_fresh

let lookup_node psub popt =
  match popt with
  | None ->
    Formula.mk_false
  | Some(p) ->
    if List.mem_assoc (PredVar.idnt_of p) psub then
      lookup psub (Pva.of_pvar p)
    else
      begin
        Format.printf "psub: %a@,p: %a@," pr psub PredVar.pr p;
        if true then
          assert false
        else
          Formula.mk_true(*@todo*)
      end
let lookup_node =
  Logger.log_block2
        "PredSubst.lookup_node"
    lookup_node

let wo_fvs = List.for_all (fvs_elem >> (=) [])

(** {6 Auxiliary constructors} *)

let bot_of_tenv = List.map (fun (p, ty) -> p, Pred.mk_bot ty)
let top_of_tenv = List.map (fun (p, ty) -> p, Pred.mk_top ty)

let mk_elem p tenv phi = p, (tenv, phi)
let elem_of_pvar pv phi = PredVar.idnt_of pv, (PredVar.args_of pv, phi)

(** {6 Operators} *)

let merge psub =
  psub
  |> List.classify (comp2 (=) fst fst)
  |> List.map (fun ((p, (tenv, _)) :: _) -> p, tenv)
  |> List.map
    (fun (p, tenv) ->
       PredVar.make p tenv
       |> Pva.of_pvar
       |> lookup psub
       |> mk_elem p tenv)

let merge_and psub =
  psub
  |> List.classify (comp2 (=) fst fst)
  |> List.map (fun ((p, (tenv, _)) :: _) -> p, tenv)
  |> List.map
    (fun (p, tenv) ->
       PredVar.make p tenv
       |> Pva.of_pvar
       |> lookup_and psub
       |> mk_elem p tenv)

let join phis psubs =
  let psub = List.flatten psubs in
  psub
  |> pvs
  |> List.unique
  |> List.map
    (fun p ->
       let args = args_of p psub in
       List.map2
         (fun phi psub ->
            let phi' =
              PredVar.make p args
              |> Pva.of_pvar
              |>  lookup psub
            in
            Formula.band [phi; phi'])
         phis psubs
       |> Formula.bor
       |> mk_elem p args)

let restrict = Map_.restrict

let normalize =
  List.map (Pair.map_snd Pred.normalize)
  >> List.sort (comp2 compare fst fst)


let size = List.map (snd >> snd >> CunFormula.size) >> Integer.sum_list
