open Util
open Syntax

module Dbg = Debug.Make (struct
  let check = Flag.Debug.make_check __MODULE__
end)

type t = {
  term : term;
  ext_mod_typ : ext_mod_typ list; (* The order matters *)
  spec : Spec.t; (* Specification to be checked, specification of external functions, etc. *)
  attr : attr list; (* Attributes of the problem *)
  kind : kind; (* Type of the problem (reachability, termination, etc.) *)
  info : info; (* Information of preprocess? (TODO: should be merged with Preprocess.info? ) *)
}

and ext_mod_typ = term Type.mod_typ

(* TODO: add Termination etc. *)
and kind = Safety | Ref_type_check of (id * Ref_type.t) list
and info = string list

and attr =
  | Module (* Problem using module features *)
  | Set_main (* A main function has been set *)
  | Sliced (* Sliced problem *)
  | CPS (* Problem with cps-terms *)
[@@deriving show]

let term { term } = term
let spec { spec } = spec
let attr { attr } = attr
let kind { kind } = kind
let info { info } = info
let init_info = []

(* Constructions *)

let safety ?(spec = Spec.init) ?(ext_mod_typ = []) ?(attr = []) ?(info = []) term =
  let attr = Module :: attr in
  { term; ext_mod_typ; spec; attr; kind = Safety; info }

let ref_type_check ?(spec = Spec.init) ?(ext_mod_typ = []) ?(attr = []) ?(info = []) term check =
  let attr = Module :: attr in
  { term; ext_mod_typ; spec; attr; kind = Ref_type_check check; info }

(* Transformations *)

let map_spec ?tr_ref ?tr_env spec =
  match (tr_ref, tr_env) with
  | Some _, Some _ -> [%invalid_arg]
  | Some f, _ -> Spec.map_ref f spec
  | None, Some f -> Spec.map_ref_env f spec
  | None, None -> spec

let map ?tr_ref ?tr_env tr problem =
  let term = tr problem.term in
  let spec = map_spec ?tr_ref ?tr_env problem.spec in
  { problem with term; spec }

let map_list tr problem =
  let terms = tr problem.term in
  List.map (fun term -> { problem with term }) terms

let map_on focus ?tr_ref ?tr_env tr problem =
  let r = tr problem.term in
  let ctx, term = focus r in
  let spec = map_spec ?tr_ref ?tr_env problem.spec in
  ctx { problem with term; spec }

(* Printers *)

let print_attr fm attr =
  match attr with
  | Set_main -> Format.fprintf fm "Set_main"
  | CPS -> Format.fprintf fm "CPS"
  | Sliced -> Format.fprintf fm "Sliced"
  | Module -> Format.fprintf fm "Module"

let print_kind fm kind =
  match kind with
  | Safety -> Format.fprintf fm "Safety"
  | Ref_type_check env ->
      Format.fprintf fm "Refinement type checking %a" Print.(list (id * Ref_type.print)) env

let print_info fm info =
  let pr fm s = Format.fprintf fm "\"%s\"" s in
  Format.fprintf fm "%a" (Print.list pr) info

let print_params fm params =
  match params with
  | [] -> ()
  | [ ty ] -> Format.fprintf fm "%a " Print.typ ty
  | _ -> Format.fprintf fm "(%a) " (print_list Print.typ ",") params

let print_ext_mod_typ fm (m, ty) = Format.fprintf fm "@[module %a : %a@]" Id.print m Print.typ ty

let print_list pr fm xs =
  let limit = !Print.config_default.length in
  Format.fprintf fm "@[<hov 1>[%a]@]" (print_list ~limit pr ";@ ") xs

let ignore_stdlib ext_mod_typ =
  let check s = s = "Stdlib" || List.exists (String.starts_with s) [ "Stdlib__"; "Camlinternal" ] in
  List.filter_out (check -| Id.name -| fst) ext_mod_typ

let print_ext_mod_typ_if_any fm ext_mod_typ =
  if ext_mod_typ <> [] then
    ext_mod_typ
    |> (not !!Dbg.check) ^> ignore_stdlib
    |> Format.fprintf fm ";@ @[ext_mod_typ:%a@]" (print_list print_ext_mod_typ)

let print_attr_if_any fm attr =
  if attr <> [] then Format.fprintf fm ";@ @[attr:%a@]" (print_list print_attr) attr

let print_spec_if_any fm spec =
  if spec <> Spec.init then Format.fprintf fm ";@ @[spec:%a@]" Spec.print spec

let print_info_if_any fm info =
  if info <> [] then Format.fprintf fm ";@ @[info:%a@]" print_info info

let print fm { term; ext_mod_typ; spec; attr; kind; info } =
  Format.fprintf fm "{@[@[term:%a@]" Print.term term;
  Format.fprintf fm "%a" print_ext_mod_typ_if_any ext_mod_typ;
  Format.fprintf fm "%a" print_spec_if_any spec;
  Format.fprintf fm "%a;@ " print_attr_if_any attr;
  Format.fprintf fm "@[kind:%a@]" print_kind kind;
  Format.fprintf fm "%a@]}" print_info_if_any info

let print' fm { term; ext_mod_typ; spec; attr; kind; info } =
  Format.fprintf fm "{@[@[term:%a@]" Print.term' term;
  Format.fprintf fm "%a" print_ext_mod_typ_if_any ext_mod_typ;
  Format.fprintf fm "%a" print_spec_if_any spec;
  Format.fprintf fm "%a;@ " print_attr_if_any attr;
  Format.fprintf fm "@[kind:%a@]" print_kind kind;
  Format.fprintf fm "%a@]}" print_info_if_any info

let print_debug = print'

let eq problem1 problem2 =
  Term_util.same_term' problem1.term problem2.term
  && problem1.ext_mod_typ = problem2.ext_mod_typ
  && problem1.spec = problem2.spec
  && problem1.attr = problem2.attr
  && problem1.kind = problem2.kind
  && problem1.info = problem2.info
