open Util
open Syntax

type t =
  {term: term;
   ext_typ: ext_typ list;
   ext_exc: ext_exc list;
   ext_mod_typ: ext_mod_typ list;
   spec: Spec.t;
   attr: attr list;
   kind: kind;
   info: info}

and ext_typ = Type.Path.t * (params * typ)
and ext_exc = Type.Path.t * typ list
and ext_mod_typ = term Type.mod_typ

(* TODO: add Termination etc. *)
and kind =
  | Safety
  | Ref_type_check of (id * Ref_type.t) list

and info = string list

and attr =
  | Module   (* Problem using module features *)
  | Set_main (* A main function has been set *)
  | Sliced   (* Sliced problem *)
  | CPS      (* Problem with cps-terms *)
[@@deriving show]

let term {term} = term
let spec {spec} = spec
let attr {attr} = attr
let kind {kind} = kind
let info {info} = info

let init_info = []

(* Constructions *)

let safety ?(spec=Spec.init) ?(ext_typ=[]) ?(ext_exc=[]) ?(ext_mod_typ=[]) ?(attr=[]) ?(info=[]) term =
  let attr = Module::attr in
  {term; ext_typ; ext_exc; ext_mod_typ; spec; attr; kind=Safety; info}

let ref_type_check ?(spec=Spec.init) ?(ext_typ=[]) ?(ext_exc=[]) ?(ext_mod_typ=[]) ?(attr=[]) ?(info=[]) term check =
  let attr = Module::attr in
  {term; ext_typ; ext_exc; ext_mod_typ; spec; attr; kind=Ref_type_check check; info}

(* Transformations *)

let map_spec ?tr_ref ?tr_env spec =
  match tr_ref, tr_env with
  | Some f, _ -> Spec.map_ref f spec
  | None, Some f -> Spec.map_ref_env f spec
  | None, None -> spec

let map ?tr_ref ?tr_env tr problem =
  let term = tr problem.term in
  let spec = map_spec ?tr_ref ?tr_env problem.spec in
  {problem with term; spec}

let map_list tr problem =
  let terms = tr problem.term in
  List.map (fun term -> {problem with term}) terms

let map_on focus ?tr_ref ?tr_env tr problem =
  let r = tr problem.term in
  let ctx,term = focus r in
  let spec = map_spec ?tr_ref ?tr_env problem.spec in
  ctx {problem with term; spec}

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
  | Ref_type_check env -> Format.fprintf fm "Refinement type checking %a" Print.(list (id * Ref_type.print)) env

let print_info fm info =
  let pr fm s = Format.fprintf fm "\"%s\"" s in
  Format.fprintf fm "%a" (Print.list pr) info

let print_params fm params =
  match params with
  | [] -> ()
  | [ty] -> Format.fprintf fm "%a " Print.typ ty
  | _ -> Format.fprintf fm "(%a) " (print_list Print.typ ",") params

let print_ext_typ fm (p,(params,ty)) = Format.fprintf fm "@[%a%a = %a@]" print_params params Type.Path.print p Print.typ ty

let print_ext_exc fm (p,tys) =
  if tys = [] then
    Format.fprintf fm "@[exn += %a@]" Type.Path.print p
  else
    Format.fprintf fm "@[exn += %a of %a@]" Type.Path.print p (print_list Print.typ " * ") tys

let print_ext_mod_typ fm (m,ty) =
  Format.fprintf fm "@[module %a : %a@]" Id.print m Print.typ ty

let print_list pr fm xs =
  let limit = !Print.config_default.length in
  Format.fprintf fm "@[<hov 1>[%a]@]" (print_list ~limit pr ";@ ") xs

let print_ext_typ_if_any fm ext_typ =
  if ext_typ <> [] then
    Format.fprintf fm ";@ @[ext_typ:%a@]" (print_list print_ext_typ) ext_typ

let print_ext_exc_if_any fm ext_exc =
  if ext_exc <> [] then
    Format.fprintf fm ";@ @[ext_exc:%a@]" (print_list print_ext_exc) ext_exc

let print_ext_mod_typ_if_any fm ext_mod_typ =
  if ext_mod_typ <> [] then
    Format.fprintf fm ";@ @[ext_mod_typ:%a@]" (print_list print_ext_mod_typ) ext_mod_typ

let print_attr_if_any fm attr =
  if attr <> [] then
    Format.fprintf fm ";@ @[attr:%a@]" (print_list print_attr) attr

let print_spec_if_any fm spec =
  if spec <> Spec.init then
    Format.fprintf fm ";@ @[spec:%a@]" Spec.print spec

let print_info_if_any fm info =
  if info <> [] then
    Format.fprintf fm ";@ @[info:%a@]" print_info info

let print fm {term; ext_typ; ext_exc; ext_mod_typ; spec; attr; kind; info} =
  Format.fprintf fm "{@[@[term:%a@]%a%a%a%a%a;@ @[kind:%a@]%a@]}"
                 Print.term_typ_top       term
                 print_ext_typ_if_any     ext_typ
                 print_ext_exc_if_any     ext_exc
                 print_ext_mod_typ_if_any ext_mod_typ
                 print_spec_if_any        spec
                 print_attr_if_any        attr
                 print_kind               kind
                 print_info_if_any        info

let print' fm {term; ext_typ; ext_exc; ext_mod_typ; spec; attr; kind; info} =
  Format.fprintf fm "{@[@[term:%a@]%a%a%a%a%a;@ @[kind:%a@]%a@]}"
                 Print.term'              term
                 print_ext_typ_if_any     ext_typ
                 print_ext_exc_if_any     ext_exc
                 print_ext_mod_typ_if_any ext_mod_typ
                 print_spec_if_any        spec
                 print_attr_if_any        attr
                 print_kind               kind
                 print_info_if_any        info

let print_debug fm {term; ext_typ; ext_exc; ext_mod_typ; spec; attr; kind; info} =
  Format.fprintf fm "{@[term:%a@]%a%a%a%a;%a@ @[kind:%a@]%a}"
                 Print.term'              term
                 print_ext_typ_if_any     ext_typ
                 print_ext_exc_if_any     ext_exc
                 print_ext_mod_typ_if_any ext_mod_typ
                 print_spec_if_any        spec
                 print_attr_if_any        attr
                 print_kind               kind
                 print_info_if_any        info

let exn_of_ext_exc {ext_exc; _} =
  let rows = List.map (fun (c,row_args) -> {Type.row_constr = Type_util.constr_of_string (Type.Path.to_string c); row_args; row_ret=None}) ext_exc in
  Type.TVariant(VNonPoly, rows)
