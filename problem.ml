open Util

type t =
    {term: Syntax.term;
     env: (Syntax.id * Ref_type.t) list;
     attr: attr list;
     kind: kind;
     info: info}
    [@@deriving show]

(* TODO: add Termination etc. *)
and kind =
  | Safety
  | Ref_type_check of (Syntax.id * Ref_type.t) list

and info = string list

and attr = ACPS

let term {term} = term
let env {env} = env
let attr {attr} = attr

let safety ?(env=[]) ?(attr=[]) ?(info=[]) term =
  {term; env; attr; kind=Safety; info}

let ref_type_check ?(env=[]) ?(attr=[]) ?(info=[]) term check =
  {term; env; attr; kind=Ref_type_check check; info}

let map ?(tr_env=Fun.id) tr {term; env; attr; kind; info} =
  let term = tr term in
  let env = tr_env env in
  {term; env; attr; kind; info}

let map_list tr {term; env; attr; kind; info} =
  let terms = tr term in
  List.map (fun term -> {term; env; attr; kind; info}) terms

let map_on focus ?(tr_env=Fun.id) tr {term; env; attr; kind; info} =
  let r = tr term in
  let ctx,term = focus r in
  let env = tr_env env in
  ctx {term; env; attr; kind; info}

let print_attr fm attr =
  match attr with
  | ACPS -> Format.fprintf fm "ACPS"

let print_kind fm kind =
  match kind with
  | Safety -> Format.fprintf fm "Safety"
  | Ref_type_check env -> Format.fprintf fm "Refinement type checking %a" Print.(list (id * Ref_type.print)) env

let print_info fm info =
  Format.printf "%a" (Print.list Format.pp_print_string) info

let print fm {term; env; attr; kind; info} =
  Format.fprintf fm "@[{@[term:%a@];@ @[env:%a@];@ @[attr:%a@];@ @[kind:%a@];@ @[info:%a@]}@]"
                 Print.term_typ_top term
                 Print.(list (id * Ref_type.print)) env
                 (Print.list print_attr) attr
                 print_kind kind
                 print_info info

let print_debug fm {term; env; attr; kind; info} =
  Format.fprintf fm "@[{@[term:%a@];@ @[env:%a@];@ @[attr:%a@];@ @[kind:%a@];@ @[info:%a@]}@]"
                 Print.term' term
                 Print.(list (id * Ref_type.print)) env
                 (Print.list print_attr) attr
                 print_kind kind
                 print_info info
