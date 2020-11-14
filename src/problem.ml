open Util

type t =
  {term: Syntax.term;
   spec: Spec.t;
   attr: attr list;
   kind: kind;
   info: info}

(* TODO: add Termination etc. *)
and kind =
  | Safety
  | Ref_type_check of (Syntax.id * Ref_type.t) list

and info = string list

and attr = Set_main | Sliced | ACPS

let term {term} = term
let spec {spec} = spec
let attr {attr} = attr
let kind {kind} = kind
let info {info} = info

let init_info = []

(* Constructions *)

let safety ?(spec=Spec.init) ?(attr=[]) ?(info=[]) term =
  {term; spec; attr; kind=Safety; info}

let ref_type_check ?(spec=Spec.init) ?(attr=[]) ?(info=[]) term check =
  {term; spec; attr; kind=Ref_type_check check; info}

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
  | ACPS -> Format.fprintf fm "ACPS"
  | Sliced -> Format.fprintf fm "Sliced"

let print_kind fm kind =
  match kind with
  | Safety -> Format.fprintf fm "Safety"
  | Ref_type_check env -> Format.fprintf fm "Refinement type checking %a" Print.(list (id * Ref_type.print)) env

let print_info fm info =
  let pr fm s = Format.fprintf fm "\"%s\"" s in
  Format.fprintf fm "%a" (Print.list pr) info

let print fm {term; spec; attr; kind; info} =
  Format.fprintf fm "{@[@[term:%a@];@ @[spec:%a@];@ @[attr:%a@];@ @[kind:%a@];@ @[info:%a@]@]}"
                 Print.term_typ_top term
                 Spec.print spec
                 (Print.list print_attr) attr
                 print_kind kind
                 print_info info

let print' fm {term; spec; attr; kind; info} =
  Format.fprintf fm "{@[@[term:%a@];@ @[spec:%a@];@ @[attr:%a@];@ @[kind:%a@];@ @[info:%a@]@]}"
                 Print.term' term
                 Spec.print spec
                 (Print.list print_attr) attr
                 print_kind kind
                 print_info info

let print_debug fm {term; spec; attr; kind; info} =
  Format.fprintf fm "{@[term:%a@];@ @[spec:%a@];@ @[attr:%a@];@ @[kind:%a@];@ @[info:%a@]}"
                 Print.term' term
                 Spec.print spec
                 (Print.list print_attr) attr
                 print_kind kind
                 print_info info
