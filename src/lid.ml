open Util
open! Type
open Type_util
open Syntax

let _LId x = LId x
let _LDot lid s = LDot(lid, s)
let _LApp lid1 lid2 = LApp(lid1, lid2)

let id_of lid =
  match lid with
  | LId x -> x
  | _ -> invalid_arg "%s" __FUNCTION__

let rec cons m lid =
  match lid with
  | LId x -> LDot(LId m, Id.name x)
  | LDot(p,s) -> LDot(cons m p, s)
  | _ -> invalid_arg "Longid.cons"

let rec append path1 path2 =
  match path2 with
  | LId x -> LDot(path1, Id.name x)
  | LDot(path2',s) -> LDot(append path1 path2', s)
  | LApp _ -> [%invalid_arg]

let rec head lid =
  match lid with
  | LId x -> x
  | LDot(lid', _) -> head lid'
  | LApp _ -> invalid_arg "Longid.head"

let rec heads lid =
  match lid with
  | LId x -> [x]
  | LDot(lid', _) -> heads lid'
  | LApp(lid1,lid2) -> heads lid1 @@@ heads lid2

let rec last lid =
  match lid with
  | LId x -> Id.name x
  | LDot(_, s) -> s
  | LApp(_, lid2) -> last lid2

let rec print_gen pr fm lid =
  let print = print_gen (fun fm x -> Format.pp_print_string fm (Id.name x)) in
  match lid with
  | LId x -> pr fm x
  | LDot(p,s) -> Format.fprintf fm "%a.%s" print p s
  | LApp(p1,p2) -> Format.fprintf fm "%a(%a)" print p1 print p2

let print fm lid = print_gen Id.print fm lid

let to_string lid = Format.asprintf "%a" print lid
let name = to_string

(*
let sig_values ty =
  match ty with
  | TModule sgn -> Some (sgn.sig_values)
  | _ -> None
 *)

let rec flatten acc = function
  | LId s -> s, acc
  | LDot(lid, s) -> flatten (s :: acc) lid
  | LApp(_, _) -> [%invalid_arg]
let flatten lid = flatten [] lid

let rec head lid =
  match lid with
  | LId id -> id
  | LDot(p, _) -> head p
  | LApp _ -> [%invalid_arg]

let typ lid =
  match lid with
  | LId x -> Id.typ x
  | LDot _ ->
      (try
         let m = head lid in
         let env = Tenv.add_module m (Id.typ m) ~env:!!Tenv.empty in
         Tenv.assoc_value (path_of_lid lid) ~env
       with Invalid_argument _ -> Ty.unknown) (* TODO *)
  | LApp _ -> [%unsupported]

let rec eq lid1 lid2 =
  match lid1, lid2 with
  | LId id1, LId id2 -> Id.eq id1 id2
  | LDot(p1,s1), LDot(p2,s2) -> eq p1 p2 && s1 = s2
  | LApp(p11,p12), LApp(p21,p22) -> eq p11 p21 && eq p12 p22
  | _ -> false

let rec compare lid1 lid2 =
  match lid1, lid2 with
  | LId _, (LDot _ | LApp _) -> -1
  | LDot _, LApp _ -> -1
  | LApp _, (LDot _ | LId _) -> 1
  | LDot _, LId _ -> 1
  | LId id1, LId id2 -> Id.compare id1 id2
  | LDot(p1,s1), LDot(p2,s2) -> Compare.dict compare p1 p2 Stdlib.compare s1 s2
  | LApp(p11,p12), LApp(p21,p22) -> Compare.dict compare p11 p21 compare p12 p22

let rec map ~f ?(g=Fun.id) lid =
  match lid with
  | LId id -> LId (f id)
  | LDot(lid', s) -> LDot(map ~f ~g lid', g s)
  | LApp(lid1, lid2) -> LApp(map ~f ~g lid1, map ~f ~g lid2)

let map_name g lid = map ~f:(Id.map_name g) ~g lid

let rec subst_head map lid =
  let sb = subst_head map in
  match lid with
  | LId id -> Id.List.assoc_default lid id map
  | LDot(p, s) -> LDot(sb p, s)
  | LApp(p1, p2) -> LApp(sb p1, sb p2)

let (=) = eq
