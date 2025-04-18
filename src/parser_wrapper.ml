(* This extension point is replaced with `include Parser_wrapper_X_YZ` by PPX
   where X.YZ is the OCaml version used to compile *)
[%%include "Parser_wrapper"]

open Util
open Mochi_util
open Asttypes
open Typedtree
module P = Path (* Path is shadowed by Type.Path *)
open Types
open Type
open! Type_util
open Syntax
open Term_util

module Dbg = Debug.Make (struct
  let check = Flag.Debug.make_check __MODULE__
end)

module Dbg_orig = Debug.Make (struct
  let check = Flag.Debug.make_check (__MODULE__ ^ ".orig")
end)

type env = {
  id_env : id list;  (** Environment for matching types of each bound variable and its occurrence *)
  tconstrs : P.Set.t;  (** Set of type constructors used  *)
  tvar_env : typ IntMap.t;  (** Environment of type variables *)
  shadowed_primitive : string list;
      (** primitevs functions/operators shadowed by user-defined ones *)
  mod_typ_env : (Ident.t * (id * typ)) list;  (** Type environment for external modules *)
  mutable vars : StringSet.t;  (** Set of variable names used for gen_fresh *)
  exist_vars : (int * term tvar) list;  (** Environment of type variables for existential type *)
  target_locs : (string * bool ref) list;  (** Unused targets *)
  stdlib_visited : bool;  (** Preventing non-termination due to [Stdlib.ref] in [Stdlib__Sys] *)
  spec : Spec.t;  (** For -target with [Spec.ref_env] *)
}

type decl =
  | Decl_letrec of (id * term) list  (** let rec .. and ... *)
  | Decl_let of (id * term) list  (** let .. and ... *)
  | Decl_let_match of (pattern * term) list  (** let (pattern) = ... and ... *)
  | Decl_type of term Type.declaration  (** type t = ... and ... *)
  | Decl_type_nonrec of term Type.declaration  (** type nonrec t = ... and ... *)
  | Ext_type of Type.path * (params * term Type.ext_row)  (** type t += ... *)
  | Ext_rebind of Type.constr * Type.path  (** exception A = B *)
  | Include of term  (** include t *)
[@@deriving show]

let ident_stdlib = Ident.create_persistent "Stdlib"

let make_env ?id_env ?tconstrs ?tvar_env ?shadowed_primitive ?mod_typ_env ?vars ?exist_vars
    ?target_locs ?spec () =
  let id_env = Option.default [] id_env in
  let tconstrs = Option.default P.Set.empty tconstrs in
  let tvar_env = Option.default IntMap.empty tvar_env in
  let shadowed_primitive = Option.default [] shadowed_primitive in
  let mod_typ_env = Option.default [] mod_typ_env in
  let vars = Option.default StringSet.empty vars in
  let exist_vars = Option.default [] exist_vars in
  let target_locs = Option.default [] target_locs |> List.map (fun loc -> (loc, ref false)) in
  let stdlib_visited = false in
  let spec = Option.default Spec.init spec in
  {
    id_env;
    tconstrs;
    tvar_env;
    shadowed_primitive;
    mod_typ_env;
    vars;
    exist_vars;
    target_locs;
    stdlib_visited;
    spec;
  }

(* TODO: Fix the usage of stdlib and stdlib' *)
let stdlib = Id.make "Stdlib" Ty.unknown
let stdlib' = Id.make "Stdlib" ()
let add_vars_to_env x env = env.vars <- StringSet.add (Id.name x) env.vars

module Id = struct
  include Id

  let make_orig = make
  let new_var_orig = new_var

  let make ~env ?id ?attr name typ =
    let x = make ?id ?attr name typ in
    add_vars_to_env x env;
    x

  let new_var ~env ?name ?attr typ =
    let x = new_var ?name ?attr typ in
    add_vars_to_env x env;
    x
end

let prim_typs : (P.t * typ) list =
  let open Predef in
  [
    (path_unit, Ty.unit);
    (path_bool, Ty.bool);
    (path_int, Ty.int);
    (path_string, Ty.string);
    (path_bytes, Ty.bytes);
    (path_exn, Ty.exn);
    (path_char, Ty.char);
    (path_float, Ty.float);
  ]

let prim_typ_constr : (P.t * path) list =
  let open Predef in
  [
    (path_list, C.list);
    (P.(Pdot (Pident ident_stdlib, "ref")), C.ref);
    (path_option, C.option);
    (path_array, C.array);
    (path_lazy_t, C.lazy_);
  ]

(* only for [exn]; we may need to fix this function if another primitive extensible type is introduced *)
let assoc_prim_path c path =
  match List.assoc_opt ~eq:P.same path prim_typs with
  | Some (TConstr (s, [])) -> s
  | Some _ -> c
  | None -> c

let prim_exc_fun = [ ("failwith", "Failure"); ("invalid_arg", "Invalid_argument") ]
let add_load_path s = Clflags.include_dirs := s :: !Clflags.include_dirs
let report_error e = Location.report_exception Format.err_formatter e
let name_of_ident = Id.normalize_name -| Ident.name (* TODO: Use Ident.unique_name *)
let name_of_longident id = Format.asprintf "%a" Pprintast.longident id
let name_of_longident_loc loc = name_of_longident loc.Asttypes.txt

let rec path_of_longident (lid : Longident.t) =
  match lid with
  | Longident.Lident s -> Type.LId (tconstr_of_string s)
  | Longident.Ldot (path, s) -> Type.LDot (path_of_longident path, Id.normalize_name s)
  | Longident.Lapply (path1, path2) -> Type.LApp (path_of_longident path1, path_of_longident path2)

let path_of_longident_loc loc = path_of_longident loc.Asttypes.txt
let from_mutable_flag = function Asttypes.Mutable -> Mutable | Asttypes.Immutable -> Immutable

let from_rec_flag = function
  | Asttypes.Recursive -> Recursive
  | Asttypes.Nonrecursive -> Nonrecursive

let is_prim_constr constrs =
  match List.map (fun row -> (string_of_constr row.row_constr, row.row_args)) constrs with
  | [ ("[]", []); ("::", ty :: _) ] -> Some (Ty.list ty)
  | _ -> None

let tconstr_of_string s = Id.make_orig s ()

(* TODO: not to use this function and use Ident.unique_name instead *)
let remove_slash_one s = if String.ends_with s "/1" then String.sub s 0 (String.length s - 2) else s
let tconstr_of_ident ident = tconstr_of_string (name_of_ident ident)

let rec path_of_path (p : P.t) : Type.path =
  match p with
  | Pident ident -> LId (tconstr_of_ident ident)
  | Pdot (p, s) -> LDot (path_of_path p, Id.normalize_name s)
  | Papply (p1, p2) -> LApp (path_of_path p1, path_of_path p2)
  | _ -> [%unsupported]
[@@ocaml.warning "-11"]

(** `typ` is the type of head *)
let rec lid_of env (path : P.t) typ : lid =
  match path with
  | Pident id -> LId (Id.make ~env (Ident.name id) typ)
  | Pdot (path, s) -> LDot (lid_of env path typ, Id.normalize_name s)
  | Papply (_, _) -> assert false
  | _ -> [%unsupported]
[@@ocaml.warning "-11"]

let normalized_path_of ~tenv path =
  let path' = path |> Env.normalize_module_path None tenv in
  let s = path' |> path_of_path |> Path.map_name remove_slash_one |> assoc_prim_path -$- path in
  (P.heads path', s)

(* typ is a type of path's head *)
let normalized_lid_of ?(pre = false) ~env ~tenv path typ =
  path
  |> (not pre) ^> Env.normalize_module_path None tenv
  |> lid_of env -$- typ
  |> Lid.map_name remove_slash_one

let cons_tconstr_env path env =
  let tconstrs = P.Set.add path env.tconstrs in
  { env with tconstrs }

(* BUGGY: If the declaration is in a signature, the entity and the interface of the module may be mismatched *)
(*        Moreover, renamed types may be conflict with the other declaration in the same module *)
let encode_nonrec_type_decl (decls : type_decls) : type_decls list =
  let tcs1 = List.rev_map fst decls in
  let tcs2 =
    List.rev_flatten_map
      (snd |- snd |- get_tconstr_typ |- List.filter_map (fst |- Type.Val._LId))
      decls
  in
  if List.Set.disjoint tcs1 tcs2 then (* WORKAROUND: The else case may be buggy *)
    [ decls ]
  else
    let rec gen_unique n cs =
      let postfix = String.make n '\'' in
      if List.exists (Id.name |- String.ends_with -$- postfix) cs then gen_unique (n + 1) cs
      else List.map (Id.add_name_after postfix) cs
    in
    let cs = gen_unique 1 @@ List.map fst decls in
    let decls1 = List.map2 (fun (_, pty) c' -> (c', pty)) decls cs in
    let decls2 =
      List.map2 (fun (c, (params, _)) c' -> (c, (params, TConstr (LId c', params)))) decls cs
    in
    [ decls1; decls2 ]

let trans_decls env (decls : decl list) : Syntax.declaration list =
  let gen_fresh =
    let bv = List.rev_flatten_map (function Decl_let defs -> List.map fst defs | _ -> []) decls in
    let gen = gen_fresh_name_var bv in
    let rec regen x =
      if StringSet.mem (Id.name x) env.vars then regen (gen x)
      else (
        add_vars_to_env x env;
        x)
    in
    gen |- regen
  in
  let trans decl (map, acc) =
    (* [map] maps shadowed variables to renamed variables *)
    let is_rec = match decl with Decl_letrec _ -> true | _ -> false in
    let rename (decl : Syntax.declaration) map =
      match decl with
      | Decl_let defs when is_rec ->
          let map, defs =
            List.L.fold_right_map defs ~init:map ~f:(fun (f, t) map ->
                let map', f' =
                  match Id.List.decomp_assoc f map with
                  | exception Not_found -> (map, f)
                  | f', map' -> (map', Id.set_typ f' (Id.typ f))
                in
                let map'' = Fmap.(list (snd _LId)) map |> IdMap.of_list in
                let t' = subst_var_map_without_typ map'' t in
                (map', (f', t')))
          in
          (map, [ Syntax.Decl_let defs ])
      | Decl_let defs ->
          let map, defs =
            List.L.fold_right_map defs ~init:map ~f:(fun (f, t) map ->
                let map', f' =
                  match Id.List.decomp_assoc f map with
                  | exception Not_found -> (map, f)
                  | f', map' -> (map', Id.set_typ f' (Id.typ f))
                in
                (map', (f', t)))
          in
          let sbst mp =
            let mp' = Fmap.(list (snd _LId)) mp |> IdMap.of_list in
            Fmap.(list (snd (subst_var_map_without_typ mp')))
          in
          let defs = sbst map defs in
          let must_rename =
            let bvs = List.map fst defs in
            let fvs = List.rev_map_flatten (snd |- get_fv) defs in
            Id.List.Set.(fvs && bvs) |> List.sort_uniq Id.compare
          in
          let b = must_rename <> [] in
          if b then Dbg.printf "must_rename: %a@." Print.(list id) must_rename;
          let map' = List.map (Pair.add_right gen_fresh) must_rename in
          if b then Dbg.printf "       map': %a@." Print.(list (id_typ * id_typ)) map';
          let defs = sbst map' defs in
          (map' @@@ map, [ Syntax.Decl_let defs ])
      | _ -> (map, [ decl ])
    in
    let decls : Syntax.declaration list =
      match decl with
      | Decl_let defs -> [ Decl_let defs ]
      | Decl_letrec defs -> [ Decl_let defs ]
      | Decl_let_match pats ->
          pats
          |> List.flatten_map (fun (p, t) ->
                 let bv = get_bv_pat p in
                 let x = Id.new_var ~env (Type.TTuple bv) in
                 let bindings = List.mapi (fun i y -> (y, Term.(proj i (var x)))) bv in
                 let t' = make_single_match t p Term.(tuple (vars bv)) in
                 (x, t') :: bindings)
          |> List.map (fun def -> Syntax.Decl_let [ def ])
      | Decl_type decls -> [ Decl_type decls ]
      | Decl_type_nonrec decls -> decls |> encode_nonrec_type_decl |> List.map Syntax._Decl_type
      | Ext_type (s, row) -> [ Type_ext (Ext_type (s, row)) ]
      | Ext_rebind (s1, s2) -> [ Type_ext (Ext_rebind (s1, s2)) ]
      | Include t -> [ Include t ]
    in
    let map, declss = List.fold_right_map rename decls map in
    (map, List.flatten declss @ acc)
  in
  let _, decls = List.fold_right trans decls ([], []) in
  decls

let binops ~loc =
  [
    ("=", make_eq);
    ("<>", make_neq);
    ("<", make_lt);
    (">", make_gt);
    ("<=", make_leq);
    (">=", make_geq);
    ("&&", make_and);
    ("||", make_or);
    ("+", make_add);
    ("-", make_sub);
    ("*", make_mul);
    ("/", make_safe_div ?loc);
  ]

let primitives ~env ~loc ~typ =
  let randb = function [ t ] -> make_app (make_rand Ty.bool) [ t ] | _ -> assert false in
  let randi = function
    | [ { desc = Const (Int 0) } ] -> Term.randi
    | [ t ] ->
        let x = Id.new_var ~env ~name:"n" Ty.int in
        [%term
          let x = randi in
          assume (0 <= x && x < `t);
          x]
    | _ -> assert false
  in
  let make_binop (s, f) =
    ( s,
      function
      | [ t1; t2 ] -> f t1 t2
      | [ t1 ] ->
          let x = Id.new_var ~env t1.typ in
          let y = Id.new_var ~env t1.typ in
          let t = f (Term.var x) (Term.var y) in
          [%term (fun x y -> `t) `t1]
      | _ -> assert false )
  in
  let make_exn_fun (fname, cname) =
    ( fname,
      function
      | [ t1 ] ->
          let c = Type.(LDot (LId stdlib', Id.normalize_name cname)) in
          make_raise (make_construct c [ t1 ] Ty.exn) ~typ
      | _ -> assert false )
  in
  [
    ("List.length", function [ t1 ] -> Term.(length t1) | _ -> assert false);
    ("@@", function t1 :: ts -> Term.(t1 @@ ts) | _ -> assert false);
    ("~-", function [ t ] -> Term.(~-t) | _ -> assert false);
    ("not", function [ t ] -> Term.(not t) | _ -> assert false);
    ("fst", function t1 :: ts -> Term.(fst ~typ t1 @@ ts) | _ -> assert false);
    ("snd", function t1 :: ts -> Term.(snd ~typ t1 @@ ts) | _ -> assert false);
    ("raise", function t1 :: ts -> Term.(raise t1 ~typ @@ ts) | _ -> assert false);
    ("ref", function [ t ] -> Term.(ref t) | _ -> assert false);
    ( "read_int",
      function
      | [ t ] ->
          let t' =
            randint_term
            |> Flag.(List.mem !mode [ NonTermination; FairNonTermination ]) ^> add_attr AAbst_under
          in
          Term.(t' @@ [ t ])
      | _ -> assert false );
    ( "!",
      function
      | [] -> assert false
      | t1 :: ts -> (
          match Val'._TConstr t1.typ with
          | Some (c, [ typ ]) when c = C.ref -> Term.deref ~typ t1
          | Some _ when ts = [] -> Term.deref ~typ t1
          | Some _ -> assert false (* TODO: type environment is needed to recover the type *)
          | None -> Term.(!t1 @@ ts)) );
    ( ":=",
      function
      | [ t1; t2 ] -> Term.(t1 := t2)
      | [ t1 ] ->
          let x = Id.new_var ~env t1.typ in
          let y = Id.new_var ~env (ref_typ t1.typ) in
          [%term (fun x y -> x := y) `t1]
      | _ -> assert false );
    ("Random.bool", randb);
    ("Random.int", randi);
    ("Stdlib__random.bool", randb (* for OCaml <=4.12 *));
    ("Stdlib__random.int", randi (* for OCaml <=4.12 *));
    (*
   "open_in", ...;
   "close_in", ...;
   "event", ...;
 *)
  ]
  @ List.map make_binop (binops ~loc)
  @ List.map make_exn_fun prim_exc_fun
  |> Fmap.(list (fst Id.normalize_name))

let check_shadow bvs env =
  let prims = List.map fst (primitives ~env ~loc:None ~typ:Ty.unit) in
  let shadowed = bvs |> List.map Id.name |> List.Set.inter prims in
  let shadowed_primitive = shadowed @ env.shadowed_primitive in
  { env with shadowed_primitive }

let is_primitive ~env x s =
  if List.mem s env.shadowed_primitive then false
  else
    let ss = [ s; Lid.to_string (LDot (LId stdlib, Id.normalize_name s)) ] in
    let ss = if Char.is_uppercase s.[0] then (Id.name stdlib ^ "__" ^ s) :: ss else ss in
    List.mem (Lid.name x) ss

let conv_primitive_app ~env ~loc t ts typ =
  let prim = primitives ~env ~loc:(Some loc) ~typ in
  match t.desc with
  | Var x -> (
      match List.find (is_primitive ~env x -| fst) prim with
      | _, f -> f ts
      | exception Not_found -> make_app t ts)
  | _ -> make_app t ts

let tmp_remove_prefix_target_exn m f =
  match m with
  | None -> f ()
  | Some m ->
      let prefix = Ident.name m ^ "." in
      let removed = !Flag.Method.target_exn |> List.map (String.remove_prefix_if_any ~prefix) in
      Ref.tmp_set Flag.Method.target_exn removed f

type from_types_type_declaration =
  env:env ->
  tenv:Env.t ->
  ?name:Ident.t ->
  ?path:path ->
  Types.type_declaration ->
  env * (term Type.params * typ)

let rec col_typ_def ~env ~tenv ~(from_types_type_declaration : from_types_type_declaration) acc rest
    =
  match rest with
  | [] -> (env, acc)
  | path :: rest' ->
      let _, s = normalized_path_of ~tenv path in
      let env, acc', rest'' =
        if List.mem_assoc s acc then (env, acc, rest')
        else
          match Env.find_type path tenv with
          | exception Not_found -> (env, acc, rest')
          | ty ->
              let env', (params, ty') = from_types_type_declaration ~env ~tenv ~path:s ty in
              let rest'' = P.Set.(elements (diff env'.tconstrs env.tconstrs) @@@ rest') in
              (env', (s, (params, ty')) :: acc, rest'')
      in
      col_typ_def ~env ~tenv ~from_types_type_declaration acc' rest''

let col_typ_def ~env ~tenv ~from_types_type_declaration paths =
  col_typ_def ~env ~tenv ~from_types_type_declaration [] paths

let rec filter_decls ?(acc : (path * (_ * typ)) list = []) tconstrs
    (decls : (path * (_ * typ)) list) =
  let need (p, _) = List.mem ~eq:Path.eq p tconstrs in
  let acc', decls' = List.partition need decls in
  if acc' = [] then acc
  else
    let acc = acc' @@@ acc in
    let tconstrs = acc' |> List.rev_flatten_map (snd |- snd |- get_tconstr_typ) |> List.map fst in
    filter_decls ~acc tconstrs decls'

let normalize_ids =
  Trans.map_var
    (Id.map_name (function
      (* TODO: check conflicts with [opt] & [sth] *)
      | "*opt*" -> "opt"
      | "*sth*" -> "sth"
      | "( *opt* )" -> "opt"
      | "( *sth* )" -> "sth"
      | name when name.[0] = '_' -> "u" ^ name
      | name -> name))

let rec apply_tpackage_constraint add_prefix constr ty =
  match ty with
  | TModSig sgn ->
      let rest, sgn =
        List.L.fold_right sgn ~init:(constr, []) ~f:(fun sig_elem (rest, acc) ->
            match sig_elem with
            | Sig_type decls ->
                let rest', decls' =
                  List.L.fold_right decls ~init:(rest, []) ~f:(fun (t, (params, ty)) (rest, acc) ->
                      match
                        List.partition (fun (path, _) -> path = add_prefix (Type.LId t)) rest
                      with
                      | [], rest -> (rest, (t, (params, ty)) :: acc)
                      | [ (_, ty') ], rest' ->
                          assert (params = []);
                          assert (ty = Ty.abst);
                          (rest', (t, ([], ty')) :: acc)
                      | _ -> invalid_arg "%s" __FUNCTION__)
                in
                (rest', Sig_type decls' :: acc)
            | Sig_value x ->
                let rest1, rest2 =
                  List.partition (fst |- Path.is_prefix (add_prefix (LId (Id.set_typ x ())))) rest
                in
                let add_prefix = add_prefix -| Path.cons x in
                let x' =
                  if is_mod_var x then Id.map_typ (apply_tpackage_constraint add_prefix rest1) x
                  else x
                in
                (rest2, Sig_value x' :: acc)
            | _ -> (rest, sig_elem :: acc))
      in
      assert (rest = []);
      TModSig sgn
  | TModLid _ -> [%unsupported]
  | TConstr _ -> ty
  | _ ->
      Format.eprintf "%a@." Print.typ ty;
      invalid_arg "%s" __FUNCTION__

let apply_tpackage_constraint ?(add_prefix = Fun.id) constr ty =
  if constr = [] then ty else apply_tpackage_constraint add_prefix constr ty

let subst_tconstr_without_copy, subst_tconstr_without_copy_typ =
  let tr = Tr2.make () in
  let tr_typ map ty =
    match ty with TConstr (LId s, []) -> Id.List.assoc_default ty s map | _ -> tr.typ_rec map ty
  in
  tr.typ <- tr_typ;
  (tr.term, tr.typ)

let unify_newtype (ss : string list) ty t =
  if ss = [] then t
  else
    let map = List.map (fun s -> (tconstr_of_string s, !!new_tvar)) ss in
    let t' = subst_tconstr_without_copy map t in
    (try unify ~ignore_non_poly_fail:true ty t'.typ with CannotUnify _ -> [%unsupported]);
    (* TODO: must use env, but we do not have env here, so we have to delay the unification *)
    t'

let make_tunivar_name s = "Tunivar " ^ s

let decomp_tunivar_name s =
  match String.split_on_char ' ' s with
  | [ "Tunivar"; s' ] -> s'
  | _ -> invalid_arg "%s" __FUNCTION__

let make_tunivar ~env var =
  let name = match var with None -> "Tunivar" | Some s -> make_tunivar_name s in
  TConstr (LId (Id.make ~env name ()), [])

let decomp_tunivar = function TConstr (LId x, []) -> x | _ -> invalid_arg "%s" __FUNCTION__

let assoc_tvar (env : env) (ty : type_expr) =
  if not (Btype.is_Tvar ty) then [%invalid_arg];
  let id = Types.get_id ty in
  match IntMap.find_opt id env.tvar_env with
  | None ->
      let ty = if Types.get_level ty = Btype.generic_level then !!new_tvar else !!new_tvar_weak in
      let tvar_env = IntMap.add id ty env.tvar_env in
      ({ env with tvar_env }, ty)
  | Some ty -> (env, ty)

let add_tconstr ~tenv ty_desc env =
  match ty_desc with
  | Tconstr (path, _, _) ->
      let path' = Env.normalize_module_path None tenv path in
      cons_tconstr_env path' env
  | _ -> env

let is_exc_constr (cstr_desc : Types.constructor_description) =
  match Types.get_desc cstr_desc.cstr_res with
  | Tconstr (path, _, _) -> path = Predef.path_exn
  | _ -> false

let from_list ~f ~env xs = List.fold_right_map (fun x env -> f ~env x) xs env

let from_option ~f ~env x =
  match x with
  | None -> (env, None)
  | Some y ->
      let env, y = f ~env y in
      (env, Some y)

module Cache = struct
  let mod_type :
      found:(typ -> env * typ) ->
      Types.module_type ->
      result_of:(env * typ -> typ) ->
      (Types.module_type -> env * typ) ->
      env * typ =
    Memoize.create_gen 100 ~key_of:Fun.id

  let mod_type_of_ident :
      found:(Ident.t option * typ -> env * typ) ->
      key_of:(Ident.t -> string) ->
      Ident.t ->
      result_of:(env * typ -> Ident.t option * typ) ->
      (string -> env * typ) ->
      env * typ =
    Memoize.create_gen 100
end

exception PatternExcep of (env * pattern)

let expand_if_arrow ~tenv ty =
  let ty' = Ctype.expand_head_opt tenv ty in
  match Types.get_desc ty' with Tarrow _ -> ty' | _ -> ty

let add_mod_typ m_orig m ty env =
  let eq = Eq.on ~eq:Ident.equal fst in
  let mod_typ_env = List.cons_unique ~eq (m_orig, (m, ty)) env.mod_typ_env in
  { env with mod_typ_env }

let rec add_mod_typ_ident ~env ~tenv id =
  if Ident.global id && Char.is_uppercase (Ident.name id).[0] (* WORKAROUND *) then
    if env.stdlib_visited && id = ident_stdlib then env
    else
      let stdlib_visited = env.stdlib_visited || id = ident_stdlib in
      let env = { env with stdlib_visited } in
      fst @@ module_type_of_ident ~env ~tenv id
  else env

and normalized_path_of' ~env ~tenv path =
  let heads, path' = normalized_path_of ~tenv path in
  let env = List.fold_left (fun env m -> add_mod_typ_ident ~env ~tenv m) env heads in
  (env, path')

and from_constructor_description ~env ~tenv desc =
  match desc.cstr_tag with
  | Cstr_constant _ -> (env, lid_of_string desc.cstr_name)
  | Cstr_block _ -> (env, lid_of_string desc.cstr_name)
  | Cstr_extension (path, _) -> normalized_path_of' ~env ~tenv path
  | Cstr_unboxed -> (env, lid_of_string desc.cstr_name)

and from_constructor_description_normalize ~env ~tenv desc =
  let env, name = from_constructor_description ~env ~tenv desc in
  match Types.get_desc desc.cstr_res with
  | Tconstr (path, _, _) ->
      ( env,
        match (Env.find_type path tenv).type_kind with
        | Type_variant _ as kind ->
            (* Really need? *)
            let constrs = decomp_Type_variant kind in
            let aux { cd_id } =
              let name' = name_of_ident cd_id in
              if name' = Path.name name then Some (lid_of_string name') else None
            in
            List.find_map_default aux name constrs
        | _ -> name )
  | _ -> assert false

and from_types_label_declaration ~env ~tenv { ld_id; ld_mutable; ld_type } =
  let s = label_of_string (name_of_ident ld_id) in
  let flag = from_mutable_flag ld_mutable in
  let env, ty = from_type_expr ~env ~tenv ld_type in
  (env, (s, (flag, ty)))

and from_types_label_declarations ~env ~tenv decls =
  List.fold_right_map (fun decl env -> from_types_label_declaration ~env ~tenv decl) decls env

(** [name] is just for debug *)
and from_types_type_declaration ~env ~tenv ?name ?path (decl : Types.type_declaration) :
    env * (typ list * typ) =
  ignore name;
  (*
    let name = Option.default_delayed (fun () -> Ident.create_local "t") name in
    Dbg_orig.printf "decl: %a@." (Printtyp.type_declaration name) decl;
   *)
  let from_ty = from_type_expr ~visited:[] ~tenv in
  let env, params_rev, constraints, _ =
    List.L.fold_left decl.type_params ~init:(env, [], [], [])
      ~f:(fun (env, params_rev, constraints, tys) ty ->
        if List.exists (eq_type ty) tys || not (Btype.is_Tvar ty) then
          let env, ty' = from_ty ~env ty in
          let p = new_tvar () in
          (env, p :: params_rev, (p, ty') :: constraints, tys)
        else
          let env, p = assoc_tvar env ty in
          (env, p :: params_rev, constraints, ty :: tys))
  in
  let params = List.rev params_rev in
  let env, ty =
    match
      match decl.type_manifest with
      | Some ty -> (
          let env, ty = from_ty ~env ty in
          match path with Some p when ty = TConstr (p, params) -> None | _ -> Some (env, ty))
      | None -> None
    with
    | Some (env, ty) -> (env, ty)
    | None -> (
        match decl.type_kind with
        | Type_abstract -> (env, Ty.abst)
        | Type_variant _ as kind ->
            let constrs = decomp_Type_variant kind in
            let env, constrs =
              from_list constrs ~env ~f:(fun ~env { cd_id; cd_args; cd_res } ->
                  let row_constr = constr_of_string (name_of_ident cd_id) in
                  let env, row_args = from_types_constructor_arguments ~env ~tenv cd_args in
                  let env, row_ret = from_option ~f:from_ty ~env cd_res in
                  (env, { row_constr; row_args; row_ret }))
            in
            let ty' = Option.default (TVariant (VNonPoly, constrs)) @@ is_prim_constr constrs in
            (env, ty')
        | Type_record (fields, _) ->
            let env, fields' = from_types_label_declarations ~env ~tenv fields in
            (env, TRecord fields')
        | Type_open -> (env, TOpen))
  in
  (env, (params, _TConstraint ty constraints))

and from_row_desc ~env ~tenv ~visited row_desc =
  let from_ty = from_type_expr ~tenv ~visited in
  let (Row row) = row_repr row_desc in
  let closed = row.closed in
  let tvar = match Types.get_desc row.more with Tvar (Some _s) -> Some () | _ -> None in
  let env, rps =
    from_list ~env row.fields ~f:(fun ~env (s, field) ->
        let row_constr = label_of_string s in
        let env, r =
          match row_field_repr field with
          | Rpresent None -> (env, Some ([], true))
          | Rpresent (Some type_expr) ->
              let env, ty = from_ty ~env type_expr in
              let tys = match ty with TTuple xs -> List.map Id.typ xs | ty -> [ ty ] in
              (env, Some (tys, true))
          | Reither _ as field -> (
              match decomp_Reither field with
              | true, [] -> (env, Some ([], false))
              | true, _ | _, [] -> assert false
              | false, [ ty ] ->
                  let env, ty = from_ty ~env ty in
                  (env, Some ([ ty ], false))
              | false, tys ->
                  let env, tys = from_list ~f:(from_type_expr ~visited ~tenv) ~env tys in
                  let ty = TConstr (C.conj, tys) in
                  (env, Some ([ ty ], false)))
          | Rabsent -> (env, None)
        in
        ( env,
          Option.map
            (fun (row_args, present) -> ({ row_constr; row_args; row_ret = None }, present))
            r ))
  in
  let rps = List.filter_map Fun.id rps in
  let lower =
    if List.for_all snd rps then None
    else
      rps
      |> List.filter_map (fun (row, present) -> if present then Some row.row_constr else None)
      |> List.sort compare
      |> Option.some
  in
  let rows = rps |> List.map fst |> List.sort (Compare.on row_constr) in
  (env, (closed, tvar, lower, rows))

and from_type_expr ?(visited = []) ~env ~tenv ty0 : env * typ =
  (*
  Format.printf "ty0: %a@." Printtyp.type_expr ty0;
  Format.printf "ty0: %a@.@." Printtyp.raw_type_expr ty0;
*)
  let id = Types.get_id ty0 in
  match List.assoc_opt id visited with
  | Some (r, b) ->
      b := true;
      (env, r)
  | None ->
      let b = ref false in
      let rty = !!new_tvar in
      let visited = (id, (rty, b)) :: visited in
      let from = from_type_expr ~tenv ~visited in
      let typ = Btype.proxy ty0 in
      let env = add_tconstr ~tenv (Types.get_desc typ) env in
      let typ = if Btype.is_Tvar typ && not (Btype.is_Tvar ty0) then ty0 else typ in
      let ty = expand_if_arrow ~tenv typ in
      let env, r =
        match Types.get_desc ty with
        | Tvar _ -> assoc_tvar env typ
        | Tarrow (_, typ1, typ2, _) ->
            let env, typ1' = from ~env typ1 in
            let env, typ2' = from ~env typ2 in
            let x = Id.new_var ~env typ1' in
            (env, TFun (x, typ2'))
        | Ttuple typs ->
            let env, tys' = from_list ~f:from ~env typs in
            (env, make_ttuple tys')
        | Tconstr (Pident x, typs, _) when (Ident.name x).[0] = '$' ->
            assert (typs = []);
            let name = Ident.name x in
            let env, tvar =
              match List.assoc_opt id env.exist_vars with
              | Some tv -> (env, tv)
              | None ->
                  let tv = (true, ref None, 0) in
                  let exist_vars = (id, tv) :: env.exist_vars in
                  ({ env with exist_vars }, tv)
            in
            (env, _TAttr [ TAExistential name ] @@ TVar tvar)
        | Tconstr (path, typs, _) ->
            let env, ty =
              match List.assoc_opt ~eq:P.same path prim_typs with
              | None ->
                  let env, c = normalized_path_of' ~env ~tenv path in
                  let c' = List.assoc_default c path prim_typ_constr in
                  let env, tys = from_list ~f:from ~env typs in
                  (env, TConstr (c', tys))
              | Some ty ->
                  assert (typs = []);
                  (env, ty)
            in
            (env, ty)
        | Tobject _ ->
            (* TODO *)
            (env, TConstr (C.obj, []))
        | Tfield _ ->
            (* TODO *)
            (env, TConstr (C.obj, []))
        | Tnil ->
            (* TODO *)
            (env, TConstr (C.obj, []))
        | Tlink ty -> from ~env ty
        | Tsubst _ -> unsupported "Tsubst"
        | Tvariant row_desc ->
            let env, (closed, tvar, lower, constrs) = from_row_desc ~env ~tenv ~visited row_desc in
            let constrs =
              constrs
              |> List.map (fun row ->
                     let row_args =
                       match row.row_args with [ TTuple xs ] -> List.map Id.typ xs | tys -> tys
                     in
                     { row with row_args })
            in
            (env, TVariant (VPoly { closed; tvar; lower }, constrs))
        | Tunivar s -> (env, make_tunivar ~env s)
        | Tpoly (typ, []) -> from ~env typ
        | Tpoly (typ, typs) ->
            let env, ty = from ~env typ in
            let env, tys = from_list ~f:from ~env typs in
            let vars =
              try List.map decomp_tunivar tys with Invalid_argument _ -> unsupported "Tpoly"
            in
            let refs = List.map (fun _ -> ref None) vars in
            let map = List.map2 (fun x r -> (x, TVar (false, r, 0))) vars refs in
            let ty' = subst_tconstr_without_copy_typ map ty in
            (env, TPoly (refs, ty'))
        | Tpackage _ as desc ->
            let path, idtys = decomp_Tpackage desc in
            let env, ty =
              match Env.find_modtype path tenv with
              | mtd -> from_modtype_declaration ~env ~tenv mtd
              | exception Not_found ->
                  let env, path' = normalized_path_of' ~env ~tenv path in
                  (env, TConstr (path', []))
            in
            let env, constr =
              from_list idtys ~env ~f:(fun ~env (id, ty) ->
                  let t = path_of_longident id in
                  let env, typ = from ~env ty in
                  (env, (t, typ)))
            in
            (env, TPackage (apply_tpackage_constraint constr ty))
      in
      let r = if !b then Ty.attr (TARec (Type.ValE._TVar rty)) r else r in
      (env, r)

and from_core_type ~env ~tenv (ty : core_type) = from_type_expr ~env ~tenv ty.ctyp_type

and take_arg_types ~env ~tenv ty n =
  if n = 0 then (env, [])
  else
    match ty |> Ctype.correct_levels |> Ctype.expand_head tenv |> Types.get_desc with
    | Tarrow (_, ty1, ty2, _) ->
        let env, ty = from_type_expr ~env ~tenv ty1 in
        let env, tys = take_arg_types ~env ~tenv ty2 (n - 1) in
        (env, ty :: tys)
    | _ -> invalid_arg "%s@." __FUNCTION__

and from_typedtree_label_declaration ~env ~tenv
    ({ ld_id; ld_mutable; ld_type } : Typedtree.label_declaration) =
  let s = label_of_string (name_of_ident ld_id) in
  let flag = from_mutable_flag ld_mutable in
  let env, ty = from_type_expr ~env ~tenv ld_type.ctyp_type in
  (env, (s, (flag, ty)))

and from_typedtree_label_declarations ~env ~tenv (fields : Typedtree.label_declaration list) =
  from_list ~f:(from_typedtree_label_declaration ~tenv) ~env fields

and from_types_constructor_arguments ~tenv ~env (cd_args : Types.constructor_arguments) =
  match cd_args with
  | Cstr_tuple args -> from_list ~f:(from_type_expr ~visited:[] ~tenv) ~env args
  | Cstr_record fields ->
      let env, fields' = from_types_label_declarations ~env ~tenv fields in
      (env, [ TRecord fields' ])

and from_typedtree_constructor_arguments ~tenv ~env (cd_args : Typedtree.constructor_arguments) =
  match cd_args with
  | Cstr_tuple args ->
      from_list ~f:(from_type_expr ~visited:[] ~tenv) ~env
      @@ List.map (fun arg -> arg.ctyp_type) args
  | Cstr_record fields ->
      let env, fields' = from_typedtree_label_declarations ~env ~tenv fields in
      (env, [ TRecord fields' ])

and from_typedtree_type_declaration ~tenv ~env (decl : Typedtree.type_declaration) :
    env * (tconstr * (typ list * typ)) =
  let c = tconstr_of_ident decl.typ_id in
  let env, ty = from_types_type_declaration ~env ~tenv decl.typ_type in
  (env, (c, ty))

and from_ident x typ =
  let id = 0 in
  Id.make ~id (name_of_ident x) typ

and from_ident_path ~env ~tenv (path : P.t) mk_ty =
  let path' = Env.normalize_module_path None tenv path in
  let head = P.head path' in
  match path' with
  | Pident _id ->
      let env, typ = mk_ty env in
      (* This trick can be removed if memoization/caching is implemented appropriately *)
      let lid = normalized_lid_of ~env ~pre:true ~tenv path' typ in
      let lid =
        match lid with
        | LId x -> (
            match List.find_opt (Id.name |- ( = ) (Id.name x)) env.id_env with
            | Some x -> LId (Id.set_typ x typ)
            | None -> lid)
        | _ -> lid
      in
      (env, lid)
  | Pdot _ ->
      let env, typ = module_type_of_ident ~env ~tenv head in
      (env, normalized_lid_of ~env ~pre:true ~tenv path' typ)
  | Papply _ -> assert false
  | _ -> [%unsupported]
[@@ocaml.warning "-11"]

and module_type_of_ident ~env ~tenv m =
  let m' = from_ident ~env m Ty.unit in
  let ty_global () = TModLid (LId (Id.set_typ m' ())) in
  if Ident.global m && List.mem_assoc ~eq:Ident.equal m env.mod_typ_env then (env, !!ty_global)
  else
    let env, ty =
      let found (_, r) = (env, r) in
      let key_of = Ident.unique_name in
      let result_of (_, r) = (None, r) in
      Cache.mod_type_of_ident ~found ~key_of m ~result_of (fun _ ->
          match Env.find_module (Pident m) tenv with
          | decl -> from_types_module_type ~env ~tenv decl.md_type
          | exception Not_found ->
              (* This module is not used? *)
              Format.eprintf "Not found: %s@." (Ident.name m);
              (env, TModSig empty_signature))
    in
    if Ident.global m then (add_mod_typ m m' ty env, !!ty_global) else (env, ty)

and get_label_name prefix label = prefix ^ label.lbl_name

and from_pattern_desc : type k. env:env -> tenv:Env.t -> k pattern_desc' -> typ -> env * pat_desc =
 fun ~env ~tenv desc typ ->
  match desc with
  | Tpat_any -> (env, PAny)
  | Tpat_var (x, _) -> (env, PVar (from_ident ~env x typ))
  | Tpat_alias ({ pat_desc = Tpat_any }, x, _) -> (env, PVar (from_ident ~env x typ))
  | Tpat_alias (p, x, _) ->
      let env, p' = from_pattern ~env p in
      (env, PAlias (p', from_ident ~env x typ))
  | Tpat_constant (Const_int n) -> (env, PConst (make (Const (Int n)) typ ~attr:const_attr))
  | Tpat_constant (Const_char c) -> (env, PConst (make (Const (Char c)) typ ~attr:const_attr))
  | Tpat_constant (Const_string _ as c) ->
      let s = decomp_Const_string c in
      (env, PConst (make (Const (String s)) typ ~attr:const_attr))
  | Tpat_constant (Const_float s) ->
      (env, PConst (make (Const (Float (float_of_string s))) typ ~attr:const_attr))
  | Tpat_constant (Const_int32 n) -> (env, PConst (make (Const (Int32 n)) typ ~attr:const_attr))
  | Tpat_constant (Const_int64 n) -> (env, PConst (make (Const (Int64 n)) typ ~attr:const_attr))
  | Tpat_constant (Const_nativeint n) ->
      (env, PConst (make (Const (Nativeint n)) typ ~attr:const_attr))
  | Tpat_tuple ps ->
      let env, ps' = from_list ~f:from_pattern ~env ps in
      (env, PTuple ps')
  | Tpat_construct _ -> (
      let loc, cstr_desc, ps = decomp_Tpat_construct desc in
      match (loc.txt, name_of_longident_loc loc, ps) with
      | Longident.(Ldot (Lident "*predef*", "None")), _, [] ->
          (env, PNone (* TODO: fix the following four patters *))
      | Longident.(Ldot (Lident "*predef*", "Some")), _, [ p ] ->
          let env, p' = from_pattern ~env p in
          (env, PSome p')
      | _, "None", [] -> (env, PNone)
      | _, "Some", [ p ] ->
          let env, p' = from_pattern ~env p in
          (env, PSome p')
      | _, "()", [] -> (env, PConst unit_term)
      | _, "[]", [] -> (env, PNil)
      | _, "(::)", [ p1; p2 ] ->
          let env, p1' = from_pattern ~env p1 in
          let env, p2' = from_pattern ~env p2 in
          (env, PCons (p1', p2'))
      | _, _, [] when typ = Ty.bool -> (
          match name_of_longident_loc loc with
          | "true" -> (env, PConst Term.true_)
          | "false" -> (env, PConst Term.false_)
          | _ -> unsupported "Shadow bool type")
      | _ ->
          let env, ps' = from_list ~f:from_pattern ~env ps in
          let env, c = from_constructor_description_normalize ~env ~tenv cstr_desc in
          (env, PConstr (false, c, ps')))
  | Tpat_variant (name, pat, _) ->
      let env, ps =
        match pat with
        | None -> (env, [])
        | Some pat' ->
            let env, p = from_pattern ~env pat' in
            let ps = match p with { pat_desc = PTuple ps } -> ps | pat -> [ pat ] in
            (env, ps)
      in
      (env, PConstr (true, lid_of_string name, ps))
  | Tpat_record (ps, _) ->
      let env, ps =
        from_list ps ~env ~f:(fun ~env (_, label, p) ->
            let s = label_of_string label.lbl_name in
            let env, p' = from_pattern ~env p in
            (env, (s, p')))
      in
      (env, PRecord ps)
  | Tpat_array ps ->
      let env, ps' = from_list ~f:from_pattern ~env ps in
      let x = Id.new_var ~env typ in
      let elem_typ = List.get @@ snd @@ Type.ValE._TConstr typ in
      let list_of_array = PrimId.list_of_array elem_typ in
      let t = [%term list_of_array x] in
      (env, PEval (x, t, Pat.list ~elem_typ ps'))
  | Tpat_or (p1, p2, _) ->
      let env, p1' = from_pattern ~env p1 in
      let env, p2' = from_pattern ~env p2 in
      (env, POr (p1', p2'))
  | Tpat_lazy p ->
      let env, p' = from_pattern ~env p in
      (env, PLazy p')
  | _ when is_Tpat_value desc -> assert false
  | Tpat_exception pat -> raise (PatternExcep (from_pattern ~env pat))
  | _ -> assert false
[@@ocaml.warning "-11"]

and from_pattern : type k. env:env -> k pattern' -> env * pattern =
 fun ~env ({ pat_desc = desc; pat_loc = _; pat_type = typ; pat_env = tenv } as pat) ->
  let env, pat_typ = from_type_expr ~env ~tenv typ in
  let env, pat_desc =
    if is_Tpat_value desc then
      let p = decomp_Tpat_value pat desc in
      from_pattern_desc ~env ~tenv p.Typedtree.pat_desc pat_typ
    else from_pattern_desc ~env ~tenv desc pat_typ
  in
  (env, make_pattern pat_desc pat_typ)

and from_value_kind = function
  | Types.Val_reg ->
      Format.eprintf "Val_reg@.";
      assert false
  | Types.Val_prim prim_desc -> Id.new_var prim_desc.Primitive.prim_name
  | Types.Val_ivar _ ->
      Format.eprintf "Val_ivar@.";
      assert false
  | Types.Val_self _ ->
      Format.eprintf "Val_self@.";
      assert false
  | Types.Val_anc _ ->
      Format.eprintf "Val_anc@.";
      assert false
  | v when is_Val_unbound v ->
      Format.eprintf "Val_unbound@.";
      assert false
  | _ -> assert false
[@@ocaml.warning "-11"]

and from_constant = function
  | Const_int n -> Int n
  | Const_char c -> Char c
  | Const_string _ as c -> String (decomp_Const_string c)
  | Const_float s -> Float (float_of_string s)
  | Const_int32 n -> Int32 n
  | Const_int64 n -> Int64 n
  | Const_nativeint n -> Nativeint n

and is_var_case case =
  match case with
  | { c_lhs = { pat_desc = Tpat_var _ }; c_guard = None } -> true
  | { c_lhs = { pat_desc = Tpat_alias ({ pat_desc = Tpat_any }, _, _) }; c_guard = None } -> true
  | _ -> false

(* TODO: fix to return attribute? *)
and from_attribute { Parsetree.attr_name; attr_payload } =
  if attr_name.txt = "mochi" then
    match attr_payload with
    | PStr [ { pstr_desc = Pstr_eval ({ pexp_desc = Pexp_ident x }, _) } ]
      when name_of_longident_loc x = "target" ->
        Some ()
    | PStr _ -> None
    | PSig _ -> None
    | PTyp _ -> None
    | PPat _ -> None
  else None

and from_attributes attrs = List.filter_map from_attribute attrs

and from_let_rec ~env pats =
  let env, ps = from_list ~f:(fun ~env { vb_pat } -> from_pattern ~env vb_pat) ~env pats in
  let xs =
    List.L.map ps ~f:(fun p ->
        match p.pat_desc with
        | PVar x -> x
        | _ -> failwith "Only variables are allowed as left-hand side of 'let rec'")
  in
  let env = { env with id_env = xs @@@ env.id_env } in
  let env = check_shadow xs env in
  let env, ts = from_list pats ~env ~f:(fun ~env { vb_expr } -> from_expression ~env vb_expr) in
  (env, List.combine xs ts)

and from_expression ~env { exp_desc; exp_loc; exp_type; exp_env = tenv; exp_attributes; exp_extra }
    : env * term =
  let env, typ = from_type_expr ~env ~tenv exp_type in
  let newtypes =
    List.filter_map (function Texp_newtype s, _, _ -> Some s | _ -> None) exp_extra
  in
  let env, t =
    match exp_desc with
    | Texp_ident (path, _, _) ->
        let env, lid = from_ident_path ~env ~tenv path (fun env -> (env, typ)) in
        if !Flag.Print.id_loc <> "" && String.exists (Lid.to_string lid) !Flag.Print.id_loc then
          Format.fprintf !Flag.Print.target "Found variable %a: %a@." Print.lid lid Print.location
            exp_loc;
        let t = Term.var_lid ~typ lid in
        let t' =
          let s = Format.asprintf "%a" Print.location exp_loc in
          if
            Ident.global (List.hd @@ P.heads path)
            && List.exists (fst |- Id.name |- ( = ) (Lid.to_string lid)) env.spec.ref_env
            && (!Flag.Method.targets = [] || List.exists (fst |- String.exists s) env.target_locs)
          then (
            if !Flag.Print.target_ext_loc then
              if !!Mochi_util.is_silent then Format.fprintf !Flag.Print.target "%s@." s
              else Format.fprintf !Flag.Print.target "Found target: %a, %s@." Print.lid lid s;
            List.iter (fun (loc, r) -> if String.exists s loc then r := true) env.target_locs;
            add_attr ATarget t)
          else t
        in
        (env, t')
    | Texp_constant c -> (env, make (Const (from_constant c)) typ ~attr:const_attr)
    | Texp_let (_, [ { vb_pat; vb_expr } ], e2)
      when (function Tpat_var _ -> false | _ -> true) vb_pat.pat_desc ->
        let shadowed_primitive = env.shadowed_primitive in
        let env, p' = from_pattern ~env vb_pat in
        let env, t1 = from_expression ~env vb_expr in
        let env, t2 =
          let env = check_shadow (get_bv_pat p') env in
          from_expression ~env e2
        in
        ({ env with shadowed_primitive }, make_single_match t1 p' t2)
    | Texp_let (Recursive, pats, e) ->
        let shadowed_primitive = env.shadowed_primitive in
        let env, bindings = from_let_rec ~env pats in
        let env, t = from_expression ~env e in
        ({ env with shadowed_primitive }, make_let bindings t)
    | Texp_let (Nonrecursive, pats, e) ->
        let shadowed_primitive = env.shadowed_primitive in
        let env, (ps, ts) =
          let env, psts =
            from_list ~env pats ~f:(fun ~env { vb_pat; vb_expr } ->
                let env, pat = from_pattern ~env vb_pat in
                let env, t = from_expression ~env vb_expr in
                (env, (pat, t)))
          in
          (env, List.split psts)
        in
        let ps, ts =
          if Flag.EvalStrategy.tuple_left_to_right then (ps, ts) else (List.rev ps, List.rev ts)
        in
        let p = make_ptuple ps in
        let t1 = make_tuple ts in
        let env, t2 =
          let env =
            let bvs = get_bv_pat p in
            { env with id_env = bvs @ env.id_env } |> check_shadow bvs
          in
          from_expression ~env e
        in
        ({ env with shadowed_primitive }, make_match t1 [ (p, t2) ])
    | Texp_function { cases = [ case ]; partial = Total } when is_var_case case -> (
        let env, (p, t) = from_case ~env case in
        match p with { pat_desc = PVar x } -> (env, make_fun x t) | _ -> assert false)
    | Texp_function { cases; partial } ->
        let { Id.typ = ty_arg }, ty_ret = Type.ValE._TFun typ in
        let env, pats = from_list ~f:from_case ~env cases in
        (env, make_function ~partial:(partial = Partial) ~loc:exp_loc ~ty_arg ~ty_ret pats)
    | Texp_apply (e, args) ->
        (* TODO: fix the evaluation when `xs <> []` *)
        let env, t = from_expression ~env e in
        let env, xs, ts =
          let env, tys =
            if List.exists (snd |- ( = ) None) args then
              (* Minor optimization *)
              take_arg_types ~env ~tenv:e.exp_env e.exp_type (List.length args)
            else (env, List.map (Fun.const Ty.unit) args (* Dummy *))
          in
          List.L.fold_right2 args tys ~init:(env, [], []) ~f:(fun (label, arg) ty (env, xs, ts) ->
              let (env, t), xs =
                match arg with
                | Some e ->
                    let e =
                      match label with
                      | Optional _ ->
                          { e with exp_env = tenv }
                          (* I don't know why, but the type environment of e is not appropriate for this context *)
                      | _ -> e
                    in
                    (from_expression ~env e, xs)
                | None ->
                    let x = Id.new_var ~env ty in
                    ((env, Term.var x), x :: xs)
              in
              (env, xs, t :: ts))
        in
        (env, Term.funs xs @@ conv_primitive_app ~env ~loc:exp_loc t ts typ)
    | Texp_match (e, pats, tp) ->
        let env, t = from_expression ~env e in
        let env, pats = from_list ~f:from_case_with_excep ~env pats in
        let pats, pats_exn =
          List.partition_map
            (fun (is_exn, p, t) -> if is_exn then Right (p, t) else Left (p, t))
            pats
        in
        let pats =
          match tp with
          | Total -> pats
          | Partial -> pats @ [ (make_pvar (Id.new_var ~env t.typ), make_fail ~loc:exp_loc typ) ]
        in
        let t =
          if pats_exn = [] then make_match ~typ t pats
          else
            let x = Id.new_var ~env @@ make_either_ty t.typ typ in
            assert (pats <> []);
            let e = Id.new_var ~env ~name:"e" Ty.exn in
            let pats_exn = List.map (Pair.map_snd (make_right t.typ)) pats_exn in
            Term.(
              let_
                [ (x, try_ (left t typ) e pats_exn) ]
                (if_ (is_left (var x)) (match_ ~typ (get_left (var x)) pats) (get_right (var x))))
        in
        (env, t)
    | Texp_try (e, pats) ->
        let x = Id.new_var ~env ~name:"e" Ty.exn in
        let env, pats' = from_list ~f:from_case ~env pats in
        let pats'' = pats' @ [ (make_pany Ty.exn, [%term raise x]) ] in
        let env, t = from_expression ~env e in
        (env, Term.trywith t x pats'')
    | Texp_tuple es ->
        let env, ts = from_list ~f:from_expression ~env es in
        (env, Term.tuple ts)
    | Texp_construct (loc, desc, es) ->
        let env, ts = from_list ~f:from_expression ~env es in
        let env, desc =
          match (name_of_longident_loc loc, ts) with
          | "()", [] -> (env, Const Unit)
          | "true", [] -> (env, Const True)
          | "false", [] -> (env, Const False)
          | "[]", [] -> (env, Nil)
          | "(::)", [ t1; t2 ] -> (env, Cons (t1, t2))
          | "None", [] -> (env, TNone)
          | "Some", [ t ] -> (env, TSome t)
          | _ ->
              let env, c = from_constructor_description_normalize ~env ~tenv desc in
              (env, Constr (false, c, ts))
        in
        let attr = make_attr ts in
        (env, make ~attr desc typ)
    | Texp_variant (name, expr) ->
        let env, ts =
          match expr with
          | None -> (env, [])
          | Some expr' ->
              let env, t = from_expression ~env expr' in
              let ts = match t with { desc = Tuple ts } -> ts | _ -> [ t ] in
              (env, ts)
        in
        (env, make (Constr (true, lid_of_string name, ts)) typ)
    | Texp_record { fields; extended_expression = None } ->
        let env, fields'' =
          fields
          |> Array.to_list
          |> List.sort (Compare.on (fun (lbl, _) -> lbl.lbl_pos))
          |> from_list ~env ~f:(fun ~env (lbl, lbl_def) ->
                 match lbl_def with
                 | Overridden (_, e) ->
                     let name = label_of_string lbl.lbl_name in
                     let env, t = from_expression ~env e in
                     (env, (name, t))
                 | _ -> assert false)
        in
        (env, make (Record fields'') typ)
    | Texp_record { fields; extended_expression = Some init } ->
        let labels = Array.to_list (fst fields.(0)).lbl_all in
        let env, t = from_expression ~env init in
        let r = new_var_of_term t in
        let env, fields' =
          from_list ~env labels ~f:(fun ~env lbl ->
              let _, e = Array.find (fun (lbl', _) -> lbl.lbl_name = lbl'.lbl_name) fields in
              let label = label_of_string lbl.lbl_name in
              let env, t =
                match e with
                | Overridden (_, e) -> from_expression ~env e
                | Kept _ ->
                    let env, ty = from_type_expr ~env ~tenv lbl.lbl_arg in
                    (env, Term.(field ~ty (var r) label))
              in
              (env, (label, t)))
        in
        (env, make_let_subst_if_var r t @@ make (Record fields') typ)
    | Texp_field (e, _, lbl) ->
        let label = label_of_string lbl.lbl_name in
        let env, t = from_expression ~env e in
        (env, make (Field (t, label)) typ)
    | Texp_setfield (e1, _, lbl, e2) ->
        let label = label_of_string lbl.lbl_name in
        let env, t1 = from_expression ~env e1 in
        let env, t2 = from_expression ~env e2 in
        (env, make (SetField (t1, label, t2)) typ)
    | Texp_array es ->
        let env, ts = from_list ~f:from_expression ~env es in
        let typ' =
          match ts with
          | t :: _ -> t.typ
          | [] -> ( try array_typ typ with Invalid_argument _ -> unsupported "Texp_array")
        in
        let f = PrimId.array_of_list typ' in
        (env, Term.(var f @ [ list ~typ:typ' ts ]))
    | Texp_ifthenelse (e1, e2, e3) ->
        let env, t1 = from_expression ~env e1 in
        let env, t2 = from_expression ~env e2 in
        let env, t3 =
          match e3 with None -> (env, unit_term) | Some e3 -> from_expression ~env e3
        in
        (env, make_if ~typ t1 t2 t3)
    | Texp_sequence (e1, e2) ->
        let env, t1 = from_expression ~env e1 in
        let env, t2 = from_expression ~env e2 in
        (env, make_seq t1 t2)
    | Texp_while (e1, e2) ->
        let env, t1 = from_expression ~env e1 in
        let env, t2 = from_expression ~env e2 in
        let x = Id.new_var ~env Ty.unit in
        let f = Id.new_var ~env ~name:"while" Ty.(fun_ unit unit) in
        let t2' =
          [%term
            if `t1 then (
              `t2;
              f ())]
        in
        ( env,
          [%term
            let f x = `t2' in
            f ()] )
    | Texp_for (x, _, e1, e2, dir, e3) ->
        let env, t1 = from_expression ~env e1 in
        let env, t2 = from_expression ~env e2 in
        let env, t3 = from_expression ~env e3 in
        let x' = from_ident ~env x Ty.int in
        if can_unify t3.typ Ty.unit then Type_util.unify t3.typ Ty.unit
        else unsupported "The body of a for-expression must have type unit";
        let f = Id.new_var ~env ~name:"for" Ty.(TFun (Id.new_var ~env ~name:"i" int, unit)) in
        let init = Id.new_var ~env ~name:"init" Ty.int in
        let last = Id.new_var ~env ~name:"last" Ty.int in
        let t =
          if !Flag.Method.abst_for_loop then
            let cond =
              match dir with Upto -> [%term init <= last] | Downto -> [%term init >= last]
            in
            let t3' =
              match dir with
              | Upto ->
                  [%term
                    assume (init <= x' && x' <= last);
                    `t3]
              | Downto ->
                  [%term
                    assume (last <= x' && x' <= init);
                    `t3]
            in
            [%term
              if `cond then
                let x' = randi in
                `t3']
          else
            let t31 = match dir with Upto -> [%term x' <= last] | Downto -> [%term x' >= last] in
            let t32 =
              let x'' = match dir with Upto -> [%term x' + 1] | Downto -> [%term x' - 1] in
              [%term
                `t3;
                f `x'']
            in
            [%term
              let f x' = if `t31 then `t32 in
              f init]
        in
        ( env,
          [%term
            let init = `t1 in
            let last = `t2 in
            `t] )
    | Texp_send _ | Texp_new _ ->
        Flag.Abstract.over "class/object";
        Flag.Abstract.under "objects are safe";
        (env, Term.rand typ)
    | Texp_instvar _ -> unsupported "expression (instvar)"
    | Texp_setinstvar _ -> unsupported "expression (setinstvar)"
    | Texp_override _ -> unsupported "expression (override)"
    | Texp_letmodule (mb_id, _loc, _, mb_expr, e) ->
        let mb_id_opt =
          if is_named_module mb_id then Some (get_module_id mb_id)
          else unsupported "expression (let module _ = ...)"
        in
        let env, m, mdl = from_module_expr_top ~env mb_id_opt mb_expr in
        let m = Option.get m in
        let env, t = from_expression ~env e in
        ( env,
          [%term
            let m = `mdl in
            `t] )
    | Texp_letexception (ext, e) ->
        let env, (s, kind) = from_typedtree_extension_constructor ~tenv ~env ext in
        let row =
          match kind with
          | `Ext_decl (ext_row_args, ext_row_ret) ->
              assert (ext_row_ret = None);
              { ext_row_path = LId s; ext_row_args; ext_row_ret }
          | _ -> assert false
        in
        let decl = Syntax.Type_ext (Ext_type (C.exn, ([], row))) in
        let env, t = from_expression ~env e in
        (env, Term.local decl t)
    | Texp_assert _ as desc ->
        let e = decomp_Texp_assert desc in
        let s = Format.asprintf "%a" Print.location exp_loc in
        if !Flag.Print.assert_loc then
          if !!Mochi_util.is_silent then Format.fprintf !Flag.Print.target "%s@." s
          else Format.fprintf !Flag.Print.target "Found assertion: %s@." s;
        let force =
          [] <> from_attributes exp_attributes
          || List.exists (fst |- String.exists s) env.target_locs
        in
        List.iter (fun (loc, r) -> if String.exists s loc then r := true) env.target_locs;
        let env, t = from_expression ~env e in
        let t' =
          if t.desc = Const False then make_fail ~force ~loc:exp_loc typ
          else make_assert ~force ~loc:exp_loc t
        in
        (env, t')
    | Texp_lazy e ->
        let env, t = from_expression ~env e in
        (env, make_lazy t)
    | Texp_object _ ->
        Flag.Abstract.over "class/object";
        (env, Term.rand typ)
    | Texp_pack mdl ->
        let env, _, mdl = from_module_expr_top ~env None mdl in
        (env, Term.pack mdl typ)
    | Texp_unreachable -> (env, Term.bot typ)
    | Texp_extension_constructor _ -> unsupported "Texp_extension_constructor"
    | Texp_letop { let_; ands; body; partial; param = _ } ->
        let from_bop ~env letop =
          let env, ty = from_type_expr ~env ~tenv letop.bop_op_type in
          let env, op = from_ident_path ~env ~tenv letop.bop_op_path (fun env -> (env, ty)) in
          let env, t = from_expression ~env letop.bop_exp in
          (env, op, ty, t)
        in
        let env, op, typ, t1 =
          let env, op, ty, t0 = from_bop ~env let_ in
          let env, t1 =
            List.L.fold_left ands ~init:(env, t0) ~f:(fun (env, acc) andop ->
                let env, op, typ, t' = from_bop ~env andop in
                (env, Term.(var_lid ~typ op @@ [ acc; t' ])))
          in
          (env, op, ty, t1)
        in
        let env, pat = from_case ~env body in
        let ty_ret = (snd pat).typ in
        let t2 = make_function ~partial:(partial = Partial) ~loc:exp_loc ~ty_ret [ pat ] in
        (env, Term.(var_lid ~typ op @@ [ t1; t2 ]))
    | Texp_open (_open_decl, e) -> from_expression ~env e
  in
  (env, t |> unify_newtype newtypes typ |> set_typ -$- typ |> add_attr (ALoc exp_loc))

and from_case : type k. env:env -> k case' -> env * (Syntax.pattern * term) =
 fun ~env { c_lhs; c_guard; c_rhs } ->
  let env, p = try from_pattern ~env c_lhs with PatternExcep _ -> assert false in
  let env, t =
    let id_env = get_bv_pat p @ env.id_env in
    from_expression ~env:{ env with id_env } c_rhs
  in
  let env, p' =
    match c_guard with
    | None -> (env, p)
    | Some e ->
        let env, t = from_expression ~env e in
        (env, Pat.when_ p t)
  in
  (env, (p', t))

and from_case_with_excep : type k. env:env -> k case' -> env * (bool * pattern * term) =
 fun ~env { c_lhs; c_guard; c_rhs } ->
  let env, p, is_excep =
    try
      let env, p = from_pattern ~env c_lhs in
      (env, p, false)
    with PatternExcep (env, p) -> (env, p, true)
  in
  let env, t =
    let id_env = get_bv_pat p @ env.id_env in
    from_expression ~env:{ env with id_env } c_rhs
  in
  let env, p' =
    match c_guard with
    | None -> (env, p)
    | Some e ->
        let env, t = from_expression ~env e in
        (env, Pat.when_ p t)
  in
  (env, (is_excep, p', t))

and from_module_binding ~env { mb_id; mb_expr } =
  from_module_expr_top ~env (some_module mb_id) mb_expr

(* [path] is for Tstr_include *)
and from_types_signature ~env ~tenv ?path (sgn : Types.signature) =
  let env, items = from_list ~f:(from_types_signature_item ~tenv ?path) sgn ~env in
  let sgn =
    items
    |> List.L.fold_right ~init:[] ~f:(fun item acc ->
           match (item, acc) with
           | `Type decl, `Types decls :: acc' -> `Types (decl :: decls) :: acc'
           | `Type decl, _ -> `Types [ decl ] :: acc
           | `Val x, _ -> `Val x :: acc
           | `Ext x, _ -> `Ext x :: acc)
    |> List.flatten_map (function
         | `Types decls ->
             let aux acc_rev (s, pty, st) =
               match (acc_rev, st) with
               | _, Trec_not -> (`Nonrec, [ (s, pty) ]) :: acc_rev
               | _, Trec_first -> (`Rec, [ (s, pty) ]) :: acc_rev
               | (flag, decl) :: acc_rev', Trec_next -> (flag, (s, pty) :: decl) :: acc_rev'
               | [], Trec_next -> assert false
             in
             (* I don't know why cyclic definitions appear; we have to see the stamp of Ident.t?
                (e.g., https://github.com/reasonml/reason/blob/7592a8f5df61fb62da577b77972a2341143a6071/src/menhir-recover/synthesis.ml) *)
             let cyclic_to_nonrec = function
               | `Rec, ([ (s, (_, TConstr (c, _))) ] as decl) when Path.(LId s = c) ->
                   (`Nonrec, decl)
               | decl -> decl
             in
             decls
             |> List.fold_left aux []
             |> List.map cyclic_to_nonrec
             |> List.rev_flatten_map (function
                  | `Rec, decl -> [ List.rev decl ]
                  | `Nonrec, decl -> List.rev @@ encode_nonrec_type_decl decl)
             |> List.map _Sig_type
         | `Val x -> [ Sig_value x ]
         | `Ext x -> [ Sig_ext x ])
  in
  (env, sgn)

and from_types_signature_item ~env ~tenv ?path sig_item =
  match sig_item with
  | Sig_value (id, val_desc, _) ->
      let env, ty = from_type_expr ~env ~tenv val_desc.val_type in
      (env, `Val (from_ident ~env id ty))
  | Sig_type (id, ty_decl, rec_status, _) ->
      let s = name_of_ident id in
      let env, ty = from_types_type_declaration ~env ~tenv ty_decl in
      let env =
        match path with None -> env | Some m -> cons_tconstr_env (Pdot (m, Ident.name id)) env
      in
      (env, `Type (constr_of_string s, ty, rec_status))
  | Sig_typext (id, ext, _, _) ->
      let ext_row_path = Type.LId (constr_of_string @@ name_of_ident id) in
      let env, (tc, params, ext_row_args, ext_row_ret) =
        from_types_extension_constructor ~tenv ~env ext
      in
      let ext = { ext_row_path; ext_row_args; ext_row_ret } in
      (env, `Ext (tc, (params, ext)))
  | Sig_module (m, _, mod_decl, _, _) ->
      let env, ty = from_types_module_type ~env ~tenv mod_decl.md_type in
      (env, `Val (from_ident ~env m ty))
  | Sig_modtype (x, mtd, _) ->
      let s = name_of_ident x in
      let env, ty = from_modtype_declaration ~env ~tenv mtd in
      (env, `Type (constr_of_string s, ([], ty), Trec_not))
  | Sig_class (c, decl, _, _) ->
      let env, ty = from_types_class_type ~env ~tenv decl.cty_type in
      (env, `Val (from_ident ~env c ty))
  | Sig_class_type (x, decl, _, _) ->
      let s = name_of_ident x in
      let env, ty = from_types_class_type ~env ~tenv decl.clty_type in
      (env, `Type (constr_of_string s, ([], ty), Trec_not))

and from_types_class_type ~env ~tenv:_ _cty = (env, typ_class)

and from_types_module_type ~env ~tenv mty =
  match Env.scrape_alias tenv (Mtype.scrape tenv mty) with
  | Mty_ident path when Ident.global (List.hd @@ P.heads path) ->
      let env, path' = normalized_path_of' ~env ~tenv path in
      (env, TModLid path')
  | Mty_ident path ->
      let env, path' = normalized_path_of' ~env ~tenv path in
      (env, TConstr (path', []))
  | Mty_signature sgn ->
      let env, sgn = from_types_signature ~env ~tenv sgn in
      (env, TModSig sgn)
  | Mty_functor _ as mty ->
      let arg, mty2 = decomp_Mty_functor mty in
      let id, (env, ty1) =
        match arg with
        | Unit -> (None, (env, TModSig empty_signature))
        | Named (id, mty1) -> (id, from_types_module_type ~env ~tenv mty1)
      in
      let m = match id with None -> Id.make ~env "_" ty1 | Some id -> from_ident ~env id ty1 in
      let env, ty2 = from_types_module_type ~env ~tenv mty2 in
      (env, TFun (m, ty2))
  | Mty_alias path -> (
      try from_types_module_type ~env ~tenv (Env.find_module path tenv).md_type
      with Not_found ->
        let env, path' = normalized_path_of' ~env ~tenv path in
        (env, TConstr (path', [])))

and from_typedtree_signature ~env ~tenv (sgn : Typedtree.signature) =
  from_types_signature ~env ~tenv sgn.sig_type

and from_typedtree_module_type ~env ~tenv mty = from_types_module_type ~env ~tenv mty.mty_type
(*
  match mty.mty_desc with
  | Tmty_ident(path,_) -> env, TConstr(normalized_path_of ~tenv:mty.mty_env path, [])
  | Tmty_signature sgn ->
      let env,sgn = from_typedtree_signature ~env ~tenv sgn in
      env, TModule sgn
  | Tmty_functor(_param, _mty) -> unsupported "Tmty_functor"
  | Tmty_with(mty, _with_ty) -> from_typedtree_module_type ~env ~tenv mty
  | Tmty_typeof _md -> unsupported "Tmty_typeof"
  | Tmty_alias(_path, _id) -> unsupported "Tmty_alias"*)

and from_module_type_declaration ~env ~tenv
    ({ mtd_name; mtd_type; _ } : Typedtree.module_type_declaration) =
  let c = constr_of_string mtd_name.txt in
  let env, ty =
    match mtd_type with
    | None -> (env, Ty.abst)
    | Some mty -> from_typedtree_module_type ~env ~tenv mty
  in
  (env, c, ty)

and from_modtype_declaration ~env ~tenv ({ mtd_type; _ } : Types.modtype_declaration) =
  match mtd_type with None -> (env, Ty.abst) | Some mty -> from_types_module_type ~env ~tenv mty

and from_module_expr_top ~env mb_id_opt mb_expr : env * id option * term =
  let env, mdl = tmp_remove_prefix_target_exn mb_id_opt (fun () -> from_module_expr ~env mb_expr) in
  let m = Option.map (from_ident ~env -$- mdl.typ) mb_id_opt in
  (env, m, mdl)

and from_module_expr ~env mb_expr : env * term =
  match mb_expr.mod_desc with
  | Tmod_structure struc ->
      let env, typ = from_types_module_type ~env ~tenv:mb_expr.mod_env mb_expr.mod_type in
      let env, fdecls = from_structure env struc in
      let decls = trans_decls env fdecls in
      let mdl = make_module ~typ decls in
      let id_env =
        let map =
          List.flatten_map (function Syntax.Decl_let defs -> List.map fst defs | _ -> []) decls
        in
        map @ env.id_env
      in
      ({ env with id_env }, mdl)
  | Tmod_ident (path, _loc) ->
      let tenv = mb_expr.mod_env in
      let path = Env.normalize_module_path None tenv path in
      let mk_ty env = from_types_module_type ~env ~tenv mb_expr.mod_type in
      let env, lid = from_ident_path ~env ~tenv path mk_ty in
      let hd = List.hd @@ P.heads path in
      if Ident.global hd then
        let m = Lid.head lid in
        let typ = TModLid (path_of_lid lid) in
        let m' = Id.set_typ m typ in
        let lid' = Lid.subst_head (IdMap.singleton m' (LId m')) lid in
        let env = add_mod_typ_ident ~env ~tenv hd in
        (env, Term.var_lid ~typ lid')
      else (env, Term.var_lid lid)
  | Tmod_functor _ as desc ->
      let arg, expr = decomp_Tmod_functor desc in
      let env, m =
        match arg with
        | Unit -> (env, Id.new_var ~env ~name:"U" (TModSig empty_signature))
        | Named (id, _, mty) ->
            let env, ty = from_typedtree_module_type ~env ~tenv:mb_expr.mod_env mty in
            let m =
              match id with
              | None -> Id.new_var ~env ~name:"U" ty
              | Some id -> from_ident ~env id ty
            in
            (env, m)
      in
      let env, mdl = from_module_expr ~env expr in
      (env, Term.fun_ m mdl)
  | Tmod_apply (e1, e2, _) ->
      let env, t1 = from_module_expr ~env e1 in
      let env, t2 = from_module_expr ~env e2 in
      let env, ty = from_types_module_type ~env ~tenv:mb_expr.mod_env mb_expr.mod_type in
      (env, set_typ Term.(t1 @ [ t2 ]) ty)
  | Tmod_constraint (expr, _, _, _) -> from_module_expr ~env expr
  | Tmod_unpack (e, mty) ->
      let env, ty = from_types_module_type ~env ~tenv:mb_expr.mod_env mty in
      let env, t = from_expression ~env e in
      (env, Term.unpack ~typ:ty t)
  | _ -> [%unsupported]
[@@ocaml.warning "-11"]

(* Unused? *)
and from_open_declaration ~env { open_expr = { mod_desc; mod_type }; open_env = tenv } =
  match mod_desc with
  | Tmod_ident (path, _) ->
      let mk_ty env = from_types_module_type ~env ~tenv mod_type in
      (env, from_ident_path ~env ~tenv path mk_ty)
  | _ -> unsupported "Tstr_open"

and from_types_extension_constructor ~tenv ~env ext =
  let from_ty = from_type_expr ~visited:[] ~tenv in
  let env, ext_row_path = normalized_path_of' ~env ~tenv ext.ext_type_path in
  let env, params = from_list ~f:from_ty ~env ext.ext_type_params in
  let env, ext_row_args = from_types_constructor_arguments ~tenv ~env ext.ext_args in
  let env, ext_row_ret = from_option ~f:from_ty ~env ext.ext_ret_type in
  (env, (ext_row_path, params, ext_row_args, ext_row_ret))

and from_typedtree_extension_constructor ~tenv ~env ext_constr : env * (constr * _) =
  let s = constr_of_string @@ name_of_ident ext_constr.ext_id in
  match ext_constr.ext_kind with
  | Text_decl _ as kind ->
      let cd_args, cd_ret = decomp_Text_decl kind in
      let env, ext_row_args = from_typedtree_constructor_arguments ~env ~tenv cd_args in
      let env, ext_row_ret = from_option ~f:(from_core_type ~tenv) ~env cd_ret in
      (env, (s, `Ext_decl (ext_row_args, ext_row_ret)))
  | Text_rebind (path, _) ->
      let env, p = normalized_path_of' ~env ~tenv path in
      (env, (s, `Ext_rebind p))

and from_str_item env str_item : env * decl list =
  let tenv = str_item.str_env in
  match str_item.str_desc with
  | Tstr_eval (e, _) ->
      let env, t = from_expression ~env e in
      (env, [ Decl_let [ (Id.new_var ~env ~name:"u" t.typ, t) ] ])
  | Tstr_value (Recursive, pats) ->
      let env, bindings = from_let_rec ~env pats in
      (env, [ Decl_letrec bindings ])
  | Tstr_value (Nonrecursive, pats) ->
      let env, decls =
        from_list ~env pats ~f:(fun ~env { vb_pat; vb_expr } ->
            let env, p = from_pattern ~env vb_pat in
            let env, t = from_expression ~env vb_expr in
            let x =
              match p.pat_desc with
              | PVar x -> Some x
              | PConst { desc = Const Unit } -> Some (Id.new_var ~env ~name:"u" Ty.unit)
              | PAny -> Some (new_var_of_term t)
              | _ -> None
            in
            let lhs = match x with Some x -> `Var x | None -> `Match p in
            (env, (lhs, t)))
      in
      let decl, bvs =
        if List.exists (fst |- function `Match _ -> true | `Var _ -> false) decls then
          ( Decl_let_match
              (List.map (Pair.map_fst @@ function `Match p -> p | `Var x -> Pat.var x) decls),
            List.rev_flatten_map
              (fst |- function `Match p -> get_bv_pat p | `Var x -> [ x ])
              decls )
        else
          ( Decl_let (List.map (Pair.map_fst @@ function `Var x -> x | _ -> assert false) decls),
            List.map (fst |- function `Var x -> x | _ -> assert false) decls )
      in
      (check_shadow bvs env, [ decl ])
  | Tstr_primitive v ->
      let env, ty = from_type_expr ~env ~tenv v.val_val.val_type in
      let x = from_ident ~env v.val_id ty in
      (env, [ Decl_let [ (x, Term.rand ty) ] ])
  | Tstr_type (rec_flag, decls) ->
      let flag = from_rec_flag rec_flag in
      let env, decls' = from_list ~f:(from_typedtree_type_declaration ~tenv) ~env decls in
      let decl =
        match flag with Nonrecursive -> Decl_type_nonrec decls' | Recursive -> Decl_type decls'
      in
      (env, [ decl ])
  | Tstr_typext ext ->
      let env, params =
        from_list ~f:(fun ~env (p, _) -> from_core_type ~tenv ~env p) ~env ext.tyext_params
      in
      assert (List.for_all Is'._TVar params);
      let env, rows =
        from_list ext.tyext_constructors ~env ~f:(fun ~env constr ->
            let env, (s, kind) = from_typedtree_extension_constructor ~tenv ~env constr in
            match kind with
            | `Ext_decl (ext_row_args, ext_row_ret) ->
                (env, { ext_row_path = LId s; ext_row_args; ext_row_ret })
            | _ -> assert false)
      in
      let env, s = normalized_path_of' ~env ~tenv ext.tyext_path in
      let s' = assoc_prim_path s ext.tyext_path in
      (env, List.map (fun row -> Ext_type (s', (params, row))) rows)
  | Tstr_exception { tyexn_constructor } ->
      let env, (s, kind) = from_typedtree_extension_constructor ~tenv ~env tyexn_constructor in
      let ext =
        match kind with
        | `Ext_decl (ext_row_args, ext_row_ret) ->
            assert (ext_row_ret = None);
            Ext_type (C.exn, ([], { ext_row_path = Type.LId s; ext_row_args; ext_row_ret }))
        | `Ext_rebind c -> Ext_rebind (s, c)
      in
      (env, [ ext ])
  | Tstr_module mb ->
      let env, m, mdl = from_module_binding ~env mb in
      let m = Option.get m in
      (env, [ Decl_let [ (m, mdl) ] ])
  | Tstr_recmodule _ -> unsupported "recursive modules"
  | Tstr_modtype mtd ->
      let env, name, ty = from_module_type_declaration ~env ~tenv mtd in
      (env, [ Decl_type [ (name, ([], ty)) ] ])
  | Tstr_open _open_decl -> (env, [])
  | Tstr_class _ | Tstr_class_type _ -> (env, [])
  | Tstr_include { incl_mod; _ } ->
      let env, t1 = from_module_expr ~env incl_mod in
      (env, [ Include t1 ])
  | Tstr_attribute _ -> (env, [])

and from_structure env struc : env * decl list =
  Dbg_orig.printf "struc: @[%a@." Printtyped.implementation struc;
  let aux (env, decls) str_item =
    let env, decls' = from_str_item env str_item in
    (env, decls @ decls')
  in
  List.fold_left aux (env, []) struc.str_items

let add_prefix prefix id = Type.LDot (prefix, name_of_ident id)

let rec col_ext tenv (summary : Env.summary) =
  match summary with
  | Env_empty -> []
  | Env_extension (summary, id, ext) ->
      (id, (lid_of_string (name_of_ident id), ext)) :: col_ext tenv summary
  | Env_module (summary, id, _, decl) ->
      Format.fprintf !Flag.Print.target "Env_module: %s@." (name_of_ident id);
      col_ext_mod_decl tenv (lid_of_string (name_of_ident id)) decl @ col_ext tenv summary
  | Env_open (summary, path) ->
      col_ext_mod_decl tenv (snd @@ normalized_path_of ~tenv path) (Env.find_module path tenv)
      @ col_ext tenv summary
  | Env_modtype (summary, _, _)
  | Env_value (summary, _, _)
  | Env_type (summary, _, _)
  | Env_class (summary, _, _)
  | Env_cltype (summary, _, _)
  | Env_functor_arg (summary, _)
  | Env_constraints (summary, _)
  | Env_persistent (summary, _) ->
      col_ext tenv summary
  | Env_copy_types _ -> col_ext tenv (summary_of_Env_copy_types summary)
  | _ when is_Env_value_unbound summary -> col_ext tenv (summary_of_Env_value_unbound summary)
  | _ when is_Env_module_unbound summary -> col_ext tenv (summary_of_Env_module_unbound summary)
  | _ -> assert false
[@@ocaml.warning "-11"]

and col_ext_mod_decl tenv (prefix : Type.path) decl =
  match decl.md_type with
  | Mty_ident _path -> []
  | Mty_signature sgn ->
      sgn
      |> List.rev_flatten_map (fun (item : Types.signature_item) ->
             match item with
             | Sig_value _ -> []
             | Sig_type _ -> []
             | Sig_typext (id, ext, _, _) -> [ (id, (add_prefix prefix id, ext)) ]
             | Sig_module (id, _, decl, _, _) -> col_ext_mod_decl tenv (add_prefix prefix id) decl
             | Sig_modtype _ -> []
             | Sig_class _ -> []
             | Sig_class_type _ -> [])
  | Mty_functor _ -> []
  | Mty_alias path -> col_ext_mod_decl tenv prefix (Env.find_module path tenv)

let col_ext env = col_ext env (Env.summary env)

let get_exc_env ~tenv =
  tenv
  |> col_ext
  |> List.filter (fun (_, (_, ext)) -> ext.ext_type_path = Predef.path_exn)
  |> List.map (fun (id, (name, _)) -> (name, id))

let with_info source_file k =
  let output_prefix = Filename.remove_extension source_file in
  Compile_common.with_info ~native:false ~tool_name:"mochi" ~source_file ~output_prefix
    ~dump_ext:"unused" k

let parse_file ?tenv ?env filename =
  let tenv = Option.default_delayed Compmisc.initial_env tenv in
  let orig = with_info filename Compile_common.parse_impl in
  let env = Option.default_delayed make_env env in
  let struc, tenv = Typemod.type_structure tenv orig in
  let env, decls = from_structure env struc in
  (tenv, orig, env, trans_decls env decls)

let parse_string ?tenv ?env ?(filename = "temp.ml") s =
  let file = Temp.S.file filename in
  let@ cout = IO.CPS.open_out file in
  output_string cout s;
  parse_file ?tenv ?env file

let add_exc_decl used_exc t =
  let labels = List.sort compare used_exc in
  let add (ext_row_path, (_path, ext_row_args)) t =
    let ext = (C.exn, ([], { ext_row_path; ext_row_args; ext_row_ret = None })) in
    Term.local (Type_ext (Ext_type ext)) t
  in
  List.fold_right add labels t

(** Remove inline records by adding new type definitions
    and change path to tconstr *)
let normalize_inline_record =
  let tr = Tr2.make () in
  tr.decl <-
    (fun env decl ->
      match decl with
      | Syntax.Decl_type decls ->
          decls
          |> List.flatten_map (fun (s, (params, ty)) ->
                 match ty with
                 | TVariant (VNonPoly, rows) ->
                     let rows', decls =
                       rows
                       |> List.split_map (fun row ->
                              match row.row_args with
                              | [ TRecord fields ] ->
                                  let c' =
                                    constr_of_string (Id.name s ^ "." ^ Id.name row.row_constr)
                                  in
                                  ( { row with row_args = [ TConstr (LId c', params) ] },
                                    [ (c', (params, TRecord fields)) ] )
                              | _ -> (row, []))
                     in
                     (s, (params, TVariant (VNonPoly, rows'))) :: List.flatten decls
                 | _ -> [ (s, (params, ty)) ])
          |> _Decl_type
      | Type_ext
          (Ext_type
            (s, (params, { ext_row_path; ext_row_args = [ (TRecord _ as ty) ]; ext_row_ret }))) ->
          assert (ext_row_ret = None);
          assert (Type.Is._LId ext_row_path);
          let s' = Type.ValE._LId ext_row_path in
          let decl1 = Syntax.Decl_type [ (s', (params, ty)) ] in
          let ty' = TConstr (LId s', params) in
          let decl2 =
            Type_ext (Ext_type (s, (params, { ext_row_path; ext_row_args = [ ty' ]; ext_row_ret })))
          in
          Decl_multi [ decl1; decl2 ]
      | _ -> tr.decl_rec env decl);
  tr.typ <-
    (fun env ty ->
      match ty with
      | TConstr (LDot (LId c1, c2), tys) when Char.is_lowercase (Id.name c1).[0] ->
          let c = Type.LId (tconstr_of_string (Id.name c1 ^ "." ^ c2)) in
          let tys' = List.map (tr.typ env) tys in
          TConstr (c, tys')
      | _ -> tr.typ_rec env ty);
  tr.term Tenv.empty

let mark_free_as_external_typ bound =
  make_trans (fun tr ty ->
      match ty with
      | TConstr (c, tys) when not (List.mem c bound) ->
          let c' = Path.map ~f:(Id.add_attr Id.External) c in
          let tys' = List.map tr tys in
          Some (TConstr (c', tys'))
      | _ -> None)

let normalize_name_of_first_class_module : term -> term =
  let tr = Tr.make () in
  tr.var <-
    (fun x ->
      match Id.typ x with
      | TPackage _ when Char.is_uppercase (Id.name x).[0] -> Id.add_name_prefix "_" x
      | _ -> x);
  tr.term

type orig = Parsetree.structure
type ext_mod_typ = Problem.ext_mod_typ list
type result = { origs : orig list; ext_mod_typ : ext_mod_typ; parsed : term }

(** Modules of standard libraries are mutually recursive *)
let inline_stdlib_types ext_mod_typ =
  match Id.List.assoc_opt stdlib' ext_mod_typ with
  | None -> ext_mod_typ (* Cannot happen? *)
  | Some (TModSig sgn) ->
      let env =
        sgn
        |> List.filter_map (function Sig_type decl -> Some decl | _ -> None)
        |> List.flatten
        |> fixed_point (fun env -> Fmap.(list (snd (snd (subst_tconstr_map_typ env)))) env)
        |> List.map (fun (x, ty) -> (Type.LDot (LId stdlib', Id.name x), ty))
      in
      ext_mod_typ
      |> List.map (fun (x, ty) ->
             if String.starts_with (Id.name x) "Stdlib__" then (x, Type_util.subst_constr_map env ty)
             else (x, ty))
  | Some _ -> assert false

let sort_ext_mod ext_mod_typ =
  let edges = ext_mod_typ |> List.flatten_map (fun (x, ty) -> [ (x, get_fv_typ ty) ]) in
  Dbg.printf "edges: %a@." Print.(list (tconstr * list tconstr)) edges;
  Tsort.sort_strongly_connected_components edges
  |@> Dbg.printf "sorted: %a@." Print.(list (list tconstr))
  |> List.flatten
  |> List.map (fun x -> (x, Id.List.assoc x ext_mod_typ))

let parse_files ?env filenames : result =
  ignore @@ Warnings.parse_options false "-a";
  let init_tenv = !!Compmisc.initial_env in
  let dirs = Load_path.get_paths () in
  List.iter (Load_path.add_dir -| Filename.dirname) filenames;
  let env = Option.default_delayed make_env env in
  let origs, _, env, cont =
    List.L.fold_right filenames ~init:([], init_tenv, env, Fun.id)
      ~f:(fun filename (origs, tenv, env, cont) ->
        let tenv, orig, env, decls = parse_file ~tenv ~env filename in
        let cont' = List.fold_right Term.local decls |- cont in
        (orig :: origs, tenv, env, cont'))
  in
  Load_path.init dirs (* Reset the load path for the next parsing *);
  let pr s t =
    if false then Format.printf "%a##parsed[%s]:%t@.@." Color.set Green s Color.reset;
    if false then
      Format.printf "%a##parsed[%s]:%t@.%a@.@." Color.set Green s Color.reset Print.term t
  in
  let parsed =
    cont Term.eod
    |@> pr "orig"
    |> normalize_ids
    |@> pr "normalize_ids"
    |> normalize_inline_record
    |@> pr "normalize_inline_record"
    |> Trans.mark_free_as_external
    |@> pr "Trans.mark_free_as_external"
    |> Trans.make_bind_for_PAlias (* See #1 of memo.md *)
    |@> pr "Trans.make_bind_for_PAlias"
    |> normalize_name_of_first_class_module
    |@> pr "normalize_name_of_first_class_module"
    |> set_afv
  in
  let ext_mod_typ =
    env.mod_typ_env
    |> List.map (fun (_, (x, ty)) -> (Id.set_typ x (), ty))
    |> inline_stdlib_types
    |> sort_ext_mod
  in
  { origs; ext_mod_typ; parsed }

let () = Compmisc.init_path init_path_arg
