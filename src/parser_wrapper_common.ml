open Util
open Syntax
open Term_util
open Type

type env =
  {id_env : id list;
   md_prefix : string;
   tconstrs : Path.t list;
   exc_env : (string * typ list) list;
   tvar_env : (int * typ) list}

let add_exc_env name typs env =
  if List.mem_assoc name env.exc_env then
    if List.eq ~eq:Type.same_shape (List.assoc name env.exc_env) typs then
      env
    else
      unsupported "Same name exception"
  else
    let exc_env = (name,typs) :: env.exc_env in
    {env with exc_env}
let exc_typ env = TVariant(false, env.exc_env)

let init_env : env =
  {id_env = [];
   md_prefix = "";
   tconstrs = [];
   exc_env = [];
   tvar_env = []}

let alpha_rename_decls (fdecls : (rec_flag * Syntax.declaration) list) : Syntax.declaration list =
  let mark (flag,decl) acc =
    let should_rename =
      match decl with
      | Decl_let defs ->
          let rec check mfdecls x =
            match mfdecls with
            | [] -> false
            | (should_rename, Nonrecursive, Decl_let defs) :: mfdecls' ->
                begin
                try
                  if Id.mem x @@ get_fv @@ Id.assoc x defs then
                    if not @@ Id.mem x should_rename then
                      true
                    else
                      check mfdecls' x
                  else
                    false
                with Not_found -> false
                end
            | _::mfdecls' -> check mfdecls' x
          in
          defs
          |> List.map fst
          |> List.filter (check acc)
      | _ -> []
    in
    (should_rename,flag,decl)::acc
  in
  let marked_fdecls = List.fold_right mark fdecls [] in
  let rename (should_rename,flag,decl) acc =
    if should_rename = [] then
      (flag,decl)::acc
    else
      match decl with
      | Decl_let defs ->
          let map = List.map (Pair.add_right Id.new_var_id) should_rename in
          let defs' =
            let map_body =
              match flag with
              | Recursive -> subst_var_map map
              | Nonrecursive -> Fun.id
            in
            List.map (fun (x,t) -> Id.assoc_default x x map, map_body t) defs
          in
          let acc' = List.fold_left (fun fdecls (x,x') -> subst_fdecls x Term.(var x') fdecls) acc map in
          (flag, Decl_let defs') :: acc'
      | _ -> assert false
  in
  List.fold_right rename marked_fdecls []
  |> List.map snd
