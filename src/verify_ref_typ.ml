open Util
open Mochi_util
open! Type
open Type_util
open Syntax
open Term_util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

let remove_ext_def = Tr2.make ()

let remove_ext_def_desc ext desc =
  match desc with
  | Local(Decl_let bindings, t) ->
      let bindings' = List.filter_out (fun (f,_) -> Id.List.mem f ext) bindings in
      let t' = remove_ext_def.term ext t in
      if bindings' = [] then t'.desc else Local(Decl_let bindings', t')
  | _ -> remove_ext_def.desc_rec ext desc

let () = remove_ext_def.desc <- remove_ext_def_desc
let remove_ext_def = remove_ext_def.term

let divide spec t ref_env =
  Debug.printf "PROGRAM: %a@." Print.term t;
  Debug.printf "ORIG: %a@." (List.print Print.id) @@ get_top_funs t;
  let ext = List.map fst ref_env in
  let t_main = remove_ext_def ext t in
  Debug.printf "MAIN: %a@." (List.print Print.id) @@ get_top_funs t_main;
  let make_spec f =
    let ref_env,ext_ref_env = List.partition (Id.eq f -| fst) ref_env in
    let ext_ref_env = List.map (fun (f,ty) -> f, None, ty) ext_ref_env in
    let aux (_,typ) =
      if not @@ Type_util.same_shape (Id.typ f) (Ref_type.to_simple typ) then
        begin
          Format.eprintf "VAR: %a@." Id.print f;
          Format.eprintf "  Prog: %a@." Print.typ @@ Id.typ f;
          Format.eprintf "  Spec: %a@." Ref_type.print typ;
          failwith "Type of %a in the specification is wrong?" Print.id f
        end
    in
    List.iter aux ref_env;
    {spec with Spec.ref_env; Spec.ext_ref_env = ext_ref_env @ spec.Spec.ext_ref_env}
    |@> Debug.printf "SUB[%a]: %a@." Print.id f Spec.print
  in
  let targets = List.map (fun f -> Id.to_string f, make_spec f, t) ext in
  Debug.printf "MAIN: %a@." Print.term t_main;
  ("MAIN", make_spec (Id.new_var ~name:"MAIN" Ty.unit), t_main)::targets


let main orig spec parsed =
  let verify (s,spec,t) =
    Debug.printf "Start verification of %s:@.%a@." s Spec.print spec;
    s, Main_loop.run ~orig (Some (Problem.safety ~spec t))
  in
  Spec.get_ref_env spec parsed
  |@> Verbose.printf "%a@." Spec.print_ref_env
  |> divide spec parsed
  |> List.map verify
  |@> Format.fprintf !Flag.Print.target "RESULT: %a@." Print.(list (string * bool))
  |> List.for_all snd
