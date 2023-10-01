open Util
open! Type
open! Type_util
open Syntax
open Term_util

type configuration =
  {error_accept: error list;
   error_reject: error list;
   verify: term -> bool;
   target: term}

and error = string

let num_of_lets =
  let col = Col.make 0 (+) in
  let col_decl decl =
    match decl with
    | Decl_let defs ->
        List.fold_left (fun acc (_,t) -> acc + 1 + col.term t) 0 defs
    | _ -> col.decl_rec decl
  in
  col.decl <- col_decl;
  col.term

exception AlreadyShrinked

let info = AInfo (InfoString "Shrinked")
let add_info t = add_attr info t
let has_info t = List.mem info t.attr
let remove_info =
  let tr = Tr.make () in
  tr.attr <- List.remove_all -$- info;
  fun conf -> {conf with target = tr.term conf.target}

exception Unchanged

let log fmt = Format.fprintf !Flag.Print.target ("[LOG] " ^^ fmt ^^ "@.")

(* 0-origin *)
let shrink_let_body =
  let tr = Tr2.make () in
  let tr_decl n decl =
    if !n < 0 then
      decl
    else
      match decl with
      | Decl_let defs when !n < List.length defs ->
          let defs' =
            List.L.mapi defs ~f:(fun i (x,t) ->
                if i = !n then
                  (if has_info t then raise AlreadyShrinked;
                   let t' = Term.rand t.typ in
                   if same_term t t' then raise Unchanged;
                   log "Shrinked: %a = %a" Print.id x Print.term t;
                   x, add_info t')
                else x, t)
          in
          n := -1;
          Decl_let defs'
      | Decl_let defs ->
          n := !n - List.length defs;
          let aux defs_rev (x,t) =
            (*            Format.fprintf !Flag.Print.target "  #%d: %a@." n Print.id x;*)
            let t' = tr.term n t in
            (x,t')::defs_rev
          in
(*
          let pr (x,t) =
            Format.fprintf !Flag.Print.target "  x: %a - %d@." Print.id x (count t)
          in
          Format.fprintf !Flag.Print.target "n: %d@." n;
          List.iter pr defs;*)
          let defs_rev = List.fold_left aux [] defs in
          (*          Format.fprintf !Flag.Print.target "n': %d@." n;*)
          Decl_let (List.rev defs_rev)
      | _ -> tr.decl_rec n decl
  in
  tr.decl <- tr_decl;
  tr.term

let shrink_let_binding =
  let tr = Tr2.make () in
  let tr_decl n decl =
    if !n < 0 then
      decl
    else
      match decl with
      | Decl_let defs when !n < List.length defs ->
          if has_info (snd @@ List.nth defs !n) then
            raise AlreadyShrinked
          else
            let x,t = List.nth defs !n in
            log "Shrinked: %a = %a" Print.id x Print.term t;
            let defs = List.remove_at !n defs in
            n := -1;
            Decl_let defs
      | Decl_let defs ->
          n := !n - List.length defs;
          let aux defs_rev (x,t) =
            let t' = tr.term n t in
            (x,t')::defs_rev
          in
          let defs_rev = List.fold_left aux [] defs in
          Decl_let (List.rev defs_rev)
      | _ -> tr.decl_rec n decl
  in
  tr.decl <- tr_decl;
  tr.term

exception Error_not_found

let get_error f t =
  let error =
    try
      Ok (f t)
    with e ->
      Error (Printexc.to_string e)
  in
  match error with
  | Ok _ -> raise Error_not_found
  | Error e -> e

let postprocess =
  remove_info

let rec apply ?prev shrink conf =
  Format.fprintf !Flag.Print.target "@.INPUT: %a@." Print.term conf.target;
  let count = num_of_lets conf.target in
  log "count: %d" count;
  let target_count =
    match prev with
    | None -> 0
    | Some (count',target) -> if count = count' then 0 else target
  in
  let rec loop error_reject target_count =
    let next_loop e = loop (Option.to_list e @ error_reject) (target_count+1) in
    log "target_count: #%d" target_count;
    if target_count >= count then
      {conf with error_reject}
    else
      try
        let target = shrink (ref target_count) conf.target in
        if conf.target = target then (Format.eprintf "Failed@."; exit 1);
        let e = get_error conf.verify target in
        log "ERROR: %s" e;
        if List.mem e conf.error_accept then
          let conf = {conf with error_reject; target} in
          log "Successfully shrinked";
          apply ~prev:(count,target_count) shrink conf
        else if List.mem e error_reject then
          (log "Already rejeced error";
           next_loop None)
        else if CommandLine.confirm "Accept the error?" then
          let error_accept = e::conf.error_accept in
          let conf = {conf with error_accept; error_reject; target} in
          log "Successfully shrinked";
          apply ~prev:(count,target_count) shrink conf
        else
          (log "Error is changed";
           next_loop (Some e))
      with AlreadyShrinked ->
             log "Already shrinked";
             next_loop None
         | Error_not_found ->
             log "Error not found";
             next_loop None
         | Unchanged ->
             log "Unchanged";
             next_loop None
  in
  loop conf.error_reject target_count

let run verify target =
  let verify t =
    let _,t = copy_tvar t in
    verify t
  in
  Mochi_util.set_silent ();
  let error = get_error verify target in
  log "ERROR: %s" error;
  {error_accept=[error]; error_reject=[]; verify; target}
  |> apply shrink_let_body
  |> remove_info
  |*> apply shrink_let_binding
  |*> remove_info
