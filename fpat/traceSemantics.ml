open Util
open Combinator

(** Trace semantics *)

let mk_call f args = Term.mk_app (Term.mk_const Const.Call) (f :: args)
let mk_ret ret ty t = Term.mk_app (Term.mk_const (Const.Ret(ty))) [ret; t]
let mk_error = Term.mk_const Const.Error

(*val redex_of : (Idnt.t -> Type.t) -> t -> (t -> t) * t*)
(** support fail, rand_int, and read_int as effectful expressions *)
let rec redex_of tenv t =
  match Term.fun_args t with
  | Term.Const(Const.Call), f :: args ->
    (fun t -> t), mk_call f args
  | Term.Const(Const.Ret(ty)), [ret; t] ->
    begin
      try
        let ctx, red = redex_of tenv t in
        (fun t -> mk_ret ret ty (ctx t)), red
      with Not_found -> (fun t -> t), mk_ret ret ty t
    end
  | f, args when args <> [] ->
    begin
      try
        let args1, (ctx, red), args2 = redex_of_args tenv [] args in
        (fun t -> Term.mk_app f (args1 @ [ctx t] @ args2)), red
      with
      | Not_found ->
        match f with
        | Term.Const(Const.Event(id)) when id = Const.event_fail ->
          let ar = 1 in
          if List.length args >= ar then
            let args1, args2 = List.split_nth ar args in
            (fun t -> Term.mk_app t args2), Term.mk_app f args1
          else raise Not_found
        | Term.Const(Const.RandInt) ->
          let ar = 1 in
          if List.length args >= ar then
            let args1, args2 = List.split_nth ar args in
            (fun t -> Term.mk_app t args2), Term.mk_app f args1
          else raise Not_found
        | Term.Const(Const.ReadInt(_, tys)) ->
          let ar = List.length tys + 1 in
          if List.length args >= ar then
            let args1, args2 = List.split_nth ar args in
            (fun t -> Term.mk_app t args2), Term.mk_app f args1
          else raise Not_found
        | Term.Var(ff) ->
          let ar =
            try
              Type.arity_of (tenv ff)
            with Not_found ->
              raise Not_found (* ff is not a function name *)
              (*(Format.printf "%a@," Idnt.pr ff; assert false)*)
          in
          if List.length args >= ar then
            let args1, args2 = List.split_nth ar args in
            (fun t -> Term.mk_app t args2), Term.mk_app f args1
          else raise Not_found
        | Term.Const(c) -> raise Not_found
        | _ -> assert false
    end
  | _ -> raise Not_found
and redex_of_args tenv args1 args =
  match args with
  | [] -> raise Not_found
  | arg :: args2 ->
    try args1, redex_of tenv arg, args2
    with Not_found -> redex_of_args tenv (args1 @ [arg]) args2
