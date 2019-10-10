open Util
open Combinator

(** Computation trees *)

(** {6 Constructors} *)

type t = {
  uid: int;
  path: int list;
  term: Term.t;
  children: (Trace.elem * t) list ref
}

(** {6 Auxiliary constructors} *)

let make uid path term children =
  { uid = uid; path = path; term = term; children = children; }

(** generate a new id of a function call *)
let gen_id =
  let cnt = ref 0 in
  fun () -> cnt := !cnt + 1; !cnt

(** [init prog] initializes a computation tree of [prog] *)
let init prog =
  let uid = gen_id () in
  let ty_main = TypEnv.lookup prog.Prog.types (Idnt.make prog.Prog.main) in
  let ret, args =
    Idnt.ret_args (Idnt.make prog.Prog.main) uid (Type.arity_of ty_main)
    |> Pair.map Term.mk_var (List.map Term.mk_var)
  in
  let _, retty = Type.args_ret ty_main in
  let start =
    TraceSemantics.mk_ret
      ret retty
      (TraceSemantics.mk_call (Term.mk_var (Idnt.make prog.Prog.main)) args)
  in
  make uid [] start (ref [])

let expand_node prog feasible penv fenv ct =
  if !(ct.children) <> [] then
    begin
      Format.printf "the specified node is already expanded@,";
      assert false
    end;
  try
    let ctx, red =
      TraceSemantics.redex_of (TypEnv.lookup prog.Prog.types) ct.term
    in
    let fenv, gns =
      match Term.fun_args red with
      | Term.Const(Const.Event id), _(*@todo*) when id = Const.event_fail ->
        Logger.printf "Event %a;" String.pr id;
        fenv,
        [ Trace.Error,
          make (gen_id ())
            ct.path
            TraceSemantics.mk_error
            (ref []) ]
      | Term.Const(Const.RandInt), [t](*@todo*) ->
        Logger.printf0 "RandInt;";
        fenv,
        [ Trace.Nop,
          make (gen_id ())
            ct.path
            (ctx (Term.mk_app t [Term.new_var ()]))
            (ref []) ]
      | Term.Const(Const.ReadInt(id, n)), ts ->
        Logger.printf0 "ReadInt;";
        assert (ts <> []);
        let r = Term.new_var () in
        let pva, phi =
          List.assoc_fail id penv
            ~on_failure:(fun () ->
                Format.printf "CompTree.expand_node: %a not found@," Idnt.pr id)
            (List.initial(* drop the continuation *) ts @ [r])
        in
        fenv,
        [ Trace.Assume((if feasible then Some(pva) else None), phi),
          make (gen_id ())
            ct.path
            (ctx (Term.mk_app (List.last ts) [r]))
            (ref []) ]
      | Term.Const(Const.Call), Term.Var(Idnt.V(_) as g) :: args ->
        Logger.printf0 "Call;";
        let fdefs = Prog.fdefs_of prog g in
        fenv,
        List.mapi
          (fun i fd ->
             let fargs =
               List.map
                 (function Pattern.V(arg) -> arg | _ -> assert false)
                 fd.Fdef.args
             in
             let faargs =
               if List.length fargs <> List.length args then begin
                 Format.printf "formal args: %a@," Idnt.pr_list fargs;
                 Format.printf "actual args: %a@," Term.pr_list args;
                 assert false
               end;
               List.combine fargs args
             in
             Trace.Call((g, ct.uid), Formula.subst faargs fd.Fdef.guard),
             make (gen_id ())
               (ct.path @ [i])
               (ctx (Term.subst faargs fd.Fdef.body))
               (ref []))
          fdefs
      | Term.Const(Const.Call), Term.Var(Idnt.T(_, _, _) as g) :: args ->
        Logger.printf0 "Call back;";
        let f = try fenv g with Not_found -> assert false in
        fenv,
        [ Trace.Call((g, ct.uid), Formula.mk_true),
          make (gen_id ())
            ct.path
            (ctx (Term.mk_app f args))
            (ref []) ]
      | Term.Const(Const.Ret(ty)), [Term.Var(ret); t] ->
        Logger.printf0 "Ret;";
        fenv,
        [ Trace.Ret(ret, (t, ty)),
          make (gen_id ())
            ct.path
            (ctx (Term.Var(ret)))
            (ref []) ]
      | func, args when args <> [] ->
        Logger.printf0 "???;";
        let f =
          match func with
          | Term.Var(f) -> f
          | _ ->
            Format.printf "%a is not a reduct@," Term.pr red;
            assert false
        in
        let uid = gen_id () in
        let argtys, retty = Type.args_ret (TypEnv.lookup prog.Prog.types f) in
        let ret, fargs = Idnt.ret_args f uid (List.length argtys) in
        let reduct =
          TraceSemantics.mk_ret
            (Term.mk_var ret) retty
            (TraceSemantics.mk_call (Term.Var(f)) (List.map Term.mk_var fargs))
        in
        let faargs =
          if List.length fargs <> List.length args then begin
            Format.printf "formal args: %a@," Idnt.pr_list fargs;
            Format.printf "actual args: %a@," Term.pr_list args;
            assert false
          end;
          List.combine fargs args
        in
        let fenv =
          EnvFun.update
            fenv
            (List.filter (fun (x, _) -> not (Prog.is_base prog x)) faargs)
        in
        assert (List.length faargs = List.length argtys);
        fenv,
        [ Trace.Arg(List.map2
                      (fun (farg, aarg) argty -> farg, (aarg, argty))
                      faargs argtys),
          make uid ct.path (ctx reduct) (ref []) ]
      | _ ->
        Format.printf "%a@," Term.pr red;
        assert false
    in
    ct.children := gns;
    fenv, List.map snd gns
  with Not_found -> (*no redex found*)
    fenv, []
let expand_node = Logger.log_block5 "CompTree.expand_node" expand_node

(** {6 Inspectors} *)

(** [traces_of ct] returns the traces of a computation tree [ct] *)
let rec traces_of ct =
  List.concat_map
    (fun (g, n) ->
       let ps = traces_of n in
       if ps = [] then [[g]] else List.map (List.cons g) ps)
    !(ct.children)

let error_traces_of = traces_of >> List.filter (List.last >> (=) Trace.Error)
let error_traces_of =
  Logger.log_block1 "CompTree.error_traces_of" error_traces_of

(** {6 Exporters} *)

let save_graphviz filename ct wl =
  let node_name uid t = String.of_int uid ^ ": " ^ Term.string_of t in
  let f = function
    | Trace.Call(_, t) -> Formula.string_of t
    | Trace.Arg(ttsub) -> Formula.string_of (Formula.of_ttsub ttsub)
    | Trace.Ret(x, tt) -> Formula.string_of (Formula.of_ttsub [x, tt])
    | Trace.Nop -> ""
    | Trace.Assume(_, _) -> "" (* @todo *)
    | Trace.Error -> ""
  in
  let rec traverse (s, l) ct =
    let s' = node_name ct.uid ct.term in
    (s, s', l)
    :: List.concat_map
      (fun (g, n) -> traverse (s', "[label = \"" ^ (f g) ^ "\"]") n)
      !(ct.children)
  in
  let es = traverse ("", "") ct |> List.unique in
  let vs =
    es
    |> List.concat_map (fun (x, y, _) -> [x, ""; y, ""])
    |> List.unique

    |> List.filter (fun (x, _) -> x <> "")

    |> List.map
      (fun (x, _) ->
         if List.exists (fun ct -> x = node_name ct.uid ct.term) wl
         then (x, "[style = dashed]")
         else (x, ""))
  in
  let es = List.filter (fun (x, _, _) -> x <> "") es in
  Graph_.save_graphviz filename vs es
