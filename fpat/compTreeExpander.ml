open Util
open Combinator

(** Computation tree expander *)

(** traversal strategies *)
type 'a s = {
  is_end: unit -> bool;
  get: unit -> 'a list;
  pick: unit -> 'a;
  add: 'a list -> unit
}

let is_end wlr () = !wlr = []
let get wlr () = !wlr

(** breadth first strategy *)
let bf_strategy ct =
  let wlr = ref [ct] in
  { is_end = is_end wlr;
    get = get wlr;
    pick = (fun () ->
        match !wlr with
        | [] -> raise Not_found
        | n :: wl -> wlr := wl; n);
    add = (fun wl -> wlr := !wlr @ wl) }

(** depth first strategy *)
let df_strategy ct =
  let wlr = ref [ct] in
  { is_end = is_end wlr;
    get = get wlr;
    pick = (fun () -> match !wlr with
        | [] -> raise Not_found
        | n :: wl -> wlr := wl; n);
    add = (fun wl -> wlr := wl @ !wlr) }

(** strategy using a filter *)
let filter_strategy filter ct =
  let wlr = ref (filter [ct]) in
  { is_end = is_end wlr;
    get = get wlr;
    pick = (fun () -> match !wlr with
        | [] -> raise Not_found
        | n :: wl -> wlr := wl; n);
    add = (fun wl -> wlr := (filter wl) @ !wlr) }

let manual = ref false
let expand_until_new_error_trace_found prog feasible penv ct strategy =
  let rec loop fenv =
    if strategy.is_end () then ()
    else
      begin
        Logger.log (fun () ->
            CompTree.save_graphviz
              (Filename.chop_extension
                 !Global.target_filename
               ^ "_comp_tree"
               ^ string_of_int !Global.cegar_iterations
               ^ ".dot")
              ct
              (strategy.get ()));
        let fenv, wl =
          CompTree.expand_node prog feasible penv fenv (strategy.pick ())
        in
        strategy.add wl;
        let rec lp () =
          Format.printf "expand the computation tree ? (y/n): %!";
          let inp = read_line () in
          if inp = "y" then true else if inp = "n" then false else lp ()
        in
        if List.exists
            (fun ct ->
               match ct.CompTree.term with
               | Term.Const(Const.Error) -> true
               | _ -> false)
            wl && (not !manual || lp ())
        then ()
        else loop fenv
      end
  in
  loop EnvFun.mk_empty
let expand_until_new_error_trace_found =
  Logger.log_block5
    "CompTreeExpander.expand_until_new_error_trace_found"
    expand_until_new_error_trace_found

let expand_all prog feasible penv ct strategy =
  let rec loop fenv =
    if strategy.is_end () then ()
    else begin
      let fenv, wl =
        CompTree.expand_node prog feasible penv fenv (strategy.pick ())
      in
      strategy.add wl;
      loop fenv
    end
  in
  loop EnvFun.mk_empty
let expand_all = Logger.log_block5 "CompTreeExpander.expand_all" expand_all


let error_traces_of prog feasible penv cexs =
  let rt = CompTree.init prog in
  let strategy =
    filter_strategy
      (List.filter
         (fun ct -> List.exists (List.is_prefix ct.CompTree.path) cexs))
      rt
  in
  (*expand_until_new_error_trace_found*)
  expand_all prog feasible penv rt strategy;
  CompTree.error_traces_of rt
let error_traces_of =
  Logger.log_block4
    ~before:(fun _ _ _ ->
        List.iter
          (Logger.printf "counterexample: %a@," (List.pr Integer.pr ":")))
    ~after:(Logger.printf "error traces:@,  %a@," (List.pr Trace.pr "@,"))
    "CompTreeExpander.error_traces_of"
    error_traces_of

