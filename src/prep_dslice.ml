open Util
open Problem
open Preprocess_common
open! Term_util

module Dbg = Debug.Make (struct
  let check = Flag.Debug.make_check __MODULE__
end)

type Syntax.prep_info += Info_slice_top_fun of Dslice.info * problem

let slice_top_fun : trans =
  let tr (problem : Problem.t) =
    Flag.Log.Time.before_slice := !!Time.get;
    let unsafe_ext_funs =
      problem.spec.ext_ref_env
      |> List.filter_out (Ref_type.is_safe_fun -| snd -| snd)
      |> List.map fst
    in
    let attr = Sliced :: List.filter_out (( = ) Problem.Set_main) problem.attr in
    let pullback =
      let trans_cex xs =
        let x = List.max ~cmp:(Compare.on Triple.fst) xs in
        let problem =
          match x with _, Some (Info_slice_top_fun (_, problem)), _ -> problem | _ -> assert false
        in
        Trans_problem.make_trans_cex_single problem [ x ]
      in
      { id_pullback with trans_cex = Some trans_cex }
    in
    let slice (fs : Syntax.id list) : trans_result * Dslice.info =
      let term, info = Dslice.slice_top_fun unsafe_ext_funs problem.term fs in
      let problem = { problem with term; attr } in
      let problem' = Problem.map Trans.remove_info_trans problem in
      ((Some (Info_slice_top_fun (info, problem)), problem'), info)
    in
    let r, _ = slice [] in
    let rec gen_next (history : history) : (trans_result * next option) option =
      let used, info =
        match history with
        | (Some (Info_slice_top_fun (info, problem)), Unsafe { vals_main }) :: _ ->
            let used = ref [] in
            let print_app t =
              match t.Syntax.desc with
              | App ({ desc = Var (LId f) }, _) -> used := f :: !used
              | _ -> ()
            in
            let ce, main = !?vals_main in
            let problem' =
              match main with
              | None -> problem
              | Some main -> Problem.map (Trans.replace_main ~force:true ~main) problem
            in
            Eval.eval ce ~hook:print_app problem';
            (!used, info)
        | _ -> assert false
      in
      let used_but_removed = Id.List.Set.inter used info.removed in
      if used_but_removed = [] then None
      else
        let fs = Id.List.Set.(used + info.do_not_removed) in
        let r, { Dslice.removed } = slice fs in
        let next = if removed = [] then None else Some (Trans gen_next) in
        Some (r, next)
    in
    (pullback, Some (r, Some (Trans gen_next)))
  in
  (Or, tr)

type Syntax.prep_info += Info_slice_main of Syntax.lid option * problem * term option

let pullback_set_main : pullback option =
  let make_get_rtyp = None in
  let trans_cex =
    Some
      (function
      | (_, Some (Info_slice_main (_, problem, main)), (lazy (ce, _))) :: _ ->
          (Eval.trans ce problem, main)
      | _ -> assert false)
  in
  Some { make_get_rtyp; trans_cex }

let set_main problem =
  assert (List.mem Sliced problem.attr);
  let attr = Problem.Set_main :: List.remove_all problem.attr Sliced in
  ( pullback_set_main,
    match Term_util.get_main problem.term |> Syntax.Val._Tuple with
    | None -> assert false
    | Some [] ->
        let term, f = Trans.set_main problem.term in
        let problem' = { problem with term; attr } in
        LazyList.singleton (Info_slice_main (f, problem', None), problem')
    | Some targets ->
        targets
        |> List.map Syntax.ValE._Var
        |> (!Flag.Method.slice_target <> "")
           ^> List.filter (fun x -> Lid.to_string x = !Flag.Method.slice_target)
        |> LazyList.of_list
        |> LazyList.map (fun f ->
               let main, term = Trans.set_main_for ~force:true [ f ] problem.term in
               let info = Format.asprintf "Target %a" Print.lid f :: problem.info in
               let problem' = { problem with term; info; attr } in
               (Info_slice_main (Some f, problem', main), problem')) )

type Syntax.prep_info += Info_slice_top_fun_by_hops of float

let slice_top_fun_by_hops ?(num = !Flag.Method.slice_num) problem =
  Flag.Log.Time.before_slice := !!Time.get;
  let unsafe_ext_funs =
    problem.spec.ext_ref_env |> List.filter_out (Ref_type.is_safe_fun -| snd -| snd) |> List.map fst
  in
  let slice = Dslice.slice_top_fun_by_hops unsafe_ext_funs problem.Problem.term in
  let make i =
    let p = float (i + 1) /. float num in
    let term = slice p in
    let info = Format.sprintf "Slice %.3f" p :: problem.info in
    let attr = Sliced :: List.filter_out (( = ) Problem.Set_main) problem.attr in
    (Info_slice_top_fun_by_hops p, { problem with term; info; attr })
  in
  if !Flag.Method.slice_i < 0 then (* for debug/experiments *)
    LazyList.init num make
  else LazyList.singleton (make !Flag.Method.slice_i)
