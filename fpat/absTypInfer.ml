open Util
open Combinator

(** Abstraction type inference *)

let mode = ref (*`IntType *) `RefType

let infer_etrs fs is_cp prog solver etrs =
  match !mode with
  | `RefType ->
    etrs
    |> RefTypInfer.infer_etrs fs is_cp solver prog
    |> Logger.pprintf "refinement types:@,  %a@," RefType.pr_env
    |> List.map @@ Pair.map_snd @@ AbsType.of_refinement_type
    |> List.classify @@ (comp2 (=) fst fst)
    |> List.map
      (function
        | (f, sty) :: fstys ->
          f, AbsType.merge (sty :: List.map snd fstys)
        | _ -> assert false)

let refine solver prog fs is_cp cexs feasible ext_cexs =
  try
    (if false then
       let penv = assert false in
       CompTreeExpander.error_traces_of prog feasible penv cexs
     else
       List.concat_map2
         (fun cex ->
            List.map
              (fun (p, ps) ->
                 let cnt = ref 0 in
                 p,
                 fun ts ->
                   let (tenv, phi) =
                     try
                       List.nth ps !cnt
                     with _ ->
                       Format.printf
                         "!cnt: %d@,p: %a@,ps: %a@,"
                         !cnt
                         Idnt.pr p
                         (List.pr (Pair.pr TypEnv.pr Formula.pr) ",")
                         ps;
                       assert false
                   in
                   let tenv = tenv @ [p, Type.mk_int] in
                   cnt := !cnt + 1;
                   if List.length tenv <> List.length ts then begin
                     Format.printf
                       "%a and %a have diff. lengths in AbsTypInfer.refine@,"
                       TypEnv.pr tenv
                       Term.pr_list ts;
                     assert false
                   end;
                   let tsub = List.map2 (fun (x, _) t -> x, t) tenv ts in
                   let tts = List.map2 (fun (_, ty) t -> t, ty) tenv ts in
                   Pva.make
                     (Idnt.T(Idnt.T(p, !cnt, List.length tenv - 1), -1, 0))
                     tts,
                   Formula.subst tsub phi)
            >> flip (CompTreeExpander.error_traces_of prog feasible) [cex])
         cexs ext_cexs)
    |> infer_etrs fs is_cp solver prog
    |> Logger.pprintf "abstraction types:@,  %a@," AbsType.pr_env
  with Global.NotImplemented s ->
    Format.printf "not implemented in %s@," s;
    assert false
let refine ?(solver=fun x->x) =
  Logger.log_block6
    "AbsTypInfer.refine"
    ~before:(fun prog fs _ cexs feasible ext_cexs ->
        assert (List.length cexs = List.length ext_cexs);
        Logger.printf "program:@,  %a@," Prog.pr prog;
        Logger.printf
          "inlined functions: %a@,"
          String.pr (String.concat "," fs);
        Logger.printf "feasible?: %a@," Bool.pr_yn feasible;
        let cex = List.hd cexs in
        let ext_cex = List.hd ext_cexs in
        Logger.printf "counterexample: %a@," (List.pr Integer.pr ":") cex;
        Logger.printf "ext. counterexample: %a@,"
          (List.pr (Pair.pr Idnt.pr (List.pr (Pair.pr TypEnv.pr Formula.pr) ",")) ":")
          ext_cex)
    (refine solver)
