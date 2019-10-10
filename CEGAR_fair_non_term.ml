open HORS_syntax
open Util
open CEGAR_util

let expansion_iter_count_ref = ref 0
module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

(**
   [x -> ex1] ex2
*)
let rec subst x ex1 ex2 =
  match ex2 with
  | Var s ->
     if s = x then
       ex1
     else
       Var s
  | Apply (e1, e2) ->
     Apply (subst x ex1 e1, subst x ex1 e2)
  | Abst (s, e1) ->
     Abst (s, subst x ex1 e1)

let rec decomp = function
  | Apply (e1, e2) ->
     let hd, e1' = decomp e1 in
     hd, e1' @ [e2]
  | e -> e, []

let apply s children =
  List.fold_left (fun e1 e2 -> Apply (e1, e2)) (Var s) children

(**
   exprをn回くらい展開して、反例木を生成する
*)
let rec expand_tree rules n expr =
  let is_term f =
    not (List.mem_assoc f rules) in

  let get_fun f =
    List.assoc f rules in

  if n < - (max 30 !Flag.FairNonTermination.expand_ce_iter_init) then
    (Flag.FairNonTermination.break_expansion_ref := true;
     Var "end") (* 打ち切れる場所が現れないときの無限ループ防止 *)
  else match expr with
  | Var s when is_term s ->
     Var s
  | Var s ->
     let e = get_fun s in
     expand_tree rules (n - 1) e
  | Abst (x, e) ->
     Abst (x, e)
  | Apply (e1, e2) ->
     begin match expand_tree rules (n - 1) e1 with
     | Var s when n < 0 && (String.starts_with s "randint_") -> (* n回展開済みで、乱数生成の直前なら、展開を打ち切る*)
        Var "end"
     | Abst (x, e) ->
        expand_tree rules n (subst x e2 e)
     | e1' ->
        begin match decomp e1' with
        | Var "end", _ -> Var "end"
        | Var s, children ->
           let e2' = expand_tree rules (n - 1) e2 in
           apply s (children @ [e2'])
        | _, _ -> assert false
        end
     end

let not_dummy = function
  | Var "_" -> false
  | _ -> true

let rec value2tree v =
  match decomp v with
  | Var "br_forall", children ->
     let child = List.find not_dummy children in
     Rose_tree.Node ("br_forall", List.map value2tree [child])
  | Var s, children ->
     Rose_tree.Node (s, List.map value2tree children)
  | _ -> assert false

let rec expansion_loop prog0 labeled is_cp ce_rules prog start_symbol =
  let count = !expansion_iter_count_ref in
  try
    Debug.printf "Expand counterexample: Size %d@." count;
    Flag.FairNonTermination.break_expansion_ref := false;
    let ce_value = expand_tree ce_rules count (Var start_symbol) in
    let ce_tree = value2tree ce_value in
    Debug.printf "tree: %a@." (Rose_tree.print Format.pp_print_string) ce_tree;
    (*feasiblity check and refinement is common with that of non-termination*)
    CEGAR_non_term.cegar prog0 labeled is_cp ce_tree prog
  with
  | CEGAR_syntax.NoProgress ->
     (Debug.printf "Increase iteration of counterexample expansion@.";
      expansion_iter_count_ref := count + 5;
      expansion_loop prog0 labeled is_cp ce_rules prog start_symbol)

let cegar prog0 labeled is_cp ce_rules prog =
  expansion_iter_count_ref := max !Flag.FairNonTermination.expand_ce_iter_init !expansion_iter_count_ref;
  (* Format.printf "RULES: %a@.@." (List.print pp_rule) ce_rules; *)
  let start_symbol = fst @@ List.hd ce_rules in
  expansion_loop prog0 labeled is_cp ce_rules prog start_symbol
