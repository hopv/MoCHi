open Util
open Syntax
open Type
open Term_util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type atom = Term of term | PApp of id * id list
type constr = {head:atom; body:atom list} (* if head is the form of `PApp(p,xs)`, `xs` must be distinct each other *)
type t = constr list
type pvar = id

module PVarSet = Set.Make(ID)

let is_base_const t =
  match t.desc with
  | Const _ -> is_base_typ t.typ
  | _ -> false

let is_simple_expr t =
  is_simple_bexp t || is_simple_aexp t || is_base_const t

let term_of_atom a =
  match a with
  | Term t -> t
  | PApp(p,xs) -> Term.(var p @ vars xs)

let atom_of_term t =
  match t.desc with
  | App({desc=Var p}, ts) ->
      let xs = List.map (function {desc=Var x} -> x | _ -> invalid_arg "CHC.atom_of_term") ts in
      if not @@ Id.is_predicate p then invalid_arg "CHC.atom_of_term";
      PApp(p, xs)
  | App _ ->
      Format.eprintf "%a@." Print.term t;
      invalid_arg "CHC.atom_of_term"
  | _ ->
      if is_simple_expr t then
        Term t
      else
        (Format.eprintf "%a@." Print.term t;
         invalid_arg "CHC.atom_of_term")

let print_atom fm a =
  match a with
  | Term t -> Print.term fm t
  | PApp(p, xs) -> Format.fprintf fm "@[%a(%a)@]" Id.print p (print_list Id.print ", ") xs
let print_constr fm {head;body} = Format.fprintf fm "@[<hv>%a@\n  |= %a@]" (List.print print_atom) body print_atom head
let print fm (constrs:t) =
  Format.fprintf fm "@[";
  List.iter (fun c -> Format.fprintf fm "%a@\n@\n" print_constr c) constrs;
  Format.fprintf fm "@]"

let print_one_sol fm (p,(xs,atoms)) = Format.fprintf fm "@[%a := %a@]" print_atom (PApp(p,xs)) (List.print print_atom) atoms
let print_sol fm sol = List.print print_one_sol fm sol

let check_type_atom a = try Type_check.check (term_of_atom a) ~ty:Ty.bool with _ -> Format.printf "UNTYPABLE: %a@." Print.term' @@ term_of_atom a ;assert false
let check_type_constr {head;body} = List.iter check_type_atom (head::body)
let check_type_constrs = List.iter check_type_constr


let of_term_list (constrs : (term list * term) list) =
  List.map (fun (body,head) -> {body=List.map atom_of_term body; head=atom_of_term head}) constrs

let to_term_list (constrs : t) =
  List.map (fun {body;head} -> List.map term_of_atom body, term_of_atom head) constrs

let decomp_app a =
  match a with
  | PApp(p,xs) -> Some (p,xs)
  | Term _ -> None
let is_app_of a p = decomp_app a |> Option.exists (fst |- Id.(=) p)
let is_app = decomp_app |- Option.is_some
let is_term = decomp_app |- Option.is_none
let decomp_term a =
  match a with
  | PApp _ -> None
  | Term t -> Some t

let same_atom a1 a2 = same_term (term_of_atom a1) (term_of_atom a2)
let unique = List.unique ~eq:same_atom

let pvar_of a =
  match a with
  | PApp(p, _) -> Some p
  | _ -> None

let rename_map ?(body=false) map a =
  match a with
  | PApp(p,xs) ->
      let dom,range = List.split map in
      if not (body || List.Set.(disjoint ~eq:Id.eq range (diff ~eq:Id.eq xs dom))) then
        (Format.eprintf "%a %a@." Print.(list (id * id)) map print_atom a;
         invalid_arg "CHC.rename_map");
      PApp(p, List.map (fun z -> List.assoc_default ~eq:Id.eq z z map) xs)
  | Term t' -> Term (subst_var_map map t')

let rename ?(body=false) x y a =
  match a with
  | PApp(p,xs) when Id.mem x xs ->
      if not body && Id.mem y xs then (Format.eprintf "[%a |-> %a](%a)@." Id.print x Id.print y print_atom a; invalid_arg "CHC.rename");
      PApp(p, List.map (fun z -> if Id.eq x z then y else z) xs)
  | PApp _ -> a
  | Term t' -> Term (subst_var x y t')

let get_fv a =
  match a with
  | Term t -> get_fv t
  | PApp(_,xs) -> xs

let get_fv_constr {head; body} = List.unique ~eq:Id.eq @@ List.flatten_map get_fv (head::body)

let map_head f {head; body} = {head=f head; body}
let map_body f {head; body} = {head; body=f body}
let map f {head;body} = {head=f head; body=List.map f body}

type data = (pvar * pvar) list * PVarSet.t * constr list * (pvar * (pvar list * atom list)) list

let dummy_pred = Id.new_predicate Ty.int

let normalize_constr {head;body} =
    match head with
    | PApp(p,xs) when List.length xs <> List.length @@ List.unique ~eq:Id.eq xs ->
        let rec aux cond acc_rev xs =
          match xs with
          | [] -> cond, List.rev acc_rev
          | x::xs' ->
              if Id.mem x xs' then
                let x' = Id.new_var_id x in
                aux (Term Term.(var x = var x')::cond) (x'::acc_rev) xs'
              else
                aux cond (x::acc_rev) xs'
        in
        let cond,xs' = aux [] [] xs in
        {head=PApp(p,xs'); body=cond@body}
    | _ -> {head; body}
let normalize constrs = List.map normalize_constr constrs

let rec once acc fv =
  match fv with
  | [] -> acc
  | [x] -> x::acc
  | x1::x2::fv' when Id.(x1 <> x2) -> once (x1::acc) (x2::fv')
  | x::fv' ->
      fv'
      |> List.drop_while (Id.(=) x)
      |> once acc
let once xs = once [] xs

let get_dependencies constrs : (pvar * pvar) list =
  let aux {body;head} =
    let p_head = match pvar_of head with None -> dummy_pred | Some p -> p in
    List.map (fun p -> p, p_head) @@ List.filter_map pvar_of body
  in
  constrs
  |> List.flatten_map aux
  |> List.unique ~eq:(Pair.eq Id.eq Id.eq)

let get_pvars deps =
  deps
  |> List.flatten_map Pair.to_list
  |> PVarSet.of_list
  |> PVarSet.remove dummy_pred



let apply_sol_atom sol fv a =
  match a with
  | PApp(p,xs) ->
      begin
        match Id.assoc_option p sol with
        | Some (ys,atoms,fv') ->
            let fv'',atoms' =
              if List.Set.disjoint ~eq:Id.eq fv fv' then
                fv', atoms
              else
                let fv'' = List.map Id.new_var_id fv' in
                fv'', List.map (rename_map ~body:true (List.combine fv' fv'')) atoms
            in
            if not @@ List.Set.disjoint ~eq:Id.eq fv fv'' then assert false;
            if List.length xs <> List.length ys then invalid_arg "CHC.apply_sol_atom";
            Debug.printf "[apply_sol_atom] fv: %a@." Print.(list id) fv;
            Debug.printf "[apply_sol_atom] fv': %a@." Print.(list id) fv';
            Debug.printf "[apply_sol_atom] fv'': %a@." Print.(list id) fv'';
            Debug.printf "[apply_sol_atom] sol: %a@." print_one_sol (p,(ys,atoms));
            Debug.printf "[apply_sol_atom] a: %a@." print_atom a;
            List.map (rename_map ~body:true (List.combine ys xs)) atoms'
            |@> Debug.printf "[apply_sol_atom] r: %a@.@." (Print.list print_atom)
        | None -> [a]
      end
  | _ -> [a]

let apply_sol_constr sol {head;body} =
  let fv = get_fv_constr {head;body} in
  let body = unique @@ List.flatten_map (apply_sol_atom sol fv) body in
  if List.exists (is_app_of head -| fst) sol then
    []
  else
    let heads = apply_sol_atom sol fv head in
    List.map (fun head -> {head; body}) heads
    |@> Debug.printf "[apply_sol_constr] input: %a@.[apply_sol_constr] output: %a@.@." print_constr {head;body} (List.print print_constr)

let apply_sol sol' (deps,ps,constrs,sol : data) : data =
  Debug.printf "[apply_sol] input: %a@." print constrs;
  let add_fv (p,(xs,atoms)) = p, (xs, atoms, List.unique ~eq:Id.eq @@ List.Set.diff ~eq:Id.eq (List.flatten_map get_fv atoms) xs) in
  Debug.printf "[apply_sol] sol': %a@." print_sol sol';
  let constrs' = List.flatten_map (apply_sol_constr @@ List.map add_fv sol') constrs in
  let deps' = get_dependencies constrs' in
  let ps' = get_pvars deps' in
  let sol'' = sol' @ sol in
  Debug.printf "[apply_sol] output: %a@." print constrs';
  deps', ps', constrs', sol''



(* Trivial simplification *)
let simplify_trivial (deps,ps,constrs,sol : data) =
  Debug.printf "INPUT: %a@." print constrs;
  check_type_constrs constrs;
  let rec loop need_rerun body1 body2 head head_fv =
    if !!Debug.check then assert (List.Set.eq ~eq:Id.eq (get_fv head) head_fv);
    match body2 with
    | [] ->
        begin
          match head with
          | Term {desc=Const True} -> None
          | Term {desc=BinOp(Eq, t1, t2)} when is_simple_expr t1 && same_term t1 t2 -> None
          | _ ->
              if List.exists (same_atom head) body1 then
                None
              else
                Some (need_rerun, {body=body1; head})
        end
    | a::body2' ->
        match a with
        | Term {desc=Const True} -> loop need_rerun body1 body2' head head_fv
        | Term {desc=Const False} -> None
        | Term {desc=BinOp(Eq, t1, t2)} when is_simple_expr t1 && same_term t1 t2 -> loop true body1 body2' head head_fv
        | Term {desc=BinOp(And, t1, t2)} -> loop need_rerun body1 (Term t1::Term t2::body2') head head_fv
        | Term {desc=BinOp(Eq, {desc=Var x}, {desc=Var y})} when not (Id.mem x head_fv && is_app head && Id.mem y head_fv) ->
            let head' = rename x y head in
            let rn = List.map (rename ~body:true x y) in
            let head_fv' = get_fv head' in
            loop true [] (rn body1 @ rn body2') head' head_fv'
        | _ -> loop need_rerun (a::body1) body2' head head_fv
  in
  let need_rerun,constrs' =
    let aux {body;head} (b,acc) =
      match loop false [] body head (get_fv head) with
      | None -> true, acc
      | Some(need_rerun,constr') -> b||need_rerun, constr'::acc
    in
    List.fold_right aux constrs (false,[])
  in
  let deps' = if need_rerun then get_dependencies constrs' else deps in
  let ps' = if need_rerun then get_pvars deps' else ps in
  Debug.printf "[simplify_trivial]  input: %a@." print constrs;
  Debug.printf "[simplify_trivial] output: %a@." print constrs';
  Some (need_rerun, (deps',ps',constrs',sol))

(* Remove predicates which do not occur in a body *)
let simplify_unused (deps,ps,constrs,sol as x : data) =
  let ps1,ps2 = PVarSet.partition (fun p -> List.exists (fun (p1,_) -> Id.(p = p1)) deps) ps in
  if PVarSet.is_empty ps2 then
    None
  else
    let () = Debug.printf "REMOVE1: %a@." Print.(list id) @@ PVarSet.elements ps2 in
    let sol' =
      let aux p =
        let xs,_ = decomp_tfun @@ Id.typ p in
        p, (xs, [])
      in
      List.map aux (PVarSet.elements ps2)
    in
    Some (true, apply_sol sol' x)

(* Forwarad inlinining *)
let simplify_inlining_forward (deps,ps,constrs,sol as x : data) =
  let check p =
    let count (n_head,n_body) {head;body} =
      (if is_app_of head p then 1+n_head else n_head),
      List.count (is_app_of -$- p) body + n_body
    in
    let n_head,n_body = List.fold_left count (0,0) constrs in
    let self_implication p {head;body} = is_app_of head p && List.exists (is_app_of -$- p) body in
    n_head = 1 && not @@ List.exists (self_implication p) constrs
  in
  let ps' = PVarSet.filter check ps in
  if PVarSet.is_empty ps' then
    None
  else
    let ps' = [List.hd @@ PVarSet.elements ps'] in (* TODO: fix *)
    let assoc p = List.find (fun {head} -> is_app_of head p) constrs in
    let sol' =
      let aux p =
        let {head;body} = assoc p in
        let _,xs = Option.get @@ decomp_app head in
        p, (xs, body)
      in
      List.map aux ps'
    in
    Debug.printf "inline': %a@." Print.(list id) ps';
    Some (true, apply_sol sol' x)

(* Backward inlinining *)
let simplify_inlining_backward (deps,ps,constrs,sol : data) =
  let aux {head;body} =
    let body1,body2 = List.partition is_app body in
    if is_term head then
      match body1 with
      | [PApp(p,xs)] ->
          let ts = List.map term_of_atom body2 in
          let t = term_of_atom head in
          let ts',xs' =
            if List.length xs = List.length @@ List.unique ~eq:Id.eq xs then
              ts, xs
            else
              let rec aux ts acc_rev xs =
                match xs with
                | [] -> ts, List.rev acc_rev
                | x::xs' ->
                    if Id.mem x xs' then
                      let x' = Id.new_var_id x in
                      aux (Term.(var x = var x')::ts) (x'::acc_rev) xs'
                    else
                      aux ts (x::acc_rev) xs'
              in
              aux ts [] xs
          in
          let goal = Term.(not (ands ts') || t) in
          let fv = List.Set.diff ~eq:Id.eq (Syntax.get_fv goal) xs' in
          Some(p, (xs', fv, Term goal))
      | _ -> None
    else
      None
  in
  let goals = List.filter_map aux constrs in
  if goals = [] then
    None
  else
    let () = Debug.printf "goals: %a@." Print.(list (id * triple (list id) __ print_atom)) goals in
    let new_constrs =
      let aux {head;body} =
        match head with
        | Term _ -> None
        | PApp(f,xs) ->
            match Id.assoc_option f goals with
            | None -> None
            | Some (ys, fv, a) ->
                let fv' = List.map Id.new_var_id fv in
                let a' =
                  a
                  |> rename_map (List.combine fv fv')
                  |> rename_map (List.combine ys xs)
                in
                Some {head=a'; body}
      in
      List.filter_map aux constrs
    in
    let constrs' = new_constrs @ constrs in
    let deps' = get_dependencies constrs' in
    let ps' = get_pvars deps' in
    let sol' = sol in
    Some (false, (deps', ps', constrs', sol'))

(* Remove clause whose body is unsatisfiable *)
let simplify_unsat (deps,ps,constrs,sol : data) =
  let is_sat {body} =
    body
    |> List.filter is_term
    |> List.map term_of_atom
    |> make_ands
    |> FpatInterface.of_term
    |> Fpat.Formula.of_term
    |> FpatInterface.is_sat
  in
  let constrs1,constrs2 = List.partition is_sat constrs in
  if constrs2 = [] then
    None
  else
    let constrs' = constrs1 in
    let deps' = get_dependencies constrs' in
    let ps' = get_pvars deps' in
    let sol' = sol in
    Some (true, (deps', ps', constrs', sol'))

(* Remove clause whose body is unsatisfiable *)
let simplify_not_in_head (deps,ps,constrs,sol as x : data) =
  let check p = not @@ List.exists (fun {head} -> is_app_of head p) constrs in
  let ps1,ps2 = PVarSet.partition check ps in
  if PVarSet.is_empty ps1 then
    None
  else
    let sol' =
      let aux p =
        let xs,_ = decomp_tfun @@ Id.typ p in
        p, (xs, [Term false_term])
      in
      List.map aux @@ PVarSet.elements ps1
    in
    Some (true, apply_sol sol' x)


(* Merge simple constraints for the same head *)
let simplify_same_head (deps,ps,constrs,sol as x : data) =
  let check p =
    let constrs' = List.filter (fun {head} -> is_app_of head p) constrs in
    List.length constrs' >= 2 &&
    List.for_all (fun {body} -> List.for_all is_term body) constrs'
  in
  let ps1,ps2 = PVarSet.partition check ps in
  if PVarSet.is_empty ps1 then
    None
  else
    let assoc p =
      let aux {head;body} =
        match decomp_app head with
        | Some (p', xs) when Id.(p = p') ->
            let fv = List.Set.diff ~eq:Id.eq (get_fv_constr {head;body}) xs in
            let t = make_ands @@ List.map term_of_atom body in
            let fv' = List.map Id.new_var_id fv in
            Some (xs, subst_var_map (List.combine fv fv') t)
        | _ -> None
      in
      constrs
      |> List.filter_map aux
      |> List.reduce (fun (xs,t) (xs',t') -> xs, make_or t (subst_var_map (List.combine xs' xs) t'))
    in
    Debug.printf "merge: %a@." Print.(list id) @@ PVarSet.elements ps1;
    let sol' =
      let aux p =
        let xs,t = assoc p in
        p, (xs, [Term t])
      in
      List.map aux @@ PVarSet.elements ps1
    in
    Some (true, apply_sol sol' x)

let simplifiers : (string * (data -> (bool * data) option)) list =
  ["simplify_unused", simplify_unused;
   "simplify_trivial", simplify_trivial;
   "simplify_not_in_head", simplify_not_in_head;
   "simplify_inlining_forward", simplify_inlining_forward;
   "simplify_unsat", simplify_unsat;
   "simplify_same_head", simplify_same_head;
(*   "simplify_inlining_backward", simplify_inlining_backward*)]

let check_data_validity (deps,ps,constrs,sol : data) =
  let deps' = get_dependencies constrs in
  let ps' = get_pvars deps' in
  if not (List.Set.eq ~eq:(Pair.eq Id.eq Id.eq) deps deps') then
    begin
      Format.eprintf "deps: %a@." Print.(list (id * id)) deps;
      Format.eprintf "deps': %a@." Print.(list (id * id)) deps';
      assert false
    end;
  if not (PVarSet.equal ps' ps) then
    begin
      Format.eprintf "ps: %a@." Print.(list id) @@ PVarSet.elements ps;
      Format.eprintf "ps': %a@." Print.(list id) @@ PVarSet.elements ps';
      assert false
    end

let simplify ?(normalized=false) (constrs:t) =
  let constrs = normalize constrs in
  Debug.printf "dummy_pred: %a@." Id.print dummy_pred;
  Debug.printf "INPUT: %a@." print constrs;
  let deps = get_dependencies constrs in
  Debug.printf "deps: %a@." Print.(list (id * id)) deps;
  let ps = get_pvars deps in
  let rec loop ?(cnt=0) orig rest x =
    Debug.printf "cnt: %d@." cnt;
    if !!Debug.check then check_data_validity x;
    match rest with
    | [] -> x
    | (desc,f)::rest' ->
        let r = f x in
        if r <> None then Debug.printf "%s is applied@." desc;
        match r with
        | None -> loop ~cnt:(cnt+1) orig rest' x
        | Some(true, x') -> loop ~cnt:(cnt+1) orig orig x'
        | Some(false, x') -> loop ~cnt:(cnt+1) orig rest' x'
  in
  let loop orig x = loop orig orig x in
  let deps',ps',constrs',sol = loop simplifiers (deps, ps, constrs, []) in
  Debug.printf "REMOVED: %a@." Print.(list id) @@ List.map fst sol;
  Debug.printf "deps': %a@." Print.(list (id * id)) @@ List.sort (Compare.on (Pair.map_same Id.id)) deps';
  Debug.printf "SIMPLIFIED: %a@." print constrs';
  Debug.printf "sol: %a@." print_sol sol;
  sol, constrs'
