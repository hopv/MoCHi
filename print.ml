open Format
open Util
open Type
open Syntax

module Debug_attr = Debug.Make(struct let check = Flag.Debug.make_check (__MODULE__ ^ ".attr") end)
module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type config =
    {ty : bool; (** print types of arguments *)
     as_ocaml : bool; (** print terms in OCaml syntax *)
     (** Unimplemented *)
     for_dmochi : bool; (** print terms for dmochi when as_ocaml=true *)
     top : bool; (** print let/type as in top-level *)
     unused : bool; (** print unused arguments *)
     depth : int} (** max depth of printing terms *)
let config_default = ref {ty=false; as_ocaml=false; for_dmochi=false; top=false; unused=false; depth=(-1)}

let set_as_ocaml () =
  Id.set_print_as_ocaml ();
  Type.set_print_as_ocaml ();
  config_default := {!config_default with as_ocaml=true}
let set_unused () =
  config_default := {!config_default with unused=true}
let set_depth depth =
  config_default := {!config_default with depth}

let is_definitions desc =
  (snd @@ decomp_locals {desc;typ=Ty.unit;attr=[]}).desc = End_of_definitions

let rec print_typ fm t = Type.print ~occur:occur_typ (print_term {!config_default with ty=false} 0) fm t
and print_ids ?fv cfg fm xs =
  if xs <> [] then
    let xs' =
      match fv with
      | None -> xs
      | Some fv ->
          if !!Debug.check || cfg.unused then
            xs
          else
            let aux x =
              if Id.mem x fv then
                x
              else if Id.typ x = TBase TUnit then
                Id.make 0 "()" [] (TBase TUnit)
              else
                Id.make 0 "_" [] @@ Id.typ x
            in
            List.map aux xs
    in
    let p_id = if cfg.ty then print_id_typ else print_id in
    print_list p_id "@ " ~first:true fm xs'

(*
  and print_id fm x = fprintf fm "(%a:%a)" Id.print x print_typ (Id.typ x)
 *)
and print_id fm x = Id.print fm x

and print_id_typ fm x = fprintf fm "(@[%a:%a@])" print_id x (Color.cyan print_typ) (Id.typ x)

(* priority (low -> high)
   9 : Seq
   10 : Local, If, Match, TryWith
   15 : Fun
   20 : Pair
   30 : Or
   40 : And
   50 : Eq, Lt, Gt, Leq, Geq
   60 : Cons
   65 : Add, Sub
   70 : Mult, Div
   80 : Raise, App, Not, Ref, SetRef
   90 : Deref
 *)

and paren pri p = if pri < p then "","" else "(",")"

and print_binop fm = function
  | Eq -> fprintf fm "="
  | Lt -> fprintf fm "<"
  | Gt -> fprintf fm ">"
  | Leq -> fprintf fm "<="
  | Geq -> fprintf fm ">="
  | And -> fprintf fm "&&"
  | Or -> fprintf fm "||"
  | Add -> fprintf fm "+"
  | Sub -> fprintf fm "-"
  | Mult -> fprintf fm "*"
  | Div -> fprintf fm "/"

and print_termlist cfg pri fm ts =
  print_list (print_term cfg pri) "@ " fm ts

and print_const cfg fm c =
  match c with
  | Unit -> fprintf fm "()"
  | True -> fprintf fm "true"
  | False -> fprintf fm "false"
  | Int n when n<0 -> fprintf fm "(%d)" n
  | Int n -> fprintf fm "%d" n
  | Char c -> fprintf fm "%C" c
  | String s -> fprintf fm "%S" s
  | Float r -> fprintf fm "%f" r
  | Int32 n -> fprintf fm "%ldl" n
  | Int64 n -> fprintf fm "%LdL" n
  | Nativeint n -> fprintf fm "%ndn" n
  | CPS_result when cfg.as_ocaml -> fprintf fm "()"
  | CPS_result -> fprintf fm "{end}"
  | Rand(TBase TInt,false) when cfg.as_ocaml -> fprintf fm "(fun () -> Random.int 0)"
  | Rand(TBase TInt,false) -> fprintf fm "rand_int"
  | Rand(TBase TInt,true) when cfg.as_ocaml -> fprintf fm "(fun () k -> k (Random.int 0))"
  | Rand(TBase TInt,true) -> fprintf fm "rand_int_cps"
  | Rand(typ',false) -> fprintf fm "rand_val[%a]" print_typ typ'
  | Rand(typ',true) -> fprintf fm "rand_val_cps[%a]" print_typ typ'

and print_attr fm = function
  | AAbst_under -> fprintf fm "AAbst_under"
  | ATerminate -> fprintf fm "ATerminate"
  | ANotFail -> fprintf fm "ANotFail"
  | ADeterministic -> fprintf fm "ADeterministic"
  | AComment s -> fprintf fm "AComment %S" s
  | AId n -> fprintf fm "AId %d" n
  | ADoNotInline -> fprintf fm "ADoNotInline"
  | AEffect e -> List.print print_effect fm e
  | ALoc l -> print_location fm l

and print_attr_list fm attrs =
  List.print print_attr fm attrs

and ignore_attr_list = ADoNotInline::const_attr

and decomp_comment a =
  match a with
  | AComment s -> Some s
  | _ -> None

and filter_attr_list attr =
  if !!Debug_attr.check then
    attr
  else
    List.Set.diff attr ignore_attr_list
    |> List.filter (Option.is_none -| decomp_comment)
    |&!Flag.Print.only_if_id&> List.filter (function AId _ -> false | _ -> true)

and print_term cfg pri fm t =
  if cfg.depth = 0 then
    fprintf fm "..."
  else
    let cfg' = {cfg with depth=cfg.depth-1} in
    let pr attr fm desc =
      let comments = List.filter_map decomp_comment t.attr in
      if comments = [] || !!Debug_attr.check
      then fprintf fm "@[%a@]" (print_desc cfg' pri attr) desc
      else fprintf fm "(@[(* @[%a@] *)@ %a@])" (print_list pp_print_string ", ") comments (print_desc cfg' pri attr) desc
    in
    let attr = filter_attr_list t.attr in
    if attr = [] || cfg.as_ocaml
    then pr t.attr fm t.desc
    else fprintf fm "(@[%a@ #@ %a@])" (pr t.attr) t.desc print_attr_list attr

and print_let_decls cfg bang fm bindings =
  let first = ref true in
  let non_rec = is_non_rec bindings in
  let print_binding fm (f,t1) =
    let pre =
      if !first then
        "let" ^ (if bang then "!" else "") ^ (if non_rec then "" else " rec")
      else
        "and"
    in
    let xs,t1' = if !!Debug.check then [], t1 else decomp_funs t1 in
    let fv = get_fv t1' in
    let pr_ty fm = if cfg.ty then Format.fprintf fm " : %a" print_typ t1'.typ in
    fprintf fm "@[<hov 2>%s @[<hov 2>%a%a%t@] =@ %a@]" pre print_id f (print_ids ~fv cfg) xs pr_ty (print_term cfg 0) t1';
    first := false
  in
  print_list print_binding "@ " fm bindings

and print_type_decls fm defs =
  let b = ref true in
  let print_decl fm (name,ty) =
    let pre = if !b then "type" else "and" in
    fprintf fm "@[<hov 2>%s @[<hov 2>%s@] =@ %a@]" pre name print_typ ty;
    b := false
  in
  print_list print_decl "@ " fm defs

and print_decl cfg bang fm decl =
  match decl with
  | Decl_type decls -> print_type_decls fm decls
  | Decl_let bindings -> print_let_decls cfg bang fm bindings

and print_decls cfg fm decls =
  Format.fprintf fm "@[%a@]" (print_list (print_decl cfg false) "@\n") decls

and print_if_label cfg fm attr =
  if !Flag.Print.only_if_id && not cfg.as_ocaml then
    match List.find_option (function AId _ -> true | _ -> false) attr with
    | Some (AId n) -> Format.fprintf fm "^%d" n
    | _ -> ()

and print_desc cfg pri attr fm desc =
  let pr_t = print_term {cfg with top=false} in
  let pr_t' pri fm t =
    match t.desc with
    | Local _ -> print_term {cfg with top=false; depth=cfg.depth+1} pri fm t
    | _ -> pr_t pri fm t
  in
  match desc with
  | End_of_definitions when cfg.as_ocaml -> fprintf fm "()"
  | End_of_definitions -> fprintf fm "EOD"
  | Const c -> print_const {cfg with top=false} fm c
  | Var x -> print_id fm x
  | Fun(x,t1) ->
      let xs,t =
        if !!Debug.check then
          [x], t1
        else
          decomp_funs {desc; typ=typ_unknown; attr=[]}
      in
      let fv = get_fv t in
      let p = 15 in
      let s1,s2 = paren pri (p+1) in
      fprintf fm "%s@[<hov 2>fun@[%a@] ->@ %a%s@]" s1 (print_ids ~fv {cfg with top=false}) xs (pr_t 0) t s2
  | App({desc=Const(Rand(TBase TInt,false))}, [{desc=Const Unit}]) when cfg.as_ocaml ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "@[<hov 2>%sRandom.int 0%s@]" s1 s2
  | App(t, ts) ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "@[<hov 2>%s%a@ %a%s@]" s1 (pr_t p) t (print_termlist {cfg with top=false} p) ts s2
  | If(t1, t2, {desc=Bottom}) when not !!Debug.check && (not cfg.as_ocaml || cfg.for_dmochi) ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[assume%a %a;@ %a@]%s" s1 (print_if_label cfg) attr (pr_t p) t1 (pr_t p) t2 s2
  | If(t1, {desc=Const Unit}, {desc=App({desc=Event("fail",_)}, [{desc=Const Unit}])}) when not !!Debug.check ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "@[<hov 2>%sassert%a %a%s@]" s1 (print_if_label cfg) attr (pr_t p) t1 s2
  | If(t1, t2, t3) ->
      let p = 10 in
      let s1,s2 = paren pri (if t3.desc = Const Unit then p else p+1) in
      fprintf fm "%s@[<hv>if%a@[@ %a@]@ then@ " s1 (print_if_label cfg) attr (pr_t p) t1;
      pp_print_if_newline fm ();
      pp_print_string fm "  ";
      fprintf fm "@[%a@]" (pr_t p) t2;
      if t3.desc <> Const Unit then
        begin
          fprintf fm "@ else@ ";
          pp_print_if_newline fm ();
          pp_print_string fm "  ";
          fprintf fm "@[%a@]" (pr_t p) t3
        end;
      fprintf fm "@]%s" s2
  | Local(Decl_let [], t) ->
      Format.eprintf "@.%a@." (pr_t 0) t;
      assert false
  | Local(Decl_let _, _) when cfg.top && is_definitions desc ->
      let decls,_ = decomp_locals {desc;typ=Ty.unit;attr=[]} in
      print_decls cfg fm decls
  | Local(Decl_let [_, {desc=App({desc=Event("fail",_)}, [{desc=Const Unit}])}], {desc=Bottom}) ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "@[%sassert@ false%s@]" s1 s2
  | Local(Decl_let [u,t1], t2) when not !!Debug.check && Id.typ u = TBase TUnit && not @@ Id.mem u @@ get_fv t2 ->
      let p = 9 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[%a;@ %a@]%s" s1 (pr_t p) t1 (pr_t' p) t2 s2
  | Local(decl, t2) ->
      let p = 10 in
      let s1,s2 = paren pri (p+1) in
      let bang = List.mem ADoNotInline attr && not cfg.as_ocaml in
      fprintf fm "%s@[<v>@[<hv>%a@]@ in@ @[<hov>%a@]@]%s" s1 (print_decl {cfg with top=false} bang) decl (pr_t' p) t2 s2
  | Not{desc = BinOp(Eq, t1, t2)} ->
      let p = 50 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[%a@ <>@ %a@]%s" s1 (pr_t p) t1 (pr_t p) t2 s2
  | BinOp((Eq|Leq|Geq|Lt|Gt), {desc=App({desc=Const(Rand(TBase TInt,false))}, [{desc=Const Unit}])}, {desc=Const _})
  | BinOp((Eq|Leq|Geq|Lt|Gt), {desc=Const _}, {desc=App({desc=Const(Rand(TBase TInt,false))}, [{desc=Const Unit}])}) ->
      let p = 80 in
      let s1,s2 = paren pri p in
      if cfg.as_ocaml then
        fprintf fm "%sRandom.bool@ ()%s" s1 s2
      else
        fprintf fm "%srand_bool@ ()%s" s1 s2
  | BinOp(Mult, {desc=Const (Int -1)}, {desc=Var x}) ->
      let p = 70 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[-%a@]%s" s1 print_id x s2
  | BinOp(op, t1, t2) ->
      let p = match op with Mult|Div -> 70 | Add|Sub -> 65 | And -> 40 | Or -> 30 | _ -> 50 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[%a@ %a@ %a@]%s" s1 (pr_t p) t1 print_binop op (pr_t p) t2 s2
  | Not t ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[not@ %a@]%s" s1 (pr_t p) t s2
  | Event(s,false) -> fprintf fm "<%s>" s
  | Event("fail",true) when cfg.as_ocaml -> fprintf fm "(fun () _ -> assert false)"
  | Event(s,true) -> fprintf fm "<|%s|>" s
  | Record fields ->
      let aux fm (s,t) = fprintf fm "%s=%a" s (pr_t 0) t in
      fprintf fm "{%a}" (print_list aux ";@ ") fields
  | Field(t,s) -> fprintf fm "%a.%s" (pr_t 9) t s
  | SetField(t1,s,t2) -> fprintf fm "%a.%s@ <-@ %a" (pr_t 9) t1 s (pr_t 3) t2
  | Nil -> fprintf fm "[]"
  | Cons(t1,t2) ->
      let rec decomp_list desc =
        match desc with
        | Nil -> Some []
        | Cons(t1, t2) -> Option.map (List.cons t1) @@ decomp_list t2.desc
        | _ -> None
      in
      begin
        match decomp_list desc with
        | None ->
            let p = 60 in
            let s1,s2 = paren pri p in
            fprintf fm "%s@[%a::@,%a@]%s" s1 (pr_t p) t1 (pr_t p) t2 s2
        | Some ts' ->
            Format.fprintf fm "%a" (List.print @@ pr_t 0) ts'
      end
  | Constr(s,ts) ->
      let p = 80 in
      let s1,s2 = paren pri p in
      if ts = []
      then pp_print_string fm s
      else fprintf fm "%s@[%s(%a)@]%s" s1 s (print_list (pr_t 20) ",") ts s2
  | Match(t,pats) ->
      let pats' =
        if cfg.as_ocaml then
          match (fst (List.last pats)).pat_desc with
          | PAny
            | PVar _ -> pats
          | _ -> pats @ [{pat_desc=PAny;pat_typ=typ_unknown}, {desc=Bottom; typ=typ_unknown; attr=[]}]
        else
          pats
      in
      let p = 10 in
      let s1,s2 = paren pri p in
      let first = ref true in
      let aux (pat,t) =
        fprintf fm "@ @[<hov 4>";
        if !first then pp_print_if_newline fm ();
        first := false;
        pp_print_string fm "| ";
        fprintf fm "@[<hov 2>%a ->@ %a@]@]" (print_pattern cfg) pat (pr_t p) t
      in
      fprintf fm "%s@[<hv>@[@[<hov 2>match@ %a@]@ with@]" s1 (pr_t p) t;
      List.iter aux pats';
      fprintf fm "@]%s" s2
  | Raise t ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[raise@ %a@]%s" s1 (pr_t p) t s2
  | TryWith(t1,{desc=Fun(e,{desc=Match({desc=Var e'},pats)})})
       when Id.(e = e') && (function ({pat_desc=PAny},{desc=Raise {desc=Var e''}}) -> Id.same e e'' | _ -> false) @@ List.last pats ->
      let p = 10 in
      let s1,s2 = paren pri (p+1) in
      let aux (pat,t) =
        let bar = if List.length pats = 2 then "" else "| " in
        fprintf fm "@ @[<hov 4>%s@[<hov 2>%a ->@]@ %a@]" bar (print_pattern cfg) pat (pr_t p) t
      in
      fprintf fm "%s@[@[<hov 2>try@ %a@]@ @[<hv 2>with" s1 (pr_t p) t1;
      List.iter aux @@ fst @@ List.decomp_snoc pats;
      fprintf fm "@]@]%s" s2
  | TryWith(t1,t2) ->
      let p = 10 in
      let s1,s2 = paren pri (p+1) in
      fprintf fm "%s@[@[<hov 2>try@ %a@]@ with@ %a@]%s" s1 (pr_t p) t1 (pr_t p) t2 s2
  | Tuple ts ->
      let p = 20 in
      fprintf fm "@[(%a)@]" (print_list (pr_t p) ",@ ") ts
  | Proj(0,t) when tuple_num t.typ = Some 2 ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[fst@ %a@]%s" s1 (pr_t p) t s2
  | Proj(1,t) when tuple_num t.typ = Some 2 ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[snd@ %a@]%s" s1 (pr_t p) t s2
  | Proj(i,t) when cfg.as_ocaml ->
      let p = 80 in
      let s1,s2 = paren pri p in
      let s = "fun (" ^ String.join "," (List.init (Option.get @@ tuple_num t.typ) (fun j -> if i = j then "x" else "_") ) ^ ") -> x" in
      fprintf fm "%s@[(%s)@ %a@]%s" s1 s (pr_t p) t s2
  | Proj(i,t) ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[#%d@ %a@]%s" s1 i (pr_t p) t s2
  | Bottom when cfg.as_ocaml -> fprintf fm "let rec bot() = bot() in bot()"
  | Bottom -> fprintf fm "_|_"
  | Label(info, t) ->
      fprintf fm "(@[label[@[%a@]]@ %a@])" print_info info (pr_t 80) t
  | Ref t ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[ref@ %a@]%s" s1 (pr_t p) t s2
  | Deref t ->
      let p = 90 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[!%a@]%s" s1 (pr_t p) t s2
  | SetRef(t1, t2) ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[%a := %a@]%s" s1 (pr_t p) t1 (pr_t p) t2 s2
  | TNone -> fprintf fm "None"
  | TSome t ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[Some %a@]%s" s1 (pr_t p) t s2
  | Module decls ->
      let p = 10 in
      let s1,s2 = paren pri (p+1) in
      fprintf fm "%s@[<v>@[<v 2>module@ @[%a@]@]@ end@]%s" s1 (print_decls {cfg with top=true}) decls s2



and print_info fm info =
  match info with
  | InfoId x ->
      fprintf fm "Id %a" print_id x
  | InfoString s ->
      fprintf fm "String %S" s
  | InfoInt n ->
      fprintf fm "Int %d" n
  | InfoTerm t ->
      fprintf fm "Term %a" (print_term {!config_default with ty=false} 80) t
  | InfoIdTerm(x,t) ->
      fprintf fm "IdTerm(%a,@ %a)" print_id x (print_term {!config_default with ty=false} 80) t



and print_pattern cfg fm pat =
  let pr_p = print_pattern cfg in
  match pat.pat_desc with
  | PAny -> pp_print_string fm "_"
  | PNondet -> pp_print_string fm "*"
  | PVar x -> print_id fm x
  | PAlias(p,x) -> fprintf fm "(%a as %a)" pr_p p print_id x
  | PConst c -> print_term cfg 1 fm c
  | PConstr(c,pats) ->
      let aux' = function
          [] -> ()
        | [pat] -> fprintf fm "(%a)" pr_p pat
        | pat::pats ->
            fprintf fm "(%a" pr_p pat;
            List.iter (fun pat -> fprintf fm ",%a" pr_p pat) pats;
            pp_print_string fm ")"
      in
      pp_print_string fm c;
      aux' pats
  | PNil -> fprintf fm "[]"
  | PCons(p1,p2) -> fprintf fm "%a::%a" pr_p p1 pr_p p2
  | PRecord pats ->
      let aux' = function
          [] -> ()
        | [_,pat] -> fprintf fm "{%a}" pr_p pat
        | (_,pat)::pats ->
            fprintf fm "{%a" pr_p pat;
            List.iter (fun (_,pat) -> fprintf fm ",%a" pr_p pat) pats;
            pp_print_string fm "}"
      in
      aux' pats
  | POr(pat1,pat2) -> fprintf fm "(%a | %a)" pr_p pat1 pr_p pat2
  | PTuple pats -> fprintf fm "(%a)" (print_list pr_p ", ") pats
  | PNone -> fprintf fm "None"
  | PSome p -> fprintf fm "(Some %a)" pr_p p
  | PWhen(p,cond) -> fprintf fm "%a when@ @[<hov 2>%a@]" pr_p p (print_term cfg 1) cond
let print_term cfg fm = print_term cfg 0 fm

let rec print_term' pri fm t =
  fprintf fm "(@[";(
    match t.desc with
    | End_of_definitions -> fprintf fm "EOD"
    | Const c -> print_const !config_default fm c
    | Var x when t.typ = Id.typ x -> print_id fm x
    | Var x -> print_id_typ fm x
    | Fun(x, t) ->
        let p = 2 in
        let s1,s2 = paren pri p in
        fprintf fm "%sfun %a -> %a%s" s1 print_id x (print_term' p) t s2
    | App(t, ts) ->
        let p = 8 in
        let s1,s2 = paren pri p in
        fprintf fm "%s%a@ %a%s" s1 (print_term' p) t (print_termlist' p) ts s2
    | If(t1, t2, t3) ->
        let p = 1 in
        let s1,s2 = paren pri (p+1) in
        fprintf fm "%s@[@[if %a@]@ then @[%a@]@ else @[%a@]@]%s"
                s1 (print_term' p) t1 (print_term' p) t2 (print_term' p) t3 s2
    | Local(Decl_let bindings, t2) ->
        let s_rec = if is_non_rec bindings then "" else " rec" in
        let p = 10 in
        let s1,s2 = paren pri (p+1) in
        let b = ref true in
        let print_binding fm (f,t1) =
          let xs,t1' = decomp_funs t1 in
          let pre = if !b then "let" ^ s_rec else "and" in
          fprintf fm "@[<hov 2>%s%a =@ %a@ @]" pre (print_ids {!config_default with ty=true}) (f::xs) (print_term' p) t1';
          b := false
        in
        let print_bindings bs = print_list print_binding "" bs in
        begin
          match t2.desc with
          | Local _ -> fprintf fm "%s@[<v>@[<hov 2>%a@]@ in@ %a@]%s"
                               s1 print_bindings bindings (print_term' p) t2 s2
          | _ -> fprintf fm     "%s@[<v>@[<hov 2>%a@]@ @[<v 2>in@ @]@[<hov>%a@]@]%s"
                         s1 print_bindings bindings (print_term' p) t2 s2
        end
    | Local(Decl_type decls, t) ->
        let p = 10 in
        let s1,s2 = paren pri (p+1) in
        let b = ref true in
        let print_decl fm (name,ty) =
          let pre = if !b then "type" else "and" in
          fprintf fm "@[<hov 2>%s @[<hov 2>%s@] =@ %a@]" pre name print_typ ty;
          b := false
        in
        let print_decls bs = print_list print_decl "@ " ~last:true bs in
        fprintf fm "%s@[<v>@[<hv>%a@]in@ @[<hov>%a@]@]%s" s1 print_decls decls (print_term' p) t s2
    | BinOp(op, t1, t2) ->
        let p = match op with Add|Sub|Mult|Div -> 6 | And -> 4 | Or -> 3 | _ -> 5 in
        let s1,s2 = paren pri p in
        fprintf fm "%s%a %a %a%s" s1 (print_term' p) t1 print_binop op (print_term' p) t2 s2
    | Not t ->
        let p = 6 in
        let s1,s2 = paren pri p in
        fprintf fm "%snot %a%s" s1 (print_term' p) t s2
    | Event(s,b) -> fprintf fm "{%s}" s
    | Record fields ->
        let aux fm (s,t) = fprintf fm "%s=%a" s (print_term' 0) t in
        fprintf fm "{%a}" (print_list aux ";@ ") fields
    | Field(t,s) -> fprintf fm "%a.%s" (print_term' 9) t s
    | SetField(t1,s,t2) -> fprintf fm "%a.%s <- %a" (print_term' 9) t1 s (print_term' 3) t2
    | Nil -> fprintf fm "[]"
    | Cons(t1,t2) ->
        let p = 7 in
        let s1,s2 = paren pri (p+1) in
        fprintf fm "%s%a::%a%s" s1 (print_term' p) t1 (print_term' p) t2 s2
    | Constr(s,ts) ->
        let p = 8 in
        let s1,s2 = paren pri p in
        let aux fm = function
            [] -> ()
          | [t] -> fprintf fm "(%a)" (print_term' 1) t
          | t::ts ->
              fprintf fm "(%a" (print_term' 1) t;
              List.iter (fun t -> fprintf fm ",%a" (print_term' 1) t) ts;
              pp_print_string fm ")"
        in
        fprintf fm "%s%s%a%s" s1 s aux ts s2
    | Match(t,pats) ->
        let p = 1 in
        let s1,s2 = paren pri (p+1) in
        let aux (pat,t) = fprintf fm "%a -> %a@ " print_pattern' pat (print_term' p) t in
        fprintf fm "%s@[match %a with@ " s1 (print_term' p) t;
        List.iter aux pats;
        fprintf fm "@]%s" s2
    | Raise t ->
        let p = 4 in
        let s1,s2 = paren pri (p+1) in
        fprintf fm "%sraise %a%s" s1 (print_term' 1) t s2
    | TryWith(t1,t2) ->
        let p = 1 in
        let s1,s2 = paren pri (p+1) in
        fprintf fm "%stry %a with@ %a%s" s1 (print_term' p) t1 (print_term' p) t2 s2
    | Tuple ts ->
        fprintf fm "@[(%a)@]" (print_list (print_term' 0) ",@ ") ts
    | Proj(0,t) when tuple_num t.typ = Some 2 ->
        let p = 4 in
        let s1,s2 = paren pri (p+1) in
        fprintf fm "%s@[fst %a@]%s" s1 (print_term' 1) t s2
    | Proj(1,t) when tuple_num t.typ = Some 2 ->
        let p = 4 in
        let s1,s2 = paren pri (p+1) in
        fprintf fm "%s@[snd %a@]%s" s1 (print_term' 1) t s2
    | Proj(i,t) ->
        let p = 4 in
        let s1,s2 = paren pri (p+1) in
        fprintf fm "%s@[#%d %a@]%s" s1 i (print_term' 1) t s2
    | Bottom -> fprintf fm "_|_"
    | Label(info, t) ->
        fprintf fm "(@[label[%a]@ %a@])" print_info info (print_term' 0) t
    | Ref t ->
        let p = 4 in
        let s1,s2 = paren pri (p+1) in
        fprintf fm "%sref %a%s" s1 (print_term' 1) t s2
    | Deref t ->
        let p = 4 in
        let s1,s2 = paren pri (p+1) in
        fprintf fm "%s!%a%s" s1 (print_term' 1) t s2
    | SetRef(t1,t2) ->
        let p = 4 in
        let s1,s2 = paren pri (p+1) in
        fprintf fm "%s%a := %a%s" s1 (print_term' 1) t1 (print_term' 1) t2 s2
    | TNone -> fprintf fm "None"
    | TSome t ->
        let p = 4 in
        let s1,s2 = paren pri (p+1) in
        fprintf fm "%sSome %a%s" s1 (print_term' 1) t s2
    | Module decls ->
        let p = 10 in
        let s1,s2 = paren pri (p+1) in
        fprintf fm "@[%s@[<hv 2>module@ @[%a@]@]@ end%s@]" s1 print_declaration' decls s2
  );fprintf fm ":@ @[%a@]@])" (Color.cyan print_typ) t.typ

and print_declaration' fm decls = (* TODO: fix *)
  let t =
    let aux decl t0 = {desc=Local(decl,t0);typ=t0.typ;attr=[]} in
    List.fold_right aux decls {desc=End_of_definitions; typ=TBase TUnit; attr=[]}
  in
  print_term' 0 fm t

and print_pattern' fm pat =
  let rec aux fm pat =
    match pat.pat_desc with
    | PAny -> pp_print_string fm "_"
    | PNondet -> pp_print_string fm "*"
    | PVar x -> print_id_typ fm x
    | PAlias(p,x) -> fprintf fm "(%a as %a)" aux p print_id x
    | PConst c -> print_term' 1 fm c
    | PConstr(c,pats) ->
        let aux' = function
            [] -> ()
          | [pat] -> fprintf fm "(%a)" aux pat
          | pat::pats ->
              fprintf fm "(%a" aux pat;
              List.iter (fun pat -> fprintf fm ",%a" aux pat) pats;
              pp_print_string fm ")"
        in
        pp_print_string fm c;
        aux' pats
    | PNil -> fprintf fm "[]"
    | PCons(p1,p2) -> fprintf fm "%a::%a" aux p1 aux p2
    | PRecord pats ->
        let aux' = function
            [] -> ()
          | [_,pat] -> fprintf fm "{%a}" aux pat
          | (_,pat)::pats ->
              fprintf fm "{%a" aux pat;
              List.iter (fun (_,pat) -> fprintf fm ",%a" aux pat) pats;
              pp_print_string fm "}"
        in
        aux' pats
    | POr(pat1,pat2) -> fprintf fm "(%a | %a)" aux pat1 aux pat2
    | PTuple pats -> fprintf fm "(%a)" (print_list aux ", ") pats
    | PNone -> fprintf fm "None"
    | PSome p -> fprintf fm "(Some %a)" aux p
    | PWhen(p,cond) -> fprintf fm "%a when@ @[<hov 2>%a@]@ " aux p (print_term' 1) cond
  in
  fprintf fm "| %a" aux pat

and print_termlist' pri = print_list (print_term' pri) "@ "


let print_defs fm (defs:(id * (id list * term)) list) =
  let print_fundef (f, (xs, t)) =
    fprintf fm "%a %a-> %a.\n" print_id f (print_ids {!config_default with ty=false}) xs (print_term {!config_default with ty=false}) t
  in
  List.iter print_fundef defs


let string_of_const c = Format.asprintf "%a" (print_const !config_default) c
let string_of_binop op = Format.asprintf "%a" print_binop op
let string_of_typ typ = Format.asprintf "%a" print_typ typ
let string_of_constr t =
  match t.desc with
  | End_of_definitions -> "End_of_definitions"
  | Const _ -> "Const"
  | Var _ -> "Var"
  | Fun _ -> "Fun"
  | App _ -> "App"
  | If _ -> "If"
  | Local _ -> "Local"
  | BinOp _ -> "BinOp"
  | Not _ -> "Not"
  | Event _ -> "Event"
  | Record _ -> "Record"
  | Field _ -> "Field"
  | SetField _ -> "SetField"
  | Nil -> "Nil"
  | Cons _ -> "Cons"
  | Constr _ -> "Constr"
  | Match _ -> "Match"
  | Raise _ -> "Raise"
  | TryWith _ -> "TryWith"
  | Tuple _ -> "Tuple"
  | Proj _ -> "Proj"
  | Bottom -> "Bottom"
  | Label _ -> "Label"
  | Ref _ -> "Ref"
  | Deref _ -> "Deref"
  | SetRef _ -> "SetRef"
  | TNone -> "TNone"
  | TSome _ -> "TSome"
  | Module _ -> "Module"


let typ = print_typ
let id = print_id
let id_typ = print_id_typ
let pattern = print_pattern !config_default
let const fm = print_const !config_default fm
let desc fm = print_desc !config_default 0 [] fm
let term fm = print_term !config_default fm
let term_top fm = print_term {!config_default with top=true} fm
let term' = print_term' 0
let term_typ fm = print_term {!config_default with ty=true} fm
let term_typ_top fm = print_term {!config_default with ty=true; top=true} fm
let defs = print_defs
let constr fm = pp_print_string fm -| string_of_constr
let attr = print_attr_list
let decls = print_decls {!config_default with ty=false; top=true}
let as_ocaml fm t =
  Id.tmp_set_print_as_ocaml @@ fun () ->
  Type.tmp_set_print_as_ocaml @@ fun () ->
  print_term {!config_default with top=true; as_ocaml=true} fm t
let as_ocaml_typ fm t =
  Id.tmp_set_print_as_ocaml @@ fun () ->
  Type.tmp_set_print_as_ocaml @@ fun () ->
  print_term {!config_default with ty=true; top=true; as_ocaml=true} fm t
let term_custom = print_term

let int = Format.pp_print_int
let float = Format.pp_print_float
let char = Format.pp_print_char
let bool = Format.pp_print_bool
let string = Format.pp_print_string
let option = Option.print
let pair = Pair.print
let ( * ) = pair
let triple = Triple.print
let list = List.print
let ignore s fm _ = Format.pp_print_string fm s
let __ fm x = ignore "" fm x
