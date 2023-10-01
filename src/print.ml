[@@@alert "-unsafe"]

open Format
open Util
open Type
open Type_util
open Syntax

module Debug_attr = Debug.Make(struct let check = Flag.Debug.make_check (__MODULE__ ^ ".attr") end)
module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type config =
    {ty : bool;         (** print types of arguments *)
     as_ocaml : bool;   (** print terms in OCaml syntax *)
     for_dmochi : bool; (** print terms for dmochi when as_ocaml=true *)
     top : bool;        (** print let/type as in top-level *)
     unused : bool;     (** print unused arguments *)
     depth : int;       (** max length of printing terms *)
     length : int;      (** max depth of printing terms *)
     omit_id : id list} (** variables whose names are unique *)
let config_default =
  ref {ty = false;
       as_ocaml = false;
       for_dmochi = false;
       top = false;
       unused = false;
       depth = -1;
       length = -1;
       omit_id = []}

let set_as_ocaml () =
  Id.set_print_as_ocaml ();
  Print_typ.set_print_as_ocaml ();
  config_default := {!config_default with as_ocaml=true}
let set_unused () =
  config_default := {!config_default with unused=true}
let set_depth depth =
  config_default := {!config_default with depth}
let set_length length =
  Print_typ.set_print_length length;
  Tenv.set_print_length length;
  config_default := {!config_default with length}

let is_definitions desc =
  (snd @@ decomp_locals (make_raw desc Ty.unit)).desc = End_of_definitions

let print_location fm {Location.loc_start} = Lexing.print_position fm loc_start

let print_dots fm = Color.s_yellow fm "..."

let rec print_typ fm t = Print_typ.typ ~occur:occur_typ (print_term {!config_default with ty=false} 0) fm t
and print_ids ?fv cfg fm xs =
  if xs <> [] then
    let xs' =
      match fv with
      | None -> xs
      | Some _ when !!Debug.check || cfg.unused -> xs
      | Some fv ->
          xs
          |> List.map (fun x ->
                 if Id.List.mem x fv then
                   x
                 else if Id.typ x = TBase TUnit then
                   Id.make "()" (TBase TUnit)
                 else
                   Id.make "_" @@ Id.typ x)
    in
    let p_id = if cfg.ty then print_id_typ else print_id in
    print_list (p_id cfg) "@ " ~first:true fm xs'

(*
  and print_id fm x = fprintf fm "(%a:%a)" Id.print x print_typ (Id.typ x)
 *)
and print_id cfg fm x =
  if not !Flag.Print.var_id && (Id.List.mem x cfg.omit_id || is_mod_var x) then
    pp_print_string fm @@ Id.name x
  else
    Id.print fm x

and print_id_typ cfg fm x = fprintf fm "(@[%a:%a@])" (print_id cfg) x (Color.cyan print_typ) (Id.typ x)

and print_lid cfg fm (lid:lid) = Lid.print_gen (print_id cfg) fm lid
and print_lid_typ cfg fm x = fprintf fm "(@[%a:%a@])" (print_lid cfg) x (Color.cyan print_typ) (Lid.typ x)

(* priority (low -> high)
   9 : Seq
   10 : Local, If, Match, TryWith
   15 : Fun
   20 : Pair
   30 : Or
   40 : And
   50 : Eq, Lt, Gt, Leq, Geq, MemSet, Subset
   60 : Cons, AddSet
   65 : Add, Sub
   70 : Mult, Div
   80 : Raise, App, Not, Ref, SetRef
   90 : Field
   100 : Deref
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
  print_list ~limit:cfg.length (print_term cfg pri) "@ " fm ts

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
  | Empty -> fprintf fm "∅"
  | Dummy _ when cfg.as_ocaml -> fprintf fm "(Obj.magic 0)"
  | Dummy ty -> fprintf fm "dummy[%a]" print_typ ty

and print_attr cfg fm = function
  | AAbst_under -> fprintf fm "AAbst_under"
  | ATerminate -> fprintf fm "ATerminate"
  | ANotFail -> fprintf fm "ANotFail"
  | ADeterministic -> fprintf fm "ADeterministic"
  | AComment s -> fprintf fm "AComment %S" s
  | AId n -> fprintf fm "AId %d" n
  | ADoNotInline -> fprintf fm "ADoNotInline"
  | AEffect e -> List.print Print_typ.effect fm e
  | ALoc l -> fprintf fm "@[%a@]" print_location l
  | AMark b -> fprintf fm "AMark %b" !b
  | AInfo info -> fprintf fm "AInfo %a" (print_info cfg) info
  | AFV fv -> fprintf fm "AFV [@[%a@]]" (print_list Id.print ",@ ") fv

and print_attr_list cfg fm attrs =
  List.print (print_attr cfg) fm attrs

and is_ignore_attr a =
  match a with
  | ADoNotInline -> true
  | AFV _ -> true
  | ALoc _ -> true
  | _ -> List.mem a const_attr

and decomp_comment a =
  match a with
  | AComment s -> Some s
  | _ -> None

and filter_attr_list attr =
  if !!Debug_attr.check then
    attr
  else
    attr
    |> List.filter_out is_ignore_attr
    |> List.filter (Option.is_none -| decomp_comment)
    |> List.filter_out (function AMark _ -> true | _ -> false)
    |&!Flag.Print.only_if_id&> List.filter (function AId _ -> false | _ -> true)

and print_term cfg pri fm t =
  if cfg.depth = 0 then
    print_dots fm
  else
    let cfg' = {cfg with depth=cfg.depth-1} in
    let pr attr fm desc =
      let comments = List.filter_map decomp_comment t.attr in
      if comments = [] || !!Debug_attr.check
      then fprintf fm "@[%a@]" (print_desc cfg' pri attr) desc
      else fprintf fm "(@[(* @[%a@] *)@ %a@])" (print_list pp_print_string ", ") comments (print_desc cfg' pri attr) desc
    in
    let attr = filter_attr_list t.attr in
    let marked = List.exists (function AMark b -> !b | _ -> false) t.attr in
    if marked then fprintf fm "@,%a%s@\n" Color.set Color.Red (String.make (Format.pp_get_margin fm ()) '<');
    if attr = [] || cfg.as_ocaml then
      pr t.attr fm t.desc
    else
      fprintf fm "(@[%a@ %a#@ %a%t@])" (pr t.attr) t.desc Color.set Color.Yellow (print_attr_list cfg') attr Color.reset;
    if marked then fprintf fm "@\n%s%t@\n" (String.make (Format.pp_get_margin fm ()) '>') Color.reset

and print_let_decls cfg bang fm bindings =
  let first = ref true in
  let non_rec = is_non_rec bindings in
  let is_module = List.exists (fun (_,t) -> is_module t || is_functor ~default:false [] t) bindings in
  let print_binding fm (f,t1) =
    let pre =
      let s_rec =
        if is_module then
          " module"
        else if non_rec then
          ""
        else
          " rec"
      in
      if !first then
        "let" ^ (if bang then "!" else "") ^ s_rec
      else
        "and"
    in
    let xs,t1' = if !!Debug.check || is_module then [], t1 else decomp_funs t1 in
    let fv = get_fv t1' in
    let cfg = update_omit_id ~bv:xs ~fv:Id.List.Set.(fv - xs) cfg in
    let pr_ty fm = if cfg.ty then Format.fprintf fm " : %a" (Color.cyan print_typ) t1'.typ in
    fprintf fm "@[<hov 2>%s @[<hov 2>%a%a%t@] =@ %a@]" pre (print_id cfg) f (print_ids ~fv cfg) xs pr_ty (print_term cfg 0) t1';
    first := false
  in
  print_list ~limit:cfg.length print_binding "@ " fm bindings

and print_type_decls cfg fm defs =
  let b = ref true in
  let pr_decl fm (c,(params,ty)) =
    let pre = if !b then "type" else "and" in
    fprintf fm "@[<hov 2>%s %a%a =@ %a@]" pre print_params params Print_typ.constr c print_typ ty;
    b := false
  in
  let box = Format.pp_open_vbox -$- 0 in
  print_list ~box ~limit:cfg.length pr_decl "@ " fm defs

and print_params fm params =
  match params with
  | [] -> ()
  | [ty] -> Format.fprintf fm "%a " print_typ ty
  | _ -> Format.fprintf fm "(%a) " (print_list print_typ ",") params

and print_decl cfg bang fm decl =
  match decl with
  | Decl_type decls -> print_type_decls cfg fm decls
  | Decl_let bindings -> print_let_decls cfg bang fm bindings
  | Type_ext (Ext_type(s, (params, row))) ->
      let ty = TVariant(VNonPoly, [row_of_ext_row row]) in
      if C.is_exn s then
        Format.fprintf fm "@[<hov 2>exception %a@]" print_typ ty
      else
        Format.fprintf fm "@[<hov 2>type %a%a +=@ %a@]" print_params params Print_typ.path s print_typ ty
  | Type_ext (Ext_rebind(s1, s2)) ->
      Format.fprintf fm "@[<hov 2>exception %a =@ %a@]" Print_typ.constr s1 Print_typ.path s2
  | Include t ->
      Format.fprintf fm "@[<hov 2>include@ %a@]" (print_term cfg 0) t
  | Decl_multi [] -> Format.fprintf fm "let _"
  | Decl_multi _ -> print_decls cfg fm (decomp_Decl_multi decl)

and print_decls ?(indent="") cfg fm decls =
  let pr fm decl = Format.fprintf fm "%s%a" indent (print_decl cfg false) decl in
  Format.fprintf fm "%a" (print_list ~limit:cfg.length pr "@\n") decls

and print_if_label cfg fm attr =
  if !Flag.Print.only_if_id && not cfg.as_ocaml then
    match List.find_opt (function AId _ -> true | _ -> false) attr with
    | Some (AId n) -> Format.fprintf fm "^%d" n
    | _ -> ()

and update_omit_id ~bv ~fv cfg =
  let eq = Compare.eq_on Id.name in
  let omit_id =
    bv
    |> List.filter (fun x -> List.count (eq x) bv = 1)
    |> List.filter_out (List.mem ~eq -$- fv)
    |> (-$-) (@@@) cfg.omit_id
  in
  {cfg with omit_id}

and print_desc cfg pri attr fm desc =
  let pr_t ?(cfg=cfg) = print_term {cfg with top=false} in
  let pr_t' ?(cfg=cfg) pri fm t = (* for printing subterms of [Local] *)
    match t.desc with
    | Local _ -> print_term {cfg with top=false; depth=cfg.depth+1} pri fm t
    | _ -> pr_t ~cfg pri fm t
  in
  let bv_decls = List.concat_map (function Decl_let defs -> List.map fst defs | _ -> []) in
  match desc with
  | End_of_definitions when cfg.as_ocaml -> fprintf fm "()"
  | End_of_definitions -> fprintf fm "EOD"
  | Const c -> print_const {cfg with top=false} fm c
  | Var x -> print_lid cfg fm x
  | Fun(x,t1) when is_functor ~default:false [] t1 || is_module t1 ->
      let p = 15 in
      let s1,s2 = paren pri (p+1) in
      fprintf fm "%s@[<hov 2>functor @[%a@] ->@ %a%s@]" s1 (print_id cfg) x (pr_t 0) t1 s2
  | Fun(x,t1) ->
      let xs,t =
        if !!Debug.check then
          [x], t1
        else
          decomp_funs (make_raw desc typ_unknown)
      in
      let fv = get_fv t in
      let cfg = update_omit_id ~bv:xs ~fv:Id.List.Set.(fv - xs) cfg in
      let p = 15 in
      let s1,s2 = paren pri (p+1) in
      fprintf fm "%s@[<hov 2>fun@[%a@] ->@ %a%s@]" s1 (print_ids ~fv {cfg with top=false}) xs (pr_t ~cfg 0) t s2
  | App(_, []) -> assert false
  | App({desc=Const(Rand(TBase TInt,false))}, [{desc=Const Unit}]) when cfg.as_ocaml ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "@[<hov 2>%sRandom.int 0%s@]" s1 s2
  | App(t, ts) when is_functor ~default:false [] t ->
      let p = 80 in
      let s1,s2 = paren pri p in
      let pr fm = fprintf fm "(@[%a@])" (pr_t 0) in
      fprintf fm "@[<hov 2>%s%a%a%s@]" s1 (pr_t p) t (print_list ~limit:cfg.length pr "") ts s2
  | App({desc=Event("fail",_)}, [{desc=Const Unit}]) ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "@[%sassert@ false%s@]" s1 s2
  | App(t, ts) ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "@[<hov 2>%s%a@ %a%s@]" s1 (pr_t p) t (print_termlist {cfg with top=false} p) ts s2
  | If(t1, t2, {desc=Bottom}) when not !!Debug.check && (not cfg.as_ocaml || cfg.for_dmochi) ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[assume%a %a;@ %a@]%s" s1 (print_if_label cfg) attr (pr_t p) t1 (pr_t p) t2 s2
  | If _ when not !!Debug.check && is_assert_desc desc ->
      let t1 = Option.get @@ decomp_assert_desc desc in
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
  | Local(Decl_let [], t) when !Flag.Debug.minimize ->
      pr_t pri fm t
  | Local(Decl_let [], t) -> pr_t pri fm t
  | Local(Decl_let _, _) when cfg.top && is_definitions desc ->
      let decls,_ = decomp_locals (make_raw desc Ty.unit) in
      let fv = get_fv (make desc Ty.unknown) in
      let cfg = update_omit_id ~bv:(bv_decls decls) ~fv cfg in
      print_decls cfg fm decls
  | Local(Decl_let [_, {desc=App({desc=Event("fail",_)}, [{desc=Const Unit}])}], {desc=Bottom}) ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "@[%sassert@ false%s@]" s1 s2
  | Local(Decl_let [u,t1], t2) when not !!Debug.check && Id.typ u = TBase TUnit && not @@ Id.List.mem u @@ get_fv t2 && t2.desc <> End_of_definitions ->
      let p = 9 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[%a;@ %a@]%s" s1 (pr_t p) t1 (pr_t' p) t2 s2
  | Local(decl, t2) ->
      let p = 10 in
      let s1,s2 = paren pri (p+1) in
      let bang = List.mem ADoNotInline attr && not cfg.as_ocaml in
      let fv = get_fv (make desc Ty.unknown) in
      let cfg = update_omit_id ~fv ~bv:(bv_decls [decl]) cfg in
      fprintf fm "%s@[<hov>@[<hv>%a@]@ in@ @[<hov>%a@]@]%s" s1 (print_decl {cfg with top=false} bang) decl (pr_t' ~cfg p) t2 s2
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
      fprintf fm "%s@[-%a@]%s" s1 (print_lid cfg) x s2
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
      let aux fm (s,t) = fprintf fm "%a=%a" Print_typ.label s (pr_t 0) t in
      fprintf fm "{%a}" (print_list ~limit:cfg.length aux ";@ ") fields
  | Field(t,s) ->
      let p = 90 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[%a.%a@]%s" s1 (pr_t p) t Print_typ.label s s2
  | SetField(t1,s,t2) -> fprintf fm "%a.%a@ <-@ %a" (pr_t 9) t1 Print_typ.label s (pr_t 3) t2
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
  | Constr(b,s,ts) ->
      let p = 80 in
      let s1,s2 = paren pri p in
      let quot = if b then "`" else "" in
      if ts = []
      then fprintf fm "%s%a" quot Print_typ.path s
      else fprintf fm "%s@[%s%a(%a)@]%s" s1 quot Print_typ.path s (print_list ~limit:cfg.length (pr_t 20) ",") ts s2
  | Match(_t1, [{pat_desc=PTuple _ps}, _t2]) when false ->
      assert false
  | Match(t,pats) ->
      let pats' =
        if cfg.as_ocaml then
          match (fst (List.last pats)).pat_desc with
          | PAny
          | PVar _ -> pats
          | _ -> pats @ [make_pattern PAny typ_unknown,
                         make_raw Bottom typ_unknown]
        else
          pats
      in
      let p = 10 in
      let s1,s2 = paren pri p in
      let aux i (pat,t) =
        if cfg.length < 0 || i <= cfg.length then
          begin
            fprintf fm "@ @[<hov 4>";
            if i = 0 then pp_print_if_newline fm ();
            pp_print_string fm "| ";
            if cfg.length >= 0 && i = cfg.length then
              (print_dots fm; Format.fprintf fm "@]")
            else
              let bv = get_bv_pat pat in
              let fv = get_fv t in
              let cfg = update_omit_id ~bv ~fv:Id.List.Set.(fv - bv) cfg in
              fprintf fm "@[<hov 2>%a ->@ %a@]@]" (print_pattern cfg) pat (pr_t ~cfg p) t
          end
      in
      fprintf fm "%s@[<hv>@[@[<hov 2>match@ %a@]@ with@]" s1 (pr_t p) t;
      List.iteri aux pats';
      fprintf fm "@]%s" s2
  | Raise t ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[raise@ %a@]%s" s1 (pr_t p) t s2
  | TryWith(t1,{desc=Fun(e,{desc=Match({desc=Var (LId e')},pats)})})
        when Id.(e = e') && (function ({pat_desc=PAny},{desc=Raise {desc=Var (LId e'')}}) -> Id.same e e'' | _ -> false) @@ List.last pats ->
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
  | Tuple [t] ->
      fprintf fm "@[(%a,)@]" (pr_t 1) t
  | Tuple ts ->
      let p = 20 in
      fprintf fm "@[(%a)@]" (print_list ~limit:cfg.length (pr_t p) ",@ ") ts
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
  | Bottom -> fprintf fm "⊥"
  | Label(info, t) ->
      fprintf fm "(@[label[@[%a@]]@ %a@])" (print_info cfg) info (pr_t 80) t
  | Ref t ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[ref@ %a@]%s" s1 (pr_t p) t s2
  | Deref t ->
      let p = 100 in
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
  | Lazy t ->
      let p = 80 in
      let s1,s2 = paren pri p in
      fprintf fm "%s@[lazy@ %a@]%s" s1 (pr_t p) t s2
  | Module [] ->
      let p = 10 in
      let s1,s2 = paren pri (p+1) in
      fprintf fm "%sstruct end%s" s1 s2
  | Module decls ->
      let p = 10 in
      let s1,s2 = paren pri (p+1) in
      fprintf fm "%s@[<v>struct@\n@[%a@]@\nend@]%s" s1 (print_decls ~indent:"  " {cfg with top=true}) decls s2
  | Pack t ->
      fprintf fm "(module %a : %a)" (pr_t 80) t print_typ t.typ
  | Unpack t ->
      fprintf fm "(val %a)" (pr_t 80) t
  | MemSet(t1, t2) ->
      let p = 50 in
      let s1,s2 = paren pri (p+1) in
      fprintf fm "%s@[%a ∈ %a@]%s" s1 (pr_t p) t1 (pr_t p) t2 s2
  | AddSet(t1, {desc=Const Empty}) ->
      fprintf fm "@[{%a}@]" (pr_t 0) t1
  | AddSet(t1, t2) ->
      let p = 60 in
      let s1,s2 = paren pri (p+1) in
      fprintf fm "%s@[{%a} ∪ %a@]%s" s1 (pr_t p) t1 (pr_t p) t2 s2
  | Subset(t1, t2) ->
      let p = 50 in
      let s1,s2 = paren pri (p+1) in
      fprintf fm "%s@[%a ⊆ %a@]%s" s1 (pr_t p) t1 (pr_t p) t2 s2
  | Forall(x, t1) ->
      let xs,t =
        if !!Debug.check then
          [x], t1
        else
          decomp_forall (make_raw desc typ_unknown)
      in
      let fv = get_fv t in
      let cfg = update_omit_id ~bv:xs ~fv:Id.List.Set.(fv - xs) cfg in
      let p = 15 in
      let s1,s2 = paren pri (p+1) in
      fprintf fm "%s@[<hov 2>forall @[%a@].@ %a%s@]" s1 (print_ids ~fv {cfg with top=false}) xs (pr_t ~cfg 0) t s2
  | Exists(x, t1) ->
      let xs,t =
        if !!Debug.check then
          [x], t1
        else
          decomp_exists (make_raw desc typ_unknown)
      in
      let fv = get_fv t in
      let cfg = update_omit_id ~bv:xs ~fv:Id.List.Set.(fv - xs) cfg in
      let p = 15 in
      let s1,s2 = paren pri (p+1) in
      fprintf fm "%s@[<hov 2>exists @[%a@].@ %a%s@]" s1 (print_ids ~fv {cfg with top=false}) xs (pr_t ~cfg 0) t s2


and print_info cfg fm info =
  match info with
  | InfoId x ->
      fprintf fm "Id %a" (print_id cfg) x
  | InfoString s ->
      fprintf fm "String %S" s
  | InfoInt n ->
      fprintf fm "Int %d" n
  | InfoTerm t ->
      fprintf fm "Term %a" (print_term {cfg with ty=false} 80) t
  | InfoIdTerm(x,t) ->
      fprintf fm "IdTerm(%a,@ %a)" (print_id cfg) x (print_term {cfg with ty=false} 80) t



and print_pattern cfg fm pat =
  let pr_p = print_pattern cfg in
  match pat.pat_desc with
  | PAny -> pp_print_string fm "_"
  | PNondet -> pp_print_string fm "*"
  | PVar x -> print_id cfg fm x
  | PAlias(p,x) -> fprintf fm "(%a as %a)" pr_p p (print_id cfg) x
  | PConst c -> print_term cfg 1 fm c
  | PConstr(b,c,pats) ->
      fprintf fm "%s%a" (if b then "`" else "") Print_typ.path c;
      if pats <> [] then
        fprintf fm "(%a)" (print_list pr_p ",") pats
  | PNil -> fprintf fm "[]"
  | PCons(p1,p2) -> fprintf fm "%a::%a" pr_p p1 pr_p p2
  | PRecord pats ->
      let aux fm (f,pat) = fprintf fm "%a =@ %a" Print_typ.label f pr_p pat in
      Format.fprintf fm "@[{@[%a@]}@]" (print_list ~limit:cfg.length aux ",@ ") pats
  | POr _ -> fprintf fm "(%a)" (print_list ~limit:cfg.length pr_p "@ | ") @@ decomp_por pat
  | PTuple [p] -> fprintf fm "(%a,)" pr_p p
  | PTuple pats -> fprintf fm "(%a)" (print_list ~limit:cfg.length pr_p ", ") pats
  | PNone -> fprintf fm "None"
  | PSome p -> fprintf fm "(Some %a)" pr_p p
  | PWhen(p,cond) -> fprintf fm "@[<hov 4>@[<hov 2>%a@] when@ @[<hov 2>%a@]@]" pr_p p (print_term cfg 1) cond
  | PLazy p -> fprintf fm "(lazy %a)" pr_p p
  | PEval(x,t,p) -> fprintf fm "@[(%a@ eval %a@ with@ %a)@]" (print_id cfg) x (print_term cfg 1) t pr_p p
let print_term cfg fm = print_term cfg 0 fm

let update_config_for_local cfg t =
  match t.desc with
  | Local _ -> {cfg with length=cfg.length-1}
  | _ -> cfg

(* TODO: merge with print_term *)
let rec print_term' cfg pri fm t =
  if cfg.depth = 0 || cfg.length = 0 then
    print_dots fm
  else
    let cfg' = {cfg with depth=cfg.depth-1} in
    let marked = List.exists (function AMark b -> !b | _ -> false) t.attr in
    if marked then fprintf fm "@\n%a%s@\n" Color.set Color.Red (String.make (Format.pp_get_margin fm ()) '<');
    fprintf fm "(@[";(
      match t.desc with
      | End_of_definitions -> fprintf fm "EOD"
      | Const c -> print_const !config_default fm c
      | Var x when (try List.mem ~eq:Type.eq (Lid.typ x) [t.typ; Ty.unknown] with _ -> true) ->
          print_lid cfg fm x
      | Var x -> print_lid_typ cfg fm x
      | Fun(x, t) ->
          let p = 2 in
          let s1,s2 = paren pri p in
          fprintf fm "%sfun %a -> %a%s" s1 (print_id cfg) x (print_term' cfg' p) t s2
      | App(t, ts) ->
          let p = 8 in
          let s1,s2 = paren pri p in
          fprintf fm "%s%a@ %a%s" s1 (print_term' cfg' p) t (print_termlist' cfg' p) ts s2
      | If(t1, t2, t3) ->
          let p = 1 in
          let s1,s2 = paren pri (p+1) in
          fprintf fm "%s@[@[if %a@]@ then @[%a@]@ else @[%a@]@]%s"
            s1 (print_term' cfg' p) t1 (print_term' cfg' p) t2 (print_term' cfg' p) t3 s2
      | Local(Decl_let bindings, t2) ->
          let s_rec =
            if List.exists (is_module -| snd) bindings then
              " module"
            else if is_non_rec bindings then
              ""
            else
              " rec"
          in
          let p = 10 in
          let s1,s2 = paren pri (p+1) in
          let b = ref true in
          let print_binding fm (f,t1) =
            let xs,t1' =
              if is_functor ~default:false [] t1 then
                [], t1
              else
                decomp_funs t1
            in
            let pre = if !b then "let" ^ s_rec else "and" in
            fprintf fm "@[<hov 2>%s%a =@ %a@]" pre (print_ids {cfg with ty=true}) (f::xs) (print_term' cfg' p) t1';
            b := false
          in
          let print_bindings bs = print_list ~limit:cfg.length print_binding "@ " bs in
          let cfg' = update_config_for_local cfg t2 in
          begin
            match t2.desc with
            | Local _ ->
                fprintf fm "%s@[<v>@[<hov 2>%a@]@ in@ %a@]%s"
                  s1 print_bindings bindings (print_term' cfg' p) t2 s2
            | _ ->
                fprintf fm "%s@[<v>@[<hov 2>%a@]@ @[<v 2>in@ @]@[<hov>%a@]@]%s"
                  s1 print_bindings bindings (print_term' cfg' p) t2 s2
          end
      | Local(Decl_type decls, t) ->
          let p = 10 in
          let s1,s2 = paren pri (p+1) in
          let cfg' = update_config_for_local cfg t in
          fprintf fm "%s@[<v>@[<hv>%a@]@ in@ @[<hov>%a@]@]%s" s1 (print_type_decls cfg) decls (print_term' cfg' p) t s2
      | Local(Type_ext(Ext_type(s, (params, row))), t) ->
          let p = 10 in
          let s1,s2 = paren pri (p+1) in
          let ty = TVariant(VNonPoly, [row_of_ext_row row]) in
          let cfg' = update_config_for_local cfg t in
          if C.is_exn s then
            fprintf fm "%s@[<v>@[exception %a@]@ in@ @[<hov>%a@]@]%s" s1 print_typ ty (print_term' cfg' p) t s2
          else
            fprintf fm "%s@[<v>@[type %a%a +=@ %a@]@ in@ @[<hov>%a@]@]%s" s1 print_params params Print_typ.path s print_typ ty (print_term' cfg' p) t s2
      | Local(Type_ext(Ext_rebind(c1,c2)), t) ->
          let p = 10 in
          let s1,s2 = paren pri (p+1) in
          let cfg' = update_config_for_local cfg t in
          fprintf fm "%s@[<v>@[exception %a =@ %a@]@ in@ @[<hov>%a@]@]%s" s1 Print_typ.constr c1 Print_typ.path c2 (print_term' cfg' p) t s2
      | Local(Include t1, t2) ->
          let p = 10 in
          let s1,s2 = paren pri (p+1) in
          fprintf fm "%s@[<hov 2>include@ %a@ in@ @[<hov>%a@]@]%s" s1 (print_term' cfg 0) t1 (print_term' cfg p) t2 s2
      | Local(Decl_multi [], t) -> print_term' cfg pri fm t
      | Local(Decl_multi decls, t) ->
          let mk_local decl t = make (Local(decl,t)) t.typ in
          print_term' cfg pri fm @@ List.fold_right mk_local decls t
      | BinOp(op, t1, t2) ->
          let p = match op with Add|Sub|Mult|Div -> 6 | And -> 4 | Or -> 3 | _ -> 5 in
          let s1,s2 = paren pri p in
          fprintf fm "%s%a %a %a%s" s1 (print_term' cfg' p) t1 print_binop op (print_term' cfg' p) t2 s2
      | Not t ->
          let p = 6 in
          let s1,s2 = paren pri p in
          fprintf fm "%snot %a%s" s1 (print_term' cfg' p) t s2
      | Event(s,_) -> fprintf fm "{%s}" s
      | Record fields ->
          let aux fm (s,t) = fprintf fm "%a=%a" Print_typ.label s (print_term' cfg' 0) t in
          fprintf fm "{%a}" (print_list ~limit:cfg.length aux ";@ ") fields
      | Field(t,s) -> fprintf fm "%a.%a" (print_term' cfg' 9) t Print_typ.label s
      | SetField(t1,s,t2) -> fprintf fm "%a.%a <- %a" (print_term' cfg' 9) t1 Print_typ.label s (print_term' cfg' 3) t2
      | Nil -> fprintf fm "[]"
      | Cons(t1,t2) ->
          let p = 7 in
          let s1,s2 = paren pri (p+1) in
          fprintf fm "%s%a::%a%s" s1 (print_term' cfg' p) t1 (print_term' cfg' p) t2 s2
      | Constr(b,s,ts) ->
          let quot = if b then "`" else "" in
          let p = 8 in
          let s1,s2 = paren pri p in
          let aux fm = function
              [] -> ()
            | [t] -> fprintf fm "(%a)" (print_term' cfg' 1) t
            | t::ts ->
                fprintf fm "(%a" (print_term' cfg' 1) t;
                List.iter (fun t -> fprintf fm ",%a" (print_term' cfg' 1) t) ts;
                pp_print_string fm ")"
          in
          fprintf fm "%s%s%a%a%s" s1 quot Print_typ.path s aux ts s2
      | Match(t,pats) ->
          let p = 1 in
          let s1,s2 = paren pri (p+1) in
          let aux (pat,t) = fprintf fm "@[<hov 4>%a -> %a@]@ " (print_pattern' cfg') pat (print_term' cfg' p) t in
          fprintf fm "%s@[match %a with@ " s1 (print_term' cfg' p) t;
          List.iter aux pats;
          fprintf fm "@]%s" s2
      | Raise t ->
          let p = 4 in
          let s1,s2 = paren pri (p+1) in
          fprintf fm "%sraise %a%s" s1 (print_term' cfg' 1) t s2
      | TryWith(t1,t2) ->
          let p = 1 in
          let s1,s2 = paren pri (p+1) in
          fprintf fm "%stry %a with@ %a%s" s1 (print_term' cfg' p) t1 (print_term' cfg' p) t2 s2
      | Tuple [t] ->
          fprintf fm "@[(%a,)@]" (print_term' cfg' 0) t
      | Tuple ts ->
          fprintf fm "@[(%a)@]" (print_list ~limit:cfg.length (print_term' cfg' 0) ",@ ") ts
      | Proj(0,t) when tuple_num t.typ = Some 2 ->
          let p = 4 in
          let s1,s2 = paren pri (p+1) in
          fprintf fm "%s@[fst %a@]%s" s1 (print_term' cfg' 1) t s2
      | Proj(1,t) when tuple_num t.typ = Some 2 ->
          let p = 4 in
          let s1,s2 = paren pri (p+1) in
          fprintf fm "%s@[snd %a@]%s" s1 (print_term' cfg' 1) t s2
      | Proj(i,t) ->
          let p = 4 in
          let s1,s2 = paren pri (p+1) in
          fprintf fm "%s@[#%d %a@]%s" s1 i (print_term' cfg' 1) t s2
      | Bottom -> fprintf fm "⊥"
      | Label(info, t) ->
          fprintf fm "(@[label[%a]@ %a@])" (print_info cfg') info (print_term' cfg' 0) t
      | Ref t ->
          let p = 4 in
          let s1,s2 = paren pri (p+1) in
          fprintf fm "%sref %a%s" s1 (print_term' cfg' 1) t s2
      | Deref t ->
          let p = 4 in
          let s1,s2 = paren pri (p+1) in
          fprintf fm "%s!%a%s" s1 (print_term' cfg' 1) t s2
      | SetRef(t1,t2) ->
          let p = 4 in
          let s1,s2 = paren pri (p+1) in
          fprintf fm "%s%a := %a%s" s1 (print_term' cfg' 1) t1 (print_term' cfg' 1) t2 s2
      | TNone -> fprintf fm "None"
      | TSome t ->
          let p = 4 in
          let s1,s2 = paren pri (p+1) in
          fprintf fm "%sSome %a%s" s1 (print_term' cfg' 1) t s2
      | Lazy t ->
          let p = 4 in
          let s1,s2 = paren pri (p+1) in
          fprintf fm "%slazy %a%s" s1 (print_term' cfg' 1) t s2
      | Module decls ->
          let p = 10 in
          let s1,s2 = paren pri (p+1) in
          fprintf fm "@[%s@[<hv 2>struct@ @[%a@]@]@ end%s@]" s1 (print_declaration' cfg') decls s2
      | Pack t ->
          fprintf fm "(module %a : %a)" (print_term' cfg' 1) t print_typ t.typ
      | Unpack t ->
          fprintf fm "(val %a)" (print_term' cfg' 1) t
      | MemSet(t1, t2) ->
          let p = 10 in
          let s1,s2 = paren pri (p+1) in
          fprintf fm "@[%s%a ∈ %a%s@]" s1 (print_term' cfg' 1) t1 (print_term' cfg' 1) t2 s2
      | AddSet(t1, t2) ->
          let p = 10 in
          let s1,s2 = paren pri (p+1) in
          fprintf fm "@[%s{%a} ∪ %a%s@]" s1 (print_term' cfg' 1) t1 (print_term' cfg' 1) t2 s2
      | Subset(t1, t2) ->
          let p = 10 in
          let s1,s2 = paren pri (p+1) in
          fprintf fm "@[%s%a ⊆ %a%s@]" s1 (print_term' cfg' 1) t1 (print_term' cfg' 1) t2 s2
      | Forall _ -> unsupported "%s" __FUNCTION__
      | Exists _ -> unsupported "%s" __FUNCTION__
    );
    fprintf fm ":@ @[%a@]@])" (Color.cyan print_typ) t.typ;
    if marked then fprintf fm "@\n%s%t@\n" (String.make (Format.pp_get_margin fm ()) '>') Color.reset

and print_declaration' cfg fm decls = (* TODO: fix *)
  let t =
    let aux decl t0 = make_raw (Local(decl,t0)) t0.typ in
    List.fold_right aux decls (make_raw End_of_definitions (TBase TUnit))
  in
  print_term' cfg 0 fm t

(* TODO: print the types of sub-patterns *)
and print_pattern' cfg fm pat =
  let rec pr fm pat =
    match pat.pat_desc with
    | PAny -> pp_print_string fm "_"
    | PNondet -> pp_print_string fm "*"
    | PVar x -> print_id_typ cfg fm x
    | PAlias(p,x) -> fprintf fm "(%a as %a)" pr p (print_id_typ cfg) x
    | PConst c -> print_term' cfg 1 fm c
    | PConstr(b,c,pats) ->
        let quot = if b then "`" else "" in
        fprintf fm "%s%a" quot Print_typ.path c;
        if pats <> [] then fprintf fm "(%a)" (print_list pr ",") pats
    | PNil -> fprintf fm "[]"
    | PCons(p1,p2) -> fprintf fm "%a::%a" pr p1 pr p2
    | PRecord pats ->
        let pr' fm (f,pat) = fprintf fm "%a =@ %a" Print_typ.label f pr pat in
        Format.fprintf fm "@[{@[%a@]}@]" (print_list ~limit:cfg.length pr' ",@ ") pats
    | POr(pat1,pat2) -> fprintf fm "(%a | %a)" pr pat1 pr pat2
    | PTuple [p] -> fprintf fm "(%a,)" pr p
    | PTuple pats -> fprintf fm "(%a)" (print_list ~limit:cfg.length pr ", ") pats
    | PNone -> fprintf fm "None"
    | PSome p -> fprintf fm "(Some %a)" pr p
    | PWhen(p,cond) -> fprintf fm "%a when@ @[<hov 2>%a@]@ " pr p (print_term' cfg 1) cond
    | PLazy p -> fprintf fm "(lazy %a)" pr p
    | PEval(x,t,p) -> fprintf fm "@[(%a@ eval %a@ with@ %a)@]" (print_id cfg) x (print_term' cfg 1) t pr p
  in
  fprintf fm "| (%a : %a)" pr pat print_typ pat.pat_typ

and print_termlist' cfg pri ts = print_list ~limit:cfg.length (print_term' cfg pri) "@ " ts


let print_defs fm (defs:(id * (id list * term)) list) =
  let print_fundef (f, (xs, t)) =
    fprintf fm "%a %a-> %a.\n" (print_id !config_default) f (print_ids {!config_default with ty=false}) xs (print_term {!config_default with ty=false}) t
  in
  List.iter print_fundef defs

let print_env fm {Tenv.menv; tenv; rebind} =
  let pr_decl fm (c,(ps,ty)) = Format.fprintf fm "%a%a = %a" print_params ps Print_typ.tconstr c print_typ ty in
  let pr_rebind fm (s1,s2) = Format.fprintf fm "exception %a = %a" Print_typ.tconstr s1 Print_typ.path s2 in
  Format.fprintf fm "@[@[menv: %a;@]@ @[tenv: %a;@]@ @[rebind: %a;@]@]"
    (List.print (Pair.print Id.print print_typ)) menv
    (List.print pr_decl) tenv
    (List.print pr_rebind) rebind

let string_of_const c = Format.asprintf "%a" (print_const !config_default) c
let string_of_binop op = Format.asprintf "%a" print_binop op
let string_of_typ typ = Format.asprintf "%a" print_typ typ
let string_of_constr desc =
  match desc with
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
  | Lazy _ -> "Lazy"
  | Module _ -> "Module"
  | Pack _ -> "Pack"
  | Unpack _ -> "Unpack"
  | MemSet _ -> "MemSet"
  | AddSet _ -> "AddSet"
  | Subset _ -> "Subset"
  | Forall _ -> "Forall"
  | Exists _ -> "Exists"

let location = print_location
let typ = print_typ
let id fm = print_id !config_default fm
let id_typ fm = print_id_typ !config_default fm
let lid fm = print_lid !config_default fm
let lid_typ fm = print_lid_typ !config_default fm
let pattern fm = print_pattern !config_default fm
let pattern' fm = print_pattern' !config_default fm
let const fm = print_const !config_default fm
let desc fm = print_desc !config_default 0 [] fm
let term fm = print_term !config_default fm
let term_top fm = print_term {!config_default with top=true} fm
let term' fm = print_term' !config_default 0 fm
let term_typ fm = print_term {!config_default with ty=true} fm
let term_typ_top fm = print_term {!config_default with ty=true; top=true} fm
let defs = print_defs
let desc_constr fm = pp_print_string fm -| string_of_constr
let attr fm = print_attr_list !config_default fm
let type_decls = print_type_decls {!config_default with ty=false; top=true}
let decls = print_decls {!config_default with ty=false; top=true}
let params = print_params
let env = print_env
let as_ocaml fm t =
  let@ () = Id.tmp_set_print_as_ocaml in
  let@ () = Print_typ.tmp_set_print_as_ocaml in
  print_term {!config_default with top=true; as_ocaml=true} fm t
let as_ocaml_typ fm t =
  let@ () = Id.tmp_set_print_as_ocaml in
  let@ () = Print_typ.tmp_set_print_as_ocaml in
  print_term {!config_default with ty=true; top=true; as_ocaml=true} fm t
let term_custom = print_term

let label = Print_typ.label
let constr = Print_typ.constr
let tconstr = Print_typ.tconstr
let path = Print_typ.path

include Print_

module T = Print_typ
