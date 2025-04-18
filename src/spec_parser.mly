%{
open Util
open Type
open Syntax
open Type_util
open Term_util
open Spec_syntax

module RT = Ref_type

let make_tmp_id s = Id.make s typ_unknown
let make_id_typ s typ = Id.make s typ
let make_self_id typ = Id.new_var ~name:"_" typ
let orig_id x = Id.set_id x 0

let tvar_counter = ref 0
let tvar_env : (string * Syntax.term Type.tvar) list ref = ref []
let reset_tvar_env () =
  tvar_counter := 0;
  tvar_env := []

let normalize_ref ty =
  reset_tvar_env ();
  RT.map_pred Trans.set_length_typ ty

let ref_var s =
  let x =
    List.assoc_opt s !tvar_env
    |> Option.default_delayed (fun () ->
           let y = Type.(ValE._TVar @@ new_tvar ()) in
           tvar_env := (s, y) :: !tvar_env;
           y)
  in
  RT.Var x
let ref_base b = RT.Base(b, Id.new_var (TBase(b)), true_term)
let ref_constr s tys = RT.Constr(s, tys, Id.new_var (TConstr(s,[])), true_term)
let ref_list typ = RT.List(Id.new_var Ty.int, true_term, Id.new_var Ty.int, true_term, typ)
let ref_fun x ty1 ty2 =
  let ty2' = RT.subst_var (orig_id x) (Id.set_typ x @@ elim_tattr @@ RT.to_simple ty1) ty2 in
  RT.Fun(x, ty1, ty2')
let ref_tuple xtys =
  let xtys' =
    List.L.fold_left xtys
      ~init:([],[])
      ~f:(fun (map,tuple) (x,rty) ->
        let x' = Id.set_typ x (RT.to_simple rty) in
        let rty' = RT.subst_map map rty in
        List.snoc map (orig_id x, make_var x'),
        (x', rty') :: tuple)
    |> snd
    |> List.rev
  in
  RT.Tuple(xtys')

let make_pat p =
  make_pattern p typ_unknown
let make_var_pat (x: Syntax.id) = make_pat @@ PVar(x)
let make_match x cases =
  make (Match(make_var x, cases)) typ_unknown

let var_of_ref_type ty =
  match ty with
  | RT.Base(_,y,_) -> y
  | _ -> Id.new_var @@ RT.to_simple ty
%}

%token <string> LIDENT /* start with lowercase letter */
%token <string> UIDENT /* start with uppercase letter */
%token <string> EVENT
%token <int> INT
%token <string> STRING
%token LPAREN
%token RPAREN
%token LSQUAR
%token RSQUAR
%token LBRACE
%token RBRACE
%token ARROW
%token AT
%token SEMI
%token COLON
%token COMMA
%token INLINE
%token INLINEF
%token TUNIT
%token TRESULT
%token TBOOL
%token TINT
%token LIST
%token EQUAL
%token LTHAN
%token GTHAN
%token LEQ
%token GEQ
%token NEQ
%token OR
%token AND
%token NOT
%token PLUS
%token MINUS
%token TIMES
%token DIV
%token BAR
%token TYPE
%token ASSERT
%token VAL
%token VALCPS
%token VALCEGAR
%token EXTERNAL
%token FAIRNESS
%token TRUE
%token FALSE
%token INTER
%token UNION
%token MATCH
%token WITH
%token UNDER_SCORE
%token PRIME
%token EOF

/* priority : low -> high */
%right ARROW
%left OR
%left AND
%nonassoc NOT
%nonassoc NEQ EQUAL LTHAN GTHAN LEQ GEQ
%left PLUS MINUS
%left TIMES DIV



%start spec
%type <t> spec

%%

exp:
| x=id
  { Term.var x }
| LPAREN e=full_exp RPAREN
  { e }
| n=INT
  { Term.int n }
| TRUE
  { Term.true_ }
| FALSE
  { Term.false_ }
| MINUS e=exp
  { Term.(~- e) }
| e1=exp EQUAL e2=exp
  { Term.(e1 = e2) }
| e1=exp LTHAN e2=exp
  { Term.(e1 < e2) }
| e1=exp GTHAN e2=exp
  { Term.(e1 > e2) }
| e1=exp LEQ e2=exp
  { Term.(e1 <= e2) }
| e1=exp GEQ e2=exp
  { Term.(e1 >= e2) }
| e1=exp NEQ e2=exp
  { Term.(e1 <> e2) }
| e1=exp AND e2=exp
  { Term.(e1 && e2) }
| e1=exp OR e2=exp
  { Term.(e1 || e2) }
| e1=exp PLUS e2=exp
  { Term.(e1 + e2) }
| e1=exp MINUS e2=exp
  { Term.(e1 - e2) }
| e1=exp TIMES e2=exp
  { Term.(e1 * e2) }
| e1=exp DIV e2=exp
  { Term.(e1 / e2) }
| NOT e=exp
  { Term.(not e) }
| len=id x=id /* for length */
  {
    if (Id.name len <> "List.length") then raise Parsing.Parse_error;
    Term.(length (var x))
  }

full_exp:
| e=exp { e }
| MATCH x=id WITH option(BAR) pats=separated_nonempty_list(BAR, match_case)
  { make_match x pats }

/* do not support `when` for the time being */
match_case:
| p=pattern ARROW e=exp { (make_pat p, e) }

pattern:
| UNDER_SCORE                                                         { PAny }
| x=id                                                                { PVar(x) }
| c=UIDENT                                                            { PConstr(false, LId (constr_of_string c), []) }
| c=UIDENT x=id                                                       { PConstr(false, LId (constr_of_string c), [make_var_pat x]) }
| c=UIDENT LPAREN ps=separated_nonempty_list(COMMA,pat_simple) RPAREN { PConstr(false, LId (constr_of_string c), ps) }

pat_simple:
| x=id        { make_var_pat x }
| UNDER_SCORE { make_pat PAny }

id:
| x=LIDENT { make_tmp_id x }

spec:
  sp=spec_list EOF { sp }

spec_list:
  { init }
| s=assert_ref_type sp=spec_list
  { {sp with assertion = s::sp.assertion} }
| s=ref_type sp=spec_list
  { {sp with ref_env = s::sp.ref_env} }
| s=ext_ref_type sp=spec_list
  { {sp with ext_ref_env = s::sp.ext_ref_env} }
| s=typedef sp=spec_list
  { {sp with abst_env = s::sp.abst_env} }
| s=typedef_cps sp=spec_list
  { {sp with abst_cps_env = s::sp.abst_cps_env} }
| s=typedef_cegar sp=spec_list
  { {sp with abst_cegar_env = s::sp.abst_cegar_env} }
| s=inline sp=spec_list
  { {sp with inlined = s::sp.inlined} }
| s=inlinef sp=spec_list
  { {sp with inlined_f = s::sp.inlined_f} }
| s=fairness sp=spec_list
  { {sp with fairness = s::sp.fairness} }

assert_ref_type:
| ASSERT x=id COLON ty=ref_typ
  { x, normalize_ref ty }

ref_type:
| TYPE x=id COLON ty=ref_typ
  { x, normalize_ref ty }

ext_ref_type:
| EXTERNAL x=id COLON ty=ref_typ
  { x, (None, normalize_ref ty) }
| EXTERNAL x=id AT s=STRING COLON ty=ref_typ
  { x, (Some s, normalize_ref ty) }

typedef:
| VAL x=id COLON ty=typ
  { x, Id.typ ty }

typedef_cps:
| VALCPS x=id COLON ty=typ
  { x, Id.typ ty }

typedef_cegar:
| VALCEGAR x=id COLON ty=typ
  { x, Id.typ ty }

fairness:
| FAIRNESS COLON LPAREN e1=EVENT COMMA e2=EVENT RPAREN
  { e1, e2 }

inline:
| INLINE x=id
  { x }

inlinef:
| INLINEF x=id
  { x }

simple_type_core:
| TUNIT { Ty.unit }
| TRESULT { typ_result }
| TBOOL { Ty.bool }
| TINT { Ty.int }
| ty=simple_type_core LIST RPAREN { make_tlist ty }

id_simple_type:
| ty=simple_type_core { make_self_id ty }
| ty=simple_type_core LSQUAR ps=pred_list RSQUAR { make_self_id (TAttr([TAPred(make_self_id ty, ps)], ty)) }
| x=id COLON ty=simple_type_core { Id.new_var ~name:(Id.name x) ty }
| x=id COLON ty=simple_type_core LSQUAR ps=pred_list RSQUAR
  {
    let x' = Id.new_var ~name:(Id.name x) ty in
    let ps' = List.map (subst_var x @@ Id.set_typ x' @@ elim_tattr ty) ps in
    Id.new_var ~name:(Id.name x) (TAttr([TAPred(x', ps')], ty))
  }

typ:
| LPAREN ty=typ RPAREN { ty }
| ty=id_simple_type { ty }
| x=typ TIMES r=typ
  {
    let typ1 = Id.typ x in
    let typ2 = Id.typ r in
    let typ2' = subst_type_var (orig_id x) (Id.set_typ x (elim_tattr typ1)) typ2 in
    let typ2'' = subst_type_var r (Id.set_typ abst_var (elim_tattr typ2)) typ2' in
    make_self_id @@ TTuple [x; Id.new_var typ2'']
  }
| x=typ ARROW r=typ
  {
    let typ1 = Id.typ x in
    let typ2 =
      Id.typ r
      |> subst_type_var (orig_id x) (Id.set_typ x @@ elim_tattr typ1)
      |> subst_type_var r (Id.set_typ abst_var @@ elim_tattr @@ Id.typ r)
    in
    make_self_id @@ TFun(x, typ2)
  }

ref_base:
| TUNIT { TUnit }
| TBOOL { TBool }
| TINT  { TInt }

ref_constr:
| x=LIDENT { x }

ref_simple:
| b=ref_base { ref_base b }
| PRIME x=LIDENT { ref_var x }
| LBRACE v=id COLON b=ref_base BAR e=full_exp RBRACE
  {
    let x = Id.set_typ v (TBase b) in
    RT.Base(b, x, subst_var v x e)
  }
| s=ref_constr { ref_constr (LId (constr_of_string s)) [] }
| LBRACE v=id COLON s=ref_constr BAR e=full_exp RBRACE
  {
    let x = Id.set_typ v (TConstr(LId (constr_of_string s),[])) in
    RT.Constr(LId (constr_of_string s), [], x, subst_var v x e)
  }
| LBRACE xs=id COLON ty=ref_simple LIST BAR e=full_exp RBRACE
  {
    let len = Id.new_var Ty.int in
    let p = subst_rev Term.(length (var xs)) len e in
    assert (not (Id.List.mem xs @@ get_fv p));
    RT.List(len, p, Id.new_var Ty.int, true_term, ty)
  }
| LPAREN ty=ref_typ RPAREN { ty }
| ty=ref_simple LIST { RT.List(Id.new_var Ty.int, true_term, Id.new_var Ty.int, true_term, ty) }
| ty=ref_simple c=ref_constr {
    let p = Type.LId (constr_of_string c) in
    let sty = TConstr(p, [RT.to_simple ty]) in
    RT.Constr(p, [ty], Id.new_var sty, true_term)
  }
/*******************************************************************************
| ty=ref_simple xp=length_ref LIST
  {
    let x, p_len = xp in
    let ty' = RT.subst_var (orig_id x) x tp in
    RT.List(x, p_len, Id.new_var Ty.int, true_term, ty')
  }
| yp=index_ref ty=ref_simple xp=length_ref LIST
  {
    let y,p_i = yp in
    let x,p_len = xp in
    let ty' = RT.subst_var (orig_id x) x ty in
    let p_i' = subst_var (orig_id x) x p_i in
    RT.List(x,p_len,y,p_i',ty')
  }


index_ref:
| LSQUAR x=id RSQUAR { Id.new_var ~name:(Id.name x) Ty.int, true_term }
| LSQUAR x=id COLON e=exp RSQUAR
  {
    let x' = Id.new_var ~name:(Id.name x) Ty.int in
    x', subst_var x x' e
  }

length_ref:
| BAR x=id BAR
  {
    let x' = Id.new_var ~name:(Id.name x) Ty.int in
    x', true_term
  }
| BAR x=id COLON e=exp BAR
  {
    let x' = Id.new_var ~name:(Id.name x) Ty.int in
    x', subst_var x x' e
  }
*******************************************************************************/
tuple_ref_typ:
| ty1=ref_simple TIMES ty2=ref_simple
  {
    [var_of_ref_type ty1, ty1; var_of_ref_type ty2, ty2]
  }
| tys=tuple_ref_typ TIMES ty=ref_simple
  { tys @ [var_of_ref_type ty, ty] }

ref_typ:
| ty=ref_simple { ty }
| x=id COLON ty1=ref_simple TIMES ty2=ref_typ
  {
    let y = Id.new_var (RT.to_simple ty2) in
    ref_tuple [(x,ty1);(y,ty2)]
  }
| LPAREN x=id COLON ty1=ref_simple RPAREN TIMES ty2=ref_typ
  {
    let y = Id.new_var (RT.to_simple ty2) in
    ref_tuple [(x,ty1);(y,ty2)]
  }
| tys=tuple_ref_typ
  { RT.Tuple tys }
| x=id COLON ty1=ref_simple ARROW ty2=ref_typ
  {
    let x' = Id.set_typ x (RT.to_simple ty1) in
    ref_fun x' ty1 ty2
  }
| LPAREN x=id COLON ty1=ref_simple RPAREN ARROW ty2=ref_typ
  {
    let x' = Id.set_typ x (RT.to_simple ty1) in
    ref_fun x' ty1 ty2
  }
| ty1=ref_typ ARROW ty2=ref_typ
  {
    let x  =
      match ty1 with
      | RT.Base(_,y,_) -> y
      | _ -> Id.new_var @@ RT.to_simple ty1
    in
    ref_fun x ty1 ty2
  }
| ty=ref_simple UNION tys=separated_nonempty_list(UNION,ref_simple) { RT.Union(RT.to_simple ty, ty::tys) }
| ty=ref_simple INTER tys=separated_nonempty_list(INTER,ref_simple) { RT.Inter(RT.to_simple ty, ty::tys) }

pred_list:
| ps=separated_list(SEMI, exp) { ps }
