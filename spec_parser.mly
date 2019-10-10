%{
open Util
open Type
open Syntax
open Term_util

module RT = Ref_type

let print_error_information () =
  try
    let st = Parsing.symbol_start_pos () in
    let en = Parsing.symbol_end_pos () in
    Format.eprintf "%s, line %d, characters %d-%d\n"
                   st.Lexing.pos_fname
                   st.Lexing.pos_lnum
                   (st.Lexing.pos_cnum - st.Lexing.pos_bol)
                   (en.Lexing.pos_cnum - en.Lexing.pos_bol)
  with _ -> ()

let parse_error _ = print_error_information ()

let make_tmp_id s = Id.make 0 s [] typ_unknown
let make_id_typ s typ = Id.make 0 s [] typ
let make_self_id typ = Id.new_var ~name:"_" typ
let orig_id x = {x with Id.id = 0}

let ref_base b = Ref_type.Base(b, Id.new_var (TBase(b)), true_term)
let ref_ADT s = Ref_type.ADT(s, Id.new_var (TData(s)), true_term)
let ref_list typ = RT.List(Id.new_var Ty.int, true_term, Id.new_var Ty.int, true_term, typ)
let ref_fun x ty1 ty2 =
  let ty2' = RT.subst_var (orig_id x) (Id.set_typ x @@ elim_tattr @@ RT.to_simple ty1) ty2 in
  RT.Fun(x, ty1, ty2')
let ref_tuple xtys =
  let xtys' = snd @@
    List.Labels.fold_left ~init:([],[]) xtys ~f:
      begin fun (map,tuple) (x,rty) ->
        let x' = Id.set_typ x (RT.to_simple rty) in
        let rty' = RT.subst_map map rty in
        List.snoc map (orig_id x, make_var x'),
        List.snoc tuple (x', rty')
      end
  in RT.Tuple(xtys')

let normalize_ref ty =
  RT.map_pred Trans.set_length_typ ty

let make_pat p = { pat_typ=typ_unknown; pat_desc=p }
let make_var_pat (x: Syntax.id) = make_pat @@ PVar(x)
let make_match x cases =
  {desc=Match(make_var x, cases);
   typ=typ_unknown;
   attr=[]}

%}

%token <string> LIDENT /* start with lowercase letter */
%token <string> UIDENT /* start with uppercase letter */
%token <string> EVENT
%token <int> INT
%token LPAREN
%token RPAREN
%token LSQUAR
%token RSQUAR
%token LBRACE
%token RBRACE
%token ARROW
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
%token END
%token EOF

/* priority : low -> high */
%left UNION
%right ARROW
%left INTER
%left OR
%left AND
%nonassoc NOT
%nonassoc EQUAL LTHAN GTHAN LEQ GEQ
%left PLUS MINUS
%left TIMES DIV
%left LIST



%start spec
%type <Spec.t> spec

%%

exp:
  id
  { make_var $1 }
| LPAREN full_exp RPAREN
  { $2 }
| INT
  { make_int $1 }
| TRUE
  { true_term }
| FALSE
  { false_term }
| MINUS exp
  { make_sub (make_int 0) $2 }
| exp EQUAL exp
  { make_eq $1 $3 }
| exp LTHAN exp
  { make_lt $1 $3 }
| exp GTHAN exp
  { make_gt $1 $3 }
| exp LEQ exp
  { make_leq $1 $3 }
| exp GEQ exp
  { make_geq $1 $3 }
| exp NEQ exp
  { make_neq $1 $3 }
| exp AND exp
  { make_and $1 $3 }
| exp OR exp
  { make_or $1 $3 }
| exp PLUS exp
  { make_add $1 $3 }
| exp MINUS exp
  { make_sub $1 $3 }
| exp TIMES exp
  { make_mul $1 $3 }
| exp DIV exp
  { make_div $1 $3 }
| NOT exp
  { make_not $2 }
| id id /* for length */
  {
    if (Id.name $1 <> "List.length") then raise Parse_error;
    make_length @@ make_var $2
  }

full_exp:
| exp { $1 }
| MATCH id WITH opt_bar match_cases
  { make_match $2 $5 }

match_cases:
| match_case                 { [$1] }
| match_case BAR match_cases { $1::$3 }

/* do not support `when` for the time being */
match_case:
| pattern ARROW exp { (make_pat $1, $3) }

pattern:
| UNDER_SCORE                         { PAny }
| id                                  { PVar($1) }
| UIDENT                              { PConstr($1, []) }
| UIDENT id                           { PConstr($1, [make_var_pat $2]) }
| UIDENT LPAREN pat_simple_seq RPAREN { PConstr($1, $3) }

pat_simple_seq:
| pat_simple                      { [$1] }
| pat_simple COMMA pat_simple_seq { $1::$3 }

pat_simple:
| id          { make_var_pat $1 }
| UNDER_SCORE { make_pat PAny }

opt_bar:
| {()}
| BAR {()}

id:
| LIDENT { make_tmp_id $1 }

spec:
  spec_list EOF { $1 }

spec_list:
  { Spec.init }
| ref_type spec_list
  { {$2 with Spec.ref_env = $1::$2.Spec.ref_env} }
| ext_ref_type spec_list
  { {$2 with Spec.ext_ref_env = $1::$2.Spec.ext_ref_env} }
| typedef spec_list
  { {$2 with Spec.abst_env = $1::$2.Spec.abst_env} }
| typedef_cps spec_list
  { {$2 with Spec.abst_cps_env = $1::$2.Spec.abst_cps_env} }
| typedef_cegar spec_list
  { {$2 with Spec.abst_cegar_env = $1::$2.Spec.abst_cegar_env} }
| inline spec_list
  { {$2 with Spec.inlined = $1::$2.Spec.inlined} }
| inlinef spec_list
  { {$2 with Spec.inlined_f = $1::$2.Spec.inlined_f} }
| fairness spec_list
  { {$2 with Spec.fairness = $1::$2.Spec.fairness} }

ref_type:
| TYPE id COLON ref_typ
  { $2, normalize_ref $4 }

ext_ref_type:
| EXTERNAL id COLON ref_typ
  { $2, normalize_ref $4 }

typedef:
| VAL id COLON typ
  { $2, Id.typ $4 }

typedef_cps:
| VALCPS id COLON typ
  { $2, Id.typ $4 }

typedef_cegar:
| VALCEGAR id COLON typ
  { $2, Id.typ $4 }

fairness:
| FAIRNESS COLON LPAREN EVENT COMMA EVENT RPAREN
  { $4, $6 }

inline:
| INLINE id
  { $2 }

inlinef:
| INLINEF id
  { $2 }

simple_type_core:
| TUNIT { Ty.unit }
| TRESULT { typ_result }
| TBOOL { Ty.bool }
| TINT { Ty.int }
| LPAREN typ LIST RPAREN { make_tlist @@ Id.typ $2 }

id_simple_type:
| simple_type_core { make_self_id $1 }
| simple_type_core LSQUAR pred_list RSQUAR { make_self_id (TAttr([TAPred(make_self_id $1, $3)], $1)) }
| id COLON simple_type_core { Id.new_var ~name:(Id.name $1) $3 }
| id COLON simple_type_core LSQUAR pred_list RSQUAR
  {
    let x = $1 in
    let typ = $3 in
    let ps = $5 in
    let x' = Id.new_var ~name:(Id.name x) typ in
    let ps' = List.map (subst_var x @@ Id.set_typ x' @@ elim_tattr typ) ps in
    Id.new_var ~name:(Id.name x) (TAttr([TAPred(x', ps')], typ))
  }

typ:
| LPAREN typ RPAREN { $2 }
| id_simple_type { $1 }
| typ TIMES typ
  {
    let x = $1 in
    let r = $3 in
    let typ1 = Id.typ x in
    let typ2 = Id.typ r in
    let typ2' = subst_type_var (orig_id x) (Id.set_typ x (elim_tattr typ1)) typ2 in
    let typ2'' = subst_type_var r (Id.set_typ abst_var (elim_tattr typ2)) typ2' in
    make_self_id @@ TTuple [x; Id.new_var typ2'']
  }
| typ ARROW typ
  {
    let x = $1 in
    let r = $3 in
    let typ1 = Id.typ x in
    let typ2 =
      Id.typ r
      |> subst_type_var (orig_id x) (Id.set_typ x @@ elim_tattr typ1)
      |> subst_type_var r (Id.set_typ abst_var @@ elim_tattr @@ Id.typ r)
    in
    make_self_id @@ TFun(x, typ2)
  }
| typ LIST
  { make_self_id @@ make_tlist @@ Id.typ $1 }

ref_base:
| TUNIT { TUnit }
| TBOOL { TBool }
| TINT  { TInt }

ref_ADT:
| LIDENT { $1 }

ref_simple:
| ref_base { ref_base $1 }
| LBRACE id COLON ref_base BAR full_exp RBRACE
  {
    let x = Id.set_typ $2 (TBase $4) in
    RT.Base($4, x, subst_var $2 x $6)
  }
| ref_ADT { ref_ADT $1 }
| LBRACE id COLON ref_ADT BAR full_exp RBRACE
  {
    let x = Id.set_typ $2 (TData $4) in
    RT.ADT($4, x, subst_var $2 x $6)
  }
| LPAREN ref_typ RPAREN { $2 }
| ref_simple LIST { RT.List(Id.new_var Ty.int,true_term,Id.new_var Ty.int,true_term,$1) }
| ref_simple length_ref LIST
  {
    let typ = $1 in
    let x,p_len = $2 in
    let typ' = RT.subst_var (orig_id x) x typ in
    RT.List(x,p_len,Id.new_var Ty.int,true_term,typ')
  }
| index_ref ref_simple length_ref LIST
  {
    let y,p_i = $1 in
    let typ = $2 in
    let x,p_len = $3 in
    let typ' = RT.subst_var (orig_id x) x typ in
    let p_i' = subst_var (orig_id x) x p_i in
    RT.List(x,p_len,y,p_i',typ')
  }

index_ref:
| LSQUAR id RSQUAR { Id.new_var ~name:(Id.name $2) Ty.int, true_term }
| LSQUAR id COLON exp RSQUAR
  {
    let x = $2 in
    let x' = Id.new_var ~name:(Id.name x) Ty.int in
    x', subst_var x x' $4
  }

length_ref:
| BAR id BAR
  {
    let x = $2 in
    let x' = Id.new_var ~name:(Id.name x) Ty.int in
    x', true_term
  }
| BAR id COLON exp BAR
  {
    let x = $2 in
    let x' = Id.new_var ~name:(Id.name x) Ty.int in
    x', subst_var x x' $4
  }

ref_typ:
| ref_simple { $1 }
| id COLON ref_simple TIMES ref_typ
  {
    let y = Id.new_var (Ref_type.to_simple $5) in
    ref_tuple [($1,$3);(y,$5)]
  }
| LPAREN id COLON ref_simple RPAREN TIMES ref_typ
  {
    let y = Id.new_var (Ref_type.to_simple $7) in
    ref_tuple [($2,$4);(y,$7)]
  }
| ref_typ TIMES ref_typ
  {
    let x  =
      match $1 with
      | RT.Base(_,y,_) -> y
      | _ -> Id.new_var (RT.to_simple $1)
    in
    RT.Tuple[x, $1; Id.new_var @@ Ref_type.to_simple $3, $3]
  }
| id COLON ref_simple ARROW ref_typ
  {
    let x = Id.set_typ $1 (Ref_type.to_simple $3)
    in ref_fun x $3 $5
  }
| LPAREN id COLON ref_simple RPAREN ARROW ref_typ
  {
    let x = Id.set_typ $2 (Ref_type.to_simple $4)
    in ref_fun x $4 $7
  }
| ref_typ ARROW ref_typ
  {
    let x  =
      match $1 with
      | RT.Base(_,y,_) -> y
      | _ -> Id.new_var @@ RT.to_simple $1
    in
    ref_fun x $1 $3
  }
| ref_typ UNION ref_typ { RT.Union(RT.to_simple $1, [$1; $3]) }
| ref_typ INTER ref_typ { RT.Inter(RT.to_simple $1, [$1; $3]) }

pred_list:
  { [] }
| exp
  { [$1] }
| exp SEMI pred_list
  { $1::$3 }
