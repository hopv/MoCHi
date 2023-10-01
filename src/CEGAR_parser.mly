%{
open CEGAR_syntax
open CEGAR_type
open CEGAR_util

let print_error_information () =

  let st =  Parsing.symbol_start_pos () in
(*
  let en = Parsing.symbol_end_pos () in
*)

  Format.eprintf "File \"%s\", line %d, characters %d-:\n"
    st.Lexing.pos_fname
    st.Lexing.pos_lnum
    (st.Lexing.pos_cnum - st.Lexing.pos_bol)
(*    (en.Lexing.pos_cnum - en.Lexing.pos_bol)*)

let parse_error _ = print_error_information ()
%}

%token <string> IDENT
%token <int> INT
%token LPAREN
%token RPAREN
%token LSQUAR
%token RSQUAR
%token ARROW
%token SEMI
%token SEMISEMI
%token COLON
%token TUNIT
%token TRESULT
%token TBOOL
%token TINT
%token EQUAL
%token LTHAN
%token GTHAN
%token LEQ
%token GEQ
%token OR
%token AND
%token NOT
%token PLUS
%token MINUS
%token TIMES
%token MAIN
%token TYPES
%token TRUE
%token FALSE
%token RANDINT
%token END
%token EOF

/* priority : low -> high */
%right ARROW
%left OR
%left AND
%nonassoc EQUAL LTHAN GTHAN LEQ GEQ
%left PLUS MINUS
%left TIMES



%start prog
%type <CEGAR_syntax.prog> prog

%%

prog:
| MAIN
  main=id
  defs=defs
  TYPES
  env=env
  EOF
  { {main; defs; env; info=init_info} }

defs:
| def=def
  {[def]}
| def=def defs=defs
  {def::defs}

def:
| fn=id args=id_list ARROW body=term SEMISEMI
  {{fn; args; cond=Const True; body}}

id:
| x=IDENT { x }

id_list:
  { [] }
| x=id xs=id_list
  { x::xs }

simple_term:
| LPAREN t=term RPAREN
  { t }
| LPAREN RPAREN
  { Const Unit }
| x=id
  { Var x }
| n=INT
  { make_int n }
| TRUE
  { Const True }
| FALSE
  { Const False }
| RANDINT
  { Const (Rand(TInt, None)) }
| END
  { Const CPS_result }

term:
| t=simple_term
  { t }
| t=simple_term ts=nonempty_list(simple_term)
  { make_app t ts }
| MINUS t=simple_term
  {
    match t with
    | Const (Int n) -> make_int (-n)
    | Var x -> make_mul (make_int (-1)) (Var x)
    | t -> make_sub (make_int 0) t
  }
| t1=term EQUAL t2=term
  { make_eq_int t1 t2 }
| t1=term LTHAN t2=term
  { make_lt t1 t2 }
| t1=term GTHAN t2=term
  { make_gt t1 t2 }
| t1=term LEQ t2=term
  { make_leq t1 t2 }
| t1=term GEQ t2=term
  { make_geq t1 t2 }
| t1=term AND t2=term
  { make_and t1 t2 }
| t1=term OR t2=term
  { make_or t1 t2 }
| t1=term PLUS t2=term
  { make_add t1 t2 }
| t1=term MINUS t2=term
  { make_sub t1 t2 }
| t1=term TIMES t2=term
  { make_sub t1 t2 }
| NOT t=simple_term
  { make_not t }


env:
  {[]}
| x=id COLON ty=typ env=env
  { (x,ty)::env }

base_type:
| TUNIT { typ_unit }
| TBOOL { typ_bool_empty }
| TINT { typ_int }

simple_type:
| ty=base_type { ty }
| TRESULT { typ_result }
| typ=base_type LSQUAR preds=pred_list RSQUAR
  { TBase(get_base typ, fun _ -> preds) }

id_simple_type:
| x=id COLON ty=base_type { x, ty }
| x=id COLON typ=base_type LSQUAR preds=pred_list RSQUAR
  { x, TBase(get_base typ, fun y -> List.map (subst x y) preds) }

typ:
| LPAREN ty=typ RPAREN { ty }
| ty=simple_type { ty }
| ty1=typ ARROW ty2=typ { TFun(ty1, fun _ -> ty2) }
| xty=id_simple_type ARROW ty2=typ
  {
    let x,typ1 = xty in
    TFun(typ1, fun y -> subst_typ x y ty2)
  }

pred_list:
  { [] }
| t=term
  { [t] }
| t=term SEMI ts=pred_list
  { t::ts }
