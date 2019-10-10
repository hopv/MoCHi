%{
open CEGAR_syntax
open CEGAR_type
open CEGAR_util

let print_error_information () =

  let st =  Parsing.symbol_start_pos () in
(*
  let en = Parsing.symbol_end_pos () in
*)

  Format.printf "File \"%s\", line %d, characters %d-:\n"
    st.Lexing.pos_fname
    st.Lexing.pos_lnum
    (st.Lexing.pos_cnum - st.Lexing.pos_bol)
(*    (en.Lexing.pos_cnum - en.Lexing.pos_bol)*)

let parse_error _ = print_error_information ()
%}

%token <string> IDENT
%token <int> INT
%token LBRACE
%token RBRACE
%token LPAREN
%token RPAREN
%token LSQUAR
%token RSQUAR
%token ARROW
%token DARROW
%token SEMI
%token SEMISEMI
%token COLON
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
%token OR
%token AND
%token NOT
%token PLUS
%token MINUS
%token TIMES
%token MAIN
%token TYPES
%token WHEN
%token PERIOD
%token TRUE
%token FALSE
%token RANDINT
%token END
%token EOF

/* priority : low -> high */
%right ARROW
%left OR
%left AND
%nonassoc NOT
%nonassoc EQUAL LTHAN GTHAN LEQ GEQ
%left PLUS MINUS
%left TIMES
%left LIST



%start prog
%type <CEGAR_syntax.prog> prog

%%

prog:
  MAIN id defs TYPES env EOF { {main=$2; defs=$3; env=$5; info=init_info} }

defs:
| def
  {[$1]}
| def defs
  {$1 :: $2}

def:
| id id_list ARROW event_list term SEMISEMI
  {($1, $2, Const True, $4, $5)}
| id id_list WHEN term ARROW event_list term SEMISEMI
  {($1, $2, $4, $6, $7)}

id:
| IDENT { $1 }

id_list:
  { [] }
| id id_list
  { $1::$2 }

event:
| LBRACE id RBRACE DARROW
  { Event $2 }

event_list:
  { [] }
| event event_list
  { $1::$2 }

simple_term:
| LPAREN term RPAREN
  { $2 }
| LPAREN RPAREN
  { Const Unit }
| LPAREN exp RPAREN
  { $2 }
| id
  { Var $1 }
| INT
  { make_int $1 }
| TRUE
  { Const True }
| FALSE
  { Const False }
| RANDINT
  { Const (Rand(TInt, None)) }
| END
  { Const CPS_result }

term:
| simple_term
  { $1 }
| term simple_term
  { App($1, $2) }

exp:
  id
  { Var $1 }
| LPAREN exp RPAREN
  { $2 }
| INT
  { make_int $1 }
| MINUS exp
  {
    match $2 with
    | Const (Int n) -> make_int (-n)
    | Var x -> make_mul (make_int (-1)) (Var x)
    | t -> make_sub (make_int 0) t
  }
| exp EQUAL exp
  { make_eq_int $1 $3 }
| exp LTHAN exp
  { make_lt $1 $3 }
| exp GTHAN exp
  { make_gt $1 $3 }
| exp LEQ exp
  { make_leq $1 $3 }
| exp GEQ exp
  { make_geq $1 $3 }
| exp AND exp
  { make_and $1 $3 }
| exp OR exp
  { make_or $1 $3 }
| exp PLUS exp
  { make_add $1 $3 }
| exp MINUS exp
  { make_sub $1 $3 }
| exp TIMES exp
  { make_sub $1 $3 }
| NOT exp
  { make_not $2 }


env:
  {[]}
| id COLON typ env
  { ($1,$3)::$4 }

base_type:
| TUNIT { typ_unit }
| TBOOL { typ_bool_empty }
| TINT { typ_int }

simple_type:
| base_type { $1 }
| TRESULT { typ_result }
| base_type LSQUAR pred_list RSQUAR
  {
    let typ = $1 in
    let preds = $3 in
    TBase(get_base typ, fun _ -> preds)
  }

id_simple_type:
| id COLON base_type { $1, $3 }
| id COLON base_type LSQUAR pred_list RSQUAR
  {
    let x = $1 in
    let typ = $3 in
    let preds = $5 in
    x, TBase(get_base typ, fun y -> List.map (subst x y) preds)
  }

typ:
| LPAREN typ RPAREN { $2 }
| simple_type { $1 }
| typ ARROW typ { TFun($1, fun _ -> $3) }
| id_simple_type ARROW typ
  {
    let x, typ1 = $1 in
    let typ2 = $3 in
    TFun(typ1, fun y -> subst_typ x y typ2)
  }

pred_list:
  { [] }
| exp
  { [$1] }
| exp SEMI pred_list
  { $1::$3 }
