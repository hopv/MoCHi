%{
open Trecs_syntax

let print_error_information () =
  let st = Parsing.symbol_start_pos () in
  let en = Parsing.symbol_end_pos () in
  print_string ("File \"" ^ st.Lexing.pos_fname);
  Format.printf "\", line %d" st.Lexing.pos_lnum;
  Format.printf ", characters %d-%d:\n"
    (st.Lexing.pos_cnum - st.Lexing.pos_bol)
    (en.Lexing.pos_cnum - en.Lexing.pos_bol)

let parse_error _ = print_error_information ()
%}

%token EOF
%token <string> IDENT
%token <int> STATE
%token <int> INT
%token LPAREN
%token RPAREN
%token TOP
%token ARROW
%token AND
%token COLON
%token DOT
%token COMMA
%token SAFE
%token UNSAFE
%token TIMEOUT
%token THE_ERROR_TRACE_IS

/* priority : low -> high */
%right ARROW
%left AND

%start output
%type <Trecs_syntax.result> output

%%

output:
  SAFE env EOF { Safe $2 }
| UNSAFE THE_ERROR_TRACE_IS error_trace EOF { Unsafe $3 }
| TIMEOUT EOF { TimeOut }

error_trace:
  DOT
  { [] }
| LPAREN IDENT COMMA INT RPAREN error_trace
  { ($2, $4) :: $6 }

env:
  { [] }
| IDENT COLON typ_list env
  { ($1, Inter_type.Inter $3) :: $4 }

typ_list:
  { [] }
| typ typ_list
  { $1::$2 }

typ:
  LPAREN typ RPAREN
  { $2 }
| TOP
  { Inter_type.Inter [] }
| INT
  {
    match $1 with
        0 -> Inter_type.Base Inter_type.True
      | 1 -> Inter_type.Base Inter_type.False
      | _ -> assert false
  }
| STATE
  { Inter_type.Base (Inter_type.State $1) }
| typ AND typ
  {
    match $1,$3 with
    | Inter_type.Inter typs1, Inter_type.Inter typs2 -> Inter_type.Inter (typs1 @ typs2)
    | Inter_type.Inter typs1, typ2 -> Inter_type.Inter (typs1 @ [typ2])
    | typ1, Inter_type.Inter typs2 -> Inter_type.Inter (typ1 :: typs2)
    | typ1, typ2 -> Inter_type.Inter [typ1; typ2]
  }
| typ ARROW typ
  { Inter_type.Fun($1, $3) }
