%{
open HorSat_syntax
%}

%token EOF
%token <int> INT
%token <int> STATE
%token <string> IDENT
%token LPAREN
%token RPAREN
%token COMMA
%token COLON
%token CARET
%token ARROW
%token DOT
%token BR_EXISTS
%token BR_FORALL
%token UNIT
%token FAIL
%token BOT
%token TOP
%token SATTYP
%token SATISFIED
%token UNSATISFIED
%token THE_SIZE_OF_TYPING
%token A_COUNTEREXAMPLE_IS

/* priority : low -> high */

%start output_apt
%type <HorSat_syntax.result> output_apt
%start output
%type <HorSat_syntax.result> output

%%

output_apt:
| SATISFIED EOF { Satisfied [] }
| UNSATISFIED THE_SIZE_OF_TYPING INT A_COUNTEREXAMPLE_IS counterexample_apt EOF { UnsatisfiedAPT $5 }
| UNSATISFIED A_COUNTEREXAMPLE_IS counterexample_apt EOF { UnsatisfiedAPT $3 }

counterexample_apt:
| LPAREN counterexample_apt RPAREN
  { $2 }
| BR_EXISTS counterexample_apt counterexample_apt
  { HorSat_syntax.br_exists $2 $3 }
| BR_FORALL counterexample_apt BOT
  { HorSat_syntax.node "br_forall" $2 }
| BR_FORALL BOT counterexample_apt
  { HorSat_syntax.node "br_forall" $3 }
| IDENT counterexample_apt
  { HorSat_syntax.node $1 $2 }
| UNIT
  { HorSat_syntax.leaf () }
| FAIL BOT
  { HorSat_syntax.leaf () }

output:
| SATISFIED EOF { Satisfied [] }
| UNSATISFIED THE_SIZE_OF_TYPING INT A_COUNTEREXAMPLE_IS counterexample EOF { Unsatisfied $5 }
| UNSATISFIED A_COUNTEREXAMPLE_IS counterexample EOF { Unsatisfied $3 }

id:
  IDENT
  { $1 }
| FAIL
  { "event_fail" }

counterexample:
  { [] }
| LPAREN id COMMA INT RPAREN counterexample
  { ($2, $4) :: $6 }

env:
| { [] }
| IDENT COLON typ_list env
  { ($1, Inter_type.Inter $3) :: $4 }

typ_list:
| { [] }
| typ typ_list
  { $1::$2 }

typ:
  LPAREN typ RPAREN
  { $2 }
| TOP
  { Inter_type.Inter [] }
| STATE
  { Inter_type.Base (Inter_type.State $1) }
| typ CARET typ
  {
    match $1,$3 with
    | Inter_type.Inter typs1, Inter_type.Inter typs2 -> Inter_type.Inter (typs1 @ typs2)
    | Inter_type.Inter typs1, typ2 -> Inter_type.Inter (typs1 @ [typ2])
    | typ1, Inter_type.Inter typs2 -> Inter_type.Inter (typ1 :: typs2)
    | typ1, typ2 -> Inter_type.Inter [typ1; typ2]
  }
| typ ARROW typ
  { Inter_type.Fun($1, $3) }
