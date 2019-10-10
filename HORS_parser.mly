%{
  open HORS_syntax
%}

%token <string> IDENT
%token DOT COMMA UNDERSCORE LPAREN RPAREN ARROW
%token EOF

%nonassoc LPAREN IDENT

%left APPLY

%start top
%type <HORS_syntax.rules> top
%%

top:
| rule_list
    { $1 }
| error
    { failwith "parse error" }

rule_list:
|
    { [] }
| rule DOT rule_list
    { $1 :: $3 }

rule:
| IDENT args ARROW expr
    { ($1, List.fold_right (fun arg e -> Abst (arg, e)) $2 $4) }

args:
|
    { [] }
| IDENT args
    { $1 :: $2 }

expr:
| LPAREN expr RPAREN
    { $2 }
| IDENT
    { Var($1) }
| expr expr %prec APPLY
    { Apply($1, $2) }
