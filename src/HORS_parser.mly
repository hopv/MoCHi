%{
  open HORS_syntax
%}

%token <string> IDENT
%token DOT LPAREN RPAREN ARROW
%token EOF

%nonassoc LPAREN IDENT

%left APPLY

%start top
%type <HORS_syntax.rules> top
%%

top:
| rules=rule_list EOF
    { rules }
| error
    { failwith "parse error" }

rule_list:
|
    { [] }
| r=rule DOT rs=rule_list
    { r::rs }

rule:
| IDENT args=args ARROW e=expr
    { ($1, List.fold_right (fun arg e -> Abst (arg, e)) args e) }

args:
|
    { [] }
| x=IDENT xs=args
    { x::xs }

expr:
| LPAREN e=expr RPAREN
    { e }
| x=IDENT
    { Var x }
| e1=expr e2=expr %prec APPLY
    { Apply(e1, e2) }
