{
open CEGAR_parser
}

let space = [' ' '\t' '\r']
let digit = ['0'-'9']
let lower = ['a'-'z' '_' '\'']
let upper = ['A'-'Z']
let symbol = ['(' ')' '*' '?' '|' '+' ',' '!' ';' '.' ':' '#']

rule token = parse
| space+
    { token lexbuf }
| '\n'
    { Lexing.new_line lexbuf;
      token lexbuf }
| "(*"
    { comment lexbuf;
      token lexbuf }
| '{' { LBRACE }
| '}' { RBRACE }
| '(' { LPAREN }
| ')' { RPAREN }
| '[' { LSQUAR }
| ']' { RSQUAR }
| '=' { EQUAL }
| '<' { LTHAN }
| '>' { GTHAN }
| "<=" { LEQ }
| ">=" { GEQ }
| "||" { OR }
| "&&" { AND }
| "not" { NOT }
| '+' { PLUS }
| '-' { MINUS }
| '*' { TIMES }
| "inline" { INLINE }
| "inlinef" { INLINEF }
| "unit" { TUNIT }
| "X" { TRESULT }
| "true" { TRUE }
| "false" { FALSE }
| "bool" { TBOOL }
| "int" { TINT }
| "list" { LIST }
| "->" { ARROW }
| "=>" { DARROW }
| ';' { SEMI }
| ";;" { SEMISEMI }
| ':' { COLON }
| "Main:" { MAIN }
| "Types:" { TYPES }
| "when" { WHEN }
| "rand_int" { RANDINT }
| "end" { END }
| '.' { PERIOD }
| digit+
    { INT(int_of_string (Lexing.lexeme lexbuf)) }
(*| lower (digit|lower|upper|'_')* *)
(*    { IDENT(Lexing.lexeme lexbuf) } *)
| lower (digit|lower|upper)*
    { IDENT(Lexing.lexeme lexbuf) }
| eof
    { EOF }
| _
    { (*Format.eprintf "unknown token %s near characters %d-%d@."
        (Lexing.lexeme lexbuf)
        (Lexing.lexeme_start lexbuf)
        (Lexing.lexeme_end lexbuf);*)
      failwith "lex error" }

and comment = parse
| "*)"
    { () }
| "(*"
    { comment lexbuf;
      comment lexbuf }
| '\n'
    { Lexing.new_line lexbuf;
      comment lexbuf }
| eof
    { failwith "unterminated comment" }
| _
    { comment lexbuf }

and string = parse
| '\"' { "" }
| (digit|lower|upper|space|symbol)+
  { let s = Lexing.lexeme lexbuf in
      s ^ (string lexbuf) }
| "\\n" { "\n" ^ (string lexbuf) }
| _
    { Format.eprintf "unknown token %s near characters %d-%d@."
        (Lexing.lexeme lexbuf)
        (Lexing.lexeme_start lexbuf)
        (Lexing.lexeme_end lexbuf);
      failwith "lex error" }
