{
open Syntax
open Spec_parser
}

let space = [' ' '\t' '\r']
let digit = ['0'-'9']
let lower = ['a'-'z' '_' '\'']
let upper = ['A'-'Z']

rule token = parse
| space+
    { token lexbuf }
| '\n'
    { Lexing.new_line lexbuf;
      token lexbuf }
| "(*"
    { comment lexbuf;
      token lexbuf }
| '(' { LPAREN }
| ')' { RPAREN }
| '[' { LSQUAR }
| ']' { RSQUAR }
| '{' { LBRACE }
| '}' { RBRACE }
| '=' { EQUAL }
| '<' { LTHAN }
| '>' { GTHAN }
| "<=" { LEQ }
| ">=" { GEQ }
| "<>" { NEQ }
| "||" { OR }
| "&&" { AND }
| "not" { NOT }
| '+' { PLUS }
| '-' { MINUS }
| '*' { TIMES }
| '/' { DIV }
| "inline" { INLINE }
| "inlinef" { INLINEF }
| "unit" { TUNIT }
| "X" { TRESULT }
| "bool" { TBOOL }
| "int" { TINT }
| "list" { LIST }
| "->" { ARROW }
| ';' { SEMI }
| ':' { COLON }
| '|' { BAR }
| ',' { COMMA }
| "type" { TYPE }
| "val" { VAL }
| "valcps" { VALCPS }
| "valcegar" { VALCEGAR }
| "external" { EXTERNAL }
| "fairness" { FAIRNESS }
| "true" { TRUE }
| "false" { FALSE }
| "match" { MATCH }
| "with" { WITH }
| "end" { END }
| "/\\" { INTER }
| "\\/" { UNION }
| "_" { UNDER_SCORE }
| digit+ { INT(int_of_string (Lexing.lexeme lexbuf)) }
| (upper(digit|lower|upper)*'.')*lower(digit|lower|upper)* { LIDENT(Lexing.lexeme lexbuf) }
| (upper(digit|lower|upper)*'.')*upper(digit|lower|upper)* { UIDENT(Lexing.lexeme lexbuf) }
| "#randint_"digit+ { LIDENT(Lexing.lexeme lexbuf) }
| (lower|upper)(digit|lower|upper)* { EVENT(Lexing.lexeme lexbuf) }
| eof { EOF }
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
