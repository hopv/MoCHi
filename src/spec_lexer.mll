{
open Spec_parser
}

let space = [' ' '\t' '\r']
let digit = ['0'-'9']
let lower = ['a'-'z' '_']
let lower' = ['a'-'z' '_' '\'']
let upper = ['A'-'Z']
let uident = upper(digit|lower'|upper)*
let lident = lower(digit|lower'|upper)*

rule token = parse
| space+      { token lexbuf }
| '\n'        { Lexing.new_line lexbuf;
                token lexbuf }
| "(*"        { comment lexbuf;
                token lexbuf }
| '('         { LPAREN }
| ')'         { RPAREN }
| '['         { LSQUAR }
| ']'         { RSQUAR }
| '{'         { LBRACE }
| '}'         { RBRACE }
| '='         { EQUAL }
| '<'         { LTHAN }
| '>'         { GTHAN }
| "<="        { LEQ }
| ">="        { GEQ }
| "<>"        { NEQ }
| "||"        { OR }
| "&&"        { AND }
| "not"       { NOT }
| '+'         { PLUS }
| '-'         { MINUS }
| '*'         { TIMES }
| '/'         { DIV }
| "inline"    { INLINE }
| "inlinef"   { INLINEF }
| "unit"      { TUNIT }
| "X"         { TRESULT }
| "bool"      { TBOOL }
| "int"       { TINT }
| "list"      { LIST }
| "->"        { ARROW }
| ';'         { SEMI }
| ':'         { COLON }
| '|'         { BAR }
| ','         { COMMA }
| '\''        { PRIME }
| "assert"    { ASSERT }
| "type"      { TYPE }
| "val"       { VAL }
| "valcps"    { VALCPS }
| "valcegar"  { VALCEGAR }
| "external"  { EXTERNAL }
| "fairness"  { FAIRNESS }
| "true"      { TRUE }
| "false"     { FALSE }
| "match"     { MATCH }
| "with"      { WITH }
| "/\\"       { INTER }
| "\\/"       { UNION }
| "_"         { UNDER_SCORE }
| digit+ as n { INT(int_of_string n) }
| (uident '.')* lident as x
              { LIDENT x }
| (uident '.')* uident as x
              { UIDENT x }
| "#randint_"digit+ as x
              { LIDENT x }
| (lower|upper)(digit|lower|upper)* as x (* Unreachabel? *)
              { EVENT x }
| "@"         { AT }
| '"' ([^'"''\\'] | '\\'['\x00'-'\xff'])+ '"'
              { let lexeme =
                  Bytes.sub_string
                    lexbuf.lex_buffer
                    (lexbuf.lex_start_pos + 1)
                    (lexbuf.lex_curr_pos - lexbuf.lex_start_pos - 2) in
                STRING(Scanf.unescaped lexeme) }
| eof         { EOF }
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
