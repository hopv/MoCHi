{
  open HORS_parser
  exception LexerError of string
}

let digit = ['0'-'9']
let space = [' ' '\t' '\r']
let char  = ['a'-'z' 'A'-'Z' '$' '_']
let symbol = ['{' '}' '[' ']' '\\' '/' '-' '>']
let ident = char (char | digit | symbol)*

rule token = parse
| space+
    { token lexbuf }
| '\n'
    { Lexing.new_line lexbuf; token lexbuf }
| ident as id
    { IDENT id }
| '.'  { DOT }
| '_'  { UNDERSCORE }
| '('  { LPAREN }
| ')'  { RPAREN }
| "->" { ARROW }
| eof { EOF }
| "(*"
    { comment lexbuf }
| _
    { raise (LexerError ("illegal token " ^ Lexing.lexeme lexbuf)) }

and comment = parse
| "*)"
    { token lexbuf }
| '\n'
    { Lexing.new_line lexbuf;
      comment lexbuf }
| eof
    { raise (LexerError "unterminated comment") }
| _
    { comment lexbuf }
