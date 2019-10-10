{
open Util
open HorSat_parser
}

let space = [' ' '\t' '\r']
let digit = ['0'-'9']
let lower = ['a'-'z' '_']
let upper = ['A'-'Z']

rule header = parse
| "The property is satisfied." { SATISFIED }
| "The property is NOT satisfied." { UNSATISFIED }
| '\n' { Lexing.new_line lexbuf; header lexbuf }
| _ { header lexbuf }
| eof { failwith "lex error" }

and token = parse
| "HorSat" { header lexbuf }
| "HorSat2" { header lexbuf }
| "The size of typing:" { THE_SIZE_OF_TYPING }
| "A counterexample is:" { A_COUNTEREXAMPLE_IS }
| "The property is satisfied." { SATISFIED }
| "The property is NOT satisfied." { UNSATISFIED }
| space+ { token lexbuf }
| "Top" { TOP }
| "~q" digit+
    {
      let s = Lexing.lexeme lexbuf in
      let _,s2 = String.split_nth s 2 in
      STATE (int_of_string s2)
    }
| '\n' { Lexing.new_line lexbuf; token lexbuf }
| '(' { LPAREN }
| ')' { RPAREN }
| '.' { DOT }
| ',' { COMMA }
| ':' { COLON }
| '^' { CARET }
| "->" { ARROW }
| "br_exists" { BR_EXISTS }
| "br_forall" { BR_FORALL }
| '_' { BOT }
| "unit" { UNIT }
| "event_fail" { FAIL }
| ('$'|lower|upper) (digit|lower|upper)* { IDENT (Lexing.lexeme lexbuf) }
| digit+ { INT (int_of_string (Lexing.lexeme lexbuf)) }
| "Elapsed Time:" { EOF }
| eof { EOF }
| _ { Format.eprintf "ERROR:%s@." (Lexing.lexeme lexbuf); failwith "lex error" }
