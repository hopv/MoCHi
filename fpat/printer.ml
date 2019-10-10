open Combinator

(** Printer combinators *)

type 'a t = Format.formatter -> 'a -> unit

let coerce f pr = fun ppf x -> pr ppf (f x)
let paren pr = fun ppf x -> Format.fprintf ppf "@[(%a)@]" pr x
let paren_tex pr = fun ppf x ->
  Format.fprintf ppf "@[\\left(%a\\right)@]" pr x
let upr_of pr arg = fun ppf () -> pr ppf arg
let rec concat_uprs_aux uprs sep = fun ppf () ->
  match uprs with
  | [] -> ()
  | [upr] -> upr ppf ()
  | upr :: uprs' ->
    Format.fprintf ppf
      "%a%a%a"
      upr ()
      Format.fprintf sep
      (concat_uprs_aux uprs' sep) ()

let concat_uprs uprs sep = fun ppf () ->
  Format.fprintf ppf "@[<hov>%a@]" (concat_uprs_aux uprs sep) ()

let concat_uprs_app (upr :: uprs) sep = fun ppf () ->
  if uprs = [] then upr ppf ()
  else
    Format.fprintf ppf
      "@[<hov2>%a@ @[<hov>%a@]@]"
      upr ()
      (concat_uprs_aux uprs sep) ()

let string_of pr x =
  Format.fprintf Format.str_formatter "@[<h>%a@]" pr x;
  Format.flush_str_formatter ()

let print_parser_error_information () =
  let st = Parsing.symbol_start_pos () in
  let en = Parsing.symbol_end_pos () in
  Format.printf
    "File \"%s\", line %d"
    st.Lexing.pos_fname
    st.Lexing.pos_lnum;
  Format.printf
    ", parser error near characters %d-%d:\n"
    (st.Lexing.pos_cnum - st.Lexing.pos_bol)
    (en.Lexing.pos_cnum - en.Lexing.pos_bol)

let print_lexer_error_information lexbuf =
  let st = Lexing.lexeme_start_p lexbuf in
  let en = Lexing.lexeme_end_p lexbuf in
  Format.printf
    "File \"%s\", line %d"
    st.Lexing.pos_fname
    st.Lexing.pos_lnum;
  Format.printf
    ", unknown token %s near characters %d-%d"
    (Lexing.lexeme lexbuf)
    (st.Lexing.pos_cnum - st.Lexing.pos_bol)
    (en.Lexing.pos_cnum - en.Lexing.pos_bol)
