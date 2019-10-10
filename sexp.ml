open Util

module Debug = Debug.Make(struct let check = Flag.Debug.make_check __MODULE__ end)

type t = A of string | S of t list

let rec parse_atom acc_rev s len i =
  let return () = Some (String.of_list @@ List.rev acc_rev) in
  if len <= i then
    i, !!return
  else
    match s.[i] with
    | c when Char.is_whitespace c -> i, !!return
    | ')' when acc_rev = [] -> i, None
    | ')' -> i, !!return
    | c -> parse_atom (c::acc_rev) s len (i+1)
let parse_atom = parse_atom []

let rec parse_list atom acc_rev s len i =
  if len <= i then
    i, List.rev acc_rev
  else
    match s.[i] with
    | c when Char.is_whitespace c -> parse_list atom acc_rev s len (i+1)
    | ')' -> i, List.rev acc_rev
    | '(' ->
        let i',ss = parse_list atom [] s len (i+1) in
        if i' >= len || s.[i'] <> ')' then invalid_arg "Sexp.parse_list";
        parse_list atom (S ss::acc_rev) s len (i'+1)
    | _ ->
        let i',r = atom s len i in
        match r with
        | None ->
            if i' < len then invalid_arg "Sexp.parse_list";
            i', List.rev acc_rev
        | Some a ->
            parse_list atom (A a::acc_rev) s len i'
let parse ?(parse_atom=parse_atom) s =
  let len = String.length s in
  let i,r = parse_list parse_atom [] s len 0 in
  if i < len then invalid_arg "Sexp.parse";
  r

let rec print fm s =
  match s with
  | A a -> Format.pp_print_string fm a
  | S ss -> Format.fprintf fm "@[(%a)@]" (print_list print " ") ss
