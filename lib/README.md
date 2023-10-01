# Ppx_mochi_term - Meta-programming for MoCHi

## Overview

Ppx_mochi_term is a library to generate types and terms of MoCHi.

You can use extension points `%term` and `%ty` for generating terms and types respectively.
For example, `[%term let x = 3 in f (x + 5)]` is translated into
`Term.(let_ [x, int 3] (var f @@ [var x + int 5]))` and `[%ty: int * bool -> int]`.
is translated into `Ty.(fun_ (tuple int bool) int)`.
(Stricly speaking, either `Term.` or `Ty.` is followed by each variables.
For example, `[%term x + 5]` is translated into `[Term.(+) (Term.var x) (Term.int 5)]`)

You can also use `%e` in extension points for dynamic codes.
For example, `let t = Term.int 10 in [%term x + [%e t]]` is tranlated into
`let t = Term.int 10 in Term.(var x + t)`.

## Supported features

Supported features are listed below.
Meta-variables are written in uppercases.
`X` is a meta-variable for variables.
`N` is a meta-variable for integers.

```
T (terms) ::=
  | ()
  | X
  | lid X
  | N
  | int X
  | T @@ T   (* T must be a list *)
  | T @ T    (* same as @@ *)
  | [%e e]   (* dynamic code *)
  | `X       (* same as [%e X] *)
  | true
  | false
  | [] TA
  | []       (* `typ` must be declared for the type of `[]` *)
  | T::T
  | None
  | Some T
  | assert T
  | let _ = T in T
  | let X X ... X = T and ... in T
  | let rec X X ... X = T and ... in T
  | raise T TA
  | raise T  (* `typ` must be declared for the type of `raise T` *)
  | T OP T
  | F T ... T
  | fun X ... X -> T
  | if T then T else T
  | if T then T
  | assert T
  | (T, ..., T)
  | T; T
  | assume T; T
  | lazy T
  | match T with CASE | ... | CASE

OP (binary operators) ::=
  | &&
  | ||
  | =>
  | +
  | -
  | *
  | /
  | |+| (* non-deterministic branch *)
  | =
  | <>
  | <
  | >
  | <=
  | >=
  | <|
  | |>
  | :=
  | |-> (* substitution *)
  | ##  (* projection *)

F (primitive functions) ::=
  | not
  | ands   (* same as `List.fold_right (&&) true` *)
  | ors    (* same as `List.fold_right (||) false` *)
  | ~-
  | br
  | brs    (* br for a list *)
  | fst
  | snd
  | ignore
  | !
  | ref
  | seqs   (* same as `List.fold_right (fun t1 t2 -> [%term [%e t1]; [%e t2])` *)
  | length (* List.length *)

CASE (pattern matching cases) ::=
  | P -> T
  | P when T -> T

P (patterns) ::=
  | X
  | N
  | (_ : typ)
  | _ TA
  | _   (* `typ` must be declared for the type of `_` *)
  | (P, ..., P)
  | P as X
  | (P | P)

TY (types) ::=
  | unit
  | bool
  | int
  | string
  | unknown   (* Ty.unknown *)
  | result    (* Ty.result *)
  | abst      (* Ty.abst *)
  | (TY, ..., TY) C
  | TY -> TY
  | [%e e]    (* dynamic code *)
  | 'X        (* same as [%e X] *)
  | TY * ... * TY

TA (type annotations) ::=
  | [@ty: TY]
  | [@ty TY]  (* same as [@ty: [%e TY]] *)
```

# Macros
- `[%unsupported]` is expanded to `unsupporet "%s" __FUNCTION__`
- `[%invalid_arg]` is expanded to `invalid_arg "%s" __FUNCTION__`
- `[%pr_loc]` is expanded to `Format.printf "%s" __LOC__`
