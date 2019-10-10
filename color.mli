
type color =
  | Default
  | Bright
  | Dim
  | Underscore
  | Blink
  | Reverse
  | Hidden
  | Black
  | Red
  | Green
  | Yellow
  | Blue
  | Magenta
  | Cyan
  | White
  | BG_Black
  | BG_Red
  | BG_Green
  | BG_Yellow
  | BG_Blue
  | BG_Magenta
  | BG_Cyan
  | BG_White

val init : unit -> unit
val set : Format.formatter -> color -> unit
val reset : Format.formatter -> unit
val wrap : color -> (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit

val fprintf : Format.formatter -> color -> ('a, Format.formatter, unit) format -> 'a
val printf : color -> ('a, Format.formatter, unit) format -> 'a
(** Partial application does not work *)

val blue : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit
val red : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit
val green : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit
val cyan : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit
val yellow : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a -> unit

val s_blue : Format.formatter -> string -> unit
val s_red : Format.formatter -> string -> unit
val s_green : Format.formatter -> string -> unit
val s_cyan : Format.formatter -> string -> unit
val s_yellow : Format.formatter -> string -> unit
