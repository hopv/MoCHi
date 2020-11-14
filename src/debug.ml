open Util

let print ?(out=BatIO.stdout) x = BatPervasives.print_any out x

module type COND = sig
  val check : unit -> bool
end

module type DEBUG = sig
  val check : unit -> bool
  val printf : ('a, Format.formatter, unit) format -> 'a
  val eprintf : ('a, Format.formatter, unit) format -> 'a
  val fprintf : Format.formatter -> ('a, Format.formatter, unit) format -> 'a
  val exec : (unit -> unit) -> unit
  val tfprintf : Format.formatter -> ('a, Format.formatter, unit) format -> 'a
  val tprintf : ('a, Format.formatter, unit) format -> 'a
end

module Make (Cond : COND) : DEBUG = struct
  let check = Cond.check
  let fprintf fm f = if check() then Format.fprintf fm f else Format.ifprintf fm f
  let printf f = fprintf Format.std_formatter f
  let eprintf f = fprintf Format.err_formatter f
  let exec f = if check() then f ()
  let tfprintf ppf f = fprintf ppf ("[%.3f] " ^^ f) !!Time.get
  let tprintf f = tfprintf Format.std_formatter f
end
