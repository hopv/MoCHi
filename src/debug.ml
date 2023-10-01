open Util

let print ?(out=BatIO.stdout) x = BatPervasives.print_any out x

module type COND = sig
  val check : unit -> bool
end

module type DEBUG = sig
  val force : bool option ref
  val on : unit -> unit
  val off : unit -> unit
  val reset : unit -> unit
  val check : unit -> bool

  val set_default_formatter : Format.formatter -> unit

  val kfprintf : (Format.formatter -> 'a) -> Format.formatter -> ('b, Format.formatter, unit, 'a) format4 -> 'b
  val printf : ?color:Color.t -> ?fm:Format.formatter -> ('a, Format.formatter, unit) format -> 'a
  val eprintf : ('a, Format.formatter, unit) format -> 'a
  val fprintf : Format.formatter -> ('a, Format.formatter, unit) format -> 'a
  val exec : (unit -> unit) -> unit
  val tfprintf : Format.formatter -> ('a, Format.formatter, unit) format -> 'a
  val tprintf : ('a, Format.formatter, unit) format -> 'a
end

module Make (Cond : COND) : DEBUG = struct
  let force = ref None
  let on () = force := Some true
  let off () = force := Some false
  let reset () = force := None
  let check () = match !force with Some b -> b | _ -> Cond.check ()

  let default_formatter = ref Format.std_formatter
  let set_default_formatter fm = default_formatter := fm

  let kfprintf k fm f = if check() then Format.kfprintf k fm f else Format.ikfprintf k fm f
  let fprintf fm f = if check() then Format.fprintf fm f else Format.ifprintf fm f
  let printf ?color ?(fm = !default_formatter) f =
    match color with
    | None -> fprintf fm f
    | Some c -> kfprintf Color.reset fm ("%a"^^f) Color.set c
  let eprintf f = fprintf Format.err_formatter f
  let exec f = if check() then f ()
  let tfprintf ppf f = fprintf ppf ("[%.3f] " ^^ f) !!Time.get
  let tprintf f = tfprintf Format.std_formatter f
end

(* This function uses '\b' *)
let print_begin_end ?(fm=Format.std_formatter) =
  let pre fm = Format.fprintf fm "%s" "BEGIN" in
  let post fm _r = Format.fprintf fm "%s" "END" in
  fun ?(pre=pre) ?(post=post) () f ->
    Format.fprintf fm "@[<v 2>%t@ " pre;
    f ()
    |@> Format.fprintf fm "@]\b\b%a@\n" post

let depth = ref 0
let (let**) =
  fun s k ->
    incr depth;
    Format.printf "BEGIN [%d]: %s@." !depth s;
    let r = k () in
    Format.printf "END [%d]: %s@." !depth s;
    decr depth;
    r
