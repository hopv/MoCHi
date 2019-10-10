open Combinator

(** Timers *)

let timers = ref []

let make () =
  let st = Unix.times () in
  (fun () ->
     let en = Unix.times () in
     (en.Unix.tms_utime -. st.Unix.tms_utime) +.
     (en.Unix.tms_cutime -. st.Unix.tms_cutime))

let start () = timers := make () :: !timers

let stop () =
  match !timers with
  | [] -> assert false
  | tm :: tms -> timers := tms; tm ()

let start_time = ref (Unix.times ())
let start_interval () = start_time := Unix.times ()
let interval () =
  let en = Unix.times () in
  (en.Unix.tms_utime -. !start_time.Unix.tms_utime) +.
  (en.Unix.tms_cutime -. !start_time.Unix.tms_cutime)

exception Timeout

let sigalrm_handler =
  Sys.Signal_handle (fun _ -> Format.printf "timeout!!!@,"; raise Timeout)

let sigalrm_catched = ref false
let sigalrm_delayed_handler =
  Sys.Signal_handle
    (fun _ -> Format.printf "timeout!!!@,"; sigalrm_catched := true)

let disable_timeout f arg =
  sigalrm_catched := false;
  let reset_sigalrm_handler =
    let old_handler = Sys.signal Sys.sigalrm sigalrm_delayed_handler in
    fun () -> Sys.set_signal Sys.sigalrm old_handler
  in
  try
    let ret = f arg in
    reset_sigalrm_handler ();
    if !sigalrm_catched then
      raise Timeout (* @todo may differ from the behavior of [old_handler] *)
    else ret
  with exc -> reset_sigalrm_handler (); raise exc


let block ?(timeout = 0) before after main =
  hook true
    (before >> start)
    after
    (fun () ->
       let reset_sigalrm_handler =
         if timeout > 0 then
           begin
             let old_handler = Sys.signal Sys.sigalrm sigalrm_handler in
             Unix.alarm timeout;
             fun () -> Sys.set_signal Sys.sigalrm old_handler
           end
         else fun () -> ()
       in
       try
         let ret = main () in
         reset_sigalrm_handler ();
         stop (), ret
       with exc -> reset_sigalrm_handler (); stop (); raise exc)
