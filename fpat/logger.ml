open Combinator

(** Logger *)

(** @todo use logger monad *)

type log_kinds = Error | Warning | Debug | Trace

let current_level = ref 0
let call_stack = ref []
let call_id = ref 0

let filter_call_id = ref (-1)
let filter_regexp = ref (Str.regexp ".")
let fun_stack = ref [] (* for optimization *)
let call_id_stack = ref 0 (* for optimization *)
let filter_exact = ref false (* whether print logs of ancestor calls *)
let filter_kinds = ref [Error; Warning; Debug; Trace]
let print_call_stack_on_exception = ref true

let check_exact b = if !filter_exact then b else true
let check_exact_from_printf () =
  if not !filter_exact then true
  else
    let call = !call_stack |> List.hd in
    let b_fun =
      if !fun_stack = [] then false else
        List.hd !fun_stack = Str.replace_first (Str.regexp "([0-9]+)") "" call
    in
    let b_call_id =
      let id =
        ignore(Str.search_forward (Str.regexp "[0-9]+") call 0);
        Str.matched_string call
        |> int_of_string
      in
      !filter_call_id = id
    in
    b_fun || b_call_id

let check_filter str =
  Str.string_match !filter_regexp str 0 &&
  (!filter_call_id = -1 || !filter_call_id = !call_id)
let check_kinds k = List.mem k !filter_kinds

let check () =
  !Global.debug
  && !Global.debug_level >= !current_level
  && !fun_stack <> []
  && !call_id_stack > 0

let ppf = ref Format.std_formatter
let oc = ref None
let get_oc () = match !oc with None -> stdout | Some(oc) -> oc

let log_begin str =
  Timer.disable_timeout
    (fun () ->
       (*if !call_stack = [] then
           Format.fprintf !ppf "@[<v>";*)
       call_id := !call_id + 1;
       current_level := !current_level + 1;
       let filter = check_filter str in
       (if filter then
          (fun_stack := str :: !fun_stack;
           call_id_stack := !call_id_stack + 1));
       let call = str ^ "(" ^ string_of_int !call_id ^ ")" in
       if check () && check_exact filter && check_kinds Trace then
         Format.fprintf !ppf "begin %s[%d]@,  @[<v>" call !current_level;
       call_stack := call :: !call_stack;
       Timer.start ())
    ()

let log_end str =
  Timer.disable_timeout
    (fun () ->
       let tm = Timer.stop () in
       let call =
         match !call_stack with
         | [] -> assert false
         | call :: call_stack' ->
           call_stack := call_stack';
           if check () && check_exact (check_filter str) && check_kinds Trace then
             (* do not remove "@," just before "end" *)
             Format.fprintf !ppf
               "@]@,end %s[%d] (%f sec.)@,"
               call !current_level tm;
           call
       in
       (match !fun_stack with
        | x::xs -> if x = str then fun_stack := xs
        | _ -> ());
       let id =
         ignore(Str.search_forward (Str.regexp "[0-9]+") call 0);
         Str.matched_string call
         |> int_of_string
       in
       (if !filter_call_id = id then call_id_stack := !call_id_stack - 1);
       current_level := !current_level - 1)
    ()

let initialize filename =
  if !Global.debug then begin
    let oc_ = open_out filename in
    oc := Some(oc_);
    ppf :=
      if !Global.print_log then Format.std_formatter
      else Format.formatter_of_out_channel oc_;
    Format.fprintf !ppf "@[<v>";
    log_begin "FPAT"
  end

let finalize () =
  if !Global.debug then begin
    log_end "FPAT";
    Format.fprintf !ppf "@]@.";
    match !oc with None -> () | Some(oc) -> close_out oc
  end

let print_fpat_call_stack () =
  Format.fprintf !ppf "FPAT call stack:@,  @[<v>";
  List.iteri (fun i ->
      if i = List.length !call_stack - 1
      then Format.fprintf !ppf "%s"
      else Format.fprintf !ppf "%s@,")
    !call_stack;
  Format.fprintf !ppf "@]@,"

let print_ocaml_call_stack () =
  let ss =
    BatString.nsplit
      (Printexc.raw_backtrace_to_string (Printexc.get_callstack 10000))
      "\n"
    |> List.filter ((<>) "")
  in
  Format.fprintf !ppf "OCaml call stack:@,  @[<v>";
  List.iteri (fun i ->
      if i = List.length ss - 1
      then Format.fprintf !ppf "%s"
      else Format.fprintf !ppf "%s@,")
    ss;
  Format.fprintf !ppf "@]@,"

let handle_sigint =
  Sys.set_signal
    Sys.sigint
    (Sys.Signal_handle
       (fun _ ->
          Format.printf "@.^C@.";
          Format.fprintf !ppf "@.^C@.";
          exit 0))

let log_block1
    str
    ?(before = fun x1 -> ())
    ?(after = fun ret -> ())
    ?(on_exception = fun exc -> ())
    f x1 =
  try
    log_begin str;
    before x1;
    let ret = f x1 in
    after ret;
    log_end str;
    ret
  with exc ->
    on_exception exc;
    if check () && check_exact (check_filter str) && check_kinds Error then begin
      Format.fprintf !ppf
        "@[<v>an exception raised:@,  %s@]@,"
        (Printexc.to_string exc);
      if !print_call_stack_on_exception then begin
        print_fpat_call_stack ();
        print_ocaml_call_stack ()
      end
    end;
    log_end str;
    raise exc

let log_block2
    str
    ?(before = fun x1 x2 -> ())
    ?(after = fun ret -> ())
    ?(on_exception = fun exc -> ())
    f x1 x2 =
  try
    log_begin str;
    before x1 x2;
    let ret = f x1 x2 in
    after ret;
    log_end str;
    ret
  with exc ->
    on_exception exc;
    if check () && check_exact (check_filter str) && check_kinds Error then begin
      Format.fprintf !ppf
        "@[<v>an exception raised:@,  %s@]@,"
        (Printexc.to_string exc);
      if !print_call_stack_on_exception then begin
        print_fpat_call_stack ();
        print_ocaml_call_stack ()
      end
    end;
    log_end str;
    raise exc

let log_block3
    str
    ?(before = fun x1 x2 x3 -> ())
    ?(after = fun ret -> ())
    ?(on_exception = fun exc -> ())
    f x1 x2 x3 =
  try
    log_begin str;
    before x1 x2 x3;
    let ret = f x1 x2 x3 in
    after ret;
    log_end str;
    ret
  with exc ->
    on_exception exc;
    if check () && check_exact (check_filter str) && check_kinds Error then begin
      Format.fprintf !ppf
        "@[<v>an exception raised:@,  %s@]@,"
        (Printexc.to_string exc);
      if !print_call_stack_on_exception then begin
        print_fpat_call_stack ();
        print_ocaml_call_stack ()
      end
    end;
    log_end str;
    raise exc

let log_block4
    str
    ?(before = fun x1 x2 x3 x4 -> ())
    ?(after = fun ret -> ())
    ?(on_exception = fun exc -> ())
    f x1 x2 x3 x4 =
  try
    log_begin str;
    before x1 x2 x3 x4;
    let ret = f x1 x2 x3 x4 in
    after ret;
    log_end str;
    ret
  with exc ->
    on_exception exc;
    if check () && check_exact (check_filter str) && check_kinds Error then begin
      Format.fprintf !ppf
        "@[<v>an exception raised:@,  %s@]@,"
        (Printexc.to_string exc);
      if !print_call_stack_on_exception then begin
        print_fpat_call_stack ();
        print_ocaml_call_stack ()
      end
    end;
    log_end str;
    raise exc

let log_block5
    str
    ?(before = fun x1 x2 x3 x4 x5 -> ())
    ?(after = fun ret -> ())
    ?(on_exception = fun exc -> ())
    f x1 x2 x3 x4 x5 =
  try
    log_begin str;
    before x1 x2 x3 x4 x5;
    let ret = f x1 x2 x3 x4 x5 in
    after ret;
    log_end str;
    ret
  with exc ->
    on_exception exc;
    if check () && check_exact (check_filter str) && check_kinds Error then begin
      Format.fprintf !ppf
        "@[<v>an exception raised:@,  %s@]@,"
        (Printexc.to_string exc);
      if !print_call_stack_on_exception then begin
        print_fpat_call_stack ();
        print_ocaml_call_stack ()
      end
    end;
    log_end str;
    raise exc

let log_block6
    str
    ?(before = fun x1 x2 x3 x4 x5 x6 -> ())
    ?(after = fun ret -> ())
    ?(on_exception = fun exc -> ())
    f x1 x2 x3 x4 x5 x6 =
  try
    log_begin str;
    before x1 x2 x3 x4 x5 x6;
    let ret = f x1 x2 x3 x4 x5 x6 in
    after ret;
    log_end str;
    ret
  with exc ->
    on_exception exc;
    if check () && check_exact (check_filter str) && check_kinds Error then begin
      Format.fprintf !ppf
        "@[<v>an exception raised:@,  %s@]@,"
        (Printexc.to_string exc);
      if !print_call_stack_on_exception then begin
        print_fpat_call_stack ();
        print_ocaml_call_stack ()
      end
    end;
    log_end str;
    raise exc


(** never fails in the no-debugging mode *)
let debug_assert ?(on_failure = fun () -> ()) e =
  if !Global.debug && not (e ()) then begin
    on_failure ();
    Format.fprintf !ppf "assertion failed!@,";
    print_fpat_call_stack ();
    print_ocaml_call_stack ();
    assert false
  end

let debug_assert_false ?(on_failure = fun () -> ()) () =
  debug_assert ~on_failure:on_failure (fun () -> false);
  assert false

let log ?(force = false) f = if force || check () then f ()

let printf0 ?(force = false) ?(kind = Debug) fmt =
  if force || (check () && check_exact_from_printf () && check_kinds kind) then Format.fprintf !ppf fmt
let printf ?(force = false) ?(kind = Debug) fmt pr x =
  if force || (check () && check_exact_from_printf () && check_kinds kind) then Format.fprintf !ppf fmt pr x
let printf2 ?(force = false) ?(kind = Debug) fmt pr1 x1 pr2 x2 =
  if force || (check () && check_exact_from_printf () && check_kinds kind) then Format.fprintf !ppf fmt pr1 x1 pr2 x2
let printf3 ?(force = false) ?(kind = Debug) fmt pr1 x1 pr2 x2 pr3 x3 =
  if force || (check () && check_exact_from_printf () && check_kinds kind) then Format.fprintf !ppf fmt pr1 x1 pr2 x2 pr3 x3
let printf4 ?(force = false) ?(kind = Debug) fmt pr1 x1 pr2 x2 pr3 x3 pr4 x4 =
  if force || (check () && check_exact_from_printf () && check_kinds kind) then Format.fprintf !ppf fmt pr1 x1 pr2 x2 pr3 x3 pr4 x4
let printf5 ?(force = false) ?(kind = Debug) fmt pr1 x1 pr2 x2 pr3 x3 pr4 x4 pr5 x5 =
  if force || (check () && check_exact_from_printf () && check_kinds kind) then Format.fprintf !ppf fmt pr1 x1 pr2 x2 pr3 x3 pr4 x4 pr5 x5

let pprintf0 ?(force = false) ?(kind = Debug) fmt x =
  if force || (check () && check_exact_from_printf () && check_kinds kind) then Format.fprintf !ppf fmt;
  x
let pprintf ?(force = false) ?(kind = Debug) fmt pr x =
  printf ~force:force ~kind:kind fmt pr x; x
let pprintf2 ?(force = false) ?(kind = Debug) fmt pr1 x1 pr2 x2 =
  printf2 ~force:force ~kind:kind fmt pr1 x1 pr2 x2; x2
