(** Globals *)

(** {6 Exceptions} *)

exception Syntax_error of string
exception Semantic_error of string
exception Type_error of string
exception NotImplemented of string
exception NoMatch of string

(** {6 Options} *)

let debug = ref false
let debug_level = ref 30

let timeout = ref 100 (* sec *)
let timeout_z3 = ref 6000 (* ms *)

let print_log = ref false
let log_fileformatter = ref Format.std_formatter
let silent = ref false

let target_filename = ref "tmp"

let game_mode = ref false
let bench_mode = ref false

let cegar_iterations = ref 0
