
(** Checking feasibility *)

(**
The target of the current implementation is call-by-value.
*)

(*
val get_prefix: Syntax.node list -> (Syntax.id * ('a * Syntax.typed_term)) list -> Syntax.typed_term -> Syntax.node list
(** [get_prefix ce defs s] calculates the shortest infeasible prefix.
    If [ce] is feasibele, it raises exception [Feasible].
    [defs] is function definitions.
    [s] is the main of a program.
*)
*)
type result =
  | Feasible of int list
  | FeasibleNonTerm of bool * (string * CEGAR_syntax.typ) list * int list
  | Infeasible of CEGAR_syntax.ce


val check: CEGAR_syntax.ce -> CEGAR_syntax.prog -> result

(** [check ce defs s] checks whether [ce] is feasible or not．
    [defs] is function definitions.
    [s] is the main of a program.
*)

val check_non_term: ?map_randint_to_preds:(int * (CEGAR_syntax.t -> CEGAR_syntax.t list)) list -> ?ext_ce:(int * bool list) list -> CEGAR_syntax.ce -> CEGAR_syntax.prog -> result

val trans_ce: CEGAR_syntax.ce -> CEGAR_syntax.prog -> bool list
val print_ce_reduction: ?map_randint_to_preds:(int * (CEGAR_syntax.t -> CEGAR_syntax.t list)) list -> ?ext_ce:(int * bool list) list -> CEGAR_syntax.ce -> CEGAR_syntax.prog -> unit

(*
val check_int: Syntax.node list -> (Syntax.id * ('a * Syntax.typed_term)) list -> Syntax.typed_term -> Syntax.typed_term * Syntax.node list
(** ??? *)
*)
