
type program = {
  fun_typ_env : Ref_type.env;
  fun_typ_neg_env : Ref_type.neg_env;
  fun_def_env : (Syntax.id * Syntax.term) list;
  exn_decl : (string * Syntax.typ list) list;
}

type label = int
type ce = (label * bool) list
type ce_set = (Syntax.id * ce) list

val print_typ_env : Format.formatter -> Ref_type.Env.t -> unit
val print_typ_neg_env : Format.formatter -> Ref_type.NegEnv.t -> unit
val print_def_env : Format.formatter -> (Syntax.id * Syntax.term) list -> unit
val print_prog : Format.formatter -> program -> unit
val print_ce : Format.formatter -> ce -> unit
val print_ce_set : Format.formatter -> ce_set -> unit

val compose_id : ?nid:int -> ?arg:int -> Syntax.id -> Syntax.id
val decomp_id : Syntax.id -> string * int option * int list
val same_top_fun : Syntax.id -> Syntax.id -> bool
val is_atom : Syntax.term -> bool
val normalize : bool -> Syntax.term -> Syntax.term
val used_by : Syntax.id -> program -> Syntax.id list
val term_of_prog : program -> Syntax.term
val take_funs_of_depth : (Syntax.id * Syntax.term) list -> Syntax.id -> int -> Syntax.id list
