(** {6 Translator for CEGAR_syntax} *)

val conv_typ : CEGAR_syntax.typ -> Fpat.Type.t
val conv_const : CEGAR_syntax.const -> Fpat.Const.t
val conv_var : string -> Fpat.Idnt.t
val conv_term : CEGAR_syntax.env -> CEGAR_syntax.t -> Fpat.Term.t
val conv_formula : CEGAR_syntax.t -> Fpat.Formula.t
val conv_event : CEGAR_syntax.event -> Fpat.Term.t
val conv_fdef : CEGAR_syntax.env -> CEGAR_syntax.fun_def -> Fpat.Fdef.t
val conv_prog : CEGAR_syntax.prog -> Fpat.Prog.t

val conv_pred : CEGAR_syntax.env -> CEGAR_syntax.t -> Fpat.Pred.t

val inv_const : Fpat.Const.t -> CEGAR_syntax.const
val inv_term : Fpat.Term.t -> CEGAR_syntax.t
val inv_formula : Fpat.Formula.t -> CEGAR_syntax.t
val inv_fdef : Fpat.Fdef.t -> string * Fpat.Pattern.t list * CEGAR_syntax.t * 'a list * CEGAR_syntax.t
val inv_abst_type : Fpat.AbsType.t -> CEGAR_syntax.typ


(** {6 Translator for Syntax} *)

val trans_type : 'a Type.t -> 'a Type.t
val trans_id : 'a Type.t Id.t -> 'a Type.t Id.t
val of_term : Syntax.term -> Fpat.Term.t


(** {6 SMT solver} *)

val implies :
  ?tenv:Fpat.TypEnv.t -> Fpat.Formula.t list -> Fpat.Formula.t list -> bool
val is_sat : ?tenv:Fpat.TypEnv.t -> Fpat.Formula.t -> bool
val is_valid : Fpat.Formula.t -> bool
val is_valid_forall_exists :
  string list -> string list -> CEGAR_syntax.t list -> CEGAR_syntax.t -> bool


(** {6 Misc} *)

val infer :
  (Fpat.HCCSSolver.t -> Fpat.HCCSSolver.t) ->
  string list ->
  (Fpat.Idnt.t -> bool) ->
  int list list ->
  (Fpat.Idnt.t * Fpat.Pred.t list) list list ->
  CEGAR_syntax.prog ->
  (string * CEGAR_syntax.typ) list
val infer_with_ext :
  string list ->
  (Fpat.Idnt.t -> bool) ->
  int list list ->
  (Fpat.Idnt.t * Fpat.Pred.t list) list list ->
  CEGAR_syntax.prog ->
  (string * CEGAR_syntax.typ) list

val parse_arg : string -> unit
val compute_strongest_post :
  CEGAR_syntax.prog ->
  int list ->
  (Fpat.Idnt.t * ((Fpat.Idnt.t * Fpat.Type.t) list * Fpat.Formula.t) list) list ->
  (Fpat.Idnt.t * Fpat.Type.t) list * Fpat.Formula.t

val insert_extra_param : Syntax.term -> Syntax.term
val instantiate_param : CEGAR_syntax.prog -> CEGAR_syntax.env * CEGAR_syntax.fun_def list * CEGAR_syntax.var

val is_cp : CEGAR_syntax.prog -> Fpat.Idnt.t -> bool

val trans_ext :
  (int * CEGAR_syntax.env) list ->
  (int * (CEGAR_syntax.t -> CEGAR_syntax.t list)) list ->
  int * CEGAR_util.ext_path_part list list -> Fpat.Idnt.t * Fpat.Pred.t list

val to_hcs : (Syntax.term list * Syntax.term) list -> Fpat.HornClause.t list
