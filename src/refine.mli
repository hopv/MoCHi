
(** CEGAR *)

exception CannotRefute

val refine :
  string list ->
  (Fpat.Idnt.t -> bool) ->
  CEGAR_syntax.ce -> CEGAR_syntax.ce list ->
  ((Fpat.Idnt.t * Fpat.Pred.t list) list) list ->
  CEGAR_syntax.prog ->
  (CEGAR_syntax.var * CEGAR_syntax.typ) list * CEGAR_syntax.prog
(** [refine prefix traces t] で，反例のリスト [traces] を用いて [t] の述語発見を行う．
*)

val refine_with_ext :
  string list ->
  (Fpat.Idnt.t -> bool) ->
  CEGAR_syntax.ce -> CEGAR_syntax.ce list ->
  ((Fpat.Idnt.t * Fpat.Pred.t list) list) list ->
  CEGAR_syntax.prog ->
  (CEGAR_syntax.var * CEGAR_syntax.typ) list * CEGAR_syntax.prog

val add_preds_env : CEGAR_syntax.env -> CEGAR_syntax.env -> CEGAR_syntax.env

val add_preds : CEGAR_syntax.env -> CEGAR_syntax.prog -> CEGAR_syntax.prog

val add_renv : (int * (CEGAR_syntax.t -> CEGAR_syntax.t list)) list -> CEGAR_syntax.env -> CEGAR_syntax.env

(*
val remove_preds : Syntax.typed_term -> Syntax.typed_term
(** [remove_preds t] で， [t] 中の述語を削除する *)
*)

exception PostCondition of (Fpat.Idnt.t * Fpat.Type.t) list * Fpat.Formula.t * Fpat.Formula.t

val refine_rank_fun : CEGAR_syntax.ce -> (Fpat.Idnt.t * Fpat.Pred.t list) list -> CEGAR_syntax.prog -> unit
