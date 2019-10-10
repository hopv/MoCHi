(** CPS-transformation for CEGAR-lang. *)

val trans : CEGAR_syntax.prog -> bool -> CEGAR_syntax.prog
(** [trans b t] で [t] をCPS変換する．
    変換元の評価戦略は call-by-value．
    [t] に単純型が付かない場合は例外 Typing.CannotUnify が投げられる．
*)


