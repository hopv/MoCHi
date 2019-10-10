(** Interface to ATP *)

(** {6 Functions for formulas} *)

(** [real_qelim phi] eliminates quantifiers over real variables in [phi] *)
val real_qelim : Formula.t -> Formula.t

(** [integer_qelim phi] eliminates quantifiers over integer variables in [phi]
    @raise NotImplemented if [phi] is non-linear *)
val integer_qelim : Formula.t -> Formula.t
