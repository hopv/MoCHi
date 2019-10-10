(** A recursion-free HCCS solver based on top-down iterative
    interpolation (see [Unno et al. PPDP'09] for detals) *)

(** {6 Options} *)

val solve_body_left_to_right : bool ref

(** @require [is_non_recursive hcs && is_well_defined hcs]
    @ensure [Map.is_map ret && Set.equiv (Map.dom ret) (pvs hcs)] *)
val solve : HCCSSolver.t
