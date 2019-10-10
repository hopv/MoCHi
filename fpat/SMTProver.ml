open Util
open Combinator

(** SMT provers *)

type model = (Idnt.t * Term.t) list
type t = TypEnv.t -> Formula.t -> bool
type timp = TypEnv.t -> Formula.t list -> Formula.t list -> bool
type s = TypEnv.t -> Formula.t -> model
type objective = Max of Term.t | Min of Term.t
type sm = TypEnv.t -> Formula.t -> objective -> model * Term.t
type sm_ = Formula.t -> Idnt.t -> (Idnt.t * int) list
type ls = (string * Formula.t) list -> model

let cvc3_command = ref "cvc3"
let print_z3 = ref false

(*val var_type : Type.t ref*)
let var_type = ref Type.mk_int(*@todo*)

let instantiate_type =
  Type.fold
    (object
      method fvar _ = !var_type
      method fbase = Type.mk_const
      method farrow ty1 ty2 = Type.mk_fun [ty1; ty2]
      method fforall (Pattern.V(x)) = Type.mk_forall [x]
      method fexists (Pattern.V(x)) = Type.mk_exists [x]
    end)

exception Unsat
exception Unknown
exception UnsatCore of string list
exception Unbounded of model * model

let is_valid_quick is_valid phi =
  if Formula.is_true phi then  true
  else if Formula.is_false phi then false
  else is_valid phi

let is_sat_quick is_sat phi =
  if Formula.is_true phi then true
  else if Formula.is_false phi then false
  else is_sat phi

let imply_quick imply phi1 phi2 =
  if Formula.is_false phi1 || Formula.is_true phi2 then true
  else if Formula.equiv phi1 phi2 then true
  else imply phi1 phi2

let dual_of f = Formula.bnot >> f >> not
let is_sat = dual_of >> is_sat_quick
let iff imply t1 t2 = imply t1 t2 && imply t2 t1

type smt_solver =
  < initialize : unit -> unit;
    finalize : unit -> unit;
    (** [is_valid tenv phi] checks whether [phi] is valid *)
    is_valid : t;
    is_sat : t;
    implies : timp;
    solve : s >

let uninitialized =
  object
    method initialize _ = assert false
    method finalize _ = assert false
    method is_valid _ _ = assert false
    method is_sat _ _ = assert false
    method implies _ _ _ = assert false
    method solve _ _ = assert false
  end

(* external functions *)

let z3 = ref (uninitialized : smt_solver)
let cvc3 = ref (uninitialized : smt_solver)
let default = ref (uninitialized : smt_solver)

let initialize () = !default#initialize ()
let finalize () = !default#finalize ()
let is_valid_dyn ?(tenv = []) phi = !default#is_valid tenv phi
let is_sat_dyn ?(tenv = []) phi = !default#is_sat tenv phi
(** @todo why not use is_valid_dyn instead? *)
let implies_dyn ?(tenv = []) phis1 phis2 = !default#implies tenv phis1 phis2
let implies_dyn ?(tenv = []) =
  Logger.log_block2
    "SMTPropver.implies_dyn"
    ~before:(fun phi1 phi2 ->
        Logger.printf3
          "tenv: %a@,input:@,  phi1: %a@,  phi2: %a@,"
          TypEnv.pr tenv Formula.pr_list phi1 Formula.pr_list phi2)
    ~after:(Logger.printf "output: %a" Bool.pr)
    (implies_dyn ~tenv)
let solve_dyn ?(tenv = []) phi = !default#solve tenv phi

let ext_solve_labeled = ref (fun _ -> assert false : ls)
let solve_labeled_dyn lphis = !ext_solve_labeled lphis

let ext_solve_opt = ref (fun _ -> assert false : sm)
let solve_opt ?(tenv = []) phi obj = !ext_solve_opt tenv phi obj
let ext_find_min_sat = ref (fun _ _ -> assert false : sm_)
let find_min_sat_dyn phi x = !ext_find_min_sat phi x


let init_z3 () = default := !z3
let init_cvc3 () = default := !cvc3
