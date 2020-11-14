(***** Types *****)

module InnerState = Map.Make(
  struct
    type t = Syntax.id
    let compare = Id.compare
  end)

type variables_info = { update_flag : Syntax.term
		      ; set_flag : Syntax.term
		      ; prev_set_flag : Syntax.term
                      ; prev_statevars : Syntax.term list
                      ; statevars : Syntax.term list
                      ; argvars : Syntax.term list
	              }

type state = { initial_state : Syntax.term list
             ; statetable : variables_info InnerState.t }

type function_info = { id : Syntax.id
		     ; args : Syntax.id list
		     }

type coefficient_info = { coeffs : int list
			; constant : int
			}

type predicate_info = { variables : Syntax.id list
		      ; coeffsMap : (Syntax.id * int) list
		      ; prev_variables : Syntax.id list
		      ; errorPaths : Fpat.Formula.t list
		      ; errorPathsWithExparam : Fpat.Formula.t list
		      ; coefficients : coefficient_info list
		      }

let pr_ranking_function fm { variables = vs; coefficients = coefficients} =
  let show_ranking_function {coeffs = cs; constant = const} =
    let show_plus c = if c > 0 then "+" else "" in
    let fold_by acc v c =
      acc ^ (if c = 0 then ""
	else if c = 1 then "+" ^ v.Id.name
	else if c = (-1) then "-" ^ v.Id.name
	else show_plus c ^ string_of_int c ^ v.Id.name)
    in
    let s = List.fold_left2 fold_by "" vs cs in
    let s = if s.[0] = '+' then String.sub s 1 (String.length s - 1) else s in
    if const = 0 then s
    else s ^ show_plus const ^ string_of_int const
  in
  match coefficients with
    | [] -> Format.fprintf fm "0"
    | c::cs -> Format.fprintf fm "%s" (List.fold_left (fun acc c' -> acc ^ ", " ^ show_ranking_function c') (show_ranking_function c) cs)

let preprocessForTerminationVerification = ref (fun (x : Syntax.term) -> x)

type holed_program = { program : Syntax.term
		     ; verified : function_info
		     ; verified_no_checking_ver : function_info option
		     ; state : state
		     }
