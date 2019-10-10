open Util
open Combinator
open Term

(** Term expressions on unit, booleans, integers, tuples,
    uninterpreted functions, and algebraic data structures *)

(** {6 Auxiliary constructors} *)

let mk_coerce ty t = mk_app (mk_const (Const.Coerce(ty))) [t]
(*val mk_ufun : TypEnv.elem -> t list -> t*)
let mk_ufun (x, ty) ts = mk_app (mk_const (Const.UFun(ty, x))) ts

(** {6 Morphisms} *)

let rec fold f t =
  (*Logger.printf "folding %a@," Term.pr t;*)
  match fun_args t with
  | Var(x), ts -> f#fvar x (List.map (fold f) ts)
  | Const(Const.Unit), [] -> f#funit ()
  | Const(Const.True), [] -> f#ftrue ()
  | Const(Const.False), [] -> f#ffalse ()
  | Const(Const.Int(n)), [] -> f#fint n
  | Const(Const.BigInt(n)), [] -> f#fbigint n
  | Const(Const.Real(fl)), [] -> f#freal fl
  | Const(Const.String(s)), [] -> f#fstring s
  | Const(Const.Neg(ty)), [t1] -> f#fneg ty (fold f t1)
  | Const(Const.Add(ty)), [t1; t2] -> f#fadd ty (fold f t1) (fold f t2)
  | Const(Const.Sub(ty)), [t1; t2] -> f#fsub ty (fold f t1) (fold f t2)
  | Const(Const.Mul(ty)), [t1; t2] -> f#fmul ty (fold f t1) (fold f t2)
  | Const(Const.Div(ty)), [t1; t2] -> f#fdiv ty (fold f t1) (fold f t2)
  | Const(Const.Max(ty)), [t1; t2] -> f#fmax ty (fold f t1) (fold f t2)
  | Const(Const.Min(ty)), [t1; t2] -> f#fmin ty (fold f t1) (fold f t2)
  | Const(Const.Mod), [t1; t2]  -> f#fmod (fold f t1) (fold f t2)
  | Const(Const.Annot(_)), [t] -> fold f t(* @todo *)
  | Const(Const.UFun(ty, x)), ts -> f#fufun ty x (List.map (fold f) ts)
  | Const(Const.Coerce(ty)), [t] -> f#fcoerce ty (fold f t)
  | Const(_), _ -> f#fformula (t |> Formula.of_term)
  | _ ->
    invalid_arg ("not supported in CunTerm.fold: " ^
                 Printer.string_of Term.pr t)
(*let fold f t = Logger.log_block2 "CunTerm.fold" fold f t*)

let fold_op f =
  fold
    (object
      method fvar x rs = f#fvar x rs
      method funit () = f#fcon Const.Unit
      method ftrue () = f#fcon Const.True
      method ffalse () = f#fcon Const.False
      method fint n = f#fcon (Const.Int n)
      method fbigint n = f#fcon (Const.BigInt n)
      method freal r = f#fcon (Const.Real r)
      method fstring s = f#fcon (Const.String s)
      method fneg ty r = f#fuop (Const.Neg ty) r
      method fadd ty r1 r2 = f#fbop (Const.Add ty) r1 r2
      method fsub ty r1 r2 = f#fbop (Const.Sub ty) r1 r2
      method fmul ty r1 r2 = f#fbop (Const.Mul ty) r1 r2
      method fdiv ty r1 r2 = f#fbop (Const.Div ty) r1 r2
      method fmax ty r1 r2 = f#fbop (Const.Max ty) r1 r2
      method fmin ty r1 r2 = f#fbop (Const.Min ty) r1 r2
      method fmod r1 r2 = f#fbop Const.Mod r1 r2
      method fufun _ _ _ = assert false
      method fcoerce ty t = assert false
      method fformula phi = f#fformula phi
    end)

(** {6 Inspectors} *)

(*val is_fun : t -> bool*)
let is_fun = function Binder(Binder.Lambda(_), _, _) -> true | _ -> false

(*val let_fun_pat : t -> (Pattern.t * Type.t -> t -> 'a) -> 'a*)
let let_fun_pat e f =
  let_binder e (fun (Binder.Lambda(ty)) p e' -> f (p, ty) e')
(*val let_fun : t -> (TypEnv.elem -> t -> 'a) -> 'a*)
let let_fun e f =
  let_fun_pat e
    (fun t e' ->
       match t with
       | (Pattern.V(x), ty) -> f (x, ty) e'
       | (Pattern.W, ty) -> f (Idnt.new_var (),ty) e'
       | _ -> assert false)

let size =
  fold
    (object
      method fvar x ns = Integer.sum_list ns + 1
      method funit () = 1
      method ftrue () = 1
      method ffalse () = 1
      method fint _ = 1
      method fbigint _ = 1
      method freal _ = 1
      method fstring _ = 1
      method fneg _ n = n + 1
      method fadd _ n1 n2 = n1 + n2 + 1
      method fsub _ n1 n2 = n1 + n2 + 1
      method fmul _ n1 n2 = n1 + n2 + 1
      method fdiv _ n1 n2 = n1 + n2 + 1
      method fmax _ n1 n2 = n1 + n2 + 1
      method fmin _ n1 n2 = n1 + n2 + 1
      method fmod n1 n2 = n1 + n2 + 1
      method fufun _ _ ns = Integer.sum_list ns + 1
      method fcoerce ty t = assert false
      method fformula phi = assert false
    end)

let rec sexp_of_atom atom =
  let fold f atm =
    (*Logger.printf "folding %a@," Atom.pr atm;*)
    match atm |> Atom.term_of |> Term.fun_args with
    | Term.Var(x), ts -> f#fvar x ts
    | Term.Const(Const.Eq(ty)), [t1; t2] -> f#feq ty t1 t2
    | Term.Const(Const.Neq(ty)), [t1; t2] -> f#fneq ty t1 t2
    | Term.Const(Const.Lt(ty)), [t1; t2] -> f#flt ty t1 t2
    | Term.Const(Const.Gt(ty)), [t1; t2] -> f#fgt ty t1 t2
    | Term.Const(Const.Leq(ty)), [t1; t2] -> f#fleq ty t1 t2
    | Term.Const(Const.Geq(ty)), [t1; t2] -> f#fgeq ty t1 t2
    | Term.Const(Const.Divides(n)), [t] -> f#fdivides n t
    | Term.Const(c), ts -> f#fterm c ts
    | _ ->
      Logger.debug_assert_false ~on_failure:(fun () ->
          Format.printf "not supported (in CunAtom.fold): %a@," Atom.pr atm)
                                ()
  in
  fold
    (object
      method fvar x ts =
        if ts = [] then Idnt.string_of x
        else
          "(" ^
          Idnt.string_of x ^ " " ^
          String.concat " " (List.map sexp_of ts) ^
          ")"
      method feq ty t1 t2 =
        "(= " ^ sexp_of t1 ^ " " ^ sexp_of t2 ^ ")"
      method fneq ty t1 t2 =
        "(or " ^
        "(< " ^ sexp_of t1 ^ " " ^ sexp_of t2 ^ ") " ^
        "(> " ^ sexp_of t1 ^ " " ^ sexp_of t2 ^ "))"
      method flt ty t1 t2 =
        "(< " ^ sexp_of t1 ^ " " ^ sexp_of t2 ^ ")"
      method fgt ty t1 t2 =
        "(> " ^ sexp_of t1 ^ " " ^ sexp_of t2 ^ ")"
      method fleq ty t1 t2 =
        "(<= " ^ sexp_of t1 ^ " " ^ sexp_of t2 ^ ")"
      method fgeq ty t1 t2 =
        "(>= " ^ sexp_of t1 ^ " " ^ sexp_of t2 ^ ")"
      method fdivides n t = assert false
      method frecognizer ty x t = assert false
      method fsmem ty t1 t2 = assert false
      method fssubset ty t1 t2 = assert false
      method fterm c ts = assert false
    end) atom

and sexp_of_formula ?(smt2=false) =
  let imply = if smt2 then "=> " else "implies " in
  Formula.fold
    (object
      method fatom = sexp_of_atom
      method ftrue () = "true"
      method ffalse () = "false"
      method fnot s = "(not " ^ s ^ ")"
      method fand s1 s2 = "(and " ^ s1 ^ " " ^ s2 ^ ")"
      method for_ s1 s2 = "(or " ^ s1 ^ " " ^ s2 ^ ")"
      method fimply s1 s2 = "(" ^ imply ^ s1 ^ " " ^ s2 ^ ")"
      method fiff s1 s2 = "(iff " ^ s1 ^ " " ^ s2 ^ ")"
      method fforall (x, ty) s = assert false
      method fexists (x, ty) s = assert false
    end)

and sexp_of t =
  fold
    (object
      method fvar x [] = Idnt.string_of x
      method funit () = "0" (* TODO: fix *)
      method ftrue () = "true"
      method ffalse () = "false"
      method fint n =
        if n >= 0 then
          string_of_int n
        else
          "(- " ^ string_of_int (-n) ^ ")"
      method fbigint n = Big_int_Z.string_of_big_int n
      method freal n = string_of_float n
      method fstring _ = assert false
      method fneg _ s = "(- " ^ s ^ ")"
      method fadd _ s1 s2 = "(+ " ^ s1 ^ " " ^ s2 ^ ")"
      method fsub _ s1 s2 = "(- " ^ s1 ^ " " ^ s2 ^ ")"
      method fmul _ s1 s2 = "(* " ^ s1 ^ " " ^ s2 ^ ")"
      method fdiv _ s1 s2 = "(div " ^ s1 ^ " " ^ s2 ^ ")" (* TODO: fix *)
      method fmax _ s1 s2 = assert false
      method fmin _ s1 s2 = assert false
      method fmod s1 s2 = assert false
      method fufun _ _ _ = assert false
      method fcoerce ty t = assert false
      method fformula phi = sexp_of_formula phi
    end) t


(** {6 Auxiliary destructors} *)

let to_lin_int_exp =
  fold
    (object
      method fvar x = function
        | [] -> [1, x], 0
        | _ -> invalid_arg "CunTerm.to_lin_int_exp"
      method funit () = invalid_arg "CunTerm.to_lin_int_exp"
      method ftrue () = invalid_arg "CunTerm.to_lin_int_exp"
      method ffalse () = invalid_arg "CunTerm.to_lin_int_exp"
      method fint n = [], n
      method fbigint n =
        try [], Big_int_Z.int_of_big_int n
        with Failure("int_of_big_int") -> invalid_arg "CunTerm.to_lin_int_exp"
      method freal _ = invalid_arg "CunTerm.to_lin_int_exp"
      method fstring _ = invalid_arg "CunTerm.to_lin_int_exp"
      method fneg ty r =
        if Type.is_int ty then LinIntExp.neg r
        else invalid_arg "CunTerm.to_lin_int_exp"
      method fadd ty r1 r2 =
        if Type.is_int ty then LinIntExp.add r1 r2
        else invalid_arg "CunTerm.to_lin_int_exp"
      method fsub ty r1 r2 =
        if Type.is_int ty then LinIntExp.add r1 (LinIntExp.neg r2)
        else invalid_arg "CunTerm.to_lin_int_exp"
      method fmul ty r1 r2 =
        if Type.is_int ty then LinIntExp.mul r1 r2
        else invalid_arg "CunTerm.to_lin_int_exp"
      method fdiv ty r1 r2 = invalid_arg "CunTerm.to_lin_int_exp"
      method fmax ty r1 r2 = invalid_arg "CunTerm.to_lin_int_exp"
      method fmin ty r1 r2 = invalid_arg "CunTerm.to_lin_int_exp"
      method fmod r1 r2 = invalid_arg "CunTerm.to_lin_int_exp"
      method fufun _ _ _ = invalid_arg "CunTerm.to_lin_int_exp"
      method fcoerce ty t = invalid_arg "CunTerm.to_lin_int_exp"
      method fformula phi = invalid_arg "CunTerm.to_lin_int_exp"
    end)

let to_lin_real_exp =
  fold
    (object
      method fvar x = function
        | [] -> [1.0, x], 0.0
        | _ -> invalid_arg "CunTerm.to_lin_real_exp"
      method funit () = invalid_arg "CunTerm.to_lin_real_exp"
      method ftrue () = invalid_arg "CunTerm.to_lin_real_exp"
      method ffalse () = invalid_arg "CunTerm.to_lin_real_exp"
      method fint n = [], float_of_int n
      method fbigint n = [], Big_int_Z.float_of_big_int n
      method freal f = [], f
      method fstring _ = invalid_arg "CunTerm.to_lin_real_exp"
      method fneg ty r =
        if Type.is_real ty then LinRealExp.neg r
        else invalid_arg "CunTerm.to_lin_real_exp"
      method fadd ty r1 r2 =
        if Type.is_real ty then LinRealExp.add r1 r2
        else invalid_arg "CunTerm.to_lin_real_exp"
      method fsub ty r1 r2 =
        if Type.is_real ty then LinRealExp.add r1 (LinRealExp.neg r2)
        else invalid_arg "CunTerm.to_lin_real_exp"
      method fmul ty r1 r2 =
        if Type.is_real ty then LinRealExp.mul r1 r2
        else invalid_arg "CunTerm.to_lin_real_exp"
      method fdiv ty r1 r2 = invalid_arg "CunTerm.to_lin_real_exp"
      method fmax ty r1 r2 = invalid_arg "CunTerm.to_lin_real_exp"
      method fmin ty r1 r2 = invalid_arg "CunTerm.to_lin_real_exp"
      method fmod r1 r2 = invalid_arg "CunTerm.to_lin_real_exp"
      method fufun _ _ _ = invalid_arg "CunTerm.to_lin_real_exp"
      method fcoerce ty t = invalid_arg "CunTerm.to_lin_real_exp"
      method fformula phi = invalid_arg "CunTerm.to_lin_real_exp"
    end)

let to_poly_int_exp =
  fold
    (object
      method fvar x = function
        | [] -> [1, [x]]
        | _ -> invalid_arg "CunTerm.to_poly_int_exp"
      method funit () = invalid_arg "CunTerm.to_poly_int_exp"
      method ftrue () = invalid_arg "CunTerm.to_poly_int_exp"
      method ffalse () = invalid_arg "CunTerm.to_poly_int_exp"
      method fint n = if n = 0 then [] else [n, []]
      method fbigint n =
        try
          let n = Big_int_Z.int_of_big_int n in
          if n = 0 then [] else [n, []]
        with Failure("int_of_big_int") ->
          invalid_arg "CunTerm.to_poly_int_exp"
      method freal _ = invalid_arg "CunTerm.to_poly_int_exp"
      method fstring _ = invalid_arg "CunTerm.to_poly_int_exp"
      method fneg ty r =
        if Type.is_int ty then PolyIntExp.neg r
        else invalid_arg "CunTerm.to_poly_int_exp"
      method fadd ty r1 r2 =
        if Type.is_int ty then PolyIntExp.add r1 r2
        else invalid_arg "CunTerm.to_poly_int_exp"
      method fsub ty r1 r2 =
        if Type.is_int ty then PolyIntExp.add r1 (PolyIntExp.neg r2)
        else invalid_arg "CunTerm.to_poly_int_exp"
      method fmul ty r1 r2 =
        if Type.is_int ty then PolyIntExp.mul r1 r2
        else invalid_arg "CunTerm.to_poly_int_exp"
      method fdiv ty r1 r2 = invalid_arg "CunTerm.to_poly_int_exp"
      method fmax ty r1 r2 = invalid_arg "CunTerm.to_poly_int_exp"
      method fmin ty r1 r2 = invalid_arg "CunTerm.to_poly_int_exp"
      method fmod r1 r2 = invalid_arg "CunTerm.to_poly_int_exp"
      method fufun _ _ _ = invalid_arg "CunTerm.to_poly_int_exp"
      method fcoerce ty t = invalid_arg "CunTerm.to_poly_int_exp"
      method fformula phi = invalid_arg "CunTerm.to_poly_int_exp"
    end)

let to_poly_real_exp =
  fold
    (object
      method fvar x = function
        | [] -> [1., [x]]
        | _ -> invalid_arg "CunTerm.to_poly_real_exp"
      method funit () = invalid_arg "CunTerm.to_poly_real_exp"
      method ftrue () = invalid_arg "CunTerm.to_poly_real_exp"
      method ffalse () = invalid_arg "CunTerm.to_poly_real_exp"
      method fint n = if n = 0 then [] else [float_of_int n, []]
      method fbigint n =
        try
          let n = Big_int_Z.int_of_big_int n in
          if n = 0 then [] else [float_of_int n, []]
        with Failure("int_of_big_int") ->
          invalid_arg "CunTerm.to_poly_real_exp"
      method freal f = if f = 0. then [] else [f, []]
      method fstring _ = invalid_arg "CunTerm.to_poly_real_exp"
      method fneg ty r =
        if Type.is_real ty then PolyRealExp.neg r
        else invalid_arg "CunTerm.to_poly_real_exp"
      method fadd ty r1 r2 =
        if Type.is_real ty then PolyRealExp.add r1 r2
        else invalid_arg "CunTerm.to_poly_real_exp"
      method fsub ty r1 r2 =
        if Type.is_real ty then PolyRealExp.add r1 (PolyRealExp.neg r2)
        else invalid_arg "CunTerm.to_poly_real_exp"
      method fmul ty r1 r2 =
        if Type.is_real ty then PolyRealExp.mul r1 r2
        else invalid_arg "CunTerm.to_poly_real_exp"
      method fdiv ty r1 r2 = invalid_arg "CunTerm.to_poly_real_exp"
      method fmax ty r1 r2 = invalid_arg "CunTerm.to_poly_real_exp"
      method fmin ty r1 r2 = invalid_arg "CunTerm.to_poly_real_exp"
      method fmod r1 r2 = invalid_arg "CunTerm.to_poly_real_exp"
      method fufun _ _ _ = invalid_arg "CunTerm.to_poly_real_exp"
      method fcoerce ty t = invalid_arg "CunTerm.to_poly_real_exp"
      method fformula phi = invalid_arg "CunTerm.to_poly_real_exp"
    end)

let lin_poly_exp_of _ = raise (Global.NotImplemented "CunTerm.lin_poly_exp_of")

(** {6 Inspectors} *)

let is_linear t =
  try ignore (to_lin_int_exp t); true with Invalid_argument _ -> false

(** [nlfvs t] returns the set of free variables in [t]
    that may occur in a non-linear integer expression
    @todo should we expand integer expressions first? *)
let rec nlfvs t =
  visit_wo_app
    (object
      method fvar _ ts = List.concat_map nlfvs ts
      method fcon c ts =
        let t = mk_app (mk_const c) ts in
        match c, ts with
        | Const.Mul(ty), [_; _] when Type.is_int ty ->
          begin
            try
              ignore (to_lin_int_exp t);
              []
            with Invalid_argument _ ->
              fvs t
          end
        | Const.Div(ty), [t1; t2] when Type.is_int ty ->
          Term.fvs t1 @ Term.fvs t2
        | Const.Mod, [t1; t2] -> Term.fvs t1 @ Term.fvs t2
        | _, _ -> List.concat_map nlfvs ts
      method fbin _ p t1 [] = Set_.diff (nlfvs t1) (Pattern.fvs p)
    end)
    t

(** {6 Operators} *)

let simplify_int_term t =
  try IntTerm.of_lin_exp (to_lin_int_exp t) with Invalid_argument _ -> t
let simplify_real_term t =
  try RealTerm.of_lin_exp (to_lin_real_exp t) with Invalid_argument _ -> t

let rec simplify t =
  visit_wo_app
    (object
      method fvar x ts = mk_app (mk_var x) ts
      method fcon c ts =
        let t =
          if Const.is_ibop c then begin
            try
              Logger.printf "binop [%a]@," Term.pr_list ts;
              let [n1; n2] = List.map IntTerm.int_of ts in
              Const.lift_ibop c n1 n2 |> IntTerm.make
            with Not_found -> mk_app (mk_const c) ts
          end else if Const.is_rbop c then begin
            try
              Logger.printf "binop [%a]@," Term.pr_list ts;
              let [f1; f2] = List.map RealTerm.float_of ts in
              Const.lift_rbop c f1 f2 |> RealTerm.make
            with Not_found -> mk_app (mk_const c) ts
          end else mk_app (mk_const c) ts
        in
        if Const.ret_int c then simplify_int_term t
        else if Const.ret_real c then simplify_real_term t
        else mk_app (mk_const c) (List.map simplify ts)
      method fbin _ _ _ _ =
        Format.printf "not supported (in CunTerm.simplify): %a@," pr t;
        raise (Global.NotImplemented "CunTerm.simplify")
    end)
    t

let rec poly_simplify t =
  visit_wo_app
    (object
      method fvar x [] = mk_var x
      method fcon c ts =
        let t = mk_app (mk_const c) ts in
        if Const.ret_int c then
          try IntTerm.of_poly_exp (to_poly_int_exp t)
          with Invalid_argument _ -> t
        else mk_app (mk_const c) (List.map poly_simplify ts)
      method fbin _ _ _ _ =
        Format.printf "not supported (in CunTerm.poly_simplify): %a@," pr t;
        raise (Global.NotImplemented "CunTerm.poly_simplify")
    end)
    t

let ufuns_of f_formula =
  fold
    (object
      method fvar _ rs = List.concat rs
      method funit () = []
      method ftrue () = []
      method ffalse () = []
      method fint _ = []
      method fbigint _ = []
      method freal _ = []
      method fstring _ = []
      method fneg _ r1 = r1
      method fadd _ r1 r2 = r1 @ r2
      method fsub _ r1 r2 = r1 @ r2
      method fmul _ r1 r2 = r1 @ r2
      method fdiv _ r1 r2 = r1 @ r2
      method fmax _ r1 r2 = r1 @ r2
      method fmin _ r1 r2 = r1 @ r2
      method fmod r1 r2 = r1 @ r2
      method fufun _ x rs = x :: List.concat rs
      method fcoerce _ r = r
      method fformula phi = f_formula phi
    end)

let int_to_real =
  fold
    (object
      method fvar x ts = Term.mk_app (Term.mk_var x) ts
      method funit () = UnitTerm.make
      method ftrue () = BoolTerm.mk_true
      method ffalse () = BoolTerm.mk_false
      method fint n = RealTerm.make (float_of_int n)
      method fbigint n = RealTerm.make (Big_int_Z.float_of_big_int n)
      method freal = RealTerm.make
      method fstring = StringTerm.make
      method fneg ty = NumTerm.neg (Type.int_to_real ty)
      method fadd ty = NumTerm.add (Type.int_to_real ty)
      method fsub ty = NumTerm.sub (Type.int_to_real ty)
      method fmul ty = NumTerm.mul (Type.int_to_real ty)
      method fdiv ty = NumTerm.div (Type.int_to_real ty)
      method fmax ty = NumTerm.max (Type.int_to_real ty)
      method fmin ty = NumTerm.min (Type.int_to_real ty)
      method fmod = IntTerm.mk_mod
      method fufun ty x = mk_ufun (x, ty)
      method fcoerce = mk_coerce
      method fformula = assert false
    end)

let real_to_int =
  fold
    (object
      method fvar x ts = Term.mk_app (Term.mk_var x) ts
      method funit () = UnitTerm.make
      method ftrue () = BoolTerm.mk_true
      method ffalse () = BoolTerm.mk_false
      method fint = IntTerm.make
      method fbigint = IntTerm.of_big_int
      method freal f = IntTerm.make (Float.round f(*@todo*))
      method fstring = StringTerm.make
      method fneg ty = NumTerm.neg (Type.real_to_int ty)
      method fadd ty = NumTerm.add (Type.real_to_int ty)
      method fsub ty = NumTerm.sub (Type.real_to_int ty)
      method fmul ty = NumTerm.mul (Type.real_to_int ty)
      method fdiv ty = NumTerm.div (Type.real_to_int ty)
      method fmax ty = NumTerm.max (Type.real_to_int ty)
      method fmin ty = NumTerm.min (Type.real_to_int ty)
      method fmod = IntTerm.mk_mod
      method fufun ty x = mk_ufun (x, ty)
      method fcoerce = mk_coerce
      method fformula = assert false
    end)



(*

val fold :
  < fvar : Idnt.t -> 'a list -> 'a;
    fint : int -> 'a;
    fneg : 'a -> 'a;
    fadd : 'a -> 'a -> 'a;
    fsub : 'a -> 'a -> 'a;
    fmul : 'a -> 'a -> 'a;
    fdiv : 'a -> 'a -> 'a;
    fmax : 'a -> 'a -> 'a;
    fmin : 'a -> 'a -> 'a;
    fmod : 'a -> 'a -> 'a; .. > ->
  t -> 'a

(** {6 Auxiliary destructors} *)

val to_lin_int_exp : t -> LinIntExp.t
val poly_exp_of : t -> PolyIntExp.t
val lin_poly_exp_of : t -> LinPolyIntExp.t

(** {6 Inspectors} *)

val is_linear : t -> bool
val nlfvs : t -> Idnt.t list

(** {6 Operators} *)

val simplify : t -> t
val poly_simplify : t -> t
 *)


let has_ufun =
  fold
    (object
      method fvar _ rs = rs <> [] || List.exists id rs
      method funit () = false
      method ftrue () = false
      method ffalse () = false
      method fint _ = false
      method fbigint _ = false
      method freal _ = false
      method fstring _ = false
      method fneg _ r1 = r1
      method fadd _ r1 r2 = r1 || r2
      method fsub _ r1 r2 = r1 || r2
      method fmul _ r1 r2 = r1 || r2
      method fdiv _ r1 r2 = r1 || r2
      method fmax _ r1 r2 = r1 || r2
      method fmin _ r1 r2 = r1 || r2
      method fmod r1 r2 = r1 || r2
      method fufun _ _ rs = List.exists id rs
      method fcoerce _ r1 = r1
      method fformula _ = assert false
    end)
