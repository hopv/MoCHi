open Util
open Combinator

include Term

(** {6 Auxiliary destructors} *)

let term_of phi = phi
let atom_of phi = phi |> Atom.of_term

let is_true = function Const(Const.True) -> true | _ -> false
let is_false = function Const(Const.False) -> true | _ -> false
let is_and = fun_args >> function Const(Const.And), [_; _] -> true | _ -> false
let is_or = fun_args >> function Const(Const.Or), [_; _] -> true | _ -> false
let is_pva pvs = atom_of >> Atom.is_pva pvs
let is_eq = atom_of >> Atom.is_eq
let is_neq = atom_of >> Atom.is_neq
let is_binder = function Binder(_,_,_) -> true | _ -> false
let is_forall = fun_args >> function
  | Binder(Binder.Forall(_), Pattern.V(_), _), [] -> true
  | _ -> false
let is_exists = fun_args >> function
  | Binder(Binder.Exists(_), Pattern.V(_), _), [] -> true
  | _ -> false
let is_mu = fun_args >> function
  | Binder(Binder.Mu, Pattern.V(_), _), [] -> true
  | _ -> false
let is_nu = fun_args >> function
  | Binder(Binder.Nu, Pattern.V(_), _), [] -> true
  | _ -> false
let is_box = fun_args >> function
  | Const(Const.Box(_)), [_] -> true | _ -> false
let is_diamond = fun_args >> function
  | Const(Const.Diamond(_)), [_] -> true | _ -> false
let contain_binder = fun_args >> function
  | Const(_), ts -> List.exists is_binder ts
  | Binder(_,_,_), _ -> true
  | _, _ -> false

let let_not phi k =
  match fun_args phi with
  | Const(Const.Not), [phi] -> k phi
  | _ ->
    Logger.debug_assert_false
      ~on_failure:(fun () -> Format.printf "error in let_not: %a@," pr phi)
      ()
let let_and phi k =
  match fun_args phi with
  | Const(Const.And), [phi1; phi2] -> k phi1 phi2
  | _ ->
    Logger.debug_assert_false
      ~on_failure:(fun () -> Format.printf "error in let_and: %a@," pr phi)
      ()
let let_or phi k =
  match fun_args phi with
  | Const(Const.Or), [phi1; phi2] -> k phi1 phi2
  | _ ->
    Logger.debug_assert_false
      ~on_failure:(fun () -> Format.printf "error in let_or: %a@," pr phi)
      ()
let let_imply phi k =
  match fun_args phi with
  | Const(Const.Imply), [phi1; phi2] -> k phi1 phi2
  | _ ->
    Logger.debug_assert_false
      ~on_failure:(fun () -> Format.printf "error in let_imply: %a@," pr phi)
      ()
let let_iff phi k =
  match fun_args phi with
  | Const(Const.Iff), [phi1; phi2] -> k phi1 phi2
  | _ ->
    Logger.debug_assert_false
      ~on_failure:(fun () -> Format.printf "error in let_iff: %a@," pr phi)
      ()
let let_forall phi k =
  match fun_args phi with
  | Binder(Binder.Forall(ty), Pattern.V(x), phi), [] -> k x ty phi
  | _ ->
    Logger.debug_assert_false
      ~on_failure:(fun () -> Format.printf "error in let_forall: %a@," pr phi)
      ()
let let_exists phi k =
  match fun_args phi with
  | Binder(Binder.Exists(ty), Pattern.V(x), phi), [] -> k x ty phi
  | _ ->
    raise (Global.NoMatch "Formula.let_exists")
let let_mu phi k =
  match fun_args phi with
  | Binder(Binder.Mu, Pattern.V(x), phi'), [] -> k x phi'
  | _ -> assert false
let let_nu phi k =
  match fun_args phi with
  | Binder(Binder.Nu, Pattern.V(x), phi'), [] -> k x phi'
  | _ -> assert false
let let_pva phi k =
  Term.let_fun_args (term_of phi) (fun t ts ->
      if ts = []
      then raise (Global.NoMatch "Formula.let_pva")
      else
        Term.let_var t (fun p ->
            k p (List.map (fun t ->
                try TypTerm.annot_term_of t
                with Global.NoMatch _(* uninterpreted predicate symbol *) ->
                  raise (Global.NoMatch "Formula.let_pva")) ts)))

(** {6 Auxiliary constructors} *)

let mk_atom c ts = Term.mk_app (Term.mk_const c) ts
let of_term = id
let of_atom = Atom.term_of

let mk_true = Atom.mk_true |> of_atom
let mk_false = Atom.mk_false |> of_atom
let mk_var x ts = Atom.mk_var x ts |> of_atom
let mk_brel c t1 t2 = Atom.mk_brel c t1 t2 |> of_atom

let eq ty t1 t2 = Atom.eq ty t1 t2 |> of_atom
let neq ty t1 t2 = Atom.neq ty t1 t2 |> of_atom
let eq_tt tt1 tt2 = Atom.eq_tt tt1 tt2 |> of_atom

let rec band phis =
  match phis with
  | [] -> mk_true
  | [phi] -> phi
  | phi :: phis' when is_true phi -> band phis'
  | phi :: _ when is_false phi -> raise Not_found
  | phi :: phis' ->
    let phi' = band phis' in
    if is_true phi' then phi
    else if is_false phi' then raise Not_found
    else mk_app (mk_const Const.And) [phi; phi']
let band phis = try phis |> List.unique |> band with Not_found -> mk_false

let mk_and phi1 phi2 = band [phi1; phi2]

let rec bor phis =
  match phis with
  | [] -> mk_false
  | [phi] -> phi
  | phi :: _ when is_true phi -> raise Not_found
  | phi :: phis' when is_false phi -> bor phis'
  | phi :: phis' ->
    let phi' = bor phis' in
    if is_true phi' then raise Not_found
    else if is_false phi' then phi
    else mk_app (mk_const Const.Or) [phi; phi']
let bor phis = try phis |> List.unique |> bor with Not_found -> mk_true

let mk_or phi1 phi2 = bor [phi1; phi2]

let bnot phi =
  match fun_args phi with
  | phi, [] when is_true phi -> mk_false
  | phi, [] when is_false phi -> mk_true
  | Const(Const.Not), [phi] -> phi
  | _ -> mk_app (mk_const Const.Not) [phi]

let imply phi1 phi2 =
  if is_true phi1 then phi2
  else if is_false phi1 then mk_true
  else if is_true phi2 then mk_true
  else if is_false phi2 then bnot phi1
  else mk_app (mk_const Const.Imply) [phi1; phi2]

let forall tenv phi =
  let tenv = Map_.restrict tenv (fvs phi) in
  if tenv = [] then
    phi
  else
    List.fold_right
      (fun (x, ty) phi -> mk_binder (Binder.Forall ty) (Pattern.V x) phi)
      tenv phi
let forall = Logger.log_block2 "Formula.forall" forall

let exists tenv phi =
  let tenv = Map_.restrict tenv (fvs phi) in
  if tenv = [] then
    phi
  else
    List.fold_right
      (fun (x, ty) phi -> mk_binder (Binder.Exists ty) (Pattern.V x) phi)
      tenv phi
(*bnot (forall tenv (bnot phi))*)
let exists =
  Logger.log_block2 "Formula.exists"
    ~before:(fun tenv phi ->
        Logger.printf2 "tenv: %a@,input: %a@," TypEnv.pr tenv pr phi)
    ~after:(Logger.printf "output: %a" pr)
    exists

let box index phi = mk_app (mk_const (Const.Box(index))) [phi]
let diamond index phi = mk_app (mk_const (Const.Diamond(index))) [phi]
let mu x phi = mk_binder Binder.Mu (Pattern.V x) phi
let nu x phi = mk_binder Binder.Nu (Pattern.V x) phi

let mk_iff phi1 phi2 =
  if equiv phi1 phi2 then
    mk_true
  else
    (*band [imply phi1 phi2; imply phi2 phi1]*)
    mk_app (mk_const Const.Iff) [phi1; phi2]
let mk_iff_disj phi1 phi2 =
  bor [band [phi1; phi2]; band [bnot phi1; bnot phi2]]
let mk_iff_conj phi1 phi2 =
  band [bor [bnot phi1; phi2]; bor [bnot phi2; phi1]]
let mk_not_iff_disj phi1 phi2 =
  bor [band [phi1; bnot phi2]; band [phi2; bnot phi1]]
let mk_not_iff_conj t1 t2 =
  band [bor [t1; t2]; bor [bnot t1; bnot t2]]

(** {6 Morphisms} *)

let rec para f phi =
  match fun_args phi with
  | Const(Const.True), [] ->
    f#ftrue ()
  | Const(Const.False), [] ->
    f#ffalse ()
  | Const(Const.Not), [phi1] ->
    f#fnot phi1 (para f phi1)
  | Const(Const.And), [phi1; phi2] ->
    f#fand phi1 (para f phi1) phi2 (para f phi2)
  | Const(Const.Or), [phi1; phi2] ->
    f#for_ phi1 (para f phi1) phi2 (para f phi2)
  | Const(Const.Imply), [phi1; phi2] ->
    f#fimply phi1 (para f phi1) phi2 (para f phi2)
  | Const(Const.Iff), [phi1; phi2] ->
    f#fiff phi1 (para f phi1) phi2 (para f phi2)
  | Binder(Binder.Forall(ty), Pattern.V(x), phi1), [] ->
    f#fforall (x, ty) phi1 (para f phi1)
  | Binder(Binder.Exists(ty), Pattern.V(x), phi1), [] ->
    f#fexists (x, ty) phi1 (para f phi1)

  | Var(_), _ | Const(_), _ ->
    phi |> Atom.of_term |> f#fatom
  | _ ->
    Logger.debug_assert_false
      ~on_failure:(fun () ->
          Format.printf
            "error in Formula.para: %a is not a well-formed formula@,"
            Term.pr phi)
      ()

let lazy_para f phi =
  Lazy.force
    (para
       (object
         method fatom atm =
           lazy (f#fatom atm)
         method ftrue () =
           lazy (f#ftrue ())
         method ffalse () =
           lazy (f#ffalse ())
         method fnot phi1 r1 =
           lazy (f#fnot phi1 r1)
         method fand phi1 r1 phi2 r2 =
           lazy (f#fand phi1 r1 phi2 r2)
         method for_ phi1 r1 phi2 r2 =
           lazy (f#for_ phi1 r1 phi2 r2)
         method fimply phi1 r1 phi2 r2 =
           lazy (f#fimply phi1 r1 phi2 r2)
         method fiff phi1 r1 phi2 r2 =
           lazy (f#fiff phi1 r1 phi2 r2)
         method fforall xty phi1 r1 =
           lazy (f#fforall xty phi1 r1)
         method fexists xty phi1 r1 =
           lazy (f#fexists xty phi1 r1)
       end)
       phi)

let fold f =
  para
    (object
      method fatom = f#fatom
      method ftrue = f#ftrue
      method ffalse = f#ffalse
      method fnot _ = f#fnot
      method fand _ r1 _ r2 = f#fand r1 r2
      method for_ _ r1 _ r2 = f#for_ r1 r2
      method fimply _ r1 _ r2 = f#fimply r1 r2
      method fiff _ r1 _ r2 = f#fiff r1 r2
      method fforall xty _ = f#fforall xty
      method fexists xty _ = f#fexists xty
    end)

let fold_pos f phi =
  fold
    (object
      method fatom atm = fun pos -> f#fatom pos atm
      method ftrue () = fun pos -> f#ftrue ()
      method ffalse () = fun pos -> f#ffalse ()
      method fnot r1 = fun pos -> f#fnot (r1 (not pos))
      method fand r1 r2 = fun pos -> f#fand (r1 pos) (r2 pos)
      method for_ r1 r2 = fun pos -> f#for_ (r1 pos) (r2 pos)
      method fimply r1 r2 = fun pos -> f#fimply (r1 pos) (r2 pos)
      method fiff r1 r2 = fun pos -> f#fiff (r1 pos) (r2 pos)
      method fforall xty r1 = fun pos -> f#fforall xty (r1 pos)
      method fexists xty r1 = fun pos -> f#fexists xty (r1 pos)
    end)
    phi
    true

let visit f =
  lazy_para
    (object
      method fatom = f#fatom
      method ftrue = f#ftrue
      method ffalse = f#ffalse
      method fnot phi1 _ = f#fnot phi1
      method fand phi1 _ phi2 _ = f#fand phi1 phi2
      method for_ phi1 _ phi2 _ = f#for_ phi1 phi2
      method fimply phi1 _ phi2 _ = f#fimply phi1 phi2
      method fiff phi1 _ phi2 _ = f#fiff phi1 phi2
      method fforall xty phi1 _ = f#fforall xty phi1
      method fexists xty phi1 _ = f#fexists xty phi1
    end)

let map_atom f =
  fold
    (object
      method fatom atm = f atm
      method ftrue () = mk_true
      method ffalse () = mk_false
      method fnot phi = bnot phi
      method fand phi1 phi2 = band [phi1; phi2]
      method for_ phi1 phi2 = bor [phi1; phi2]
      method fimply phi1 phi2 = imply phi1 phi2
      method fiff phi1 phi2 = mk_iff phi1 phi2
      method fforall xty phi1 = forall [xty] phi1
      method fexists xty phi1 = exists [xty] phi1
    end)

let fold_band f =
  fold
    (object
      method fatom atm = f atm
      method ftrue _ = true
      method ffalse _ = true
      method fnot b1 = b1
      method fand b1 b2 = b1 && b2
      method for_  b1 b2 = b1 && b2
      method fimply b1 b2 = b1 && b2
      method fiff b1 b2 = b1 && b2
      method fforall _ b1 = b1
      method fexists _ b1 = b1
    end)

let fold_bor f =
  fold
    (object
      method fatom atm = f atm
      method ftrue _ = false
      method ffalse _ = false
      method fnot b1 = b1
      method fand b1 b2 = b1 || b2
      method for_  b1 b2 = b1 || b2
      method fimply b1 b2 = b1 || b2
      method fiff b1 b2 = b1 || b2
      method fforall _ b1 = b1
      method fexists _ b1 = b1
    end)

let fold_set f =
  fold
    (object
      method fatom atm = f atm
      method ftrue () = []
      method ffalse () =  []
      method fnot r1 =  r1
      method fand r1 r2 = r1 @ r2
      method for_ r1 r2 = r1 @ r2
      method fimply r1 r2 = r1 @ r2
      method fiff r1 r2 = r1 @ r2
      method fforall _ r1 = r1
      method fexists _ r1 = r1
    end)

(** {6 Printers} *)

let pr_tex ppf phi =
  Format.fprintf ppf "@[<hv>";
  fold
    (object
       method fatom atm = fun ppf l ->
         Atom.pr_tex ppf atm
       method ftrue _ = fun ppf l ->
         Format.fprintf ppf "\\top"
       method ffalse _ = fun ppf l ->
         Format.fprintf ppf "\\bot"
       method fnot r1 = fun ppf l ->
         Format.fprintf ppf "\\neg %a" r1 0
       method fand r1 r2 = fun ppf l ->
         if l < 1 then Format.fprintf ppf "@[\\left(@[<hv>";
         Format.fprintf ppf "%a \\land @ %a" r1 1 r2 1;
         if l < 1 then Format.fprintf ppf "@]\\right)@]"
       method for_ r1 r2 = fun ppf l ->
         if l < 2 then Format.fprintf ppf "@[\\left(@[<hv>";
         Format.fprintf ppf "%a \\lor @ %a" r1 2 r2 2;
         if l < 2 then Format.fprintf ppf "@]\\right)@]"
       method fimply r1 r2 = fun ppf l ->
         if l < 3 then Format.fprintf ppf "@[\\left(";
         Format.fprintf
           ppf "@[<hv2>@[<hv>%a@] \\Rightarrow @ @[<hv>%a@]@]" r1 2 r2 3;
         if l < 3 then Format.fprintf ppf "\\right)@]"
       method fiff r1 r2 = fun ppf l ->
         if l < 4 then Format.fprintf ppf "@[\\left(";
         Format.fprintf
           ppf "@[<hv2>@[<hv>%a@] \\Leftrightarrow @ @[<hv>%a@]@]" r1 4 r2 4;
         if l < 4 then Format.fprintf ppf "\\right)@]"
       method fforall xty r1 = fun ppf l ->
         Format.fprintf ppf "\\forall %a.@. %a" TypEnv.pr_elem_compact xty r1 0
       method fexists xty r1 = fun ppf l ->
         Format.fprintf ppf "\\exists %a.@. %a" TypEnv.pr_elem_compact xty r1 0
     end)
    phi ppf 4;
  Format.fprintf ppf "@]"

let pr ppf phi =
  Format.fprintf ppf "@[<hv>";
  fold
    (object
      method fatom atm = fun ppf l ->
        Atom.pr ppf atm
      method ftrue _ = fun ppf l ->
        Format.fprintf ppf "true"
      method ffalse _ = fun ppf l ->
        Format.fprintf ppf "false"
      method fnot r1 = fun ppf l ->
        Format.fprintf ppf "not %a" r1 0
      method fand r1 r2 = fun ppf l ->
        if l < 1 then Format.fprintf ppf "@[(@[<hv>";
        Format.fprintf ppf "%a /\\@ %a" r1 1 r2 1;
        if l < 1 then Format.fprintf ppf "@])@]"
      method for_ r1 r2 = fun ppf l ->
        if l < 2 then Format.fprintf ppf "@[(@[<hv>";
        Format.fprintf ppf "%a \\/@ %a" r1 2 r2 2;
        if l < 2 then Format.fprintf ppf "@])@]"
      method fimply r1 r2 = fun ppf l ->
        if l < 3 then Format.fprintf ppf "@[(";
        Format.fprintf ppf "@[<hv2>@[<hv>%a@] =>@ @[<hv>%a@]@]" r1 2 r2 3;
        if l < 3 then Format.fprintf ppf ")@]"
      method fiff r1 r2 = fun ppf l ->
        if l < 4 then Format.fprintf ppf "@[(";
        Format.fprintf ppf "@[<hv2>@[<hv>%a@] <=>@ @[<hv>%a@]@]" r1 4 r2 4;
        if l < 4 then Format.fprintf ppf ")@]"
      method fforall xty r1 = fun ppf l ->
        Format.fprintf ppf "A %a. %a" TypEnv.pr_elem_compact xty r1 0
      method fexists xty r1 = fun ppf l ->
        Format.fprintf ppf "E %a. %a" TypEnv.pr_elem_compact xty r1 0
    end)
    phi ppf 4;
  Format.fprintf ppf "@]"

let pr_list ppf = Format.fprintf ppf "@[<hv>%a@]" (List.pr pr ",@,")

(*
let pr ppf =
  let rec _pr prec ppf =
    visit
      (object
          method ftrue _ =
            Format.fprintf ppf "%s" Common.symbols.(0)
          method ffalse _ =
            Format.fprintf ppf "%s" Common.symbols.(1)
          method fnot phi =
            let prec' = 5 in
            (if prec' <= prec then
               Format.fprintf ppf "(");
            Format.fprintf
              ppf
              "%s%a"
              Common.symbols.(2)
              (_pr prec') phi;
            if prec' <= prec then
              Format.fprintf ppf ")"
          method fand phi1 phi2 =
            let prec' = 4 in
            (if prec' <= prec then
               Format.fprintf ppf "(");
            Format.fprintf
              ppf
              "%a"
              (Util.pr_list_string_separator (_pr prec') Common.symbols.(3))
              ((conjs_of phi1) @ (conjs_of phi2));
            if prec' <= prec then
              Format.fprintf ppf ")"
          method f_or phi1 phi2 =
            let prec' = 3 in
            (if prec' <= prec then
               Format.fprintf ppf "(");
            Format.fprintf
              ppf
              "%a"
              (Util.pr_list_string_separator (_pr prec') Common.symbols.(4))
              ((disjs_of phi1) @ (disjs_of phi2));
            if prec' <= prec then
              Format.fprintf ppf ")"
          method fimply phi1 phi2 =
            let prec' = 2 in
            (if prec' <= prec then
               Format.fprintf ppf "(");
            Format.fprintf
              ppf "%a%s%a"
              (_pr prec') phi1
              Common.symbols.(5)
              (_pr prec') phi2;
            if prec' <= prec then
              Format.fprintf ppf ")"
          method fforall id phi =
            let prec' = 1 in
            (if prec' <= prec then
               Format.fprintf ppf "(");
            Format.fprintf
              ppf
              "%s%a.%a"
              Common.symbols.(6)
              Id.pr id
              (_pr prec') phi;
            if prec' <= prec then
              Format.fprintf ppf ")"
          method fexists id phi =
            let prec' = 1 in
            (if prec' <= prec then
               Format.fprintf ppf "(");
            Format.fprintf
              ppf
              "%s%a.%a"
              Common.symbols.(7)
              Id.pr id
              (_pr prec') phi;
            if prec' <= prec then
              Format.fprintf ppf ")"
          method fbinrel ar1 rel ar2 =
            Format.fprintf
              ppf
              "%a%s%a"
              Arith.pr ar1
              (BinRel.string_of rel)
              Arith.pr ar2
          method fatom id =
            Format.fprintf
              ppf
              "%a"
              Id.pr id
          method fvar id ids =
            Format.fprintf
              ppf
              "%s(%a)"
              id
              (Util.pr_list Id.pr ",") ids
        end)
  in
  _pr 0 ppf
 *)


(** {6 Inspectors} *)

let fvs_unit phi =
  SimTypJudge.env_of phi Type.mk_bool
  |> TypEnv.filter_ty Type.mk_unit
  |> List.unique
let fvs_bool phi =
  SimTypJudge.env_of phi Type.mk_bool
  |> TypEnv.filter_ty Type.mk_bool
  |> List.unique
let fvs_int phi =
  SimTypJudge.env_of phi Type.mk_bool
  |> TypEnv.filter_ty Type.mk_int
  |> List.unique
let fvs_ty phi =
  SimTypJudge.env_of phi Type.mk_bool
  |> TypEnv.merge

let fpvs = fold_set Atom.fpvs
let fpvs_strict = fold_set Atom.fpvs_strict

let rec args_of_binder phi acc =
  match phi with
  | Binder(Binder.Forall(ty), Pattern.V(x), p)
  | Binder(Binder.Exists(ty), Pattern.V(x), p) ->
    args_of_binder p ((x,ty)::acc)
  | _ -> acc, phi
let args_of_binder phi = args_of_binder phi []

let string_of = Term.string_of

let atoms = fold_set List.return

let conjuncts_of =
  lazy_para
    (object
      method fatom atm = [of_atom atm]
      method ftrue () = [mk_true]
      method ffalse () = [mk_false]
      method fnot phi _ = [bnot phi]
      method fand _ phis1 _ phis2 = Lazy.force phis1 @ Lazy.force phis2
      method for_ phi1 _ phi2 _ = [bor [phi1; phi2]]
      method fimply phi1 _ phi2 _ = [imply phi1 phi2]
      method fiff phi1 _ phi2 _ = [mk_iff phi1 phi2]
      (*[imply phi1 phi2; imply phi2 phi1]*)
      method fforall xty phi1 _ = [forall [xty] phi1]
      method fexists xty phi1 _ = [exists [xty] phi1]
    end)

let disjuncts_of =
  lazy_para
    (object
      method fatom atm = [of_atom atm]
      method ftrue () = [mk_true]
      method ffalse () = [mk_false]
      method fnot phi _ = [bnot phi]
      method fand phi1 _ phi2 _ = [band [phi1; phi2]]
      method for_ _ phis1 _ phis2 = Lazy.force phis1 @ Lazy.force phis2
      method fimply phi1 _ phi2 _ = [imply phi1 phi2]
      (*[bnot phi1; phi2]*)
      method fiff phi1 _ phi2 _ = [mk_iff phi1 phi2]
      (*[band [phi1; phi2]; band [bnot phi1; bnot phi2]]*)
      method fforall xty phi1 _ = [forall [xty] phi1]
      method fexists xty phi1 _ = [exists [xty] phi1]
    end)

(** {6 Operators} *)

let subst_tvars tsub = term_of >> Term.subst_tvars tsub >> of_term

let elim_imply_iff =
  fold
    (object
      method fatom = of_atom
      method ftrue () = mk_true
      method ffalse () = mk_false
      method fnot = bnot
      method fand = mk_and
      method for_ = mk_or
      method fimply phi1' phi2' = bor [bnot phi1'; phi2']
      method fiff phi1' phi2' =
        bor [band [phi1'; phi2']; band [bnot phi1'; bnot phi2']]
      method fforall xty phi' = forall [xty] phi'
      method fexists xty phi' = exists [xty] phi'
    end)

let eqcls_of =
  conjuncts_of
  >> (List.partition_map
        (fun phi ->
           match phi |> term_of |> Term.fun_args with
           | Const(Const.Eq ty), [Var x1; Var x2] -> `L([x1; x2], ty)
           | _ -> `R(phi)))
  >> (Pair.map_fst
        (fix
           (List.fold_left
              (fun eqcs (eqc2, ty2) ->
                 let updated = ref false in
                 let eqcs' =
                   List.map
                     (fun (eqc1, ty1) ->
                        if Set_.inter eqc2 eqc1 <> [] then begin
                          (*Logger.debug_assert
                            (fun () -> ty1 = ty2)
                            ~on_failure:(fun () ->
                                Format.printf "error in Formula.eqcls_of@,");*)
                          updated := true;
                          List.unique (eqc1 @ eqc2), ty1
                        end else (eqc1, ty1))
                     eqcs
                 in
                 if !updated then eqcs' else (eqc2, ty2) :: eqcs')
              [])
           List.eq_length))

let remove_annot = map_atom (Atom.remove_annot >> of_atom)

let unfold phi =
  if is_mu phi then let_mu phi (fun x phi' -> subst [x, phi] phi')
  else if is_nu phi then let_nu phi (fun x phi' -> subst [x, phi] phi')
  else phi

(** {6 Auxiliary constructors} *)

let of_tsub =
  List.map (Pair.map_fst Term.mk_var >> uncurry2 (eq Type.mk_unknown(*@todo*))) >> band

(** {6 Auxiliary destructors} *)

let resolve_duplicates_in_ttsub =
  List.classify (comp2 (=) fst fst)
  >> List.map (fun ((x, tt1) :: ttsub') ->
      (x, tt1), List.map (snd >> eq_tt tt1) ttsub')
  >> List.split
  >> Pair.map_snd List.flatten

let resolve_duplicates_in_tsub tsub =
  resolve_duplicates_in_ttsub (List.map (fun (x, t) -> x, (t, Type.mk_unknown)) tsub) |> Pair.map_fst TypTermSubst.tsub_of

let non_dup_ttsub is_valid =
  List.unique
  >> List.classify (comp2 (=) fst fst)
  >> List.for_all (function
      | [] -> assert false
      | (_, tt1) :: ttsub' ->
        List.for_all (snd >> eq_tt tt1 >> is_valid) ttsub')
let non_dup_ttsub ?(is_valid = fun t -> assert false) =
  Logger.log_block1 "TypTermSubst.non_dup" (non_dup_ttsub is_valid)

let of_ttsub_elem (x, (t, ty)) =
  if Term.mk_var x = t then mk_true else eq_tt (Term.mk_var x, ty) (t, ty)
let of_ttsub = List.map of_ttsub_elem >> band

(** {6 Operators} *)

let extract_ttsub is_bound =
  eqcls_of
  >> (Pair.map_fst
        (List.map
           (fun (eqc, ty) ->
              let bvs, fvs = List.partition is_bound eqc in
              if bvs = [] then
                let tt = Term.mk_var (List.hd fvs), ty in
                List.map (fun x -> x, tt) (List.tl fvs),
                []
              else
                let bv, bvs' = List.hd bvs, List.tl bvs
                in
                List.map (fun fv -> fv, (Term.mk_var bv, ty)) fvs,
                List.map (fun bv' -> eq ty (Term.mk_var bv) (Term.mk_var bv')) bvs')
         >> List.unzip
         >> Pair.map List.flatten List.flatten
         (* for ML type system *)))
  >> (fun ((ttsub, phis'), phis) -> ttsub, phis @ phis' |> band)
(** [extract_ttsub p phi] returns [(ttsub, phis)]
    @ensure List.for_all (p >> not) (dom ttsub) *)
(*val extract_ttsub : (Idnt.t -> bool) -> t -> TypTermSubst.t * t*)
let extract_ttsub =
  Logger.log_block2 "Formula.extract_ttsub"
    ~after:(Logger.printf "output: %a" (Pair.pr TypTermSubst.pr pr)) extract_ttsub

let is_simple x t =
  not (Idnt.is_coeff x) && Term.coeffs t = []
let to_simple_ttsub =
  conjuncts_of
  >> List.partition_map
    (term_of >> Term.fun_args >> function
      | Term.Const(Const.Eq ty), [Term.Var(x); t] when is_simple x t ->
        `L(x, (t, ty))
      | Term.Const(Const.Eq ty), [t; Term.Var(x)] when is_simple x t ->
        `L(x, (t, ty))
      | t, ts -> `R(mk_app t ts))
  >> Pair.map_fst (List.unique >> resolve_duplicates_in_ttsub)
  >> (fun ((ttsub, phis1), phis2) ->
      ttsub, (* subst tsub*)band (phis1 @ phis2))

(** [to_rename_tsub bvs phi] tries to eliminate as many term variables,
    which are existentially quantified implicitly, in [phi] as
    possible
    @ensure variables in [bvs] are not eliminated *)
let to_rename_tsub simplify bvs phi =
  phi
  |> extract_ttsub (fun x -> List.mem x bvs || Idnt.is_coeff x)
  |> Pair.map TypTermSubst.tsub_of simplify
  |> (fun (tsub, phi) -> tsub, subst tsub phi)
let to_rename_tsub =
  Logger.log_block3 "Formula.to_rename_tsub"
    ~before:(fun _ bvs phi ->
        Logger.printf2 "input:@,  %a@,  %a@," Idnt.pr_list bvs pr phi)
    ~after:(snd >> Logger.printf "output:@,  %a" pr)
    to_rename_tsub

let is_const bvs x t =
  not (List.mem x bvs) && not (Idnt.is_coeff x) && Term.fvs t = []
let to_const_tsub bvs phi =
  let tsub, phis =
    phi
    |> conjuncts_of
    |> List.partition_map
      (term_of >> Term.fun_args >> function
        | Term.Const(Const.Eq ty), [Term.Var(x); t] when is_const bvs x t ->
          `L(x, t)
        | Term.Const(Const.Eq ty), [t; Term.Var(x)] when is_const bvs x t ->
          `L(x, t)
        | Term.Var(x), [] when is_const bvs x (IntTerm.make 0(*dummy*)) ->
          `L(x, term_of mk_true)
        | Term.Const(Const.Not), [Term.Var(x)]
          when is_const bvs x (IntTerm.make 0(*dummy*)) ->
          `L(x, term_of mk_false)
        | t, ts ->`R(mk_app t ts))
    |> Pair.map_fst List.unique
  in
  if Bag.duplicated (List.map fst tsub)
  then tsub, mk_false
  else tsub, subst tsub (band phis)
