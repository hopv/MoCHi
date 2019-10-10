open Combinator
open Util

exception CannotUnify
exception CannotMatch

module type BINDER = sig
  type t
  val pr : Pattern.t -> unit Printer.t -> t Printer.t
end

module type CONST = sig
  type t
  val pr : unit Printer.t list -> t Printer.t
  val pr_tex : unit Printer.t list -> t Printer.t
end

module Make = functor(Binder : BINDER) -> functor(Const : CONST) -> struct
  (** {6 Constructors} *)

  type t =
    | Var of Idnt.t
    | Const of Const.t
    | App of t * t
    | Binder of Binder.t * Pattern.t * t

  (** {6 Auxiliary constructors} *)

  let mk_var x = Var(x)
  let mk_const c = Const(c)
  let mk_binder b p t = Binder(b, p, t)
  let rec mk_app t ts =
    match ts with
    | [] -> t
    | t' :: ts' -> mk_app (App(t, t')) ts'
  let mk_app2 (t :: ts) = mk_app t ts

  let new_var () = mk_var (Idnt.new_var ())
  let var_of_string x = mk_var (Idnt.make x)
  let new_coeff () = mk_var (Idnt.new_coeff ())

  (** {6 Auxiliary destructors} *)

  let rec fun_args t =
    match t with
    | App(t1, t2) ->
      let f, args = fun_args t1 in
      f, args @ [t2]
    | _ -> t, []

  let let_var t k =
    match t with
    | Var(x) -> k x
    | _ -> raise (Global.NoMatch "let_var")

  let let_const t k =
    match t with
    | Const(c) -> k c
    | _ -> raise (Global.NoMatch "let_const")

  let let_app t k =
    match t with
    | App(t1, t2) -> k t1 t2
    | _ -> raise (Global.NoMatch "let_app")

  let let_fun_args t k =
    match fun_args t with
    | f, args -> k f args
    | _ -> raise (Global.NoMatch "let_fun_args")

  let let_binder t k =
    match t with
    | Binder(b, p, t) -> k b p t
    | _ -> raise (Global.NoMatch "let_binder")

  let var_of t = let_var t id

  let is_var t =
    match t with
    | Var(_) -> true
    | _ -> false

  let is_const t =
    match t with
    | Const(_) -> true
    | _ -> false

  let is_app t =
    match t with
    | App(_, _) -> true
    | _ -> false

  let is_binder t =
    match t with
    | Binder(_, _, _) -> true
    | _ -> false

  (** {6 Morphisms} *)

  let rec para f t =
    match t with
    | Var(x) ->
      f#fvar x
    | Const(c) ->
      f#fcon c
    | App(t1, t2) ->
      f#fapp t1 (para f t1) t2 (para f t2)
    | Binder(b, p, t1) ->
      f#fbin b p t1 (para f t1)

  let rec para_app f t =
    let t0, ts = fun_args t in
    if ts = [] then
      match t0 with
      | Var(x) ->
        f#fvar x
      | Const(c) ->
        f#fcon c
      | Binder(b, p, t1) ->
        f#fbin b p t1 (para_app f t1)
    else
      f#fapp
        t0 (para_app f t0)
        ts (List.map (para_app f) ts)

  let rec para_wo_app f t =
    match fun_args t with
    | Var(x), ts ->
      f#fvar x ts (List.map (para_wo_app f) ts)
    | Const(c), ts ->
      f#fcon c ts (List.map (para_wo_app f) ts)
    | Binder(b, p, t1), ts ->
      f#fbin b p
        t1 (para_wo_app f t1)
        ts (List.map (para_wo_app f) ts)

  let lazy_para f t =
    Lazy.force
      (para
         (object
           method fvar x = lazy (f#fvar x)
           method fcon c = lazy (f#fcon c)
           method fapp t1 r1 t2 r2 = lazy (f#fapp t1 r1 t2 r2)
           method fbin b p t1 r1 = lazy (f#fbin b p t1 r1)
         end)
         t)

  let lazy_para_app f t =
    Lazy.force
      (para_app
         (object
           method fvar x = lazy (f#fvar x)
           method fcon c = lazy (f#fcon c)
           method fapp t1 r1 ts rs = lazy (f#fapp t1 r1 ts rs)
           method fbin b p t1 r1 = lazy (f#fbin b p t1 r1)
         end)
         t)

  let lazy_para_wo_app f t =
    Lazy.force
      (para_wo_app
         (object
           method fvar x ts rs = lazy (f#fvar x ts rs)
           method fcon c ts rs = lazy (f#fcon c ts rs)
           method fbin b p t1 r1 ts rs = lazy (f#fbin b p t1 r1 ts rs)
         end)
         t)

  let fold f =
    para
      (object
        method fvar = f#fvar
        method fcon = f#fcon
        method fapp _ r1 _ r2 = f#fapp r1 r2
        method fbin b p _ = f#fbin b p
      end)

  let fold_app f =
    para_app
      (object
        method fvar x = f#fvar x
        method fcon c = f#fcon c
        method fapp _ r _ rs = f#fapp r rs
        method fbin b p _ r = f#fbin b p r
      end)

  let fold_wo_app f =
    para_wo_app
      (object
        method fvar x _ rs = f#fvar x rs
        method fcon c _ rs = f#fcon c rs
        method fbin b p _ r _ rs = f#fbin b p r rs
      end)

  let visit f =
    lazy_para
      (object
        method fvar = f#fvar
        method fcon = f#fcon
        method fapp t1 _ t2 _ = f#fapp t1 t2
        method fbin b p t1 _ = f#fbin b p t1
      end)

  let visit_wo_app f =
    lazy_para_wo_app
      (object
        method fvar x ts _ = f#fvar x ts
        method fcon c ts _ = f#fcon c ts
        method fbin b p t1 _ ts _ = f#fbin b p t1 ts
      end)

  let map_var f =
    fold
      (object
        method fvar x = mk_var (f x)
        method fcon c = mk_const c
        method fapp t1 t2 = mk_app t1 [t2]
        method fbin b p t1 = mk_binder b p t1
      end)

  let map_con f =
    fold
      (object
        method fvar x = mk_var x
        method fcon c = mk_const (f c)
        method fapp t1 t2 = mk_app t1 [t2]
        method fbin b p t1 = mk_binder b p t1
      end)

  (** {6 Printers} *)

  let upr_of_app upr uprs = fun ppf () ->
    Format.fprintf
      ppf
      "@[<hov2>%a@ %a@]"
      upr ()
      (Printer.concat_uprs_app uprs "@ ") ()

  (** @todo add prec
      @todo add one-liner *)
  let upr_of =
    fold_wo_app
      (object
        method fvar x uprs =
          if uprs = [] then
            Printer.upr_of Idnt.pr x
          else
            upr_of_app (Printer.upr_of Idnt.pr x) uprs
            |> Printer.paren
        method fcon c uprs =
          if uprs = [] then
            Printer.upr_of (Const.pr uprs) c
          else
            Printer.upr_of (Const.pr uprs) c
            |> Printer.paren
        method fbin b p upr uprs =
          if uprs = [] then
            Printer.upr_of (Binder.pr p upr) b
            |> Printer.paren
          else
            upr_of_app
              (Printer.upr_of (Binder.pr p upr) b
               |> Printer.paren)
              uprs
            |> Printer.paren
      end)

  let tex_upr_of =
    fold_wo_app
      (object
        method fvar x uprs =
          if uprs = [] then
            Printer.upr_of Idnt.pr x
          else
            upr_of_app (Printer.upr_of Idnt.pr x) uprs
            |> Printer.paren_tex
        method fcon c uprs =
          if uprs = [] then
            Printer.upr_of (Const.pr_tex uprs) c
          else
            Printer.upr_of (Const.pr_tex uprs) c
            |> Printer.paren_tex
        method fbin b p upr uprs =
          if uprs = [] then
            Printer.upr_of (Binder.pr p upr) b
            |> Printer.paren_tex
          else
            upr_of_app
              (Printer.upr_of (Binder.pr p upr) b
               |> Printer.paren_tex)
              uprs
            |> Printer.paren_tex
      end)

  let pr ppf t = upr_of t ppf ()
  let pr_list ppf = Format.fprintf ppf "@[<hv>%a@]" (List.pr pr ",@,")
  let pr_tex ppf t = tex_upr_of t ppf ()

  (** {6 Inspectors} *)

  let string_of = Printer.string_of pr

  let equiv t1 t2 = t1 = t2

  let occurs x =
    fold
      (object
        method fvar y = x = y
        method fcon _ = false
        method fapp b1 b2 = b1 || b2
        method fbin _ p b1 = b1 && not (Pattern.occurs x p)
      end)

  let num_of_const_occurrences c =
    fold
      (object
        method fvar _ = 0
        method fcon c' = if c = c' then 1 else 0
        method fapp n1 n2 = n1 + n2
        method fbin _ _ n1 = n1
      end)

  let num_of_var_occurrences x =
    fold
      (object
        method fvar x' = if x = x' then 1 else 0
        method fcon _ = 0
        method fapp n1 n2 = n1 + n2
        method fbin _ p n1 =
          if List.mem x (Pattern.fvs p) then 0 else n1
      end)

  let fvs =
    fold
      (object
        method fvar x = if Idnt.is_coeff x then [] else [x]
        method fcon _ = []
        method fapp fvs1 fvs2 = List.unique (fvs1 @ fvs2)
        method fbin _ p fvs1 = Set_.diff fvs1 (Pattern.fvs p)
      end)

  let coeffs =
    fold
      (object
        method fvar x = if Idnt.is_coeff x then [x] else []
        method fcon _ = []
        method fapp cs1 cs2 = List.unique (cs1 @ cs2)
        method fbin _ p cs1 = Set_.diff cs1 (Pattern.fvs p)
      end)

  let constants =
    fold
      (object
        method fvar _ = []
        method fcon c = [c]
        method fapp cs1 cs2 = List.unique (cs1 @ cs2)
        method fbin _ _ cs1 = cs1
      end)

  let find_mapc f t =
    para
      (object
        method fvar x = fun ctx ->
          f ctx (mk_var x)
          |> Option.elem_of_nf
        method fcon c = fun ctx ->
          f ctx (mk_const c)
          |> Option.elem_of_nf
        method fapp t1 r1 t2 r2 = fun ctx ->
          let ctx1 = fun t1 -> ctx (mk_app t1 [t2]) in
          let ctx2 = fun t2 -> ctx (mk_app t1 [t2]) in
          ctx1
          |> try_
            r1
            (fun Not_found _ ->
               ctx2
               |> try_
                 r2
                 (fun Not_found _ ->
                    f ctx (mk_app t1 [t2])
                    |> Option.elem_of_nf))
        method fbin _ _ _ _ = fun ctx ->
          assert false
      end)
      t
      id

  let find_all_mapc f t =
    para
      (object
        method fvar x = fun ctx ->
          f ctx (mk_var x)
          |> Option.list_of
        method fcon c = fun ctx ->
          f ctx (mk_const c)
          |> Option.list_of
        method fapp t1 r1 t2 r2 = fun ctx ->
          let ctx1 = fun t1 -> ctx (mk_app t1 [t2]) in
          let ctx2 = fun t2 -> ctx (mk_app t1 [t2]) in
          (f ctx (mk_app t1 [t2])
           |> Option.list_of)
          @ r1 ctx1
          @ r2 ctx2
        method fbin _ _ _ _ = fun ctx ->
          assert false
      end)
      t
      id

  (** {6 Operators} *)

  let subst tsub t =
    fold
      (object
        method fvar x = fun tsub ->
          Map_.apply_default (mk_var x) tsub x
        method fcon c = fun tsub ->
          mk_const c
        method fapp r1 r2 = fun tsub ->
          mk_app (r1 tsub) [r2 tsub]
        method fbin b p r1 = fun tsub ->
          tsub
          |> (* @todo *)
          List.map
            (function
              | (Idnt.N(n), t) -> Idnt.N(n + 1), t
              | xt -> xt)
          |> flip Map_.diff (Pattern.fvs p)
          |> r1
          |> mk_binder b p
      end)
      t
      tsub

  module IdntMap =
    Map.Make(struct type t = Idnt.t let compare = compare end)

  let subst_m tsub t =
    fold
      (object
        method fvar x = fun tsub ->
          try
            IdntMap.find x tsub
          with Not_found ->
            mk_var x
        method fcon c = fun tsub ->
          mk_const c
        method fapp r1 r2 = fun tsub ->
          mk_app (r1 tsub) [r2 tsub]
        method fbin b p r1 = fun tsub ->
          let xs = Pattern.fvs p in
          tsub
          |> IdntMap.filter (fun x _ -> List.mem x xs |> not)
          |> r1
          |> mk_binder b p
      end)
      t
      tsub

  let subst_fixed ?(simplify = id) tsub t =
    fix (subst tsub >> simplify) (=)(*equiv*) t
  let subst_fixed ?(simplify = id) =
    Logger.log_block2
            "AbsTerm.subst_fixed"
      ~before:(fun _ -> Logger.printf "input: %a@," pr)
      ~after:(Logger.printf "output: %a" pr)
      (subst_fixed ~simplify:simplify)

  let fresh xs =
    subst (List.map (fun x -> x, new_var ()) xs)

  let rename vmap =
    subst (List.map (fun (x, y) -> x, mk_var y) vmap)

  let alpha_conv t =
    fold
      (object
        method fvar x = fun vmap ->
          mk_var (Map_.apply_default x vmap x)
        method fcon c = fun vmap ->
          mk_const c
        method fapp r1 r2 = fun vmap ->
          mk_app (r1 vmap) [r2 vmap]
        method fbin b p r1 = fun vmap ->
          let vmap' = Pattern.new_vmap p in
          mk_binder b (Pattern.rename vmap' p) (r1 (vmap' @ vmap))
      end)
      t
      []

  let shift k t =
    fold
      (object
        method fvar x = fun m ->
          match x with
          | Idnt.N(n) ->
            if n > m then
              mk_var (Idnt.N(n + k))
            else
              mk_var (Idnt.N(n))
          | _ -> assert false
        method fcon c = fun m ->
          mk_const c
        method fapp r1 r2 = fun m ->
          mk_app (r1 m) [r2 m]
        method fbin b p r1 = fun m ->
          mk_binder b p (r1 (m + 1))
      end)
      t
      (-1)

  let rec reduce tts =
    match tts with
    | [] -> []
    | (t1, t2) :: tts' ->
      if t1 = t2 then
        reduce tts'
      else begin
        match fun_args t1, fun_args t2 with
        | (Const(c1), ts1), (Const(c2), ts2) ->
          if c1 = c2 && List.eq_length ts1 ts2 then
            reduce (List.combine ts1 ts2 @ tts')
          else
            begin
              Logger.printf2 ~force:true
                "incompatible types: %a and %a@," pr t1 pr t2;
              raise CannotUnify
            end
        | _, _ ->
          (t1, t2) :: reduce tts'
      end

  let rec unify gvs tts xts1 xts2 =
    Logger.printf "#tts = %a@," Integer.pr (List.length tts);
    if tts = [] then
      xts1 @ xts2
    else begin
      let xts, tmp =
        List.partition_map
          (function
            | Var(x), t when fvs t = [] ->
              `L(x, t)
            | t, Var(x) when fvs t = [] ->
              `L(x, t)
            | Var(x), t when not (List.mem x gvs) ->
              `R(Var(x), t)
            | t, Var(x) when not (List.mem x gvs) ->
              `R(Var(x), t)
            | Var(x), t | t, Var(x) ->
              `R(Var(x), t)
            | t1, t2 ->
              Logger.printf2 ~force:true
                "incompatible types: %a and %a@," pr t1 pr t2;
              raise CannotUnify)
          tts
      in
      let xts = List.unique xts in
      if Bag.duplicated (List.map fst xts) then
        begin
          let ts = Bag.get_dup_elems xts |> List.map snd in
          Logger.printf ~force:true
            "incompatible types: %a@," (List.pr pr ",") ts;
          raise CannotUnify
        end;
      let sub =
        List.fold_left
          (fun sub (x, t) -> IdntMap.add x t sub)
          IdntMap.empty xts
      in
      let tmp =
        tmp
        |> List.map (Pair.lift (subst_m sub))
        |> reduce
      in
      match tmp with
      | [] ->
        let xts2' = List.map (Pair.map_snd (subst_m sub)) xts2 in
        xts @ xts1 @ xts2'
      | (Var(x), t) :: tts'
      | (t, Var(x)) :: tts' ->
        if occurs x t then
          begin
            Logger.printf2 ~force:true
              "recursive type constraint error: %a =?= %a@,"
              Idnt.pr x pr t;
            raise CannotUnify
          end
        else
          let tts'' =
            tts'
            |> List.map (Pair.lift (subst [x, t]))
            |> reduce
          in
          let sub = IdntMap.add x t sub in
          let xts2' =
            List.map
              (fun (x', t') -> assert (x <> x'); x', subst_m sub t')
              xts2
          in
          unify gvs tts'' (xts @ xts1) ((x, t) :: xts2')
      | _ -> assert false
    end

  let unify gvs tts =
    unify gvs (tts |> reduce) [] []
    |> Logger.pprintf
      "unification succeeded:@,  %a"
      (List.pr (Pair.pr Idnt.pr pr) ",@ ")
  let unify ?(gvs=[]) = Logger.log_block1 "AbsTerm.unify" (unify gvs)

  let rec pat_match t p =
    match t, p with
    | _, Var(x) ->
      [x, t]
    | App(t1, t2), App(p1, p2) ->
      pat_match t1 p1 @ pat_match t2 p2
    | Const(c1), Const(c2) ->
      if c1 = c2 then
        []
      else
        raise CannotMatch
    | _, _ ->
      raise CannotMatch
  let pat_match t p =
    pat_match t p
    |> (if_ Map_.non_dup
          id
          (fun _ -> raise CannotMatch))
end
