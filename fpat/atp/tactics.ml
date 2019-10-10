(* ========================================================================= *)
(* Goals, LCF-like tactics and Mizar-like proofs.                            *)
(*                                                                           *)
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
(* ========================================================================= *)

type goals =
  Goals of ((string * fol formula) list * fol formula)list *
           (thm list -> thm);;

(* ------------------------------------------------------------------------- *)
(* Printer for goals (just shows first goal plus total number).              *)
(* ------------------------------------------------------------------------- *)

let print_goal =
  let print_hyp (l,fm) =
    open_hbox(); print_string(l^":"); print_space();
    print_formula print_atom fm; print_newline(); close_box() in
  fun (Goals(gls,jfn)) ->
    match gls with
      (asl,w)::ogls ->
         print_newline();
         (if ogls = [] then print_string "1 subgoal:" else
          (print_int (length gls);
           print_string " subgoals starting with"));
         print_newline();
         do_list print_hyp (rev asl);
         print_string "---> ";
         open_hvbox 0; print_formula print_atom w; close_box();
         print_newline()
    | [] -> print_string "No subgoals";;

#install_printer print_goal;;

(* ------------------------------------------------------------------------- *)
(* Setting up goals and terminating them in a theorem.                       *)
(* ------------------------------------------------------------------------- *)

let set_goal p =
  let chk th = if concl th = p then th else failwith "wrong theorem" in
  Goals([[],p],fun [th] -> chk(modusponens th truth));;

let extract_thm gls =
  match gls with
    Goals([],jfn) -> jfn []
  | _ -> failwith "extract_thm: unsolved goals";;

let tac_proof g prf = extract_thm(itlist (fun f -> f) (rev prf) g);;

let prove p prf = tac_proof (set_goal p) prf;;

(* ------------------------------------------------------------------------- *)
(* Conjunction introduction tactic.                                          *)
(* ------------------------------------------------------------------------- *)

let conj_intro_tac (Goals((asl,And(p,q))::gls,jfn)) =
  let jfn' (thp::thq::ths) =
    jfn(imp_trans_chain [thp; thq] (and_pair p q)::ths) in
  Goals((asl,p)::(asl,q)::gls,jfn');;

(* ------------------------------------------------------------------------- *)
(* Handy idiom for tactic that does not split subgoals.                      *)
(* ------------------------------------------------------------------------- *)

let jmodify jfn tfn (th::oths) = jfn(tfn th :: oths);;

(* ------------------------------------------------------------------------- *)
(* Version of gen_right with a bound variable change.                        *)
(* ------------------------------------------------------------------------- *)

let gen_right_alpha y x th =
  let th1 = gen_right y th in
  imp_trans th1 (alpha x (consequent(concl th1)));;

(* ------------------------------------------------------------------------- *)
(* Universal introduction.                                                   *)
(* ------------------------------------------------------------------------- *)

let forall_intro_tac y (Goals((asl,(Forall(x,p) as fm))::gls,jfn)) =
  if mem y (fv fm) or exists (mem y ** fv ** snd) asl
  then failwith "fix: variable already free in goal" else
  Goals((asl,subst(x |=> Var y) p)::gls,
        jmodify jfn (gen_right_alpha y x));;

(* ------------------------------------------------------------------------- *)
(* Another inference rule: |- P[t] ==> exists x. P[x]                        *)
(* ------------------------------------------------------------------------- *)

let right_exists x t p =
  let th = contrapos(ispec t (Forall(x,Not p))) in
  let Not(Not p') = antecedent(concl th) in
  end_itlist imp_trans
   [imp_contr p' False; imp_add_concl False (iff_imp1 (axiom_not p'));
    iff_imp2(axiom_not (Not p')); th; iff_imp2(axiom_exists x p)];;

(* ------------------------------------------------------------------------- *)
(* Existential introduction.                                                 *)
(* ------------------------------------------------------------------------- *)

let exists_intro_tac t (Goals((asl,Exists(x,p))::gls,jfn)) =
  Goals((asl,subst(x |=> t) p)::gls,
        jmodify jfn (fun th -> imp_trans th (right_exists x t p)));;

(* ------------------------------------------------------------------------- *)
(* Implication introduction tactic.                                          *)
(* ------------------------------------------------------------------------- *)

let imp_intro_tac s (Goals((asl,Imp(p,q))::gls,jfn)) =
  let jmod = if asl = [] then add_assum True else imp_swap ** shunt in
  Goals(((s,p)::asl,q)::gls,jmodify jfn jmod);;

(* ------------------------------------------------------------------------- *)
(* Append contextual hypothesis to unconditional theorem.                    *)
(* ------------------------------------------------------------------------- *)

let assumptate (Goals((asl,w)::gls,jfn)) th =
  add_assum (list_conj (map snd asl)) th;;

(* ------------------------------------------------------------------------- *)
(* Get the first assumption (quicker than head of assumps result).           *)
(* ------------------------------------------------------------------------- *)

let firstassum asl =
  let p = snd(hd asl) and q = list_conj(map snd (tl asl)) in
  if tl asl = [] then imp_refl p else and_left p q;;

(* ------------------------------------------------------------------------- *)
(* Import "external" theorem.                                                *)
(* ------------------------------------------------------------------------- *)

let using ths p g =
  let ths' = map (fun th -> itlist gen (fv(concl th)) th) ths in
  map (assumptate g) ths';;

(* ------------------------------------------------------------------------- *)
(* Turn assumptions p1,...,pn into theorems |- p1 /\ ... /\ pn ==> pi        *)
(* ------------------------------------------------------------------------- *)

let rec assumps asl =
  match asl with
    [] -> []
  | [l,p] -> [l,imp_refl p]
  | (l,p)::lps ->
        let ths = assumps lps in
        let q = antecedent(concl(snd(hd ths))) in
        let rth = and_right p q in
        (l,and_left p q)::map (fun (l,th) -> l,imp_trans rth th) ths;;

(* ------------------------------------------------------------------------- *)
(* Produce canonical theorem from list of theorems or assumption labels.     *)
(* ------------------------------------------------------------------------- *)

let by hyps p (Goals((asl,w)::gls,jfn)) =
  let ths = assumps asl in map (fun s -> assoc s ths) hyps;;

(* ------------------------------------------------------------------------- *)
(* Main automatic justification step.                                        *)
(* ------------------------------------------------------------------------- *)

let justify byfn hyps p g =
  match byfn hyps p g with
    [th] when consequent(concl th) = p -> th
  | ths ->
      let th = lcffol(itlist (mk_imp ** consequent ** concl) ths p) in
      if ths = [] then assumptate g th else imp_trans_chain ths th;;

(* ------------------------------------------------------------------------- *)
(* Nested subproof.                                                          *)
(* ------------------------------------------------------------------------- *)

let proof tacs p (Goals((asl,w)::gls,jfn)) =
  [tac_proof (Goals([asl,p],fun [th] -> th)) tacs];;

(* ------------------------------------------------------------------------- *)
(* Trivial justification, producing no hypotheses.                           *)
(* ------------------------------------------------------------------------- *)

let at once p gl = [] and once = [];;

(* ------------------------------------------------------------------------- *)
(* Hence an automated terminal tactic.                                       *)
(* ------------------------------------------------------------------------- *)

let auto_tac byfn hyps (Goals((asl,w)::gls,jfn) as g) =
  let th = justify byfn hyps w g in
  Goals(gls,fun ths -> jfn(th::ths));;

(* ------------------------------------------------------------------------- *)
(* A "lemma" tactic.                                                         *)
(* ------------------------------------------------------------------------- *)

let lemma_tac s p byfn hyps (Goals((asl,w)::gls,jfn) as g) =
  let tr = imp_trans(justify byfn hyps p g) in
  let mfn = if asl = [] then tr else imp_unduplicate ** tr ** shunt in
  Goals(((s,p)::asl,w)::gls,jmodify jfn mfn);;

(* ------------------------------------------------------------------------- *)
(* Elimination tactic for existential quantification.                        *)
(* ------------------------------------------------------------------------- *)

let exists_elim_tac l fm byfn hyps (Goals((asl,w)::gls,jfn) as g) =
  let Exists(x,p) = fm in
  if exists (mem x ** fv) (w::map snd asl)
  then failwith "exists_elim_tac: variable free in assumptions" else
  let th = justify byfn hyps (Exists(x,p)) g in
  let jfn' pth =
    imp_unduplicate(imp_trans th (exists_left x (shunt pth))) in
  Goals(((l,p)::asl,w)::gls,jmodify jfn jfn');;

(* ------------------------------------------------------------------------- *)
(* If |- p ==> r and |- q ==> r then |- p \/ q ==> r                         *)
(* ------------------------------------------------------------------------- *)

let ante_disj th1 th2 =
  let p,r = dest_imp(concl th1) and q,s = dest_imp(concl th2) in
  let ths = map contrapos [th1; th2] in
  let th3 = imp_trans_chain ths (and_pair (Not p) (Not q)) in
  let th4 = contrapos(imp_trans (iff_imp2(axiom_not r)) th3) in
  let th5 = imp_trans (iff_imp1(axiom_or p q)) th4 in
  right_doubleneg(imp_trans th5 (iff_imp1(axiom_not(Imp(r,False)))));;

(* ------------------------------------------------------------------------- *)
(* Elimination tactic for disjunction.                                       *)
(* ------------------------------------------------------------------------- *)

let disj_elim_tac l fm byfn hyps (Goals((asl,w)::gls,jfn) as g) =
  let th = justify byfn hyps fm g and Or(p,q) = fm in
  let jfn' (pth::qth::ths) =
    let th1 = imp_trans th (ante_disj (shunt pth) (shunt qth)) in
    jfn(imp_unduplicate th1::ths) in
  Goals(((l,p)::asl,w)::((l,q)::asl,w)::gls,jfn');;

(* ------------------------------------------------------------------------- *)
(* A simple example.                                                         *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let g0 = set_goal
 <<(forall x. x <= x) /\
   (forall x y z. x <= y /\ y <= z ==> x <= z) /\
   (forall x y. f(x) <= y <=> x <= g(y))
   ==> (forall x y. x <= y ==> f(x) <= f(y)) /\
       (forall x y. x <= y ==> g(x) <= g(y))>>;;

let g1 = imp_intro_tac "ant" g0;;

let g2 = conj_intro_tac g1;;

let g3 = funpow 2 (auto_tac by ["ant"]) g2;;

extract_thm g3;;

(* ------------------------------------------------------------------------- *)
(* All packaged up together.                                                 *)
(* ------------------------------------------------------------------------- *)

prove <<(forall x. x <= x) /\
        (forall x y z. x <= y /\ y <= z ==> x <= z) /\
        (forall x y. f(x) <= y <=> x <= g(y))
        ==> (forall x y. x <= y ==> f(x) <= f(y)) /\
            (forall x y. x <= y ==> g(x) <= g(y))>>
      [imp_intro_tac "ant";
       conj_intro_tac;
       auto_tac by ["ant"];
       auto_tac by ["ant"]];;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Declarative proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let multishunt i th =
  let th1 = imp_swap(funpow i (imp_swap ** shunt) th) in
  imp_swap(funpow (i-1) (unshunt ** imp_front 2) th1);;

let assume lps (Goals((asl,Imp(p,q))::gls,jfn)) =
  if end_itlist mk_and (map snd lps) <> p then failwith "assume" else
  let jfn' th = if asl = [] then add_assum True th
                else multishunt (length lps) th in
  Goals((lps@asl,q)::gls,jmodify jfn jfn');;

let note (l,p) = lemma_tac l p;;

let have p = note("",p);;

let so tac arg byfn =
  tac arg (fun hyps p (Goals((asl,w)::_,_) as gl) ->
                     firstassum asl :: byfn hyps p gl);;

let fix = forall_intro_tac;;

let consider (x,p) = exists_elim_tac "" (Exists(x,p));;

let take = exists_intro_tac;;

let cases x = disj_elim_tac "" x;;

(* ------------------------------------------------------------------------- *)
(* Thesis modification.                                                      *)
(* ------------------------------------------------------------------------- *)

let conclude p byfn hyps (Goals((asl,w)::gls,jfn) as gl) =
  let th = justify byfn hyps p gl in
  if p = w then Goals((asl,True)::gls,jmodify jfn (fun _ -> th)) else
  let p',q = dest_and w in
  if p' <> p then failwith "conclude: bad conclusion" else
  let mfn th' = imp_trans_chain [th; th'] (and_pair p q) in
  Goals((asl,q)::gls,jmodify jfn mfn);;

(* ------------------------------------------------------------------------- *)
(* A useful shorthand for solving the whole goal.                            *)
(* ------------------------------------------------------------------------- *)

let our thesis byfn hyps (Goals((asl,w)::gls,jfn) as gl) =
  conclude w byfn hyps gl
and thesis = "";;

(* ------------------------------------------------------------------------- *)
(* Termination.                                                              *)
(* ------------------------------------------------------------------------- *)

let qed (Goals((asl,w)::gls,jfn) as gl) =
  if w = True then Goals(gls,fun ths -> jfn(assumptate gl truth :: ths))
  else failwith "qed: non-trivial goal";;

(* ------------------------------------------------------------------------- *)
(* A simple example.                                                         *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let ewd954 = prove
 <<(forall x y. x <= y <=> x * y = x) /\
   (forall x y. f(x * y) = f(x) * f(y))
   ==> forall x y. x <= y ==> f(x) <= f(y)>>
 [note("eq_sym",<<forall x y. x = y ==> y = x>>)
    using [eq_sym <<|x|>> <<|y|>>];
  note("eq_trans",<<forall x y z. x = y /\ y = z ==> x = z>>)
    using [eq_trans <<|x|>> <<|y|>> <<|z|>>];
  note("eq_cong",<<forall x y. x = y ==> f(x) = f(y)>>)
    using [axiom_funcong "f" [<<|x|>>] [<<|y|>>]];
  assume ["le",<<forall x y. x <= y <=> x * y = x>>;
          "hom",<<forall x y. f(x * y) = f(x) * f(y)>>];
  fix "x"; fix "y";
  assume ["xy",<<x <= y>>];
  so have <<x * y = x>> by ["le"];
  so have <<f(x * y) = f(x)>> by ["eq_cong"];
  so have <<f(x) = f(x * y)>> by ["eq_sym"];
  so have <<f(x) = f(x) * f(y)>> by ["eq_trans"; "hom"];
  so have <<f(x) * f(y) = f(x)>> by ["eq_sym"];
  so conclude <<f(x) <= f(y)>> by ["le"];
  qed];;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* More examples not in the main text.                                       *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
prove
 <<(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x)))
   ==> exists y. p(f(f(f(f(y)))))>>
  [assume ["A",<<exists x. p(x)>>];
   assume ["B",<<forall x. p(x) ==> p(f(x))>>];
   note ("C",<<forall x. p(x) ==> p(f(f(f(f(x)))))>>)
   proof
    [have <<forall x. p(x) ==> p(f(f(x)))>> by ["B"];
     so conclude <<forall x. p(x) ==> p(f(f(f(f(x)))))>> at once;
     qed];
   consider ("a",<<p(a)>>) by ["A"];
   take <<|a|>>;
   so conclude <<p(f(f(f(f(a)))))>> by ["C"];
   qed];;

(* ------------------------------------------------------------------------- *)
(* Alternative formulation with lemma construct.                             *)
(* ------------------------------------------------------------------------- *)

let lemma (s,p) (Goals((asl,w)::gls,jfn) as gl) =
  Goals((asl,p)::((s,p)::asl,w)::gls,
        fun (thp::thw::oths) ->
            jfn(imp_unduplicate(imp_trans thp (shunt thw)) :: oths)) in
prove
 <<(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x)))
   ==> exists y. p(f(f(f(f(y)))))>>
  [assume ["A",<<exists x. p(x)>>];
   assume ["B",<<forall x. p(x) ==> p(f(x))>>];
   lemma ("C",<<forall x. p(x) ==> p(f(f(f(f(x)))))>>);
     have <<forall x. p(x) ==> p(f(f(x)))>> by ["B"];
     so conclude <<forall x. p(x) ==> p(f(f(f(f(x)))))>> at once;
     qed;
   consider ("a",<<p(a)>>) by ["A"];
   take <<|a|>>;
   so conclude <<p(f(f(f(f(a)))))>> by ["C"];
   qed];;

(* ------------------------------------------------------------------------- *)
(* Running a series of proof steps one by one on goals.                      *)
(* ------------------------------------------------------------------------- *)

let run prf g = itlist (fun f -> f) (rev prf) g;;

(* ------------------------------------------------------------------------- *)
(* LCF-style interactivity.                                                  *)
(* ------------------------------------------------------------------------- *)

let current_goal = ref[set_goal False];;

let g x = current_goal := [set_goal x]; hd(!current_goal);;

let e t = current_goal := (t(hd(!current_goal))::(!current_goal));
          hd(!current_goal);;

let es t = current_goal := (run t (hd(!current_goal))::(!current_goal));
           hd(!current_goal);;

let b() = current_goal := tl(!current_goal); hd(!current_goal);;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

prove <<p(a) ==> (forall x. p(x) ==> p(f(x)))
        ==> exists y. p(y) /\ p(f(y))>>
      [our thesis at once;
       qed];;

prove
 <<(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x)))
   ==> exists y. p(f(f(f(f(y)))))>>
  [assume ["A",<<exists x. p(x)>>];
   assume ["B",<<forall x. p(x) ==> p(f(x))>>];
   note ("C",<<forall x. p(x) ==> p(f(f(f(f(x)))))>>) proof
    [have <<forall x. p(x) ==> p(f(f(x)))>> by ["B"];
     so our thesis at once;
     qed];
   consider ("a",<<p(a)>>) by ["A"];
   take <<|a|>>;
   so our thesis by ["C"];
   qed];;

prove <<forall a. p(a) ==> (forall x. p(x) ==> p(f(x)))
                  ==> exists y. p(y) /\ p(f(y))>>
      [fix "c";
       assume ["A",<<p(c)>>];
       assume ["B",<<forall x. p(x) ==> p(f(x))>>];
       take <<|c|>>;
       conclude <<p(c)>> by ["A"];
       note ("C",<<p(c) ==> p(f(c))>>) by ["B"];
       so our thesis by ["C"; "A"];
       qed];;

prove <<p(c) ==> (forall x. p(x) ==> p(f(x)))
                  ==> exists y. p(y) /\ p(f(y))>>
      [assume ["A",<<p(c)>>];
       assume ["B",<<forall x. p(x) ==> p(f(x))>>];
       take <<|c|>>;
       conclude <<p(c)>> by ["A"];
       our thesis by ["A"; "B"];
       qed];;

prove <<forall a. p(a) ==> (forall x. p(x) ==> p(f(x)))
                  ==> exists y. p(y) /\ p(f(y))>>
      [fix "c";
       assume ["A",<<p(c)>>];
       assume ["B",<<forall x. p(x) ==> p(f(x))>>];
       take <<|c|>>;
       conclude <<p(c)>> by ["A"];
       note ("C",<<p(c) ==> p(f(c))>>) by ["B"];
       our thesis by ["C"; "A"];
       qed];;

prove <<forall a. p(a) ==> (forall x. p(x) ==> p(f(x)))
                  ==> exists y. p(y) /\ p(f(y))>>
      [fix "c";
       assume ["A",<<p(c)>>];
       assume ["B",<<forall x. p(x) ==> p(f(x))>>];
       take <<|c|>>;
       note ("D",<<p(c)>>) by ["A"];
       note ("C",<<p(c) ==> p(f(c))>>) by ["B"];
       our thesis by ["C"; "A"; "D"];
       qed];;


prove <<(p(a) \/ p(b)) ==> q ==> exists y. p(y)>>
  [assume ["A",<<p(a) \/ p(b)>>];
   assume ["",<<q>>];
   cases <<p(a) \/ p(b)>> by ["A"];
     take <<|a|>>;
     so our thesis at once;
     qed;

     take <<|b|>>;
     so our thesis at once;
     qed];;

prove
  <<(p(a) \/ p(b)) /\ (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(y))>>
  [assume ["base",<<p(a) \/ p(b)>>;
           "Step",<<forall x. p(x) ==> p(f(x))>>];
   cases <<p(a) \/ p(b)>> by ["base"];
     so note("A",<<p(a)>>) at once;
     note ("X",<<p(a) ==> p(f(a))>>) by ["Step"];
     take <<|a|>>;
     our thesis by ["A"; "X"];
     qed;

     take <<|b|>>;
     so our thesis by ["Step"];
     qed];;

prove
 <<(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(y))>>
  [assume ["A",<<exists x. p(x)>>];
   assume ["B",<<forall x. p(x) ==> p(f(x))>>];
   consider ("a",<<p(a)>>) by ["A"];
   so note ("concl",<<p(f(a))>>) by ["B"];
   take <<|a|>>;
   our thesis by ["concl"];
   qed];;

prove <<(forall x. p(x) ==> q(x)) ==> (forall x. q(x) ==> p(x))
       ==> (p(a) <=> q(a))>>
  [assume ["A",<<forall x. p(x) ==> q(x)>>];
   assume ["B",<<forall x. q(x) ==> p(x)>>];
   note ("von",<<p(a) ==> q(a)>>) by ["A"];
   note ("bis",<<q(a) ==> p(a)>>) by ["B"];
   our thesis by ["von"; "bis"];
   qed];;

(*** Mizar-like

prove
  <<(p(a) \/ p(b)) /\ (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(y))>>
  [assume ["A",<<antecedent>>];
   note ("Step",<<forall x. p(x) ==> p(f(x))>>) by ["A"];
   per_cases by ["A"];
     suppose ("base",<<p(a)>>);
     note ("X",<<p(a) ==> p(f(a))>>) by ["Step"];
     take <<|a|>>;
     our thesis by ["base"; "X"];
     qed;

     suppose ("base",<<p(b)>>);
     our thesis by ["Step"; "base"];
     qed;
   endcase];;

*****)

END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Some amusing efficiency tests versus a "direct" spec.                     *)
(* ------------------------------------------------------------------------- *)

(*****

let test n = gen "x"

let double_th th =
  let tm = concl th in modusponens (modusponens (and_pair tm tm) th) th;;

let testcase n =
  gen "x" (funpow n double_th (lcftaut <<p(x) ==> q(1) \/ p(x)>>));;

let test n = time (spec <<|2|>>) (testcase n),
             time (subst ("x" |=> <<|2|>>)) (concl(testcase n));
             ();;

test 10;;
test 11;;
test 12;;
test 13;;
test 14;;
test 15;;

****)
