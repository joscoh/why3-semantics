Require Export Typing.

From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

(*Default values for fn, sn*)


Definition fn_d : fn :=
  (mk_fn id_fs sn_d tm_d).

Definition pn_d : pn :=
  (mk_pn (Build_predsym id_sym) sn_d Ftrue).

HB.instance Definition _ := hasDecEq.Build funsym funsym_eqb_spec.
HB.instance Definition _ := hasDecEq.Build predsym predsym_eqb_spec.

(*If x is in (map f l), get the y such that In y l and 
  y = f x*)
Fixpoint get_map_elt {A B: Type} (eq_dec: forall (x y: B), {x = y} + {x <> y}) 
  (f: A -> B) (x: B) (l: list A):
  option A :=
  match l with
  | nil => None
  | y :: tl => if eq_dec (f y) x then Some y else get_map_elt eq_dec f x tl
  end.

Lemma get_map_elt_some {A B: Type} (eq_dec: forall (x y: B), {x = y} + {x <> y}) 
  (f: A -> B) (x: B) (l: list A) y:
  get_map_elt eq_dec f x l = Some y ->
  In y l /\ f y = x.
Proof.
  induction l; simpl; try discriminate.
  destruct (eq_dec (f a) x); simpl; subst.
  - intros Hsome; inversion Hsome; subst; auto.
  - intros Hsome. apply IHl in Hsome; destruct_all; auto.
Qed.

Lemma demorgan_or (P Q: Prop):
  ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof.
  tauto.
Qed.

Lemma get_map_elt_none {A B: Type} (eq_dec: forall (x y: B), {x = y} + {x <> y}) 
  (f: A -> B) (x: B) (l: list A) :
  get_map_elt eq_dec f x l = None <-> ~ In x (map f l).
Proof.
  induction l; simpl.
  - split; auto.
  - destruct (eq_dec (f a) x); simpl; subst.
    + split; try discriminate. intros C. exfalso. apply C; auto.
    + rewrite -> IHl, demorgan_or.
      split; intros; destruct_all; auto.
Qed.

(*First, we need a decidable version of
  [decrease_fun] and [decrease_pred], assuming we already
  have fs and ps*)
Fixpoint check_decrease_fun (fs: list fn) (ps: list pn)
  (small: list vsymbol) (hd: option vsymbol) (m: mut_adt)
  (vs: list vty) (t: term) : bool :=
  match t with
  | Tfun f l ts =>
    match (get_map_elt funsym_eq_dec fn_sym f fs) with
    | Some f_decl =>
         match nth tm_d ts (sn_idx f_decl) with
        | Tvar x => 
          (x \in small) &&
          (l == map vty_var (s_params f)) &&
          all (check_decrease_fun fs ps small hd m vs) ts
        | _ => false
        end 
    | None => (*Not recursive*)
      all (check_decrease_fun fs ps small hd m vs) ts
    end
      
  (*Other hard cases - pattern matches*)
  | Tmatch tm v pats =>
    check_decrease_fun fs ps small hd m vs tm &&
    match tm with
    | Tvar mvar =>
        if check_var_case hd small mvar then
          all (fun x =>
          check_decrease_fun fs ps
          (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x))) 
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
          small)) (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)
          ) pats
        (*Non-smaller cases - TODO: less repetition?*)
        else 
          all (fun x =>
            check_decrease_fun fs ps 
            (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
            (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats
    | Tfun c l tms =>
        all (fun x => check_decrease_fun fs ps
          (union vsymbol_eq_dec
            (vsyms_in_m m vs (get_constr_smaller small hd m vs c l tms x.1))
            (remove_all vsymbol_eq_dec (pat_fv x.1) small))
          (upd_option_iter hd (pat_fv x.1)) m vs x.2) pats
    | _ => all (fun x =>
      check_decrease_fun fs ps 
      (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats
    end
  | Tlet t1 v t2 =>
    check_decrease_fun fs ps small hd m vs t1 &&
    check_decrease_fun fs ps (remove vsymbol_eq_dec v small) (upd_option hd v) m vs t2
  | Tif f1 t1 t2 =>
    check_decrease_pred fs ps small hd m vs f1 &&
    check_decrease_fun fs ps small hd m vs t1 &&
    check_decrease_fun fs ps small hd m vs t2
  | Teps f v =>
    check_decrease_pred fs ps (remove vsymbol_eq_dec v small) (upd_option hd v) m vs f
  | _ => true
  end

with check_decrease_pred (fs: list fn) (ps: list pn)
  (small: list vsymbol) (hd: option vsymbol) (m: mut_adt)
  (vs: list vty) (f: formula) : bool :=
  (*Don't use any recursive instance*)
  (* (all (fun f' => negb (funsym_in_fmla (fn_sym f') f)) fs &&
  all (fun p => negb (predsym_in_fmla (pn_sym p) f)) ps) || *)
  match f with
  | Fpred p l ts =>
    match (get_map_elt predsym_eq_dec pn_sym p ps) with
    | Some p_decl =>
         match nth tm_d ts (sn_idx p_decl) with
        | Tvar x => 
          (x \in small) &&
          (l == map vty_var (s_params p)) &&
          all (check_decrease_fun fs ps small hd m vs) ts
        | _ => false
        end 
    | None => (*Not recursive*)
      all (check_decrease_fun fs ps small hd m vs) ts
    end
   (*Other hard cases - pattern matches*)
   | Fmatch tm v pats =>
    check_decrease_fun fs ps small hd m vs tm &&
    match tm with
    | Tvar mvar =>
        if check_var_case hd small mvar then
          all (fun x =>
          check_decrease_pred fs ps
          (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x))) 
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
          small)) (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)
          ) pats
        else 
          all (fun x =>
            check_decrease_pred fs ps 
            (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
            (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats
    | Tfun c l tms =>
        all (fun x => check_decrease_pred fs ps
          (union vsymbol_eq_dec
            (vsyms_in_m m vs (get_constr_smaller small hd m vs c l tms x.1))
            (remove_all vsymbol_eq_dec (pat_fv x.1) small))
          (upd_option_iter hd (pat_fv x.1)) m vs x.2) pats
    | _ => all (fun x =>
      check_decrease_pred fs ps 
      (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats
    end
  | Fnot f =>
    check_decrease_pred fs ps small hd m vs f 
  | Fquant q v f =>
    check_decrease_pred fs ps (remove vsymbol_eq_dec v small) (upd_option hd v) m vs f
  | Feq ty t1 t2 =>
    check_decrease_fun fs ps small hd m vs t1 &&
    check_decrease_fun fs ps small hd m vs t2
  | Fbinop b f1 f2 =>
    check_decrease_pred fs ps small hd m vs f1 &&
    check_decrease_pred fs ps small hd m vs f2
  | Flet t1 v f =>
    check_decrease_fun fs ps small hd m vs t1 &&
    check_decrease_pred fs ps (remove vsymbol_eq_dec v small) (upd_option hd v) m vs f
  | Fif f1 f2 f3 =>
    check_decrease_pred fs ps small hd m vs f1 &&
    check_decrease_pred fs ps small hd m vs f2 &&
    check_decrease_pred fs ps small hd m vs f3
  | _ => true
  end.

Ltac reflT := apply ReflectT; constructor.

Lemma nth_eq {A: Type} (n: nat) (s: seq A) (d: A):
  List.nth n s d = nth d s n.
Proof.
  move: n. elim:s=>[// [|]// | h t /= IH [// | n' /=]].
  by apply IH.
Qed.

Ltac reflF := let C := fresh "C" in apply ReflectF => C; inversion C; subst.

Lemma inP: forall {A: eqType} (x: A) (l: seq A),
  reflect (In x l) (x \in l).
Proof.
  move=> A x l. elim: l => [//= | h t /= IH].
  - by apply ReflectF.
  - rewrite in_cons. apply orPP => //.
    rewrite eq_sym. apply eqP.
Qed.

(*Some tactics to help*)
(*TODO: use elsewhere*)
Ltac nodup_inj :=
  match goal with
  | H: ?f ?x = ?f ?y, Hn1: NoDup (List.map ?f ?l) |- _ => assert (x = y) by
    (apply (NoDup_map_in Hn1); assumption);
    subst y; clear H
  end.

Ltac all_inj :=
  repeat match goal with
  | H : ?f ?x = ?f ?y |- _ =>
    tryif progress(injection H) then intros; subst; clear H else fail
  end.

Ltac in_map_contra :=
  match goal with
  | H: In ?x ?l, H1: ~ In (?f ?x) (List.map ?f ?l) |- _ =>
    exfalso; apply H1; rewrite in_map_iff; exists x; auto
  end.

(*For the trivial cases of Tfun*)
Ltac tfun_triv t :=
  reflF; [nodup_inj; generalize dependent t;
        intros; subst; try discriminate;
        try solve[all_inj; contradiction] | in_map_contra].

(*Destruct things we need for reflection*)
Ltac refl_destruct :=
  match goal with
    (*| |- context [funsym_eqb ?f1 ?f2] => destruct (funsym_eqb_spec f1 f2); subst
    | |- context [predsym_eqb ?f1 ?f2] => destruct (predsym_eqb_spec f1 f2); subst*)
    | |- context [?x \in ?l] => case: (inP x l); intros
    | |- context [?x == ?l] => case: (@eqP _ x l); intros
    | |- context [check_var_case ?hd ?small ?v] => destruct (check_var_case_spec hd small v); intros
    | H: forall (small : list vsymbol) (hd: option vsymbol),
      reflect (?P _ _ small hd _ _ ?t)
        (?b _ _ small hd _ _ ?t) |-
      context [?b _ _ ?s1 ?h1 _ _ ?t] => 
      destruct (H s1 h1)
  end.

Local Lemma ForallT_reflect {A: Type} {l: list A} {B C: Type}
        {P: B -> C -> A -> Prop} {p: B -> C -> A -> bool}
        (Hall: ForallT (fun a => forall b c, reflect (P b c a) (p b c a)) l):
        forall b c,
        reflect (forall x, In x l -> P b c x) (all (p b c) l).
Proof.
  intros. induction l; simpl.
  - apply ReflectT. intros; contradiction.
  - destruct (ForallT_hd _ _ _ Hall b c).
    2: { apply ReflectF; intro Con. specialize (Con a). auto. }
    simpl. destruct (IHl (ForallT_tl _ _ _ Hall)); simpl;
    [apply ReflectT | apply ReflectF]; auto.
    intros; destruct_all; subst; auto.
Qed.

Lemma all_eta {A: Type} (b: A -> bool) (l: list A) :
  all (fun x => b x) l = all b l.
Proof.
  reflexivity.
Qed.

Ltac refl_destruct_full :=
  first[ match goal with
  | H: ForallT (fun (t: term) => forall (small : list vsymbol) (hd : option vsymbol), 
          reflect (?P1 _ _ small hd _ _ t)
          (?b1 _ _ small hd _ _ t)) ?tms |-
        context [reflect ?P (all (?b1 _ _ ?s1 ?h1 _ _) ?tms)] =>
        let A := fresh in
        pose proof (A:=ForallT_reflect H);
        rewrite <- all_eta;
        destruct (A s1 h1)
  end
| refl_destruct ].

Ltac Forall_forall_all :=
  repeat match goal with
  | H: Forall ?P ?l |- _ => rewrite Forall_forall in H
  | |- Forall ?P ?l => rewrite Forall_forall
  end.

Local Lemma ForallT_reflect' {A D: Type} {l: list (D * A)} {B C: Type}
        {P: B -> C -> A -> Prop} {p: B -> C -> A -> bool}
        (Hall: ForallT (fun a => forall b c, reflect (P b c a) (p b c a)) (List.map snd l)):
        forall b c,
        reflect (forall x, In x l -> P (b x) (c x) (snd x)) (all (fun x => p (b x) (c x) (snd x)) l).
Proof.
  intros. induction l; simpl.
  - apply ReflectT. intros; contradiction.
  - destruct (ForallT_hd _ _ _ Hall (b a) (c a)) as [Ha | Ha]; simpl.
    2: { apply ReflectF. intro Hnot; apply Ha; auto. }
    specialize (IHl (ForallT_tl _ _ _ Hall)). destruct IHl;
    [apply ReflectT | apply ReflectF]; auto.
    intros x [Hax | Hinx]; subst; auto.
Qed.

Ltac match_case small hd Halliff constr :=
  let Hall2 := fresh in
  case: (Halliff (fun x => remove_all vsymbol_eq_dec (pat_fv x.1) small) 
        (fun x => upd_option_iter hd (pat_fv x.1))) => Hall2;
          [ apply ReflectT, constr | reflF].

Lemma check_decrease_spec fs ps m vs (Hn1: NoDup (List.map fn_sym fs))
  (Hn2: NoDup (List.map pn_sym ps)) (t: term) (f: formula):
  (forall small hd,
    reflect (decrease_fun fs ps small hd m vs t)
      (check_decrease_fun fs ps small hd m vs t)) *
    (forall small hd,
      reflect (decrease_pred fs ps small hd m vs f)
        (check_decrease_pred fs ps small hd m vs f)).
Proof.
  revert t f. apply term_formula_rect; simpl; try solve[intros; reflT];
  (*Solve all non-nested cases*)
  try solve[intros; repeat (refl_destruct; try solve[reflF; contradiction]; try solve[reflT; auto])].
  - (*Tfun*) 
    intros f1 tys tms Hall small hd.
    destruct (get_map_elt funsym_eq_dec fn_sym f1 fs) as [f_decl |]  eqn : Helt.
    + apply get_map_elt_some in Helt.
      rewrite <- nth_eq.
      destruct Helt as [Hinfs Hf1]; subst.
      destruct (List.nth (sn_idx f_decl) tms tm_d) eqn : Hnth;
      try solve[tfun_triv (List.nth (sn_idx f_decl) tms tm_d)].
      (*Only var case is interesting*)
      refl_destruct; [| tfun_triv (List.nth (sn_idx f_decl) tms tm_d)].
      refl_destruct; [| tfun_triv (List.nth (sn_idx f_decl) tms tm_d)].  simpl.
      refl_destruct_full.
      * apply ReflectT. apply Dec_fun_in with (x:=v)(f_decl:=f_decl); auto.
        rewrite Forall_forall; auto.
      * tfun_triv (List.nth (sn_idx f_decl) tms tm_d). Forall_forall_all. auto.
    + apply get_map_elt_none in Helt. refl_destruct_full.
      * reflT; auto.
      * reflF; Forall_forall_all; auto.
  - (*Tmatch*) 
    intros tm ty pats Htm Hps small hd.
    pose proof (ForallT_reflect' Hps) as Halliff.
    destruct (Htm small hd) as [Htm' | Htm'].
    2: { reflF; auto; apply Htm'; constructor. }
    simpl. destruct tm as [| v | f tys tms | | | | ]; try solve[ match_case small hd Halliff Dec_tmatch_rec; auto].
    + (*Tvar*)
      refl_destruct; [|match_case small hd Halliff Dec_tmatch_rec; auto].
      destruct (Halliff (fun x => (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs x.1))
           (remove_all vsymbol_eq_dec (pat_fv x.1) small)))
        (fun x => (upd_option_iter hd (pat_fv x.1))));
      [apply ReflectT, Dec_tmatch | reflF]; solve[auto].
    + (*Tconstr*)
      destruct (Halliff (fun x => (union vsymbol_eq_dec (vsyms_in_m m vs (get_constr_smaller small hd m vs f tys tms x.1))
           (remove_all vsymbol_eq_dec (pat_fv x.1) small)))
        (fun x => (upd_option_iter hd (pat_fv x.1))));
      [apply ReflectT, Dec_tmatch_constr | reflF]; solve[auto].
  - (*Fpred - very similar*)
    intros p1 tys tms Hall small hd.
    destruct (get_map_elt predsym_eq_dec pn_sym p1 ps) as [p_decl |]  eqn : Helt.
    + apply get_map_elt_some in Helt.
      rewrite <- nth_eq.
      destruct Helt as [Hinps Hp1]; subst.
      destruct (List.nth (sn_idx p_decl) tms tm_d) eqn : Hnth;
      try solve[tfun_triv (List.nth (sn_idx p_decl) tms tm_d)].
      refl_destruct; [| tfun_triv (List.nth (sn_idx p_decl) tms tm_d)].
      refl_destruct; [| tfun_triv (List.nth (sn_idx p_decl) tms tm_d)].  simpl.
      refl_destruct_full.
      * apply ReflectT. apply Dec_pred_in with (x:=v)(p_decl:=p_decl); auto.
        rewrite Forall_forall; auto.
      * tfun_triv (List.nth (sn_idx p_decl) tms tm_d). Forall_forall_all. auto.
    + apply get_map_elt_none in Helt. refl_destruct_full.
      * reflT; auto.
      * reflF; Forall_forall_all; auto.
  - (*Fmatch*)
    intros tm ty pats Htm Hps small hd.
    pose proof (ForallT_reflect' Hps) as Halliff.
    destruct (Htm small hd) as [Htm' | Htm'].
    2: { reflF; auto; apply Htm'; constructor. }
    simpl. destruct tm as [| v | f tys tms | | | | ]; try solve[ match_case small hd Halliff Dec_fmatch_rec; auto].
    + (*Tvar*)
      refl_destruct; [|match_case small hd Halliff Dec_fmatch_rec; auto].
      destruct (Halliff (fun x => (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs x.1))
           (remove_all vsymbol_eq_dec (pat_fv x.1) small)))
        (fun x => (upd_option_iter hd (pat_fv x.1))));
      [apply ReflectT, Dec_fmatch | reflF]; solve[auto].
    + (*Tconstr*)
      destruct (Halliff (fun x => (union vsymbol_eq_dec (vsyms_in_m m vs (get_constr_smaller small hd m vs f tys tms x.1))
           (remove_all vsymbol_eq_dec (pat_fv x.1) small)))
        (fun x => (upd_option_iter hd (pat_fv x.1))));
      [apply ReflectT, Dec_fmatch_constr | reflF]; solve[auto].
Qed.

Definition check_decrease_fun_spec fs ps m vs (t: term) small hd
  (Hn1: NoDup (map fn_sym fs))
  (Hn2: NoDup (map pn_sym ps)):=
  (fst (check_decrease_spec fs ps m vs Hn1 Hn2 t Ftrue)) small hd.

Definition check_decrease_pred_spec fs ps m vs (f: formula) small hd
  (Hn1: NoDup (map fn_sym fs))
  (Hn2: NoDup (map pn_sym ps)):=
  (snd (check_decrease_spec fs ps m vs Hn1 Hn2 tm_d f)) small hd.

(*Part 2: Finding the indices*)
Section TermCheck.
Context {gamma: context} (gamma_valid: valid_context gamma).

(*The main part remaining is finding the indices. We use a somewhat naive
  approach, looking at all possibilities (Coq does similar, it
  seems unlikely to be able to do significantly better).
  As an optimization, we only consider the possible indices for 
  a given ADT. Since each ADT is unlikely to be used more than once
  or twice per function, this should be pretty fast in practice*)

(*Naively, find all mutual ADTs and arguments present among
  the vsymbol list*)
Definition get_adts_present (l: list (list vsymbol)) : list (mut_adt * list vty) :=
  fold_right (fun v acc => match (is_vty_adt gamma (snd v)) with
                            | Some (m, a, vs) => union (tuple_eq_dec mut_adt_dec (list_eq_dec vty_eq_dec))
                                [(m, vs)] acc
                            | None => acc
                            end) nil (concat l).

(*Generate the candidate index lists: for a given ADT, consists
  of all of the possible indices for each funsym/predsym*)
Definition get_idx_lists_aux 
  (mutfun: list (funsym * list vsymbol * term))
  (mutpred: list (predsym * list vsymbol * formula)) :
  list (mut_adt * list vty * (list (list nat))) :=

  let vsyms := (map (fun x => snd (fst x)) mutfun ++
      map (fun x => snd (fst x)) mutpred) in

  map (fun x =>
    let '(m, vs) := x in

    (*Build list for this mut_adt*)

    (*1.funsyms*)
    let l : list (list nat) :=
      map (fun args =>
        map fst ((filter (fun it =>
          vty_in_m m vs (snd it)
        ))
        (combine (iota 0 (length args)) (map snd args)))
      
      ) vsyms 
      
      in
      (*If any are null, discard*)
      let l2 := if List.existsb null l then nil else l in

      (m, vs, l2))

  (get_adts_present vsyms).

Definition get_idx_lists 
  (mutfun: list (funsym * list vsymbol * term))
  (mutpred: list (predsym * list vsymbol * formula)) :
  list (mut_adt * list vty * (list (list nat))) :=

  (*Filter out non-null lists*)
  filter (fun x => negb (null (snd x))) (get_idx_lists_aux mutfun mutpred).

(*Transform a candidate list into a list of candidates*)
(*The input list of lists has length |fun| + |pred|
  and ith element includes all possible candidate indices 
  for fun/pred i.
  Output instead is a list of lists, each of length |fun| + |pred|
  where each lists give one possible complete set of indices*)
Fixpoint get_possible_index_lists (l: list (list nat)) : list (list nat) :=
  match l with
  | l1 :: rest =>
    let rec := get_possible_index_lists rest in
    concat (List.map (fun x => List.map (fun y => x :: y) rec) l1)
  | nil => [nil]
  end.

  (*TODO: move*)

(*A version of find that finds the (first) element satisfying a predicate*)
(*TODO: combine*)
Definition find_elt_pred {A: Type} (f: A -> bool) (l: list A) :
  option A :=
  fold_right (fun x acc => if f x then Some x else acc) None l.

Lemma find_elt_pred_some {A: Type} (f: A -> bool) (l: list A) x :
  find_elt_pred f l = Some x ->
  In x l /\ f x.
Proof.
  induction l as [| h t IH]; simpl; try discriminate.
  destruct (f h) eqn : Hf.
  - intros. all_inj. auto.
  - intros Hsome. apply IH in Hsome; destruct_all; auto.
Qed.

Lemma find_elt_pred_none {A: Type} (f: A -> bool) (l: list A):
  find_elt_pred f l = None <-> forall x, In x l -> f x = false.
Proof.
  induction l as [| h t IH]; simpl.
  - split; intros; auto; contradiction.
  - destruct (f h) eqn : Hfh.
    + split; intros Hall; auto; try discriminate.
      rewrite Hall in Hfh; auto; discriminate.
    + rewrite IH. split; intros; destruct_all; auto.
Qed.


  (*Now, a version of [find] that returns the element: given
  a function that evaluates to Some x (success) or None (failure),
  return the first success*)
Definition find_elt {A B: Type} (f: A -> option B) (l: list A) :
  option (A * B) :=
  fold_right (fun x acc => match f x with | None => acc | Some y => Some (x, y) end)
  None l.

Lemma find_elt_some {A B : eqType} (f: A -> option B) (l: list A) x y:
  find_elt f l = Some (x, y) ->
  x \in l /\ f x = Some y.
Proof.
  elim: l =>[//| h t /= Ih].
  case Hh: (f h)=>[a |].
  - move=> [Hax] hay; subst. by rewrite mem_head.
  - move=> Hfind. apply Ih in Hfind.
    case: Hfind => Hinxt Hfx.
    by rewrite in_cons Hinxt orbT.
Qed.

Lemma find_elt_none {A B : eqType} (f: A -> option B) (l: list A):
  reflect (forall y, y \in l -> f y = None)
    (find_elt f l == None).
Proof.
  elim: l => [//= | h t /= IH].
  - by apply ReflectT.
  - case Hh: (f h) => [a |].
    + apply ReflectF. move=> C. 
      rewrite C in Hh=>//. by rewrite mem_head.
    + eapply equivP. apply IH.
      split; move=> Hall y.
      * rewrite in_cons => /orP[/eqP Hhy | Hint]; subst=>//.
        by apply Hall.
      * move=> Hint. apply Hall. by rewrite in_cons Hint orbT.
Qed. 


Definition make_fn (f: funsym) (args: list vsymbol) (t: term) (i: nat) :=
  mk_fn f (mk_sn f args i) t.
Definition make_pn (p: predsym) (args: list vsymbol) (f: formula) (i: nat) :=
  mk_pn p (mk_sn p args i) f.

(*For a given mutual ADT, args, and set of index lists, find
  an index list that works, if any*)
Definition find_idx_list l
  (*(mutfun: list (funsym * list vsymbol * term))
  (mutpred: list (predsym * list vsymbol * formula))*) m vs
  (candidates : list (list nat))
  (*NOTE: candidates preprocessed by get_possible_index_lists*) : 
  option (list nat) :=

  find_elt_pred (fun il =>
    all (fun (f : fn) => check_decrease_fun  
      (funpred_defs_to_sns l il).1 
      (funpred_defs_to_sns l il).2 [::] 
      (Some (List.nth (sn_idx f) (sn_args f) vs_d)) m vs (fn_body f))
      (funpred_defs_to_sns l il).1 &&
    all (fun (p : pn) => check_decrease_pred
      (funpred_defs_to_sns l il).1 
      (funpred_defs_to_sns l il).2 [::] 
      (Some (List.nth (sn_idx p) (sn_args p) vs_d)) m vs (pn_body p))
      (funpred_defs_to_sns l il).2) candidates.
    (* )



    let fs := List.map (fun x =>
      fundef_to_fn x.1.1.1 x.1.1.2 x.1.2 x.2) 
      (combine mutfun (firstn (length mutfun) il)) in

    let ps := List.map (fun x =>
      preddef_to_pn x.1.1.1 x.1.1.2 x.1.2 x.2) 
      (combine mutpred (skipn (length mutfun) il)) in

    all (fun x =>
        let i := fst x in
        let f : fn := snd x in
        check_decrease_fun fs ps nil
        (Some (List.nth i (sn_args f) vs_d)) m vs (fn_body f))
        (combine (firstn (length fs) il) fs) &&
      all (fun x =>
        let i := fst x in
        let p : pn := snd x in
        check_decrease_pred fs ps nil
        (Some (List.nth i (sn_args p) vs_d)) m vs (pn_body p))
        (combine (skipn (length fs) il) ps)
  ) candidates.

 (Forall (fun f : fn => decrease_fun (funpred_defs_to_sns l il).1 
    (funpred_defs_to_sns l il).2 [::] 
    (Some (List.nth (sn_idx f) (sn_args f) vs_d)) m vs (fn_body f)) 
  (funpred_defs_to_sns l il).1) *)



(*We also need to check the params. This is easy; we do it generically*)

(*Given a list of A's and a function A -> B, return Some x 
  iff f y = x for all y in l*)
Definition find_eq {A B: eqType} (f: A -> B) (l: list A) : option B :=
  match l with
  | nil => None
  | x :: tl => 
    (*x is our candidate*)
    if all (fun y => f y == f x) l then Some (f x) else None
    end.

(*TODO: move*)
Lemma find_eq_spec {A B: eqType} (f: A -> B) (l: list A) (b: B):
  reflect (l <> nil /\ forall x, x \in l -> f x = b)
  (find_eq f l == Some b).
Proof.
  rewrite /find_eq.
  case: l => [//= | h t /=].
  - by apply ReflectF => [] [].
  - rewrite eq_refl/=.
    case: (all (fun y : A => f y == f h) t) /allP => [ Hall| Hnotall].
    + case: (Some (f h) == Some b) /eqP => [[Hhb] | Hneq]; subst.
      * apply ReflectT.  split=>//. move=> x.
        rewrite in_cons => /orP[/eqP Hxh | Hint]; subst=>//.
        by apply /eqP; apply Hall.
      * apply ReflectF.
        move=> [_ Hall2].
        rewrite Hall2 in Hneq=>//.
        by rewrite mem_head.
    + apply ReflectF.
      move=> [_ Hall].
      apply Hnotall. move=> x Hinx. rewrite !Hall //.
      by rewrite mem_head.
      by rewrite in_cons Hinx orbT.
Qed. 

(* Definition option_map2 {A B C: Type} (f: A -> B -> C) (o1: option A) (o2: option B) : option C :=
  match o1, o2 with
  | Some x1, Some x2 => Some (f x1 x2)
  | _, _ => None
  end. *)

Definition mut_adt_eqb (m1 m2: mut_adt) : bool :=
  mut_adt_dec m1 m2.

Lemma mut_adt_eqb_spec (m1 m2: mut_adt) :
  reflect (m1 = m2) (mut_adt_eqb m1 m2).
Proof.
  unfold mut_adt_eqb. destruct (mut_adt_dec m1 m2); subst; simpl;
  [apply ReflectT | apply ReflectF]; auto.
Qed.

HB.instance Definition _ := hasDecEq.Build fpsym fpsym_eqb_spec.
HB.instance Definition _ := hasDecEq.Build mut_adt mut_adt_eqb_spec.
(*And now the full function to check termination*)
Check obind.

Definition check_termination (l: list funpred_def) :
  option (mut_adt * list typevar * list vty * list nat) :=
    if null l then None else
    let t := split_funpred_defs l in
    let syms := (List.map (fun x => f_sym x.1.1) t.1) ++
      (List.map (fun x => p_sym x.1.1) t.2) in

    (*First, find params*)
    obind (fun params => 
       (*Look through all candidates, find one*)
      obind (fun y => 
        let '(m, vs, _, idxs) := y in
        
          Some (m, params, vs, idxs) 
      ) (find_elt (fun x =>
        let '(m, vs, cands) := x in
         (*Some of these might be implied by typing but we check them anyway for proofs*)
         if ((length vs =? length (m_params m))%nat &&
          mut_in_ctx m gamma) then
        find_idx_list l (*t.1 t.2*) m vs (get_possible_index_lists cands)
        else None)
        (get_idx_lists t.1 t.2))
    
    ) (find_eq (fun x => s_params x) syms).
    (* match find_eq (fun x => s_params x) syms with
    | None => None
    | Some params =>
      (*Look through all candidates, find one*)
      match (find_elt (fun x =>
        let '(m, vs, cands) := x in
        find_idx_list t.1 t.2 m vs cands)
        (get_idx_lists t.1 t.2)) with
      | Some (m, vs, _, idxs) =>
         (*Some of these might be implied by typing but we check them anyway for proofs*)
        if ((length vs =? length (m_params m))%nat &&
          mut_in_ctx m gamma) then
          Some (m, params, vs, idxs) else None
      | None => None
      end
    end. *)


    

(*And now we have to prove correctness*)

(*TODO: move*)
Lemma nullP {A: Type} (s: seq A):
  reflect (s = nil) (null s).
Proof.
  case: s=>/= [| h t].
  apply ReflectT=>//.
  by apply ReflectF.
Qed.

HB.instance Definition _ := hasDecEq.Build fn fn_eqb_spec.
HB.instance Definition _ := hasDecEq.Build pn pn_eqb_spec.

Lemma size_length {A: Type} (l: list A):
  size l = length l.
Proof.
  by [].
Qed.

(*Very annoying lemmas but this is better than having to
  prove these things twice. We need this result for each of the next
  two*)
(* Lemma find_idx_list_all_equuiv1 l m vs il
  (Hl: In l (mutfuns_of_context gamma))
  (Hlen: length l = length il):
  let fs := List.map (fun x =>
      fundef_to_fn x.1.1.1 x.1.1.2 x.1.2 x.2) 
      (combine (split_funpred_defs l).1 (firstn (length (split_funpred_defs l).1) il)) in
  let ps := List.map (fun x =>
      preddef_to_pn x.1.1.1 x.1.1.2 x.1.2 x.2) 
      (combine (split_funpred_defs l).2 (skipn (length (split_funpred_defs l).1) il)) in
  reflect 
  (Forall (fun f : fn => decrease_fun (funpred_defs_to_sns l il).1 
    (funpred_defs_to_sns l il).2 [::] 
    (Some (List.nth (sn_idx f) (sn_args f) vs_d)) m vs (fn_body f)) 
  (funpred_defs_to_sns l il).1)
  (all (fun x =>
        let i := fst x in
        let f : fn := snd x in
        check_decrease_fun fs ps nil
        (Some (List.nth i (sn_args f) vs_d)) m vs (fn_body f))
        (combine (firstn (length fs) il) fs)) *
  reflect 
  ( Forall (fun p : pn => decrease_pred (funpred_defs_to_sns l il).1 
    (funpred_defs_to_sns l il).2 [::] 
    (Some (List.nth (sn_idx p) (sn_args p) vs_d)) m vs (pn_body p)) 
  (funpred_defs_to_sns l il).2)
  (all (fun x =>
        let i := fst x in
        let p : pn := snd x in
        check_decrease_pred fs ps nil
        (Some (List.nth i (sn_args p) vs_d)) m vs (pn_body p))
        (combine (skipn (length fs) il) ps)).
Proof.
  set (t:=(split_funpred_defs l)) . 
  (*Some useful facts about lengths*)
  have Htlen := split_funpred_defs_length l.
  have Hsztake: length (firstn (length t.1) il) = length t.1 by
    rewrite firstn_length; apply min_l; unfold t; lia.
  have Hszcomb1: length (combine t.1 (firstn (length t.1) il)) = length t.1
    by rewrite combine_length Hsztake Nat.min_id.
  have Hszskip: length (skipn (length t.1) il) = length t.2 by
    rewrite skipn_length /t; lia.
  have Hszcomb2: length (combine t.2 (skipn (length t.1) il)) = length t.2 
    by rewrite combine_length Hszskip Nat.min_id.
  move=> fs ps.
  (*Prove each individually*)
  split.
  - Search reflect Forall all.



let fs := List.map (fun x =>
      fundef_to_fn x.1.1.1 x.1.1.2 x.1.2 x.2) 
      (combine mutfun (firstn (length mutfun) il)) in

    let ps := List.map (fun x =>
      preddef_to_pn x.1.1.1 x.1.1.2 x.1.2 x.2) 
      (combine mutpred (skipn (length mutfun) il)) in

    all (fun x =>
        let i := fst x in
        let f : fn := snd x in
        check_decrease_fun fs ps nil
        (Some (List.nth i (sn_args f) vs_d)) m vs (fn_body f))
        (combine (firstn (length fs) il) fs) &&
      all (fun x =>
        let i := fst x in
        let p : pn := snd x in
        check_decrease_pred fs ps nil
        (Some (List.nth i (sn_args p) vs_d)) m vs (pn_body p))
        (combine (skipn (length fs) il) ps)


  Forall (fun f : fn => decrease_fun (funpred_defs_to_sns l il).1 
    (funpred_defs_to_sns l il).2 [::] 
    (Some (List.nth (sn_idx f) (sn_args f) vs_d)) m vs (fn_body f)) 
  (funpred_defs_to_sns l il).1 *)

Lemma forallb_ForallP {A: Type} (P: A -> Prop) (p: pred A) (s: seq A):
  (forall x, In x s -> reflect (P x ) (p x)) ->
  reflect (Forall P s) (all p s).
Proof.
  elim: s =>[//= Hall | h t /= IH Hall].
  - apply ReflectT. constructor.
  - case: (p h) /(Hall h (or_introl _)) => //= Hh; last by reflF.
    have IHt: (forall x : A, In x t -> reflect (P x) (p x)) by
      move=> x Hinx; apply Hall; right.
    move: IH => /(_ IHt) IH.
    case: (all p t) /IH => Ht/=; last by reflF.
    apply ReflectT. by constructor.
Qed. 

Lemma find_idx_list_some_cands l m vs candidates il:
  find_idx_list l
    m vs candidates = Some il ->
  In il candidates.
Proof.
  rewrite /find_idx_list.
  set (t:=(split_funpred_defs l)).
  move=> Hfind. apply find_elt_pred_some in Hfind. apply Hfind.
Qed. 

Lemma find_idx_list_some l m vs candidates il
  (Hlen: length l = length il)
  (Hl: In l (mutfuns_of_context gamma)):
  find_idx_list l
    m vs candidates = Some il ->
  Forall (fun f : fn => decrease_fun (funpred_defs_to_sns l il).1 
    (funpred_defs_to_sns l il).2 [::] 
    (Some (List.nth (sn_idx f) (sn_args f) vs_d)) m vs (fn_body f)) 
  (funpred_defs_to_sns l il).1 /\
  Forall (fun p : pn => decrease_pred (funpred_defs_to_sns l il).1 
    (funpred_defs_to_sns l il).2 [::] 
    (Some (List.nth (sn_idx p) (sn_args p) vs_d)) m vs (pn_body p)) 
  (funpred_defs_to_sns l il).2.
Proof.
  rewrite /find_idx_list.
  set (t:=(split_funpred_defs l)).
  move=> Hfind. apply find_elt_pred_some in Hfind. move: Hfind.
  move=> [] Hinil /andP[Hfun Hpred].
  split_all=>//.
  - apply /forallb_ForallP; last by apply Hfun.
    move=> f Hinf. by apply check_decrease_fun_spec;
    apply (funpred_defs_to_sns_NoDup (valid_context_wf _ gamma_valid)).
  - apply /forallb_ForallP; last by apply Hpred.
    move=> f Hinf. by apply check_decrease_pred_spec;
    apply (funpred_defs_to_sns_NoDup (valid_context_wf _ gamma_valid)).
Qed.


(* 


  (*Some useful facts about lengths*)
  have Htlen := split_funpred_defs_length l.
  have Hsztake: length (firstn (length t.1) il) = length t.1 by
    rewrite firstn_length; apply min_l; unfold t; lia.
  have Hszcomb1: length (combine t.1 (firstn (length t.1) il)) = length t.1
    by rewrite combine_length Hsztake Nat.min_id.
  have Hszskip: length (skipn (length t.1) il) = length t.2 by
    rewrite skipn_length /t; lia.
  have Hszcomb2: length (combine t.2 (skipn (length t.1) il)) = length t.2 
    by rewrite combine_length Hszskip Nat.min_id.
  split_all =>//.
  - rewrite {Hpred} Forall_forall => f.
    rewrite funpred_defs_to_sns_in_fst //.
    move=> [i [Hi Hf]].
    move: Hfun => /(_ ((List.nth i il 0), f)) => Hfun.
    apply /check_decrease_fun_spec; try by 
      apply (funpred_defs_to_sns_NoDup (valid_context_wf _ gamma_valid)).
    (*Main part is proving the "in" hypothesis*)
    prove_hyp Hfun.
    {
      rewrite !map_length.
      apply /inP. rewrite Hszcomb1 in_combine_iff; last
        by rewrite !map_length Hsztake Hszcomb1.
      exists i. rewrite Hsztake.
      split=>//.
      move=> d1 d2.
      rewrite !firstn_nth //.
      rewrite -> map_nth_inbound with (d2:=(id_fs, nil, tm_d, 0));
        last by rewrite Hszcomb1.
      rewrite !combine_nth // firstn_nth //.
      simpl in *; f_equal =>//. by apply nth_indep; lia.
    }
    (*The result is easy*)
    have Hidx: (List.nth i il 0) = (sn_idx f) by rewrite /= in Hf; subst.
    by rewrite Hidx in Hfun.
  - (*Very similar*)
    rewrite {Hfun} Forall_forall => f.
    rewrite funpred_defs_to_sns_in_snd //.
    move=> [i [Hi Hf]].
    move: Hpred => /(_ ((List.nth (length t.1 + i)%coq_nat il 0), f)) => Hpred.
    apply /check_decrease_pred_spec; try by 
      apply (funpred_defs_to_sns_NoDup (valid_context_wf _ gamma_valid)).
    (*Main part is proving the "in" hypothesis*)
    prove_hyp Hpred.
    {
      rewrite !map_length.
      apply /inP.
      rewrite combine_length Hsztake Nat.min_id in_combine_iff; last 
        by rewrite !map_length Hszcomb2.
      exists i. rewrite Hszskip. split=>//.
      move=> /=d1 d2.
      rewrite skipn_nth.
      rewrite -> map_nth_inbound with (d2:=(id_ps, nil, Ftrue, 0)); last
        by rewrite Hszcomb2.
      rewrite !combine_nth // !skipn_nth.
      f_equal =>//. apply nth_indep. unfold t. lia.
      simpl in Hf; subst. rewrite !map_length /t.
      unfold preddef_to_pn. f_equal. f_equal.  simpl.
      by rewrite Hszcomb1.
    }
    have Hidx: (List.nth (length t.1 + i)%coq_nat il 0) = (sn_idx f) by
      rewrite /= in Hf; subst; rewrite map_length Hszcomb1.
    by rewrite Hidx in Hpred.
Qed. *)

(*And the none case*)
Lemma find_idx_list_none l m vs candidates
  (Hl: In l (mutfuns_of_context gamma))
  (Hcand: forall il, In il candidates -> length l = length il):
  find_idx_list l
    m vs candidates = None -> (*really iff but we only need 1*)
  forall il, In il candidates ->
  ~ 
  (Forall (fun f : fn => decrease_fun (funpred_defs_to_sns l il).1 
    (funpred_defs_to_sns l il).2 [::] 
    (Some (List.nth (sn_idx f) (sn_args f) vs_d)) m vs (fn_body f)) 
  (funpred_defs_to_sns l il).1 /\
  Forall (fun p : pn => decrease_pred (funpred_defs_to_sns l il).1 
    (funpred_defs_to_sns l il).2 [::] 
    (Some (List.nth (sn_idx p) (sn_args p) vs_d)) m vs (pn_body p)) 
  (funpred_defs_to_sns l il).2).
Proof.
  rewrite /find_idx_list.
  set (t:=(split_funpred_defs l)).
  move=> Hfind. rewrite find_elt_pred_none in Hfind.
  move=> il Hinl [Hfuns Hpreds].
  move: Hfind => /(_ il Hinl).
  rewrite andb_false_iff => [[Hfun | Hpred]].
  - move: Hfun => /forallb_ForallP => 
    /(_ (fun f : fn => decrease_fun (funpred_defs_to_sns l il).1 
    (funpred_defs_to_sns l il).2 [::] 
    (Some (List.nth (sn_idx f) (sn_args f) vs_d)) m vs (fn_body f))).
    move=> Hfun. apply Hfun=>// x Hinx.
    by apply check_decrease_fun_spec;
    apply (funpred_defs_to_sns_NoDup (valid_context_wf _ gamma_valid))=>//;
    apply Hcand.
  - move: Hpred => /forallb_ForallP => 
    /(_ (fun p : pn => decrease_pred (funpred_defs_to_sns l il).1 
    (funpred_defs_to_sns l il).2 [::] 
    (Some (List.nth (sn_idx p) (sn_args p) vs_d)) m vs (pn_body p))).
    move=> Hpred. apply Hpred=>// x Hinx.
    by apply check_decrease_pred_spec;
    apply (funpred_defs_to_sns_NoDup (valid_context_wf _ gamma_valid))=>//;
    apply Hcand.
Qed.

Lemma get_possible_index_lists_spec (l: list (list nat)) (l1: list nat):
  In l1 (get_possible_index_lists l) <->
  length l1 = length l /\
  forall i, (i < length l)%coq_nat -> In (List.nth i l1 0) (List.nth i l nil).
Proof.
  generalize dependent l1.
  induction l as [| lhd ltl IH]; intros l1; simpl.
  - split; intros; destruct_all; try contradiction.
    + split; auto. intros. lia.
    + left. symmetry. apply length_zero_iff_nil; assumption.
  - split.
    + rewrite in_concat. intros [l2 [Hinl2 Hnl1]].
      rewrite in_map_iff in Hinl2.
      destruct Hinl2 as [ihd [Hl2 Hinihd]].
      subst. rewrite in_map_iff in Hnl1.
      destruct Hnl1 as [itl [Hl1 Hinitl]].
      subst. simpl.
      apply IH in Hinitl.
      destruct Hinitl as [Hlen Halli].
      split=>//; [lia |].
      intros i Hi. destruct i; auto.
      apply Halli. lia.
    + intros [Hlen Halli].
      rewrite in_concat. destruct l1 as [|ihd itl]; [discriminate|].
      assert (Hinitl: In itl (get_possible_index_lists ltl)).
      {
        apply IH. simpl in *. split; try lia.
        intros i Hi. specialize (Halli (S i)). apply Halli. lia.
      }
      eexists. split.
      rewrite in_map_iff. exists ihd.
      split. reflexivity. specialize (Halli 0 ltac:(lia)). apply Halli.
      rewrite in_map_iff. exists itl. split; auto.
Qed.

Lemma has_existsP {A: Type} (b: A -> bool) (P: A -> Prop) {l: list A}:
  (forall x, In x l -> reflect (P x) (b x)) ->
  reflect (exists x, In x l /\ P x) (List.existsb b l).
Proof.
  elim: l => //=[_ |h t /= IH Hrefl].
  { reflF. by case: H. }
  case: (Hrefl h (ltac:(auto))) => Hph/=.
  { apply ReflectT. exists h. by auto. }
  prove_hyp IH.
  { move=> x Hinx. by apply Hrefl; auto. }
  case: IH => Hex.
  - apply ReflectT. case: Hex => [y [Hiny Hy]].
    by exists y; auto.
  - reflF.
    case: H => [[Hxh | Hinx]] Hpx; subst=>//.
    apply Hex. by exists x.
Qed.

Lemma filter_nil {A: Type} (p: A -> bool) (l: list A):
  filter p l = nil <-> forall x, In x l -> p x = false.
Proof.
  induction l as [| h t IH]; simpl.
  - split; auto; intros; contradiction.
  - destruct (p h) eqn : Hph.
    + split; auto; try discriminate.
      intros Hall. rewrite Hall in Hph; auto. discriminate.
    + rewrite IH. split; intros; auto. destruct_all; auto.
Qed. 

Lemma map_nil {A B: Type} (f: A -> B) (l: list A):
  map f l = nil ->
  l = nil.
Proof.
  destruct l; simpl; auto; discriminate.
Qed.

(*TODO: do we need the full spec?*)
(*TODO: do we need other direction?*)
Lemma get_idx_lists_spec mutfun mutpred m vs cands:
  In (m, vs, cands) (get_idx_lists mutfun mutpred) (*/\ cands <> nil*) ->
  (*Normal case*)
  (cands <> nil /\
    
    (length cands = (length mutfun + length mutpred)%coq_nat /\
  forall i, (i < length cands)%coq_nat -> 
    (List.nth i cands nil) <> nil /\
    forall n, In n (List.nth i cands nil) ->
    (n < length (List.nth i (map (fun x => snd (fst x)) mutfun ++
      map (fun x => snd (fst x)) mutpred) nil))%coq_nat /\
    vty_in_m m vs (snd (List.nth n (List.nth i (map (fun x => snd (fst x)) mutfun ++
      map (fun x => snd (fst x)) mutpred) nil) vs_d)))) (*\/
  (*Nil case*)
  (cands = nil /\ exists vars, In vars (map (fun x => snd (fst x)) mutfun ++
      map (fun x => snd (fst x)) mutpred) /\
      forall x, In x vars -> vty_in_m m vs (snd x) = false))*).
Proof.
  unfold get_idx_lists.
  - rewrite in_filter/= => [[Hnotnull]].
    rewrite /get_idx_lists_aux.
    rewrite in_map_iff. move=> [[m1 vs1]] [Heq Hinads].
    (*move=> [[[m1 vs1] [Heq Hinads]] Hnotn]. *)
    injection Heq. intros Hex Hvs Hm; subst m1 vs1.
    match goal with
    | H: (match ?b with | true => ?l1 | false => ?l2 end
    ) = ?y |- _ => destruct b eqn : Hnullex
    end.
    (*Null case*)
    { by subst. }
    (*Non-null case*)
    split.
    { move => C. by rewrite C in Hnotnull. }
    subst.
    rewrite !map_length.
    split_all.
    + by rewrite app_length !map_length.
    + intros i. rewrite app_length !map_length. intros Hi.
      split.
      { apply existsb_false in Hnullex.
        rewrite Forall_forall in Hnullex.
        move=> Heqnull.
        have: @null nat nil by []. rewrite -Heqnull.
        rewrite Hnullex //. apply nth_In.
        by rewrite !map_length app_length !map_length.
      }
      intros n.
      rewrite -> !map_nth_inbound with (d2:=nil);
      last by rewrite app_length !map_length; lia.
      rewrite in_map_iff. intros [[j ty] [Hn Hint]]; subst.
      revert Hint.
      rewrite in_filter. simpl. intros [Htym Hinj].
      revert Hinj. rewrite in_combine_iff; last
        by rewrite -size_length size_iota !map_length.
      move=> [k]. rewrite -size_length size_iota.
      move=> [Hk Hallnthk].
      specialize (Hallnthk 0 vty_int).
      move: Hallnthk => [] Hj Hty; subst.
      move: Htym. rewrite -> map_nth_inbound with (d2:=vs_d) =>//.
      rewrite (nth_eq _ (iota _ _)) nth_iota //.
      by apply /ltP.
Qed. 
  (* - move => [Hnotnull [Hlen Hall]].
    rewrite in_filter. split.
    { rewrite /=. by apply /nullP. }
    rewrite /get_idx_lists_aux.
    rewrite in_map_iff.
    exists (m, vs). split.
    + f_equal.
      match goal with
      | |- context[match ?b with | true => ?l1 | false => ?l2 end]
       => destruct b eqn : Hnullex
      end.
      * (*Here, prove if one is null, we have a contradiction*) 
        apply existsb_exists in Hnullex.
        case: Hnullex => [l1 [Hinl1 Hnulll1]].
        rewrite in_map_iff in Hinl1.
        case: Hinl1 => [vars [Hvars Hinvars]].
        subst.
        destruct (In_nth _ _ nil Hinvars) as [j[Hj Hvars]].
        move: Hj. rewrite app_length !map_length => Hj.
        rewrite -Hlen in Hj.
        move: Hall => /(_ j Hj).
        move=> [Hjnull Hinj].
        move: Hnulll1 => /nullP.
        move=> Hnull; apply map_nil in Hnull.
        rewrite filter_nil in Hnull.
        destruct (List.nth j cands nil) as [| n1 ntl]=>//.
        move: Hinj => /(_ n1 ltac:(simpl; auto)).
        move=> [Hn1 Hinm].
        move: Hnull => /(_ (n1, (List.nth n1 (List.nth j ([seq x.1.2 | x <- mutfun] ++ [seq x.1.2 | x <- mutpred]) [::]) vs_d).2)).
        move=> Hfalse. move: Hinm. rewrite Hfalse //.
        rewrite in_combine_iff; last
          by rewrite -size_length size_iota map_length.
        rewrite -size_length size_iota.
        exists n1. 
        split; first by subst.
        move=> d1 d2. f_equal.
        { rewrite nth_eq nth_iota //. apply /ltP. by subst. }
        subst vars. by rewrite -> map_nth_inbound with (d2:=vs_d).
      * (*Nothing is null*)
        apply list_eq_ext'.
        { by rewrite !map_length app_length !map_length. }
        move=> n d.
        rewrite !map_length app_length !map_length => Hn. *)

(*What i want to say: either
1. every list is not nil and all indices of vars have the correct type OR
2. there is a list that is nil and there are no indices of that
  type in the syms*)
(* Lemma get_idx_lists_spec mutfun mutpred m vs cands:
  In (m, vs, cands) (get_idx_lists mutfun mutpred) (*/\ cands <> nil*) <->
  (*Normal case*)
  ((length cands = (length mutfun + length mutpred)%coq_nat /\
  forall i, (i < length cands)%coq_nat -> 
    (List.nth i cands nil) <> nil /\
    forall n, In n (List.nth i cands nil) ->
    vty_in_m m vs (snd (List.nth n (List.nth i (map (fun x => snd (fst x)) mutfun ++
      map (fun x => snd (fst x)) mutpred) nil) vs_d))) \/
  (*Nil case*)
  (cands = nil /\ exists vars, In vars (map (fun x => snd (fst x)) mutfun ++
      map (fun x => snd (fst x)) mutpred) /\
      forall x, In x vars -> vty_in_m m vs (snd x) = false)).
Proof.
  unfold get_idx_lists. split.
  - rewrite in_map_iff. move=> [[m1 vs1]] [Heq Hinads].
    (*move=> [[[m1 vs1] [Heq Hinads]] Hnotn]. *)
    injection Heq. intros Hex Hvs Hm; subst m1 vs1.
    match goal with
    | H: (match ?b with | true => ?l1 | false => ?l2 end
    ) = ?y |- _ => destruct b eqn : Hnullex
    end.
    (*Null case*)
    {
      right. split=>//. apply existsb_exists in Hnullex.
      case: Hnullex => [il [Hinil Hnll]].
      apply null_nil in Hnll. subst.
      rewrite in_map_iff in Hinil.
      case: Hinil => [vars [Hnil Hinvars]].
      apply map_nil in Hnil.
      rewrite filter_nil in Hnil.
      exists vars. split=>//.
      move=> x Hinx. 
      destruct (In_nth vars x vs_d Hinx) as [i [Hi Hx]]; subst.
      move: Hnil => /(_ (i, (snd (List.nth i vars vs_d))))/= ->//.
      rewrite in_combine_iff; last
        by rewrite -size_length size_iota map_length.
      exists i. rewrite -size_length size_iota. split=>//.
      move=> d1 d2. rewrite (nth_eq _ (iota _ _)) nth_iota; last by apply /ltP.
      by rewrite -> map_nth_inbound with (d2:=vs_d).   
    }
    (*Non-null case*)
    subst.
    rewrite !map_length.
    left.
    split.
    + by rewrite app_length !map_length.
    + intros i. rewrite app_length !map_length. intros Hi.
      split.
      { apply existsb_false in Hnullex.
        rewrite Forall_forall in Hnullex.
        move=> Heqnull.
        have: @null nat nil by []. rewrite -Heqnull.
        rewrite Hnullex //. apply nth_In.
        by rewrite !map_length app_length !map_length.
      }
      intros n.
      rewrite -> !map_nth_inbound with (d2:=nil);
      last by rewrite app_length !map_length; lia.
      rewrite in_map_iff. intros [[j ty] [Hn Hint]]; subst.
      revert Hint.
      rewrite in_filter. simpl. intros [Htym Hinj].
      revert Hinj. rewrite in_combine_iff; last
        by rewrite -size_length size_iota !map_length.
      move=> [k]. rewrite -size_length size_iota.
      move=> [Hk Hallnthk].
      specialize (Hallnthk 0 vty_int).
      move: Hallnthk => [] Hj Hty; subst.
      move: Htym. rewrite -> map_nth_inbound with (d2:=vs_d) =>//.
      rewrite (nth_eq _ (iota _ _)) nth_iota //.
      by apply /ltP.
  - move=> [Hnonull | Hnull].
    + (*Not null case first*)
      (*START*)
  
   move=> [Hlen | Halli]. move => [Hlen Halli].
    rewrite in_map_iff/=. split.
    exists (m, vs). split.
    + f_equal.
      (*TODO: need to do something better for null (or maybe filter
        it out after, might be easier)*)
    split.
    move=> A.
    exists (m, vs).
    move => A.
      2: { by []. }
      
      
       Unshelve.
      rewrite /=.
      injection Hallnthk.
      intros [k].
       
       
        }
      
       intros [Hv]
      rewrite in_app_iff.
      
       rewrite in_map_iff.
      2: { rewrite app_length !map_length. lia. }
      Unshelve.


    + subst; contradiction.


    destruct (@has_existsP _ null (fun x => x <> nil) [seq [seq i.1 | i <- combine (iota 0 (Datatypes.length args)) [seq i.2 | i <- args] & vty_in_m m vs i.2] | args <- [seq x.1.2 | x <- mutfun] ++ [seq x.1.2 | x <- mutpred]]).
    2: {}
    Search List.existsb reflect.



    vty_in_m m vs (snd ). *)

(*Idea: we know exactly what the list will be - it will be the
  map over iota... for this particular m (because we just have an
  amalgamation of them) and we know not all none because il has to
  be in it. *)


(* Lemma get_idx_lists_equiv (mutfun : list (funsym * seq vsymbol * term)) mutpred :
  get_idx_lists mutfun mutpred =
  filter (fun l => forallb (fun x => negb (null x)) l)
    (map (fun l => filter (fun i => vty_in_m m vs (List.nth i l vs_d).2) 
      (iota 0 (length l)))
      (map (fun x => x.1.2) mutfun ++ map (fun x => x.1.2) mutpred)
    ). *)

Lemma null_app {A: Type} (l1 l2: list A):
  null (l1 ++ l2) = null l1 && null l2.
Proof.
  by case: l1.
Qed.

(* Lemma is_vty_adt_in_m ty m a vs:
  is_vty_adt gamma ty = Some (m, a, vs) ->
  vty_in_m m vs ty.
Proof.
  move=> His. apply is_vty_adt_some in His.
  case: His => [Hty [a_in m_in]]; subst.
  apply /vty_in_m_spec. by exists a.
Qed. *)

Lemma is_vty_adt_in_m m vs ty (m_in: mut_in_ctx m gamma):
  vty_in_m m vs ty <-> exists a, is_vty_adt gamma ty = Some (m, a, vs).
Proof.
  split.
  - unfold vty_in_m. destruct ty=>//.
    move=> /andP[Hfind]. case: list_eq_dec => //Hl _; subst.
    move: Hfind. case Hfind: (find_ts_in_mut t m) => [a |//].
    move=> _. apply find_ts_in_mut_some in Hfind.
    case: Hfind => [Hadt Ht]; subst.
    exists a. by apply is_vty_adt_iff.
  - move=> [a Hisadt]. apply is_vty_adt_some in Hisadt.
    case: Hisadt => [Hty [a_in m_in']]; subst.
    apply /vty_in_m_spec. by exists a.
Qed.

Lemma get_adts_present_in (l: list (list vsymbol)) m vs
  (m_in: mut_in_ctx m gamma):
  In (m, vs) (get_adts_present l) <->
  exists v, In v (concat l) /\ vty_in_m m vs (snd v).
Proof.
  rewrite /get_adts_present.
  elim: (concat l) => [| h t IH].
  - split=>//. intros; destruct_all; auto.
  - (*hack*) Opaque union. rewrite /=.
    case Hisadt: (is_vty_adt gamma h.2) => [[[m1 a1] vs1]|].
    + rewrite union_elts IH. simpl.
      split.
      * move=> [[[] Hm1 Hvs | []] | [v [Hinv Hinm]]]; subst.
        { exists h. split; auto. apply is_vty_adt_in_m=>//. by exists a1. }
        { exists v. split; auto. }
      * move=> [v [[Hhv | Hinv] Hinm]]; subst.
        { left. left. apply is_vty_adt_in_m in Hinm=>//.
          case: Hinm => [a2 Hisadt2].
          rewrite Hisadt2 in Hisadt. by inversion Hisadt; subst. }
        { right. by exists v. }
    + rewrite IH. split.
      * move=> [v [Hinv Hinm]]. exists v. by auto.
      * move=> [v [[Hhv | Hinv] Hinm]]; last by exists v; auto.
        subst. rewrite is_vty_adt_in_m in Hinm=>//.
        case: Hinm => [a Hisadt']. by rewrite Hisadt' in Hisadt.
Qed.

Lemma null_filter {A: Type} (p: A -> bool) (l: seq A):
  reflect (forall x, In x l -> p x = false) (null (filter p l)).
Proof.
  apply iff_reflect.
  rewrite -filter_nil. symmetry. apply null_nil.
Qed.

(*Other direction - suppose we know a list that works. Then there 
  is some candidate in [get_idx_lists] such that il is in it*)
Lemma get_idx_lists_exists (mutfun : list (funsym * seq vsymbol * term)) mutpred m vs il
  (m_in: mut_in_ctx m gamma)
  (Hnotnull: (length mutfun + length mutpred)%coq_nat <> 0)
  (Hlen: length il = (length mutfun + length mutpred)%coq_nat)
  (Hilbound: forall i, (i < length il)%coq_nat ->
    (List.nth i il 0 < length (List.nth i
      (map (fun x => (snd (fst x))) mutfun ++
      map (fun x => snd (fst x)) mutpred) nil))%coq_nat)
  (Hil: forall i, (i < length il)%coq_nat ->
    vty_in_m m vs (snd (List.nth (List.nth i il 0) 
      (List.nth i
      (map (fun x => (snd (fst x))) mutfun ++
      map (fun x => snd (fst x)) mutpred) nil) vs_d))):
  exists cands, In (m, vs, cands) (get_idx_lists mutfun mutpred) /\
    (forall i, (i < length cands)%coq_nat -> In (List.nth i il 0) (List.nth i cands nil)).
Proof.
  rewrite /get_idx_lists/get_idx_lists_aux.
  (*A key result we will need*)
  have Hincomb: (forall j, (j < length il)%coq_nat ->
      In (List.nth j il 0, (List.nth (List.nth j il 0) 
        (List.nth j ([seq x.1.2 | x <- mutfun] ++ 
          [seq x.1.2 | x <- mutpred]) [::]) vs_d).2) 
          [seq it <- combine (iota 0 (length (List.nth j
            ([seq x.1.2 | x <- mutfun] ++ [seq x.1.2 | x <- mutpred]) [::]))) 
          [seq i.2 | i <- List.nth j ([seq x.1.2 | x <- mutfun] ++ 
            [seq x.1.2 | x <- mutpred]) [::]] | vty_in_m m vs it.2]).
  {
    move=> k Hk. rewrite in_filter. split; first by apply Hil.
    rewrite in_combine_iff -(size_length (iota _ _)) size_iota;
      last by rewrite map_length.
    exists (List.nth k il 0). split; first by apply Hilbound.
    move=> d1 d2. f_equal.
    * rewrite (nth_eq _ (iota _ _)) nth_iota //. by apply /ltP; apply Hilbound.
    * rewrite -> map_nth_inbound with (d2:=vs_d) =>//.
      by apply Hilbound.
  }
  (*The list is just the one from (m, vs) in the function.
    And we will prove that it will not be null when filtered*)
  exists ( map (fun args =>
        map fst ((filter (fun it =>
          vty_in_m m vs (snd it)
        ))
        (combine (iota 0 (length args)) (map snd args)))
      ) (map (fun x => snd (fst x)) mutfun ++
      map (fun x => snd (fst x)) mutpred) ).
  split.
  - rewrite in_filter. split.
    + simpl. rewrite null_map null_app !null_map.
      apply /negP => /andP[Hnull1 Hnull2].
      apply Hnotnull. destruct mutfun=>//. by destruct mutpred.
    + rewrite in_map_iff.
      exists (m, vs). split.
      (*Easier - show (m, vs) is in [get_adts_present]*)
      2: {
        apply get_adts_present_in=>//.
        move: Hil => /(_ 0 (ltac:(lia))) => Hinm.
        eexists. split; last by apply Hinm.
        rewrite in_concat. eexists.
        split; last by apply nth_In; apply Hilbound; lia.
        apply nth_In. rewrite app_length !map_length. lia.
      }
      (*Harder - show not null*)
      f_equal.
      match goal with
      | |- context[match ?b with | true => ?l1 | false => ?l2 end]
       => destruct b eqn : Hnullex
      end. 2: by [].
      apply existsb_exists in Hnullex.
      exfalso.
      case: Hnullex => [l1 [Hinl1 Hnull1]].
      rewrite in_map_iff in Hinl1.
      case: Hinl1 => [vars [Hl1 Hinvars]]; subst.
      rewrite null_map in Hnull1.
      move: Hnull1 => /null_filter Hallfalse.
      destruct (In_nth _ _ nil Hinvars) as [j [Hj Hvars]]; subst.
      (*Contradiction - we know that there is an element where vty_in_m is true*)
      move: Hj. rewrite app_length !map_length -Hlen => Hj.
      move: Hincomb => /(_ _ Hj). rewrite in_filter/= => [[Hinm' Hinj]] .
      move: Hallfalse => /( _ _ Hinj)/=.
      by rewrite Hinm'.
  - (*Now, we need to prove the last part - that il appears in cands.
      We did most of the work already in [Hincomb]*)
    move=> i. rewrite !map_length app_length !map_length -Hlen => Hi.
    rewrite -> map_nth_inbound with (d2:=nil)=>//;
      last by rewrite app_length !map_length; lia.
    rewrite in_map_iff. 
    by eexists; split; [| apply (Hincomb _ Hi)].
Qed.

  (*TODO: maybe better to give nicer functional spec for [get_idx_lists_aux]
    as in:
    = filter 
      (fun l => forallb (negb null) l)
    
      (map (fun l => filter (fun i => vty_in_m m vs (nth i l)) 
      (iota 0 length l)) 
    (mutfun_vars ++ mutpred_vars))

  and then filter out null

  then we can say this, and prove that il is in here
  basically, get combine and 
  *)

(*Is this proved/implied anywhere?*)
Lemma funpred_def_valid_args (l: list funpred_def)
  (Hall: Forall (funpred_def_valid_type gamma) l)
  (i: nat) (Hi: (i < length l)%coq_nat):
  List.map snd (List.nth i ([seq x.1.2 | x <- (split_funpred_defs l).1] ++ 
    [seq x.1.2 | x <- (split_funpred_defs l).2]) nil) =
  s_args (List.nth i (map (fun x => f_sym x.1.1) (split_funpred_defs l).1 ++
    (map (fun x => p_sym x.1.1) (split_funpred_defs l).2)) id_fs).
Proof.
  have Hlen:=(split_funpred_defs_length l).
  have [Hin1 Hin2] := split_funpred_defs_in_l l.
  rewrite Forall_forall in Hall.
  set (t:=(split_funpred_defs l)) in *.
  have [Hi' | Hi']: ((i < length t.1)%coq_nat \/ (length t.1 <= i)%coq_nat) by lia.
  - rewrite !app_nth1; try by rewrite map_length.
    rewrite -> !map_nth_inbound with (d2:=(id_fs, nil, tm_d)); try by [].
    have : In (List.nth i t.1 (id_fs, [::], tm_d)) t.1
      by apply nth_In.
    rewrite Hin1 => Hinl.
    apply Hall in Hinl.
    move: Hinl. rewrite //=. intros H; apply H.
  - rewrite !app_nth2; try by rewrite map_length.
    rewrite -> !map_nth_inbound with (d2:=(id_ps, nil, Ftrue)); try 
      by rewrite !map_length; lia.
    rewrite !map_length.
    have : In (List.nth (i - length t.1)%coq_nat t.2 (id_ps, [::], Ftrue)) t.2 by
      apply nth_In; lia.
    rewrite Hin2 => Hinl.
    apply Hall in Hinl.
    move: Hinl. rewrite //=. intros H; apply H.
Qed.

Lemma plus_minus (n m: nat):
  ((n + m)%coq_nat - n)%coq_nat = m.
Proof.
  lia.
Qed.

(*The converse is not true because in principle many lists could
  satsify the conditions*)
Theorem check_termination_some (l: list funpred_def) m params vs il
  (Hinl: In l (mutfuns_of_context gamma)):
  check_termination l = Some (m, params, vs, il) ->
  funpred_def_term gamma l m params vs il.
Proof.
  rewrite /check_termination /funpred_def_term.
  case: (nullP l) =>// Hnotnull.
  set (t := (split_funpred_defs l)).
  set (funsyms := (List.map (fun x : funsym * seq vsymbol * term => f_sym x.1.1) t.1)).
  set (predsyms :=  List.map (fun x : predsym * seq vsymbol * formula => p_sym x.1.1) t.2).
  case Hfind: (find_eq  (fun (x : fpsym) => s_params x) (funsyms ++ predsyms)) => [params1 | //].
  move: Hfind => /eqP /find_eq_spec [Hnull' Hparams].
  case Helt: (find_elt (fun '(m0, vs0, cands) => 
    if (Datatypes.length vs0 =? Datatypes.length (m_params m0))%N && mut_in_ctx m0 gamma then
    find_idx_list l m0 vs0 (get_possible_index_lists cands) else None) (get_idx_lists t.1 t.2)) =>
    [[[[m1 vs1] cands1] idx1]|//].
  apply find_elt_some in Helt.
  case: Helt => [Hinlists Hfindlist].
  move=> Hsome. rewrite /= in Hsome.
  case: Hsome => Hm1 Hparams1 Hvs1 Hidx1; subst.
  move: Hfindlist.
  case: (Nat.eqb_spec (length vs) (length (m_params m))) =>// Hlenvs1.
  case m_in: (mut_in_ctx m gamma) =>// Hfindlist.
  rewrite /= in Hfindlist.
  have Hcands:=(find_idx_list_some_cands _ _ _ _ _ Hfindlist).
  (*Use this to get length info*)
  move: Hinlists => /inP Hinlists.
  apply get_idx_lists_spec in Hinlists.
  case: Hinlists => [Hcandsnull [Hcandslen Hcandspec]].
  apply get_possible_index_lists_spec in Hcands.
  case: Hcands => [Hlenil Hallil].
  have Hlenil': length il = length l. {
    pose proof (split_funpred_defs_length l). unfold t in Hcandslen. lia.
  }
  apply find_idx_list_some in Hfindlist =>//.
  split_all =>//.
  (*The hard goals were already proved. Here we prove some well-formedness
    results*)
  - move=> i Hi. move: Hallil => /(_ i ltac:(lia)) => Hincands.
    move: Hcandspec => /(_ i ltac:(lia)).
    move=> [Hnotnil] /(_ _ Hincands) [Hlt] _ .
    pose proof (all_funpred_def_valid_type gamma_valid _ Hinl).
    rewrite -funpred_def_valid_args //.
    rewrite !map_length. apply Hlt. lia.
  - move=> f. rewrite funpred_defs_to_sns_in_fst //.
    move=> [i [Hi /= Hf]]. subst; simpl.
    move: Hallil => /(_ i ltac:(unfold t in *; lia)) => Hincands.
    move: Hcandspec => /(_ i ltac:(unfold t in *; lia)) => [[Hnotnil]]
    /(_ _ Hincands) [] Hlt.
    rewrite app_nth1; last by rewrite map_length; unfold t; lia.
    by rewrite -> map_nth_inbound with (d2:= (id_fs, nil, tm_d)).
  - move=> p. rewrite funpred_defs_to_sns_in_snd //.
    move=> [i [Hi /= Hf]]. subst; simpl.
    move: Hallil => /(_ (length t.1 + i)%coq_nat ltac:(unfold t in *; lia)) => Hincands.
    move: Hcandspec => /(_ (length t.1 + i)%coq_nat ltac:(unfold t in *; lia)) => [[Hnotnil]]
    /(_ _ Hincands) [] Hlt.
    rewrite app_nth2; last by rewrite map_length; unfold t; lia.
    rewrite !map_length combine_length firstn_length min_l; last by
      unfold t in *; lia.
    rewrite plus_minus.
    by rewrite -> map_nth_inbound with (d2:= (id_ps, nil, Ftrue)).
  - move=> f. rewrite funpred_defs_to_sns_in_fst //.
    move=> [i [Hi /= Hf]]. subst; simpl.
    apply Hparams. rewrite mem_cat /funsyms. apply /orP; left.
    apply /inP. rewrite in_map_iff. eexists. split; [reflexivity|].
    by apply nth_In.
  - move=> p. rewrite funpred_defs_to_sns_in_snd //.
    move=> [i [Hi /= Hf]]. subst; simpl.
    apply Hparams. rewrite mem_cat /funsyms. apply /orP; right.
    apply /inP. rewrite in_map_iff. eexists. split; [reflexivity|].
    by apply nth_In.
Qed.

Lemma obind_none {A B: Type} (f: A -> option B) (o: option A) :
  obind f o = None ->
  o = None \/ exists x, o = Some x /\ f x = None.
Proof.
  rewrite /obind/oapp. case: o => [x Hfx | _ ].
  - right. by exists x.
  - by left.
Qed.

(*reflect (size vs = size (m_params m) /\
    mut_in_ctx m gamma /\
    (forall f, f \in fs ->
      vty_in_m m vs (snd (nth vs_d (sn_args f) (sn_idx f)))) /\
    (forall p, p \in ps ->
      vty_in_m m vs (snd (nth vs_d (sn_args p) (sn_idx p) ))) /\
    (forall f, f \in fs ->
       decrease_fun fs ps nil 
      (Some (nth vs_d (sn_args f) (sn_idx f))) m vs (fn_body f)) /\
    (forall p, p \in ps ->
      decrease_pred fs ps nil 
      (Some (nth vs_d (sn_args p) (sn_idx p))) m vs (pn_body p)))
    (find_mut_args fs ps il == Some (m, vs)).*)

(*The converse: if our check returns none, there is no
  possible set of indices for termination*)
Theorem check_termination_none (l: list funpred_def)
  (Hinl: In l (mutfuns_of_context gamma)):
  check_termination l = None ->
  forall m params vs il,
    ~ funpred_def_term gamma l m params vs il.
Proof.
  move=> Hfind m params vs il.
  rewrite /funpred_def_term => [[Hlnil [Hlenvs [m_in [Hlenil 
    [Hargsnth [Hfvty [Hpty [Hfparams [Hpparams [Hfdec Hpdec]]]]]]]]]]].
  move: Hfind.
  rewrite /check_termination.
  case: (nullP l) => [//| _].
  set (t:=(split_funpred_defs l)) in *.
  (*First, prove that find_eq must be [Some params]*)
  have /eqP Hfindeq': find_eq [eta s_params] (map (fun y => f_sym y.1.1) t.1 ++ map (fun y => p_sym y.1.1) t.2) ==
    Some params.
  {
    apply /find_eq_spec. split=>//. 
    - move=> Hnotnil.
      pose proof (split_funpred_defs_length l).
      apply (f_equal (@length _)) in Hnotnil.
      rewrite app_length !map_length in Hnotnil; unfold t in *; simpl in *.
      have: length l = 0 by lia.
      by rewrite length_zero_iff_nil.
    - move=> x. rewrite mem_cat => /orP[/inP | /inP];
      rewrite in_map_iff => [[[[f vars] tm] [/=Hx Hinf]]]; subst.
      (*Get the nat index to build the fn*)
      + destruct (In_nth _ _ (id_fs, nil, tm_d) Hinf) as [i [Hi Hf]].
        move: Hfparams => /(_ (fundef_to_fn f vars tm (List.nth i il 0)))->//.
        apply funpred_defs_to_sns_in_fst =>//.
        exists i. split=>//. by rewrite Hf.
      + destruct (In_nth _ _ (id_ps, nil, Ftrue) Hinf) as [i [Hi Hf]].
        move: Hpparams => /(_ (preddef_to_pn f vars tm (List.nth (length t.1 + i)%coq_nat il 0)))->//.
        apply funpred_defs_to_sns_in_snd =>//.
        exists i. split=>//. rewrite Hf/=.
        rewrite map_length combine_length firstn_length min_l//.
        pose proof (split_funpred_defs_length l); lia.
  }
  rewrite Hfindeq'/=.
  move=> Hfind. apply obind_none in Hfind.
  case: Hfind => [Hgetidx | Hfind].
  {
    (*Here, we need a contradiction from the candidates; we use
      [get_idx_lists_exists]*)
    move: Hgetidx => /eqP /find_elt_none/=.
    (*Need hypotheses for [get_idx_lists_exists]*)
    have Hnotzero: (length t.1 + length t.2)%coq_nat <> 0.
    { unfold t. rewrite (split_funpred_defs_length l).
      move=> Hnzero. by apply length_zero_iff_nil in Hnzero.
    }
    have Hleneq: (length il = (length t.1 + length t.2)%coq_nat) by
      by rewrite (split_funpred_defs_length l).
    pose proof (get_idx_lists_exists t.1 t.2 m vs il m_in Hnotzero Hleneq) as Hget.
    prove_hyp Hget.
    {
      move=> i Hi. move: Hargsnth => /(_ i Hi).
      rewrite -funpred_def_valid_args//; try lia; first by
        rewrite map_length.
      by apply all_funpred_def_valid_type.
    }
    prove_hyp Hget.
    {
      move=> i Hi.
      (*Here we need 2 cases: fn and pn*)
      have [Hi' | Hi']: (i < length t.1)%coq_nat \/ (length t.1 <= i)%coq_nat by lia.
      - set (y:=(List.nth i t.1 (id_fs, nil, tm_d))). 
        move: Hfvty => /(_ (fundef_to_fn y.1.1 y.1.2 y.2  (List.nth i il 0))).
        rewrite funpred_defs_to_sns_in_fst//= => Hfvty.
        rewrite app_nth1; last by rewrite map_length.
        rewrite -> map_nth_inbound with (d2:= (id_fs, nil, tm_d))=>//.
        apply Hfvty.
        by exists i. 
      - set (y:=(List.nth (i - length t.1)%coq_nat t.2 (id_ps, nil, Ftrue))). 
        move: Hpty => /(_ (preddef_to_pn y.1.1 y.1.2 y.2  (List.nth i il 0))).
        rewrite funpred_defs_to_sns_in_snd//= => Hpvty.
        rewrite app_nth2 map_length//.
        rewrite -> map_nth_inbound with (d2:= (id_ps, nil, Ftrue))=>//; last by lia.
        apply Hpvty.
        exists (i - (length t.1))%coq_nat. rewrite !map_length. split.
        + unfold t in *; lia.
        + rewrite combine_length firstn_length min_l=>//;
            last by unfold t in *; lia.
          f_equal. f_equal. unfold t in *. lia.
    }
    (*Finally, can use cands*)
    case: Hget => [cands [Hinget Hcands]].
    have Hinget':=Hinget.
    move: Hinget => /inP Hinget.
    move=> /(_ (m, vs, cands) Hinget).
    rewrite Hlenvs m_in Nat.eqb_refl/=.
    move=> Hfind. apply find_idx_list_none with (il:=il) in Hfind=>//.
    (*This gives us our contradiction*)
    - by apply Hfind.
    - move=> l1. rewrite get_possible_index_lists_spec => [[Hlen]] _.
      apply get_idx_lists_spec in Hinget'. destruct_all; lia.
    - rewrite get_possible_index_lists_spec. split=>//.
      apply get_idx_lists_spec in Hinget'. destruct_all; lia.
  }
  (*Rest is trivial*)
  by case: Hfind => [[[[m1 params1]cands1 ]il1]/= [Hfind Hnone]]//.
Qed.