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
Variable gamma: context.

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
Definition get_idx_lists 
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
  | nil => nil
  end.

  (*TODO: move*)

(*A version of find that finds the (first) element satisfying a predicate*)
Definition find_elt_pred {A: Type} (f: A -> bool) (l: list A) :
  option A :=
  fold_right (fun x acc => if f x then Some x else acc) None l.

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
Definition find_idx_list 
  (mutfun: list (funsym * list vsymbol * term))
  (mutpred: list (predsym * list vsymbol * formula)) m vs
  (candidates : list (list nat))
  (*NOTE: candidates has length |mutfun| + |mutpred|
  and ith element of candidate includes all candidate indices
  for fun/pred element i*) : 
  option (list nat) :=

  let cands := get_possible_index_lists candidates in

  find_elt_pred (fun il =>
    let fs := List.map (fun x =>
      make_fn x.1.1.1 x.1.1.2 x.1.2 x.2) 
      (combine mutfun (take (size mutfun) il)) in

    let ps := List.map (fun x =>
      make_pn x.1.1.1 x.1.1.2 x.1.2 x.2) 
      (combine mutpred (drop (size mutpred) il)) in

    all (fun x =>
        let i := fst x in
        let f : fn := snd x in
        check_decrease_fun fs ps nil
        (Some (nth vs_d (sn_args f) i )) m vs (fn_body f))
        (combine (take (size fs) il) fs) &&
      all (fun x =>
        let i := fst x in
        let p : pn := snd x in
        check_decrease_pred fs ps nil
        (Some (nth vs_d (sn_args p) i)) m vs (pn_body p))
        (combine (drop (size fs) il) ps)
  ) cands.



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

HB.instance Definition _ := hasDecEq.Build fpsym fpsym_eqb_spec.

(*And now the full function to check termination*)

Definition check_termination (l: list funpred_def) :
  option (mut_adt * list typevar * list vty * list nat) :=
    let t := split_funpred_defs l in
    let syms := (List.map (fun x => f_sym x.1.1) t.1) ++
      (List.map (fun x => p_sym x.1.1) t.2) in

    (*First, find params*)
    match find_eq (fun x => s_params x) syms with
    | None => None
    | Some params =>
      (*Look through all candidates, find one*)
      option_map (fun y =>
        let '(m, vs, _, idxs) := y in
        (m, params, vs, idxs) )
      
      (find_elt (fun x =>
        let '(m, vs, cands) := x in
        find_idx_list t.1 t.2 m vs cands)
        (get_idx_lists t.1 t.2))
    end.

(*And now we have to prove correct*)