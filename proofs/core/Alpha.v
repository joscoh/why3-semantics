Require Import Common.
Require Import Syntax.
Require Import IndTypes.
Require Import Semantics.
Require Import Types.
Require Import Typing.
Require Import Substitution.
Require Import Denotational.
Require Import GenElts.
Require Import Coq.Logic.Eqdep_dec.

(*For a proof using induction on length of list*)
Require Import Coq.Arith.Wf_nat.
Require Import Wellfounded.

Require Import FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs".


(*First, some functions we need*)

(*Split a list into pieces of the appropriate lengths if we can*)
Fixpoint split_lens {A: Type} (l: list A) (lens: list nat) :
  list (list A) :=
  match lens with
  | len :: tl =>
    (firstn len l) ::
    split_lens (skipn len l) tl
  | nil => nil
  end.

Lemma split_lens_length {A: Type} (l: list A) (lens: list nat) :
  length (split_lens l lens) = length lens.
Proof.
  revert l.
  induction lens; simpl; intros; auto.
Qed.

Lemma split_lens_concat {A: Type} (l: list A) (lens: list nat) :
  sum lens = length l ->
  l = concat (split_lens l lens).
Proof.
  revert l. induction lens; simpl; intros; auto.
  destruct l; auto; inversion H.
  rewrite <- IHlens.
  rewrite firstn_skipn; auto.
  rewrite skipn_length, <- H, Nat.add_comm, Nat.add_sub; auto.
Qed.

Lemma split_lens_nodup {A: Type} (l: list A) (lens: list nat) :
  sum lens = length l ->
  NoDup l ->
  forall (i: nat) (d: list A),
    i < length lens ->
    NoDup (nth i (split_lens l lens) d).
Proof.
  revert l. induction lens; simpl; intros; auto; try lia.
  destruct i.
  - apply NoDup_firstn; assumption.
  - apply IHlens; try lia.
    + rewrite skipn_length, <- H, Nat.add_comm, Nat.add_sub; auto.
    + apply NoDup_skipn; assumption.
Qed. 

Lemma split_lens_ith {A: Type} (l: list A) (lens: list nat) (i: nat) :
  sum lens = length l ->
  i < length lens ->
  length (nth i (split_lens l lens) nil) = nth i lens 0.
Proof.
  revert l i. induction lens; simpl; intros; auto; try lia.
  destruct i.
  - rewrite firstn_length.
    apply Nat.min_l. lia.
  - specialize (IHlens (skipn a l) i).
    rewrite IHlens; auto; try lia.
    rewrite skipn_length, <- H, Nat.add_comm, Nat.add_sub; auto.
Qed.

Lemma in_split_lens_ith {A: Type} (l: list A) (lens: list nat) (i: nat) x (d: list A) :
  sum lens = length l ->
  i < length lens ->
  In x (nth i (split_lens l lens) d) ->
  In x l.
Proof.
  revert l i. induction lens; simpl; intros; auto; destruct i; auto; try lia.
  - apply In_firstn in H1; auto.
  - apply IHlens in H1; try lia.
    + apply In_skipn in H1; auto.
    + rewrite skipn_length, <- H. lia.
Qed.

(*Some tactics that will be useful:*)

Ltac wf_tac :=
  repeat (
  repeat match goal with
  | |- NoDup (nth ?i (split_lens ?a ?b) ?d) =>
    apply split_lens_nodup
  | |- context [length (split_lens ?l1 ?l2)] =>
    rewrite split_lens_length
  | |- context [length (nth ?l (split_lens ?a ?b) ?d)] =>
    intros; rewrite split_lens_ith
  | |- context [concat (split_lens ?l1 ?l2)] =>
      rewrite <- split_lens_concat
  end; list_tac2; auto; try lia).

  (*Nearly all function, predicate, pattern constr cases need
    nested induction. This does the boilerplate work*)
Ltac nested_ind_case :=
  repeat match goal with
  | H: length ?l1 =? length ?l2 |- _ => unfold is_true in H
  (*TODO: reduce duplication*)
  | H: Forall ?f ?tms1, Hlen: (length ?tms1 =? length ?tms2) = true |- _ =>
    let x1 := fresh "x" in
    let l1 := fresh "l" in
    let Hp := fresh "Hp" in
    let Hforall := fresh "Hforall" in
    apply Nat.eqb_eq in Hlen; generalize dependent tms2;
    induction tms1; simpl; intros; destruct tms2; inversion Hlen; auto;
    simpl; inversion H as [| x1 l1 Hp Hforall]; subst
  | H: Forall ?f (map ?g ?tms1), Hlen: (length ?tms1 =? length ?tms2) = true |- _ =>
    let x1 := fresh "x" in
    let l1 := fresh "l" in
    let Hp := fresh "Hp" in
    let Hforall := fresh "Hforall" in
    apply Nat.eqb_eq in Hlen; generalize dependent tms2;
    induction tms1; simpl; intros; destruct tms2; inversion Hlen; auto;
    simpl; inversion H as [| x1 l1 Hp Hforall]; subst
  end.

Ltac alpha_case x Heq :=
  destruct x; try solve[inversion Heq]; simpl; simpl in *.

Ltac case_match_hyp :=
  repeat match goal with 
      |- (match ?p with |Some l => ?x | None => ?y end) = ?z -> ?q =>
        let Hp := fresh "Hmatch" in 
        destruct p eqn: Hp end.
Ltac case_match_goal :=
  repeat match goal with 
        |- (match ?p with |Some l => ?x | None => ?y end) = ?z =>
          let Hp := fresh "Hmatch" in 
          destruct p eqn: Hp end; auto.

(*Alpha Equivalence*)

Section Alpha.

Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma)
 {pd: pi_dom} (all_unif: forall m, mut_in_ctx m gamma -> IndTypes.uniform m)
  {vt: @val_typevar sigma} {pf: pi_funpred gamma_valid pd}.

Notation term_rep := (term_rep gamma_valid pd all_unif vt pf).
Notation formula_rep := (formula_rep gamma_valid pd all_unif vt pf).

(*Check that (x, y) binding is at the same point in the list.*)
Definition eq_var (vars: list (vsymbol * vsymbol)) v1 v2 :=
  fold_right (fun t acc => (vsymbol_eq_dec v1 (fst t) && vsymbol_eq_dec v2 (snd t)) ||
    (negb (vsymbol_eq_dec v1 (fst t)) && negb (vsymbol_eq_dec v2 (snd t)) &&
    acc)) (vsymbol_eq_dec v1 v2) vars.

(*Like [eq_var] but requires that the two elements
  are in the list*)
Definition in_firstb {A B: Type} 
  (eq_dec1: forall (x y: A), {x=y} + {x<>y})
  (eq_dec2: forall (x y: B), {x=y} + {x<>y}) 
  (x: A * B) (l: list (A * B)) : bool :=
  fold_right (fun y acc => 
    (eq_dec1 (fst x) (fst y) && eq_dec2 (snd x) (snd y)) ||
    (negb (eq_dec1 (fst x) (fst y)) && negb (eq_dec2 (snd x) (snd y)) &&
    acc)) false l.

Notation var_in_firstb := (in_firstb vsymbol_eq_dec vsymbol_eq_dec).

Section EqVarLemmas.

Lemma eq_var_flip vars x y:
  eq_var vars x y = eq_var (flip vars) y x.
Proof.
  induction vars; simpl.
  - apply eq_dec_sym.
  - rewrite eq_dec_sym. f_equal. solve_bool.
    f_equal. solve_bool. apply IHvars.
Qed.

Lemma var_in_firstb_flip vars x y:
  var_in_firstb (x, y) vars =
  var_in_firstb (y, x) (flip vars).
Proof.
  induction vars; simpl; auto.
  rewrite eq_dec_sym, IHvars, andb_comm, 
  (andb_comm (negb _)). reflexivity.
Qed. 

Lemma in_firstb_in_eq l x y z:
  NoDup (map fst l) ->
  var_in_firstb (x, y) l ->
  In (x, z) l ->
  y = z.
Proof.
  induction l; simpl; intros. inversion H1.
  vsym_eq x (fst a); simpl in H0.
  - vsym_eq y (snd a); inversion H0; subst. clear H0.
    destruct H1; [rewrite H0 |]; auto.
    inversion H; subst. exfalso.
    apply H3. rewrite in_map_iff. exists (fst a, z); auto.
  - vsym_eq y (snd a); simpl in H0; try solve[inversion H0].
    inversion H; subst.
    destruct H1; subst; auto.
    contradiction.
Qed.

Lemma in_firstb_in_eq_r l x y z:
  NoDup (map snd l) ->
  var_in_firstb (y, x) l ->
  In (z, x) l ->
  y = z.
Proof.
  intros.
  assert (NoDup (map fst (flip l))). rewrite map_fst_flip; auto.
  assert (var_in_firstb (x, y) (flip l)) by
    (rewrite var_in_firstb_flip, flip_flip; auto).
  assert (In (x, z) (flip l)). rewrite in_flip_iff; auto.
  apply (in_firstb_in_eq _ _ _ _ H2 H3 H4).
Qed.

Lemma eq_var_eq vars x y:
  eq_var vars x y = var_in_firstb (x, y) vars || 
  (negb (in_dec vsymbol_eq_dec x (map fst vars)) &&
   negb (in_dec vsymbol_eq_dec y (map snd vars)) &&
   vsymbol_eq_dec x y).
Proof.
  induction vars; simpl; auto.
  rewrite eq_dec_sym. vsym_eq (fst a) x; simpl; simpl_bool; auto.
  rewrite eq_dec_sym. vsym_eq (snd a) y; simpl; simpl_bool; auto.
  rewrite IHvars. f_equal. 
  destruct (in_dec vsymbol_eq_dec x (map fst vars)); auto; simpl.
  destruct (in_dec vsymbol_eq_dec y (map snd vars)); auto.
Qed.

Lemma in_firstb_app x y l1 l2:
  var_in_firstb (x, y) (l1 ++ l2) =
  var_in_firstb (x, y) l1 || (var_in_firstb (x, y) l2 &&
    negb (in_dec vsymbol_eq_dec x (map fst l1)) && 
    negb (in_dec vsymbol_eq_dec y (map snd l1))).
Proof.
  induction l1; simpl; simpl_bool; auto.
  rewrite eq_dec_sym. vsym_eq (fst a) x; simpl; simpl_bool; auto.
  rewrite eq_dec_sym. vsym_eq (snd a) y; simpl; simpl_bool; auto.
  rewrite IHl1. f_equal. 
  destruct (in_dec vsymbol_eq_dec x (map fst l1)); simpl;
  simpl_bool; auto.
  destruct (in_dec vsymbol_eq_dec y (map snd l1)); auto.
Qed.

Lemma in_firstb_in {A B: Type} 
  (eq_dec1 : forall x y : A, {x = y} + {x <> y})
  (eq_dec2 : forall x y : B, {x = y} + {x <> y}) 
  (x : A * B) (l : list (A * B)) :
  in_firstb eq_dec1 eq_dec2 x l ->
  In x l.
Proof.
  induction l; simpl; auto.
  bool_to_prop; intros; destruct_all; repeat simpl_sumbool.
  - destruct x; destruct a; simpl in *; subst; auto.
  - right; auto.
Qed. 

Lemma in_firstb_refl: forall x l,
  (forall x, In x l -> fst x = snd x) ->
  In x (map fst l) ->
  var_in_firstb (x, x) l.
Proof.
  induction l; simpl; intros; [destruct H0 |].
  vsym_eq x (fst a); simpl; simpl_bool.
  - vsym_eq (fst a) (snd a). simpl.
    rewrite H in n; auto.
  - vsym_eq x (snd a); simpl; auto.
    + rewrite H in n; auto.
    + apply IHl; auto. destruct H0; subst; auto.
      contradiction.
Qed.

Lemma eq_var_refl: forall v vars,
  (forall x, In x vars -> fst x = snd x) ->
  eq_var vars v v.
Proof.
  induction vars; simpl; intros. vsym_eq v v.
  vsym_eq v (fst a); simpl; simpl_bool.
  - vsym_eq (fst a) (snd a).
    specialize (H a). exfalso. rewrite H in n. contradiction. auto.
  - vsym_eq v (snd a); simpl.
    rewrite H in n; auto.
Qed.

Lemma eq_var_app l1 l2 x y :
  eq_var (l1 ++ l2) x y =
  (in_firstb vsymbol_eq_dec vsymbol_eq_dec (x, y) l1) ||
  (negb (in_dec vsymbol_eq_dec x (map fst l1)) &&
  negb (in_dec vsymbol_eq_dec y (map snd l1)) &&
  eq_var l2 x y).
Proof.
  induction l1; simpl; [simpl_bool |]; auto.
  destruct a as [a1 a2]; simpl in *.
  rewrite eq_dec_sym. vsym_eq a1 x; simpl; simpl_bool; auto.
  rewrite eq_dec_sym. vsym_eq a2 y; simpl; simpl_bool; auto.
  rewrite IHl1. f_equal. f_equal.
  destruct (in_dec vsymbol_eq_dec x (map fst l1)); auto.
  destruct (in_dec vsymbol_eq_dec y (map snd l1)); auto.
Qed.

Lemma in_firstb_notin_fst {A B: Type} 
(eq_dec1 : forall x y : A, {x = y} + {x <> y})
(eq_dec2 : forall x y : B, {x = y} + {x <> y}) 
(x : A) (y: B) (l : list (A * B)) :
~ In x (map fst l) ->
in_firstb eq_dec1 eq_dec2 (x, y) l = false.
Proof.
  intros.
  destruct (in_firstb eq_dec1 eq_dec2 (x, y) l) eqn : Hin; auto.
  apply in_firstb_in in Hin.
  exfalso.
  apply H. rewrite in_map_iff. exists (x, y); auto.
Qed.

Lemma in_firstb_notin_snd {A B: Type} 
(eq_dec1 : forall x y : A, {x = y} + {x <> y})
(eq_dec2 : forall x y : B, {x = y} + {x <> y}) 
(x : A) (y: B) (l : list (A * B)) :
~ In y (map snd l) ->
in_firstb eq_dec1 eq_dec2 (x, y) l = false.
Proof.
  intros.
  destruct (in_firstb eq_dec1 eq_dec2 (x, y) l) eqn : Hin; auto.
  apply in_firstb_in in Hin.
  exfalso.
  apply H. rewrite in_map_iff. exists (x, y); auto.
Qed.

End EqVarLemmas.


(*We need the condition that [in_firstb] for the Pvar and Pbind case.
  If not, suppose we have the patterns
  Por (Pvar y) (Pvar x) and Por (Pvar x) (Pvar x)
  and vars = [(y, x)] (= combine (pat_fv p1) (pat_fv p2))
  then this would be alpha equivalent
  *)
Fixpoint alpha_equiv_p (vars: list (vsymbol * vsymbol)) (p1 p2: pattern)  : bool :=
  match p1, p2 with
  | Pvar v1, Pvar v2 =>
    vty_eq_dec (snd v1) (snd v2) &&
    var_in_firstb (v1, v2) vars (*NOTE: we need this, see above*)
  | Pconstr f1 ty1 ps1, Pconstr f2 ty2 ps2 =>
    (funsym_eq_dec f1 f2) &&
    (length ps1 =? length ps2) &&
    (list_eq_dec vty_eq_dec ty1 ty2) &&
    all2 (fun p1 p2 => alpha_equiv_p vars p1 p2) ps1 ps2
  | Por p1 p3, Por p2 p4 =>
    alpha_equiv_p vars p1 p2 &&
    alpha_equiv_p vars p3 p4
  | Pbind p1 v1, Pbind p2 v2 =>
    vty_eq_dec (snd v1) (snd v2) &&
    var_in_firstb (v1, v2) vars &&
    alpha_equiv_p vars p1 p2
  | Pwild, Pwild => true
  | _, _ => false
  end.

(*Interlude: prove that if [alpha_equiv_p] holds, the
  two patterns have free variables given by the map
  between them. This is a bit tricky to show.*)

Section PatEquivFv.

(*We will create a map from a list giving the domain and codomain*)

(*Could make polymorphic (and subsume ty_subst_fun) but
  we don't want even more eq_decs. Should use ssreflect probably*)
Fixpoint mk_fun (l1 l2: list vsymbol) (x: vsymbol) : vsymbol :=
  match l1, l2 with
  | a :: t1, b :: t2 => if vsymbol_eq_dec x a then b else mk_fun t1 t2 x
  | _, _ => x
  end.

Lemma mk_fun_in l1 l2 x:
  length l1 <= length l2 ->
  In x l1 ->
  In (mk_fun l1 l2 x) l2.
Proof.
  revert l2. induction l1; simpl; intros; auto. destruct H0.
  destruct l2. inversion H. simpl in H.
  vsym_eq x a; simpl; try triv.
  destruct H0; subst; auto.
  contradiction. right. apply IHl1; auto; lia.
Qed.

Lemma mk_fun_nth l1 l2 i d1 d2
  (Hlen: length l1 = length l2)
  (Hn1: NoDup l1)
  (Hi: i < length l1):
  mk_fun l1 l2 (nth i l1 d1) = nth i l2 d2.
Proof.
  generalize dependent l2.
  generalize dependent i.
  induction l1; simpl; intros; destruct l2; inversion Hlen; [lia|].
  destruct i.
  - vsym_eq a a.
  - inversion Hn1; subst.
    vsym_eq (nth i l1 d1) a; simpl.
    + exfalso. apply H2. wf_tac.
    + apply IHl1; auto. lia.
Qed.

Lemma mk_fun_inj (l1 l2: list vsymbol):
  NoDup l1 ->
  NoDup l2 ->
  length l1 <= length l2 ->
  (forall x y, In x l1 -> In y l1 -> 
    (mk_fun l1 l2 x) = (mk_fun l1 l2 y) -> x = y).
Proof.
  revert l2. induction l1; simpl; intros. destruct H2.
  destruct l2. inversion H1. simpl in H1.
  inversion H; inversion H0; subst.
  vsym_eq x a.
  - vsym_eq y a.
    destruct H3; subst; auto.
    apply mk_fun_in with(l2:=l2) in H3; auto.
    contradiction. lia.
  - vsym_eq y a.
    + destruct H2; subst; auto.
      apply mk_fun_in with(l2:=l2) in H2; auto. contradiction. lia.
    + destruct H2; subst; auto; try contradiction.
      destruct H3; subst; auto; try contradiction. 
      apply IHl1 with(l2:=l2); auto. lia.
Qed.

Lemma map_mk_fun l1 l2
  (Hlen: length l1 = length l2)
  (Hn1: NoDup l1):
  map (mk_fun l1 l2) l1 = l2.
Proof.
  generalize dependent l2.
  induction l1; simpl; intros; destruct l2; inversion Hlen; auto.
  vsym_eq a a. f_equal.
  inversion Hn1; subst.
  erewrite map_ext_in. apply IHl1; auto.
  intros. vsym_eq a0 a.
Qed.

(*map over a pattern, changing free vars according to map*)
(*This is useful for considering how alpha equivalent patterns
  behave*)
Fixpoint map_pat (f: vsymbol -> vsymbol) (p: pattern) : pattern :=
  match p with
  | Pvar x => Pvar (f x)
  | Pwild => Pwild
  | Pconstr c tys ps =>
    Pconstr c tys (map (fun x => map_pat f x) ps)
  | Por p1 p2 =>
    Por (map_pat f p1) (map_pat f p2)
  | Pbind p1 x =>
    Pbind (map_pat f p1) (f x)
  end.

Lemma map_pat_free_vars (f: vsymbol -> vsymbol) (p: pattern)
  (Hinj: forall x y, In x (pat_fv p) -> In y (pat_fv p) ->
    f x = f y -> x = y):
  pat_fv (map_pat f p) = map f (pat_fv p).
Proof.
  induction p; simpl; auto.
  - simpl in Hinj.
    induction ps; simpl in *; auto.
    inversion H; subst.
    rewrite map_union with(eq_dec2:=vsymbol_eq_dec).
    + rewrite H2, IHps; auto.
      * intros; apply Hinj; auto; simpl_set; triv.
      * intros; apply Hinj; auto; simpl_set; triv.
    + intros x y. rewrite !in_app_iff; intros; apply Hinj; auto;
      simpl_set_small; auto.
  - simpl in Hinj. rewrite map_union with(eq_dec2:=vsymbol_eq_dec).
    + rewrite IHp1, IHp2; auto; intros; apply Hinj; simpl_set; auto.
    + intros x y. rewrite !in_app_iff; intros; apply Hinj; simpl_set; auto.
  - simpl in Hinj.
    rewrite map_union with (eq_dec2:=vsymbol_eq_dec); simpl.
    + rewrite IHp; auto.
      intros; apply Hinj; simpl_set; auto.
    + intros x y. rewrite !in_app_iff; simpl.
      rewrite !or_false_r; intros; apply Hinj; simpl_set; auto.
Qed.

(*If f coincides with the list vars, an alpha equivalent
  pattern is really just [map_pat f]*)
Lemma alpha_equiv_p_map vars (p1 p2: pattern) (f: vsymbol -> vsymbol)
  (Heq: alpha_equiv_p vars p1 p2)
  (Hfeq: forall x y,
    var_in_firstb (x, y) vars -> y = f x):
  p2 = map_pat f p1.
Proof.
  generalize dependent p2.
  induction p1; simpl; intros; destruct p2; try solve[inversion Heq]; auto.
  - erewrite <- Hfeq. reflexivity. bool_hyps; auto.
  - bool_hyps. repeat simpl_sumbool. f_equal.
    nested_ind_case.
    rewrite all2_cons in H1. bool_hyps.
    rewrite (Hp p), (IHps Hforall _ H2); auto.  
  - bool_hyps.
    rewrite  <- (IHp1_1 p2_1), <- (IHp1_2 p2_2); auto.
  - bool_hyps. 
    rewrite <- (IHp1 p2); auto.
    f_equal. apply Hfeq; auto. 
Qed.

(*We also need a result about the types of the resulting
  free variables*)
Lemma alpha_equiv_p_map_f vars (p1 p2: pattern) (f: vsymbol -> vsymbol)
  (Heq: alpha_equiv_p vars p1 p2)
  (Hfeq: forall x y,
    var_in_firstb (x, y) vars -> y = f x):
  forall x, In x (pat_fv p1) -> snd x = snd (f x).
Proof.
  generalize dependent p2.
  induction p1; simpl; intros; destruct p2; try solve[inversion Heq]; auto.
  - bool_hyps. simpl_sumbool. destruct H as [Hvx | []]; subst. 
    erewrite <- Hfeq. apply e. auto.
  - bool_hyps; repeat simpl_sumbool.
    nested_ind_case; [inversion H0|].
    rewrite all2_cons in H2; bool_hyps.
    simpl_set_small. destruct H0.
    + apply (Hp p); auto.
    + apply (IHps Hforall H0 _ H3); auto.
  - destruct H.
  - simpl_set. bool_hyps.
    destruct H; [apply (IHp1_1 p2_1) | apply (IHp1_2 p2_2)]; auto.
  - simpl_set. bool_hyps.
    simpl_set. destruct H as [Hinx | [Hxv | []]]; subst.
    + apply (IHp1 _ H1); auto.
    + apply Hfeq in H2; subst.
      simpl_sumbool.
Qed.

(*If we map a function over the variables of a pattern,
  if the function agrees with vars and mantains types,
  the two patterns are alpha equivalent*)
Lemma map_pat_alpha_equiv vars p1 f
  (Hf1: forall x, In x (pat_fv p1) ->
    snd x = snd (f x))
  (Hf2: forall x, In x (pat_fv p1) ->
    var_in_firstb (x, (f x)) vars):
  alpha_equiv_p vars p1 (map_pat f p1).
Proof.
  intros; induction p1; simpl; auto.
  - rewrite Hf1; simpl; auto.
    rewrite eq_dec_refl, Hf2; simpl; auto.
  - rewrite !eq_dec_refl, map_length, Nat.eqb_refl. simpl.
    induction ps; simpl; intros; auto.
    rewrite all2_cons; inversion H; subst.
    rewrite H2; simpl.
    + apply IHps; auto; simpl.
      * intros; apply Hf1; simpl; simpl_set; triv.
      * intros; apply Hf2; simpl; simpl_set; triv.
    + intros; apply Hf1; simpl; simpl_set; triv.
    + intros; apply Hf2; simpl; simpl_set; triv.
  - rewrite IHp1_1, IHp1_2; auto; intros;
    [apply Hf1 | apply Hf2 | apply Hf1 | apply Hf2];
    simpl; simpl_set; triv.
  - rewrite Hf1, eq_dec_refl, Hf2, IHp1; simpl; auto;
    intros; [apply Hf1 | apply Hf2 | |]; simpl; simpl_set; auto.
Qed.

(*So now we need a map that is injective over free vars of p1
  AND maps all var_in_firstb pairs of variables from vars
  together. This is not too hard, using what we have*)

(*Now we provide a new definition of [mk_fun] that does not
  require the lists to be of the same length but still has
  the property we want*)
Definition mk_fun_gen (l1 l2: list vsymbol) (x: vsymbol) : vsymbol :=
  let n1 := length l1 in
  let n2 := length l2 in
  let l2' := if (n2 <? n1) then l2 ++
    gen_vars (n1 - n2) l2 else l2 in
  mk_fun l1 l2' x.

Lemma mk_fun_gen_inj (l1 l2: list vsymbol):
  NoDup l1 ->
  NoDup l2 ->
  forall x y,
    In x l1 -> In y l1 -> mk_fun_gen l1 l2 x = mk_fun_gen l1 l2 y -> x = y.
Proof.
  intros. unfold mk_fun_gen in H3. apply mk_fun_inj in H3; auto.
  - destruct (length l2 <? length l1); auto.
    apply add_notin_nodup; auto.
    apply nth_vs_inj.
  - destruct (Nat.ltb_spec0 (length l2) (length l1)); try lia.
    rewrite app_length, gen_vars_length. lia.
Qed.

Lemma mk_fun_in_firstb (l1 l2 l3: list vsymbol) x y:
  var_in_firstb (x, y) (combine l1 l2) ->
  mk_fun l1 (l2 ++ l3) x = y.
Proof.
  revert l2. induction l1; simpl; intros;[inversion H |].
  destruct l2; [inversion H |]. (*Why we need this and NOT var_eqb!*) 
  simpl. simpl in H.
  vsym_eq x a; simpl in H.
  - vsym_eq y v. inversion H.
  - apply IHl1. bool_hyps; auto.
Qed.

Lemma mk_fun_gen_in_firstb (l1 l2: list vsymbol):
  forall x y,
    var_in_firstb (x, y) (combine l1 l2) ->
    y = mk_fun_gen l1 l2 x.
Proof.
  revert l2. induction l1; simpl; intros; auto; [inversion H |].
  destruct l2; [inversion H|].
  simpl in H.
  unfold mk_fun_gen in *. simpl.
  specialize (IHl1 l2 x y).
  rewrite Nat_eqb_S.
  destruct (length l2 <? length l1) eqn: Hlen.
  - vsym_eq x a; simpl in H.
    + vsym_eq y v. inversion H.
    + vsym_eq y v; try solve[inversion H].
      simpl in H.
      rewrite mk_fun_in_firstb with(y:=y); auto.
  - vsym_eq x a; simpl in H.
    + vsym_eq y v. inversion H.
    + vsym_eq y v.
Qed.

(*Now we put everything together*)
(*We don't really care what the function is, except that it
  is injective*)
Lemma alpha_equiv_p_fv (l1 l2: list vsymbol) 
  (p1 p2: pattern)
  (Hn1: NoDup l1)
  (Hn2: NoDup l2)
  (Hl1: forall x, In x (pat_fv p1) -> In x l1)
  (Heq: alpha_equiv_p (combine l1 l2) p1 p2):
  pat_fv p2 = map (mk_fun_gen l1 l2) (pat_fv p1).
Proof.
  apply alpha_equiv_p_map with(f:=mk_fun_gen l1 l2) in Heq.
  - rewrite Heq at 1. 
    rewrite map_pat_free_vars; auto.
    intros. apply mk_fun_gen_inj in H1; auto.
  - intros. apply mk_fun_gen_in_firstb; auto.
Qed.

Lemma mk_fun_vars_eq (l1 l2: list vsymbol)
  (p1 p2: pattern)
  (Hn1: NoDup l1)
  (Hn2: NoDup l2)
  (Hl1: forall x, In x (pat_fv p1) -> In x l1)
  (Heq: alpha_equiv_p (combine l1 l2) p1 p2):
  forall x, In x (pat_fv p1) ->
  snd (mk_fun_gen l1 l2 x) = snd x.
Proof.
  intros. symmetry. 
  eapply alpha_equiv_p_map_f. apply Heq.
  intros; apply mk_fun_gen_in_firstb; auto.
  auto.
Qed.

(*We need these results to know how the free variables and
  length of fv lists are related in some inductive cases.
  Mostly, we use the specific list vars = combine (pat_fv p1) (pat_fv p2),
  so we prove these results, which are not true inductively
  (Hence, why we need the stronger lemmas)*)

Lemma mk_fun_vars_eq_full (p1 p2: pattern)
  (Heq: alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2):
  forall x, In x (pat_fv p1) ->
  snd (mk_fun_gen (pat_fv p1) (pat_fv p2) x) = snd x.
Proof.
  intros. apply (mk_fun_vars_eq _ _ p1 p2); auto;
  apply NoDup_pat_fv.
Qed. 

(*Version with vars*)
Corollary alpha_equiv_p_fv' (vars: list (vsymbol * vsymbol))
  (p1 p2: pattern)
  (Hn1: NoDup (map fst vars))
  (Hn2: NoDup (map snd vars))
  (Hl1: forall x, In x (pat_fv p1) -> In x (map fst vars))
  (Heq: alpha_equiv_p vars p1 p2):
  pat_fv p2 = map (mk_fun_gen (map fst vars) (map snd vars)) (pat_fv p1).
Proof.
  apply alpha_equiv_p_fv; auto.
  rewrite combine_eq; auto.
Qed.

Corollary alpha_equiv_p_fv_len  (l1 l2: list vsymbol) 
  (p1 p2: pattern)
  (Hn1: NoDup l1)
  (Hn2: NoDup l2)
  (Hl1: forall x, In x (pat_fv p1) -> In x l1)
  (Heq: alpha_equiv_p (combine l1 l2) p1 p2):
  length (pat_fv p1) = length (pat_fv p2).
Proof.
  rewrite (alpha_equiv_p_fv l1 l2 p1 p2); wf_tac.
Qed.

Corollary alpha_equiv_p_fv_len' (vars: list (vsymbol * vsymbol))
  (p1 p2: pattern)
  (Hn1: NoDup (map fst vars))
  (Hn2: NoDup (map snd vars))
  (Hl1: forall x, In x (pat_fv p1) -> In x (map fst vars))
  (Heq: alpha_equiv_p vars p1 p2):
  length (pat_fv p1) = length (pat_fv p2).
Proof.
  rewrite (alpha_equiv_p_fv' vars p1 p2); wf_tac.
Qed.

(*For the condition we use in [alpha_equiv_t]*)
Corollary alpha_equiv_p_fv_full (p1 p2: pattern):
  alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2 ->
  pat_fv p2 = map (mk_fun_gen (pat_fv p1) (pat_fv p2)) (pat_fv p1).
Proof.
  intros.
  apply alpha_equiv_p_fv; auto; apply NoDup_pat_fv.
Qed.

(*This result is extremely useful for us*)
Corollary alpha_equiv_p_fv_len_full (p1 p2: pattern):
  alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2 ->
  length (pat_fv p1) = length (pat_fv p2).
Proof.
  intros.
  rewrite (alpha_equiv_p_fv_full p1 p2); auto. 
  rewrite map_length; auto.
Qed.

End PatEquivFv.

(*Now we have some results about [match_val_single]
  and pattern alpha equivalence*)

Ltac simpl_proj :=
  simpl projT1; simpl projT2; simpl proj1_sig; simpl proj2_sig.

(*If two patterns are alpha-equivalent, then if the first pattern
  doesn't match, neither does the second.
  The constructor case has giant proof terms and takes a while,
  though it is conceptually simple*)
Lemma match_val_single_alpha_p_none {ty: vty}
(Hval Hval2: valid_type sigma ty)
(d: domain (dom_aux pd) (v_subst (v_typevar vt) ty))
(p1 p2: pattern)
(vars: list (vsymbol * vsymbol))
(Heq: alpha_equiv_p vars p1 p2) :
match_val_single gamma_valid pd all_unif vt ty Hval d p1 = None ->
match_val_single gamma_valid pd all_unif vt ty Hval2 d p2 = None.
Proof.
  revert ty d Hval Hval2.
  generalize dependent p2. induction p1.
  - simpl; intros; alpha_case p2 Heq.
    bool_hyps. simpl_sumbool.
    destruct (vty_eq_dec (snd v) ty); subst; auto;[inversion H|].
    destruct (vty_eq_dec (snd v0) ty); subst; auto.
    rewrite e in n; contradiction.
  - intros; destruct p2; try solve[inversion Heq].
    revert H0.
    simpl in Heq.
    revert Heq; bool_to_prop.
    intros [[[Hfeq Hps] Htys] Hall]. repeat simpl_sumbool.
    apply Nat.eqb_eq in Hps.
    rename l0 into ps2.
    rename l into tys.
    rename f0 into f.
    (*Get Hall into more usable form*)
    rewrite fold_is_true in Hall.
    rewrite all2_forall with(d1:=Pwild)(d2:=Pwild) in Hall; auto.
    (*Now deal with main result*)
    unfold match_val_single; fold (match_val_single gamma_valid).
    (*The hard case: need lots of generalization for dependent types
    and need nested induction*) 
    generalize dependent (is_sort_adt_spec gamma_valid (v_subst (v_typevar vt) ty)).
    generalize dependent ((@adt_srts_length_eq _ _ gamma_valid vt ty)).
    generalize dependent (@adts_srts_valid _ _ gamma_valid vt ty).
    destruct (is_sort_adt (v_subst (v_typevar vt) ty)) eqn : Hisadt; [|solve[auto]].
    intros Hsrtsvalid Hsrtslen Hadtspec.
    destruct p as [[[m adt] ts] srts].
    destruct (Hadtspec m adt ts srts eq_refl) as 
      [Hvaleq [Hinmut [Hincts Htseq]]].
    assert (Hlenpeq : (Hsrtslen m adt ts srts eq_refl Hval) =
    (Hsrtslen m adt ts srts eq_refl Hval2)). {
      apply UIP_dec. apply Nat.eq_dec.
    }
    rewrite <- !Hlenpeq.
    destruct (funsym_eq_dec
    (projT1
      (find_constr_rep gamma_valid m Hincts srts
          (Hsrtslen m adt ts srts eq_refl Hval) (dom_aux pd) adt
          Hinmut (adts pd m srts) (all_unif m Hincts)
          (scast (adts pd m srts adt Hinmut)
            (dom_cast (dom_aux pd) Hvaleq d)))) f);[|solve[auto]].
    clear Hlenpeq.
    (*Need nested induction: simplify first*)
    generalize dependent (find_constr_rep gamma_valid m Hincts srts
    (Hsrtslen m adt ts srts eq_refl Hval) 
    (dom_aux pd) adt Hinmut (adts pd m srts)
    (all_unif m Hincts)
    (scast (adts pd m srts adt Hinmut)
      (dom_cast (dom_aux pd) Hvaleq d))).
    intros constr. destruct constr as [f' Hf']. 
    simpl_proj. intros Hf; subst.
    generalize dependent ((Hsrtsvalid m adt (adt_name adt) srts f eq_refl Hval (fst (proj1_sig Hf')))).
    generalize dependent ((Hsrtsvalid m adt (adt_name adt) srts f eq_refl Hval2 (fst (proj1_sig Hf')))).
    destruct Hf'. simpl_proj. clear e.
    destruct x. generalize dependent a.
    generalize dependent ps2.
    generalize dependent ps. 
    generalize dependent ((funsym_sigma_args f srts)).
    induction l; intros. 
    + destruct ps. inversion H0. destruct ps2; inversion Hps. 
      reflexivity.
    + destruct ps; destruct ps2; inversion Hps; auto.
      revert H0.
      case_match_hyp.
      intro C; inversion C.
      * (*First succeeds, rest fail*)
        intros _.
        case_match_goal.
        (*Contradicts IH*)
        eapply IHl in Hmatch0.
        rewrite Hmatch0 in Hmatch2. inversion Hmatch2.
        -- clear Hmatch Hmatch0 Hmatch1 Hmatch2 IHl.
          inversion H; subst; auto.
        -- assumption.
        -- intros j Hj; apply (Hall (S j)). simpl; lia.
      * (*first fails *) 
        intros _.
        case_match_goal.
        (*Contradicts fact that both need to be equivalent - from
          original IH (behind the giant proof terms)*)
        inversion H; subst.
        eapply H3 in Hmatch.
        rewrite Hmatch in Hmatch0. inversion Hmatch0.
        apply (Hall 0). simpl; lia.
  - intros. destruct p2; try solve[inversion Heq].
    inversion H.
  - simpl; intros. destruct p2; try solve[inversion Heq].
    revert Heq. bool_to_prop; intros [Hp1 Hp2].
    simpl.
    revert H. case_match_hyp; [intro C; inversion C|].
    intros. eapply IHp1_1 in Hmatch. rewrite Hmatch. 2: assumption.
    eapply IHp1_2. auto. apply H.
  - simpl; intros. destruct p2; try solve[inversion Heq]. simpl.
    revert Heq; bool_to_prop; intros [[Htys Heq] Hp12]; simpl_sumbool.
    revert H. case_match_hyp.
    + destruct (vty_eq_dec (snd v) ty); [intro C; inversion C |].
      intros _.
      case_match_goal. destruct (vty_eq_dec (snd v0) ty); auto.
      subst. rewrite e in n. contradiction.
    + intros _. erewrite IHp1; auto. apply Hmatch.
Qed.

(*Now we resume definition of alpha equivalence for terms
  and formulas*)

Definition add_vals {A B: Type} (keys: list A) (vals: list B) (assoc: list (A * B)) :
  list (A * B) :=
  combine keys vals ++ assoc.

(*The definition of alpha equivalence - in the var case,
  we use [eq_var], which enforces that the mapping must either
  appear in the list as the first ocurrence of each variable,
  or the variables are the same*)
Fixpoint alpha_equiv_t (vars: list (vsymbol * vsymbol)) (t1 t2: term) : bool :=
  match t1, t2 with
  | Tconst c1, Tconst c2 => (*TODO: not great - because of
    equality of real numbers*) all_dec (c1 = c2)
  | Tvar v1, Tvar v2 =>
    eq_var vars v1 v2
  | Tfun f1 ty1 tm1, Tfun f2 ty2 tm2 =>
    (funsym_eq_dec f1 f2) &&
    (length tm1 =? length tm2) && 
    (list_eq_dec vty_eq_dec ty1 ty2) &&
    (all2 (fun t1 t2 => alpha_equiv_t vars t1 t2)) tm1 tm2
  | Tlet tm1 x tm2, Tlet tm3 y tm4 =>
    vty_eq_dec (snd x) (snd y) &&
    alpha_equiv_t vars tm1 tm3 &&
    alpha_equiv_t ((x, y) :: vars) tm2 tm4
  | Tif f1 t1 t3, Tif f2 t2 t4 =>
    alpha_equiv_f vars f1 f2 &&
    alpha_equiv_t vars t1 t2 &&
    alpha_equiv_t vars t3 t4
  | Tmatch t1 ty1 ps1, Tmatch t2 ty2 ps2 =>
    alpha_equiv_t vars t1 t2 &&
    (length ps1 =? length ps2) &&
    (vty_eq_dec ty1 ty2) &&
    all2 (fun (x1 x2: pattern * term) =>
      alpha_equiv_p (combine (pat_fv (fst x1)) (pat_fv (fst x2)))
        (fst x1) (fst x2) &&
      alpha_equiv_t (add_vals (pat_fv (fst x1)) (pat_fv (fst x2)) vars)
        (snd x1) (snd x2)) ps1 ps2
  | Teps f1 x, Teps f2 y => 
    vty_eq_dec (snd x) (snd y) &&
    alpha_equiv_f ((x, y) :: vars) f1 f2
  | _, _ => false
  end
with alpha_equiv_f (vars: list (vsymbol * vsymbol)) (f1 f2: formula) {struct f1} : bool :=
  match f1, f2 with
  | Fpred p1 ty1 tm1, Fpred p2 ty2 tm2 =>
    (predsym_eq_dec p1 p2) &&
    (length tm1 =? length tm2) && 
    (list_eq_dec vty_eq_dec ty1 ty2) &&
    (all2 (fun t1 t2 => alpha_equiv_t vars t1 t2)) tm1 tm2
  | Fquant q1 x f1, Fquant q2 y f2 =>
    quant_eq_dec q1 q2 &&
    vty_eq_dec (snd x) (snd y) &&
    alpha_equiv_f ((x, y) :: vars) f1 f2
  | Feq ty1 t1 t3, Feq ty2 t2 t4 =>
    vty_eq_dec ty1 ty2 &&
    alpha_equiv_t vars t1 t2 &&
    alpha_equiv_t vars t3 t4
  | Fbinop b1 f1 f3, Fbinop b2 f2 f4 =>
    binop_eq_dec b1 b2 &&
    alpha_equiv_f vars f1 f2 &&
    alpha_equiv_f vars f3 f4
  | Fnot f1, Fnot f2 =>
    alpha_equiv_f vars f1 f2
  | Ftrue, Ftrue => true
  | Ffalse, Ffalse => true
  | Flet t1 x f1, Flet t2 y f2 =>
    vty_eq_dec (snd x) (snd y) &&
    alpha_equiv_t vars t1 t2 &&
    alpha_equiv_f ((x, y) :: vars) f1 f2
  | Fif f1 f3 f5, Fif f2 f4 f6 =>
    alpha_equiv_f vars f1 f2 &&
    alpha_equiv_f vars f3 f4 &&
    alpha_equiv_f vars f5 f6
  | Fmatch t1 ty1 ps1, Fmatch t2 ty2 ps2 =>
    alpha_equiv_t vars t1 t2 &&
    (length ps1 =? length ps2) &&
    (vty_eq_dec ty1 ty2) &&
    all2 (fun (x1 x2: pattern * formula) =>
      alpha_equiv_p (combine (pat_fv (fst x1)) (pat_fv (fst x2)))
        (fst x1) (fst x2) &&
      alpha_equiv_f (add_vals (pat_fv (fst x1)) (pat_fv (fst x2)) vars)
        (snd x1) (snd x2)) ps1 ps2
  | _, _ => false
  end.

(*Full alpha equivalence: when there are no vars in the
  context*)
Definition a_equiv_t: term -> term -> bool :=
  alpha_equiv_t nil.
Definition a_equiv_f: formula -> formula -> bool :=
  alpha_equiv_f nil.
  

(*First, we prove that alpha equivalence implies equal
  denotations. To do this, we first need results about 
  [alpha_equiv_p] and [match_val_single]*)
Section AlphaEquivDenotational.

Section DenotPat.

(*Symmetry on [alpha_equiv_p]*)

Lemma alpha_equiv_p_sym (p1 p2: pattern)
  (vars: list (vsymbol * vsymbol)):
  alpha_equiv_p vars p1 p2 = alpha_equiv_p (flip vars) p2 p1.
Proof.
  revert p2. induction p1; simpl; intros; destruct p2; auto; simpl.
  - rewrite eq_dec_sym, var_in_firstb_flip. reflexivity.
  - rewrite eq_dec_sym, Nat.eqb_sym.
    destruct (length l0 =? length ps) eqn : Hlen; simpl_bool; auto.
    f_equal; [f_equal; apply eq_dec_sym |].
    rewrite Nat.eqb_sym in Hlen.
    nested_ind_case.
    rewrite !all2_cons, (Hp p), (IHps Hforall _ H1).
    reflexivity.
  - rewrite IHp1_1, IHp1_2. reflexivity.
  - rewrite eq_dec_sym, IHp1. do 2 f_equal.
    apply var_in_firstb_flip.
Qed.

(*From the symmetry, we get that [match_val_single] are either
  always both None or both Some*)
Lemma match_val_single_alpha_p_none_iff {ty: vty}
  (Hval Hval2: valid_type sigma ty)
  (d: domain (dom_aux pd) (v_subst (v_typevar vt) ty))
  (p1 p2: pattern)
  (vars: list (vsymbol * vsymbol))
  (Heq: alpha_equiv_p vars p1 p2):
  match_val_single gamma_valid pd all_unif vt ty Hval d p1 = None <->
  match_val_single gamma_valid pd all_unif vt ty Hval2 d p2 = None.
Proof.
  split; intros.
  - apply (match_val_single_alpha_p_none Hval _ _ _ _ _ Heq); auto.
  - apply (match_val_single_alpha_p_none Hval2 _ _ p2 _ (flip vars)); auto.
    rewrite <- alpha_equiv_p_sym; auto.
Qed.

(*Now we will do the Some case - if two alpha equivalent patterns
  both match (and we know this is iff), then
  the bindings are the same, for the (x, y) pairs in vars*)
Lemma match_val_single_alpha_p_some {ty: vty}
  (Hval Hval2: valid_type sigma ty)
  (d: domain (dom_aux pd) (v_subst (v_typevar vt) ty))
  (p1 p2: pattern)
  (vars: list (vsymbol * vsymbol))
  (Heq: alpha_equiv_p vars p1 p2)
  (Hnodup1: NoDup (map fst vars))
  (Hnodup2: NoDup (map snd vars))
  l1 l2 x y t (def: vsymbol):
  match_val_single gamma_valid pd all_unif vt ty Hval d p1 = Some l1 ->
  match_val_single gamma_valid pd all_unif vt ty Hval2 d p2 = Some l2 ->
  In (x, y) vars ->
  In (x, t) l1 <-> In (y, t) l2.
Proof.
  revert ty d Hval Hval2 l1 l2.
  generalize dependent p2. induction p1.
  - simpl; intros; destruct p2; try solve[inversion Heq].
    simpl in *.
    revert Heq; bool_to_prop; intros [Htys Heq].
    repeat simpl_sumbool.
    destruct (vty_eq_dec (snd v) ty); subst; inversion H.
    destruct (vty_eq_dec (snd v0) (snd v)); subst; inversion H0.
    subst. clear H. clear H0. simpl.
    apply or_iff_compat_r. split; intros Heq'; inversion Heq'; subst;
    f_equal.
    + apply (in_firstb_in_eq _ _ _ _ Hnodup1 Heq); auto.
    + apply (in_firstb_in_eq_r _ _ _ _ Hnodup2 Heq); auto.
  - (*Constr case, let's see how awful this is*)
    intros; destruct p2; try solve[inversion Heq].
    revert H0 H1.
    simpl in Heq.
    revert Heq; bool_to_prop.
    intros [[[Hfeq Hps] Htys] Hall]. repeat simpl_sumbool.
    apply Nat.eqb_eq in Hps.
    rename l0 into ps2.
    rename l into tys.
    rename f0 into f.
    (*Get Hall2 into more usable form*)
    rewrite fold_is_true in Hall.
    rewrite all2_forall with(d1:=Pwild)(d2:=Pwild) in Hall; auto.
    (*Now deal with main result*)
    unfold match_val_single; fold (match_val_single gamma_valid).
    (*The hard case: need lots of generalization for dependent types
    and need nested induction*) 
    generalize dependent (is_sort_adt_spec gamma_valid (v_subst (v_typevar vt) ty)).
    generalize dependent ((@adt_srts_length_eq _ _ gamma_valid vt ty)).
    generalize dependent (@adts_srts_valid _ _ gamma_valid vt ty).
    destruct (is_sort_adt (v_subst (v_typevar vt) ty)) eqn : Hisadt;[|intros; solve[inversion H0]].
    intros Hsrtsvalid Hsrtslen Hadtspec.
    destruct p as [[[m adt] ts] srts].
    destruct (Hadtspec m adt ts srts eq_refl) as 
      [Hvaleq [Hinmut [Hincts Htseq]]].
    assert (Hlenpeq : (Hsrtslen m adt ts srts eq_refl Hval) =
    (Hsrtslen m adt ts srts eq_refl Hval2)). {
      apply UIP_dec. apply Nat.eq_dec.
    }
    rewrite <- !Hlenpeq.
    destruct (funsym_eq_dec
    (projT1
      (find_constr_rep gamma_valid m Hincts srts
          (Hsrtslen m adt ts srts eq_refl Hval) (dom_aux pd) adt
          Hinmut (adts pd m srts) (all_unif m Hincts)
          (scast (adts pd m srts adt Hinmut)
            (dom_cast (dom_aux pd) Hvaleq d)))) f);[|intros; solve[inversion H0]].
    clear Hlenpeq.
    (*Need nested induction: simplify first*)
    generalize dependent (find_constr_rep gamma_valid m Hincts srts
    (Hsrtslen m adt ts srts eq_refl Hval) 
    (dom_aux pd) adt Hinmut (adts pd m srts)
    (all_unif m Hincts)
    (scast (adts pd m srts adt Hinmut)
      (dom_cast (dom_aux pd) Hvaleq d))).
    intros constr. destruct constr as [f' Hf']. 
    simpl_proj. intros Hf; subst.
    generalize dependent ((Hsrtsvalid m adt (adt_name adt) srts f eq_refl Hval (fst (proj1_sig Hf')))).
    generalize dependent ((Hsrtsvalid m adt (adt_name adt) srts f eq_refl Hval2 (fst (proj1_sig Hf')))).
    destruct Hf'. simpl_proj. clear e.
    destruct x0. generalize dependent a.
    generalize dependent ps2.
    generalize dependent ps. 
    revert l1. revert l2.
    generalize dependent ((funsym_sigma_args f srts)).
    induction l; intros. 
    + destruct ps; [|inversion H0]. destruct ps2; inversion Hps.
      inversion H0; inversion H1; subst. reflexivity. 
    + destruct ps; destruct ps2; inversion Hps; auto.
      inversion H0.
      revert H0 H1.
      case_match_hyp.
      all: intro Hls; inversion Hls. subst.
      case_match_hyp.
      all: intro Hls2; inversion Hls2. subst.
      (*We handle the first case and the IH separately*)
      apply in_app_iff_simpl.
      * (*from original IH*) clear Hmatch2 Hmatch0 Hls Hls2.
        inversion H; subst.
        eapply H3.
        2: apply Hmatch.
        2: apply Hmatch1.
        2: auto.
        apply (Hall 0). simpl; lia.
      * (*from constr IH*) clear Hmatch Hmatch1. 
        inversion H; subst.
        eapply IHl.
        4: apply Hmatch0.
        4: apply Hmatch2.
        all: auto.
        intros j Hj; apply (Hall (S j)). simpl; lia.
  - (*hard case done, now we can do the rest*)
    intros. destruct p2; try solve[inversion Heq].
    inversion H; inversion H0; subst. reflexivity.
  - simpl; intros. destruct p2; try solve[inversion Heq]. 
    revert Heq.  bool_to_prop; intros [Hp1 Hp2].
    simpl.
    revert H H0; simpl. case_match_hyp.
    + intro Hl; inversion Hl; subst.
      case_match_hyp.
      * intros Hl'; inversion Hl'; subst.
        eapply IHp1_1. apply Hp1. apply Hmatch. apply Hmatch0. auto.
      * assert (match_val_single gamma_valid pd all_unif vt ty Hval d p1_1 = None).
        rewrite match_val_single_alpha_p_none_iff. apply Hmatch0. apply Hp1. all: auto.
        rewrite H in Hmatch; inversion Hmatch.
    + intros Hmatch1. case_match_hyp.
      * (*another contradiction, both should be None*)
        rewrite match_val_single_alpha_p_none_iff in Hmatch.
        2: apply Hp1. rewrite Hmatch in Hmatch0. inversion Hmatch0.
        all: auto.
      * intros.
        eapply IHp1_2. apply Hp2. apply Hmatch1. apply H0. auto.
  - simpl; intros. destruct p2; try solve[inversion Heq].
    simpl in H0.
    revert Heq; bool_to_prop; intros [[Htys Heq] Hp12]; simpl_sumbool.
    revert H H0. case_match_hyp; [|intro C; inversion C].
    destruct (vty_eq_dec (snd v) ty); [| intro C; inversion C].
    intros Hl1; inversion Hl1; subst.
    case_match_hyp; [|intro C; inversion C].
    destruct (vty_eq_dec (snd v0) (snd v)); subst. 2: { rewrite e in n; contradiction. }
    simpl. intros Hl2; inversion Hl2; subst. simpl.
    apply or_iff.
    + split; intros Heq'; inversion Heq'; subst; f_equal.
      apply (in_firstb_in_eq _ _ _ _ Hnodup1 Heq); auto.
      apply (in_firstb_in_eq_r _ _ _ _ Hnodup2 Heq); auto.
    + eapply IHp1. apply Hp12. apply Hmatch. apply Hmatch0. auto.
Qed.

End DenotPat.

(*Now, we show that terms/formulas which are alpha equivalent
  have equivalent denotations. This is very annoying to prove.
  The pattern match case, understandably, is the hardest.*)
Lemma alpha_equiv_equiv (t: term) (f: formula) :
  (forall (t2: term) (vars: list (vsymbol * vsymbol)) 
  (v1 v2: val_vars pd vt) (ty: vty)
  (Hty: term_has_type sigma t ty)
  (Hty2: term_has_type sigma t2 ty)
  (Heq: alpha_equiv_t vars t t2)
  (Hvals: forall x y (Heq: snd x = snd y),
    (*This is the first binding for x and for y*)
    var_in_firstb (x, y) vars ->
    v1 x = (dom_cast _ (f_equal _ (eq_sym Heq))
    (v2 y)))
  (Hvals2: forall x,
    (~In x (map fst vars) /\ ~ In x (map snd vars)) ->
    v1 x = v2 x),
  term_rep v1 t ty Hty =
  term_rep v2 t2 ty Hty2) /\
  (forall (f2: formula) (vars: list (vsymbol * vsymbol))  
  (v1 v2: val_vars pd vt)
  (Hval: valid_formula sigma f)
  (Hval2: valid_formula sigma f2)
  (Heq: alpha_equiv_f vars f f2)
  (Hvals: forall x y (Heq: snd x = snd y),
    var_in_firstb (x, y) vars ->
    v1 x = (dom_cast _ (f_equal _ (eq_sym Heq))
    (v2 y)))
  (Hvals2: forall x,
    (~In x (map fst vars) /\ ~ In x (map snd vars)) ->
    v1 x = v2 x),
  formula_rep v1 f Hval =
  formula_rep v2 f2 Hval2).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; auto.
  - (*Tconst*)
    alpha_case t2 Heq. 
    rewrite simpl_all_dec in Heq. subst.
    erewrite term_fv_agree. apply term_rep_irrel.
    simpl. intros; destruct H.
  - (*Tvar - harder*) 
    alpha_case t2 Heq.
    rewrite eq_var_eq in Heq. bool_hyps.
    destruct Heq; bool_hyps; repeat simpl_sumbool.
    + inversion Hty; inversion Hty2; subst.
      specialize (Hvals _ _ (eq_sym H7) H).
      rewrite !tvar_rep. unfold var_to_dom.
      rewrite Hvals.
      (*Now need to deal with casts: this is annoying*)
      unfold dom_cast.
      destruct v0; simpl in *.
      subst. simpl.
      assert ((ty_var_inv (has_type_eq eq_refl Hty)) = eq_refl) by
        (apply UIP_dec; apply vty_eq_dec).
      rewrite H0. simpl.
      assert ((ty_var_inv (has_type_eq eq_refl Hty2)) = eq_refl) by
        (apply UIP_dec; apply vty_eq_dec).
      rewrite H1. reflexivity.
    + erewrite term_fv_agree. apply term_rep_irrel. simpl.
      intros. destruct H as [Heq | []]; subst.
      apply Hvals2. split; auto.
  - (*Tfun*)
    alpha_case t2 Heq. bool_hyps; repeat simpl_sumbool.
    rename H3 into Hlen; rename H1 into Hall.
    apply Nat.eqb_eq in Hlen.
    rewrite !tfun_rep.
    (*Deal with casting*)
    f_equal; [apply UIP_dec; apply vty_eq_dec |].
    f_equal; [apply UIP_dec; apply sort_eq_dec |].
    f_equal.
    (*Now prove that arg_lists equivalent*)
    apply get_arg_list_ext; wf_tac.
    rewrite fold_is_true in Hall.
    rewrite all2_forall with(d1:=tm_d)(d2:=tm_d) in Hall; auto.
    intros. rewrite Forall_forall in H. 
    apply H with(vars:=vars); wf_tac.
  - (*Tlet - harder case*)
    alpha_case t2 Heq. 
    rename t2_1 into tm3. rename t2_2 into tm4.
    rename v into x. rename v0 into y.
    bool_hyps; simpl_sumbool.
    rename H3 into Ha1; rename H2 into Ha2.
    rewrite !tlet_rep.
    inversion Hty; inversion Hty2; subst.
    apply H0 with (vars:=(x, y) :: vars); auto.
    + simpl. intros. bool_hyps.
      destruct H1; bool_hyps; repeat simpl_sumbool.
      * unfold substi.
        vsym_eq x x. vsym_eq y y.
        unfold eq_rec_r, eq_rec, eq_rect, dom_cast.
        assert (e0 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        assert (e1 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        rewrite H1, H2. simpl. clear e0 e1 H1 H2.
        destruct x; destruct y; simpl in *; subst.
        assert (Heq = eq_refl) by (apply UIP_dec; apply vty_eq_dec).
        rewrite H1; simpl.
        apply H with(vars:=vars); auto.
      * unfold substi. vsym_eq x0 x. vsym_eq y0 y.
    + (*prove Hvals2*)
      simpl. intros.
      unfold substi. destruct H1 as [Hnotx Hnoty].
      not_or Hx0.
      vsym_eq x0 x. vsym_eq x0 y.
  - (*Tif*)
    alpha_case t0 Heq.
    bool_hyps.
    rewrite !tif_rep. 
    rewrite (H _ _ _ v2 _ (proj2 (proj2 (ty_if_inv (has_type_eq eq_refl Hty2)))) H2),
      (H0 _ _ _ v2 _ _ (proj1 (ty_if_inv (has_type_eq eq_refl Hty2))) H4),
      (H1 _ _ _ v2 _ _ (proj1 (proj2 (ty_if_inv (has_type_eq eq_refl Hty2)))) H3); auto.
  - (*Tmatch - predictably, this is the hard case*)
    alpha_case t2 Heq.
    rename t2 into tm2.
    rename v into tys.
    rename v0 into tys2.
    rename l into ps2.
    bool_hyps; repeat simpl_sumbool.
    rename H1 into Htm; rename H4 into Hps; rename H2 into Hall.
    apply Nat.eqb_eq in Hps.
    rewrite fold_is_true in Hall.
    rewrite all2_forall with(d1:=(Pwild, tm_d))(d2:=(Pwild, tm_d)) in Hall; auto.
    rewrite !tmatch_rep.
    (*Need nested induction here*)
    generalize dependent (proj1 (ty_match_inv (has_type_eq eq_refl Hty))).
    generalize dependent (proj2 (ty_match_inv (has_type_eq eq_refl Hty))).
    generalize dependent (proj1 (ty_match_inv (has_type_eq eq_refl Hty2))).
    generalize dependent (proj2 (ty_match_inv (has_type_eq eq_refl Hty2))).
    inversion Hty2; subst. clear H4 H8 H9 Hty2.
    inversion Hty; subst. clear H4 H9 H10 Hty.
    generalize dependent tys2.
    generalize dependent ps2.
    
    induction ps; simpl; intros; destruct ps2; inversion Hps; auto.
    destruct a. simpl.
    destruct p. simpl.
    rewrite <- (H _ _ v1 v2 _ t0 t Htm) at 1; auto.
    (*Now need to know [match_val_single] is same - separate lemmas*)
    destruct (match_val_single gamma_valid pd all_unif vt tys2
    (has_type_valid gamma_valid tm tys2 t0) (term_rep v1 tm tys2 t0) p0) eqn : Hmatch1.
    + (*In Some case, need to know how lists relate*)

      (*First, get some info we need*)
      assert (Htyp: pattern_has_type sigma p tys2) by
        (apply (H6 (p, t2)); simpl; triv).
      assert (Htyp0: pattern_has_type sigma p0 tys2) by
        (apply (H7 (p0, t1)); simpl; triv).
      assert (Hpeq: alpha_equiv_p (combine (pat_fv p0) (pat_fv p)) p0 p). {
        specialize (Hall 0 ltac:(lia)); simpl in Hall.
        bool_hyps; auto.
      }
      pose proof (alpha_equiv_p_fv_len_full _ _ Hpeq) as Hlen2.
      destruct (match_val_single gamma_valid pd all_unif vt tys2
      (has_type_valid gamma_valid tm2 tys2 t) (term_rep v1 tm tys2 t0) p) eqn : Hmatch2.
      * assert (A:=Hall). specialize (A 0 ltac:(lia)); simpl in A.
        bool_hyps. rename H1 into Hp; rename H3 into Ht12.
        inversion H0; subst. eapply H4. apply Ht12.
        -- intros. 
          unfold add_vals in H1.
          rewrite in_firstb_app in H1.
          bool_hyps; destruct H1 as [Hinfv | H1]; bool_hyps.
          ++ (*Case 1: (x, y) are in free vars of p0 and p respectively.
            Then we use [match_val_single_alpha_p_some] and
            [match_val_single_nodup] to show that their valuations
            are the same.*)
            apply in_firstb_in in Hinfv.
            assert (Hincom:=Hinfv).
            rewrite in_combine_iff in Hinfv; wf_tac.
            destruct Hinfv as [i [Hi Hith]].
            specialize (Hith vs_d vs_d). inversion Hith.
            (*Now, we know that x is in l by 
              [match_val_single_free_var]*)
            assert (Hinxl: In x (map fst l)). {
              apply match_val_single_free_var with(x:=x)(ty':=tys2) in Hmatch1;
              auto.
              apply Hmatch1. subst. wf_tac.
            }
            rewrite in_map_iff in Hinxl. destruct Hinxl as [bnd [Hx Hinbnd]].
            destruct bnd as [x' t']. simpl in Hx. subst x'.
            (*Now, we use [match_val_single_alpha_p_some] to show
              that (y, t') is in l0*)
            assert (Hinyl: In (y, t') l0). {
              eapply match_val_single_alpha_p_some in Hmatch2.
              rewrite <- Hmatch2. apply Hinbnd. apply Hp.
              all: wf_tac. apply Hmatch1. 
            }
            (*Finally, we use NoDup of l, l0 
              (from [match_val_single_nodup]) to give the binding*)
            assert (Hnodup1: NoDup (map fst l)). {
              eapply match_val_single_nodup in Hmatch1.
              apply Hmatch1. apply Htyp0.
            }
            assert (Hnodup2: NoDup (map fst l0)). {
              eapply match_val_single_nodup in Hmatch2.
              apply Hmatch2. apply Htyp.
            }
            rewrite !extend_val_with_list_lookup with(t:=t'); auto.
            (*Now handle all the casting*)
            destruct (vty_eq_dec (snd x) (projT1 t')).
            ** destruct (vty_eq_dec (snd y) (projT1 t')).
              {
                destruct x. destruct y. simpl in *; subst. simpl.
                assert (e0 = eq_refl). apply UIP_dec. apply vty_eq_dec.
                rewrite H1. reflexivity. 
              }
              { 
                exfalso.
                rewrite Heq in e. contradiction.
              }
            ** (*contradiction case - types match in output
              by [match_val_single_typs]*)
              apply match_val_single_typs with(x:=x)(t:=t') in Hmatch1;
              auto. exfalso. rewrite Hmatch1 in n. contradiction.
              (*And we are done!*)
          ++ (*Now in the other case, neither are free vars, so
            we use Hvals2*)
            repeat simpl_sumbool.
            rewrite map_fst_combine in n0; wf_tac.
            rewrite map_snd_combine in n; wf_tac.
            assert (Hxl: ~ In x (map fst l)). {
              intro C. 
              apply match_val_single_free_var with(x:=x)(ty':=tys2) in Hmatch1;
              auto.
              apply Hmatch1 in C. contradiction.
            }
            assert (Hyl0: ~ In y (map fst l0)). {
              intro C.
              apply match_val_single_free_var with(x:=y)(ty':=tys2) in Hmatch2;
              auto.
              apply Hmatch2 in C; contradiction.
            }
            rewrite !extend_val_with_list_notin'; wf_tac.
        -- (*Here, we must show preservation of [Hvals2]*) 
          unfold add_vals.
          intros x. rewrite !map_app, !in_app_iff;
          intros [Hnotx1 Hnotx2].
          not_or Hnotx. rewrite map_fst_combine in Hnotx2; wf_tac.
          rewrite map_snd_combine in Hnotx; wf_tac.
          rewrite !extend_val_with_list_notin'; wf_tac;
          intro C.
          ++ apply match_val_single_free_var with(x:=x)(ty':=tys2) in Hmatch2;
            auto.
            apply Hmatch2 in C; contradiction.
          ++ apply match_val_single_free_var with(x:=x)(ty':=tys2) in Hmatch1;
            auto.
            apply Hmatch1 in C; contradiction.
      * (*Contradiction: both are Some or both are None*)
        exfalso.
        rewrite <- match_val_single_alpha_p_none_iff in Hmatch2.
        rewrite Hmatch2 in Hmatch1. inversion Hmatch1. apply Hpeq.
    + (*In None case, both None, use IH*) 
      assert (match_val_single gamma_valid pd all_unif vt tys2
      (has_type_valid gamma_valid tm2 tys2 t) (term_rep v1 tm tys2 t0) p
      = None). {
        eapply match_val_single_alpha_p_none. 2: apply Hmatch1.
        specialize (Hall 0 ltac:(lia)). simpl in Hall.
        bool_hyps; auto. apply H1.
      }
      rewrite H1. apply IHps; auto; clear IHps.
      * inversion H0; subst; auto.
      * intros j Hj; specialize (Hall (S j) ltac:(lia)); simpl in Hall;
        auto.
      * intros; apply H6; simpl; triv.
  - (*Teps - similar to Tlet*) 
    alpha_case t2 Heq.
    bool_hyps; simpl_sumbool.
    rename H1 into Heq.
    rewrite !teps_rep. f_equal. apply functional_extensionality_dep; intros.
    erewrite H. reflexivity. apply Heq.
    + (*Prove Hvals preserved*)
      intros. simpl in H0.
      bool_hyps; destruct H0; bool_hyps; repeat simpl_sumbool.
      * unfold substi. 
        (*Just annoying casting stuff*)
        vsym_eq v v. vsym_eq v0 v0.
        unfold eq_rec_r, eq_rec, eq_rect, dom_cast.
        assert (e0 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        assert (e1 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        rewrite H0, H1. simpl. clear e0 e1 H0 H1.
        generalize dependent (proj2 (ty_eps_inv (has_type_eq eq_refl Hty))).
        generalize dependent (proj2 (ty_eps_inv (has_type_eq eq_refl Hty2))).
        intros. subst. destruct v; simpl in *; subst; simpl.
        assert (e1 = eq_refl) by (apply UIP_dec; apply vty_eq_dec).
        assert (Heq0 = eq_refl) by (apply UIP_dec; apply vty_eq_dec).
        rewrite H0, H1. reflexivity.
      * unfold substi.
        vsym_eq x0 v. vsym_eq y v0.
    + (*prove Hvals2*)
      simpl. intros.
      unfold substi. destruct H0 as [Hnotx Hnoty]; not_or Hx0.
      vsym_eq x0 v. vsym_eq x0 v0.
  - (*Fpred - similar as Tfun*)
    alpha_case f2 Heq. bool_hyps; repeat simpl_sumbool.
    rename H3 into Hlen; rename H1 into Hall.
    apply Nat.eqb_eq in Hlen.
    rewrite !fpred_rep.
    f_equal.
    (*Now prove that arg_lists equivalent*)
    apply get_arg_list_pred_ext; wf_tac.
    rewrite fold_is_true in Hall.
    rewrite all2_forall with(d1:=tm_d)(d2:=tm_d) in Hall; auto.
    intros. rewrite Forall_forall in H. 
    apply H with(vars:=vars); wf_tac.
  - (*Fquant - similar to let cases*)
    alpha_case f2 Heq. bool_hyps; repeat simpl_sumbool.
    rename H1 into Heq.
    destruct v; destruct v0; simpl in *; subst.
    (*So we don't have to repeat proofs*)
    assert (Halleq: forall d,
      formula_rep (substi pd vt v1 (s, v0) d) f
        (valid_quant_inj (valid_formula_eq eq_refl Hval)) =
      formula_rep (substi pd vt v2 (s0, v0) d) f2
        (valid_quant_inj (valid_formula_eq eq_refl Hval2))). {
      intros. eapply H. apply Heq.
      - (*Prove Hval*) 
        intros. simpl in H0. bool_hyps; destruct H0; bool_hyps;
        repeat simpl_sumbool.
        + unfold substi. 
          (*Just annoying casting stuff*)
          vsym_eq (s, v0) (s, v0).
          vsym_eq (s0, v0) (s0, v0).
          unfold eq_rec_r, eq_rec, eq_rect, dom_cast.
          assert (e0 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
          assert (e = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
          assert (Heq0 = eq_refl) by (apply UIP_dec; apply vty_eq_dec).
          rewrite H0, H1, H2. reflexivity.
        + unfold substi. vsym_eq x (s, v0). vsym_eq y (s0, v0).
      - (*prove Hvals2*)
        simpl. intros.
        unfold substi. destruct H0; not_or Hx.
        vsym_eq x (s, v0). vsym_eq x (s0, v0).
    }
    destruct q0.
    + (*Tforall*)
      rewrite !fforall_rep. simpl.
      apply all_dec_eq. split; intros.
      * rewrite <- Halleq; auto.
      * rewrite Halleq; auto.
    + (*Texists*)
      rewrite !fexists_rep; simpl.
      apply all_dec_eq; split; intros [d Hrep]; exists d.
      * rewrite <- Halleq; auto.
      * rewrite Halleq; auto.
  - (*Feq*)
    alpha_case f2 Heq. bool_hyps; simpl_sumbool.
    rewrite !feq_rep.
    rewrite H with(t2:=t)(vars:=vars)(v2:=v2)
    (Hty2:=(proj1 (valid_eq_inj (valid_formula_eq eq_refl Hval2)))),
      H0 with(t2:=t0)(vars:=vars)(v2:=v2)
    (Hty2:=(proj2 (valid_eq_inj (valid_formula_eq eq_refl Hval2)))); auto.
  - (*Fbinop*)
    alpha_case f0 Heq; bool_hyps; simpl_sumbool.
    rewrite !fbinop_rep.
    rewrite H with(f2:=f0_1)(vars:=vars)(v2:=v2)
    (Hval2:=(proj1 (valid_binop_inj (valid_formula_eq eq_refl Hval2)))),
    H0 with(f2:=f0_2)(vars:=vars)(v2:=v2)
    (Hval2:=(proj2 (valid_binop_inj (valid_formula_eq eq_refl Hval2)))); auto.
  - (*Fnot*)
    alpha_case f2 Heq.  
    rewrite !fnot_rep. f_equal. apply H with(vars:=vars); auto.
  - (*Ftrue*)
    alpha_case f2 Heq. reflexivity.
  - (*Ffalse*)
    alpha_case f2 Heq. reflexivity.
  - (*Flet - just like Tlet*)
    alpha_case f2 Heq. 
    rename t into tm2.
    rename v into x. rename v0 into y.
    bool_hyps; simpl_sumbool.
    rename H3 into Ha1; rename H2 into Ha2.
    rewrite !flet_rep.
    apply H0 with (vars:=(x, y) :: vars); auto.
    + simpl. intros. bool_hyps.
      destruct H1; bool_hyps; repeat simpl_sumbool.
      * unfold substi.
        vsym_eq x x. vsym_eq y y.
        unfold eq_rec_r, eq_rec, eq_rect, dom_cast.
        assert (e0 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        assert (e1 = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        rewrite H1, H2. simpl. clear e0 e1 H1 H2.
        destruct x; destruct y; simpl in *; subst.
        assert (Heq = eq_refl) by (apply UIP_dec; apply vty_eq_dec).
        rewrite H1; simpl.
        apply H with(vars:=vars); auto.
      * unfold substi. vsym_eq x0 x. vsym_eq y0 y.
    + (*prove Hvals2*)
      simpl. intros.
      unfold substi. destruct H1 as [Hnotx Hnoty].
      not_or Hx0.
      vsym_eq x0 x. vsym_eq x0 y.
  - (*Fif*)
    alpha_case f0 Heq. bool_hyps.
    rewrite !fif_rep.
    rewrite H with(f2:=f0_1)(vars:=vars)(v2:=v2)
      (Hval2:=(proj1 (valid_if_inj (valid_formula_eq eq_refl Hval2)))),
    H0 with (f2:=f0_2)(vars:=vars)(v2:=v2)
      (Hval2:=(proj1 (proj2 (valid_if_inj (valid_formula_eq eq_refl Hval2))))),
    H1 with (f2:=f0_3)(vars:=vars) (v2:=v2)
      (Hval2:=(proj2 (proj2 (valid_if_inj (valid_formula_eq eq_refl Hval2))))); auto.
  - (*Fmatch - similar to Tmatch*)
    alpha_case f2 Heq.
    rename t into tm2.
    rename v into tys.
    rename v0 into tys2.
    rename l into ps2.
    bool_hyps; repeat simpl_sumbool.
    rename H1 into Htm. rename H4 into Hps. rename H2 into Hall.
    (*Get Hall into something more usable*)
    apply Nat.eqb_eq in Hps.
    rewrite fold_is_true in Hall.
    rewrite all2_forall with(d1:=(Pwild, Ftrue))(d2:=(Pwild, Ftrue)) in Hall; auto.
    rewrite !fmatch_rep.
    (*Need nested induction here*)
    generalize dependent (proj1 (valid_match_inv (valid_formula_eq eq_refl Hval))).
    generalize dependent (proj2 (valid_match_inv (valid_formula_eq eq_refl Hval))).
    generalize dependent (proj1 (valid_match_inv (valid_formula_eq eq_refl Hval2))).
    generalize dependent (proj2 (valid_match_inv (valid_formula_eq eq_refl Hval2))).
    inversion Hval2; subst. clear H4 H7 H8 Hval2.
    inversion Hval; subst. clear H4 H8 H9 Hval.
    generalize dependent tys2.
    generalize dependent ps2.
    
    induction ps; simpl; intros; destruct ps2; inversion Hps; auto.
    destruct a. simpl.
    destruct p. simpl.
    rewrite <- (H _ _ v1 v2 _ t0 t Htm) at 1; auto.
    (*Now need to know [match_val_single] is same - separate lemmas*)
    destruct (match_val_single gamma_valid pd all_unif vt tys2
    (has_type_valid gamma_valid tm tys2 t0) (term_rep v1 tm tys2 t0) p0) eqn : Hmatch1.
    + (*In Some case, need to know how lists relate*)

      (*First, get some info we need*)
      assert (Htyp: pattern_has_type sigma p tys2) by
        (inversion H6; subst; auto).
      assert (Htyp0: pattern_has_type sigma p0 tys2) by
        (inversion H7; subst; auto).
      assert (Hpeq: alpha_equiv_p (combine (pat_fv p0) (pat_fv p)) p0 p). {
        specialize (Hall 0 ltac:(lia)); simpl in Hall. bool_hyps; auto.
      }
      pose proof (alpha_equiv_p_fv_len_full _ _ Hpeq) as Hpfvs.
      destruct (match_val_single gamma_valid pd all_unif vt tys2
      (has_type_valid gamma_valid tm2 tys2 t) (term_rep v1 tm tys2 t0) p) eqn : Hmatch2.
      * assert (A:=Hall). specialize (A 0 ltac:(lia)); simpl in A.
        bool_hyps. rename H1 into Hp. rename H3 into Ht12.
        inversion H0; subst. eapply H4. apply Ht12.
        -- intros. 
          unfold add_vals in H1.
          rewrite in_firstb_app in H1.
          bool_hyps; destruct H1 as [Hinfv | ?]; bool_hyps; 
          repeat simpl_sumbool.
          ++ (*Case 1: (x, y) are in free vars of p0 and p respectively.
            Then we use [match_val_single_alpha_p_some] and
            [match_val_single_nodup] to show that their valuations
            are the same.*)
            apply in_firstb_in in Hinfv.
            assert (Hincom:=Hinfv).
            rewrite in_combine_iff in Hinfv; wf_tac.
            destruct Hinfv as [i [Hi Hith]].
            specialize (Hith vs_d vs_d). inversion Hith.
            (*Now, we know that x is in l by 
              [match_val_single_free_var]*)
            assert (Hinxl: In x (map fst l)). {
              apply match_val_single_free_var with(x:=x)(ty':=tys2) in Hmatch1;
              auto.
              apply Hmatch1. subst. wf_tac.
            }
            rewrite in_map_iff in Hinxl. destruct Hinxl as [bnd [Hx Hinbnd]].
            destruct bnd as [x' t']. simpl in Hx. subst x'.
            (*Now, we use [match_val_single_alpha_p_some] to show
              that (y, t') is in l0*)
            assert (Hinyl: In (y, t') l0). {
              eapply match_val_single_alpha_p_some in Hmatch2.
              rewrite <- Hmatch2. apply Hinbnd. apply Hp.
              all: wf_tac. apply Hmatch1. 
            }
            (*Finally, we use NoDup of l, l0 
              (from [match_val_single_nodup]) to give the binding*)
            assert (Hnodup1: NoDup (map fst l)). {
              eapply match_val_single_nodup in Hmatch1.
              apply Hmatch1. apply Htyp0.
            }
            assert (Hnodup2: NoDup (map fst l0)). {
              eapply match_val_single_nodup in Hmatch2.
              apply Hmatch2. apply Htyp.
            }
            rewrite !extend_val_with_list_lookup with(t:=t'); auto.
            (*Now handle all the casting*)
            destruct (vty_eq_dec (snd x) (projT1 t')).
            ** destruct (vty_eq_dec (snd y) (projT1 t')).
              {
                destruct x. destruct y. simpl in *; subst. simpl.
                assert (e0 = eq_refl). apply UIP_dec. apply vty_eq_dec.
                rewrite H1. reflexivity. 
              }
              { 
                exfalso.
                rewrite Heq in e. contradiction.
              }
            ** (*contradiction case - types match in output
              by [match_val_single_typs]*)
              apply match_val_single_typs with(x:=x)(t:=t') in Hmatch1;
              auto. exfalso. rewrite Hmatch1 in n. contradiction.
              (*And we are done!*)
          ++ (*Now in the other case, neither are free vars, so
            we use Hvals2*)
            rewrite map_fst_combine in n0; wf_tac.
            rewrite map_snd_combine in n; wf_tac.
            assert (Hxl: ~ In x (map fst l)). {
              intro C. 
              apply match_val_single_free_var with(x:=x)(ty':=tys2) in Hmatch1;
              auto.
              apply Hmatch1 in C. contradiction.
            }
            assert (Hyl0: ~ In y (map fst l0)). {
              intro C.
              apply match_val_single_free_var with(x:=y)(ty':=tys2) in Hmatch2;
              auto.
              apply Hmatch2 in C; contradiction.
            }
            rewrite !extend_val_with_list_notin'; wf_tac.
        -- (*Here, we must show preservation of [Hvals2]*) 
          unfold add_vals.
          intros x. rewrite !map_app, !in_app_iff;
          intros [Hnotx1 Hnotx2].
          not_or Hnotx. rewrite map_fst_combine in Hnotx2; wf_tac.
          rewrite map_snd_combine in Hnotx; wf_tac.
          rewrite !extend_val_with_list_notin'; wf_tac;
          intro C.
          ++ apply match_val_single_free_var with(x:=x)(ty':=tys2) in Hmatch2;
            auto.
            apply Hmatch2 in C; contradiction.
          ++ apply match_val_single_free_var with(x:=x)(ty':=tys2) in Hmatch1;
            auto.
            apply Hmatch1 in C; contradiction.
      * (*Contradiction: both are Some or both are None*)
        exfalso.
        rewrite <- match_val_single_alpha_p_none_iff in Hmatch2.
        rewrite Hmatch2 in Hmatch1. inversion Hmatch1. apply Hpeq.
    + (*In None case, both None, use IH*) 
      assert (match_val_single gamma_valid pd all_unif vt tys2
      (has_type_valid gamma_valid tm2 tys2 t) (term_rep v1 tm tys2 t0) p
      = None). {
        eapply match_val_single_alpha_p_none. 2: apply Hmatch1.
        specialize (Hall 0 ltac:(lia)); simpl in Hall; bool_hyps.
        apply H1.
      }
      rewrite H1. apply IHps; auto; clear IHps.
      * inversion H0; subst; auto.
      * intros j Hj; specialize (Hall (S j) ltac:(lia)); simpl in Hall;
        auto.
      * inversion H6; subst; auto.
      * inversion H7; subst; auto.
Qed.

(*Corollaries*)
Definition alpha_equiv_t_equiv t := proj_tm alpha_equiv_equiv t.
Definition alpha_equiv_f_equiv f := proj_fmla alpha_equiv_equiv f.

(*And the correctness theorems*)
Corollary a_equiv_t_equiv (t1 t2: term) (v: val_vars pd vt)
  (ty: vty)
  (Hty1: term_has_type sigma t1 ty)
  (Hty2: term_has_type sigma t2 ty)
  (Heq: a_equiv_t t1 t2):
  term_rep v t1 ty Hty1 = term_rep v t2 ty Hty2.
Proof.
  apply alpha_equiv_t_equiv with(vars:=nil); auto.
  intros. inversion H.
Qed.

Corollary a_equiv_f_equiv (f1 f2: formula) (v: val_vars pd vt)
  (Hval1: valid_formula sigma f1)
  (Hval2: valid_formula sigma f2)
  (Heq: a_equiv_f f1 f2):
  formula_rep v f1 Hval1 = formula_rep v f2 Hval2.
Proof.
  apply alpha_equiv_f_equiv with(vars:=nil); auto.
  intros. inversion H.
Qed.

End AlphaEquivDenotational.

(*Now, we prove the equivalence relation*)
Section Equivalence.

(*Reflexivity*)

Lemma alpha_equiv_p_same (p: pattern) 
  (vars: list (vsymbol * vsymbol))
  (Hvars: forall x, In x vars -> fst x = snd x)
  (Hallin: forall x, In x (pat_fv p) -> In x (map fst vars)):
  alpha_equiv_p vars p p.
Proof.
  induction p; simpl; auto.
  - bool_to_prop; split; [simpl_sumbool |].
    apply in_firstb_refl; auto.
    apply Hallin; simpl; auto.
  - bool_to_prop; split_all; 
    [simpl_sumbool | apply Nat.eqb_refl | simpl_sumbool |]. 
    simpl in Hallin. induction ps; simpl; auto;
    rewrite all2_cons;
    bool_to_prop; inversion H; subst; split; auto.
    + apply H2; intros. apply Hallin. simpl; simpl_set; triv.
    + apply IHps; auto. intros. apply Hallin. simpl; simpl_set; triv.
  - rewrite IHp1, IHp2; auto; intros; apply Hallin; simpl; simpl_set; triv.
  - bool_to_prop; split_all; [simpl_sumbool | | apply IHp; simpl; auto].
    + apply in_firstb_refl; auto. apply Hallin; simpl; simpl_set; auto.
    + intros; apply Hallin; simpl; simpl_set; triv.
Qed.

Lemma alpha_equiv_same (t: term) (f: formula):
  (forall vars
  (Hvars: forall x, In x vars -> fst x = snd x),
  alpha_equiv_t vars t t) /\
  (forall vars
  (Hvars: forall x, In x vars -> fst x = snd x),
  alpha_equiv_f vars f f).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto.
  - simpl_sumbool.
  - apply eq_var_refl; auto. 
  - bool_to_prop. split_all; [simpl_sumbool | apply Nat.eqb_refl | simpl_sumbool |].
    induction l1; simpl; auto; intros; rewrite all2_cons.
    bool_to_prop. inversion H; subst.
    split; [apply H2 |]; auto.
  - bool_to_prop. split_all; [simpl_sumbool | apply H| apply H0]; auto.
    simpl; intros. destruct H1; subst; auto.
  - bool_to_prop; split_all; [apply H | apply H0 | apply H1]; auto.
  - bool_to_prop. split_all; [apply H | apply Nat.eqb_refl | simpl_sumbool |]; auto.
    clear H.
    induction ps; simpl; intros; auto; rewrite all2_cons.
    inversion H0; subst. 
    destruct a. bool_to_prop; split_all; auto.
    + apply alpha_equiv_p_same; auto.
      * intros. rewrite in_combine_iff in H; auto.
        destruct H as [i [Hi Hx]].
        specialize (Hx vs_d vs_d). subst; simpl; reflexivity.
      * intros. rewrite map_fst_combine; auto.
    + apply H2. intros. 
      unfold add_vals in H. rewrite in_app_iff in H.
      destruct H; auto.
      rewrite in_combine_iff in H; auto.
      destruct H as [i [Hi Hx]].
      specialize (Hx vs_d vs_d). subst; simpl; reflexivity.
  - bool_to_prop; split; [simpl_sumbool | apply H]; auto;
    simpl; intros. destruct H0; subst; auto.
  - bool_to_prop. split_all; [simpl_sumbool | apply Nat.eqb_refl | simpl_sumbool |].
    induction tms; simpl; auto; intros; rewrite all2_cons.
    bool_to_prop. inversion H; subst.
    split; [apply H2 |]; auto.
  - bool_to_prop; split_all; try simpl_sumbool; apply H; simpl; intros;
    destruct H0; subst; auto.
  - bool_to_prop; split_all; [simpl_sumbool | apply H | apply H0];
    simpl; intros; triv.
  - bool_to_prop; split_all; [simpl_sumbool | apply H | apply H0];
    simpl; intros; triv.
  - bool_to_prop; split_all; [simpl_sumbool | apply H | apply H0];
    simpl; intros; try triv.
    destruct H1; subst; auto.
  - bool_to_prop; split_all; [apply H | apply H0 | apply H1]; auto.
  - bool_to_prop. split_all; [apply H | apply Nat.eqb_refl | simpl_sumbool |]; auto.
    clear H.
    induction ps; simpl; intros; auto; rewrite all2_cons.
    inversion H0; subst. 
    destruct a. bool_to_prop; split_all; auto.
    + apply alpha_equiv_p_same; auto.
      * intros. rewrite in_combine_iff in H; auto.
        destruct H as [i [Hi Hx]].
        specialize (Hx vs_d vs_d). subst; simpl; reflexivity.
      * intros. rewrite map_fst_combine; auto.
    + apply H2. intros. 
      unfold add_vals in H. rewrite in_app_iff in H.
      destruct H; auto.
      rewrite in_combine_iff in H; auto.
      destruct H as [i [Hi Hx]].
      specialize (Hx vs_d vs_d). subst; simpl; reflexivity.
Qed.

Definition alpha_t_equiv_same t := proj_tm alpha_equiv_same t.
Definition alpha_f_equiv_same f := proj_fmla alpha_equiv_same f.

(*Full reflexivity*)
Lemma a_equiv_t_refl (t: term):
  a_equiv_t t t.
Proof.
  unfold a_equiv_t.
  apply alpha_t_equiv_same. intros. inversion H.
Qed.

Lemma a_equiv_f_refl (f: formula):
  a_equiv_f f f.
Proof.
  unfold a_equiv_f.
  apply alpha_f_equiv_same; intros; inversion H.
Qed.

(*Symmetry*)
Lemma alpha_equiv_sym (t: term) (f: formula):
  (forall t1 l,
    alpha_equiv_t l t t1 = alpha_equiv_t (flip l) t1 t) /\
  (forall f1 l,
    alpha_equiv_f l f f1 = alpha_equiv_f (flip l) f1 f).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; auto.
  - destruct t1; auto; simpl.
    apply all_dec_eq; split; intros; subst; auto.
  - destruct t1; auto; simpl.
    apply eq_var_flip.
  - destruct t1; auto; simpl.
    rewrite (Nat.eqb_sym (length l3)).
    destruct (length l1 =? length l3) eqn : Hlen; simpl_bool; auto.
    rewrite eq_dec_sym. f_equal; [f_equal; apply eq_dec_sym |].
    nested_ind_case; rewrite !all2_cons; f_equal; auto.
  - destruct t1; auto; simpl. rewrite H, H0, eq_dec_sym; auto. 
  - destruct t0; auto; simpl.
    rewrite H, H0, H1; auto.
  - destruct t1; auto; simpl.
    rewrite (Nat.eqb_sym (length l0)).
    destruct (length ps =? length l0) eqn : Hlen; simpl_bool; auto.
    rewrite H, eq_dec_sym. f_equal.
    nested_ind_case; rewrite !all2_cons.
    destruct a as [p1 tm1]; destruct p as [p2 tm2].
    rewrite alpha_equiv_p_sym, flip_combine.
    f_equal; [f_equal |]; auto.
    rewrite Hp.
    unfold add_vals.
    rewrite flip_app, flip_combine; auto.
  - destruct t1; auto; simpl.
    rewrite H, eq_dec_sym. reflexivity.
  - destruct f1; auto; simpl.
    rewrite (Nat.eqb_sym (length l1)).
    destruct (length tms =? length l1) eqn : Hlen; simpl_bool; auto.
    rewrite eq_dec_sym.
    f_equal; [f_equal; apply eq_dec_sym |].
    nested_ind_case; rewrite !all2_cons. f_equal; auto.
  - destruct f1; auto; simpl.
    rewrite H, eq_dec_sym. f_equal. f_equal.
    apply eq_dec_sym.
  - destruct f1; auto; simpl.
    rewrite eq_dec_sym, H, H0; reflexivity.
  - destruct f0; auto; simpl.
    rewrite eq_dec_sym, H, H0; reflexivity.
  - destruct f1; auto; simpl.
    apply H.
  - destruct f1; auto.
  - destruct f1; auto.
  - destruct f1; auto; simpl.
    rewrite eq_dec_sym, H, H0; reflexivity.
  - destruct f0; auto; simpl.
    rewrite H, H0, H1; reflexivity.
  - destruct f1; auto; simpl.
    rewrite (Nat.eqb_sym (length l0)).
    destruct (length ps =? length l0) eqn : Hlen; simpl_bool; auto.
    rewrite H, eq_dec_sym. f_equal.
    nested_ind_case; rewrite !all2_cons.
    destruct a as [p1 tm1]; destruct p as [p2 tm2].
    rewrite alpha_equiv_p_sym, flip_combine.
    f_equal; [f_equal |]; auto.
    rewrite Hp. unfold add_vals.
    rewrite flip_app, flip_combine; auto.
Qed.

Definition alpha_t_equiv_sym t := proj_tm alpha_equiv_sym t. 
Definition alpha_f_equiv_sym f := proj_fmla alpha_equiv_sym f.

(*Transitivity*)

(*First, we describe the list: it is a bit more complicated
  than flip, and we need some lemmas about it*)
Section TransList.

Definition alist_trans (l1 l2: list (vsymbol * vsymbol)) :=
  map2 (fun x y => (fst x, snd y)) l1 l2.

Lemma in_firstb_trans v1 v2 x y z:
  map snd v1 = map fst v2 ->
  var_in_firstb (x, y) v1 ->
  var_in_firstb (y, z) v2 ->
  var_in_firstb (x, z) (alist_trans v1 v2).
Proof.
  revert v2. induction v1; simpl; intros; destruct v2; inversion H; subst;
  [inversion H0 |].
  simpl. clear H. simpl in H1.
  vsym_eq x (fst a); simpl in *; auto; revert H0; simpl_bool; intros.
  + vsym_eq y (snd a). vsym_eq (snd a) (fst p); auto; simpl in *.
    vsym_eq z (snd p).
  + vsym_eq y (snd a); simpl in H0.
    vsym_eq y (fst p); simpl in *.
    vsym_eq z (snd p); simpl in *.
    apply IHv1; auto.
Qed.

(*Could prove from above with [eq_var_eq], but shorter to juse
  repeat proof*)
Lemma eq_var_trans v1 v2 x y z:
  map snd v1 = map fst v2 ->
  eq_var v1 x y ->
  eq_var v2 y z ->
  eq_var (alist_trans v1 v2) x z.
Proof.
  revert v2. induction v1; simpl; intros; destruct v2; inversion H; subst.
  - simpl in H1. vsym_eq x y.
  - simpl. clear H. simpl in H1.
    vsym_eq x (fst a); simpl in *; auto; revert H0; simpl_bool; intros.
    + vsym_eq y (snd a). vsym_eq (snd a) (fst p); auto; simpl in *.
      vsym_eq z (snd p).
    + vsym_eq y (snd a); simpl in H0.
      vsym_eq y (fst p); simpl in *.
      vsym_eq z (snd p); simpl in *.
      apply IHv1; auto.
Qed.

Lemma combine_alist_trans l1 l2 l3:
  length l1 = length l2 ->
  length l2 = length l3 ->
  alist_trans (combine l1 l2) (combine l2 l3) = combine l1 l3.
Proof.
  intros Hlen1 Hlen2.
  generalize dependent l3.
  generalize dependent l2.
  induction l1; simpl; intros; destruct l2; inversion Hlen1;
  destruct l3; inversion Hlen2; auto; simpl.
  f_equal. apply IHl1; auto.
Qed.

Lemma alist_trans_app l1 l2 l3 l4:
  length l1 = length l2 ->
  alist_trans l1 l2 ++ alist_trans l3 l4 =
  alist_trans (l1 ++ l3) (l2 ++ l4).
Proof.
  intros Hlen.
  generalize dependent l2.
  induction l1; simpl; intros;
  destruct l2; inversion Hlen; simpl; auto.
  f_equal. apply IHl1; auto.
Qed.

End TransList.

(*The pattern case is easy, but its use relies on the lengths of
  the free vars lists being the same (in the map assumption)
  which comes from [alpha_equiv_p_fv_len_full]*)
Lemma alpha_equiv_p_trans (p1 p2 p3: pattern)
  (v1 v2: list (vsymbol * vsymbol))
  (Hl: map snd v1 = map fst v2)
  (Heq1: alpha_equiv_p v1 p1 p2)
  (Heq2: alpha_equiv_p v2 p2 p3):
  alpha_equiv_p (alist_trans v1 v2) p1 p3.
Proof.
  generalize dependent p3.
  generalize dependent p2. 
  induction p1; simpl; intros;
  alpha_case p2 Heq1;
  alpha_case p3 Heq2;
  simpl in Heq2; revert Heq1 Heq2;
  bool_to_prop; intros; destruct_all;
  repeat simpl_sumbool; simpl; auto.
  - split; [simpl_sumbool; simpl; rewrite e0 in n; contradiction | ].
    apply in_firstb_trans with(y:=v0); auto.
  - apply Nat.eqb_eq in H7, H3.
    rewrite H7, H3, Nat.eqb_refl. split_all; auto.
    rename l0 into ps2.
    rename l2 into ps3.
    rename H7 into Hlen1.
    rename H3 into Hlen2.
    generalize dependent ps3.
    generalize dependent ps2.
    induction ps; simpl; intros; destruct ps2; inversion Hlen1;
    destruct ps3; inversion Hlen2; auto; 
    rewrite all2_cons in H5, H1 |- * ;
    revert H1 H5; bool_to_prop; intros; destruct_all.
    inversion H; subst.
    split.
    + apply (H8 p); auto.
    + apply (IHps H9 ps2); auto.
  - split; [apply (IHp1_1 p2_1) | apply (IHp1_2 p2_2)]; auto.
  - split_all; [simpl_sumbool; simpl; rewrite e0 in n; contradiction |
    | apply (IHp1 p2); auto].
    apply in_firstb_trans with(y:=v0); auto.
Qed.

(*Now the transitivity lemma. This is annoying to prove*)
Lemma alpha_equiv_trans (t: term) (f: formula) :
  (forall t1 t2 (v1 v2: list (vsymbol * vsymbol))
    (Hl: map snd v1 = map fst v2)
    (Heq1: alpha_equiv_t v1 t t1)
    (Heq2: alpha_equiv_t v2 t1 t2),
    alpha_equiv_t (alist_trans v1 v2) t t2) /\
  (forall f1 f2 (v1 v2: list (vsymbol * vsymbol))
    (Hl: map snd v1 = map fst v2)
    (Heq1: alpha_equiv_f v1 f f1)
    (Heq2: alpha_equiv_f v2 f1 f2),
    alpha_equiv_f (alist_trans v1 v2) f f2).
Proof.
  revert t f; apply term_formula_ind; simpl; intros.
  - (*Tconst*) 
    alpha_case t1 Heq1; alpha_case t2 Heq2.
    rewrite simpl_all_dec in Heq1, Heq2 |- *; subst; auto.
  - (*Tvar*)
    alpha_case t1 Heq1; alpha_case t2 Heq2.
    eapply eq_var_trans.
    apply Hl. apply Heq1. apply Heq2.
  - (*Tfun*)
    alpha_case t1 Heq1; alpha_case t2 Heq2.
    bool_hyps; repeat simpl_sumbool; simpl.
    apply Nat.eqb_eq in H7, H3.
    rewrite H7, H3, Nat.eqb_refl. simpl.
    rename H7 into Hlen1.
    rename H3 into Hlen2.
    generalize dependent l2.
    generalize dependent l4.
    induction l1; simpl; intros; destruct l2; inversion Hlen1;
    destruct l4; inversion Hlen2; auto; rewrite all2_cons in H5, H1 |- *.
    bool_hyps.
    inversion H; subst. bool_to_prop; split.
    + apply H8 with(t1:=t); auto.
    + apply IHl1 with(l2:=l2); auto.
  - (*Tlet*)
    alpha_case t1 Heq1; alpha_case t2 Heq2.
    bool_hyps; repeat simpl_sumbool.
    bool_to_prop; split_all.
    + simpl_sumbool. exfalso. rewrite e0 in n. contradiction.
    + apply H with(t1:=t1_1); auto.
    + assert (Hmap: map snd ((v, v0) :: v1) = map fst ((v0, v3) :: v2)). {
        simpl. f_equal. auto. 
      }
      apply (H0 _ _ _ _ Hmap H5 H2).
  - (*Tif*)
    alpha_case t0 Heq1; alpha_case t3 Heq2.
    bool_hyps. bool_to_prop.
    split_all; [apply (H f0) | apply (H0 t0_1) | apply (H1 t0_2)]; auto.
  - (*Tmatch*)
    alpha_case t1 Heq1; alpha_case t2 Heq2.
    bool_hyps; repeat simpl_sumbool.
    apply Nat.eqb_eq in H8, H4.
    bool_to_prop; split_all; auto.
    + apply (H t1); auto.
    + rewrite H8, H4; apply Nat.eqb_refl.
    + clear H H5 H1.
      rename l into ps2.
      rename l0 into ps3.
      rename H8 into Hlen1.
      rename H4 into Hlen2.
      generalize dependent ps2.
      generalize dependent ps3.
      induction ps; intros;
      destruct ps2; inversion Hlen1;
      destruct ps3; inversion Hlen2; auto.
      destruct a as [p1 tm1].
      destruct p as [p2 tm2].
      destruct p0 as [p3 tm3].
      rewrite all2_cons in H6, H2 |- *; bool_hyps.
      pose proof (alpha_equiv_p_fv_len_full _ _ H5) as Hlenp1.
      pose proof (alpha_equiv_p_fv_len_full _ _ H) as Hlenp2.
      bool_to_prop.
      inversion H0; subst.
      split_all.
      * rewrite <- combine_alist_trans with(l2:=pat_fv p2); auto.
        apply alpha_equiv_p_trans with(p2:=p2); auto.
        rewrite map_snd_combine, map_fst_combine; auto.
      * unfold add_vals.
        rewrite <- combine_alist_trans with(l2:=pat_fv p2); auto.
        rewrite alist_trans_app.
        -- apply H10 with(t1:=tm2); auto.
          rewrite !map_app, Hl, map_fst_combine, map_snd_combine; auto.
        -- rewrite !combine_length. lia.
      * apply IHps with(ps2:=ps2); auto.
  - (*Teps*)
    alpha_case t1 Heq1; alpha_case t2 Heq2.
    bool_hyps; repeat simpl_sumbool.
    bool_to_prop; split.
    + simpl_sumbool. simpl. rewrite e0 in n. contradiction.
    + assert (Hmap: map snd ((v, v0) :: v1) = map fst ((v0, v3) :: v2)). {
        simpl. f_equal. auto.
      }
      apply (H _ _ _ _ Hmap H3 H1).
  - (*Fpred*)
    alpha_case f1 Heq1; alpha_case f2 Heq2.
    bool_hyps; repeat simpl_sumbool; simpl.
    apply Nat.eqb_eq in H7, H3.
    rewrite H7, H3, Nat.eqb_refl. simpl.
    rename H7 into Hlen1.
    rename H3 into Hlen2.
    generalize dependent l2.
    generalize dependent l0.
    induction tms; simpl; intros; destruct l0; inversion Hlen1;
    destruct l2; inversion Hlen2; auto; rewrite all2_cons in H5, H1 |- *.
    bool_hyps. bool_to_prop.
    inversion H; subst. split.
    + apply H8 with (t1:=t); auto.
    + apply IHtms with(l0:=l0); auto.
  - (*Fquant*)
    alpha_case f1 Heq1; alpha_case f2 Heq2.
    bool_hyps; repeat simpl_sumbool. simpl.
    bool_to_prop; split_all.
    + simpl_sumbool. simpl. rewrite e0 in n. contradiction.
    + assert (Hmap: map snd ((v, v0) :: v1) = map fst ((v0, v3) :: v2)). {
        simpl. f_equal. auto.
      }
      apply (H _ _ _ _ Hmap H4 H1).
  - (*Feq*)
    alpha_case f1 Heq1; alpha_case f2 Heq2; bool_hyps;
    repeat simpl_sumbool; simpl.
    bool_to_prop; split; [apply (H t) | apply (H0 t0)]; auto.
  - (*Fbinop*)
    alpha_case f0 Heq1; alpha_case f3 Heq2; bool_hyps;
    repeat simpl_sumbool; simpl.
    bool_to_prop; split; [apply (H f0_1) | apply (H0 f0_2)]; auto.
  - (*Fnot*)
    alpha_case f1 Heq1; alpha_case f2 Heq2.
    apply (H f1); auto.
  - (*Ftrue*)
    alpha_case f1 Heq1; alpha_case f2 Heq2; auto.
  - (*Ffalse*) 
    alpha_case f1 Heq1; alpha_case f2 Heq2; auto.
  - (*Flet*)
    alpha_case f1 Heq1; alpha_case f2 Heq2; bool_hyps;
    repeat simpl_sumbool.
    bool_to_prop; split_all.
    + simpl_sumbool. simpl. rewrite e0 in n. contradiction.
    + apply (H t); auto.
    + assert (Hmap: map snd ((v, v0) :: v1) = map fst ((v0, v3) :: v2)). {
        simpl. f_equal. auto. 
      }
      apply (H0 _ _ _ _ Hmap H5 H2).
  - (*Tif*)
    alpha_case f0 Heq1; alpha_case f4 Heq2; bool_hyps.
    bool_to_prop; split_all; 
    [apply (H f0_1) | apply (H0 f0_2) | apply (H1 f0_3)]; auto.
  - (*Tmatch*)
    alpha_case f1 Heq1; alpha_case f2 Heq2; bool_hyps;
    repeat simpl_sumbool.
    apply Nat.eqb_eq in H8, H4.
    rewrite (H t), H8, H4, Nat.eqb_refl; auto; simpl.
    clear H H5 H1.
    rename l into ps2.
    rename l0 into ps3.
    rename H8 into Hlen1.
    rename H4 into Hlen2.
    generalize dependent ps2.
    generalize dependent ps3.
    induction ps; intros;
    destruct ps2; inversion Hlen1;
    destruct ps3; inversion Hlen2; auto.
    destruct a as [p1 tm1].
    destruct p as [p2 tm2].
    destruct p0 as [p3 tm3].
    revert H6 H2; bool_to_prop; intros;
    destruct_all; rewrite all2_cons in H6, H2 |- *.
    bool_hyps.
    pose proof (alpha_equiv_p_fv_len_full _ _ H5) as Hlenp1.
    pose proof (alpha_equiv_p_fv_len_full _ _ H) as Hlenp2.
    inversion H0; subst.
    bool_to_prop; split_all.
    * rewrite <- combine_alist_trans with(l2:=pat_fv p2); auto.
      apply alpha_equiv_p_trans with(p2:=p2); auto.
      rewrite map_snd_combine, map_fst_combine; auto.
    * unfold add_vals.
      rewrite <- combine_alist_trans with(l2:=pat_fv p2); auto.
      rewrite alist_trans_app.
      -- apply (H10 tm2); auto.
        rewrite !map_app, Hl, map_fst_combine, map_snd_combine; auto.
      -- rewrite !combine_length. lia.
    * apply IHps with(ps2:=ps2); auto.
Qed.

Definition alpha_equiv_t_trans t := proj_tm alpha_equiv_trans t.
Definition alpha_equiv_f_trans f := proj_fmla alpha_equiv_trans f.

Corollary a_equiv_t_trans (t1 t2 t3: term):
  a_equiv_t t1 t2 ->
  a_equiv_t t2 t3 ->
  a_equiv_t t1 t3.
Proof.
  unfold a_equiv_t. apply alpha_equiv_t_trans; reflexivity.
Qed.

Corollary a_equiv_f_trans (f1 f2 f3: formula):
  a_equiv_f f1 f2 ->
  a_equiv_f f2 f3 ->
  a_equiv_f f1 f3.
Proof.
  unfold a_equiv_f. apply alpha_equiv_f_trans; reflexivity.
Qed.

End Equivalence.

(*Now we show that alpha equivalence preserves typing*)

Section AlphaTypes.

(*As long as the vars list includes all free vars of p1
  and has no duplicates, any two patterns that are
  alpha equivalent are well-typed if the other is*)
Lemma alpha_equiv_p_type (p1 p2: pattern)
  (vars: list (vsymbol * vsymbol)) (ty: vty)
  (Heq: alpha_equiv_p vars p1 p2)
  (Hn1: NoDup (map fst vars))
  (Hn2: NoDup (map snd vars))
  (Hallin: forall x, In x (pat_fv p1) -> In x (map fst vars))
  (Hty: pattern_has_type sigma p1 ty):
  pattern_has_type sigma p2 ty.
Proof.
  generalize dependent ty.
  generalize dependent p2.
  induction p1; simpl; intros; auto; 
  alpha_case p2 Heq; bool_hyps;
  repeat simpl_sumbool.
  - inversion Hty; subst. rewrite e. constructor.
    rewrite <- e; assumption.
  - (*This case is hard because we have to show that the free
    variable sets are disjoint. This follows from [alpha_equiv_p_fv']
    which describes the relationship between the free variables
    of alpha-equivalent patterns*)
    apply Nat.eqb_eq in H3.
    inversion Hty; subst.
    (*Get something useful out of H1 so we only need induction once*)
    rename l0 into ps2.
    rewrite fold_is_true in H1.
    rewrite all2_forall with(d1:=Pwild)(d2:=Pwild) in H1; auto.
    rename H1 into Hall.
    constructor; auto; try lia.
    + assert (length (map (ty_subst (s_params f0) l) (s_args f0)) = length ps2). {
        rewrite map_length; lia.
      }
      subst sigma0.
      generalize dependent ((map (ty_subst (s_params f0) l) (s_args f0))).
      intros a Hall2 Hlen2.
      revert Hall2 H.
      rewrite !Forall_forall; intros.
      rewrite in_combine_iff in H0; auto.
      destruct H0 as [i [Hi Hx]].
      specialize (Hx Pwild vty_int). subst. simpl.
      eapply H.
      3: apply Hall; lia.
      wf_tac.
      * intros; apply Hallin. simpl. simpl_set. 
        exists (nth i ps Pwild); split; wf_tac.
      * specialize (Hall2 (nth i ps Pwild, nth i a vty_int));
        apply Hall2.
        rewrite in_combine_iff; try lia.
        exists i. split; try lia. intros.
        f_equal; apply nth_indep; lia.
    + intros. intros [Hin1 Hin2].
      assert (Hi:=Hall).
      specialize (Hi i ltac:(lia)).
      specialize (Hall j ltac:(lia)).
      (*Crucially, we need [alpha_equiv_p_fv'] here*)
      apply alpha_equiv_p_fv' in Hall; auto.
      apply alpha_equiv_p_fv' in Hi; auto.
      2: { intros; apply Hallin. simpl. simpl_set. exists (nth i ps Pwild).
        split; wf_tac. }
      2: { intros; apply Hallin. simpl. simpl_set. exists (nth j ps Pwild).
        split; wf_tac. }
      rewrite nth_indep with(d':=Pwild) in Hin1 by lia.
      rewrite nth_indep with(d':=Pwild) in Hin2 by lia.
      rewrite Hall in Hin2.
      rewrite Hi, in_map_iff in Hin1.
      destruct Hin1 as [y1 [Hx Hiny1]].
      subst.
      rewrite in_map_iff in Hin2.
      destruct Hin2 as [y2 [Hx Hy2]].
      (*What we have to show: y1 = y2, 
        follows from injectivity of mk_fun_gen
        Really all we need is that the mapping function is
        injective, we don't care that is it specifically mk_fun_gen*)
      apply mk_fun_gen_inj in Hx; auto.
      2: { apply Hallin. simpl. simpl_set. 
        exists (nth j ps (Pwild)); split; wf_tac. }
      2: { apply Hallin; simpl; simpl_set.
        exists (nth i ps Pwild); split; wf_tac. }
      subst. apply (H12 i j Pwild y1 ltac:(lia) ltac:(lia) H2).
      split; auto.
  - assumption.
  - inversion Hty; subst.
    simpl in Hallin.
    constructor; auto.
    + apply IHp1_1; auto. intros; apply Hallin; simpl_set; triv.
    + apply IHp1_2; auto. intros; apply Hallin; simpl_set; triv.
    + (*Again we need the relationship between the free variables,
        but equivalence is much easier than disjointness*)
      intros x.
      apply alpha_equiv_p_fv' in H; auto.
      apply alpha_equiv_p_fv' in H0; auto.
      * rewrite H, H0. rewrite !in_map_iff.
        split; intros [y [Hx Hiny]]; subst; exists y; split; auto;
        apply H7; auto.
      * intros; apply Hallin; simpl_set; triv.
      * intros; apply Hallin; simpl_set; triv.
  - inversion Hty; subst.
    rewrite e. constructor; auto.
    + apply alpha_equiv_p_fv' in H0; auto.
      * rewrite H0. rewrite in_map_iff.
        intros [y [Hv0 Hiny]]; subst.
        (*Again, follows from injectivity of [mk_fun_gen]*)
        rewrite <- (combine_eq vars) in H1 at 3.
        apply mk_fun_gen_in_firstb in H1.
        apply mk_fun_gen_inj in H1; auto.
        -- subst; contradiction.
        -- apply Hallin; simpl; simpl_set; triv.
        -- apply Hallin; simpl; simpl_set; triv.
      * intros; apply Hallin; simpl; simpl_set; triv.
    + apply IHp1; auto.
      * intros; apply Hallin; simpl; simpl_set; triv.
      * rewrite <- e; assumption.
Qed.

(*A more specific version*)
Lemma alpha_equiv_p_type_full (p1 p2: pattern) (ty: vty)
  (Heq: alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2)
  (Hlens: length (pat_fv p1) = length(pat_fv p2))
  (Hty: pattern_has_type sigma p1 ty):
  pattern_has_type sigma p2 ty.
Proof.
  apply alpha_equiv_p_type with(ty:=ty) in Heq; auto.
  - apply map_fst_combine_nodup; apply NoDup_pat_fv.
  - apply map_snd_combine_nodup; apply NoDup_pat_fv.
  - intros. rewrite map_fst_combine; auto.
Qed.
    
(*alpha equivalence preserves well-typedness*)
Lemma alpha_equiv_type (t: term) (f: formula):
  (forall t1 (vars: list (vsymbol * vsymbol)) (ty: vty)
    (Heq: alpha_equiv_t vars t t1)
    (Hvars: forall x y, In (x, y) vars -> snd x = snd y),
    term_has_type sigma t ty ->
    term_has_type sigma t1 ty) /\
  (forall f1 (vars: list (vsymbol * vsymbol))
    (Heq: alpha_equiv_f vars f f1)
    (Hvars: forall x y, In (x, y) vars -> snd x = snd y),
    valid_formula sigma f ->
    valid_formula sigma f1).
Proof.
  revert t f; apply term_formula_ind; simpl; intros.
  - alpha_case t1 Heq.
    rewrite simpl_all_dec in Heq; subst; auto.
  - alpha_case t1 Heq.
    rewrite eq_var_eq in Heq.
    bool_hyps; destruct Heq; bool_hyps; repeat simpl_sumbool.
    apply in_firstb_in in H0.
    apply Hvars in H0.
    inversion H; subst.
    rewrite H0. constructor. rewrite <- H0; auto.
  - alpha_case t1 Heq. bool_hyps; repeat simpl_sumbool.
    apply Nat.eqb_eq in H4.
    inversion H0; subst. constructor; auto; try lia.
    clear -H13 H2 H H10 H4 Hvars.
    assert (length l1 = length (map (ty_subst (s_params f) l0) (s_args f))) by wf_tac.
    generalize dependent (map (ty_subst (s_params f) l0) (s_args f)).
    intros typs; revert typs.
    clear H10. generalize dependent l2. induction l1; simpl; intros; auto;
    destruct typs; inversion H0.
    + destruct l2; inversion H4. constructor.
    + destruct l2; inversion H4. inversion H13; subst.
      inversion H; subst.
      rewrite all2_cons in H2; bool_hyps.
      constructor; auto; simpl.
      eapply H9. apply H1. auto. apply H7.
  - alpha_case t1 Heq; bool_hyps; repeat simpl_sumbool.
    inversion H1; subst. constructor; auto.
    + eapply H. apply H4. intros; auto. rewrite <- e; auto.
    + eapply H0. apply H3. 2: auto. simpl; intros x y [Heq | Hin].
      * inversion Heq; subst; auto.
      * auto.
  - alpha_case t0 Heq. bool_hyps.
    inversion H2; subst.
    constructor; [apply (H _ _ H3) | apply (H0 _ _ _ H5) | apply (H1 _ _ _ H4)]; auto.
  - alpha_case t1 Heq. bool_hyps; repeat simpl_sumbool.
    apply Nat.eqb_eq in H5.
    inversion H1; subst.
    rewrite fold_is_true in H3.
    rewrite all2_forall with(d1:=(Pwild, tm_d)) (d2:=(Pwild, tm_d)) in H3; auto.
    constructor; [apply (H _ _ _ H2); auto | | |
      destruct l; destruct ps; auto; inversion H5].
    + intros. destruct (In_nth _ _ (Pwild, tm_d) H4) as [n [Hn Hx]]; 
      subst.
      specialize (H3 n ltac:(lia)). simpl in H3.
      bool_hyps. rename H3 into Heqp.
      apply alpha_equiv_p_type_full with(ty:=v0) in Heqp; auto.
      apply alpha_equiv_p_fv_len_full; auto.
      apply H10. wf_tac.
    + intros. destruct (In_nth _ _ (Pwild, tm_d) H4) as [n [Hn Hx]]; 
      subst.
      specialize (H3 n ltac:(lia)).
      bool_hyps. rename H3 into Heqp. rename H6 into Heqt.
      rewrite Forall_forall in H0.
      eapply H0. 2: apply Heqt.
      * wf_tac.
      * unfold add_vals.
        intros. rewrite in_app_iff in H3.
        destruct H3; auto.
        rewrite (alpha_equiv_p_fv_full _ _ Heqp) in H3.
        rewrite in_combine_iff in H3; wf_tac.
        destruct H3 as [i [Hi Hxy]].
        specialize (Hxy vs_d vs_d). inversion Hxy; subst. clear Hxy.
        rewrite map_nth_inbound with(d2:=vs_d); auto.
        rewrite mk_fun_vars_eq_full; auto.
        wf_tac.
      * apply H12. wf_tac.
  - (*Teps*)
    alpha_case t1 Heq.
    bool_hyps; simpl_sumbool.
    inversion H0; subst.
    rewrite e. constructor.
    + apply H in H2; auto. simpl; intros x y [Hxy | Hinxy]; auto.
      inversion Hxy; subst; auto.
    + rewrite <- e; assumption.
  - (*Fpred*)
    alpha_case f1 Heq.
    bool_hyps; repeat simpl_sumbool.
    apply Nat.eqb_eq in H4.
    inversion H0; subst. constructor; auto; try lia.
    clear -H11 H2 H H9 H4 Hvars. subst sigma0.
    assert (length l0 = length (map (ty_subst (p_params p0) l) (p_args p0))) by wf_tac.
    generalize dependent (map (ty_subst (p_params p0) l) (p_args p0)).
    intros typs; revert typs.
    clear H9. rename l0 into tms2. generalize dependent tms2. 
    induction tms; simpl; intros; auto;
    destruct typs; inversion H0;
    destruct tms2; inversion H4; simpl; try solve[constructor];
    rewrite all2_cons in H2.
    inversion H11; subst.
    inversion H; subst.
    bool_hyps.
    constructor; auto; simpl.
    eapply H9. apply H1. auto. apply H7.
  - (*Fquant*)
    alpha_case f1 Heq. bool_hyps; repeat simpl_sumbool.
    inversion H0; subst.
    constructor; [rewrite <- e |]; auto.
    apply H in H2; auto. simpl; intros x y [Hxy | Hinxy]; auto.
    inversion Hxy; subst; auto.
  - (*Feq*)
    alpha_case f1 Heq. bool_hyps; simpl_sumbool.
    inversion H1; subst.
    constructor; [apply H with(ty:=v0) in H4 | 
      apply H0 with(ty:=v0) in H3]; auto.
  - (*Fbinop - same*)
    alpha_case f0 Heq. bool_hyps; simpl_sumbool.
    inversion H1; subst.
    constructor; [apply H in H4 | apply H0 in H3]; auto.
  - (*Fnot*)
    alpha_case f1 Heq. 
    inversion H0; subst.
    constructor.
    apply H in Heq; auto.
  - (*Ftrue*)
    alpha_case f1 Heq; constructor.
  - (*Ffalse*)
    alpha_case f1 Heq; constructor.
  - (*Flet*)
    alpha_case f1 Heq; bool_hyps; simpl_sumbool.
    inversion H1; subst. constructor; auto.
    + eapply H. apply H4. intros; auto. rewrite <- e; auto.
    + eapply H0. apply H3. 2: auto. simpl; intros x y [Heq | Hin].
      * inversion Heq; subst; auto.
      * auto.
  - (*Fif*)
    alpha_case f0 Heq; bool_hyps.
    inversion H2; subst.
    constructor; [apply (H _ _ H3) | apply (H0 _ _  H5) | apply (H1 _ _ H4)]; auto.
  - (*Fmatch*)
    alpha_case f1 Heq. bool_hyps; repeat simpl_sumbool.
    apply Nat.eqb_eq in H5.
    inversion H1; subst.
    rewrite fold_is_true in H3.
    rewrite all2_forall with(d1:=(Pwild, Ftrue))(d2:=(Pwild, Ftrue)) in H3; auto.
    constructor; auto; [apply (H _ _ _ H2); auto | | |
      destruct l; destruct ps; auto; inversion H5].
    + rewrite Forall_forall; intros. 
      destruct (In_nth _ _ (Pwild, Ftrue) H4) as [n [Hn Hx]]; subst.
      specialize (H3 n ltac:(lia)).
      bool_hyps. rename H3 into Heqp.
      apply alpha_equiv_p_type_full with(ty:=v0) in Heqp; auto.
      apply alpha_equiv_p_fv_len_full; auto.
      rewrite Forall_forall in H10.
      apply H10. wf_tac.
    + rewrite Forall_forall; intros. 
      destruct (In_nth _ _ (Pwild, Ftrue) H4) as [n [Hn Hx]]; subst.
      specialize (H3 n ltac:(lia)).
      bool_hyps; rename H3 into Heqp; rename H6 into Heqt.
      rewrite Forall_forall in H0.
      eapply H0. 2: apply Heqt.
      * wf_tac.
      * unfold add_vals.
        intros. rewrite in_app_iff in H3.
        destruct H3; auto.
        rewrite (alpha_equiv_p_fv_full _ _ Heqp) in H3.
        rewrite in_combine_iff in H3; wf_tac.
        destruct H3 as [i [Hi Hxy]].
        specialize (Hxy vs_d vs_d). inversion Hxy; subst. clear Hxy.
        rewrite map_nth_inbound with(d2:=vs_d); auto.
        rewrite mk_fun_vars_eq_full; auto.
        wf_tac.
      * rewrite Forall_forall in H11. apply H11. wf_tac.
Qed. 

Definition alpha_equiv_t_type t := proj_tm alpha_equiv_type t.
Definition alpha_equiv_f_valid f := proj_fmla alpha_equiv_type f.

Corollary a_equiv_t_type (t1 t2: term) (ty: vty):
  a_equiv_t t1 t2 ->
  term_has_type sigma t1 ty ->
  term_has_type sigma t2 ty.
Proof.
  unfold a_equiv_t. intros Heq.
  apply alpha_equiv_t_type with(vars:=nil); auto.
  simpl; intros ? ? [].
Qed.

Corollary a_equiv_f_valid (f1 f2: formula):
  a_equiv_f f1 f2 ->
  valid_formula sigma f1 ->
  valid_formula sigma f2.
Proof.
  unfold a_equiv_f. intros Heq.
  apply alpha_equiv_f_valid with(vars:=nil); auto.
  simpl; intros ? ? [].
Qed.

End AlphaTypes.

(*Here we need a bunch of results which describe how we can
  alter the list without changing alpha equivalence.
  We need these to reason about substitution and alpha
  equivalence*)
Section AlterList.

(*1. We can always remove the second identical binding from the list*)
Lemma alpha_equiv_full_dup (t: term) (f: formula):
  (forall t1 x y v1 v2 v3,
    alpha_equiv_t (v1 ++ (x, y) :: v2 ++ (x, y) :: v3) t t1 =
    alpha_equiv_t (v1 ++ (x, y) :: v2 ++ v3) t t1) /\
  (forall f1 x y v1 v2 v3,
    alpha_equiv_f (v1 ++ (x, y) :: v2 ++ (x, y) :: v3) f f1 =
    alpha_equiv_f (v1 ++ (x, y) :: v2 ++ v3) f f1).
Proof.
  revert t f. apply term_formula_ind; simpl; auto; intros.
  - destruct t1; auto. rewrite !eq_var_app; simpl; rewrite !eq_var_app; simpl.
    vsym_eq v x; simpl. vsym_eq v0 y.
  - destruct t1; auto.
    destruct (length l1 =? length l2) eqn : Hlen; simpl_bool; auto.
    f_equal. nested_ind_case. rewrite !all2_cons. f_equal; auto.
  - destruct t1; auto. f_equal; [f_equal |]; auto.
    apply (H0 _ _ _ ((v, v0) :: v1)).
  - destruct t0; auto.
    rewrite H, H0, H1; auto.
  - destruct t1; auto.
    destruct (length ps =? length l) eqn : Hlen; simpl_bool; auto.
    f_equal; [f_equal |]; auto.
    nested_ind_case. rewrite !all2_cons.
    destruct a as [p1 tm1]; destruct p as [p2 tm2].
    f_equal; [f_equal |]; auto.
    unfold add_vals.
    specialize (Hp tm2 x y (combine (pat_fv p1) (pat_fv p2) ++ v1) v2 v3).
    rewrite <- !app_assoc in Hp. apply Hp.
  - destruct t1; auto.
    f_equal. apply (H _ _ _ ((v, v0) :: v1)).
  - destruct f1; auto.
    destruct (length tms =? length l0) eqn : Hlen; simpl_bool; auto.
    f_equal. nested_ind_case. rewrite !all2_cons. f_equal; auto.
  - destruct f1; auto.
    f_equal. apply (H _ _ _ ((v, v0) :: v1)).
  - destruct f1; auto. f_equal; [f_equal |]; auto.
  - destruct f0; auto. f_equal; [f_equal |]; auto.
  - destruct f1; auto.
  - destruct f1; auto. f_equal; [f_equal |]; auto.
    apply (H0 _ _ _ ((v, v0) :: v1)).
  - destruct f0; auto. f_equal; [f_equal |]; auto.
  - destruct f1; auto.
    destruct (length ps =? length l) eqn : Hlen; simpl_bool; auto.
    f_equal; [f_equal |]; auto.
    nested_ind_case. rewrite !all2_cons.
    destruct a as [p1 tm1]; destruct p as [p2 tm2].
    f_equal; [f_equal |]; auto.
    unfold add_vals.
    specialize (Hp tm2 x y (combine (pat_fv p1) (pat_fv p2) ++ v1) v2 v3).
    rewrite <- !app_assoc in Hp. apply Hp.
Qed.

Definition alpha_equiv_t_full_dup t := proj_tm alpha_equiv_full_dup t.
Definition alpha_equiv_f_full_dup f := proj_fmla alpha_equiv_full_dup f.

(*2. If both elements of a pair appear separately earlier in the list,
  we can remove this.
  This is a special case we need for [alpha_equiv_dup] because it
  holds unconditionally*)
Lemma alpha_equiv_dup3 (t1: term) (f1: formula) :
  (forall t2 x1 x2 y1 y2 v1 v2 v3 v4,
    alpha_equiv_t (v1 ++ (x1, y1) :: v2 ++ (x2, y2) :: v3 ++ (x2, y1) :: v4) t1 t2 =
    alpha_equiv_t (v1 ++ (x1, y1) :: v2 ++ (x2, y2) :: v3 ++ v4) t1 t2) /\
  (forall f2 x1 x2 y1 y2 v1 v2 v3 v4,
    alpha_equiv_f (v1 ++ (x1, y1) :: v2 ++ (x2, y2) :: v3 ++ (x2, y1) :: v4) f1 f2 =
    alpha_equiv_f (v1 ++ (x1, y1) :: v2 ++ (x2, y2) :: v3 ++ v4) f1 f2).
Proof.
  revert t1 f1; apply term_formula_ind; simpl; auto; intros.
  - destruct t2; auto. repeat (rewrite !eq_var_app; simpl).
    vsym_eq v x1; simpl.
    vsym_eq v x2; simpl.
    vsym_eq v0 y2; simpl.
    vsym_eq v0 y1.
  - destruct t2; auto. destruct (length l1 =? length l2) eqn : Hlen;
    simpl_bool; auto. f_equal. nested_ind_case.
    rewrite !all2_cons. f_equal; auto.
  - destruct t2; auto. f_equal; [f_equal|]; auto.
    apply (H0 _ _ _ _ _ ((v, v0) :: v1)).
  - destruct t0; auto.
    rewrite H, H0, H1; auto.
  - destruct t2; auto.
    destruct (length ps =? length l) eqn : Hlen; simpl_bool; auto.
    f_equal; [f_equal |]; auto.
    nested_ind_case. rewrite !all2_cons.
    destruct a as [p1 tm1]; destruct p as [p2 tm2].
    f_equal; [f_equal |]; auto.
    unfold add_vals.
    specialize (Hp tm2 x1 x2 y1 y2 (combine (pat_fv p1) (pat_fv p2) ++ v1) v2 v3 v4).
    rewrite <- !app_assoc in Hp. apply Hp.
  - destruct t2; auto.
    f_equal. apply H with(v1:=((v, v0) :: v1)).
  - destruct f2; auto.
    destruct (length tms =? length l0) eqn : Hlen; simpl_bool; auto.
    f_equal. nested_ind_case. rewrite !all2_cons. f_equal; auto.
  - destruct f2; auto.
    f_equal. apply H with (v1:=((v, v0) :: v1)).
  - destruct f2; auto. f_equal; [f_equal |]; auto.
  - destruct f0; auto. f_equal; [f_equal |]; auto.
  - destruct f2; auto.
  - destruct f2; auto. f_equal; [f_equal |]; auto.
    apply H0 with(v1:=((v, v0) :: v1)).
  - destruct f0; auto. f_equal; [f_equal |]; auto.
  - destruct f2; auto.
    destruct (length ps =? length l) eqn : Hlen; simpl_bool; auto.
    f_equal; [f_equal |]; auto.
    nested_ind_case. rewrite !all2_cons.
    destruct a as [p1 tm1]; destruct p as [p2 tm2].
    f_equal; [f_equal |]; auto.
    unfold add_vals.
    specialize (Hp tm2 x1 x2 y1 y2 (combine (pat_fv p1) (pat_fv p2) ++ v1) v2 v3 v4).
    rewrite <- !app_assoc in Hp. apply Hp.
Qed.

Definition alpha_equiv_t_dup3 t := proj_tm alpha_equiv_dup3 t. 
Definition alpha_equiv_f_dup3 f := proj_fmla alpha_equiv_dup3 f.

(*We also need the symmetric lemma*)
(*TOOO: better name*)
Lemma alpha_equiv_t_dup3' (t1 t2: term) (x1 x2 y1 y2: vsymbol)
  (v1 v2 v3 v4: list (vsymbol * vsymbol)):
  alpha_equiv_t (v1 ++ (x1, y1) :: v2 ++ (x2, y2) :: v3 ++ (x1, y2) :: v4) t1 t2 =
  alpha_equiv_t (v1 ++ (x1, y1) :: v2 ++ (x2, y2) :: v3 ++ v4) t1 t2.
Proof.
  rewrite !(alpha_t_equiv_sym t1).
  repeat (rewrite !flip_app; simpl).
  rewrite alpha_equiv_t_dup3. reflexivity.
Qed.

Lemma alpha_equiv_f_dup3' (f1 f2: formula) (x1 x2 y1 y2: vsymbol)
  (v1 v2 v3 v4: list (vsymbol * vsymbol)):
  alpha_equiv_f (v1 ++ (x1, y1) :: v2 ++ (x2, y2) :: v3 ++ (x1, y2) :: v4) f1 f2 =
  alpha_equiv_f (v1 ++ (x1, y1) :: v2 ++ (x2, y2) :: v3 ++ v4) f1 f2.
Proof.
  rewrite !(alpha_f_equiv_sym f1).
  repeat (rewrite !flip_app; simpl).
  rewrite alpha_equiv_f_dup3. reflexivity.
Qed.

(*3: If (x, y1) appears before (x, y2) and if y2 is not free
  in t1, then we can ignore the second binding. This is
  annoying to prove*)
Lemma alpha_equiv_dup (t: term) (f: formula):
  (forall t1 x y1 y2 v1 v2 v3
    (Hfree: ~ In y2 (term_fv t1)),
    alpha_equiv_t (v1 ++ (x, y1) :: v2 ++ (x, y2) :: v3) t t1 =
    alpha_equiv_t (v1 ++ (x, y1) :: v2 ++ v3) t t1) /\
  (forall f1 x y1 y2 v1 v2 v3
    (Hfree: ~ In y2 (form_fv f1)),
    alpha_equiv_f (v1 ++ (x, y1) :: v2 ++ (x, y2) :: v3) f f1 =
    alpha_equiv_f (v1 ++ (x, y1) :: v2 ++ v3) f f1).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto.
  - destruct t1; auto.
    simpl in Hfree. not_or Hv.
    repeat (rewrite !eq_var_app; simpl).
    vsym_eq v x; simpl.
    vsym_eq v0 y2.
  - destruct t1; auto.
    destruct (length l1 =? length l2) eqn : Hlen; simpl_bool; auto.
    f_equal.
    nested_ind_case. rewrite !all2_cons. simpl in Hfree.
    simpl_set.
    f_equal.
    rewrite Hp; auto. 
    apply IHl1; auto. simpl; simpl_set; auto.
  - destruct t1; auto.
    simpl in Hfree. simpl_set.
    f_equal; [f_equal |];
    [apply H |]; auto.
    not_or Hiny2.
    vsym_eq v0 y2.
    + apply alpha_equiv_t_dup3 with(v1:=nil).
    + apply (H0 _ _ _ _ ((v, v0) :: v1)); auto.
  - destruct t0; auto.
    simpl in Hfree. simpl_set.
    rewrite H, H0, H1; auto.
  - destruct t1; auto.
    simpl in Hfree. rewrite union_elts in Hfree.
    not_or Hy.
    rewrite H; auto. clear H Hy.
    destruct (length ps =? length l) eqn : Hlen; simpl;
    simpl_bool; auto.
    f_equal. nested_ind_case. rewrite !all2_cons.
    destruct a as [p1 tm1]. destruct p as [p2 tm2].
    simpl in Hy0. simpl_set. not_or Hy. simpl.
    destruct (alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2) eqn : Hpeq;
    simpl_bool; auto.
    pose proof (alpha_equiv_p_fv_len_full _ _ Hpeq) as Hlen2.
    rewrite (IHps Hforall); simpl_set; auto. f_equal.
    unfold add_vals.
    (*Again we need to see if y is in the bound vars or not*)
    destruct (in_dec vsymbol_eq_dec y2 (pat_fv p2)).
    * destruct (in_combine_split_r (pat_fv p1) (pat_fv p2) vs_d vs_d _ i Hlen2) as 
      [j [l1 [l2 [Hj [Hy2 Hcomb]]]]].
      rewrite Hcomb,<- !app_assoc. simpl.
      rewrite app_assoc, 
      alpha_equiv_t_dup3 with(v1:=l1)(v2:=(l2 ++ v1))(v3:=v2) (v4:=v3),
      !app_assoc; auto.
    * rewrite app_assoc, Hp with(v1:=(combine (pat_fv p1) (pat_fv p2) ++ v1)); auto.
      rewrite !app_assoc; auto.
  - (*Teps*)
    destruct t1; auto. f_equal.
    simpl in Hfree. simpl_set.
    vsym_eq y2 v0.
    + apply alpha_equiv_f_dup3 with(v1:=nil).
    + apply H with(v1:=((v, v0) :: v1)); auto.
  - (*Fpred*)
    destruct f1; auto.
    destruct (length tms =? length l0) eqn : Hlen; simpl_bool; auto.
    f_equal.
    nested_ind_case. rewrite !all2_cons. simpl in Hfree.
    rewrite union_elts in Hfree. not_or Hy2.
    rewrite (IHtms Hforall); auto. f_equal.
    apply Hp; auto.
  - (*Fquant*)
    destruct f1; auto. f_equal.
    simpl in Hfree. simpl_set.
    vsym_eq y2 v0.
    + apply alpha_equiv_f_dup3 with(v1:=nil).
    + apply H with(v1:=((v, v0) :: v1)); auto.
  - (*Feq*)
    destruct f1; auto. simpl in Hfree. simpl_set.
    not_or Hy2. rewrite H, H0; auto.
  - (*Fbinop*)
    destruct f0; auto. simpl in Hfree. simpl_set.
    not_or Hy2. rewrite H, H0; auto.
  - (*Fnot*)
    destruct f1; auto.
  - (*Flet*)
    destruct f1; auto.
    simpl in Hfree. simpl_set.
    not_or Hy2.
    f_equal; [f_equal |];
    [apply H |]; auto.
    vsym_eq v0 y2.
    + apply alpha_equiv_f_dup3 with(v1:=nil).
    + apply (H0 _ _ _ _ ((v, v0) :: v1)); auto.
  - (*Fif*)
    destruct f0; auto.
    simpl in Hfree. simpl_set. not_or Hy2.
    rewrite H, H0, H1; auto.
  - (*Fmatch*)
    destruct f1; auto.
    simpl in Hfree. rewrite union_elts in Hfree.
    not_or Hy.
    rewrite H; auto. clear H Hy.
    destruct (length ps =? length l) eqn : Hlen; simpl;
    simpl_bool; auto.
    f_equal. nested_ind_case. rewrite !all2_cons.
    destruct a as [p1 tm1]. destruct p as [p2 tm2].
    simpl in Hy0. simpl_set. simpl. not_or Hy.
    destruct (alpha_equiv_p (combine (pat_fv p1) (pat_fv p2)) p1 p2) eqn : Hpeq;
    simpl_bool; auto.
    pose proof (alpha_equiv_p_fv_len_full _ _ Hpeq) as Hlen2.
    rewrite (IHps Hforall); simpl_set; auto. f_equal.
    unfold add_vals.
    (*Again we need to see if y is in the bound vars or not*)
    destruct (in_dec vsymbol_eq_dec y2 (pat_fv p2)).
    * destruct (in_combine_split_r (pat_fv p1) (pat_fv p2) vs_d vs_d _ i Hlen2) as 
      [j [l1 [l2 [Hj [Hy2 Hcomb]]]]].
      rewrite Hcomb,<- !app_assoc. simpl.
      rewrite app_assoc, 
      alpha_equiv_f_dup3 with(v1:=l1)(v2:=(l2 ++ v1))(v3:=v2) (v4:=v3),
      !app_assoc; auto.
    * rewrite app_assoc, Hp with(v1:=(combine (pat_fv p1) (pat_fv p2) ++ v1)); auto.
      rewrite !app_assoc; auto.
Qed.

Definition alpha_t_equiv_dup_fst t := proj_tm alpha_equiv_dup t.
Definition alpha_f_equiv_dup_fst f := proj_fmla alpha_equiv_dup f.

(*4. We can add a redundant binding (x, x) as long as x does not
  appear later in the list.*)
Lemma alpha_equiv_redundant (t: term) (f: formula):
  (forall (t1: term) (x: vsymbol) (v1 v2: list (vsymbol * vsymbol))
    (Hnotinx1: ~ In x (map fst v2))
    (Hnotinx2: ~ In x (map snd v2)),
    alpha_equiv_t (v1 ++ (x, x) :: v2) t t1 =
    alpha_equiv_t (v1 ++ v2) t t1) /\
  (forall (f1: formula) (x: vsymbol) (v1 v2: list (vsymbol * vsymbol))
    (Hnotinx1: ~ In x (map fst v2))
    (Hnotinx2: ~ In x (map snd v2)),
    alpha_equiv_f (v1 ++ (x, x) :: v2) f f1 =
    alpha_equiv_f (v1 ++ v2) f f1).
Proof.
  revert t f; apply term_formula_ind; simpl; auto; intros.
  - destruct t1; auto.
    rewrite !eq_var_app. simpl.
    rewrite !eq_var_eq.
    vsym_eq v x; simpl; simpl_bool.
    + destruct (in_dec vsymbol_eq_dec x (map fst v2)); 
      try contradiction; simpl_bool.
      vsym_eq v0 x; [vsym_eq x x | vsym_eq x v0]; simpl_bool; auto.
      * destruct (in_dec vsymbol_eq_dec x (map snd v2));
        try contradiction; simpl_bool; auto.
      * rewrite in_firstb_notin_fst with(l:=v2); simpl_bool; auto.
    + vsym_eq v0 x; simpl; simpl_bool; auto.
      vsym_eq v x; simpl; simpl_bool.
      rewrite in_firstb_notin_snd with(l:=v2); simpl_bool; auto.
  - destruct t1; auto.
    destruct (length l1 =? length l2) eqn : Hlen; simpl_bool; auto.
    f_equal. nested_ind_case. rewrite !all2_cons. f_equal; auto.
  - destruct t1; auto.
    f_equal; [f_equal |]; auto.
    apply (H0 _ _ ((v, v0) :: v1)); auto.
  - destruct t0; auto.
    f_equal; [f_equal |]; auto.
  - destruct t1; auto.
    destruct (length ps =? length l) eqn: Hlen;
    simpl_bool; auto. 
    f_equal; [f_equal |]; auto.
    nested_ind_case. rewrite !all2_cons.
    destruct a as [p1 tm1]; destruct p as [p2 tm2].
    f_equal; [f_equal |]; auto.
    unfold add_vals. 
    specialize (Hp tm2 x (combine (pat_fv p1) (pat_fv p2) ++ v1) v2).
    rewrite <- !app_assoc in Hp. apply Hp; auto.
  - destruct t1; auto. f_equal.
    apply (H _ _ ((v, v0) :: v1)); auto.
  - destruct f1; auto.
    destruct (length tms =? length l0) eqn : Hlen; simpl_bool; auto.
    f_equal. nested_ind_case; rewrite !all2_cons; f_equal; auto.
  - destruct f1; auto.
    f_equal. apply (H _ _ ((v, v0) :: v1)); auto.
  - destruct f1; auto. f_equal; [f_equal |]; auto.
  - destruct f0; auto. f_equal; [f_equal |]; auto. 
  - destruct f1; auto.
  - destruct f1; auto. f_equal; [f_equal |]; auto.
    apply (H0 _ _ ((v, v0) :: v1)); auto.
  - destruct f0; auto. f_equal; [f_equal |]; auto.
  - destruct f1; auto.
    destruct (length ps =? length l) eqn: Hlen;
    simpl_bool; auto. 
    f_equal; [f_equal |]; auto.
    nested_ind_case. rewrite !all2_cons.
    destruct a as [p1 tm1]; destruct p as [p2 tm2].
    f_equal; [f_equal |]; auto.
    unfold add_vals. 
    specialize (Hp tm2 x (combine (pat_fv p1) (pat_fv p2) ++ v1) v2).
    rewrite <- !app_assoc in Hp. apply Hp; auto.
Qed.

Definition alpha_equiv_t_redundant t := proj_tm alpha_equiv_redundant t.
Definition alpha_equiv_f_redundant f := proj_fmla alpha_equiv_redundant f.

(*Remove redundant lists - do generically so we prove once*)
Section RemoveList.

Variable A: Type.
Variable a_eq : list (vsymbol * vsymbol) -> A -> A -> bool.
Variable a_redundant: forall (t1 t2: A) (x:vsymbol)
  (v1 v2: list (vsymbol * vsymbol))
  (Hnotinx1: ~ In x (map fst v2))
  (Hnotinx2: ~ In x (map snd v2)),
  a_eq (v1 ++ (x, x) :: v2) t1 t2 =
  a_eq (v1 ++ v2) t1 t2.
Variable a_fulldup: forall (t1 t2: A) (x y: vsymbol)
  (v1 v2 v3: list (vsymbol * vsymbol)),
  a_eq (v1 ++ (x, y) :: v2 ++ (x, y) :: v3) t1 t2 =
  a_eq (v1 ++ (x, y) :: v2 ++ v3) t1 t2.

(*This proof could be improved for sure*)
Lemma a_redundant_list (t1 t2: A) 
  (v1 v2: list (vsymbol * vsymbol))
  (Halleq: forall x, In x v1 -> fst x = snd x)
  (Hnotin1: forall x, In x (map fst v1) -> ~ In x (map fst v2))
  (Hnotin2: forall x, In x (map fst v1) -> ~ In x (map snd v2)):
  a_eq (v1 ++ v2) t1 t2 =
  a_eq v2 t1 t2.
Proof.
  (*A bit tricky: do induction on the length of v1, not v1 itself*)
  induction v1 using (well_founded_induction
                     (wf_inverse_image _ nat _ (@length _)
                        PeanoNat.Nat.lt_wf_0)).
  destruct v1; simpl; auto.
  destruct p as [x y].
  assert (fst (x, y) = snd (x, y)). apply Halleq. left; auto.
  simpl in H0; subst.
  (*See if (y, y) appears in v1 or not*)
  destruct (in_dec (tuple_eq_dec vsymbol_eq_dec vsymbol_eq_dec) 
  (y, y) v1).
  - (*If so, use [a_fulldup]*)
    apply in_split in i.
    destruct i as [l1 [l2 Hv1]].
    rewrite Hv1, <- app_assoc. simpl.
    specialize (a_fulldup t1 t2 y y nil l1 (l2 ++ v2)).
    simpl in a_fulldup. rewrite a_fulldup.
    (*Here, we can use the IH, since the list is shorter*)
    rewrite app_assoc, app_comm_cons.
    apply (H ((y, y) :: l1 ++ l2)); simpl.
    + rewrite Hv1, !app_length; simpl. lia.
    + intros; apply Halleq; simpl. destruct H0; auto. right.
      subst. rewrite in_app_iff in H0. in_tac; simpl.
      destruct H0; auto.
    + intros x. rewrite map_app, in_app_iff; intros; 
      apply Hnotin1; simpl. subst. 
      rewrite map_app, in_app_iff; simpl.
      destruct_all; auto.
    + intros x. rewrite map_app, in_app_iff; intros;
      apply Hnotin2; simpl; subst.
      rewrite map_app, in_app_iff; simpl;
      destruct_all; auto.
  - (*If not, use a_redundant*)
    specialize (a_redundant t1 t2 y nil (v1 ++ v2)).
    simpl in a_redundant. rewrite a_redundant; auto.
    + apply H; simpl in *; auto.
    + rewrite map_app, in_app_iff; intros [C | C].
      * apply n. rewrite in_map_iff in C.
        destruct C as [[x' y'] [Hy Hinxy']]; simpl in Hy; subst.
        assert (fst (y, y') = snd (y, y')). apply Halleq. right; auto.
        simpl in H0; subst; auto.
      * apply (Hnotin1 y); auto. simpl. auto.
    + rewrite map_app, in_app_iff; intros [C | C].
      * apply n. rewrite in_map_iff in C.
        destruct C as [[x' y'] [Hy Hinxy']]; simpl in Hy; subst.
        assert (fst (x', y) = snd (x', y)). apply Halleq. right; auto.
        simpl in H0; subst; auto.
      * apply (Hnotin2 y); auto. simpl; auto.
Qed.

End RemoveList.

Definition alpha_equiv_t_redundant' :=
  a_redundant_list _ _ alpha_equiv_t_redundant alpha_equiv_t_full_dup.
Definition alpha_equiv_f_redundant' :=
  a_redundant_list _ _ alpha_equiv_f_redundant alpha_equiv_f_full_dup.

Corollary a_equiv_t_expand (vars: list (vsymbol * vsymbol)) t1 t2:
  a_equiv_t t1 t2 ->
  (forall x, In x vars -> fst x = snd x) ->
  alpha_equiv_t vars t1 t2.
Proof.
  unfold a_equiv_t; intros.
  rewrite <- (app_nil_r vars).
  rewrite alpha_equiv_t_redundant' with(v1:=vars)(v2:=nil); auto.
Qed.

Corollary a_equiv_f_expand vars f1 f2:
  a_equiv_f f1 f2 ->
  (forall x, In x vars -> fst x = snd x) ->
  alpha_equiv_f vars f1 f2.
Proof.
  unfold a_equiv_f; intros.
  rewrite <- (app_nil_r vars).
  rewrite alpha_equiv_f_redundant' with (v1:=vars)(v2:=nil); auto.
Qed.

Corollary a_equiv_t_expand_combine (l: list vsymbol) t1 t2:
  a_equiv_t t1 t2 ->
  alpha_equiv_t (combine l l) t1 t2.
Proof.
  intros. apply a_equiv_t_expand; auto.
  intros. rewrite in_combine_iff in H0; auto.
  destruct H0 as [i [Hi Hx]].
  specialize (Hx vs_d vs_d). subst. reflexivity.
Qed.

Corollary a_equiv_f_expand_combine (l: list vsymbol) f1 f2:
  a_equiv_f f1 f2 ->
  alpha_equiv_f (combine l l) f1 f2.
Proof.
  intros. apply a_equiv_f_expand; auto.
  intros. rewrite in_combine_iff in H0; auto.
  destruct H0 as [i [Hi Hx]].
  specialize (Hx vs_d vs_d). subst. reflexivity.
Qed.

End AlterList.

(*Now we come to substitution and alpha equivalence.
  To specify this, we first express that a variable occurs the
  same way in two patterns, terms, or formulas*)
Section AlphaSub.

Fixpoint same_in_p (p1 p2: pattern) (x: vsymbol) : bool :=
  match p1, p2 with
  | Pvar v1, Pvar v2 => eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 x)
  | Pconstr f1 tys1 ps1, Pconstr t2 tys2 ps2 =>
    (length ps1 =? length ps2) &&
    all2 (fun p1 p2 => same_in_p p1 p2 x) ps1 ps2
  | Pwild, Pwild => true
  | Por p1 p2, Por p3 p4 =>
    same_in_p p1 p3 x &&
    same_in_p p2 p4 x
  | Pbind p1 v1, Pbind p2 v2 =>
    same_in_p p1 p2 x &&
    eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 x)
  | _, _ => false
  end.

Fixpoint same_in_t (t1 t2: term) (x: vsymbol) : bool :=
  match t1, t2 with
  | Tconst _, Tconst _ => true
  | Tvar v1, Tvar v2 => eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 x)
  | Tlet tm1 v1 tm2, Tlet tm3 v2 tm4 =>
    same_in_t tm1 tm3 x &&
    (eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 x)) &&
    same_in_t tm2 tm4 x
  | Tfun f1 tys1 tms1, Tfun f2 tys2 tms2 =>
    (length tms1 =? length tms2) &&
    all2 (fun t1 t2 => same_in_t t1 t2 x) tms1 tms2
  | Tif f1 tm1 tm2, Tif f2 tm3 tm4 =>
    same_in_f f1 f2 x &&
    same_in_t tm1 tm3 x &&
    same_in_t tm2 tm4 x
  | Tmatch tm1 v1 ps1, Tmatch tm2 v2 ps2 =>
    (length ps1 =? length ps2) &&
    same_in_t tm1 tm2 x &&
    all2 (fun x1 x2 => 
      (length (pat_fv (fst x1)) =? length (pat_fv (fst x2))) &&
      same_in_p (fst x1) (fst x2) x &&
      same_in_t (snd x1) (snd x2) x) ps1 ps2
  | Teps f1 v1, Teps f2 v2 =>
    (eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 x)) &&
    same_in_f f1 f2 x
  | _, _ => false
  end
with same_in_f (f1 f2: formula) (x: vsymbol) : bool :=
  match f1, f2 with
  | Fpred p1 tys1 tms1, Fpred p2 tys2 tms2 =>
    (length tms1 =? length tms2) &&
    all2 (fun t1 t2 => same_in_t t1 t2 x) tms1 tms2
  | Fquant q1 v1 f1, Fquant q2 v2 f2 =>
    eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 x) &&
    same_in_f f1 f2 x
  | Feq v1 t1 t2, Feq v2 t3 t4 =>
    same_in_t t1 t3 x &&
    same_in_t t2 t4 x
  | Fbinop b1 f1 f2, Fbinop b2 f3 f4 =>
    same_in_f f1 f3 x &&
    same_in_f f2 f4 x
  | Fnot f1, Fnot f2 =>
    same_in_f f1 f2 x
  | Ftrue, Ftrue => true
  | Ffalse, Ffalse => true
  | Flet tm1 v1 f1, Flet tm2 v2 f2 =>
    same_in_t tm1 tm2 x &&
    (eqb (vsymbol_eq_dec v1 x) (vsymbol_eq_dec v2 x)) &&
    same_in_f f1 f2 x
  | Fif f1 f2 f3, Fif f4 f5 f6 =>
    same_in_f f1 f4 x &&
    same_in_f f2 f5 x &&
    same_in_f f3 f6 x
  | Fmatch tm1 v1 ps1, Fmatch tm2 v2 ps2 =>
    (length ps1 =? length ps2) &&
    same_in_t tm1 tm2 x &&
    all2 (fun x1 x2 => 
     (length (pat_fv (fst x1)) =? length (pat_fv (fst x2))) &&
      same_in_p (fst x1) (fst x2) x &&
      same_in_f (snd x1) (snd x2) x) ps1 ps2
  | _, _ => false
  end.

Lemma same_in_p_fv (p1 p2: pattern) x:
  same_in_p p1 p2 x ->
  In x (pat_fv p1) <-> In x (pat_fv p2).
Proof.
  revert p2. induction p1; simpl; intros p2 Hsame; destruct p2;
  try solve[inversion Hsame]; simpl; try reflexivity.
  - vsym_eq v x; vsym_eq v0 x; try solve[inversion Hsame];
    split; intros [Heq | []]; auto.
  - simpl_set. revert Hsame; bool_to_prop; intros; destruct Hsame as [Hlen Hall].
    apply Nat.eqb_eq in Hlen.
    rewrite fold_is_true, all2_forall with(d1:=Pwild)(d2:=Pwild) in Hall; auto.
    split; intros [p [Hiny Hinx]];
    pose proof (In_nth _ _ Pwild Hiny) as Hnth; destruct Hnth as [n [Hn Hp]]; subst;
    [exists (nth n l0 Pwild) | exists (nth n ps Pwild)]; split; wf_tac;
    rewrite Forall_forall in H; specialize (Hall n ltac:(lia)); apply H in Hall; auto;
    try (apply Hall; assumption); wf_tac.
  - simpl_set. revert Hsame; bool_to_prop; intros [Hs1 Hs2]. 
    rewrite (IHp1_1 p2_1), (IHp1_2 p2_2); auto. reflexivity.
  - revert Hsame; bool_to_prop; intros [Hsame Heq]. 
    simpl_set.
    rewrite (IHp1 p2); auto.
    vsym_eq v x; vsym_eq v0 x; try solve[inversion Heq]; try reflexivity;
    split; intros [Hin | Heq']; subst; auto; contradiction.
Qed.

(*We prove that [same_in] is reflexive*)

Lemma same_in_p_refl (p: pattern) x:
  same_in_p p p x.
Proof.
  induction p; simpl; auto.
  - rewrite eqb_reflx; auto.
  - rewrite Nat.eqb_refl; simpl. induction ps; simpl; auto.
    rewrite all2_cons. inversion H; subst.
    rewrite H2, IHps; auto.
  - rewrite IHp1, IHp2; auto.
  - rewrite IHp, eqb_reflx; auto.
Qed. 

Lemma same_in_refl (t: term) (f: formula):
  (forall x, same_in_t t t x) /\
  (forall x, same_in_f f f x).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; auto.
  - rewrite eqb_reflx; auto.
  - induction l1; simpl; auto.
    rewrite all2_cons. inversion H; subst.
    rewrite Nat.eqb_refl in IHl1.
    rewrite Nat.eqb_refl, H2, IHl1; auto.
  - rewrite H, H0, eqb_reflx; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H, Nat.eqb_refl. simpl.
    induction ps; simpl; intros; auto.
    rewrite all2_cons. inversion H0; subst.
    rewrite Nat.eqb_refl, same_in_p_refl, H3, IHps; auto.
  - rewrite eqb_reflx, H; auto.
  - induction tms; simpl; auto.
    rewrite all2_cons. inversion H; subst.
    rewrite Nat.eqb_refl in IHtms.
    rewrite Nat.eqb_refl, H2, IHtms; auto.
  - rewrite eqb_reflx, H; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0, eqb_reflx; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H, Nat.eqb_refl; simpl.
    induction ps; simpl; intros; auto.
    rewrite all2_cons. inversion H0; subst.
    rewrite Nat.eqb_refl, same_in_p_refl, H3, IHps; auto.
Qed.

Definition same_in_t_refl t := proj_tm same_in_refl t. 
Definition same_in_f_refl f := proj_fmla same_in_refl f.

(*This lemma describes how substitution affects alpha equivalence, 
  and states that under some conditions, a substiution is alpha equivalent
  under the context extended with the substitution.
  We give more useful corollaries; we need the general form to prove
  results about iterated substitution.
  *)
Theorem alpha_equiv_sub (t: term) (f: formula):
  (forall (tm2: term) (x y: vsymbol) v1 v2
    (Htys: snd x = snd y)
    (Hbnd: ~ In y (bnd_t tm2))
    (Hfree: ~ In y (term_fv tm2))
    (Hsame: same_in_t t tm2 x)
    (Hv1a: ~In x (map fst v1))
    (Hv1b: ~ In y (map snd v1))
    (Heq: alpha_equiv_t (v1 ++ v2) t tm2),
    alpha_equiv_t (v1 ++ (x, y) :: v2) t (sub_t x y tm2)) /\
  (forall (fm2: formula) (x y: vsymbol) v1 v2
    (Htys: snd x = snd y)
    (Hbnd: ~ In y (bnd_f fm2))
    (Hfree: ~ In y (form_fv fm2))
    (Hsame: same_in_f f fm2 x)
    (Hv1a: ~In x (map fst v1))
    (Hv1b: ~ In y (map snd v1))
    (Heq: alpha_equiv_f (v1 ++ v2) f fm2),
    alpha_equiv_f (v1 ++ (x, y):: v2) f (sub_f x y fm2)).
Proof.
  revert t f; apply term_formula_ind; simpl; auto; intros.
  - (*Tconst*) alpha_case tm2 Heq; auto.
  - (*Tvar*) alpha_case tm2 Heq. not_or Hvy. clear Hbnd Hvy0.
    vsym_eq v x; simpl.
    + vsym_eq x v0.
      * vsym_eq v0 v0.
        rewrite eq_var_app. simpl.
        destruct (in_dec vsymbol_eq_dec v0 (map fst v1)); simpl; try contradiction.
        destruct (in_dec vsymbol_eq_dec y (map snd v1)); simpl; try contradiction.
        vsym_eq v0 v0; simpl. vsym_eq y y. simpl. simpl_bool. auto.
      * vsym_eq v0 x.
    + vsym_eq v0 x. vsym_eq x v0.
      revert Heq. rewrite !eq_var_app. simpl. vsym_eq v x. vsym_eq v0 y.
  - (*Tfun*)
    alpha_case tm2 Heq. bool_hyps; repeat simpl_sumbool. clear H4.
    rewrite map_length, H3; simpl.
    nested_ind_case; rewrite all2_cons in H1, H5 |- *.
    bool_hyps. bool_to_prop; split.
    + apply Hp; auto; intro C; [apply Hbnd | apply Hfree]; simpl; simpl_set; wf_tac.
    + apply IHl1; wf_tac; intro C; [apply Hbnd | apply Hfree]; simpl; simpl_set; wf_tac.
  - (*Tlet*)
    alpha_case tm0 Heq. simpl_set.
    rewrite in_app_iff in Hbnd.
    bool_hyps; repeat simpl_sumbool; simpl. bool_to_prop; split.
    + apply H; auto.
    + vsym_eq x v0.
      * vsym_eq v0 v0. vsym_eq v v0.
        pose proof (alpha_t_equiv_dup_fst tm2 tm0_2 v0 v0 y nil v1 v2).
        simpl in H1.
        rewrite H1; auto.
        not_or Hy. auto.
      * vsym_eq v0 x. vsym_eq v x.
        not_or Hy.
        apply H0 with(v1:=(v, v0) :: v1); auto; simpl; intros [Heq | Hin]; subst;
        auto.
  - (*Tif*)
    alpha_case tm2 Heq. bool_hyps. 
    simpl_set. rewrite !in_app_iff in Hbnd. 
    rewrite H, H0, H1; auto.
  - (*Tmatch - basically iterated Tlet, we need the many previous results*)
    alpha_case tm2 Heq.
    bool_hyps; repeat simpl_sumbool. clear H4.
    rewrite in_app_iff in Hbnd.
    simpl_set_small. not_or Hy.
    rewrite map_length, H5, H; auto. simpl.
    clear Hy Hy1 H.
    rename Hy0 into Hfree.
    rename Hy2 into Hbnd.
    rename l into ps2.
    nested_ind_case. rewrite all2_cons in H2, H6 |- *.
    bool_hyps.
    destruct a.
    inversion H0; subst. 
    destruct p as [p1 t1].
    case_in.
    + unfold add_vals.
      rewrite H; simpl.
      bool_to_prop;
      split_all; auto.
      2: { apply IHps; auto; intro C; [apply Hbnd | apply Hfree]; simpl; simpl_set; wf_tac. }
      simpl in i.
      apply Nat.eqb_eq in H6.
      rewrite <- same_in_p_fv in i. 2: apply H10. simpl in i.
      destruct (in_combine_split_l _ _ vs_d vs_d _ i H6) as 
        [n [v1' [v2' [Hn [Hx Hcomb]]]]]. simpl in Hcomb.
      rewrite Hcomb, <- app_assoc.
      simpl.
      rewrite (app_assoc v2' v1).
      rewrite (alpha_t_equiv_dup_fst t t1 x _ _ v1' (v2' ++ v1) v2); auto.
      * rewrite <- app_assoc.
        replace (v1' ++ (x, nth n (pat_fv p1) vs_d) :: v2' ++ v1 ++ v2) with
        ((v1' ++ (x, nth n (pat_fv p1) vs_d) :: v2') ++ (v1 ++ v2)) by 
        (rewrite <- !app_assoc; reflexivity).
        rewrite <- Hcomb. auto.
      * intro C; apply Hfree; simpl; simpl_set.
        left. split; auto. intro C1.
        apply Hbnd. simpl. wf_tac.
    + (*In this case, we need to do substitution*)
      simpl.
      apply Nat.eqb_eq in H6.
      simpl in H.
      rewrite H; simpl.
      bool_to_prop; split.
      * unfold add_vals.
        rewrite app_assoc. apply (Hp t1 x y (combine (pat_fv p0) (pat_fv p1) ++ v1)); auto.
        -- intro C. apply Hbnd. simpl. wf_tac.
        -- intro C. apply Hfree. simpl. simpl_set. left; split; wf_tac.
          intro C1. apply Hbnd. simpl; wf_tac.
        -- rewrite map_app. wf_tac; auto. intro C.
          destruct C; auto. simpl in n.
          apply same_in_p_fv in H10. apply H10 in H11.
          contradiction.
        -- rewrite map_app. wf_tac; intro C.
          destruct C; auto. apply Hbnd. simpl. wf_tac.
        -- rewrite <- app_assoc. auto.
      * apply IHps; auto. (*TODO: use free_bnd_tac*)
        -- intro C. apply Hbnd. simpl. wf_tac.
        -- intro C. apply Hfree. simpl. simpl_set; wf_tac.
  - (*Teps*)
    alpha_case tm2 Heq. simpl_set.
    bool_hyps.
    not_or Hy.
    vsym_eq x v0; rewrite H0; simpl.
    + vsym_eq v0 v0. vsym_eq v v0.
      pose proof (alpha_f_equiv_dup_fst f f0 v0 v0 y nil v1 v2).
      simpl in H4.
      rewrite H4, H1; auto. 
    + vsym_eq v0 x. vsym_eq v x.
      apply H with(v1:=(v, v0) :: v1); auto; simpl; intros [Heq | Hin]; subst;
      auto.
  - (*Fpred*)
    alpha_case fm2 Heq. bool_hyps; repeat simpl_sumbool. clear H4.
    rewrite map_length, H3; simpl.
    nested_ind_case; rewrite all2_cons in H1, H5 |- *.
    bool_hyps. bool_to_prop; split.
    + apply Hp; auto; intro C; [apply Hbnd | apply Hfree]; simpl; simpl_set; wf_tac.
    + apply IHtms; wf_tac; intro C; [apply Hbnd | apply Hfree]; simpl; simpl_set; wf_tac.
  - (*Fquant - same as Teps*)
    alpha_case fm2 Heq. simpl_set.
    bool_hyps; repeat simpl_sumbool.
    not_or Hy.
    vsym_eq x v0; rewrite e, !eq_dec_refl; simpl.
    + vsym_eq v0 v0. vsym_eq v v0.
      pose proof (alpha_f_equiv_dup_fst f fm2 v0 v0 y nil v1 v2).
      simpl in H0.
      rewrite H0; auto. 
    + vsym_eq v0 x. vsym_eq v x.
      apply H with(v1:=(v, v0) :: v1); auto; simpl; intros [Heq | Hin]; subst;
      auto.
  - (*Feq*)
    alpha_case fm2 Heq. bool_hyps. simpl_set.
    simpl_set. rewrite in_app_iff in Hbnd.
    rewrite H1, H, H0; auto. 
  - (*Fbinop*)
    alpha_case fm2 Heq. bool_hyps. simpl_set.
    simpl_set. rewrite in_app_iff in Hbnd.
    rewrite H1, H, H0; auto. 
  - (*Fnot*)
    alpha_case fm2 Heq.
    apply H; auto.
  - (*Ftrue*)
    alpha_case fm2 Heq; auto.
  - (*Ffalse*)
    alpha_case fm2 Heq; auto.
  - (*Flet*)
    alpha_case fm2 Heq. simpl_set.
    rewrite in_app_iff in Hbnd. bool_hyps. rewrite H1.
    simpl. bool_to_prop; split.
    + apply H; auto.
    + vsym_eq x v0.
      * vsym_eq v0 v0. vsym_eq v v0.
        pose proof (alpha_f_equiv_dup_fst f fm2 v0 v0 y nil v1 v2).
        simpl in H7.
        rewrite H7; auto.
        not_or Hy. auto.
      * vsym_eq v0 x. vsym_eq v x.
        not_or Hy.
        apply H0 with(v1:=(v, v0) :: v1); auto; simpl; intros [Heq | Hin]; subst;
        auto.
  - (*Fif*)
    alpha_case fm2 Heq. simpl_set.
    rewrite !in_app_iff in Hbnd. bool_hyps.
    rewrite H, H0, H1; auto.
  - (*Fmatch - exact same as Tmatch (except we use [alpha_f_equiv_dup]) *)
    alpha_case fm2 Heq.
    bool_hyps; repeat simpl_sumbool. clear H4.
    rewrite in_app_iff in Hbnd.
    simpl_set_small. not_or Hy.
    rewrite map_length, H5, H; auto. simpl.
    clear Hy Hy1 H.
    rename Hy0 into Hfree.
    rename Hy2 into Hbnd.
    rename l into ps2.
    nested_ind_case. rewrite all2_cons in H2, H6 |- *.
    bool_hyps.
    destruct a.
    inversion H0; subst. 
    destruct p as [p1 t1].
    case_in.
    + unfold add_vals.
      rewrite H; simpl.
      bool_to_prop;
      split_all; auto.
      2: { apply IHps; auto; intro C; [apply Hbnd | apply Hfree]; simpl; simpl_set; wf_tac. }
      simpl in i.
      apply Nat.eqb_eq in H6.
      rewrite <- same_in_p_fv in i. 2: apply H10. simpl in i.
      destruct (in_combine_split_l _ _ vs_d vs_d _ i H6) as 
        [n [v1' [v2' [Hn [Hx Hcomb]]]]]. simpl in Hcomb.
      rewrite Hcomb, <- app_assoc.
      simpl.
      rewrite (app_assoc v2' v1).
      rewrite (alpha_f_equiv_dup_fst f t1 x _ _ v1' (v2' ++ v1) v2); auto.
      * rewrite <- app_assoc.
        replace (v1' ++ (x, nth n (pat_fv p1) vs_d) :: v2' ++ v1 ++ v2) with
        ((v1' ++ (x, nth n (pat_fv p1) vs_d) :: v2') ++ (v1 ++ v2)) by 
        (rewrite <- !app_assoc; reflexivity).
        rewrite <- Hcomb. auto.
      * intro C; apply Hfree; simpl; simpl_set.
        left. split; auto. intro C1.
        apply Hbnd. simpl. wf_tac.
    + (*In this case, we need to do substitution*)
      simpl.
      apply Nat.eqb_eq in H6.
      simpl in H.
      rewrite H; simpl.
      bool_to_prop; split.
      * unfold add_vals.
        rewrite app_assoc. apply (Hp t1 x y (combine (pat_fv p0) (pat_fv p1) ++ v1)); auto.
        -- intro C. apply Hbnd. simpl. wf_tac.
        -- intro C. apply Hfree. simpl. simpl_set. left; split; wf_tac.
          intro C1. apply Hbnd. simpl; wf_tac.
        -- rewrite map_app. wf_tac; auto. intro C.
          destruct C; auto. simpl in n.
          apply same_in_p_fv in H10. apply H10 in H11.
          contradiction.
        -- rewrite map_app. wf_tac; intro C.
          destruct C; auto. apply Hbnd. simpl. wf_tac.
        -- rewrite <- app_assoc. auto.
      * apply IHps; auto. (*TODO: use free_bnd_tac*)
        -- intro C. apply Hbnd. simpl. wf_tac.
        -- intro C. apply Hfree. simpl. simpl_set; wf_tac.
Qed.

(*Corollaries*)
Definition alpha_equiv_sub_t_full t := proj_tm alpha_equiv_sub t.
Definition alpha_equiv_sub_f_full f := proj_fmla alpha_equiv_sub f.

(*How a substitution changes alpha equivalence*)
Corollary alpha_equiv_sub_t (t: term) (x y: vsymbol)
  (Htys: snd x = snd y)
  (Hbnd: ~ In y (bnd_t t))
  (Hfree: ~ In y (term_fv t)):
  alpha_equiv_t [(x, y)] t (sub_t x y t).
Proof.
  apply alpha_equiv_sub_t_full with(v1:=nil)(v2:=nil); simpl; auto.
  - apply same_in_t_refl.
  - apply a_equiv_t_refl.
Qed.

Corollary alpha_equiv_sub_f (f: formula) (x y: vsymbol)
  (Htys: snd x = snd y)
  (Hbnd: ~ In y (bnd_f f))
  (Hfree: ~ In y (form_fv f)):
  alpha_equiv_f [(x, y)] f (sub_f x y f).
Proof.
  apply alpha_equiv_sub_f_full with(v1:=nil)(v2:=nil); simpl; auto.
  - apply same_in_f_refl.
  - apply a_equiv_f_refl.
Qed.

(*We need 2 more results about [same_in] - it is unchanged by
  substitution (for new variable) and it is transitive*)

Lemma same_in_sub (t: term) (f: formula):
  (forall (x y z: vsymbol),
  z <> x ->
  z <> y ->
  same_in_t t (sub_t x y t) z) /\
  (forall (x y z: vsymbol),
  z <> x ->
  z <> y ->
  same_in_f f (sub_f x y f) z).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; auto.
  - vsym_eq v z.
    + vsym_eq x z. vsym_eq z z.
    + vsym_eq x v.
      * vsym_eq y z.
      * vsym_eq v z.
  - induction l1; simpl; auto. rewrite all2_cons. inversion H; subst.
    specialize (IHl1 H5).
    bool_to_prop.
    apply andb_true_iff in IHl1. destruct IHl1 as [Hlens Hall].
    rewrite Hlens, H4, Hall; auto.
  - rewrite H; auto; simpl.
    rewrite eqb_reflx.
    vsym_eq x v.
    + apply same_in_t_refl.
    + apply H0; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H, map_length, Nat.eqb_refl; auto. simpl.
    induction ps; simpl; intros; auto.
    rewrite all2_cons. inversion H0; subst.
    case_in.
    + rewrite Nat.eqb_refl, same_in_p_refl, same_in_t_refl, IHps; auto.
    + rewrite Nat.eqb_refl, same_in_p_refl; simpl.
      rewrite H5, IHps; auto.
  - vsym_eq x v; rewrite eqb_reflx.
    + rewrite same_in_f_refl; auto.
    + rewrite H; auto.
  - induction tms; simpl; auto. rewrite all2_cons. inversion H; subst.
    specialize (IHtms H5).
    bool_to_prop.
    apply andb_true_iff in IHtms. destruct IHtms as [Hlens Hall].
    rewrite Hlens, H4, Hall; auto.
  - vsym_eq x v; rewrite eqb_reflx; [apply same_in_f_refl | apply H]; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0; auto.
  - rewrite H, eqb_reflx; auto.
    vsym_eq x v; [apply same_in_f_refl | apply H0]; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H, map_length, Nat.eqb_refl; auto; simpl.
    induction ps; simpl; auto.
    rewrite all2_cons. inversion H0; subst.
    case_in; rewrite Nat.eqb_refl, same_in_p_refl; simpl.
    + rewrite same_in_f_refl, IHps; auto.
    + rewrite H5, IHps; auto.
Qed. 

Definition same_in_sub_t t := proj_tm same_in_sub t.
Definition same_in_sub_f f := proj_fmla same_in_sub f.

Lemma same_in_p_trans (p1 p2 p3: pattern) x:
  same_in_p p1 p2 x ->
  same_in_p p2 p3 x ->
  same_in_p p1 p3 x.
Proof.
  revert p2 p3. induction p1; simpl; intros p2 p3 Hp12 Hp23; intros;
  alpha_case p2 Hp12; alpha_case p3 Hp23; auto.
  - vsym_eq v x; vsym_eq v0 x.
  - bool_hyps.
    apply Nat.eqb_eq in H2, H0.
    rewrite H2, H0, Nat.eqb_refl. simpl.
    rename H2 into Hlen1.
    rename H0 into Hlen2.
    rename l0 into ps2.
    rename l2 into ps3.
    generalize dependent ps3.
    generalize dependent ps2.
    induction ps; simpl; intros; destruct ps2; inversion Hlen1; auto;
    destruct ps3; inversion Hlen2; simpl in *.
    rewrite all2_cons in H3, H1 |- *; bool_hyps.
    inversion H; subst.
    rewrite (H8 p), (IHps H9 ps2); auto.
  - revert Hp12 Hp23; bool_to_prop; intros; destruct_all.
    rewrite (IHp1_1 p2_1), (IHp1_2 p2_2); auto.
  - revert Hp12 Hp23; bool_to_prop; intros; destruct_all.
    rewrite (IHp1 p2); auto.
    vsym_eq v x; vsym_eq v0 x.
Qed.
    
(*Annoying to prove - repetitive, can be automated I expect*)
Lemma same_in_trans (t: term) (f: formula):
  (forall (t2 t3: term) x
    (Hs1: same_in_t t t2 x)
    (Hs2: same_in_t t2 t3 x),
    same_in_t t t3 x) /\
  (forall (f2 f3: formula) x
    (Hs1: same_in_f f f2 x)
    (Hs2: same_in_f f2 f3 x),
    same_in_f f f3 x).
Proof.
  revert t f. apply term_formula_ind; simpl; auto; intros.
  - alpha_case t2 Hs1. alpha_case t3 Hs2. auto.
  - alpha_case t2 Hs1. alpha_case t3 Hs2. 
    vsym_eq v x; vsym_eq v0 x.
  - alpha_case t2 Hs1. alpha_case t3 Hs2. bool_hyps.
    apply Nat.eqb_eq in H2, H0.
    rewrite H2, H0, Nat.eqb_refl. simpl.
    rename H2 into Hlen1.
    rename H0 into Hlen2.
    generalize dependent l4. generalize dependent l2.
    induction l1; simpl; intros; destruct l2; inversion Hlen1; auto;
    destruct l4; inversion Hlen2.
    rewrite all2_cons in H3, H1 |- *.
    inversion H; subst.
    bool_hyps; bool_to_prop; split.
    + rewrite H6; auto. apply H3. apply H0.
    + apply IHl1 with(l2:=l2); auto.
  - alpha_case t2 Hs1. alpha_case t3 Hs2.
    bool_hyps.
    rewrite (H t2_1), (H0 t2_2); auto. simpl.
    vsym_eq v x; vsym_eq v0 x; vsym_eq v1 x.
  - alpha_case t0 Hs1. alpha_case t3 Hs2. bool_hyps.
    rewrite (H f0), (H0 t0_1), (H1 t0_2); auto.
  - alpha_case t2 Hs1. alpha_case t3 Hs2. bool_hyps.
    apply Nat.eqb_eq in H4, H1.
    rename H4 into Hlen1.
    rename H1 into Hlen2.
    rename l into ps2.
    rename l0 into ps3.
    rewrite (H t2), Hlen1, Hlen2, Nat.eqb_refl; auto; simpl.
    clear H6 H3. generalize dependent ps3.
    generalize dependent ps2.
    induction ps; simpl; intros; destruct ps2; inversion Hlen1; auto;
    destruct ps3; inversion Hlen2; simpl in *.
    rewrite all2_cons in H2, H5 |- *.
    bool_hyps.
    apply Nat.eqb_eq in H5, H1.
    inversion H0; subst.
    rewrite H5, H1, Nat.eqb_refl, (same_in_p_trans _ (fst p)), (H13 (snd p)),
    (IHps H14 ps2); auto.
  - alpha_case t2 Hs1. alpha_case t3 Hs2. bool_hyps.
    rewrite (H f0); auto. vsym_eq v x; vsym_eq v0 x; vsym_eq v1 x.
  - alpha_case f2 Hs1. alpha_case f3 Hs2. bool_hyps.
    apply Nat.eqb_eq in H2, H0.
    rewrite H2, H0, Nat.eqb_refl. simpl.
    rename H2 into Hlen1.
    rename H0 into Hlen2.
    generalize dependent l2. generalize dependent l0.
    induction tms; simpl; intros; destruct l0; inversion Hlen1; auto;
    destruct l2; inversion Hlen2.
    rewrite all2_cons in H3, H1 |- *.
    inversion H; subst. bool_hyps.
    bool_to_prop; split.
    + rewrite H6; auto. apply H3. apply H0.
    + apply IHtms with(l0:=l0); auto.
  - alpha_case f2 Hs1. alpha_case f3 Hs2. bool_hyps.
    rewrite (H f2); auto. vsym_eq v x; vsym_eq v0 x; vsym_eq v1 x.
  - alpha_case f2 Hs1. alpha_case f3 Hs2. bool_hyps.
    rewrite (H t), (H0 t0); auto.
  - alpha_case f0 Hs1. alpha_case f3 Hs2. bool_hyps.
    rewrite (H f0_1), (H0 f0_2); auto.
  - alpha_case f2 Hs1. alpha_case f3 Hs2.
    apply (H f2); auto.
  - alpha_case f2 Hs1. alpha_case f3 Hs2. auto.
  - alpha_case f2 Hs1. alpha_case f3 Hs2. auto.
  - alpha_case f2 Hs1. alpha_case f3 Hs2. bool_hyps.
    rewrite (H t), (H0 f2); auto. vsym_eq v x; vsym_eq v0 x; vsym_eq v1 x.
  - alpha_case f0 Hs1. alpha_case f4 Hs2. bool_hyps.
    rewrite (H f0_1), (H0 f0_2), (H1 f0_3); auto.
  - alpha_case f2 Hs1. alpha_case f3 Hs2. bool_hyps.
    apply Nat.eqb_eq in H4, H1.
    rename H4 into Hlen1.
    rename H1 into Hlen2.
    rename l into ps2.
    rename l0 into ps3.
    rewrite (H t), Hlen1, Hlen2, Nat.eqb_refl; auto; simpl.
    generalize dependent ps3.
    generalize dependent ps2.
    induction ps; simpl; intros; destruct ps2; inversion Hlen1; auto;
    destruct ps3; inversion Hlen2; simpl in *.
    rewrite all2_cons in H5, H2 |- *. bool_hyps.
    apply Nat.eqb_eq in H5, H1.
    inversion H0; subst.
    rewrite H5, H1, Nat.eqb_refl, (same_in_p_trans _ (fst p)), (H15 (snd p)),
    (IHps H16 ps2); auto.
Qed.

Definition same_in_t_trans t := proj_tm same_in_trans t.
Definition same_in_f_trans f := proj_fmla same_in_trans f. 

Lemma same_in_sub_ts (t: term) vs z:
  ~ In z (map fst vs) ->
  ~ In (fst z) (map snd vs) ->
  same_in_t t (sub_ts vs t) z.
Proof.
  intros; induction vs; simpl in *.
  - apply same_in_t_refl.
  - not_or Hz. eapply same_in_t_trans.
    apply IHvs; auto.
    apply same_in_sub_t; auto. intro Heq.
    subst. contradiction.
Qed. 

Lemma same_in_sub_fs (f: formula) vs z:
  ~ In z (map fst vs) ->
  ~ In (fst z) (map snd vs) ->
  same_in_f f (sub_fs vs f) z.
Proof.
  intros; induction vs; simpl in *.
  - apply same_in_f_refl.
  - not_or Hz. eapply same_in_f_trans.
    apply IHvs; auto.
    apply same_in_sub_f; auto. intro Heq.
    subst. contradiction.
Qed.

End AlphaSub.

(*Now that we have our structural results, we prove results
  about alpha equivalence of let, quantifiers, and match statements.
  This means that we should never again need to unfold the
  definition of alpha equivalence or work inductively over the list*)
Section API.

(*These results, with all our work, are easy*)
Lemma alpha_convert_quant
  (q: quant) (v1 v2: vsymbol) (Heq: snd v1 = snd v2) (f: formula)
  (Hbnd: ~In v2 (bnd_f f))
  (Hfree: ~In v2 (form_fv f)):
  a_equiv_f (Fquant q v1 f) (Fquant q v2 (sub_f v1 v2 f)).
Proof.
  unfold a_equiv_f. simpl.
  bool_to_prop; split_all; try solve[simpl_sumbool].
  apply alpha_equiv_sub_f; auto.
Qed.

Lemma alpha_convert_tlet 
  (v1 v2: vsymbol) (Heq: snd v1 = snd v2) (tm1 tm2: term)
  (Hbnd: ~In v2 (bnd_t tm2))
  (Hfree: ~In v2 (term_fv tm2)):
  a_equiv_t (Tlet tm1 v1 tm2) (Tlet tm1 v2 (sub_t v1 v2 tm2)).
Proof.
  unfold a_equiv_t.
  simpl. destruct (vty_eq_dec (snd v1) (snd v2)); simpl; auto.
  bool_to_prop. split.
  - apply alpha_t_equiv_same; simpl; intros. destruct H.
  - apply alpha_equiv_sub_t; auto.
Qed.

Lemma alpha_convert_flet 
  (v1 v2: vsymbol) (Heq: snd v1 = snd v2) (t1: term) (f2: formula)
  (Hbnd: ~In v2 (bnd_f f2))
  (Hfree: ~In v2 (form_fv f2)):
  a_equiv_f (Flet t1 v1 f2) (Flet t1 v2 (sub_f v1 v2 f2)).
Proof.
  unfold a_equiv_f.
  simpl. destruct (vty_eq_dec (snd v1) (snd v2)); simpl; auto.
  bool_to_prop. split.
  - apply alpha_t_equiv_same; simpl; intros. destruct H.
  - apply alpha_equiv_sub_f; auto.
Qed.

Lemma alpha_convert_teps
  (v1 v2: vsymbol) (Heq: snd v1 = snd v2) (f: formula)
  (Hbnd: ~In v2 (bnd_f f))
  (Hfree: ~In v2 (form_fv f)):
  a_equiv_t (Teps f v1) (Teps (sub_f v1 v2 f) v2).
Proof.
  unfold a_equiv_t. simpl.
  rewrite Heq, eq_dec_refl; simpl.
  apply alpha_equiv_sub_f; auto.
Qed.

(*Congruences*)

Lemma alpha_tlet_congr v1 tm1 tm2 tm3 tm4:
  a_equiv_t tm1 tm3 ->
  a_equiv_t tm2 tm4 ->
  a_equiv_t (Tlet tm1 v1 tm2) (Tlet tm3 v1 tm4).
Proof.
  unfold a_equiv_t; simpl; intros.
  rewrite H, eq_dec_refl; simpl_bool.
  apply a_equiv_t_expand; simpl; auto.
  intros x [Hx | []]; subst; auto.
Qed.

(*And from transitivity:*)
Lemma alpha_convert_tlet':
forall v1 v2 : vsymbol,
  snd v1 = snd v2 ->
  forall tm1 tm2 tm3 tm4 : term,
  ~ In v2 (bnd_t tm4) ->
  ~ In v2 (term_fv tm4) ->
  a_equiv_t tm1 tm3 ->
  a_equiv_t tm2 tm4 ->
  a_equiv_t (Tlet tm1 v1 tm2) (Tlet tm3 v2 (sub_t v1 v2 tm4)).
Proof.
  intros.
  eapply a_equiv_t_trans.
  2: apply alpha_convert_tlet; auto.
  apply alpha_tlet_congr; auto.
Qed.

Lemma alpha_teps_congr v f1 f2:
  a_equiv_f f1 f2 ->
  a_equiv_t (Teps f1 v) (Teps f2 v).
Proof.
  unfold a_equiv_f, a_equiv_t; simpl; intros.
  rewrite eq_dec_refl; simpl.
  apply a_equiv_f_expand; auto; simpl;
  intros x [Hx | []]; subst; auto.
Qed.

Lemma alpha_convert_teps': forall v1 v2,
  snd v1 = snd v2 ->
  forall f1 f2: formula,
  ~ In v2 (bnd_f f2) ->
  ~ In v2 (form_fv f2) ->
  a_equiv_f f1 f2 ->
  a_equiv_t (Teps f1 v1) (Teps (sub_f v1 v2 f2) v2).
Proof.
  intros. eapply a_equiv_t_trans.
  2: apply alpha_convert_teps; auto.
  apply alpha_teps_congr; auto.
Qed.

Lemma alpha_quant_congr q v f1 f2:
  a_equiv_f f1 f2 ->
  a_equiv_f (Fquant q v f1) (Fquant q v f2).
Proof.
  unfold a_equiv_f; simpl; intros.
  rewrite !eq_dec_refl; simpl.
  apply a_equiv_f_expand; auto; simpl;
  intros x [Hx | []]; subst; auto.
Qed.

Lemma alpha_convert_quant': forall q v1 v2,
  snd v1 = snd v2 ->
  forall f1 f2: formula,
  ~ In v2 (bnd_f f2) ->
  ~ In v2 (form_fv f2) ->
  a_equiv_f f1 f2 ->
  a_equiv_f (Fquant q v1 f1) (Fquant q v2 (sub_f v1 v2 f2)).
Proof.
  intros. eapply a_equiv_f_trans.
  2: apply alpha_convert_quant; auto.
  apply alpha_quant_congr; auto.
Qed.

Lemma alpha_tfun_congr f tys tms1 tms2:
  length tms1 = length tms2 ->
  Forall (fun x => a_equiv_t (fst x) (snd x)) (combine tms1 tms2) ->
  a_equiv_t (Tfun f tys tms1) (Tfun f tys tms2).
Proof.
  unfold a_equiv_t. simpl. intros Hlen Hall.
  bool_to_prop; split_all; try simpl_sumbool; 
    [rewrite Hlen; apply Nat.eqb_refl |].
  generalize dependent tms2.
  induction tms1; simpl; intros; destruct tms2; inversion Hlen; auto.
  inversion Hall; subst.
  rewrite all2_cons. bool_to_prop; split; auto.
Qed.

Lemma alpha_fpred_congr f tys tms1 tms2:
  length tms1 = length tms2 ->
  Forall (fun x => a_equiv_t (fst x) (snd x)) (combine tms1 tms2) ->
  a_equiv_f (Fpred f tys tms1) (Fpred f tys tms2).
Proof.
  unfold a_equiv_f. simpl. intros Hlen Hall.
  bool_to_prop; split_all; try simpl_sumbool; 
    [rewrite Hlen; apply Nat.eqb_refl |].
  generalize dependent tms2.
  induction tms1; simpl; intros; destruct tms2; inversion Hlen; auto.
  inversion Hall; subst.
  rewrite all2_cons; bool_to_prop; split; auto.
Qed.

Lemma alpha_tif_congr f1 t1 t2 f2 t3 t4:
  a_equiv_f f1 f2 ->
  a_equiv_t t1 t3 ->
  a_equiv_t t2 t4 ->
  a_equiv_t (Tif f1 t1 t2) (Tif f2 t3 t4).
Proof.
  unfold a_equiv_t, a_equiv_f; simpl; intros Hf Ht1 Ht2;
  rewrite Hf, Ht1, Ht2; reflexivity.
Qed.

Lemma alpha_feq_congr ty t1 t2 t3 t4:
  a_equiv_t t1 t2 ->
  a_equiv_t t3 t4 ->
  a_equiv_f (Feq ty t1 t3) (Feq ty t2 t4).
Proof.
  unfold a_equiv_t, a_equiv_f; intros; simpl;
  rewrite eq_dec_refl, H, H0; auto.
Qed.

Lemma alpha_fbinop_congr b f1 f2 f3 f4:
  a_equiv_f f1 f2 ->
  a_equiv_f f3 f4 ->
  a_equiv_f (Fbinop b f1 f3) (Fbinop b f2 f4).
Proof.
  unfold a_equiv_f; intros; simpl;
  rewrite eq_dec_refl, H, H0; auto.
Qed.

Lemma alpha_flet_congr v1 tm1 tm2 f1 f2:
  a_equiv_t tm1 tm2 ->
  a_equiv_f f1 f2 ->
  a_equiv_f (Flet tm1 v1 f1) (Flet tm2 v1 f2).
Proof.
  unfold a_equiv_t, a_equiv_f; simpl; intros.
  rewrite H, eq_dec_refl; simpl_bool.
  apply a_equiv_f_expand; simpl; auto.
  intros x [Hx | []]; subst; auto.
Qed.

(*And from transitivity:*)
Lemma alpha_convert_flet':
forall v1 v2 : vsymbol,
  snd v1 = snd v2 ->
  forall tm1 tm2 f1 f2,
  ~ In v2 (bnd_f f2) ->
  ~ In v2 (form_fv f2) ->
  a_equiv_t tm1 tm2 ->
  a_equiv_f f1 f2 ->
  a_equiv_f (Flet tm1 v1 f1) (Flet tm2 v2 (sub_f v1 v2 f2)).
Proof.
  intros.
  eapply a_equiv_f_trans.
  2: apply alpha_convert_flet; auto.
  apply alpha_flet_congr; auto.
Qed.

Lemma alpha_fif_congr f1 f2 f3 f4 f5 f6:
  a_equiv_f f1 f2 ->
  a_equiv_f f3 f4 ->
  a_equiv_f f5 f6 ->
  a_equiv_f (Fif f1 f3 f5) (Fif f2 f4 f6).
Proof.
  unfold a_equiv_f; simpl; intros Hf Ht1 Ht2;
  rewrite Hf, Ht1, Ht2; reflexivity.
Qed.

Lemma alpha_fnot_congr f1 f2:
  a_equiv_f f1 f2 ->
  a_equiv_f (Fnot f1) (Fnot f2).
Proof.
  unfold a_equiv_f; simpl; auto.
Qed.

End API.

(*We need some iterated versions of the above free variable lemmas
  and congruence lemmas: we do terms and formulas together by
  generalizing *)
Section Iter.

Context {A: Type}.
Variable sub: vsymbol -> vsymbol -> A -> A.
Variable free_in: vsymbol -> A -> bool.
Variable sub_notin: forall (t: A) (x y: vsymbol), x <> y ->
  free_in x (sub x y t) = false.
Variable sub_diff: forall (t: A) (x y z: vsymbol),
  z <> x -> z <> y -> free_in z (sub x y t) = free_in z t.
Notation subs := (sub_mult sub).
(*For bound vars*)
Variable bnd: A -> list vsymbol.
Variable bnd_sub : forall (t: A) (x y: vsymbol),
  bnd (sub x y t) = bnd t.

(*The iterated version of [sub_fv_notin]. Awkward to state so
  that we can prove term and formula versions together*)
(*TODO: move some of this to Substitution*)
Lemma sub_mult_fv_notin
  (vars: list (vsymbol * string)) (t: A)
  (Hn: NoDup (map fst vars))
  (Huniq: forall x, In x (map fst vars) -> ~ In (fst x) (map snd vars)):
  forall x, In x (map fst vars) -> free_in x (subs vars t) = false.
Proof.
  induction vars; simpl; intros. destruct H.
  destruct H; subst.
  - rewrite sub_notin; auto.
    destruct a as[v str]; destruct v as [nm ty]; simpl in *; intro C;
    inversion C; subst.
    apply (Huniq (str, ty)); simpl; triv.
  - inversion Hn; subst. 
    rewrite sub_diff; auto.
    + apply IHvars; auto.
      intros. intro C.
      apply (Huniq x0); simpl; triv.
    + intro C; subst. contradiction.
    + destruct a; destruct v; simpl in *; intro C; inversion C; subst.
      apply (Huniq (s, v)); triv.
Qed.

Lemma sub_mult_fv_diff (vars: list (vsymbol * string)) (t: A):
  forall x, ~ In x (map fst vars) -> 
    ~ In x (combine (map snd vars) (map snd (map fst vars))) ->
  free_in x (subs vars t) = free_in x t.
Proof.
  intros x Hn1 Hn2.
  induction vars; simpl; auto.
  simpl in Hn1, Hn2. not_or Hn.
  rewrite sub_diff; auto.
Qed.

Lemma bnd_subs vars (t: A):
  bnd (subs vars t) = bnd t.
Proof.
  induction vars; simpl; auto.
  rewrite bnd_sub; assumption.
Qed.

Variable sub_eq: forall t x, sub x x t = t.

Lemma free_in_sub_impl (t: A) (x y z: vsymbol):
free_in z (sub x y t) ->
free_in z t \/ z = y.
Proof.
  vsym_eq x y.
  - rewrite sub_eq; intros; auto.
  - vsym_eq z x.
    + rewrite sub_notin; auto.
    + vsym_eq z y.
      rewrite sub_diff; auto.
Qed.

Lemma free_in_subs_impl (t: A) (x: vsymbol) l:
free_in x (subs l t) ->
free_in x t \/ In (fst x) (map snd l).
Proof.
  induction l; simpl; auto; intros.
  apply free_in_sub_impl in H.
  destruct H; subst; simpl; auto.
  apply IHl in H.
  destruct H; auto.
Qed.

Variable alpha: list (vsymbol * vsymbol) -> A -> A -> bool.
Notation a_eq := (alpha nil).
Variable fv : A -> list vsymbol.
Variable alpha_sym: forall t1 t2 l,
  alpha l t1 t2 = alpha (flip l) t2 t1.
Variable alpha_redundant: forall t1 t2 x v1 v2,
  ~ In x (map fst v2) ->
  ~ In x (map snd v2) ->
  alpha (v1 ++ (x, x) :: v2) t1 t2 =
  alpha (v1 ++ v2) t1 t2.
Variable alpha_trans: forall t1 t2 t3 v1 v2,
  map snd v1 = map fst v2 ->
  alpha v1 t1 t2 ->
  alpha v2 t2 t3 ->
  alpha (alist_trans v1 v2) t1 t3.

(*Prove congruence lemma for sub*)
Variable alpha_sub: forall t x y,
  snd x = snd y ->
  ~ In y (bnd t) ->
  ~ In y (fv t) -> alpha [(x, y)] t (sub x y t).

(*Annoying to show, need lots of transitivity and
strengthening/weakening with [redundant] lemma*)
Lemma a_eq_sub_congr (t1 t2: A) (x y: vsymbol)
  (Hsnd: snd x = snd y)
  (Hbnd1: ~ In y (bnd t1))
  (Hbnd2: ~ In y (bnd t2))
  (Hfree1: ~ In y (fv t1))
  (Hfree2: ~In y (fv t2))
  (Heq: a_eq t1 t2):
  a_eq (sub x y t1) (sub x y t2).
Proof.
  pose proof (alpha_sub _ _ _ Hsnd Hbnd1 Hfree1) as Heq1.
  pose proof (alpha_sub _ _ _ Hsnd Hbnd2 Hfree2) as Heq2.
  rewrite alpha_sym in Heq1.
  simpl in Heq1.
  assert (Heq3: alpha [(x, x)] t1 t2) by
    (rewrite alpha_redundant with(v1:=nil)(v2:=nil)(x:=x); auto).
  assert (Hmap: map snd [(y, x)] = map fst [(x, x)]) by reflexivity.
  pose proof (alpha_trans _ _ _ _ _ Hmap Heq1 Heq3).
  simpl in H.
  assert (Hmap2: map snd [(y, x)] = map fst [(x, y)]) by reflexivity.
  pose proof (alpha_trans _ _ _ _ _ Hmap2 H Heq2).
  simpl in H0.
  rewrite alpha_redundant with (x:=y)(v1:=nil)(v2:=nil) in H0; auto.
Qed.

Variable free_in_spec: forall t x,
  free_in x t <-> In x (fv t).

Lemma a_equiv_subs_congr (t1 t2: A) 
  (vars: list (vsymbol * string))
  (Hbnd1: forall x, In (fst x) (map snd vars) -> ~ In x (bnd t1))
  (Hbnd2: forall x, In (fst x) (map snd vars) -> ~ In x (bnd t2))
  (Hfree1: forall x, In (fst x) (map snd vars) -> ~ In x (fv t1))
  (Hfree2: forall x, In (fst x) (map snd vars) -> ~ In x (fv t2))
  (Hn: NoDup (map snd vars))
  (Heq: a_eq t1 t2):
  a_eq (subs vars t1) (subs vars t2).
Proof.
  induction vars; simpl; auto.
  simpl in *.
  inversion Hn; subst.
  apply a_eq_sub_congr; auto.
  - rewrite bnd_subs; apply Hbnd1; auto.
  - rewrite bnd_subs; apply Hbnd2; auto.
  - intro C. apply free_in_spec in C.
    apply free_in_subs_impl in C.
    destruct C.
    + apply free_in_spec in H.
      apply (Hfree1 (snd a, snd (fst a))); auto.
    + simpl in H. contradiction.
  - intro C. apply free_in_spec in C.
    apply free_in_subs_impl in C.
    destruct C.
    + apply free_in_spec in H.
      apply (Hfree2 (snd a, snd (fst a))); auto.
    + simpl in H. contradiction.
Qed.

End Iter.

(*Now we specialize these results for terms and formulas*)

Definition sub_ts_fv_notin := sub_mult_fv_notin _ _ 
sub_t_fv_notin sub_t_fv_diff.
Definition sub_fs_fv_notin := sub_mult_fv_notin _ _
sub_f_fv_notin sub_f_fv_diff.
Definition sub_ts_fv_diff := sub_mult_fv_diff _ _
sub_t_fv_diff.
Definition sub_fs_fv_diff := sub_mult_fv_diff _ _
sub_f_fv_diff.
Definition bnd_sub_ts := bnd_subs _ _ bnd_sub_t.
Definition bnd_sub_fs := bnd_subs _ _ bnd_sub_f.

Definition a_equiv_t_sub_ts_congr :=
a_equiv_subs_congr _ _ sub_t_fv_notin sub_t_fv_diff _ 
bnd_sub_t sub_t_eq _ _  alpha_t_equiv_sym alpha_equiv_t_redundant
alpha_equiv_t_trans alpha_equiv_sub_t free_in_t_spec.
Definition a_equiv_f_sub_fs_congr :=
a_equiv_subs_congr _ _ sub_f_fv_notin sub_f_fv_diff _ 
bnd_sub_f sub_f_eq _ _  alpha_f_equiv_sym alpha_equiv_f_redundant
alpha_equiv_f_trans alpha_equiv_sub_f free_in_f_spec.

(*Now we want to define a function to rename bound variables to unique
  values such that terms and formulas have no duplicate bound
  variables and no clashes between free and bound variable names.
  This makes many transformations easier.*)

Section Convert.

Definition mk_fun_str (l: list vsymbol) (l2: list string) :
  vsymbol -> vsymbol :=
  mk_fun l (combine l2 (map snd l)).

Notation split l n := (firstn n l, skipn n l).

Fixpoint alpha_t_aux (t: term) (l: list string) {struct t} : term :=
  (*We only care about the bound variable and inductive cases*)
  match t with
  | Tlet t1 x t2 => 
    match l with
    | str :: tl =>
      let (l1, l2) := split tl (length (bnd_t t1)) in 
      Tlet (alpha_t_aux t1 l1) (str, snd x) (sub_t x (str, snd x) 
      (alpha_t_aux t2 l2))
    | _ => t
    end
  | Tfun fs tys tms =>
    (*Split up the list into pieces of appropriate lengths 
      (size (bnd_t tm))*)
    let lens := map (fun tm => length (bnd_t tm)) tms in
    let l_split := split_lens l lens in
    Tfun fs tys (map2 (fun (tm: term) (l': list string) =>
    alpha_t_aux tm l') tms l_split)
  | Tif f t1 t2 =>
    let f_sz := length (bnd_f f) in
    let t1_sz := length (bnd_t t1) in
    let (l1, lrest) := split l f_sz in
    let (l2, l3) := split lrest t1_sz in
    Tif (alpha_f_aux f l1) 
      (alpha_t_aux t1 l2)
      (alpha_t_aux t2 l3)
  | Tmatch t1 ty ps =>
    (*First do the pattern substitutions, then do the terms
      recursively*)
    let lens := map (fun x => length (pat_fv (fst x)) + 
      length (bnd_t (snd x))) ps in
    let t1_sz := length (bnd_t t1) in
    let (l1, l2) := split l (t1_sz) in
    let l_split := split_lens l2 lens in
    
    Tmatch (alpha_t_aux t1 l1) ty
      (map2 (fun (x: pattern * term) (strs: list string) =>
        let p_sz := length (pat_fv (fst x)) in
        let (l1, l2) := split strs p_sz in
        let t2 := alpha_t_aux (snd x) l2 in
        let vars := combine (pat_fv (fst x)) l1 in
        (map_pat (mk_fun_str (pat_fv (fst x)) l1) (fst x), sub_ts vars t2)) ps l_split)
  | Teps f v =>
    match l with
    | nil => t
    | str :: tl =>
      let v' := (str, snd v) in
      Teps (sub_f v v' (alpha_f_aux f tl)) v'
    end
  | _ => t (*no other bound variables/recursive cases*)
  end
with alpha_f_aux (f: formula) (l: list string) {struct f} : formula :=
  match f with
  | Fpred ps tys tms =>
    (*Split up the list into pieces of appropriate lengths 
      (size (bnd_t tm))*)
    let lens := map (fun tm => length (bnd_t tm)) tms in
    let l_split := split_lens l lens in
    Fpred ps tys (map2 (fun (t: term) (l': list string) =>
      alpha_t_aux t l') tms l_split)
  | Fquant q v f1 =>
      match l with
      | str :: tl =>
        let v' := (str, snd v) in
        Fquant q v' (sub_f v v' (alpha_f_aux f1 tl))
      | _ => f
      end
  | Feq ty t1 t2 =>
    let t_sz := length (bnd_t t1) in
    let (l1, l2) := split l t_sz in
    Feq ty (alpha_t_aux t1 l1)
      (alpha_t_aux t2 l2)
  | Fbinop b f1 f2 =>
    let f_sz := length (bnd_f f1) in
    let (l1, l2) := split l f_sz in
    Fbinop b (alpha_f_aux f1 l1)
      (alpha_f_aux f2 l2)
  | Fnot f1 =>
    Fnot (alpha_f_aux f1 l)
  | Flet t v f1 =>
    match l with
    | str :: tl =>
      let (l1, l2) := split tl (length (bnd_t t)) in 
      Flet (alpha_t_aux t l1) (str, snd v) (sub_f v (str, snd v) 
      (alpha_f_aux f1 l2))
    | _ => f
    end
  | Fif f1 f2 f3 =>
    let f1_sz := length (bnd_f f1) in
    let f2_sz := length (bnd_f f2) in
    let (l1, lrest) := split l f1_sz in
    let (l2, l3) := split lrest f2_sz in
    Fif (alpha_f_aux f1 l1) 
      (alpha_f_aux f2 l2)
      (alpha_f_aux f3 l3)
  | Fmatch t1 ty ps =>
    (*First do the pattern substitutions, then do the terms
      recursively*)
    let lens := map (fun x => length (pat_fv (fst x)) + 
    length (bnd_f (snd x))) ps in
    let t1_sz := length (bnd_t t1) in
    let (l1, l2) := split l t1_sz in
    let l_split := split_lens l2 lens in
    
    Fmatch (alpha_t_aux t1 l1) ty
      (map2 (fun (x: pattern * formula) (strs: list string) =>
        let p_sz := length (pat_fv (fst x)) in
        let (l1, l2) := split strs p_sz in
        let f2 := alpha_f_aux (snd x) l2 in
        let vars := combine (pat_fv (fst x)) l1 in
        (map_pat (mk_fun_str (pat_fv (fst x)) l1) (fst x), sub_fs vars f2)) ps l_split)
  | _ => f (*No other bound/recursive cases*)
  end.

(*Some lemmas about [mk_fun_str] and pattern free vars*)

Lemma map_pat_str_fv (strs: list string) (p: pattern) :
  length (pat_fv p) = length strs ->
  NoDup strs ->
  pat_fv (map_pat (mk_fun_str (pat_fv p) strs) p) = map (mk_fun_str (pat_fv p) strs) (pat_fv p).
Proof.
  intros.
  apply map_pat_free_vars. intros.
  unfold mk_fun_str in H3.
  apply mk_fun_inj in H3; auto.
  - apply NoDup_pat_fv.
  - apply NoDup_combine_l; auto.
  - rewrite H.
    unfold vsymbol. (*otherwise rewrite fails*)
    rewrite combine_length, map_length, <- H, Nat.min_id.
    apply Nat.le_refl.
Qed.

Lemma in_map_pat_str_fv_iff (strs: list string) (p: pattern):
  length (pat_fv p) = length strs ->
  NoDup strs ->
  forall x, In x (pat_fv (map_pat (mk_fun_str (pat_fv p) strs) p)) <->
    In x (combine strs (map snd (pat_fv p))).
Proof.
  intros. rewrite map_pat_str_fv; auto.
  rewrite in_map_iff.
  split; intros.
  - destruct H1 as [y [Hx Hiny]]; subst.
    unfold mk_fun_str.
    pose proof (mk_fun_in (pat_fv p) (combine strs (map snd (pat_fv p))) y).
    unfold vsymbol in H, H1.
    rewrite H, combine_length, map_length, <- H, Nat.min_id in H1.
    apply H1; auto.
  - unfold vsymbol in H1. 
    rewrite in_combine_iff in H1; wf_tac.
    destruct H1 as [i [Hi Hx]].
    specialize (Hx EmptyString vty_int). 
    unfold mk_fun_str.
    exists (nth i (pat_fv p) vs_d).
    split; wf_tac.
    rewrite mk_fun_nth with(d2:=vs_d); unfold vsymbol in *; wf_tac.
    + unfold vs_d.
      rewrite combine_nth; wf_tac.
    + rewrite combine_length, map_length. lia.
Qed.

Corollary in_map_pat_str_fv (strs: list string) (p: pattern):
  length (pat_fv p) = length strs ->
  NoDup strs ->
  forall x, In x (pat_fv (map_pat (mk_fun_str (pat_fv p) strs) p)) ->
    In (fst x) strs.
Proof.
  intros. apply in_map_pat_str_fv_iff in H1; auto.
  unfold vsymbol in H1.
  rewrite in_combine_iff in H1; wf_tac.
  destruct H1 as [i [Hi Hx]].
  specialize (Hx EmptyString vty_int); subst; simpl.
  wf_tac.
Qed.

(*1. The bound variables, after conversion,
  are unique and all from the input list.
  This proof is very tedious and should be improved*)
Lemma alpha_aux_bnd (t: term) (f: formula) :
  (forall (l: list string),
    NoDup l ->
    length l = length (bnd_t t) ->
    NoDup (bnd_t (alpha_t_aux t l)) /\
    (forall x, In x (bnd_t (alpha_t_aux t l)) -> In (fst x) l)) /\
  (forall (l: list string),
    NoDup l ->
    length l = length (bnd_f f) ->
    NoDup (bnd_f (alpha_f_aux f l)) /\
    (forall x, In x (bnd_f (alpha_f_aux f l)) -> In (fst x) l)).
Proof.
  revert t f.
  apply term_formula_ind; simpl; intros; auto.
  - split; [constructor | intros x []]. 
  - split; [constructor | intros x []].
  - (*Tfun case*) 
    split.
    + rewrite NoDup_concat_iff. split.
      * intros x. rewrite in_map_iff.
        intros [t1 [Hbndt1 Hint1]]. subst.
        rewrite in_map2_iff with(d1:=tm_d)(d2:=nil) in Hint1;
        wf_tac.
        destruct Hint1 as [i [Hi Ht1]]; subst.
        rewrite Forall_forall in H.
        apply H; simpl; wf_tac.
      * intros i1 i2 d x. wf_tac.
        intros [Hin1 Hin2].
        (*Idea: suppose in both, then by IH (twice), in 2 different
          parts of l - contradicts NoDup l*)
        rewrite Forall_forall in H.
        rewrite (map2_nth _ _ _ tm_d nil) in Hin1, Hin2; wf_tac.
        apply H in Hin1, Hin2; auto; wf_tac.
        assert (NoDup (concat (split_lens l0 (map (fun t => length (bnd_t t)) l1)))) by
          (rewrite <- split_lens_concat; wf_tac).
          rewrite NoDup_concat_iff in H5.
        split_all. apply (H6 i1 i2 nil (fst x)); wf_tac.
    + intros x. rewrite in_concat. intros [bl [Hinbl Hinx]].
      rewrite in_map_iff in Hinbl.
      destruct Hinbl as [t1 [Ht1 Hint1]]; subst.
      rewrite (in_map2_iff _ _ _ tm_d nil) in Hint1; wf_tac.
      destruct Hint1 as [i [Hi Ht1]]; subst.
      rewrite Forall_forall in H.
      apply H in Hinx; auto; wf_tac.
      rewrite (split_lens_concat l0 (map (fun t => length (bnd_t t)) l1));
      [|wf_tac]. rewrite in_concat. eexists. split; [| apply Hinx]. wf_tac.
  - (*Tlet case*)
    destruct l; inversion H2; simpl.
    inversion H1; subst.
    split.
    + constructor.
      * (*TODO: automate the "In" part*) 
        intro Hin.
        apply in_app_or in Hin.
        destruct Hin.
        -- apply H in H3; wf_tac.
        -- rewrite bnd_sub_t in H3.
          apply H0 in H3; wf_tac. 
      * rewrite NoDup_app_iff'.
        split_all.
        -- apply H; wf_tac.
        -- rewrite bnd_sub_t. apply H0; wf_tac.
        -- intros x.
          rewrite bnd_sub_t.
          intros [Hinx1 Hinx2].
          apply H in Hinx1; wf_tac.
          apply H0 in Hinx2; wf_tac.
          apply (nodup_firstn_skipn Hinx1 Hinx2); auto.
    + intros x [Hx | Hinx]; subst;[left; auto|].
      apply in_app_or in Hinx.
      destruct Hinx as [Hinx | Hinx].
      * apply H in Hinx; wf_tac.
      * rewrite bnd_sub_t in Hinx. apply H0 in Hinx; wf_tac.
  - (*Tif case*)
    split.
    + rewrite !NoDup_app_iff'.
      split_all.
      * apply H; wf_tac.
      * apply H0; wf_tac.
      * apply H1; wf_tac.
      * intros x [Hinx1 Hinx2].
        apply H0 in Hinx1; wf_tac.
        apply H1 in Hinx2; wf_tac.
        apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac. 
      * intros x [Hinx1 Hinx2].
        apply H in Hinx1; wf_tac.
        apply in_app_or in Hinx2. destruct Hinx2.
        -- apply H0 in H4; wf_tac.
          apply (nodup_firstn_skipn Hinx1); wf_tac. 
        -- apply H1 in H4; wf_tac.
          apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x Hinx.
      repeat (apply in_app_or in Hinx; destruct Hinx as [Hinx | Hinx]).
      * apply H in Hinx; wf_tac.
      * apply H0 in Hinx; wf_tac.
      * apply H1 in Hinx; wf_tac. 
  - (*Tmatch case*)
    assert (Hsum: sum (map
        (fun x : pattern * term =>
        Datatypes.length (pat_fv (fst x)) + Datatypes.length (bnd_t (snd x)))
        ps) = Datatypes.length (skipn (Datatypes.length (bnd_t tm)) l)). {
          wf_tac. rewrite H2,length_concat, 
        map_map, Nat.add_comm, Nat.add_sub. f_equal. apply map_ext_in_iff; intros.
        rewrite app_length; auto.
    }
    split.
    + rewrite NoDup_app_iff'; split_all.
      * apply H; wf_tac.
      * rewrite NoDup_concat_iff; split_all.
        -- intros x. rewrite in_map_iff.
          intros [pt1 [Hx Hinx]]; subst.
          rewrite (in_map2_iff _ _ _ (Pwild, tm_d) nil) in Hinx; wf_tac.
          destruct Hinx as [i [Hi Hpt1]].
          rewrite NoDup_app_iff'.
          split_all; subst; wf_tac.
          ++ simpl. rewrite bnd_sub_ts.
            rewrite Forall_forall in H0.
            apply H0; auto; wf_tac.
          ++ intros x. simpl.
            rewrite bnd_sub_ts. 
            intros [Hinx1 Hinx2].
            (*Need this a lot even though it's ugly*)
            apply in_map_pat_str_fv in Hinx1; wf_tac.
            rewrite Forall_forall in H0.
            apply H0 in Hinx2; wf_tac.
            apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
        -- intros i1 i2 d x. wf_tac.
          rewrite !map2_nth with(d1:=(Pwild, tm_d)) (d2:=nil); wf_tac.
          intros [Hini1 Hini2].
          (*Now we get 4 cases need to show each is impossible*)
          destruct Hini1 as [Hini1 | Hini1].
          ++ apply in_map_pat_str_fv in Hini1; wf_tac.
            revert Hini1. wf_tac. intros Hini1.
            apply In_firstn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** apply in_map_pat_str_fv in Hini2; wf_tac.
              revert Hini2. wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** simpl in Hini2.
              rewrite bnd_sub_ts in Hini2.
              rewrite Forall_forall in H0.
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
          ++ simpl in Hini1. 
            rewrite bnd_sub_ts in Hini1.
            rewrite Forall_forall in H0.
            apply H0 in Hini1; wf_tac.
            apply In_skipn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** apply in_map_pat_str_fv in Hini2; wf_tac.
              revert Hini2; wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** simpl in Hini2.
              rewrite bnd_sub_ts in Hini2.
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
      * intros x.
        rewrite in_concat. intros [Hinx1 [l1 [Hinl1 Hinxl1]]].
        apply H in Hinx1; wf_tac.
        rewrite in_map_iff in Hinl1. destruct Hinl1 as [p1 [Hl1 Hinp1]].
        subst.
        rewrite in_map2_iff with(d1:=(Pwild, tm_d))(d2:=nil) in Hinp1; wf_tac.
        destruct Hinp1 as [i [Hi Hp1]]; subst.
        (*And now we have to show these are distinct, will be similar*)
        apply in_app_or in Hinxl1.
        destruct Hinxl1 as [Hinx2 | Hinx2].
        -- apply in_map_pat_str_fv in Hinx2; wf_tac.
          revert Hinx2; wf_tac; intros.
          apply In_firstn in Hinx2.
          apply in_split_lens_ith in Hinx2; wf_tac.
          apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
        -- simpl in Hinx2.
          rewrite bnd_sub_ts in Hinx2.
          rewrite Forall_forall in H0; apply H0 in Hinx2; wf_tac.
          apply In_skipn in Hinx2.
          apply in_split_lens_ith in Hinx2; wf_tac.
          apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
    + (*Second part - TODO very similar to previous*)
      intros x Hinx.
      apply in_app_or in Hinx.
      destruct Hinx as [Hinx | Hinx].
      * apply H in Hinx; wf_tac.
      * rewrite in_concat in Hinx.
        destruct Hinx as [l1 [Hinl1 Hinxl1]].
        rewrite in_map_iff in Hinl1.
        destruct Hinl1 as [p1 [Hl1 Hinp1]].
        subst.
        rewrite in_map2_iff with (d1:=(Pwild, tm_d))(d2:=nil) in Hinp1; wf_tac.
        destruct Hinp1 as [i [Hi Hp1]]; subst.
        apply in_app_or in Hinxl1.
        destruct Hinxl1 as [Hinx | Hinx].
        -- apply in_map_pat_str_fv in Hinx; wf_tac.
          revert Hinx; wf_tac; intros.
          apply in_split_lens_ith in Hinx; wf_tac.
        -- simpl in Hinx.
          rewrite bnd_sub_ts in Hinx.
          rewrite Forall_forall in H0; apply H0 in Hinx; wf_tac.
          apply In_skipn in Hinx.
          apply in_split_lens_ith in Hinx; wf_tac.
  - (*Epsilon case*)
    destruct l; inversion H1; subst; simpl.
    inversion H0; subst.
    rewrite bnd_sub_f.
    split.
    + constructor; [|apply H; wf_tac].
      intro Hin. apply H in Hin; wf_tac.
    + intros. destruct H2; subst; [left; auto | right].
      apply H in H2; wf_tac.
  - (*Fpred case - same as Tfun*)
    split.
    + rewrite NoDup_concat_iff. split.
      * intros x. rewrite in_map_iff.
        intros [t1 [Hbndt1 Hint1]]. subst.
        rewrite in_map2_iff with(d1:=tm_d)(d2:=nil) in Hint1;
        wf_tac.
        destruct Hint1 as [i [Hi Ht1]]; subst.
        rewrite Forall_forall in H.
        apply H; simpl; wf_tac.
      * intros i1 i2 d x. wf_tac.
        intros [Hin1 Hin2].
        (*Idea: suppose in both, then by IH (twice), in 2 different
          parts of l - contradicts NoDup l*)
        rewrite Forall_forall in H.
        rewrite (map2_nth _ _ _ tm_d nil) in Hin1, Hin2; wf_tac.
        apply H in Hin1, Hin2; auto; wf_tac.
        assert (NoDup (concat (split_lens l (map (fun t => length (bnd_t t)) tms)))) by
          (rewrite <- split_lens_concat; wf_tac).
          rewrite NoDup_concat_iff in H5.
        split_all. apply (H6 i1 i2 nil (fst x)); wf_tac.
    + intros x. rewrite in_concat. intros [bl [Hinbl Hinx]].
      rewrite in_map_iff in Hinbl.
      destruct Hinbl as [t1 [Ht1 Hint1]]; subst.
      rewrite (in_map2_iff _ _ _ tm_d nil) in Hint1; wf_tac.
      destruct Hint1 as [i [Hi Ht1]]; subst.
      rewrite Forall_forall in H.
      apply H in Hinx; auto; wf_tac.
      rewrite (split_lens_concat l (map (fun t => length (bnd_t t)) tms));
        [|wf_tac]. rewrite in_concat. eexists. split; [| apply Hinx]. wf_tac.
  - (*Fquant*)
    destruct l; inversion H1; subst; simpl.
    inversion H0; subst.
    rewrite bnd_sub_f.
    split.
    + constructor; [intro C; apply H in C |apply H]; wf_tac.
    + intros. destruct H2; subst;[left | right]; auto.
      apply H in H2; wf_tac.
  - (*Feq*)
    split.
    + rewrite NoDup_app_iff'; split_all;[apply H | apply H0 |]; wf_tac.
      intros x [Hinx1 Hinx2].
      apply H in Hinx1; wf_tac; apply H0 in Hinx2; wf_tac.
      apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x Hinx.
      apply in_app_or in Hinx. destruct Hinx as [Hinx | Hinx]; 
      [apply H in Hinx | apply H0 in Hinx];wf_tac.
  - (*Fbinop*)
    split.
    + rewrite NoDup_app_iff'; split_all;[apply H|apply H0|]; wf_tac.
      intros x [Hinx1 Hinx2].
      apply H in Hinx1; wf_tac; apply H0 in Hinx2; wf_tac.
      apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x Hinx.
      apply in_app_or in Hinx; destruct Hinx as [Hinx | Hinx];
      [apply H in Hinx | apply H0 in Hinx];wf_tac.
  - (*trivial*)
    split;[constructor | intros x []].
  - split;[constructor | intros x []].
  - (*Flet*)
    destruct l; inversion H2; subst.
    inversion H1; subst; simpl; rewrite bnd_sub_f.
    split.
    + constructor.
      * intro C. apply in_app_or in C.
        destruct C as [Hins | Hins];
        [apply H in Hins | apply H0 in Hins]; wf_tac.
      * rewrite NoDup_app_iff'; split_all; [apply H | apply H0 |];wf_tac.
        intros x [Hinx1 Hinx2]; apply H in Hinx1; apply H0 in Hinx2; wf_tac.
        apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x [Hx | Hinx]; subst;[left | right]; auto.
      apply in_app_or in Hinx; destruct Hinx as [Hinx | Hinx];
      [apply H in Hinx | apply H0 in Hinx]; wf_tac.
  - (*Fif*)
    split.
    + rewrite !NoDup_app_iff'; split_all;
      [apply H | apply H0 | apply H1 | |]; wf_tac;
      intros x; [| rewrite in_app_iff];
      intros [Hinx1 Hinx2];[|destruct Hinx2 as [Hinx2 | Hinx2]];
      [apply H0 in Hinx1; apply H1 in Hinx2 | apply H in Hinx1; 
        apply H0 in Hinx2 | apply H in Hinx1; apply H1 in Hinx2]; wf_tac;
      apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x.
      rewrite ! in_app_iff; intros [Hinx | [Hinx | Hinx]];
      [apply H in Hinx | apply H0 in Hinx | apply H1 in Hinx]; wf_tac.
  - (*Fmatch case - very similar to Tmatch*)
    assert (Hsum: sum (map
      (fun x : pattern * formula =>
      Datatypes.length (pat_fv (fst x)) + Datatypes.length (bnd_f (snd x)))
      ps) = Datatypes.length (skipn (Datatypes.length (bnd_t tm)) l)). {
        wf_tac. rewrite H2,length_concat, 
      map_map, Nat.add_comm, Nat.add_sub. f_equal. apply map_ext_in_iff; intros.
      rewrite app_length; auto.
    }
    split.
    + rewrite NoDup_app_iff'; split_all.
      * apply H; wf_tac.
      * rewrite NoDup_concat_iff; split_all.
        -- intros x. rewrite in_map_iff.
          intros [pt1 [Hx Hinx]]; subst.
          rewrite (in_map2_iff _ _ _ (Pwild, Ftrue) nil) in Hinx; wf_tac.
          destruct Hinx as [i [Hi Hpt1]].
          rewrite NoDup_app_iff'.
          split_all; subst; wf_tac.
          ++ simpl. rewrite bnd_sub_fs.
            rewrite Forall_forall in H0.
            apply H0; auto; wf_tac.
          ++ intros x.
            simpl. rewrite bnd_sub_fs.
            intros [Hinx1 Hinx2].
            (*Need this a lot even though it's ugly*)
            apply in_map_pat_str_fv in Hinx1; wf_tac.
            rewrite Forall_forall in H0.
            apply H0 in Hinx2; wf_tac.
            apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
        -- intros i1 i2 d x. wf_tac.
          rewrite !map2_nth with(d1:=(Pwild, Ftrue)) (d2:=nil); wf_tac.
          intros [Hini1 Hini2].
          (*Now we get 4 cases need to show each is impossible*)
          destruct Hini1 as [Hini1 | Hini1].
          ++ apply in_map_pat_str_fv in Hini1; wf_tac.
            revert Hini1. wf_tac. intros Hini1.
            apply In_firstn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** apply in_map_pat_str_fv in Hini2; wf_tac.
              revert Hini2. wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** simpl in Hini2; rewrite bnd_sub_fs in Hini2. 
              rewrite Forall_forall in H0.
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
          ++ simpl in Hini1; rewrite bnd_sub_fs in Hini1. 
            rewrite Forall_forall in H0.
            apply H0 in Hini1; wf_tac.
            apply In_skipn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** apply in_map_pat_str_fv in Hini2; wf_tac.
              revert Hini2; wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** simpl in Hini2; rewrite bnd_sub_fs in Hini2. 
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
    * intros x.
      rewrite in_concat. intros [Hinx1 [l1 [Hinl1 Hinxl1]]].
      apply H in Hinx1; wf_tac.
      rewrite in_map_iff in Hinl1. destruct Hinl1 as [p1 [Hl1 Hinp1]].
      subst.
      rewrite in_map2_iff with(d1:=(Pwild, Ftrue))(d2:=nil) in Hinp1; wf_tac.
      destruct Hinp1 as [i [Hi Hp1]]; subst.
      (*And now we have to show these are distinct, will be similar*)
      apply in_app_or in Hinxl1.
      destruct Hinxl1 as [Hinx2 | Hinx2].
      -- apply in_map_pat_str_fv in Hinx2; wf_tac.
        revert Hinx2; wf_tac; intros.
        apply In_firstn in Hinx2.
        apply in_split_lens_ith in Hinx2; wf_tac.
        apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
      -- simpl in Hinx2; rewrite bnd_sub_fs in Hinx2. 
        rewrite Forall_forall in H0; apply H0 in Hinx2; wf_tac.
        apply In_skipn in Hinx2.
        apply in_split_lens_ith in Hinx2; wf_tac.
        apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
    + (*Second part - TODO very similar to previous*)
    intros x Hinx.
    apply in_app_or in Hinx.
    destruct Hinx as [Hinx | Hinx].
    * apply H in Hinx; wf_tac.
    * rewrite in_concat in Hinx.
      destruct Hinx as [l1 [Hinl1 Hinxl1]].
      rewrite in_map_iff in Hinl1.
      destruct Hinl1 as [p1 [Hl1 Hinp1]].
      subst.
      rewrite in_map2_iff with (d1:=(Pwild, Ftrue))(d2:=nil) in Hinp1; wf_tac.
      destruct Hinp1 as [i [Hi Hp1]]; subst.
      apply in_app_or in Hinxl1.
      destruct Hinxl1 as [Hinx | Hinx].
      -- apply in_map_pat_str_fv in Hinx; wf_tac.
        revert Hinx; wf_tac; intros.
        apply in_split_lens_ith in Hinx; wf_tac.
      -- simpl in Hinx; rewrite bnd_sub_fs in Hinx. 
        rewrite Forall_forall in H0; apply H0 in Hinx; wf_tac.
        apply In_skipn in Hinx.
        apply in_split_lens_ith in Hinx; wf_tac.
Qed.

Definition alpha_t_aux_bnd t := proj_tm alpha_aux_bnd t.
Definition alpha_f_aux_bnd f := proj_fmla alpha_aux_bnd f.

Ltac prove_hyp H :=
  match goal with
  | H: ?P -> ?Q |- _ => let N := fresh in assert (N: P); [|specialize (H N); clear N]
  end.

Ltac prove_hyps n H :=
  match constr:(n) with
  | O => idtac
  | (S ?m) => prove_hyp H; [|prove_hyps m H]
  end.

Ltac vsym_eq2 x y z :=
  let H := fresh in
  assert (H: x = y \/ (x <> y /\ x = z) \/ (x <> y /\ x <> z)) by
  (vsym_eq x y; right; vsym_eq x z);
  destruct H as [? | [[? ?]|[? ?]]].

(*2: The free variables after conversion are equal.
  NOTE: in general, it is true that the free variables of
  any alpha-equivalent terms are equal, but this is hard to
  show, and we don't need the general version at the moment.
  (proved part of it in alt approach)*)
Lemma alpha_aux_fv (t: term) (f: formula) :
  (forall (l: list string)
    (Hnodupl: NoDup l)
    (Hlen: length l = length (bnd_t t))
    (Hfree: forall x, In (fst x) l -> ~ In x (term_fv t))
    (Hbnd: forall x, In (fst x) l -> ~ In x (bnd_t t)),
    forall x,
    free_in_t x (alpha_t_aux t l) = free_in_t x t) /\
  (forall (l: list string)  
    (Hnodupl: NoDup l)
    (Hlen: length l = length (bnd_f f))
    (Hfree: forall x, In (fst x) l -> ~ In x (form_fv f))
    (Hbnd: forall x, In (fst x) l -> ~ In x (bnd_f f)),
    forall x,
    free_in_f x (alpha_f_aux f l) = free_in_f x f).
Proof.
  revert t f. apply term_formula_ind; simpl; auto; intros; try reflexivity.
  - apply existsb_eq; wf_tac.
    revert H. rewrite !Forall_forall; intros.
    revert H0. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d).
    subst; simpl. rewrite map2_nth with(d1:=tm_d)(d2:=nil); wf_tac.
    apply H; wf_tac; intros y Hiny C; apply in_split_lens_ith in Hiny; wf_tac.
    + apply (Hfree y); simpl_set; auto.
      exists (nth i l1 tm_d). split; wf_tac.
    + apply (Hbnd y); auto. rewrite in_concat.
      exists (bnd_t (nth i l1 tm_d)). split; wf_tac.
  - (*Let - this case is complicated because we are binding variables*) 
    destruct l; inversion Hlen.
    simpl. inversion Hnodupl; subst.
    rewrite H; wf_tac; try(intros y Hiny C); [|apply (Hfree y) | apply (Hbnd y)];
    try(simpl; right; wf_tac); [|simpl_set; triv].
    f_equal.
    assert (v <> (s, snd v)). {
      intro C; subst. apply (Hbnd v); try triv. 
      left; rewrite C; auto.
    }
    specialize (H0 (skipn (Datatypes.length (bnd_t tm1)) l)).
    prove_hyps 4 H0; wf_tac;
    try(intros y Hiny C); [apply (Hfree y) | apply (Hbnd y)|];
    try solve[simpl; right; wf_tac];
    [simpl_set; right; split; auto; intro Heq; subst;
      apply (Hbnd v); [right; wf_tac | left; auto]
    | ].
    (*Now we proceed by cases depending on whether x = v,
      x = (s, snd v), or none of the above*)
    vsym_eq2 x v (s, snd v).
    + subst. rewrite sub_t_fv_notin; auto. simpl_bool.
      vsym_eq v v.
    + (*If x = (s, snd v)*)
      subst. vsym_eq (s, snd v) (s, snd v).
      rewrite sub_t_fv_in; auto.
      * rewrite !H0.
        vsym_eq (s, snd v) v. simpl.
        (*TODO: change Hfree to use [free_in_t]?*)
        symmetry. apply free_in_t_negb. intro Hin.
        apply (Hfree (s, snd v)). left; auto. 
        simpl_set. triv.
      * intro Hin. apply alpha_t_aux_bnd in Hin; wf_tac.
    + (*The last case is quite easy, nothing changes*) 
      rewrite sub_t_fv_diff; auto.
      vsym_eq x (s, snd v); simpl.
      vsym_eq x v; simpl.
      apply H0.
  - (*If case - hypotheses for IH's are annoying *)
    rewrite H, H0, H1; wf_tac; intros y Hiny C;
    [apply (Hfree y) | apply (Hbnd y) | apply (Hfree y) | apply (Hbnd y) |
    apply (Hfree y) | apply (Hbnd y)];
    try(apply (Hfree y)); try(apply (Hbnd y));
    try (apply In_skipn in Hiny); try (apply In_firstn in Hiny);
    wf_tac; simpl_set; try (rewrite !in_app_iff); triv.
  - (*Match case - let's see*)
    specialize (H (firstn (Datatypes.length (bnd_t tm)) l)).
    prove_hyps 4 H; wf_tac; try(intros y Hiny C);
    [apply (Hfree y) | apply (Hbnd y) |]; wf_tac;
    [simpl_set; triv | ].
    rewrite H. f_equal.
    apply existsb_eq; wf_tac.
    revert H0. rewrite !Forall_forall; intros.
    revert H1. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx (Pwild, tm_d) (Pwild, tm_d)).
    subst; simpl.
    rewrite map2_nth with(d1:=(Pwild, tm_d))(d2:=nil); wf_tac.
    assert (Hsum: sum
    (map
       (fun x0 : pattern * term =>
        Datatypes.length (pat_fv (fst x0)) + Datatypes.length (bnd_t (snd x0)))
       ps) = Datatypes.length l - Datatypes.length (bnd_t tm)). {
      rewrite Hlen, length_concat, map_map, Nat.add_comm, Nat.add_sub.
      f_equal. apply map_ext_in_iff; intros.
        rewrite app_length; auto.
    }
    match goal with
    | |- context [in_bool ?e ?x ?l] => destruct (in_bool_spec e x l)
    end; simpl.
    + (*If x is in the pattern free vars, then it is in l*)
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst (nth i ps (Pwild, tm_d))))); simpl; auto.
      symmetry. apply free_in_t_negb. intro Hinfree.
      simpl in i0.
      apply in_map_pat_str_fv in i0; wf_tac.
      apply In_firstn in i0.
      apply in_split_lens_ith in i0; wf_tac.
      apply (Hfree x); wf_tac. simpl_set.
      right. exists (nth i ps (Pwild, tm_d)).
      split; wf_tac.
      simpl_set. split; auto.
    + (*Otherwise, x not in pattern free vars*)
      (*Need this result in 2 places*)
      assert (Hnotfree: forall x0 : string * vty,
      In (fst x0)
           (nth i
              (split_lens (skipn (Datatypes.length (bnd_t tm)) l)
                 (map
                    (fun x1 : pattern * term =>
                     Datatypes.length (pat_fv (fst x1)) +
                     Datatypes.length (bnd_t (snd x1))) ps)) []) ->
      ~ (In x0 (term_fv (snd (nth i ps (Pwild, tm_d)))) \/
        In x0 (pat_fv (fst (nth i ps (Pwild, tm_d)))))). {
        intros y Hy C.
        apply in_split_lens_ith in Hy; wf_tac.
        (*Do [pat_fv] first*)
        assert (~In y (pat_fv (fst (nth i ps (Pwild, tm_d))))). {
          (*Contradiction: y in l, so not bound in pattern,
            which is same as pattern free var*)
          intro Hnot.
          apply (Hbnd y); wf_tac. right.
          rewrite in_concat. exists (pat_fv (fst (nth i ps (Pwild, tm_d))) ++
            bnd_t (snd (nth i ps (Pwild, tm_d)))). split; wf_tac.
          exists (nth i ps (Pwild, tm_d)); split; wf_tac.
        }
        destruct C; try contradiction.
        (*Here, contradicts [Hfree], need [pat_fv result]*)
        apply (Hfree y); simpl_set; wf_tac.
        right. exists (nth i ps (Pwild, tm_d)). split;
        auto; simpl_set; wf_tac. 
      }
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst (nth i ps (Pwild, tm_d))))); simpl.
      * apply sub_ts_fv_notin; wf_tac.
        intros y Hiny Hiny2.
        apply In_firstn in Hiny2. apply Hnotfree in Hiny2.
        not_or Hiny. contradiction.
      * simpl in n.
        rewrite sub_ts_fv_diff; wf_tac. 
        -- rewrite H0; wf_tac.
          ++ intros y Hy C.
            apply In_skipn in Hy.
            apply Hnotfree in Hy. apply Hy; triv.
          ++ intros y Hy C.
            apply In_skipn in Hy.
            apply in_split_lens_ith in Hy; wf_tac.
            apply (Hbnd y); wf_tac. right.
            rewrite in_concat. exists (pat_fv (fst (nth i ps (Pwild, tm_d))) ++
              bnd_t (snd (nth i ps (Pwild, tm_d)))). split; wf_tac.
            exists (nth i ps (Pwild, tm_d)); split; wf_tac.
        -- intro C.
          apply n. simpl.
          apply in_map_pat_str_fv_iff; wf_tac.
  - (*Teps - basically same as let*) 
    destruct l; inversion Hlen. simpl.
    assert (v <> (s, snd v)). {
      intro C; subst. apply (Hbnd v); try triv. 
      left; rewrite C; auto.
    }
    inversion Hnodupl; subst.
    specialize (H l).
    prove_hyps 4 H; wf_tac;
    try(intros y Hiny C); [apply (Hfree y) | apply (Hbnd y)|];
    try solve[simpl; right; wf_tac];
    simpl_set; auto.
    split; auto; intro Heq; subst.
    apply (Hbnd v); [right; wf_tac | left; auto].
    (*Now we proceed by cases depending on whether x = v,
      x = (s, snd v), or none of the above*)
    vsym_eq2 x v (s, snd v).
    + subst. rewrite sub_f_fv_notin; auto. simpl_bool.
      vsym_eq v v.
    + (*If x = (s, snd v)*)
      subst. vsym_eq (s, snd v) (s, snd v).
      rewrite sub_f_fv_in; auto.
      * rewrite !H.
        vsym_eq (s, snd v) v. simpl.
        symmetry. apply free_in_f_negb. intro Hin.
        apply (Hfree (s, snd v)). left; auto. 
        simpl_set. triv.
      * intro Hin. apply alpha_f_aux_bnd in Hin; wf_tac.
    + (*The last case is quite easy, nothing changes*) 
      rewrite sub_f_fv_diff; auto.
      vsym_eq x (s, snd v); simpl.
      vsym_eq x v; simpl.
      apply H.
  - (*Fpred*)
    apply existsb_eq; wf_tac.
    revert H. rewrite !Forall_forall; intros.
    revert H0. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d).
    subst; simpl. rewrite map2_nth with(d1:=tm_d)(d2:=nil); wf_tac.
    apply H; wf_tac; intros y Hiny C; apply in_split_lens_ith in Hiny; wf_tac.
    + apply (Hfree y); simpl_set; auto.
      exists (nth i tms tm_d). split; wf_tac.
    + apply (Hbnd y); auto. rewrite in_concat.
      exists (bnd_t (nth i tms tm_d)). split; wf_tac.
  - (*Fquant -similar to let/eps*)
    destruct l; inversion Hlen.
    inversion Hnodupl;subst.
    simpl.
    assert (v <> (s, snd v)). {
      intro C; subst. apply (Hbnd v); try triv. 
      left; rewrite C; auto.
    }
    specialize (H l).
    prove_hyps 4 H; wf_tac;
    try(intros y Hiny C); [apply (Hfree y) | apply (Hbnd y)|];
    try solve[simpl; right; wf_tac];
    simpl_set; auto.
    split; auto; intro Heq; subst.
    apply (Hbnd v); [right; wf_tac | left; auto].
    (*Now we proceed by cases depending on whether x = v,
      x = (s, snd v), or none of the above*)
    vsym_eq2 x v (s, snd v).
    + subst. rewrite sub_f_fv_notin; auto. simpl_bool.
      vsym_eq v v.
    + (*If x = (s, snd v)*)
      subst. vsym_eq (s, snd v) (s, snd v).
      rewrite sub_f_fv_in; auto.
      * rewrite !H.
        vsym_eq (s, snd v) v. simpl.
        (*TODO: change Hfree to use [free_in_t]?*)
        symmetry. apply free_in_f_negb. intro Hin.
        apply (Hfree (s, snd v)). left; auto. 
        simpl_set. triv.
      * intro Hin. apply alpha_f_aux_bnd in Hin; wf_tac.
    + (*The last case is quite easy, nothing changes*) 
      rewrite sub_f_fv_diff; auto.
      vsym_eq x (s, snd v); simpl.
      vsym_eq x v; simpl.
      apply H.
  - (*Feq*)
    rewrite H, H0; wf_tac; intros y Hiny C;
    try solve[(apply (Hfree y); wf_tac; simpl_set; triv)];
    apply (Hbnd y); wf_tac.
  - (*Fbinop*)
    rewrite H, H0; wf_tac; intros y Hiny C;
    try solve[(apply (Hfree y); wf_tac; simpl_set; triv)];
    apply (Hbnd y); wf_tac.
  - (*Flet*)
    destruct l; inversion Hlen.
    simpl. inversion Hnodupl; subst.
    rewrite H; wf_tac; try(intros y Hiny C); [|apply (Hfree y) | apply (Hbnd y)];
    try(simpl; right; wf_tac); [|simpl_set; triv].
    f_equal.
    assert (v <> (s, snd v)). {
      intro C; subst. apply (Hbnd v); try triv. 
      left; rewrite C; auto.
    }
    specialize (H0 (skipn (Datatypes.length (bnd_t tm)) l)).
    prove_hyps 4 H0; wf_tac;
    try(intros y Hiny C); [apply (Hfree y) | apply (Hbnd y)|];
    try solve[simpl; right; wf_tac];
    [simpl_set; right; split; auto; intro Heq; subst;
      apply (Hbnd v); [right; wf_tac | left; auto]
    | ].
    (*Now we proceed by cases depending on whether x = v,
      x = (s, snd v), or none of the above*)
    vsym_eq2 x v (s, snd v).
    + subst. rewrite sub_f_fv_notin; auto. simpl_bool.
      vsym_eq v v.
    + (*If x = (s, snd v)*)
      subst. vsym_eq (s, snd v) (s, snd v).
      rewrite sub_f_fv_in; auto.
      * rewrite !H0.
        vsym_eq (s, snd v) v. simpl.
        symmetry. apply free_in_f_negb. intro Hin.
        apply (Hfree (s, snd v)). left; auto. 
        simpl_set. triv.
      * intro Hin. apply alpha_f_aux_bnd in Hin; wf_tac.
    + (*The last case is quite easy, nothing changes*) 
      rewrite sub_f_fv_diff; auto.
      vsym_eq x (s, snd v); simpl.
      vsym_eq x v; simpl.
      apply H0.
  - (*Fif*)
    rewrite H, H0, H1; wf_tac; intros y Hiny C;
    [apply (Hfree y) | apply (Hbnd y) | apply (Hfree y) | apply (Hbnd y) |
    apply (Hfree y) | apply (Hbnd y)];
    try(apply (Hfree y)); try(apply (Hbnd y));
    try (apply In_skipn in Hiny); try (apply In_firstn in Hiny);
    wf_tac; simpl_set; triv.
  - (*Fmatch - copied and pasted*)
    specialize (H (firstn (Datatypes.length (bnd_t tm)) l)).
    prove_hyps 4 H; wf_tac; try(intros y Hiny C);
    [apply (Hfree y) | apply (Hbnd y) |]; wf_tac;
    [simpl_set; triv | ].
    rewrite H. f_equal.
    apply existsb_eq; wf_tac.
    revert H0. rewrite !Forall_forall; intros.
    revert H1. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx (Pwild, Ftrue) (Pwild, Ftrue)).
    subst; simpl.
    rewrite map2_nth with(d1:=(Pwild, Ftrue))(d2:=nil); wf_tac.
    assert (Hsum: sum
    (map
      (fun x0 : pattern * formula =>
        Datatypes.length (pat_fv (fst x0)) + Datatypes.length (bnd_f (snd x0)))
      ps) = Datatypes.length l - Datatypes.length (bnd_t tm)). {
      rewrite Hlen, length_concat, map_map, Nat.add_comm, Nat.add_sub.
      f_equal. apply map_ext_in_iff; intros.
        rewrite app_length; auto.
    }
    match goal with
    | |- context [in_bool ?e ?x ?l] => destruct (in_bool_spec e x l)
    end; simpl.
    + (*If x is in the pattern free vars, then it is in l*)
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst (nth i ps (Pwild, Ftrue))))); simpl; auto.
      symmetry. apply free_in_f_negb. intro Hinfree.
      simpl in i0.
      apply in_map_pat_str_fv in i0; wf_tac.
      apply In_firstn in i0.
      apply in_split_lens_ith in i0; wf_tac.
      apply (Hfree x); wf_tac. simpl_set.
      right. exists (nth i ps (Pwild, Ftrue)).
      split; wf_tac.
      simpl_set. split; auto.
    + (*Otherwise, x not in pattern free vars*)
      (*Need this result in 2 places*)
      assert (Hnotfree: forall x0 : string * vty,
      In (fst x0)
          (nth i
              (split_lens (skipn (Datatypes.length (bnd_t tm)) l)
                (map
                    (fun x1 : pattern * formula =>
                    Datatypes.length (pat_fv (fst x1)) +
                    Datatypes.length (bnd_f (snd x1))) ps)) []) ->
      ~ (In x0 (form_fv (snd (nth i ps (Pwild, Ftrue)))) \/
        In x0 (pat_fv (fst (nth i ps (Pwild, Ftrue)))))). {
        intros y Hy C.
        apply in_split_lens_ith in Hy; wf_tac.
        (*Do [pat_fv] first*)
        assert (~In y (pat_fv (fst (nth i ps (Pwild, Ftrue))))). {
          (*Contradiction: y in l, so not bound in pattern,
            which is same as pattern free var*)
          intro Hnot.
          apply (Hbnd y); wf_tac. right.
          rewrite in_concat. exists (pat_fv (fst (nth i ps (Pwild, Ftrue))) ++
            bnd_f (snd (nth i ps (Pwild, Ftrue)))). split; wf_tac.
          exists (nth i ps (Pwild, Ftrue)); split; wf_tac.
        }
        destruct C; try contradiction.
        (*Here, contradicts [Hfree], need [pat_fv result]*)
        apply (Hfree y); simpl_set; wf_tac.
        right. exists (nth i ps (Pwild, Ftrue)). split;
        auto; simpl_set; wf_tac. 
      }
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst (nth i ps (Pwild, Ftrue))))); simpl.
      * (*If x in orig pattern free vars, need to show false*)
        apply sub_fs_fv_notin; wf_tac.
        intros y Hiny Hiny2.
        apply In_firstn in Hiny2. apply Hnotfree in Hiny2.
        not_or Hiny. contradiction.
      * simpl in n.
        rewrite sub_fs_fv_diff; wf_tac. 
        -- rewrite H0; wf_tac.
          ++ intros y Hy C.
            apply In_skipn in Hy.
            apply Hnotfree in Hy. apply Hy; triv.
          ++ intros y Hy C.
            apply In_skipn in Hy.
            apply in_split_lens_ith in Hy; wf_tac.
            apply (Hbnd y); wf_tac. right.
            rewrite in_concat. exists (pat_fv (fst (nth i ps (Pwild, Ftrue))) ++
              bnd_f (snd (nth i ps (Pwild, Ftrue)))). split; wf_tac.
            exists (nth i ps (Pwild, Ftrue)); split; wf_tac.
        -- intro C.
          apply n. simpl.
          apply in_map_pat_str_fv_iff; wf_tac.
Qed.

Definition alpha_t_aux_fv t := proj_tm alpha_aux_fv t.
Definition alpha_f_aux_fv f := proj_fmla alpha_aux_fv f. 

Corollary alpha_t_aux_fv' (t: term):
  (forall (l: list string)
  (Hnodupl: NoDup l)
  (Hlen: length l = length (bnd_t t))
  (Hfree: forall x, In (fst x) l -> ~ In x (term_fv t))
  (Hbnd: forall x, In (fst x) l -> ~ In x (bnd_t t)),
  forall x, In x (term_fv (alpha_t_aux t l)) <-> In x (term_fv t)).
Proof.
  intros. rewrite <- !free_in_t_spec, alpha_t_aux_fv; auto.
  reflexivity.
Qed. 

Corollary alpha_f_aux_fv' (f: formula):
  (forall (l: list string)
  (Hnodupl: NoDup l)
  (Hlen: length l = length (bnd_f f))
  (Hfree: forall x, In (fst x) l -> ~ In x (form_fv f))
  (Hbnd: forall x, In (fst x) l -> ~ In x (bnd_f f)),
  forall x, In x (form_fv (alpha_f_aux f l)) <-> In x (form_fv f)).
Proof.
  intros. rewrite <- !free_in_f_spec, alpha_f_aux_fv; auto.
  reflexivity.
Qed. 

(*TODO: move earlier*)


(*TODO: move*)
Lemma mk_fun_in_firstb_iff (l1 l2: list vsymbol) x y
  (Hlen: length l1 = length l2)
  (Hn2: NoDup l2)
  (Hin: In x l1):
  var_in_firstb (x, y) (combine l1 l2) <-> mk_fun l1 l2 x = y.
Proof.
  generalize dependent l2. induction l1; simpl; intros. inversion Hin.
  destruct l2; inversion Hlen; simpl.
  vsym_eq x a; simpl.
  - vsym_eq y v; simpl; split; intros; auto. inversion H.
  - inversion Hn2; subst. destruct Hin; subst; try contradiction.
    vsym_eq y v; simpl.
    + split; intros; auto. inversion H1.
      exfalso. apply H2. rewrite <- H1. apply mk_fun_in; auto; lia.
    + apply IHl1; auto.
Qed.

(*Only need injectivity on the elts*)
Lemma NoDup_map_inj {A B: Type} (f: A -> B) (l: list A)
  (Hinj: forall x y, In x l -> In y l -> f x = f y -> x = y):
  NoDup l ->
  NoDup (map f l).
Proof.
  induction l; simpl; intros; inversion H; constructor; subst.
  - intro C.
    rewrite in_map_iff in C.
    destruct C as [y [Hy Hiny]].
    assert (a = y) by (apply Hinj; simpl; auto).
    subst. contradiction.
  - apply IHl; auto. intros; apply Hinj; simpl; auto.
Qed. 

(*mapping [mk_fun_str] over a pattern results in an
  alpha-equivalent pattern under the valuation mapping
  their free variables*)
Lemma map_pat_str_alpha p strs
  (Hlen: length strs = length (pat_fv p))
  (Hn: NoDup strs):
  alpha_equiv_p
    (combine (pat_fv p) (map (mk_fun_str (pat_fv p) strs) (pat_fv p))) p
    (map_pat (mk_fun_str (pat_fv p) strs) p).
Proof.
  assert (Hlen2: Datatypes.length (pat_fv p) =
    Datatypes.length (combine strs (map snd (pat_fv p)))) by
    (unfold vsymbol; rewrite combine_length, map_length,
    Hlen, Nat.min_id; auto).
  apply map_pat_alpha_equiv.
  - intros. unfold mk_fun_str.
    pose proof (In_nth _ _ vs_d H).
    destruct H0 as [i [Hi Hx]]; subst.
    rewrite mk_fun_nth with(d2:=vs_d); wf_tac.
    unfold vs_d, vsymbol. rewrite combine_nth; wf_tac.
    rewrite map_nth_inbound with(d2:=vs_d); auto.
  - intros. apply mk_fun_in_firstb_iff; wf_tac.
    + apply NoDup_map_inj; [|apply NoDup_pat_fv].
      unfold mk_fun_str.
      apply mk_fun_inj; wf_tac. 2: rewrite Hlen2; auto.
      apply NoDup_combine_l; auto.
    + unfold mk_fun_str.
      rewrite map_mk_fun; wf_tac.
Qed.

(*Alpha equivalence with iterated substitution*)

(*TODO: combine with other section?*)
Section AlphaSubIter.

Context {A: Type}.
Variable bnd : A -> list vsymbol.
Variable fv: A -> list vsymbol.
Variable free_in: vsymbol -> A -> bool.
Variable sub : vsymbol -> vsymbol -> A -> A.
Notation subs := (sub_mult sub).
Variable alpha: list (vsymbol * vsymbol) -> A -> A -> bool.
Variable same: A -> A -> vsymbol -> bool.

Variable alpha_refl: forall t, alpha nil t t.
Variable alpha_sub_full: forall (t tm2 : A) (x y : vsymbol)
  (v1 v2 : list (vsymbol * vsymbol)),
  snd x = snd y ->
  ~ In y (bnd tm2) ->
  ~ In y (fv tm2) ->
  same t tm2 x ->
  ~ In x (map fst v1) ->
  ~ In y (map snd v1) ->
  alpha (v1 ++ v2) t tm2 ->
  alpha (v1 ++ (x, y) :: v2) t (sub x y tm2).
Variable bnd_subs: forall vars t,
  bnd (subs vars t) = bnd t.
Variable free_in_negb: forall t x,
  free_in x t = false <-> ~ In x (fv t).
Variable subs_fv_diff: forall vars t x,
  ~ In x (map fst vars) ->
  ~ In x (combine (map snd vars) (map snd (map fst vars))) ->
  free_in x (subs vars t) = free_in x t.
Variable same_in_subs: forall t vs z,
  ~ In z (map fst vs) ->
  ~ In (fst z) (map snd vs) ->
  same t (subs vs t) z.


Lemma alpha_equiv_subs (t: A) (vs: list vsymbol) (strs: list string)
  (Hlen: length strs = length vs)
  (Hnotbnd: forall s, In (fst s) strs -> ~ In s (bnd t))
  (Hnotfree: forall s, In (fst s) strs -> ~ In s (fv t))
  (Hnodup: NoDup strs)
  (Hn1: NoDup vs)
  (Hnew: forall x, In x vs -> ~ In (fst x) strs):
  alpha (add_vals vs (combine strs (map snd vs)) nil) t
    (subs (combine vs strs) t).
Proof.
  unfold add_vals.
  generalize dependent strs. induction vs; simpl; intros;
  destruct strs; inversion Hlen.
  - apply alpha_refl.
  - simpl. inversion Hn1; subst.
    inversion Hnodup; subst.
    apply (alpha_sub_full _ _ a (s, snd a) nil _); auto.
    + rewrite bnd_subs. intro C.
      apply (Hnotbnd (s, snd a)); simpl; auto.
    + rewrite <- free_in_negb.
      rewrite subs_fv_diff.
      * rewrite free_in_negb. apply Hnotfree. simpl; auto.
      * rewrite map_fst_combine; auto.
        intro C.
        apply (Hnew (s, snd a)); simpl; auto.
      * rewrite map_fst_combine, map_snd_combine; auto.
        intro C.
        apply in_combine_l in C. contradiction.
    + apply same_in_subs.
      * rewrite map_fst_combine; auto.
      * rewrite map_snd_combine; auto.
        specialize (Hnew a).
        intro C.
        apply Hnew; simpl; auto.
    + simpl. apply IHvs; auto.
      * intros. intro C. apply (Hnotbnd s0); simpl; auto.
      * intros. intro C. apply (Hnotfree s0); simpl; auto.
      * intros x Hinx1 Hinx2. apply (Hnew x); simpl; auto.
Qed.

End AlphaSubIter.

Definition alpha_equiv_sub_ts :=
  alpha_equiv_subs _ _ _ _ _ _ a_equiv_t_refl alpha_equiv_sub_t_full
  bnd_sub_ts free_in_t_negb sub_ts_fv_diff same_in_sub_ts.
Definition alpha_equiv_sub_fs :=
  alpha_equiv_subs _ _ _ _ _ _ a_equiv_f_refl alpha_equiv_sub_f_full
  bnd_sub_fs free_in_f_negb sub_fs_fv_diff same_in_sub_fs.

(*Before our final result, we handle the match cases separately
  using a sort-of-congruence lemma. These proofs are
  tricky and the tmatch and fmatch cases are very similar.
  They should be combined if possible*)

Lemma alpha_tmatch tm1 tm2 v ps (strs: list (list string))
  (f: term -> list string -> term)
  (Heq1: a_equiv_t tm1 tm2)
  (Hlen1: length strs = length ps)
  (Hlen2: forall i, i < length ps ->
    length (pat_fv (fst (nth i ps (Pwild, tm_d)))) +
    length (bnd_t (snd (nth i ps (Pwild, tm_d)))) = 
    length (nth i strs nil))
  (Hf: forall i, i < length ps ->
    let x := nth i ps (Pwild, tm_d) in
    a_equiv_t (snd x) 
      (f (snd x) (skipn (length (pat_fv (fst x))) (nth i strs nil))))
  (Hfbnd: forall i, i < length ps ->
    let x := nth i ps (Pwild, tm_d) in
    let l' := (skipn (length (pat_fv (fst x))) (nth i strs nil)) in
    forall y, In y (bnd_t (f (snd x) l')) -> In (fst y) l'
  )
  (Hffree: forall i, i < length ps ->
    let x := nth i ps (Pwild, tm_d) in
    let l' := (skipn (length (pat_fv (fst x))) (nth i strs nil)) in
    forall y, free_in_t y (f (snd x) l') = free_in_t y (snd x))
  (Hnotfree: forall v l, In l strs -> In (fst v) l ->
    ~ In v (big_union vsymbol_eq_dec term_fv (map snd ps)))
  (Hnotbnd: forall v l, In l strs -> In (fst v) l ->
    ~ In v (concat
    (map (fun p : pattern * term => pat_fv (fst p) ++ bnd_t (snd p))
       ps)))
  (Hnodup: NoDup (concat strs)):
  a_equiv_t (Tmatch tm1 v ps)
    (Tmatch tm2 v
     (map2
        (fun (x : pattern * term) (strs : list string) =>
         (map_pat
            (mk_fun_str (pat_fv (fst x))
               (firstn (length (pat_fv (fst x))) strs)) 
            (fst x),
          sub_ts
            (combine (pat_fv (fst x))
               (firstn (length (pat_fv (fst x))) strs))
            (f (snd x)
               (skipn (length (pat_fv (fst x))) strs)))) ps strs)).
Proof.
  unfold a_equiv_t in *.
  simpl.
  rewrite Heq1, map2_length, Hlen1, Nat.min_id, Nat.eqb_refl; simpl.
  destruct (vty_eq_dec v v); auto; simpl. clear e.
  generalize dependent strs. clear Heq1.
  induction ps; simpl; intros; auto.
  destruct strs; inversion Hlen1.
  destruct a as [p1 t1].
  rewrite all2_cons.
  simpl.
  rewrite NoDup_concat_iff in Hnodup. destruct Hnodup as [Hn1 Hn2].
  assert (Hlenl: Datatypes.length (firstn (Datatypes.length (pat_fv p1)) l) =
    Datatypes.length (pat_fv p1)) by
    (wf_tac; specialize (Hlen2 0 ltac:(lia)); simpl in Hlen2; lia).
  assert (Hnl: NoDup l) by (apply Hn1; simpl; auto).
  rewrite map_pat_str_fv; wf_tac.
  rewrite map_pat_str_alpha; wf_tac; simpl.
  unfold mk_fun_str at 1.
  rewrite map_mk_fun; wf_tac.
  2: {
    unfold vsymbol in *;
    rewrite combine_length, Hlenl, map_length. lia.
  }
  bool_to_prop; split.
  - (*We need transitivity, which is annoying because we have to go forward*) 
    pose proof (alpha_equiv_sub_ts t1 (pat_fv p1) 
      (firstn (Datatypes.length (pat_fv p1)) l) Hlenl).
    assert (forall s : string * vty,
    In (fst s) (firstn (Datatypes.length (pat_fv p1)) l) ->
    ~ In s (bnd_t t1)). {
      intros v' Hinvl Hinvb.
      apply (Hnotbnd v' l); simpl; wf_tac. 
    }
    specialize (H H1); clear H1.
    assert (forall s : string * vty,
    In (fst s) (firstn (Datatypes.length (pat_fv p1)) l) ->
    ~ In s (term_fv t1)). {
      intros v' Hinl Hinvf.
      apply (Hnotfree v' l); simpl; simpl_set; wf_tac.
    }
    specialize (H H1 ltac:(wf_tac) (NoDup_pat_fv _)); clear H1.
    assert (forall x : vsymbol,
    In x (pat_fv p1) ->
    ~ In (fst x) (firstn (Datatypes.length (pat_fv p1)) l)). {
      intros v' Hinvb Hinvl.
      apply (Hnotbnd v' l); simpl; wf_tac.
    }
    specialize (H H1); clear H1.
    specialize (Hf 0 ltac:(lia)); simpl in Hf.
    assert (Heq2: a_equiv_t
    (sub_ts (combine (pat_fv p1) (firstn (Datatypes.length (pat_fv p1)) l)) t1)
    (sub_ts (combine (pat_fv p1) (firstn (Datatypes.length (pat_fv p1)) l))
       (f t1 (skipn (Datatypes.length (pat_fv p1)) l)))). {
        apply a_equiv_t_sub_ts_congr; auto.
        - intros x. rewrite map_snd_combine; auto.
          intros. intro C.
          apply (Hnotbnd x l); simpl; wf_tac.
        - intros x. rewrite map_snd_combine; auto.
          intros. intro C.
          specialize (Hfbnd 0 ltac:(lia)); simpl in Hfbnd.
          apply Hfbnd in C.
          apply (nodup_firstn_skipn H1 C). auto.
        - intros x. rewrite map_snd_combine; auto.
          intros. intro C.
          apply (Hnotfree x l); simpl; simpl_set; wf_tac.
        - intros x. rewrite map_snd_combine; auto.
          intros. intro C.
          apply free_in_t_spec in C.
          specialize (Hffree 0 ltac:(lia)); simpl in Hffree.
          rewrite Hffree in C.
          apply free_in_t_spec in C.
          apply (Hnotfree x l); simpl; wf_tac; simpl_set; auto. 
        - rewrite map_snd_combine; wf_tac.
       }
    revert H; unfold add_vals; rewrite !app_nil_r; intros.
    pose proof (a_equiv_t_expand_combine (combine 
      (firstn (Datatypes.length (pat_fv p1)) l) (map snd (pat_fv p1))) 
      _ _ Heq2) as Heq3.
    assert (Hmap: map snd
      (combine (pat_fv p1)
        (combine (firstn (Datatypes.length (pat_fv p1)) l) (map snd (pat_fv p1)))) =
    map fst
      (combine (combine (firstn (Datatypes.length (pat_fv p1)) l) (map snd (pat_fv p1)))
        (combine (firstn (Datatypes.length (pat_fv p1)) l) (map snd (pat_fv p1))))). {
      rewrite map_snd_combine; auto.
      rewrite map_fst_combine; auto.
      rewrite combine_length, Hlenl, map_length, Nat.min_id; auto. 
    }
    (*Now we can use transitivity*)
    pose proof (alpha_equiv_t_trans _ _ _ _ _ Hmap H Heq3).
    rewrite combine_alist_trans in H1; auto.
    unfold vsymbol in *.
    rewrite combine_length, map_length, Hlenl. lia.
  - (*Inductive case*) 
    apply IHps; auto.
    + intros. apply (Hlen2 (S i) ltac:(lia)). 
    + intros. apply (Hf (S i) ltac:(lia)). 
    + intros. apply (Hfbnd (S i) (ltac:(lia))); auto.
    + intros. apply (Hffree (S i) (ltac:(lia))).
    + intros. intro Hin.
      apply (Hnotfree v0 l0); simpl; auto; simpl_set; auto.
    + intros. intro Hin.
      apply (Hnotbnd v0 l0); simpl; auto; rewrite !in_app_iff; auto.
    + rewrite NoDup_concat_iff. split_all; auto.
      * intros; apply Hn1; simpl; auto.
      * intros. simpl in Hn2. 
        apply (Hn2 (S i1) (S i2) d x ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

(*TODO: bad to duplicate, should combine somehow*)
Lemma alpha_fmatch tm1 tm2 v ps (strs: list (list string))
  (f: formula -> list string -> formula)
  (Heq1: a_equiv_t tm1 tm2)
  (Hlen1: length strs = length ps)
  (Hlen2: forall i, i < length ps ->
    length (pat_fv (fst (nth i ps (Pwild, Ftrue)))) +
    length (bnd_f (snd (nth i ps (Pwild, Ftrue)))) = 
    length (nth i strs nil))
  (Hf: forall i, i < length ps ->
    let x := nth i ps (Pwild, Ftrue) in
    a_equiv_f (snd x) 
      (f (snd x) (skipn (length (pat_fv (fst x))) (nth i strs nil))))
  (Hfbnd: forall i, i < length ps ->
    let x := nth i ps (Pwild, Ftrue) in
    let l' := (skipn (length (pat_fv (fst x))) (nth i strs nil)) in
    forall y, In y (bnd_f (f (snd x) l')) -> In (fst y) l'
  )
  (Hffree: forall i, i < length ps ->
    let x := nth i ps (Pwild, Ftrue) in
    let l' := (skipn (length (pat_fv (fst x))) (nth i strs nil)) in
    forall y, free_in_f y (f (snd x) l') = free_in_f y (snd x))
  (Hnotfree: forall v l, In l strs -> In (fst v) l ->
    ~ In v (big_union vsymbol_eq_dec form_fv (map snd ps)))
  (Hnotbnd: forall v l, In l strs -> In (fst v) l ->
    ~ In v (concat
    (map (fun p : pattern * formula => pat_fv (fst p) ++ bnd_f (snd p))
       ps)))
  (Hnodup: NoDup (concat strs)):
  a_equiv_f (Fmatch tm1 v ps)
    (Fmatch tm2 v
     (map2
        (fun (x : pattern * formula) (strs : list string) =>
         (map_pat
            (mk_fun_str (pat_fv (fst x))
               (firstn (length (pat_fv (fst x))) strs)) 
            (fst x),
          sub_fs
            (combine (pat_fv (fst x))
               (firstn (length (pat_fv (fst x))) strs))
            (f (snd x)
               (skipn (length (pat_fv (fst x))) strs)))) ps strs)).
Proof.
  unfold a_equiv_f, a_equiv_t in *.
  simpl.
  rewrite Heq1, map2_length, Hlen1, Nat.min_id, Nat.eqb_refl, 
  eq_dec_refl; simpl.
  generalize dependent strs. clear Heq1.
  induction ps; simpl; intros; auto.
  destruct strs; inversion Hlen1.
  rewrite all2_cons.
  destruct a as [p1 t1].
  simpl.
  rewrite NoDup_concat_iff in Hnodup. destruct Hnodup as [Hn1 Hn2].
  assert (Hlenl: Datatypes.length (firstn (Datatypes.length (pat_fv p1)) l) =
    Datatypes.length (pat_fv p1)) by
    (wf_tac; specialize (Hlen2 0 ltac:(lia)); simpl in Hlen2; lia).
  assert (Hnl: NoDup l) by (apply Hn1; simpl; auto).
  rewrite map_pat_str_fv; wf_tac.
  rewrite map_pat_str_alpha; wf_tac; simpl.
  unfold mk_fun_str at 1.
  rewrite map_mk_fun; wf_tac.
  2: {
    unfold vsymbol in *;
    rewrite combine_length, Hlenl, map_length. lia.
  }
  bool_to_prop; split.
  - (*We need transitivity, which is annoying because we have to go forward*) 
    pose proof (alpha_equiv_sub_fs t1 (pat_fv p1) 
      (firstn (Datatypes.length (pat_fv p1)) l) Hlenl).
    assert (forall s : string * vty,
    In (fst s) (firstn (Datatypes.length (pat_fv p1)) l) ->
    ~ In s (bnd_f t1)). {
      intros v' Hinvl Hinvb.
      apply (Hnotbnd v' l); simpl; wf_tac. 
    }
    specialize (H H1); clear H1.
    assert (forall s : string * vty,
    In (fst s) (firstn (Datatypes.length (pat_fv p1)) l) ->
    ~ In s (form_fv t1)). {
      intros v' Hinl Hinvf.
      apply (Hnotfree v' l); simpl; simpl_set; wf_tac.
    }
    specialize (H H1 ltac:(wf_tac) (NoDup_pat_fv _)); clear H1.
    assert (forall x : vsymbol,
    In x (pat_fv p1) ->
    ~ In (fst x) (firstn (Datatypes.length (pat_fv p1)) l)). {
      intros v' Hinvb Hinvl.
      apply (Hnotbnd v' l); simpl; wf_tac.
    }
    specialize (H H1); clear H1.
    specialize (Hf 0 ltac:(lia)); simpl in Hf.
    assert (Heq2: a_equiv_f
    (sub_fs (combine (pat_fv p1) (firstn (Datatypes.length (pat_fv p1)) l)) t1)
    (sub_fs (combine (pat_fv p1) (firstn (Datatypes.length (pat_fv p1)) l))
       (f t1 (skipn (Datatypes.length (pat_fv p1)) l)))). {
        apply a_equiv_f_sub_fs_congr; auto.
        - intros x. rewrite map_snd_combine; auto.
          intros. intro C.
          apply (Hnotbnd x l); simpl; wf_tac.
        - intros x. rewrite map_snd_combine; auto.
          intros. intro C.
          specialize (Hfbnd 0 ltac:(lia)); simpl in Hfbnd.
          apply Hfbnd in C.
          apply (nodup_firstn_skipn H1 C). auto.
        - intros x. rewrite map_snd_combine; auto.
          intros. intro C.
          apply (Hnotfree x l); simpl; simpl_set; wf_tac.
        - intros x. rewrite map_snd_combine; auto.
          intros. intro C.
          apply free_in_f_spec in C.
          specialize (Hffree 0 ltac:(lia)); simpl in Hffree.
          rewrite Hffree in C.
          apply free_in_f_spec in C.
          apply (Hnotfree x l); simpl; wf_tac; simpl_set; auto. 
        - rewrite map_snd_combine; wf_tac.
       }
    revert H; unfold add_vals; rewrite !app_nil_r; intros.
    pose proof (a_equiv_f_expand_combine (combine 
      (firstn (Datatypes.length (pat_fv p1)) l) (map snd (pat_fv p1))) 
      _ _ Heq2) as Heq3.
    assert (Hmap: map snd
      (combine (pat_fv p1)
        (combine (firstn (Datatypes.length (pat_fv p1)) l) (map snd (pat_fv p1)))) =
    map fst
      (combine (combine (firstn (Datatypes.length (pat_fv p1)) l) (map snd (pat_fv p1)))
        (combine (firstn (Datatypes.length (pat_fv p1)) l) (map snd (pat_fv p1))))). {
      rewrite map_snd_combine; auto.
      rewrite map_fst_combine; auto.
      rewrite combine_length, Hlenl, map_length, Nat.min_id; auto. 
    }
    (*Now we can use transitivity*)
    pose proof (alpha_equiv_f_trans _ _ _ _ _ Hmap H Heq3).
    rewrite combine_alist_trans in H1; auto.
    unfold vsymbol in *.
    rewrite combine_length, map_length, Hlenl. lia.
  - (*Inductive case*) 
    apply IHps; auto.
    + intros. apply (Hlen2 (S i) ltac:(lia)). 
    + intros. apply (Hf (S i) ltac:(lia)). 
    + intros. apply (Hfbnd (S i) (ltac:(lia))); auto.
    + intros. apply (Hffree (S i) (ltac:(lia))).
    + intros. intro Hin.
      apply (Hnotfree v0 l0); simpl; auto; simpl_set; auto.
    + intros. intro Hin.
      apply (Hnotbnd v0 l0); simpl; auto; rewrite !in_app_iff; auto.
    + rewrite NoDup_concat_iff. split_all; auto.
      * intros; apply Hn1; simpl; auto.
      * intros. simpl in Hn2. 
        apply (Hn2 (S i1) (S i2) d x ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

(*TODO: might be helpful to use earlier*)
(*Solve inductive cases for proving variables not
  in free or bound variables*)
Ltac free_bnd Hfree Hbnd :=
  let x := fresh "x" in
  let Hinx1 := fresh "Hinx" in
  let Hinx2 := fresh "Hinx" in
  intros x Hinx1;
  match goal with
    | |- ~ In ?x (form_fv ?f) => intros Hinx2; apply (Hfree x)
    | |- ~ In ?x (bnd_f ?f) => intros Hinx2; apply (Hbnd x)
    | |- ~ In ?x (term_fv ?t) => intros Hinx2; apply (Hfree x)
    | |- ~ In ?x (bnd_t ?t) => intros Hinx2; apply (Hbnd x)
    end; simpl_set; wf_tac;
  repeat (match goal with
  | H: In ?x (nth ?i (split_lens ?l1 ?l2) ?d) |- In ?x ?l1 =>
    apply in_split_lens_ith in H
  | |- In ?x (concat ?l) => rewrite in_concat
  (*2 goals from [in_map_iff]*)
  | H: In ?x (?f (nth ?i ?l ?d)), H1: ?i < length ?l |- 
    exists y, In y ?l /\ In ?x (?f y) =>
    exists (nth i l d); split
  | H: In ?x (?f (nth ?i ?l ?d)), H1: ?i < length ?l |-
    exists y, In y (map ?f ?l) /\ In ?x y =>
    exists (f (nth i l d)); split
  (*The annoying bound variable case*)
  | H: In ?x (?f ?t) |-
    ?P \/ In ?x (?f ?t) /\ ?x <> ?v =>
    right
  | H: In ?x (?f ?t) |-
  In ?x (?f ?t) /\ ?x <> ?v =>
  let C := fresh in
  split; auto; intro C; subst;
  apply (Hbnd v); simpl
  end; wf_tac).

(*Finally, our last main theorem: this conversion
  function is alpha equivalent to the original term/formula
  if all of the new variables are unique and distinct.
  Most cases follow from the API; the match cases are hard*)
Theorem alpha_aux_equiv (t: term) (f: formula):
  (forall l
    (Hn: NoDup l)
    (Hlen: length l = length (bnd_t t))
    (Hfree: forall x, In (fst x) l -> ~ In x (term_fv t))
    (Hbnd: forall x, In (fst x) l -> ~ In x (bnd_t t)),
    a_equiv_t t (alpha_t_aux t l)) /\
  (forall l
    (Hn: NoDup l)
    (Hlen: length l = length (bnd_f f))
    (Hfree: forall x, In (fst x) l -> ~ In x (form_fv f))
    (Hbnd: forall x, In (fst x) l -> ~ In x (bnd_f f)),
    a_equiv_f f (alpha_f_aux f l)).
Proof.
  revert t f. apply term_formula_ind; simpl; intros; auto;
  try solve[apply a_equiv_t_refl].
  - (*Tfun*)
    apply alpha_tfun_congr; wf_tac.
    revert H.
    rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H0; wf_tac.
    destruct H0 as [i [Hi Hx]].
    specialize (Hx tm_d tm_d); subst. simpl.
    rewrite map2_nth with(d1:=tm_d)(d2:=nil); wf_tac.
    apply H; wf_tac; free_bnd Hfree Hbnd.
  - (*Tlet*)
    destruct l; inversion Hlen.
    inversion Hn; subst.
    apply alpha_convert_tlet'; wf_tac.
    + intro C.
      apply alpha_t_aux_bnd in C; wf_tac.
    + intro C.
      rewrite alpha_t_aux_fv' in C; wf_tac;
      try free_bnd Hfree Hbnd.
      apply (Hfree (s, snd v)); simpl; simpl_set; auto.
      right. split; auto. intro Heq.
      apply (Hbnd v); auto. simpl. rewrite <- Heq. triv.
    + apply H; wf_tac; free_bnd Hfree Hbnd.
    + apply H0; wf_tac; free_bnd Hfree Hbnd.
  - (*Tif*)
    apply alpha_tif_congr; [apply H | apply H0 | apply H1];
    wf_tac; free_bnd Hfree Hbnd.
  - (*Tmatch*)
    rewrite app_length, length_concat, map_map in Hlen.
    assert (Hlen': length l = length (bnd_t tm) +
      sum (map (fun x => length (pat_fv (fst x)) + length (bnd_t (snd x))) ps)). {
      rewrite Hlen. f_equal. f_equal. apply map_ext.
      intros; rewrite app_length; auto.
    }
    (*did most work in separate lemma, but the side
      conditions are very annoying to show*)
    (*We need some multiple times, so we prove them separately*)
    (*First, nothing in the portion of the list we are interested
      in is free in the term*)
    assert (Hnotfv: forall i, i < length ps ->
      let y := nth i ps (Pwild, tm_d) in
      let l' := skipn (Datatypes.length (pat_fv (fst y)))
        (nth i
           (split_lens (skipn (Datatypes.length (bnd_t tm)) l)
              (map
                 (fun x : pattern * term =>
                  Datatypes.length (pat_fv (fst x)) + Datatypes.length (bnd_t (snd x)))
                 ps)) []) in
      forall x, In (fst x) l' -> ~ In x (term_fv (snd y))). {
      intros i Hi y l' x Hinx1 Hinx2.
      destruct (in_dec vsymbol_eq_dec x (pat_fv (fst y))).
      -- apply (Hbnd x); wf_tac. apply In_skipn in Hinx1.
        apply in_split_lens_ith in Hinx1; wf_tac.
        right. rewrite in_concat.
        exists (pat_fv (fst y) ++ bnd_t (snd y)). split; wf_tac.
        exists y. split; auto. subst y; wf_tac.
      -- apply (Hfree x); wf_tac. apply In_skipn in Hinx1.
        apply in_split_lens_ith in Hinx1; wf_tac.
        simpl_set. right. exists y. simpl_set. split; auto.
        subst y; wf_tac.
    }
    (*Similarly, nothing is bound in the term*)
    assert (Hnotbnd: forall i, i < length ps ->
      let y := nth i ps (Pwild, tm_d) in
      let l' := skipn (Datatypes.length (pat_fv (fst y)))
        (nth i
           (split_lens (skipn (Datatypes.length (bnd_t tm)) l)
              (map
                 (fun x : pattern * term =>
                  Datatypes.length (pat_fv (fst x)) + Datatypes.length (bnd_t (snd x)))
                 ps)) []) in
      forall x, In (fst x) l' -> ~ In x (bnd_t (snd y))). {
      intros i Hi y l' x Hinx1 Hinx2.
      apply In_skipn in Hinx1.
      apply in_split_lens_ith in Hinx1; wf_tac.
      apply (Hbnd x); wf_tac. right.
      rewrite in_concat. exists (pat_fv (fst y) ++ bnd_t (snd y)).
      split; wf_tac. exists y. split; wf_tac. subst y; wf_tac.
    }
    apply alpha_tmatch; wf_tac.
    + apply H; wf_tac; free_bnd Hfree Hbnd.
    + intros. rewrite split_lens_ith; wf_tac.
    + intros i Hi. rewrite Forall_forall in H0.
      apply H0; wf_tac.
    + intros i Hi y l'.
      intros z Hinz.
      apply alpha_t_aux_bnd in Hinz; subst l' y; wf_tac.
    + intros i Hi y l' z.
      apply alpha_t_aux_fv; subst l' y; wf_tac.
    + (*ugh this one is annoying - go from In to nth*)
      intros z strs Hins Hinz1 Hinz2.
      pose proof (In_nth _ _ nil Hins).
      destruct H1 as [n' [Hn' Hstrs]].
      revert Hn'. wf_tac.
      subst. clear Hins.
      apply in_split_lens_ith in Hinz1; wf_tac.
      simpl_set. destruct Hinz2 as [tm' [Hintm' Hinz]].
      rewrite in_map_iff in Hintm'. 
      destruct Hintm' as [p [Hmt' Hinp]]; subst.
      destruct (in_dec vsymbol_eq_dec z (pat_fv (fst p))).
      * (*In this case, bound*)
        apply (Hbnd z); wf_tac. right.
        rewrite in_concat. exists (pat_fv (fst p) ++ bnd_t (snd p)).
        split; wf_tac. exists p. split; wf_tac.
      * (*In this case, free*)
        apply (Hfree z); wf_tac. simpl_set.
        right. exists p. simpl_set; auto.
    + (*Similar to last one*)
      intros z strs Hins Hinz1 Hinz2.
      pose proof (In_nth _ _ nil Hins).
      destruct H1 as [n' [Hn' Hstrs]].
      revert Hn'; wf_tac.
      subst. clear Hins.
      apply in_split_lens_ith in Hinz1; wf_tac.
      apply (Hbnd z); wf_tac.
  - (*Teps*)
    destruct l; inversion Hlen.
    inversion Hn; subst.
    apply alpha_convert_teps'; wf_tac.
    + intro C.
      apply alpha_f_aux_bnd in C; wf_tac.
    + intro C.
      rewrite alpha_f_aux_fv' in C; wf_tac;
      try free_bnd Hfree Hbnd.
      apply (Hfree (s, snd v)); simpl; simpl_set; auto.
      split; auto. intro Heq.
      apply (Hbnd v); auto. simpl. rewrite <- Heq. triv.
    + apply H; wf_tac; free_bnd Hfree Hbnd.
  - (*Fpred*)
    apply alpha_fpred_congr; wf_tac.
    revert H.
    rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H0; wf_tac.
    destruct H0 as [i [Hi Hx]].
    specialize (Hx tm_d tm_d); subst. simpl.
    rewrite map2_nth with(d1:=tm_d)(d2:=nil); wf_tac.
    apply H; wf_tac; free_bnd Hfree Hbnd.
  - (*Fquant*)
    destruct l; inversion Hlen.
    inversion Hn; subst.
    apply alpha_convert_quant'; wf_tac.
    + intro C.
      apply alpha_f_aux_bnd in C; wf_tac.
    + intro C.
      rewrite alpha_f_aux_fv' in C; wf_tac;
      try free_bnd Hfree Hbnd.
      apply (Hfree (s, snd v)); simpl; simpl_set; auto.
      split; auto. intro Heq.
      apply (Hbnd v); auto. simpl. rewrite <- Heq. triv.
    + apply H; wf_tac; free_bnd Hfree Hbnd.
  - (*Feq*)
    apply alpha_feq_congr; [apply H | apply H0]; wf_tac;
    free_bnd Hfree Hbnd.
  - (*Fbinop*)
    apply alpha_fbinop_congr; [apply H | apply H0]; wf_tac;
    free_bnd Hfree Hbnd.
  - (*Fnot*)
    apply alpha_fnot_congr. apply H; wf_tac; free_bnd Hfree Hbnd.
  - (*Flet*)
    destruct l; inversion Hlen.
    inversion Hn; subst.
    apply alpha_convert_flet'; wf_tac.
    + intro C.
      apply alpha_f_aux_bnd in C; wf_tac.
    + intro C.
      rewrite alpha_f_aux_fv' in C; wf_tac;
      try free_bnd Hfree Hbnd.
      apply (Hfree (s, snd v)); simpl; simpl_set; auto.
      right. split; auto. intro Heq.
      apply (Hbnd v); auto. simpl. rewrite <- Heq. triv.
    + apply H; wf_tac; free_bnd Hfree Hbnd.
    + apply H0; wf_tac; free_bnd Hfree Hbnd.
  - (*Fif*)
    apply alpha_fif_congr; [apply H | apply H0 | apply H1];
    wf_tac; free_bnd Hfree Hbnd.
  - (*Fmatch - TODO reduce duplication*)
    rewrite app_length, length_concat, map_map in Hlen.
    assert (Hlen': length l = length (bnd_t tm) +
      sum (map (fun x => length (pat_fv (fst x)) + length (bnd_f (snd x))) ps)). {
      rewrite Hlen. f_equal. f_equal. apply map_ext.
      intros; rewrite app_length; auto.
    }
    (*did most work in separate lemma, but the side
      conditions are very annoying to show*)
    (*We need some multiple times, so we prove them separately*)
    (*First, nothing in the portion of the list we are interested
      in is free in the term*)
    assert (Hnotfv: forall i, i < length ps ->
      let y := nth i ps (Pwild, Ftrue) in
      let l' := skipn (Datatypes.length (pat_fv (fst y)))
        (nth i
          (split_lens (skipn (Datatypes.length (bnd_t tm)) l)
              (map
                (fun x : pattern * formula =>
                  Datatypes.length (pat_fv (fst x)) + Datatypes.length (bnd_f (snd x)))
                ps)) []) in
      forall x, In (fst x) l' -> ~ In x (form_fv (snd y))). {
      intros i Hi y l' x Hinx1 Hinx2.
      destruct (in_dec vsymbol_eq_dec x (pat_fv (fst y))).
      -- apply (Hbnd x); wf_tac. apply In_skipn in Hinx1.
        apply in_split_lens_ith in Hinx1; wf_tac.
        right. rewrite in_concat.
        exists (pat_fv (fst y) ++ bnd_f (snd y)). split; wf_tac.
        exists y. split; auto. subst y; wf_tac.
      -- apply (Hfree x); wf_tac. apply In_skipn in Hinx1.
        apply in_split_lens_ith in Hinx1; wf_tac.
        simpl_set. right. exists y. simpl_set. split; auto.
        subst y; wf_tac.
    }
    (*Similarly, nothing is bound in the term*)
    assert (Hnotbnd: forall i, i < length ps ->
      let y := nth i ps (Pwild, Ftrue) in
      let l' := skipn (Datatypes.length (pat_fv (fst y)))
        (nth i
          (split_lens (skipn (Datatypes.length (bnd_t tm)) l)
              (map
                (fun x : pattern * formula =>
                  Datatypes.length (pat_fv (fst x)) + Datatypes.length (bnd_f (snd x)))
                ps)) []) in
      forall x, In (fst x) l' -> ~ In x (bnd_f (snd y))). {
      intros i Hi y l' x Hinx1 Hinx2.
      apply In_skipn in Hinx1.
      apply in_split_lens_ith in Hinx1; wf_tac.
      apply (Hbnd x); wf_tac. right.
      rewrite in_concat. exists (pat_fv (fst y) ++ bnd_f (snd y)).
      split; wf_tac. exists y. split; wf_tac. subst y; wf_tac.
    }
    apply alpha_fmatch; wf_tac.
    + apply H; wf_tac; free_bnd Hfree Hbnd.
    + intros. rewrite split_lens_ith; wf_tac.
    + intros i Hi. rewrite Forall_forall in H0.
      apply H0; wf_tac.
    + intros i Hi y l'.
      intros z Hinz.
      apply alpha_f_aux_bnd in Hinz; subst l' y; wf_tac.
    + intros i Hi y l' z.
      apply alpha_f_aux_fv; subst l' y; wf_tac.
    + (*ugh this one is annoying - go from In to nth*)
      intros z strs Hins Hinz1 Hinz2.
      destruct (In_nth _ _ nil Hins) as [n' [Hn' Hstrs]].
      revert Hn'; wf_tac.
      subst. clear Hins.
      apply in_split_lens_ith in Hinz1; wf_tac.
      simpl_set. destruct Hinz2 as [tm' [Hintm' Hinz]].
      rewrite in_map_iff in Hintm'. 
      destruct Hintm' as [p [Hmt' Hinp]]; subst.
      destruct (in_dec vsymbol_eq_dec z (pat_fv (fst p))).
      * (*In this case, bound*)
        apply (Hbnd z); wf_tac. right.
        rewrite in_concat. exists (pat_fv (fst p) ++ bnd_f (snd p)).
        split; wf_tac. exists p. split; wf_tac.
      * (*In this case, free*)
        apply (Hfree z); wf_tac. simpl_set.
        right. exists p. simpl_set; auto.
    + (*Similar to last one*)
      intros z strs Hins Hinz1 Hinz2.
      destruct (In_nth _ _ nil Hins) as [n' [Hn' Hstrs]].
      revert Hn'; wf_tac.
      subst. clear Hins.
      apply in_split_lens_ith in Hinz1; wf_tac.
      apply (Hbnd z); wf_tac.
Qed.

Definition alpha_t_aux_equiv t := proj_tm alpha_aux_equiv t.
Definition alpha_f_aux_equiv f := proj_fmla alpha_aux_equiv f.

End Convert.

(*Before giving the final conversion function, we define
  a looser notion: two terms/formulas have the same "shape" -
  ignoring free and bound variables.
  We show that alpha equivalence implies this, but also that
  this implies equivalence of [valid_ind_form] and [ind_positive]*)
Section Shape.

Fixpoint shape_p (p1 p2: pattern) :=
  match p1, p2 with
  | Pwild, Pwild => true
  | Por pa pb, Por pc pd => shape_p pa pc && shape_p pb pd
  | Pbind p1 v1, Pbind p2 v2 => shape_p p1 p2
  | Pvar v1, Pvar v2 => true
  | Pconstr f1 tys1 ps1, Pconstr f2 tys2 ps2 =>
    (funsym_eq_dec f1 f2) &&
    (list_eq_dec vty_eq_dec tys1 tys2) &&
    (length ps1 =? length ps2) &&
    all2 (fun p1 p2 => shape_p p1 p2) ps1 ps2
  | _, _ => false
  end.

Lemma alpha_p_shape vars p1 p2
  (Heq: alpha_equiv_p vars p1 p2):
  shape_p p1 p2.
Proof.
  generalize dependent p2. induction p1; simpl; intros;
  alpha_case p2 Heq; auto; bool_hyps; repeat simpl_sumbool;
  simpl.
  - rewrite H3. simpl. nested_ind_case.
    rewrite all2_cons in H1 |- *. bool_hyps.
    rewrite (Hp p), (IHps Hforall _ H2); auto.
  - rewrite IHp1_1, IHp1_2; auto.
Qed.

Fixpoint shape_t (t1 t2: term):=
  match t1, t2 with
  | Tconst c1, Tconst c2 => true
  | Tvar v1, Tvar v2 => true
  | Tfun f1 ty1 tm1, Tfun f2 ty2 tm2 =>
    (funsym_eq_dec f1 f2) &&
    (length tm1 =? length tm2) && 
    (list_eq_dec vty_eq_dec ty1 ty2) &&
    (all2 (fun t1 t2 => shape_t t1 t2)) tm1 tm2
  | Tlet tm1 x tm2, Tlet tm3 y tm4 =>
    shape_t tm1 tm3 &&
    shape_t tm2 tm4
  | Tif f1 t1 t3, Tif f2 t2 t4 =>
    shape_f f1 f2 &&
    shape_t t1 t2 &&
    shape_t t3 t4
  | Tmatch t1 ty1 ps1, Tmatch t2 ty2 ps2 =>
    shape_t t1 t2 &&
    (length ps1 =? length ps2) &&
    (vty_eq_dec ty1 ty2) &&
    all2 (fun (x1 x2: pattern * term) =>
      shape_p (fst x1) (fst x2) &&
      shape_t (snd x1) (snd x2)) ps1 ps2
  | Teps f1 x, Teps f2 y => 
    shape_f f1 f2
  | _, _ => false
  end
with shape_f (f1 f2: formula) {struct f1} : bool :=
  match f1, f2 with
  | Fpred p1 ty1 tm1, Fpred p2 ty2 tm2 =>
    (predsym_eq_dec p1 p2) &&
    (length tm1 =? length tm2) && 
    (list_eq_dec vty_eq_dec ty1 ty2) &&
    (all2 (fun t1 t2 => shape_t t1 t2)) tm1 tm2
  | Fquant q1 x f1, Fquant q2 y f2 =>
    quant_eq_dec q1 q2 &&
    shape_f f1 f2
  | Feq ty1 t1 t3, Feq ty2 t2 t4 =>
    vty_eq_dec ty1 ty2 &&
    shape_t t1 t2 &&
    shape_t t3 t4
  | Fbinop b1 f1 f3, Fbinop b2 f2 f4 =>
    binop_eq_dec b1 b2 &&
    shape_f f1 f2 &&
    shape_f f3 f4
  | Fnot f1, Fnot f2 =>
    shape_f f1 f2
  | Ftrue, Ftrue => true
  | Ffalse, Ffalse => true
  | Flet t1 x f1, Flet t2 y f2 =>
    shape_t t1 t2 &&
    shape_f f1 f2
  | Fif f1 f3 f5, Fif f2 f4 f6 =>
    shape_f f1 f2 &&
    shape_f f3 f4 &&
    shape_f f5 f6
  | Fmatch t1 ty1 ps1, Fmatch t2 ty2 ps2 =>
    shape_t t1 t2 &&
    (length ps1 =? length ps2) &&
    (vty_eq_dec ty1 ty2) &&
    all2 (fun (x1 x2: pattern * formula) =>
      shape_p (fst x1) (fst x2) &&
      shape_f (snd x1) (snd x2)) ps1 ps2
  | _, _ => false
  end.

Lemma alpha_shape t1 f1:
  (forall t2 vars
    (Heq: alpha_equiv_t vars t1 t2),
    shape_t t1 t2) /\
  (forall f2 vars
    (Heq: alpha_equiv_f vars f1 f2),
    shape_f f1 f2).
Proof.
  revert t1 f1. apply term_formula_ind; simpl; auto;
  intros.
  - alpha_case t2 Heq; auto.
  - alpha_case t2 Heq; auto.
  - alpha_case t2 Heq; bool_hyps; repeat simpl_sumbool.
    rewrite H3. simpl. nested_ind_case.
    rewrite all2_cons in H1 |- *. bool_hyps.
    rewrite (Hp t vars), (IHl1 Hforall _ H2); auto.
  - alpha_case t2 Heq; bool_hyps.
    rewrite (H t2_1 vars), (H0 t2_2 ((v, v0) :: vars)); auto.
  - alpha_case t0 Heq; bool_hyps.
    rewrite (H f0 vars), (H0 t0_1 vars), (H1 t0_2 vars); auto.
  - alpha_case t2 Heq; bool_hyps; repeat simpl_sumbool.
    rewrite (H t2 vars); auto. clear H H1. rewrite H4; simpl.
    nested_ind_case. rewrite all2_cons in H2 |- *; bool_hyps.
    rewrite (alpha_p_shape (combine (pat_fv (fst a)) (pat_fv (fst p)))),
      (Hp _ (add_vals (pat_fv (fst a)) (pat_fv (fst p)) vars) ),
      (IHps Hforall _ H1); auto.
  - alpha_case t2 Heq. bool_hyps. apply (H _ ((v, v0) :: vars)); auto.
  - alpha_case f2 Heq; bool_hyps; repeat simpl_sumbool.
    rewrite H3. simpl. nested_ind_case.
    rewrite all2_cons in H1 |- *. bool_hyps.
    rewrite (Hp t vars), (IHtms Hforall _ H2); auto.
  - alpha_case f2 Heq. bool_hyps; repeat simpl_sumbool.
    apply (H _ ((v, v0) :: vars)); auto.
  - alpha_case f2 Heq; bool_hyps; repeat simpl_sumbool.
    rewrite (H t vars), (H0 t0 vars); auto.
  - alpha_case f0 Heq; bool_hyps; repeat simpl_sumbool.
    rewrite (H f0_1 vars), (H0 f0_2 vars); auto.
  - alpha_case f2 Heq; apply (H _ vars); auto.
  - alpha_case f2 Heq; bool_hyps.
    rewrite (H t vars), (H0 f2 ((v, v0) :: vars)); auto.
  - alpha_case f0 Heq; bool_hyps.
    rewrite (H f0_1 vars), (H0 f0_2 vars), (H1 f0_3 vars); auto.
  - alpha_case f2 Heq; bool_hyps; repeat simpl_sumbool.
    rewrite (H t vars); auto. clear H H1. rewrite H4; simpl.
    nested_ind_case. rewrite all2_cons in H2 |- *; bool_hyps.
    rewrite (alpha_p_shape (combine (pat_fv (fst a)) (pat_fv (fst p)))),
      (Hp _ (add_vals (pat_fv (fst a)) (pat_fv (fst p)) vars) ),
      (IHps Hforall _ H1); auto.
Qed.

Definition alpha_shape_t t := proj_tm alpha_shape t.
Definition alpha_shape_f f := proj_fmla alpha_shape f.

(*We prove that this preserves [valid_ind_form]
  and [ind_positive]*)
Lemma shape_ind_form p (f1 f2: formula):
  shape_f f1 f2 ->
  valid_ind_form p f1 ->
  valid_ind_form p f2.
Proof.
  intros Hshp Hind. generalize dependent f2.
  induction Hind; intros; simpl in Hshp;
  [alpha_case f2 Hshp | alpha_case f0 Hshp |
    alpha_case f2 Hshp | alpha_case f2 Hshp];
  bool_hyps; repeat simpl_sumbool; constructor; auto.
  apply Nat.eqb_eq in H4.
  rewrite H0, H4; auto.
Qed.

Lemma shape_predsym_in t1 f1:
  (forall t2 p
    (Hshp: shape_t t1 t2),
    predsym_in_term p t1 = predsym_in_term p t2) /\
  (forall f2 p
    (Hshp: shape_f f1 f2),
    predsym_in p f1 = predsym_in p f2).
Proof.
  revert t1 f1; apply term_formula_ind; simpl; intros.
  - alpha_case t2 Hshp; auto.
  - alpha_case t2 Hshp; auto.
  - alpha_case t2 Hshp; bool_hyps; repeat simpl_sumbool.
    nested_ind_case. rewrite all2_cons in H1. bool_hyps.
    rewrite (Hp t), (IHl1 Hforall _ H2); auto.
  - alpha_case t2 Hshp. bool_hyps.
    rewrite (H t2_1), (H0 t2_2); auto.
  - alpha_case t0 Hshp. bool_hyps.
    rewrite (H f0), (H0 t0_1), (H1 t0_2); auto.
  - alpha_case t2 Hshp. bool_hyps; repeat simpl_sumbool.
    rewrite (H t2); auto; f_equal.
    clear H1 H. nested_ind_case.
    rewrite all2_cons in H2. bool_hyps.
    rewrite (Hp (snd p0)), (IHps Hforall _ H1); auto.
  - alpha_case t2 Hshp. apply H. auto.
  - alpha_case f2 Hshp; bool_hyps; repeat simpl_sumbool. f_equal.
    nested_ind_case. rewrite all2_cons in H1. bool_hyps.
    rewrite (Hp t), (IHtms Hforall _ H2); auto.
  - alpha_case f2 Hshp. bool_hyps. simpl_sumbool.
  - alpha_case f2 Hshp. bool_hyps. rewrite (H t), (H0 t0); auto.
  - alpha_case f0 Hshp; bool_hyps; repeat simpl_sumbool.
    rewrite (H f0_1), (H0 f0_2); auto.
  - alpha_case f2 Hshp. apply H; auto.
  - alpha_case f2 Hshp; auto.
  - alpha_case f2 Hshp; auto.
  - alpha_case f2 Hshp; auto. bool_hyps.
    rewrite (H t), (H0 f2); auto.
  - alpha_case f0 Hshp. bool_hyps.
    rewrite (H f0_1), (H0 f0_2), (H1 f0_3); auto.
  - alpha_case f2 Hshp. bool_hyps; repeat simpl_sumbool.
    rewrite (H t); auto; f_equal.
    clear H1 H. nested_ind_case.
    rewrite all2_cons in H2. bool_hyps.
    rewrite (Hp (snd p0)), (IHps Hforall _ H1); auto.
Qed.

Definition shape_t_predsym_in t := proj_tm shape_predsym_in t.
Definition shape_f_predsym_in f := proj_fmla shape_predsym_in f.

Lemma shape_ind_strictly_positive ps f1 f2:
  shape_f f1 f2 ->
  ind_strictly_positive ps f1 ->
  ind_strictly_positive ps f2.
Proof.
  intros Hshp Hind. generalize dependent f2.
  induction Hind; intros; simpl in Hshp.
  - apply ISP_notin; intros.
    rewrite <- (shape_f_predsym_in f f2); auto.
  - alpha_case f2 Hshp; bool_hyps; repeat simpl_sumbool.
    apply ISP_pred; auto.
    (*TODO: improve nested_ind_case*)
    apply Nat.eqb_eq in H4. rename l0 into tms2.
    generalize dependent tms2.
    induction ts; simpl; intros; destruct tms2; inversion H4; auto.
    rewrite all2_cons in H2. bool_hyps. simpl in H0.
    destruct H1; subst.
    + rewrite <-(shape_t_predsym_in a t); auto.
    + apply IHts with(tms2:=tms2); auto.
  - alpha_case f0 Hshp. bool_hyps. repeat simpl_sumbool.
    apply ISP_impl; auto. intros.
    rewrite <- (shape_f_predsym_in f1 f0_1); auto.
  - alpha_case f2 Hshp. bool_hyps; simpl_sumbool.
    apply ISP_quant; auto.
  - alpha_case f0 Hshp; bool_hyps; simpl_sumbool.
    apply ISP_and; auto.
  - alpha_case f0 Hshp; bool_hyps; simpl_sumbool.
    apply ISP_or; auto.
  - alpha_case f2 Hshp; bool_hyps. apply ISP_let; auto.
    intros. rewrite <- (shape_t_predsym_in t t0); auto.
  - alpha_case f0 Hshp; bool_hyps. apply ISP_if; auto;
    intros. rewrite <- (shape_f_predsym_in f1 f0_1); auto.
  - alpha_case f2 Hshp; bool_hyps; repeat simpl_sumbool.
    apply ISP_match; [
      intros; rewrite <-(shape_t_predsym_in t t0); auto |].
    clear H2 H.
    apply Nat.eqb_eq in H5.
    rename l into ps2. generalize dependent ps2.
    induction pats; simpl; intros; destruct ps2; inversion H5;
    auto. rewrite all2_cons in H3; bool_hyps.
    simpl in H0, H1.
    destruct H; subst; auto.
    + apply (H1 (snd a)); auto.
    + apply IHpats with(ps2:=ps2); auto.
      intros. apply (H1 f0); auto.
Qed.

Lemma shape_ind_positive ps f1 f2:
  shape_f f1 f2 ->
  ind_positive ps f1 ->
  ind_positive ps f2.
Proof.
  intros Hshp Hind. generalize dependent f2.
  induction Hind; intros; simpl in Hshp;
  [alpha_case f2 Hshp | alpha_case f2 Hshp | alpha_case f2 Hshp |
    alpha_case f0 Hshp] ; bool_hyps;
  repeat simpl_sumbool; try constructor; auto.
  - apply Nat.eqb_eq in H4.
    generalize dependent l0. induction ts; simpl; intros;
    destruct l0; inversion H4; auto.
    rewrite all2_cons in H2. bool_hyps.
    destruct H1; subst.
    + rewrite <- (shape_t_predsym_in a t); auto.
      apply H0; simpl; auto.
    + apply IHts with(l0:=l0); auto.
      intros; apply H0; simpl; auto.
  - intros. rewrite <- (shape_t_predsym_in t t0); auto.
  - apply (shape_ind_strictly_positive _ f1); auto.
Qed.

End Shape.
  

(*Now we can give a final alpha conversion function
  and show it has all the nice properties we want*)
Section ConvertFn.

Definition a_convert_t (t: term) :=
  alpha_t_aux t (gen_strs (length (bnd_t t)) (bnd_t t ++ term_fv t)).
Definition a_convert_f (f: formula) :=
  alpha_f_aux f (gen_strs (length (bnd_f f)) (bnd_f f ++ form_fv f)).

(*Correctness*)
Theorem a_convert_t_wf t :
  term_wf (a_convert_t t).
Proof.
  unfold term_wf.
  pose proof (gen_strs_nodup (length (bnd_t t)) (bnd_t t ++ term_fv t)) as Hnodup.
  pose proof (gen_strs_length (length (bnd_t t)) (bnd_t t ++ term_fv t)) as Hlen.
  pose proof (gen_strs_notin (length (bnd_t t)) (bnd_t t ++ term_fv t)) as Hnotin.
  split.
  - apply alpha_t_aux_bnd; auto.
  - intros x [Hinx1 Hinx2].
    apply alpha_t_aux_bnd in Hinx2; auto.
    apply alpha_t_aux_fv' in Hinx1; auto;
    try (intros y Hy1 Hy2; apply Hnotin in Hy1; apply Hy1; in_tac).
    apply Hnotin in Hinx2. apply Hinx2. in_tac.
Qed.

Theorem a_convert_t_equiv t:
  a_equiv_t t (a_convert_t t).
Proof.
  apply alpha_t_aux_equiv; 
  [apply gen_strs_nodup | apply gen_strs_length | |];
  intros y Hy Hy2; apply gen_strs_notin in Hy; apply Hy; in_tac.
Qed.

(*And the corollaries:*)
Corollary a_convert_t_ty t ty:
  term_has_type sigma t ty ->
  term_has_type sigma (a_convert_t t) ty.
Proof.
  apply a_equiv_t_type.
  apply a_convert_t_equiv.
Qed.

Corollary a_convert_t_rep v t ty 
  (Hty: term_has_type sigma t ty):
  term_rep v t ty Hty = 
  term_rep v (a_convert_t t) ty (a_convert_t_ty t ty Hty).
Proof.
  apply a_equiv_t_equiv.
  apply a_convert_t_equiv.
Qed.

(*And likewise for formulas*)

Theorem a_convert_f_wf f :
  fmla_wf (a_convert_f f).
Proof.
  unfold fmla_wf.
  pose proof (gen_strs_nodup (length (bnd_f f)) (bnd_f f ++ form_fv f)) as Hnodup.
  pose proof (gen_strs_length (length (bnd_f f)) (bnd_f f ++ form_fv f)) as Hlen.
  pose proof (gen_strs_notin (length (bnd_f f)) (bnd_f f ++ form_fv f)) as Hnotin.
  split.
  - apply alpha_f_aux_bnd; auto.
  - intros x [Hinx1 Hinx2].
    apply alpha_f_aux_bnd in Hinx2; auto.
    apply alpha_f_aux_fv' in Hinx1; auto;
    try (intros y Hy1 Hy2; apply Hnotin in Hy1; apply Hy1; in_tac).
    apply Hnotin in Hinx2. apply Hinx2. in_tac.
Qed.

Theorem a_convert_f_equiv f:
  a_equiv_f f (a_convert_f f).
Proof.
  apply alpha_f_aux_equiv;
  [apply gen_strs_nodup | apply gen_strs_length | |];
  intros y Hy Hy2; apply gen_strs_notin in Hy; apply Hy; in_tac.
Qed.

(*And the corollaries:*)
Corollary a_convert_f_valid f:
  valid_formula sigma f ->
  valid_formula sigma (a_convert_f f).
Proof.
  apply a_equiv_f_valid.
  apply a_convert_f_equiv.
Qed.

Corollary a_convert_f_rep v f 
  (Hval: valid_formula sigma f):
  formula_rep v f Hval = 
  formula_rep v (a_convert_f f) (a_convert_f_valid f Hval).
Proof.
  apply a_equiv_f_equiv.
  apply a_convert_f_equiv.
Qed.

Corollary a_convert_f_valid_ind_form p f:
  valid_ind_form p f ->
  valid_ind_form p (a_convert_f f).
Proof.
  intros. eapply shape_ind_form. 2: apply H.
  apply alpha_shape_f with(vars:=nil).
  apply a_convert_f_equiv.
Qed.

Corollary a_convert_f_pos ps f:
  ind_positive ps f ->
  ind_positive ps (a_convert_f f).
Proof.
  intros. eapply shape_ind_positive. 2: apply H.
  apply alpha_shape_f with (vars:=nil).
  apply a_convert_f_equiv.
Qed.

End ConvertFn.

End Alpha.