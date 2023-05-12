(*Eliminate let*)

Require Import Alpha.
Require Import Task.
From Equations Require Import Equations.
Set Bullet Behavior "Strict Subproofs".

(*Utilities for sublists (TODO: move?)*)
Lemma sublist_refl {A: Type} (l: list A):
  sublist l l.
Proof.
  unfold sublist. auto.
Qed.

Lemma sublist_big_union {A B: Type} 
  (eq_dec: forall (x y: A), {x=y} + {x<>y})
  (f: B -> list A) (l: list B) (g: B -> B):
  Forall (fun x => sublist (f (g x)) (f x)) l ->
  sublist (big_union eq_dec f (map g l)) (big_union eq_dec f l).
Proof.
  intros.
  unfold sublist.
  intros. simpl_set.
  rewrite Forall_forall in H.
  destruct H0 as [y [Hiny Hinx]].
  rewrite in_map_iff in Hiny.
  destruct Hiny as [z [Hy Hinz]]; subst.
  exists z. split; auto.
  apply H in Hinz.
  apply Hinz; auto.
Qed.

Lemma sublist_union {A: Type} (eq_dec: forall (x y: A), {x=y}+{x<>y})
  (l1 l2 l3 l4: list A):
  sublist l1 l2 ->
  sublist l3 l4 ->
  sublist (union eq_dec l1 l3) (union eq_dec l2 l4).
Proof.
  unfold sublist. intros. simpl_set.
  destruct H1; auto.
Qed.

Lemma sublist_remove {A: Type} (eq_dec: forall (x y: A), {x=y}+{x<>y})
  v l1 l2:
  sublist l1 l2 ->
  sublist (remove eq_dec v l1) (remove eq_dec v l2).
Proof.
  unfold sublist; intros; simpl_set; destruct_all; split; auto.
Qed.

Lemma sublist_remove_all  {A: Type} (eq_dec: forall (x y: A), {x=y}+{x<>y})
  l1 l2 l3:
  sublist l2 l3 ->
  sublist (remove_all eq_dec l1 l2) (remove_all eq_dec l1 l3).
Proof.
  unfold sublist; intros; simpl_set; destruct_all; auto.
Qed.

Ltac solve_subset :=
  repeat match goal with
  | |- sublist ?x ?x => apply sublist_refl
  | |- sublist (Common.union ?eq_dec ?l1 ?l2) (Common.union ?eq_dec ?l3 ?l4) =>
    apply sublist_union; auto
  | |- sublist (remove ?eq_dec ?x ?l1) (remove ?eq_dec ?x ?l2) =>
    apply sublist_remove; auto
  | |- sublist (big_union ?eq_dec ?f (map ?g ?l)) (big_union ?eq_dec ?f ?l) =>
    apply sublist_big_union; auto
  | |- sublist (remove_all ?eq_dec ?l1 ?l2) (remove_all ?eq_dec ?l1 ?l3) =>
    apply sublist_remove_all; auto
  | H: Forall ?P (map ?f ?l) |- Forall ?Q ?l => rewrite Forall_map in H; 
    revert H; apply Forall_impl; auto; simpl; intros
  | |- Forall ?P ?l => rewrite Forall_forall; auto; simpl; intros; simpl
  end.

(*First version (not why3's)*)
Section ElimLetAlt.

Fixpoint elim_let_t (bt: bool) (bf: bool) (t: term) : term :=
  match t with
  | Tlet tm1 x tm2 => 
    if bt then
    safe_sub_t (elim_let_t bt bf tm1) x (elim_let_t bt bf tm2)
    else Tlet (elim_let_t bt bf tm1) x (elim_let_t bt bf tm2)
  | Tfun f tys tms => Tfun f tys (map (elim_let_t bt bf) tms)
  | Tif f t1 t2 =>
    Tif (elim_let_f bt bf f) (elim_let_t bt bf t1)
      (elim_let_t bt bf t2)
  | Tmatch tm ty ps =>
    Tmatch (elim_let_t bt bf tm) ty
      (map (fun x => (fst x, elim_let_t bt bf (snd x))) ps)
  | Teps f v =>
    Teps (elim_let_f bt bf f) v
  | _ => t
  end
with elim_let_f (bt: bool) (bf: bool) (f: formula) : formula :=
  match f with
  | Fpred ps tys tms => Fpred ps tys (map (elim_let_t bt bf) tms)
  | Fquant q v f => Fquant q v (elim_let_f bt bf f)
  | Feq ty t1 t2 => Feq ty (elim_let_t bt bf t1) (elim_let_t bt bf t2)
  | Fbinop b f1 f2 => Fbinop b (elim_let_f bt bf f1) (elim_let_f bt bf f2)
  | Fnot f => Fnot (elim_let_f bt bf f)
  | Flet tm1 v f =>
    if bf then
    safe_sub_f (elim_let_t bt bf tm1) v (elim_let_f bt bf f)
    else Flet (elim_let_t bt bf tm1) v (elim_let_f bt bf f)
  | Fif f1 f2 f3 => Fif (elim_let_f bt bf f1) (elim_let_f bt bf f2)
    (elim_let_f bt bf f3)
  | Fmatch tm ty ps =>
    Fmatch (elim_let_t bt bf tm) ty
      (map (fun x => (fst x, elim_let_f bt bf (snd x))) ps)
  | _ => f
  end.

(*TODO: we should really generalize to some kind of mapping*)

Lemma elim_let_typed gamma bt bf (t: term) (f: formula) :
  (forall ty (Hty: term_has_type gamma t ty),
    term_has_type gamma (elim_let_t bt bf t) ty) /\
  (forall (Hty: formula_typed gamma f), formula_typed gamma (elim_let_f bt bf f)).
Proof.
  revert t f; apply term_formula_ind; simpl; auto; intros;
  inversion Hty; subst; try solve[constructor; auto].
  - constructor; auto. rewrite map_length; auto.
    assert (Hlen: length (map (ty_subst (s_params f1) l) (s_args f1)) =
      length l1) by (rewrite map_length; auto).
    clear -H10 Hlen H.
    generalize dependent l1.
    induction (map (ty_subst (s_params f1) l) (s_args f1)); simpl;
    intros;
    destruct l1; inversion Hlen; auto.
    inversion H; subst. inversion H10; subst.
    constructor; auto.
  - destruct v as [x xty]; simpl in *.
    destruct bt. 
    + apply safe_sub_t_typed; auto.
    + constructor; auto.
  - constructor; auto; [| | rewrite null_map; auto].
    + intros x. rewrite in_map_iff.
      intros [y [Hx Hiny]]; subst; simpl; auto.
    + clear -H9 H0. induction ps; simpl in *; auto;
      intros.
      inversion H0; subst.
      destruct H; subst; simpl; auto.
  - constructor; auto. rewrite map_length; auto.
    assert (Hlen: length (map (ty_subst (s_params p) tys) (s_args p)) =
      length tms) by (rewrite map_length; auto).
    clear -H8 Hlen H.
    generalize dependent tms.
    induction (map (ty_subst (s_params p) tys) (s_args p)); simpl;
    intros;
    destruct tms; inversion Hlen; auto.
    inversion H; subst. inversion H8; subst.
    constructor; auto.
  - destruct v as [x xty]; simpl in *.
    destruct bf. 
    + apply safe_sub_f_typed; auto.
    + constructor; auto.
  - constructor; auto; [| | rewrite null_map; auto].
    + intros x. rewrite in_map_iff.
      intros [y [Hx Hiny]]; subst; simpl; auto.
    + clear -H8 H0. induction ps; simpl in *; auto;
      intros.
      inversion H0; subst.
      destruct H; subst; simpl; auto.
Qed.

Definition elim_let_t_typed bt bf t gamma := proj_tm 
  (elim_let_typed gamma bt bf) t.
Definition elim_let_f_typed bt bf f gamma := proj_fmla 
  (elim_let_typed gamma bt bf) f.

(*Then prove free vars*)


(*Need sublist (not eq) because the var to sub may not
  be in the term*)
Lemma elim_let_fv bt bf (t: term) (f: formula) :
  (sublist (tm_fv (elim_let_t bt bf t)) (tm_fv t)) /\
  (sublist (fmla_fv (elim_let_f bt bf f)) (fmla_fv f)).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto;
  solve_subset. (*Only 2 nontrivial - let *)
  - destruct bt; simpl.
    + (*Need to know if var to sub appears freely in term or not*) 
      destruct (in_dec vsymbol_eq_dec v  (tm_fv (elim_let_t true bf tm2))).
      * unfold sublist. intros x.
        rewrite safe_sub_t_fv; auto; simpl_set. intros;
        destruct_all; auto.
      * rewrite safe_sub_t_notin; auto.
        unfold sublist. intros.
        simpl_set.
        right. split; auto.
        intro C; subst; contradiction. 
    + solve_subset.
  - destruct bf; simpl.
    + destruct (in_dec vsymbol_eq_dec v  (fmla_fv (elim_let_f bt true f))).
      * unfold sublist. intros x.
        rewrite safe_sub_f_fv; auto; simpl_set. intros;
        destruct_all; auto.
      * rewrite safe_sub_f_notin; auto.
        unfold sublist. intros.
        simpl_set.
        right. split; auto.
        intro C; subst; contradiction.
    + apply sublist_union; auto.
      apply sublist_remove; auto.
Qed.

Definition elim_let_f_fv bt bf f :=
  proj_fmla (elim_let_fv bt bf) f.

(*Finally, prove that the semantics are preserved*)
Section Rep.

Context {gamma: context} (gamma_valid: valid_context gamma) 
  (pd: pi_dom) (vt: val_typevar) (pf: pi_funpred gamma_valid pd).

Lemma elim_let_rep bt bf t f:
  (forall vv ty (Hty1: term_has_type gamma t ty) 
    (Hty2: term_has_type gamma (elim_let_t bt bf t) ty),
    term_rep gamma_valid pd vt pf vv (elim_let_t bt bf t) ty Hty2 =
    term_rep gamma_valid pd vt pf vv t ty Hty1) /\
  (forall vv (Hty1: formula_typed gamma f) 
    (Hty2: formula_typed gamma (elim_let_f bt bf f)),
    formula_rep gamma_valid pd vt pf vv (elim_let_f bt bf f) Hty2 =
    formula_rep gamma_valid pd vt pf vv f Hty1).
Proof.
  revert t f; apply term_formula_ind; intros;
  try solve[simpl; apply term_rep_irrel];
  try solve[simpl_rep_full; apply fmla_rep_irrel];
  try reflexivity;
  simpl in *; simpl_rep_full.
  - (*TODO: need better way to do this - maybe sep
      extensionality lemma for these*)
    assert (ty_fun_ind_ret Hty2 = ty_fun_ind_ret Hty1).
      apply UIP_dec. apply vty_eq_dec.
    rewrite H0. f_equal. f_equal. apply UIP_dec. apply sort_eq_dec.
    f_equal. apply get_arg_list_ext; rewrite map_length; auto.
    intros.
    rewrite Forall_forall in H.
    revert Hty0.
    rewrite map_nth_inbound with(d2:=tm_d); auto; intros.
    apply H. apply nth_In; auto.
  - destruct bt.
    + destruct v as [x xty].
      erewrite safe_sub_t_rep, H, H0.
      reflexivity.
      Unshelve.
      all: inversion Hty1; subst;
      apply elim_let_t_typed; auto.
    + simpl_rep_full. erewrite H, H0. reflexivity.
  - erewrite H, H0, H1; reflexivity.
  - iter_match_gen Hty1 Htm1 Hpat1 Hty1.
    iter_match_gen Hty2 Htm2 Hpat2 Hty2.
    induction ps; simpl; intros; auto.
    simpl in *. destruct a as [p1 t1];
    simpl in *.
    rewrite H with(Hty1:=Hty1) at 1.
    rewrite match_val_single_irrel with (Hval2:=(Forall_inv Hpat1)).
    simpl.
    inversion H0; subst.
    case_match_goal; auto.
  - f_equal.
    apply functional_extensionality_dep; intros.
    assert ((proj2' (ty_eps_inv Hty2)) = (proj2' (ty_eps_inv Hty1))). {
      apply UIP_dec. apply vty_eq_dec.
    }
    erewrite H0, H. reflexivity.
  - f_equal. apply get_arg_list_ext; rewrite map_length; auto;
    intros. revert Hty0.
    rewrite map_nth_inbound with(d2:=tm_d); auto; intros.
    rewrite Forall_forall in H; apply H; auto.
    apply nth_In; auto.
  - destruct q; simpl_rep_full; apply all_dec_eq;
    split; [intros Hd d | intros Hd d | intros [d Hd]; exists d |
    intros [d Hd]; exists d]; try (erewrite H; apply Hd);
    erewrite <- H; apply Hd.
  - erewrite H, H0; reflexivity.
  - erewrite H, H0; reflexivity.
  - erewrite H; reflexivity.
  - destruct bf.
    + destruct v as [x xty].
      erewrite safe_sub_f_rep, H, H0.
      reflexivity.
      Unshelve.
      all: inversion Hty1; subst.
      apply elim_let_t_typed; auto.
      apply elim_let_f_typed; auto.
    + simpl_rep_full.
      erewrite H, H0. reflexivity.
  - erewrite H, H0, H1; reflexivity.
  - iter_match_gen Hty1 Htm1 Hpat1 Hty1.
    iter_match_gen Hty2 Htm2 Hpat2 Hty2.
    induction ps; simpl; intros; auto.
    destruct a as [p1 t1]; simpl in *.
    rewrite H with(Hty1:=Hty1) at 1.
    rewrite match_val_single_irrel with (Hval2:=(Forall_inv Hpat1)).
    simpl.
    inversion H0; subst.
    case_match_goal; auto.
Qed.
  
Definition elim_let_f_rep bt bf f :=
  proj_fmla (elim_let_rep bt bf) f.
  

End Rep.

(*Define the transformation*)
Definition eliminate_let_term (gamma: context) : trans gamma :=
  trans_goal gamma (elim_let_f true false).
  
Definition eliminate_let_fmla (gamma: context) : trans gamma :=
  trans_goal gamma (elim_let_f false true).

Definition eliminate_let (gamma: context) : trans gamma :=
  trans_goal gamma (elim_let_f true true).

(*Now we prove soundness*)
Lemma eliminate_let_sound_gen (gamma: context) :
  forall b1 b2,
  sound_trans (trans_goal gamma (elim_let_f b1 b2)).
Proof.
  intros.
  apply trans_goal_sound.
  intros. split_all.
  - apply elim_let_f_typed; auto.
  - apply elim_let_f_fv.
  - intros. erewrite elim_let_f_rep in H.
    apply H.
Qed.

Theorem eliminate_let_term_sound gamma:
  sound_trans (eliminate_let_term gamma).
Proof.
  apply eliminate_let_sound_gen.
Qed.

Theorem eliminate_let_fmla_sound gamma:
  sound_trans (eliminate_let_fmla gamma).
Proof.
  apply eliminate_let_sound_gen.
Qed.

Theorem elim_let_sound gamma:
  sound_trans (eliminate_let gamma).
Proof.
  apply eliminate_let_sound_gen.
Qed.

End ElimLetAlt.

(*The Why3 implementation is a lot more difficult to deal with,
  though it is arguably a bit more "natural" - it more closely
  mirrors what a human might do.
  The main difference is that it does f(t2[f(t1) / x])
  instead of (f(t2))[f(t1) /x]. This induces many difficulties:
  1. It is not structurally decreasing, so we cannot write it as
    a Fixpoint.
  2. The termination measure is actually very tricky. One measure
    that works is a lexicographic order (number of lets, size of term).
    Formalizing this takes some work: we need to define these metrics.
  3. Even with the termination measure, Equations (and Program, and
    Function) do not allow well-founded mutual recursion. So we have
    to awkwardly encode our function as a single dependently typed
    function.
  4. For mapping over a list recursively, we need to use a dependent 
    map function, or else we lose information in the Equations
    obligations.
  5. Finally, in the Tlet/Flet cases, the number of lets (the first
    measure) only decreases if the term we substitute has no lets
    in it. Since this is a recursive call, we need the return
    type of our function to be a sigma type encoding this info.
  6. Even this is not quite enough. For Equations to give us a 
    good enough elimination principle, we need to take in the
    bool parameters in the function. But they also need to be
    Section variables, since Equations does not allow us to
    use them in the well-founded relation otherwise (and we need
    them; we count the number of lets that we will remove).
    So we take in additional boolean parameters b1 and b2
    and proofs b1 = bt and b2 = bf. We specialize these for the
    final definition as bt bf eq_refl eq_refl, but for proofs
    they must be generic.
*)
Require Import Coq.Relations.Relation_Operators.
Section ElimLetWhy3.

(*To start, we define the size of a term/formula*)
Fixpoint tm_size (t: term) : nat :=
  match t with
  | Tconst c => 0
  | Tvar _ => 0
  | Tfun _ _ tms => 1 + sum (map tm_size tms)
  | Tlet t1 _ t2 => 1 + tm_size t1 + tm_size t2
  | Tif f t1 t2 => 1+ fmla_size f + tm_size t1 + tm_size t2
  | Tmatch tm _ ps =>
    1 + tm_size tm + sum (map (fun x => tm_size (snd x)) ps)
  | Teps f _ => 1 + fmla_size f
  end
with fmla_size (f: formula) : nat :=
  match f with
  | Fpred _ _ tms => 1 + sum (map tm_size tms)
  | Fquant _ _ f => 1 + fmla_size f
  | Feq _ t1 t2 => 1 + tm_size t1 + tm_size t2
  | Fbinop _ f1 f2 => 1 + fmla_size f1 + fmla_size f2
  | Fnot f => 1 + fmla_size f
  | Ftrue => 0
  | Ffalse => 0
  | Flet tm _ f => 1 + tm_size tm + fmla_size f
  | Fif f1 f2 f3 => 1 + fmla_size f1 + fmla_size f2 + fmla_size f3
  | Fmatch tm _ ps =>
    1 + tm_size tm + sum (map (fun x => fmla_size (snd x)) ps)
  end.

Variable bt: bool.
Variable bf: bool.

(*Count the number of "lets" in a term/formula*)
Fixpoint count_let_t (t: term) : nat :=
  match t with
  | Tfun _ _ tms => sum (map count_let_t tms)
  | Tlet t1 v t2 =>
    count_let_t t1 + (if bt then 1 else 0) +
    count_let_t t2
  | Tif f t1 t2 => count_let_f f + count_let_t t1 + count_let_t t2
  | Tvar v => 0
  | Tconst _ => 0
  | Teps f v => count_let_f f
  | Tmatch t _ ps => count_let_t t +
    sum (map (fun p => count_let_t (snd p)) ps)
  end
with count_let_f (f: formula) : nat :=
  match f with
  | Fpred _ _ tms => sum (map count_let_t tms)
  | Fquant _ v f => count_let_f f
  | Fbinop _ f1 f2 => count_let_f f1 + count_let_f f2
  | Feq _ t1 t2 => count_let_t t1 + count_let_t t2
  | Fnot f => count_let_f f
  | Flet t v f => count_let_t t + (if bf then 1 else 0) +
    count_let_f f
  | Fif f1 f2 f3 => count_let_f f1 + count_let_f f2 +
    count_let_f f3
  | Fmatch t _ ps => count_let_t t +
    sum (map (fun p => count_let_f (snd p)) ps)
  | Ftrue => 0
  | Ffalse => 0
  end.

(*Build a lexicographic order based on 2 nat functions*)

(*First, generic*)
Section Lex.

Context {A: Type} (r1 r2: A -> nat).

Definition lexnat (x y: A): Prop :=
  slexprod nat nat lt lt (r1 x, r2 x) (r1 y, r2 y).

Lemma lexnat_wf: well_founded lexnat.
Proof.
  unfold lexnat.
  unfold well_founded.
  intros.
  apply Inverse_Image.Acc_inverse_image.
  apply Lexicographic_Product.wf_slexprod; auto;
  apply Wf_nat.lt_wf.
Defined.

End Lex.

(*The bundled types we need to eliminate mutual recursion*)

Definition tm_fmla := Either term formula.
Definition tm_fmla_ty (x: tm_fmla) : Type :=
  match x with
  | Left _ => term
  | Right _ => formula
  end.
Definition tm_fmla_size (x: tm_fmla) : nat :=
  match x with
  | Left t => tm_size t
  | Right f => fmla_size f
  end.
Definition tm_fmla_count_let (x: tm_fmla) : nat :=
  match x with
  | Left t => count_let_t t
  | Right f => count_let_f f
  end.

Arguments Left {_} {_}.
Arguments Right {_} {_}.

Definition elim_let_rel: tm_fmla -> tm_fmla -> Prop :=
  lexnat tm_fmla_count_let tm_fmla_size.

Definition elim_let_rel_wf : well_founded elim_let_rel :=
  lexnat_wf _ _.

(*Dependent mapping over a list*)


(*Inspired by Equations/examples/RoseTree.v*)

Definition map_In {A B: Type} (l: list A) 
  (f: forall (x: A), In x l -> B) : list B :=
  dep_map f l (all_in_refl l).

Lemma dep_map_length {A B: Type} {P: A -> Prop} 
  (f: forall x: A, P x -> B) (l: list A) (Hall: Forall P l):
  length (dep_map f l Hall) = length l.
Proof.
  revert Hall.
  induction l; simpl; intros; auto.
Qed.

Lemma dep_map_nth {A B: Type} {P: A -> Prop}
(f: forall x: A, P x -> B) (l: list A) (Hall: Forall P l)
(i: nat) (d1: A) (d2: B) (Hnth: P (nth i l d1)):
i < length l ->
nth i (dep_map f l Hall) d2 =
f (nth i l d1) Hnth.
Proof.
  revert i Hall Hnth. induction l; simpl; intros; auto.
  - lia.
  - destruct i. f_equal. apply proof_irrel.
    apply IHl. lia.
Qed.

Lemma map_In_length {A B: Type} (l: list A) 
(f: forall (x: A), In x l -> B):
length (map_In l f) = length l.
Proof.
  unfold map_In; rewrite dep_map_length; auto.
Qed.

Lemma map_In_spec {A B : Type} (f : A -> B) (l : list A) :
  map_In l (fun (x : A) (_ : In x l) => f x) = map f l.
Proof.
  (*This is very dumb, but we need an A*)
  destruct l; auto.
  remember (a :: l) as l'.
  unfold map_In.
  apply list_eq_ext'; rewrite dep_map_length; [rewrite map_length |]; auto.
  intros n d Hn.
  erewrite dep_map_nth with(d1:=a); auto; [|apply nth_In; auto].
  rewrite map_nth_inbound with(d2:=a); auto.
Qed.

Lemma in_map_In_iff {A B: Type} (l: list A)
  (f: forall (x: A), In x l -> B) (y: B):
  In y (map_In l f) <-> exists x Hin, f x Hin = y.
Proof.
  unfold map_In. split; intros.
  - apply dep_map_in in H.
    destruct H as [x [H [Hinx Hy]]]; subst; exists x; exists H; auto.
  - destruct H as [x [Hin Hy]]; subst.
    assert (Hinx:=Hin).
    apply in_dep_map with(f:=f)(Hall:=all_in_refl l) in Hinx.
    destruct Hinx as [Hin' Hinx].
    assert (Hin = Hin') by apply proof_irrel.
    subst; auto.
Qed.

(*Proof obligations about our measures*)
Section ProofObligations.

Lemma in_sum_le l x:
  In x l ->
  x <= sum l.
Proof.
  induction l; simpl; intros; destruct H; subst; auto;
  try lia.
  apply IHl in H; lia.
Qed.

(*sub_t relation with count_let_t*)

Lemma count_let_sub tm x (Htm: count_let_t tm = 0) t f:
  count_let_t (sub_t tm x t) = count_let_t t /\
  count_let_f (sub_f tm x f) = count_let_f f.
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto.
  - vsym_eq x v.
  - f_equal. induction l1; simpl; auto.
    inversion H; subst; auto. rewrite H2, IHl1; auto.
  - rewrite H. destruct bt; auto; vsym_eq x v.
  - rewrite H. f_equal. f_equal.
    induction ps; simpl in *; auto.
    inversion H0; subst.
    rewrite IHps; auto.
    destruct (in_bool vsymbol_eq_dec x (pat_fv (fst a))); simpl; auto.
    rewrite H3; auto.
  - vsym_eq x v.
  - f_equal. induction tms; simpl; auto.
    inversion H; subst; auto. rewrite H2, IHtms; auto.
  - vsym_eq x v.
  - rewrite H. destruct bf; auto; vsym_eq x v.
  - rewrite H. f_equal. f_equal.
    induction ps; simpl in *; auto.
    inversion H0; subst.
    rewrite IHps; auto.
    destruct (in_bool vsymbol_eq_dec x (pat_fv (fst a))); simpl; auto.
    rewrite H3; auto.
Qed.

Definition count_let_sub_t tm x t Htm :=
  proj_tm (count_let_sub tm x Htm) t.
Definition count_let_sub_f tm x f Htm :=
  proj_fmla (count_let_sub tm x Htm) f.

(*count_let is preserved by [shape]*)
Lemma count_let_shape t1 f1:
  (forall t2 (Heq: shape_t t1 t2),
    count_let_t t1 = count_let_t t2) /\
  (forall f2 (Heq: shape_f f1 f2),
    count_let_f f1 = count_let_f f2).
Proof.
  revert t1 f1; apply term_formula_ind; simpl; intros; auto.
  - alpha_case t2 Heq; auto.
  - alpha_case t2 Heq; auto.
  - alpha_case t2 Heq. bool_hyps.
    f_equal.
    nested_ind_case.
    rewrite all2_cons in H1. bool_hyps.
    erewrite IHl1, Hp; try reflexivity; auto.
  - alpha_case t2 Heq. bool_hyps.
    rewrite (H _ H1), (H0 _ H2); auto.
  - alpha_case t0 Heq. bool_hyps.
    rewrite (H _ H2), (H0 _ H4), (H1 _ H3); auto.
  - alpha_case t2 Heq. bool_hyps.
    rewrite (H _ H1); auto. f_equal. f_equal.
    nested_ind_case.
    rewrite all2_cons in H2.
    bool_hyps.
    rewrite (Hp _ H7), (IHps Hforall l); auto.
  - alpha_case t2 Heq. apply H; auto.
  - alpha_case f2 Heq.  bool_hyps.
    f_equal.
    nested_ind_case.
    rewrite all2_cons in H1. bool_hyps.
    erewrite IHtms, Hp; try reflexivity; auto.
  - alpha_case f2 Heq. bool_hyps. apply H; auto.
  - alpha_case f2 Heq. bool_hyps.
    rewrite (H _ H3), (H0 _ H2); auto.
  - alpha_case f0 Heq. bool_hyps.
    rewrite (H _ H3), (H0 _ H2); auto.
  - alpha_case f2 Heq. apply H; auto.
  - alpha_case f2 Heq; auto.
  - alpha_case f2 Heq; auto.
  - alpha_case f2 Heq; bool_hyps.
    rewrite (H _ H1), (H0 _ H2); auto.
  - alpha_case f0 Heq. bool_hyps.
    rewrite (H _ H2), (H0 _ H4), (H1 _ H3); auto.
  - alpha_case f2 Heq. bool_hyps.
    rewrite (H _ H1); auto. f_equal. f_equal.
    nested_ind_case.
    rewrite all2_cons in H2.
    bool_hyps.
    rewrite (Hp _ H7), (IHps Hforall l); auto.
Qed.

Definition count_let_shape_t t1 := proj_tm count_let_shape t1.
Definition count_let_shape_f f1 := proj_fmla count_let_shape f1.

(*And thus, this applies to [safe_sub]*)
Lemma count_let_safe_sub_t tm x t (Htm: count_let_t tm = 0):
  count_let_t (safe_sub_t tm x t) = count_let_t t.
Proof.
  unfold safe_sub_t.
  destruct (in_bool vsymbol_eq_dec x (tm_fv t)); auto.
  rewrite count_let_sub_t; auto.
  destruct (existsb (fun x0 : vsymbol => in_bool vsymbol_eq_dec x0 (tm_bnd t)) (tm_fv tm)); auto.
  apply count_let_shape_t.
  apply alpha_shape_t with(vars:=nil).
  rewrite a_equiv_t_sym.
  apply a_convert_t_equiv.
Qed.

Lemma count_let_safe_sub_f tm x f (Htm: count_let_t tm = 0):
  count_let_f (safe_sub_f tm x f) = count_let_f f.
Proof.
  unfold safe_sub_f.
  destruct (in_bool vsymbol_eq_dec x (fmla_fv f)); auto.
  rewrite count_let_sub_f; auto.
  destruct (existsb (fun x0 : vsymbol => in_bool vsymbol_eq_dec x0 (fmla_bnd f)) (tm_fv tm)); auto.
  apply count_let_shape_f.
  apply alpha_shape_f with(vars:=nil).
  rewrite a_equiv_f_sym.
  apply a_convert_f_equiv.
Qed.


Lemma sum_0 l:
  sum l = 0 <-> Forall (fun x => x = 0) l.
Proof.
  induction l; simpl; intros; split; intros; auto.
  - constructor. lia. apply IHl; lia.
  - inversion H; subst. rewrite IHl; auto.
Qed.


End ProofObligations.


(*Now we can write the Equations function*)

Instance elim_let_rel_wf':
WellFounded
        (Telescopes.tele_measure (Telescopes.tip tm_fmla) (Either term formula)
           (fun x : tm_fmla => x) elim_let_rel).
Proof.
  apply elim_let_rel_wf.
  Defined.

Ltac destruct_sig :=
  repeat match goal with
  | |- context [(proj1_sig ?x)] => destruct x; simpl
  end; simpl in *; try lia; auto.

Ltac solve_triv_lexprod :=
  match goal with
  | |- slexprod nat nat lt lt (?x1, ?x2) (?x3, ?x4) =>
    let Hle := fresh in
    assert (Hle: x1 <= x3); [try lia|
      let Hlt := fresh in
      let Heq := fresh in
      let H := fresh in
      assert (H: x1 < x3 \/ x1 = x3) by lia;
      destruct H as [Hlt | Heq];
      [apply left_slex; auto | try (rewrite <- Heq); 
        apply right_slex; auto; try lia]]
end.

Obligation Tactic := intros; try(unfold elim_let_rel, lexnat); simpl;
try solve_triv_lexprod;
destruct_sig.

Definition tm_fmla_count_let' {x: tm_fmla} (y: tm_fmla_ty x) : nat :=
  match x as x' return tm_fmla_ty x' -> nat with
  | Left _ => fun t => count_let_t t
  | Right _ => fun f => count_let_f f
  end y.

Equations elim_let_tm_fmla (x: tm_fmla) b1 b2 (Hb1: bt = b1) (Hb2: bf = b2) : 
  { r: tm_fmla_ty x | tm_fmla_count_let' r = 0}
  by wf x elim_let_rel :=
(*Tlet - the interesting case*)
elim_let_tm_fmla (Left (Tlet tm1 x tm2)) true b2 Heq1 Heq2 =>
  (*Why we need this: not structurally recursive*)
  elim_let_tm_fmla (Left (safe_sub_t 
    (proj1_sig (elim_let_tm_fmla (Left tm1) true b2 Heq1 Heq2)) x tm2))
    true b2 Heq1 Heq2
  (*Need to retain info about bt in proof*);
elim_let_tm_fmla (Left (Tlet tm1 x tm2)) false b2 Heq1 Heq2 =>
  exist _ (Tlet (proj1_sig (elim_let_tm_fmla (Left tm1) false b2 Heq1 Heq2)) x 
    (proj1_sig (elim_let_tm_fmla (Left tm2) false b2 Heq1 Heq2))) _;
(*Other term cases*)
elim_let_tm_fmla (Left (Tconst c)) _ _ _ _ := exist _ (Tconst c) eq_refl;
elim_let_tm_fmla (Left (Tvar v)) _ _ _ _ := exist _ (Tvar v) eq_refl;
elim_let_tm_fmla (Left (Tfun f tys tms)) b1 b2 Heq1 Heq2 :=
  exist _ (Tfun f tys (map_In tms 
    (fun x H => proj1_sig (elim_let_tm_fmla (Left x) b1 b2 Heq1 Heq2)))) _;
elim_let_tm_fmla (Left (Tif f t1 t2)) b1 b2 Heq1 Heq2 :=
  exist _ (Tif (proj1_sig (elim_let_tm_fmla (Right f) b1 b2 Heq1 Heq2)) 
    (proj1_sig (elim_let_tm_fmla (Left t1) b1 b2 Heq1 Heq2))
    (proj1_sig (elim_let_tm_fmla (Left t2) b1 b2 Heq1 Heq2))) _;
elim_let_tm_fmla (Left (Tmatch tm ty ps)) b1 b2 Heq1 Heq2 :=
  exist _ (Tmatch (proj1_sig (elim_let_tm_fmla (Left tm) b1 b2 Heq1 Heq2))
    (*Coq/Equations complains without types given here*)
    ty (@map_In (pattern * term) (pattern * term) ps 
      (fun (x: pattern * term) H =>
     (fst x, proj1_sig (elim_let_tm_fmla (Left (snd x)) b1 b2 Heq1 Heq2))))) _;
elim_let_tm_fmla (Left (Teps f v)) b1 b2 Heq1 Heq2 :=
  exist _ (Teps (proj1_sig (elim_let_tm_fmla (Right f) b1 b2 Heq1 Heq2)) v) _;
(*Formula cases - first Flet*)
elim_let_tm_fmla (Right (Flet t x f)) b1 true Heq1 Heq2 =>
  (*Why we need this: not structurally recursive*)
  elim_let_tm_fmla (Right (safe_sub_f 
    (proj1_sig (elim_let_tm_fmla (Left t) b1 true Heq1 Heq2)) x f))
    b1 true Heq1 Heq2;
elim_let_tm_fmla (Right (Flet t x f)) b1 false Heq1 Heq2 =>
  exist _ (Flet (proj1_sig (elim_let_tm_fmla (Left t) b1 false Heq1 Heq2)) x 
    (proj1_sig (elim_let_tm_fmla (Right f) b1 false Heq1 Heq2))) _;
elim_let_tm_fmla (Right (Fpred p tys tms)) b1 b2 Heq1 Heq2 :=
  exist _ (Fpred p tys (map_In tms 
  (fun x H => proj1_sig (elim_let_tm_fmla (Left x) b1 b2 Heq1 Heq2)))) _;
elim_let_tm_fmla (Right (Fquant q v f)) b1 b2 Heq1 Heq2 :=
  exist _ (Fquant q v (proj1_sig (elim_let_tm_fmla (Right f) b1 b2 Heq1 Heq2))) _;
elim_let_tm_fmla (Right (Feq ty t1 t2)) b1 b2 Heq1 Heq2 :=
  exist _ (Feq ty (proj1_sig (elim_let_tm_fmla (Left t1) b1 b2 Heq1 Heq2)) 
    (proj1_sig (elim_let_tm_fmla (Left t2) b1 b2 Heq1 Heq2))) _;
elim_let_tm_fmla (Right (Fbinop b f1 f2)) b1 b2 Heq1 Heq2 :=
  exist _ (Fbinop b (proj1_sig (elim_let_tm_fmla (Right f1) b1 b2 Heq1 Heq2)) 
    (proj1_sig (elim_let_tm_fmla (Right f2) b1 b2 Heq1 Heq2))) _;
elim_let_tm_fmla (Right (Fnot f)) b1 b2 Heq1 Heq2 :=
  exist _ (Fnot (proj1_sig (elim_let_tm_fmla (Right f) b1 b2 Heq1 Heq2))) _;
elim_let_tm_fmla (Right Ftrue) _ _ _ _ := exist _ Ftrue eq_refl;
elim_let_tm_fmla (Right Ffalse) _ _ _ _ := exist _ Ffalse eq_refl;
elim_let_tm_fmla (Right (Fif f1 f2 f3)) b1 b2 Heq1 Heq2 :=
  exist _ (Fif (proj1_sig (elim_let_tm_fmla (Right f1) b1 b2 Heq1 Heq2)) 
    (proj1_sig (elim_let_tm_fmla (Right f2) b1 b2 Heq1 Heq2))
    (proj1_sig (elim_let_tm_fmla (Right f3) b1 b2 Heq1 Heq2))) _;
elim_let_tm_fmla (Right (Fmatch tm ty ps)) b1 b2 Heq1 Heq2 :=
  exist _ (Fmatch (proj1_sig (elim_let_tm_fmla (Left tm) b1 b2 Heq1 Heq2))
  (*Coq/Equations complains without types given here*)
  ty (@map_In (pattern * formula) (pattern * formula) ps 
    (fun x H =>
    (fst x, proj1_sig (elim_let_tm_fmla (Right (snd x)) b1 b2 Heq1 Heq2))))) _.
Next Obligation.
(*Because of [map_In], we have the hypothesis we need*)
- apply in_sum_le; rewrite in_map_iff. exists x; auto.
- apply Arith_prebase.le_lt_n_Sm_stt.
  apply in_sum_le.
  rewrite in_map_iff; exists x; auto.
Defined.
Next Obligation.
(*Tfun number of lets*)
apply sum_0.
rewrite Forall_forall. intros.
rewrite in_map_iff in H.
destruct H as [t [Hx Hint]]; subst.
rewrite in_map_In_iff in Hint.
destruct Hint as [x [Hinx Ht]]; subst.
destruct_sig.
Defined.
Next Obligation.
(*Hard one: the non-structurally-recursive let call*)
- subst. rewrite Heq1. (*We need info about bt*)
  (*Here, we need the info from the dependent type*)
  rewrite count_let_safe_sub_t; try lia.
- subst. rewrite Heq1 in H, H1.
  rewrite count_let_safe_sub_t in H, H1; auto. lia.
Defined.
Next Obligation.
(*bt=false number of lets*)
subst. rewrite Heq1. lia. 
Defined.
Next Obligation.
(*Tmatch termination*)
- eapply Nat.le_trans; [| apply Nat.le_add_l].
  apply in_sum_le. rewrite in_map_iff. exists x; auto.
- apply Arith_prebase.le_lt_n_Sm_stt.
  eapply Nat.le_trans; [| apply Nat.le_add_l].
  apply in_sum_le. rewrite in_map_iff. exists x; auto.
Defined.
Next Obligation.
(*Tmatch number of lets*)
rewrite e; simpl.
apply sum_0.
rewrite Forall_forall; intros.
rewrite in_map_iff in H.
destruct H as [p [Hp Hinx]]; subst.
rewrite in_map_In_iff in Hinx.
destruct Hinx as [p1 [Hin Hp]]; subst; simpl.
destruct_sig.
Defined.
Next Obligation.
(*Fpred termination*)
- apply in_sum_le; rewrite in_map_iff. exists x; auto.
- apply Arith_prebase.le_lt_n_Sm_stt.
  apply in_sum_le.
  rewrite in_map_iff; exists x; auto.
Defined.
Next Obligation.
(*Fpred number of lets*)
apply sum_0.
rewrite Forall_forall. intros.
rewrite in_map_iff in H.
destruct H as [t [Hx Hint]]; subst.
rewrite in_map_In_iff in Hint.
destruct Hint as [x [Hinx Ht]]; subst.
destruct_sig.
Defined.
Next Obligation.
(* non-structurally-recursive let call*)
- subst. rewrite Heq2. (*We need info about bt*)
  (*Here, we need the info from the dependent type*)
  rewrite count_let_safe_sub_f; lia.
- subst. rewrite Heq2 in H, H1.
  rewrite count_let_safe_sub_f in H, H1; lia.
Defined.
Next Obligation.
(*bt=false number of lets*)
subst. rewrite Heq2; lia.
Defined.
Next Obligation.
(*Fmatch termination*)
- eapply Nat.le_trans; [| apply Nat.le_add_l].
  apply in_sum_le. rewrite in_map_iff. exists x; auto.
- apply Arith_prebase.le_lt_n_Sm_stt.
  eapply Nat.le_trans; [| apply Nat.le_add_l].
  apply in_sum_le. rewrite in_map_iff. exists x; auto.
Defined.
Next Obligation.
(*Fmatch number of lets*)
rewrite e; simpl.
apply sum_0.
rewrite Forall_forall; intros.
rewrite in_map_iff in H.
destruct H as [p [Hp Hinx]]; subst.
rewrite in_map_In_iff in Hinx.
destruct Hinx as [p1 [Hin Hp]]; subst; simpl.
destruct_sig.
Defined.

(*Now our function is defined. We can define the term and
  formula versions and show that underneath all of the dependent
  types, we have the functions we expect*)
Section RewriteLemma.

(*First, as why3 does, we include a mapping function
  over terms and formulas for the recursive cases*)
(*NOTE: we cannot use this in the Equations definition;
  we get unsolvable proof obligations*)

(*Not binding or type safe*)
Definition t_map (f1: term -> term) (f2: formula -> formula) 
  (t: term): term :=
  match t with
  | Tfun f vs tms => Tfun f vs (map_In tms (fun x H => f1 x))
  | Tlet t1 v t2 => Tlet (f1 t1) v (f1 t2)
  | Tif f t1 t2 => Tif (f2 f) (f1 t1) (f1 t2)
  | Tmatch tm ty ps => Tmatch (f1 tm) ty 
      (map (fun x => (fst x, f1 (snd x))) ps)
  | Teps f v => Teps (f2 f) v
  | _ => t
  end.

Definition f_map (f1: term -> term) (f2: formula -> formula) 
  (f: formula): formula :=
  match f with
  | Fpred p tys tms => Fpred p tys (map f1 tms)
  | Fquant q x f => Fquant q x (f2 f)
  | Feq ty t1 t2 => Feq ty (f1 t1) (f1 t2)
  | Fbinop b fa fb => Fbinop b (f2 fa) (f2 fb)
  | Fnot f => Fnot (f2 f)
  | Flet t v f => Flet (f1 t) v (f2 f)
  | Fif fa fb fc => Fif (f2 fa) (f2 fb) (f2 fc)
  | Fmatch tm ty ps => Fmatch (f1 tm) ty
  (map (fun x => (fst x, f2 (snd x))) ps)
  | _ => f
  end.

(*Do in 2 pieces*)
Definition elim_let_tm_aux b1 b2 Heq1 Heq2 (t: term) : term :=
  proj1_sig (elim_let_tm_fmla (Left t) b1 b2 Heq1 Heq2).
Definition elim_let_fmla_aux b1 b2 Heq1 Heq2 (f: formula)  : formula :=
  proj1_sig (elim_let_tm_fmla (Right f) b1 b2 Heq1 Heq2).

(*The actual functions*)
Definition elim_let_tm (t: term) : term :=
  elim_let_tm_aux bt bf eq_refl eq_refl t.
Definition elim_let_fmla (f: formula) : formula :=
  elim_let_fmla_aux bt bf eq_refl eq_refl f.

Lemma elim_let_tm_eq_aux (t: term) b1 b2 Heq1 Heq2 :
  elim_let_tm_aux b1 b2 Heq1 Heq2 t =
  match t with
  | Tlet t1 v t2 =>
    let t1' := elim_let_tm_aux b1 b2 Heq1 Heq2 t1 in
    if bt then
    elim_let_tm_aux b1 b2 Heq1 Heq2 (safe_sub_t t1' v t2)
    else Tlet t1' v (elim_let_tm_aux b1 b2 Heq1 Heq2 t2)
  | _ => t_map (elim_let_tm_aux b1 b2 Heq1 Heq2) 
    (elim_let_fmla_aux b1 b2 Heq1 Heq2) t
  end.
Proof.
  unfold elim_let_tm_aux; destruct t; simpl; auto.
  - rewrite elim_let_tm_fmla_equation_1; reflexivity.
  - rewrite elim_let_tm_fmla_equation_2; reflexivity.
  - rewrite elim_let_tm_fmla_equation_3; reflexivity.
  - (*We need aux so we can destruct without dependent type issues*) 
    destruct b1; subst; simpl.
    + rewrite Heq1 at 1.
      rewrite elim_let_tm_fmla_equation_4; reflexivity.
    + rewrite Heq1 at 1.
      rewrite elim_let_tm_fmla_equation_5; reflexivity.
  - rewrite elim_let_tm_fmla_equation_6; reflexivity.
  - rewrite elim_let_tm_fmla_equation_7; simpl.
    f_equal. apply map_In_spec.
  - rewrite elim_let_tm_fmla_equation_8; reflexivity.
Qed.

(*The theorem we want: 
  the definition in why3/src/transform/eliminate_let.ml*)
Theorem elim_let_tm_eq (t: term) :
elim_let_tm t =
match t with
| Tlet t1 v t2 =>
  let t1' := elim_let_tm t1 in
  if bt then
  elim_let_tm (safe_sub_t t1' v t2)
  else Tlet t1' v (elim_let_tm t2)
| _ => t_map elim_let_tm elim_let_fmla t
end.
Proof.
  apply elim_let_tm_eq_aux.
Qed.

Lemma elim_let_fmla_eq_aux (f: formula) b1 b2 Heq1 Heq2 :
  elim_let_fmla_aux b1 b2 Heq1 Heq2 f =
  match f with
  | Flet t v f =>
    let t1' := elim_let_tm_aux b1 b2 Heq1 Heq2 t in
    if bf then
    elim_let_fmla_aux b1 b2 Heq1 Heq2 (safe_sub_f t1' v f)
    else Flet t1' v (elim_let_fmla_aux b1 b2 Heq1 Heq2 f)
  | _ => f_map (elim_let_tm_aux b1 b2 Heq1 Heq2) 
    (elim_let_fmla_aux b1 b2 Heq1 Heq2) f
  end.
Proof.
  unfold elim_let_fmla_aux; destruct f; simpl; auto.
  - rewrite elim_let_tm_fmla_equation_9; simpl; 
    rewrite map_In_spec; reflexivity.
  - rewrite elim_let_tm_fmla_equation_10; reflexivity.
  - rewrite elim_let_tm_fmla_equation_11; reflexivity.
  - rewrite elim_let_tm_fmla_equation_12; reflexivity.
  - rewrite elim_let_tm_fmla_equation_13; reflexivity.
  - rewrite elim_let_tm_fmla_equation_14; reflexivity.
  - rewrite elim_let_tm_fmla_equation_15; reflexivity.
  - (*We need aux so we can destruct without dependent type issues*) 
    destruct b2; subst; simpl.
    + rewrite Heq2 at 1.
      rewrite elim_let_tm_fmla_equation_16; reflexivity.
    + rewrite Heq2 at 1.
      rewrite elim_let_tm_fmla_equation_17; reflexivity.
  - rewrite elim_let_tm_fmla_equation_18; reflexivity.
  - rewrite elim_let_tm_fmla_equation_19; simpl.
    f_equal. apply map_In_spec.
Qed.

Lemma elim_let_fmla_eq (f: formula) :
  elim_let_fmla f =
  match f with
  | Flet t v f =>
    let t' := elim_let_tm t in
    if bf then
    elim_let_fmla (safe_sub_f t' v f)
    else Flet t' v (elim_let_fmla f)
  | _ => f_map elim_let_tm elim_let_fmla f
  end.
Proof.
  apply elim_let_fmla_eq_aux.
Qed.

End RewriteLemma.

(*Now we have to prove soundness. This is more difficult because 
  we can't use structural induction; we use the induction principle
  generated by Equations. But this means that our theorem
  statements must be a bit awkward*)

(*First, typing*)
Section Typing.
Variable gamma: context.

(*We need a separate definition for our prop*)
Definition elim_let_tm_fmla_ty (x: tm_fmla) (y: tm_fmla_ty x) : Prop :=
  match x as x' return tm_fmla_ty x' -> Prop with
  | Left t1 => fun t2 => 
    forall ty, term_has_type gamma t1 ty -> term_has_type gamma t2 ty
  | Right f1 => fun f2 =>
    formula_typed gamma f1 -> formula_typed gamma f2
  end y.

Lemma elim_let_tm_fmla_typed (x: tm_fmla) b1 b2 Heq1 Heq2:
  elim_let_tm_fmla_ty x (proj1_sig (elim_let_tm_fmla x b1 b2 Heq1 Heq2)).
Proof.
  apply elim_let_tm_fmla_elim; intros; simpl; intros; auto; simpl in *.
  - inversion H1; subst; auto.
    rewrite map_In_spec. constructor; auto;
    [rewrite map_length; auto|].
    assert (length tms = length (map (ty_subst (s_params f) tys) (s_args f)))
      by (rewrite map_length; auto).
    generalize dependent (map (ty_subst (s_params f) tys) (s_args f)).
    clear -H.
    induction tms; simpl; intros; auto.
    destruct l; inversion H2. inversion H12; subst; simpl in H. 
    constructor; auto.
    apply H; auto.
  - (*Without the b1 b2 Heq1 Heq2, Equations does not give us
    a good enough IH here - don't know about [safe_sub]*)
    apply H0. destruct x0 as [x1 x2].
    inversion H1; subst; simpl in *. 
    apply safe_sub_t_typed; auto.
  - inversion H2; subst. constructor; auto.
  - inversion H3; subst.
    constructor; auto.
  - rewrite map_In_spec. 
    inversion H2; subst. constructor; auto; [| |rewrite null_map; auto];
    intros p; rewrite in_map_iff; 
    intros [p1 [Hp Hinp1]]; subst; simpl; auto.
  - inversion H1; subst. constructor; auto.
  - inversion H1; subst. rewrite map_In_spec; constructor; auto;
    try rewrite map_length; auto.
    assert (length tms = length (map (ty_subst (s_params p) tys) (s_args p)))
      by (rewrite map_length; auto).
    generalize dependent (map (ty_subst (s_params p) tys) (s_args p)).
    clear -H.
    induction tms; simpl; intros; auto.
    destruct l; inversion H2. inversion H10; subst; simpl in H. 
    constructor; auto.
    apply H; auto.
  - inversion H1; subst. constructor; auto.
  - inversion H2; subst. constructor; auto.
  - inversion H2; subst. constructor; auto.
  - inversion H1; subst. constructor; auto.
  - inversion H1; subst. apply H0. destruct x0 as [x1 x2]. 
    apply safe_sub_f_typed; auto.
  - inversion H2; subst. constructor; auto.
  - inversion H3; subst. constructor; auto.
  - rewrite map_In_spec. 
    inversion H2; subst. constructor; auto; [| |rewrite null_map; auto];
    intros p; rewrite in_map_iff; 
    intros [p1 [Hp Hinp1]]; subst; simpl; auto.
Qed.

(*And our corollaries*)
Lemma elim_let_tm_typed (t: term) (ty: vty):
  term_has_type gamma t ty ->
  term_has_type gamma (elim_let_tm t) ty.
Proof.
  intros.
  apply (elim_let_tm_fmla_typed (Left t) bt bf eq_refl eq_refl);
  auto.
Qed.

Lemma elim_let_fmla_typed (f: formula):
  formula_typed gamma f ->
  formula_typed gamma (elim_let_fmla f).
Proof.
  intros.
  apply (elim_let_tm_fmla_typed (Right f) bt bf eq_refl eq_refl);
  auto.
Qed.

End Typing.

(*Part 2: free vars*)
Section FreeVars.


(*We need a separate definition for our prop*)
Definition elim_let_tm_fmla_fv_sublist (x: tm_fmla) (y: tm_fmla_ty x) : Prop :=
  match x as x' return tm_fmla_ty x' -> Prop with
  | Left t1 => fun t2 => 
    sublist (tm_fv t2) (tm_fv t1)
  | Right f1 => fun f2 =>
    sublist (fmla_fv f2) (fmla_fv f1)
  end y.

Lemma elim_let_tm_fmla_fv (x: tm_fmla) b1 b2 Heq1 Heq2:
elim_let_tm_fmla_fv_sublist x (proj1_sig (elim_let_tm_fmla x b1 b2 Heq1 Heq2)).
Proof.
  apply elim_let_tm_fmla_elim; intros; simpl; intros; auto; simpl in *;
  try (rewrite map_In_spec); solve_subset;
  try solve[ rewrite Forall_forall; auto]. 
  (*Only 2 nontrivial goals - let*) 
  - eapply sublist_trans. apply H0. unfold sublist. intros.
    destruct (in_dec vsymbol_eq_dec x0 (tm_fv tm2)).
    + rewrite safe_sub_t_fv in H1; auto.
      simpl_set. destruct H1; auto.
    + rewrite safe_sub_t_notin in H1; auto.
      simpl_set. right; split; auto. intro C; subst; contradiction.
  - eapply sublist_trans. apply H0. unfold sublist. intros.
    destruct (in_dec vsymbol_eq_dec x0 (fmla_fv f)).
    + rewrite safe_sub_f_fv in H1; auto.
      simpl_set. destruct H1; auto.
    + rewrite safe_sub_f_notin in H1; auto.
      simpl_set. right; split; auto. intro C; subst; contradiction.
Qed.

(*Corollary:*)
Lemma elim_let_fmla_fv (f: formula):
  sublist (fmla_fv (elim_let_fmla f)) (fmla_fv f).
Proof.
  apply (elim_let_tm_fmla_fv (Right f) bt bf eq_refl eq_refl);
  auto.
Qed.

End FreeVars.

(*Last piece: preserves semantics*)
Section Rep.

Context {gamma: context} (gamma_valid: valid_context gamma) 
  (pd: pi_dom) (vt: val_typevar) (pf: pi_funpred gamma_valid pd).

Definition elim_let_tm_fmla_rep_eq (x: tm_fmla) (y: tm_fmla_ty x) : Prop :=
  match x as x' return tm_fmla_ty x' -> Prop with
  | Left t1 => fun t2 => 
    forall vv ty (Hty1: term_has_type gamma t1 ty) 
      (Hty2: term_has_type gamma t2 ty),
    term_rep gamma_valid pd vt pf vv t2 ty Hty2 =
    term_rep gamma_valid pd vt pf vv t1 ty Hty1
  | Right f1 => fun f2 =>
    forall vv (Hty1: formula_typed gamma f1)
      (Hty2: formula_typed gamma f2),
    formula_rep gamma_valid pd vt pf vv f2 Hty2 =
    formula_rep gamma_valid pd vt pf vv f1 Hty1
  end y.

Lemma elim_let_tm_fmla_rep (x: tm_fmla) b1 b2 Heq1 Heq2:
elim_let_tm_fmla_rep_eq x (proj1_sig (elim_let_tm_fmla x b1 b2 Heq1 Heq2)).
Proof.
  apply elim_let_tm_fmla_elim; intros; simpl; intros; auto; simpl in *;
  try apply term_rep_irrel; simpl_rep_full.
  - (*TODO: fix*)
    assert (ty_fun_ind_ret Hty2 = ty_fun_ind_ret Hty1).
      apply UIP_dec. apply vty_eq_dec.
    rewrite H1. f_equal. f_equal. apply UIP_dec. apply sort_eq_dec.
    f_equal. clear H1. revert Hty2.
    rewrite map_In_spec; intros.
    apply get_arg_list_ext; rewrite map_length; auto.
    intros.
    revert Hty0.
    rewrite map_nth_inbound with(d2:=tm_d); auto; intros.
    apply H. apply nth_In; auto.
  - (*Tlet case 1*)
    inversion Hty1; subst.
    destruct x0 as [x1 x2]. erewrite H0.  erewrite safe_sub_t_rep.
    erewrite H. reflexivity.
    Unshelve.
    apply safe_sub_t_typed; auto.
    all: apply (elim_let_tm_fmla_typed gamma (Left tm1)); auto.
  - (*Tlet case 2*)
    erewrite H, H0. reflexivity.
  - (*Tif*) erewrite H, H0, H1; reflexivity.
  - (*Tmatch*)
    revert Hty2. clear H1.
    rewrite !map_In_spec; intros.
    iter_match_gen Hty1 Htm1 Hpat1 Hty1.
    iter_match_gen Hty2 Htm2 Hpat2 Hty2.
    induction ps; simpl; intros; auto.
    simpl in *. destruct a as [p1 t1];
    simpl in *.
    rewrite H with(Hty1:=Hty1) at 1.
    rewrite match_val_single_irrel with (Hval2:=(Forall_inv Hpat1)).
    simpl.
    case_match_goal; auto.
    apply (H0 (p1, t1)); auto.
  - f_equal. apply functional_extensionality_dep; intros.
    assert ((proj2' (ty_eps_inv Hty2)) = (proj2' (ty_eps_inv Hty1))). {
      apply UIP_dec. apply vty_eq_dec.
    }
    erewrite H, H1. reflexivity.
  - f_equal. revert Hty2. 
    rewrite map_In_spec; intros.
    apply get_arg_list_ext; rewrite map_length; auto.
    intros.
    revert Hty0.
    rewrite map_nth_inbound with(d2:=tm_d); auto; intros.
    apply H. apply nth_In; auto.
  - destruct q; simpl_rep_full; apply all_dec_eq; split;
    [intros Hd d | intros Hd d| intros [d Hd]; exists d |
    intros [d Hd]; exists d];
    try (erewrite H; apply Hd);
    erewrite <- H; apply Hd.
  - erewrite H, H0; reflexivity.
  - erewrite H, H0; reflexivity.
  - f_equal. apply H.
  - (*Flet case 1*)
    inversion Hty1; subst.
    destruct x0 as [x1 x2]. erewrite H0.  erewrite safe_sub_f_rep.
    erewrite H. reflexivity.
    Unshelve.
    apply safe_sub_f_typed; auto.
    all: apply (elim_let_tm_fmla_typed gamma (Left t)); auto.
  - (*Flet case 2*)
    erewrite H, H0. reflexivity.
  - (*Fif*) erewrite H, H0, H1; reflexivity.
  - (*Fmatch*)
    revert Hty2. clear H1.
    rewrite !map_In_spec; intros.
    iter_match_gen Hty1 Htm1 Hpat1 Hty1.
    iter_match_gen Hty2 Htm2 Hpat2 Hty2.
    induction ps; simpl; intros; auto.
    simpl in *. destruct a as [p1 t1];
    simpl in *.
    rewrite H with(Hty1:=Hty1) at 1.
    rewrite match_val_single_irrel with (Hval2:=(Forall_inv Hpat1)).
    simpl.
    case_match_goal; auto.
    apply (H0 (p1, t1)); auto.
Qed.

(*And the corollary:*)
Lemma elim_let_fmla_rep vv (f: formula) :
  forall (Hty1: formula_typed gamma f)
    (Hty2: formula_typed gamma (elim_let_fmla f)),
    formula_rep gamma_valid pd vt pf vv (elim_let_fmla f) Hty2 =
    formula_rep gamma_valid pd vt pf vv f Hty1.
Proof.
  apply (elim_let_tm_fmla_rep (Right f) bt bf eq_refl eq_refl);
  auto.
Qed.

End Rep.

End ElimLetWhy3.

(*Define the transformation*)
Definition eliminate_let_term2 (gamma: context) : trans gamma :=
  trans_goal gamma (elim_let_fmla true false).
  
Definition eliminate_let_fmla2 (gamma: context) : trans gamma :=
  trans_goal gamma (elim_let_fmla false true).

Definition eliminate_let2 (gamma: context) : trans gamma :=
  trans_goal gamma (elim_let_fmla true true).

(*Now we prove soundness*)
Lemma eliminate_let_sound_gen2 (gamma: context) :
  forall b1 b2,
  sound_trans (trans_goal gamma (elim_let_fmla b1 b2)).
Proof.
  intros.
  apply trans_goal_sound.
  intros. split_all.
  - apply elim_let_fmla_typed; auto.
  - apply elim_let_fmla_fv.
  - intros. erewrite elim_let_fmla_rep in H.
    apply H.
Qed.

Theorem eliminate_let_term_sound2 gamma:
  sound_trans (eliminate_let_term2 gamma).
Proof.
  apply eliminate_let_sound_gen2.
Qed.

Theorem eliminate_let_fmla_sound2 gamma:
  sound_trans (eliminate_let_fmla2 gamma).
Proof.
  apply eliminate_let_sound_gen2.
Qed.

Theorem elim_let_sound2 gamma:
  sound_trans (eliminate_let2 gamma).
Proof.
  apply eliminate_let_sound_gen2.
Qed.
