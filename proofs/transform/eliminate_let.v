(*Eliminate let*)

Require Import Alpha.
Require Import Task.
From Equations Require Import Equations.
Set Bullet Behavior "Strict Subproofs".

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

(*Need sublist (not eq) because the var to sub may not
  be in the term*)
Lemma elim_let_fv bt bf (t: term) (f: formula) :
  (sublist (tm_fv (elim_let_t bt bf t)) (tm_fv t)) /\
  (sublist (fmla_fv (elim_let_f bt bf f)) (fmla_fv f)).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto;
  try apply sublist_refl.
  - apply sublist_big_union; auto.
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
    + apply sublist_union; auto.
      apply sublist_remove; auto.
  - repeat (apply sublist_union; auto).
  - apply sublist_union; auto.
    apply sublist_big_union; auto.
    rewrite Forall_map in H0; revert H0. simpl.
    apply Forall_impl; intros.
    apply sublist_remove_all; auto.
  - apply sublist_remove; auto.
  - apply sublist_big_union; auto.
  - apply sublist_remove; auto.
  - apply sublist_union; auto.
  - apply sublist_union; auto.
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
  - repeat (apply sublist_union; auto).
  - apply sublist_union; auto.
    apply sublist_big_union; auto.
    rewrite Forall_map in H0.
    revert H0. apply Forall_impl.
    intros. apply sublist_remove_all; auto.
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

(*TODO: proof obligations about our measures*)
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

(*TODO: remove*)

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

Obligation Tactic := intros; try(unfold elim_let_rel, lexnat); simpl;
destruct_sig.

Definition tm_fmla_count_let' {x: tm_fmla} (y: tm_fmla_ty x) : nat :=
  match x as x' return tm_fmla_ty x' -> nat with
  | Left _ => fun t => count_let_t t
  | Right _ => fun f => count_let_f f
  end y.



Equations elim_let_tm_fmla (x: tm_fmla) : 
  { r: tm_fmla_ty x | tm_fmla_count_let' r = 0}
  by wf x elim_let_rel :=
elim_let_tm_fmla (Left (Tlet tm1 x tm2)) =>
  let t1 := proj1_sig (elim_let_tm_fmla (Left tm1)) in
  (*Need to retain info about bt in proof*)
  match bt as b return bt = b -> 
  {r : tm_fmla_ty (Left (Tlet tm1 x tm2)) | tm_fmla_count_let' r = 0} with
  (*Why we need this: not structurally recursive*)
  | true => fun Hb => 
     elim_let_tm_fmla (Left (safe_sub_t t1 x tm2))
  | false => fun Hb => 
    exist _ (Tlet t1 x (proj1_sig (elim_let_tm_fmla (Left tm2)))) _
  end eq_refl ;
elim_let_tm_fmla (Left (Tconst c)) := exist _ (Tconst c) eq_refl;
elim_let_tm_fmla (Left (Tvar v)) := exist _ (Tvar v) eq_refl;
elim_let_tm_fmla (Left (Tfun f tys tms)) :=
  exist _ (Tfun f tys (map_In tms 
    (fun x H => proj1_sig (elim_let_tm_fmla (Left x))))) _;
elim_let_tm_fmla (Left (Tif f t1 t2)) :=
  exist _ (Tif (proj1_sig (elim_let_tm_fmla (Right f))) 
    (proj1_sig (elim_let_tm_fmla (Left t1)))
    (proj1_sig (elim_let_tm_fmla (Left t2)))) _;
elim_let_tm_fmla (Left t) := exist _ (t_map 
  (fun x => proj1_sig (elim_let_tm_fmla (Left x)))
  (fun x => proj1_sig (elim_let_tm_fmla (Right x))) t) _;
elim_let_tm_fmla (Right (Flet t x f)) =>
  let t1 := proj1_sig (elim_let_tm_fmla (Left t)) in
  (*Need to retain info about bt in proof*)
  match bf as b return bf = b -> 
  {r : tm_fmla_ty (Right (Flet t x f)) | tm_fmla_count_let' r = 0} with
  (*Why we need this: not structurally recursive*)
  | true => fun Hb => 
    elim_let_tm_fmla (Right (safe_sub_f t1 x f))
  | false => fun Hb => 
    exist _ (Flet t1 x (proj1_sig (elim_let_tm_fmla (Right f)))) _
  end eq_refl ;
elim_let_tm_fmla (Right f) := exist _ (f_map 
(fun x => proj1_sig (elim_let_tm_fmla (Left x)))
(fun x => proj1_sig (elim_let_tm_fmla (Right x))) f) _.
Next Obligation.
(*Tfun termination*)
(*Because of [map_In], we have the hypothesis we need*)
assert (count_let_t x <= sum (map count_let_t tms)). {
  apply in_sum_le; rewrite in_map_iff. exists x; auto.
}
apply Lt.le_lt_or_eq_stt in H0.
destruct H0.
- apply left_slex; auto.
- rewrite H0. apply right_slex.
  apply Arith_prebase.le_lt_n_Sm_stt.
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
(*First let (t1) termination*)
destruct bt; simpl.
- apply left_slex. (*TODO: avoid lia maybe*) lia.
- destruct (count_let_t tm2).
  + rewrite !Nat.add_0_r. apply right_slex.
    lia.
  + apply left_slex; lia.
Defined.
Next Obligation.
(*Hard one: the non-structurally-recursive let call*)
rewrite Hb. (*We need info about bt*)
(*Here, we need the info from the dependent type*)
rewrite count_let_safe_sub_t.
- apply left_slex. lia.
- subst t1. simpl.
  destruct ((elim_let_tm_fmla (Left tm1) 
    (elim_let_tm_fmla_obligations_obligation_3 tm1 x tm2)));
  simpl; auto.
Defined.
Next Obligation.
(*The other let case (bt false)*)
rewrite Hb.
destruct (count_let_t tm1).
- simpl. apply right_slex. lia.
- apply left_slex; lia.
Defined.
Next Obligation.
(*bt=false number of lets*)
rewrite Hb at 1.
rewrite Nat.add_0_r.
subst t1; simpl.
destruct_sig.
Defined.
Next Obligation.
(*Termination for Tif - case 1*)
rewrite <- Nat.add_assoc.
destruct (count_let_t t1 + count_let_t t2);
[rewrite Nat.add_0_r; apply right_slex| apply left_slex]; lia.
Defined.
Next Obligation.
(*Tif termination 2*)
rewrite (Nat.add_comm _ (count_let_t t1)), <- Nat.add_assoc.
destruct (count_let_f f + count_let_t t2);
[rewrite Nat.add_0_r; apply right_slex | apply left_slex]; lia.
Defined.
Next Obligation.
(*Tif termination 3*)
destruct (count_let_f f + count_let_t t1);
[apply right_slex | apply left_slex]; lia.
Defined.
Next Obligation.
(*Tmatch termination 1*)
(*TODO: fix program, no map*)


(*ALL BELOW IS OLD*)
  


(*Eliminate lets from terms and/or formulas by using 
  (safe) substitution*)


(*This is very awkward: Equations/Function/Program Fixpoint 
  do not support mutual well-founded definitions. 
  So we need this awkward encoding. Is there a way to make this
  more generic?*)


Definition size_l (A: Type) (l: list A) : nat :=
  list_rect (fun _ => nat) 0 (fun _ _ rec => S rec) l.

(*Now, for example, let us define functions that work on the size
  of the list*)

  Require Import Coq.Arith.Wf_nat.

Section ListRectAlt.

Variable A: Type.
Variable P: list A -> Type.
Variable P_lt: forall (l: list A) (IH:forall (x: list A), 
  size_l _ x < size_l _ l -> P x), P l.

Definition list_rect_alt (l: list A) : P l :=
  Fix (well_founded_ltof _ (size_l A)) (fun l => P l) P_lt l.

End ListRectAlt.
(*
(*Write functions on terms/formulas based on the smaller relation*)
Section TermFmlaAlt.

Variable P1: term -> Type.
Variable P2: formula -> Type.
Variable P_tm: forall (t2: term) (IH: forall (t1: term),
  tm_size t1 < tm_size t2 -> P1 t1), P1 t2.
Variable P_fmla: forall (f2: formula) (IH: forall (f1: formula),
  fmla_size f1 < fmla_size f2 -> P2 f1), P2 f2.

Definition tm_fmla := Either term formula.
Definition tm_fmla_ty (x: tm_fmla) : Type :=
  match x with
  | Left t => P1 t
  | Right f => P2 f
  end.
Definition tm_fmla_size (x: tm_fmla) : nat :=
  match x with
  | Left t => tm_size t
  | Right f => fmla_size f
  end.

(*The body is not important*)
Definition term_formula_rect_alt (t: term) (f: formula) : P1 t * P2 f :=
let fn :=
Fix (well_founded_ltof _ (tm_fmla_size)) tm_fmla_ty
(fun x =>
  match x as x' return 
  (forall y, ltof tm_fmla tm_fmla_size y x' -> tm_fmla_ty y) ->
  tm_fmla_ty x' with
  | Left t => fun IH => P_tm t (fun t1 Hsz => IH (Left _ _ t1) Hsz)
  | Right f => fun IH => P_fmla f (fun f1 Hsz => IH (Right _ _ f1) Hsz)
  end) in
(fn (Left _ _ t), fn (Right _ _ f)).

End TermFmlaAlt.*)

(*I think we should just do with Equations, we want this to be readable*)


  (*
  Context {A : Type} (f : A -> nat).
  Equations list_size (l : list A) : nat :=
   | nil := 0
   | x :: xs := S (f x + list_size xs).
  
  Lemma In_list_size:
    forall x xs, In x xs -> f x < S (list_size xs).
  Proof.
    intros. funelim (list_size xs); simpl in *. destruct H.
    destruct H0.
    * subst; lia.
    * specialize (H _ H0). intuition. 
  Qed.
End list_size.
Transparent list_size.

Module RoseTree.

  Section roserec.
    Context {A : Set}.

    Inductive t : Set :=
    | leaf (a : A) : t
    | node (l : list t) : t.
    Derive NoConfusion for t.

    Fixpoint size (r : t) :=
      match r with
      | leaf a => 0
      | node l => S (list_size size l)
      end.

    Equations? elements (r : t) : list A by wf (size r) lt :=
    elements (leaf a) := [a];
    elements (node l) := concat (map_In l (fun x H => elements x)).
    Proof. red. now apply In_list_size. Qed.
      
    Equations elements_def (r : t) : list A :=
    elements_def (leaf a) := [a];
    elements_def (node l) := concat (List.map elements_def l).
    Lemma elements_equation (r : t) : elements r = elements_def r.
    Proof.
      funelim (elements r); simp elements_def; trivial. f_equal.
      induction l; simpl; auto. simp map_In. rewrite H. rewrite IHl; auto.
      intros. apply H. now constructor 2. now constructor.
    Qed.

    (** To solve measure subgoals *)
    Hint Extern 4 (_ < _) => simpl; lia : Below.
    Hint Extern 4 (MR _ _ _ _) => repeat red; simpl in *; lia : Below.

    Obligation Tactic := simpl in *; program_simpl; try typeclasses eauto with Below subterm_relation.
    (* Nested rec *) 


*)
Section ElimLet.

Context (bt bf: bool).


(*TODO: see*)

(*Fixpoint elim_let_t (t: term) : term :=
  match t with
  | Tlet tm1 x tm2 => 
    if bt then
    safe_sub_t (elim_let_t tm1) x (elim_let_t tm2)
    else Tlet (elim_let_t tm1) x (elim_let_t tm2)
  | _ => t_map elim_let_t elim_let_f t
  end 
with elim_let_f (f: formula) : formula :=
match f with
| Flet tm1 x f => 
  if bt then
  safe_sub_f (elim_let_t tm1) x (elim_let_f f)
  else Flet (elim_let_t tm1) x (elim_let_f f)
| _ => f_map elim_let_t elim_let_f f
end.*)

(*For the Equations proofs, we need a map function
  where we only prove the property for all elements in a list,
  not any arbitrary element*)
(*Fixpoint map_dep_in {A B: Type} (eq_dec: forall (x y: A), {x=y} +{x<>y}) 
  (l: list A) (f: {x: A | in_bool eq_dec x l} -> B):
  list B :=
  match l as l' return ({x: A | in_bool eq_dec x l'} -> B) -> list B
  with
  | nil => fun _ => nil
  | x :: t => fun f => f (exist _ x _) :: map_dep_in eq_dec t 
    (fun y => f
  end.

Check dep_map.
*)

(*The [t_map] and [f_map] that Why3 uses does not work
  with the wf measure here: we get impossible obligations,
  where we need to show that arbitrary terms are smaller than
  some fixed size*)

Fixpoint times_free_t (x: vsymbol) (t: term) : nat :=
  match t with
  | Tfun _ _ tms => sum (map (times_free_t x) tms)
  | Tlet t1 v t2 => times_free_t x t1 +
    (if vsymbol_eq_dec x v then 0 else times_free_t x t2)
  | Tif f t1 t2 => times_free_f x f + times_free_t x t1 + times_free_t x t2
  | Tvar v => if vsymbol_eq_dec x v then 1 else 0
  | Tconst _ => 0
  | Teps f v => if vsymbol_eq_dec x v then 0 else times_free_f x f
  | Tmatch t _ ps => times_free_t x t +
    sum (map (fun p => if in_bool vsymbol_eq_dec x (pat_fv (fst p)) then
      0 else times_free_t x (snd p)) ps)
  end
with times_free_f (x: vsymbol) (f: formula) : nat :=
  match f with
  | Fpred _ _ tms => sum (map (times_free_t x) tms)
  | Fquant _ v f => if vsymbol_eq_dec x v then 0 else times_free_f x f
  | Fbinop _ f1 f2 => times_free_f x f1 + times_free_f x f2
  | Feq _ t1 t2 => times_free_t x t1 + times_free_t x t2
  | Fnot f => times_free_f x f
  | Flet t v f => times_free_t x t +
    (if vsymbol_eq_dec x v then 0 else times_free_f x f)
  | Fif f1 f2 f3 => times_free_f x f1 + times_free_f x f2 +
    times_free_f x f3
  | Fmatch t _ ps => times_free_t x t +
    sum (map (fun p => if in_bool vsymbol_eq_dec x (pat_fv (fst p)) then
      0 else times_free_f x (snd p)) ps)
  | Ftrue => 0
  | Ffalse => 0
  end.


Lemma times_free_t_in x t f:
  ((times_free_t x t) = 0 <-> ~In x (tm_fv t)) /\
  ((times_free_f x f) = 0 <-> ~In x (fmla_fv f)).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto;
  try solve[split; intros; auto].
  - vsym_eq x v; split; intros; auto; try discriminate;
    not_or Hv; try contradiction. intros [Hxv | []]; subst; 
    contradiction.
  - rewrite sum_0, Forall_map. split; intros.
    + intro C. simpl_set.
      destruct C as [y [Hy Hinx]].
      rewrite Forall_forall in *.
      specialize (H _ Hy).
      specialize (H0 _ Hy).
      apply H; auto.
    + revert H. apply Forall_impl_strong; intros.
      apply H1. intro C.
      apply H0. simpl_set. exists a; auto.
  - simpl_set. vsym_eq x v; simpl; split; intros; auto.
    + intro C. destruct_all; auto; try contradiction.
      apply H; auto; lia.
    + not_or Hx. apply H in Hx. rewrite Hx; auto.
    + intro C.
      destruct_all; subst; [apply H | apply H0]; auto; try lia.
    + not_or Hx. apply H in Hx.
      assert (~ In x (tm_fv tm2)) by auto. apply H0 in H1. lia.
Admitted.

(*We prove a stronger lemma - the size of a substituted term
  is equal to the size of the original term t plus
  the size of the new term times the number of times x appears
  free in t. We need this for a strong enough IH in the function/predicate
  (and probably match) case*)
(*Not sure we need thi*)
Lemma tm_size_sub_t t1 x t f:
  (tm_size (sub_t t1 x t) = tm_size t + (times_free_t x t) * (tm_size t1)) /\
  (fmla_size (sub_f t1 x f) = fmla_size f +
    (times_free_f x f) * (tm_size t1)).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto; try lia.
  - vsym_eq x v; simpl; try lia.
  - induction l1; simpl in *; auto; try lia.
    inversion H; subst.
    apply IHl1 in H3; lia.
  - rewrite H. vsym_eq x v; lia.
  - rewrite H. f_equal.
    rewrite <- !Nat.add_assoc. f_equal.
    rewrite Nat.mul_add_distr_r, Nat.add_assoc,
    (Nat.add_comm (sum _) (_* tm_size t1)), <- !Nat.add_assoc. 
    f_equal. clear H.
    (*Now we just have the recursive goal*)
    induction ps; simpl in *; auto; try lia.
    inversion H0; subst.
    specialize (IHps H3).
    destruct (in_bool vsymbol_eq_dec x (pat_fv (fst a))); simpl; auto; lia.
  - vsym_eq x v; simpl; lia.
  - induction tms; simpl in *; auto; try lia.
    inversion H; subst.
    apply IHtms in H3; lia.
  - vsym_eq x v; simpl;lia.
  - vsym_eq x v; simpl; lia.
  - rewrite H. f_equal.
    rewrite <- !Nat.add_assoc. f_equal.
    rewrite Nat.mul_add_distr_r, Nat.add_assoc,
    (Nat.add_comm (sum _) (_* tm_size t1)), <- !Nat.add_assoc. 
    f_equal. clear H.
    (*Now we just have the recursive goal*)
    induction ps; simpl in *; auto; try lia.
    inversion H0; subst.
    specialize (IHps H3).
    destruct (in_bool vsymbol_eq_dec x (pat_fv (fst a))); simpl; auto; lia.
Qed.

(*I am dumb - this is NOT smaller
  What we need (or could use) is a lexicographic order:
  (num_lets x, tm_size x)
*)



Definition tm_fmla_let (x: tm_fmla) : nat :=
  match x with
  | Left t => count_let_t t
  | Right f => count_let_f f
  end.

(*Lexicographic order via nats - stdlib only has pairs*)
Section Lex.

Context {A: Type} (r1 r2: A -> nat).

Inductive lex : A -> A -> Prop :=
  | lex_fst: forall x y,
    r1 x < r1 y ->
    lex x y
  | lex_snd: forall x y,
    r1 x = r1 y ->
    r2 x < r2 y ->
    lex x y.

(*Prove well-founded*)
(*Is this true? yes*)

Lemma r1_acc: forall x y,
  r1 x < r1 y ->
  Acc lex y ->
  Acc lex x.
Proof.
  intros. generalize dependent x.
  induction H0; simpl; intros.
  assert (lex x0 x) by (constructor; auto).
  apply H; auto.
Qed.

Lemma acc_r1_r2: forall (x: A),
  Acc r1 x ->
  ()

End Lex.
Require Import Coq.Relations.Relation_Operators.

Section Foo.
Import SigTNotations.

  Variable A : Type.
  Variable B : A -> Type.
  Variable leA : A -> A -> Prop.
  Variable leB : forall x : A, B x -> B x -> Prop.

  Notation LexProd := (lexprod leA leB).

  Lemma acc_A_B_lexprod :
    forall x : A,
      Acc leA x ->
      (forall x0 : A, clos_trans A leA x0 x -> well_founded (leB x0)) ->
      forall y : B x, Acc (leB x) y -> Acc LexProd (x; y).
  Proof.
    induction 1 as [x _ IHAcc]; intros H2 y.
    induction 1 as [x0 H IHAcc0]; intros.
    apply Acc_intro.
    destruct y as [x2 y1]; intro H6.
    simple inversion H6; intro.
    - cut (leA x2 x); intros.
      + apply IHAcc; auto with sets.
        * intros.
          apply H2.
          apply t_trans with x2; auto with sets.

        * red in H2.
          apply H2.
          auto with sets.

      + injection H1 as [= <- _].
        injection H3 as [= <- _]; auto with sets.

    - rewrite <- H1.
      apply eq_sigT_eq_dep in H3.
      destruct H3.
      apply IHAcc0.
      assumption.
  Defined.*)

  Theorem wf_lexprod :
    well_founded leA ->
    (forall x : A, well_founded (leB x)) -> well_founded LexProd.
  Proof.
    intros wfA wfB; unfold well_founded.
    destruct a.
    apply acc_A_B_lexprod; auto with sets; intros.
    red in wfB.
    auto with sets.
  Defined.

Check wf_incl.

Lemma lex_acc2: forall x y,
  r1 x = r1 y ->
  r2 x < r2 y ->
  Acc lex x.
Proof.
  intros.
  remember (r2 y) as n.
  generalize dependent x.
  generalize dependent y.
  induction n; simpl; intros; auto; try lia.
  constructor.
  intros. inversion H1; subst.
  - 

(*
Lemma lex_acc1: forall n x,
  r1 x < n ->
  Acc lex x.
Proof.
  induction n; simpl; intros; try lia.
  constructor.
  intros.
  inversion H0; subst.
  - apply IHn; lia.
  - 

  remember (r1 y) as n.
  generalize dependent y.
  generalize dependent x.
  induction n; simpl; intros; subst; auto; try lia.
  constructor.
  intros. inversion H0; subst.
  - 


  - lia. constructor; intros.
    + inversion H0; subst.
  *)

Lemma lex_acc: forall x,
  Acc lex x.
Proof.
  intros.
  constructor.
  intros.
  induction H.
  - admit.
  -  


  remember (r1 x) as n1.
  generalize dependent x.
  induction n1; simpl; intros.
  - constructor; intros.
    inversion H; subst; auto; try lia.

  - constructor; intros.
    inversion H; subst.


  remember (r1 x) as n1.
  remember (r2 x) as n2.
  
  generalize dependent x.
  
  induction n1; simpl; intros.
  - constructor. intros.
    inversion H; subst.
    + lia.
    + 
  assert (forall y, r1 y < r1 x -> Acc lex )

Lemma lex_wf: well_founded lex.
Proof.
  unfold well_founded.
  intros.
  constructor.
  intros.
  induction H.



Require Import Coq.Relations.Relation_Operators.
Check well_founded_ltof.
Check ltof.
(*The relation we use*)
Definition elim_let_rel: tm_fmla -> tm_fmla -> Prop :=
  slexprod _ _ (ltof _ tm_fmla_let) (ltof _ tm_fmla_size).






cbn.
subst.


simpl.


lia.

Search (?x < S ?y).

in_sum_le



Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.

Search elim_let_tm_fmla.


(*Now we prove an induction principle *)



elim_let_tm_fmla;.


elim_let_tm_fmla (Left (Tconst c)) => Tconst c;
elim_let_tm_fmla (Left (Tvar v)) => Tvar v;
elim_let_tm_fmla (Left (Tfun f tys tms)) =>
  Tfun f tys (map ((fun x => elim_let_tm_fmla (Left x))) tms);
elim_let_tm_fmla (Left (Tlet tm1 x tm2)) =>
  
elim_let_tm_fmla (Left (Tif f t1 t2)) =>
  Tif 
  .



(*Now we can define a function on sizes*)
Definition elim_let_tm_fmla (t: term) (f: formula) :
  term * formula :=
  term_formula_rect_alt (fun _ => term) (fun _ => formula)
  (fun t rec =>
    match t with
    | Tlet tm1 x tm2 => 
    if bt then
    rec (safe_sub_t (elim_let_t))


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
    | 
  
  ).



.



  (fun x => match x with
            ).


Variable A: Type.


Check list_rect_alt.



Eval compute in (size_l _ [4;6;7;8]).


Definition size (A: Type) (l: list A) : nat.
induction l.
exact 0.
exact (S (IHl)).
Show Proof.

Definition size_l (A: Type) (l: list A) : nat :=
  list_rect A (fun l => match l with | nil => 0 | _ :: t => )


  Equations tm_fmla_func (x: tm_fmla) : tm_fmla_ret x
  by wf (tm_fmla_size x) lt :=
  tm_fmla_func (Left (Tconst c)) := tconst_case c;
  tm_fmla_func (Left (Tvar v)) := tvar_case v;
  tm_fmla_func (Left (Tfun f tys tms)) := tfun_case f tys 
    (map (fun x => tm_fmla_func (Left _ _ x)) tms);
  tm_fmla_func (Left (Tlet t1 v t2)) := 
    tlet_case (tm_fmla_func (Left _ _ t1)) v (tm_fmla_func (Left _ _ t2));
  tm_fmla_func (Left (Tif f t1 t2)) := tif_case f t1 t2;
  tm_fmla_func (Left (Tmatch tm ty ps)) := tmatch_case tm ty ps;
  tm_fmla_func (Left (Teps f v)) := teps_case f v;
  tm_fmla_func (Right (Fpred p tys tms)) := fpred_case p tys tms;
  tm_fmla_func (Right (Fquant q v f)) := fquant_case q v f;
  tm_fmla_func (Right (Feq v t1 t2)) := feq_case v t1 t2;
  tm_fmla_func (Right (Fbinop b f1 f2)) := fbinop_case b f1 f2;
  tm_fmla_func (Right (Fnot f)) := fnot_case f;
  tm_fmla_func (Right Ftrue) := ftrue_case;
  tm_fmla_func (Right Ffalse) := ffalse_case;
  tm_fmla_func (Right (Flet t v f)) := flet_case t v f;
  tm_fmla_func (Right (Fif f1 f2 f3)) := fif_case f1 f2 f3;
  tm_fmla_func (Right (Fmatch tm v ps)) := fmatch_case tm v ps
  .




Require Import Coq.Arith.Wf_nat.

(*Equations/Function/Program Fixpoint do not support 
  mutual well-founded definitions. So we give a custom utility
  to do this for size*)
Section SizeRec.

Variable rec_term: forall t, 

Variable tconst_case: constant -> term.
Variable tvar_case: vsymbol -> term.
Variable tfun_case: funsym -> list vty -> list term -> term.
Variable tlet_case: term -> vsymbol -> term -> term.
Variable tif_case: formula -> term -> term -> term.
Variable tmatch_case: term -> vty -> list (pattern * term) -> term.
Variable teps_case: formula -> vsymbol -> term.

Variable fpred_case: predsym -> list vty -> list term -> formula.
Variable fquant_case: quant -> vsymbol -> formula -> formula.
Variable feq_case: vty -> term -> term -> formula.
Variable fbinop_case: binop -> formula -> formula -> formula.
Variable fnot_case: formula -> formula.
Variable ftrue_case: formula.
Variable ffalse_case: formula.
Variable flet_case: term -> vsymbol -> formula -> formula.
Variable fif_case: formula -> formula -> formula -> formula.
Variable fmatch_case: term -> vty -> 
  list (pattern * formula) -> formula.

Definition tm_fmla := Either term formula.
Definition tm_fmla_ret (x: tm_fmla) : Set :=
  match x with
  | Left _ => term
  | Right _ => formula
  end.

Definition tm_fmla_size (x: tm_fmla) : nat :=
  match x with
  | Left t => tm_size t
  | Right f => fmla_size f
  end.

Equations tm_fmla_func (x: tm_fmla) : tm_fmla_ret x
  by wf (tm_fmla_size x) lt :=
  tm_fmla_func (Left (Tconst c)) := tconst_case c;
  tm_fmla_func (Left (Tvar v)) := tvar_case v;
  tm_fmla_func (Left (Tfun f tys tms)) := tfun_case f tys 
    (map (fun x => tm_fmla_func (Left _ _ x)) tms);
  tm_fmla_func (Left (Tlet t1 v t2)) := 
    tlet_case (tm_fmla_func (Left _ _ t1)) v (tm_fmla_func (Left _ _ t2));
  tm_fmla_func (Left (Tif f t1 t2)) := tif_case f t1 t2;
  tm_fmla_func (Left (Tmatch tm ty ps)) := tmatch_case tm ty ps;
  tm_fmla_func (Left (Teps f v)) := teps_case f v;
  tm_fmla_func (Right (Fpred p tys tms)) := fpred_case p tys tms;
  tm_fmla_func (Right (Fquant q v f)) := fquant_case q v f;
  tm_fmla_func (Right (Feq v t1 t2)) := feq_case v t1 t2;
  tm_fmla_func (Right (Fbinop b f1 f2)) := fbinop_case b f1 f2;
  tm_fmla_func (Right (Fnot f)) := fnot_case f;
  tm_fmla_func (Right Ftrue) := ftrue_case;
  tm_fmla_func (Right Ffalse) := ffalse_case;
  tm_fmla_func (Right (Flet t v f)) := flet_case t v f;
  tm_fmla_func (Right (Fif f1 f2 f3)) := fif_case f1 f2 f3;
  tm_fmla_func (Right (Fmatch tm v ps)) := fmatch_case tm v ps
  .
Next Obligation.

Definition tm_func (t: term) : term := tm_fmla_func (Left _ _ t).
Definition fmla_func (f: formula) : formula := tm_fmla_func (Right _ _ f).

Definition tm_fmla_funcs (t: term) (f: formula) : term * formula :=
    (tm_func t, fmla_func f).

  End SizeRec.

Definition elim_let_tf (t: term) (f: formula) := tm_fmla_funcs.
Check elim_let_tf.



Definition tm_fmla_func_size (x: tm_fmla) : tm_fmla_ret x := 
  Fix (well_founded_ltof _ tm_fmla_size) (fun x => tm_fmla_ret x)
  (fun x =>
    match x with
    | Left (Tconst c) =>(tconst_case c)
    | _ => Left tm_d
    end
  
  
  )


  
  
  tm_fmla (fun x y => ltof (tm_fmla_size x) (tm_fmla_size y))
    .




Check term_formula_rect.





Variable const_case: constant -> 








Section ElimLet.

Variable bt: bool.
Variable bf: bool.

Equations elim_let_t (t: term) : term
 by wf (tm_size t) lt :=
 elim_let_t (Tlet tm1 x tm2) :=
  if bt then
  elim_let_t (safe_sub_t (elim_let_t tm1) x tm2)
  else Tlet (elim_let_t tm1) x (elim_let_t tm2);
elim_let_t (Tif f t1 t2) :=
  Tif (elim_let_f f) (elim_let_t t1) (elim_let_t t2);
elim_let_t (Tconst c) := Tconst c;
elim_let_t (Tvar v) := Tvar v;
elim_let_t (Tfun f tys tms) :=
  Tfun f tys (map (fun x => elim_let_t x) tms);
with elim_let_f (f: formula) : formula
by wf (fmla_size f) lt :=
elim_let_f (Fpred ps tys tms) =>
  Fpred ps tys (map (fun x => elim_let_t x) tms)

  .

Function elim_let_t (bt: bool) (bf: bool) (t: term) {measure (size t)} : term :=
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



    
    Search safe_sub_t tm_fv.


    Search tm_fv safe_sub_t.
  (sublist (tm_fv (elim_let_t bt bf t)) (tm_fv t))
  (forall ty (Hty: term_has_type gamma t ty),
    term_has_type gamma (elim_let_t bt bf t) ty) /\
  (forall (Hty: formula_typed gamma f), formula_typed gamma (elim_let_f bt bf f)).








  match 
  | Tmatch tm ty ps =>
    Tmatch (elim_let_t tm fmla tm)

    
    sub_t tm1' (elim_let_t tm fmla tm2)


    elim_let_t tm fmla 
      (if tm then sub_t (elim_let_t tm fmla tm1) x tm2 else t)
  | 