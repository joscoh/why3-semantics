(*Here we give a denotational semantics for Why3, assuming some classical axioms*)
Require Import Syntax.
Require Import Types.
Require Import Typing.
Require Import Typechecker. (*We need [typecheck_dec]*)
Require Import IndTypes.
Require Import Semantics.
Require Import Hlist.
Require Import Coq.Program.Equality.

(*The axioms we need: excluded middle and definite description*)
Require Import Coq.Logic.ClassicalEpsilon.

Ltac split_all :=
  repeat match goal with
  | H: ?P /\ ?Q |- _ => destruct H
  | |- ?P /\ ?Q => split
  end.

(*This gives us the following (we give a shorter name)*)
Definition all_dec : forall (P : Prop), {P} + {~P} := excluded_middle_informative.

(*Can we interpret ADTs as Coq inductive types?*)

Section Denot.

Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma)
  (pd: pi_dom) .

(*Representation of terms, formulas, patterns*)

Notation domain := (domain (dom_aux pd)).
Notation val x :=  (v_subst (v_typevar x)).
Notation val_typevar := (@val_typevar sigma).
Notation substi := (substi pd).

(*TODO: 2 options: can take in hypothesis that term has type ty and then use
  dependent type obligations
  OR just match on type and return option (but then we need options everywhere)
  
  for now, use typing hypothesis - this makes the function stuff a bit easier
  and we shouldn't have to match on types everywhere
  *)
(*TODO: HERE*)
Definition cast_dom_vty {v: val_typevar} 
{v1 v2: vty} (Heq: v1 = v2) (x: domain (val v v1)) : domain (val v v2).
Proof.
  subst. apply x.
Defined.

(*First, try function case - quite nontrivial *)

(*TODO: move*)
Lemma ty_subst_fun_in: forall params args d (x: typevar),
  NoDup params ->
  In x params ->
  length params = length args ->
  exists ty, In (x, ty) (combine params args) /\ ty_subst_fun params args d x = ty.
Proof.
  intros. generalize dependent args. induction params; simpl; intros; auto.
  inversion H0.
  inversion H; subst. destruct args. inversion H1.
  simpl in H0. destruct H0; subst.
  - exists v. split. left; auto. destruct (typevar_eq_dec x x); auto. contradiction.
  - inversion H1. specialize (IHparams H5 H0 args H3). destruct IHparams as [ty [Hin Hty]].
    exists ty. split. right; auto. destruct (typevar_eq_dec x a); auto.
    subst. contradiction.
Qed. 

Lemma ty_subst_fun_notin: forall params args d (x: typevar),
  ~In x params ->
  ty_subst_fun params args d x = d.
Proof.
  intros. revert args. induction params; simpl; intros; auto.
  destruct args; auto. destruct (typevar_eq_dec x a); auto; subst.
  exfalso. apply H. left; auto. apply IHparams. intro C. apply H. right; auto.
Qed.

Lemma combine_map2: forall {A B C: Type} (l1 : list A) (l2: list B) (f: B -> C),
  combine l1 (map f l2) = map (fun x => (fst x, f (snd x))) (combine l1 l2).
Proof.
  intros. revert l2. induction l1; simpl; intros; auto.
  destruct l2; simpl in *; auto.
  rewrite IHl1. reflexivity.
Qed.

(*A crucial result for the function arguments:
  Suppose we have a function f<alpha>(tau) : t, where alpha and tau are vectors
  In a well-typed function application f<mu>(ts), ts_i has type sigma(tau_i), where
  sigma maps alpha_i -> mu_i. Thus, [[ts_i]]_v has type [[v(sigma(tau_i))]].

  When dealing with valuations, we apply [[f<v(mu)>]] to arguments [[ts_i]]_v,
  each of which has must have type [[sigma'(tau_i)]], 
  where sigma maps alpha_i -> v(mu_i)

  Thus, we need to show that v(sigma(tau)) = sigma'(tau_i), which we do in the
  following lemma.

  TODO: do we need this for interp as well? Why didn't we need it there? Did we
  assume the wrong types for the arguments?

*)
Lemma funsym_subst_eq: forall (params: list typevar) (args: list vty) (v: typevar -> sort) (ty: vty),
  NoDup params ->
  length params = length args ->
  v_subst v (ty_subst params args ty) =
  ty_subst_s params (map (v_subst v) args) ty.
Proof.
  intros. unfold ty_subst_s. unfold ty_subst.
  apply sort_inj. unfold v_subst; simpl.
  induction ty; simpl; auto.
  - destruct (in_dec typevar_eq_dec v0 params).
     + assert (Hin:=i). 
       apply (ty_subst_fun_in params args vty_int v0 H) in i; auto.
       destruct i as [ty [Hinty Hty]]. rewrite !Hty.
       apply (ty_subst_fun_in params (sorts_to_tys
       (map
          (fun t : vty =>
           exist (fun t0 : vty => is_sort t0) (v_subst_aux (fun x : typevar => v x) t) (v_subst_aux_sort v t))
          args)) vty_int v0 H) in Hin.
        destruct Hin as [ty' [Hinty' Hty']]; simpl in *.
        unfold sort. (*annoying type equality thing*) rewrite Hty'.
        2 : {
          unfold sorts_to_tys. rewrite !map_length; auto.
        }
        unfold sorts_to_tys in Hinty'.
        rewrite map_map, combine_map2, in_map_iff in Hinty'.
        destruct Hinty' as [[v1 ty2] [Htup Hinty2]].
        simpl in Htup. inversion Htup.
        assert (ty = ty2). {
          eapply combine_NoDup_l. apply H. apply Hinty. subst; auto. 
        }
        subst. auto.
    + rewrite !ty_subst_fun_notin by assumption. auto.
  - f_equal. apply list_eq_ext'; rewrite !map_length; auto.
    intros n d Hn. rewrite !map_nth_inbound with (d2:=vty_int); auto.
    2: rewrite map_length; auto. rewrite Forall_forall in H1. apply H1.
    apply nth_In. auto.
Qed.

(*Axiom typecheck_dec: forall s t,
  (exists x, term_has_type s t x) ->
  { x | term_has_type s t x}.*)

Lemma ty_fun_ind_ret {f vs ts ty} (H: term_has_type sigma (Tfun f vs ts) ty):
  ty = ty_subst (s_params f) vs (s_ret f).
Proof.
  inversion H; auto.
Qed.

(*TODO: move*)
Lemma s_params_nodup: forall (f: funsym),
  NoDup (s_params f).
Proof.
  intros [f]; simpl. eapply reflect_iff. apply nodup_NoDup. apply s_params_nodup.
Qed.

Lemma p_params_nodup: forall (p: predsym),
  NoDup (p_params p).
Proof.
  intros [p]; simpl. eapply reflect_iff. apply nodup_NoDup. apply p_params_nodup.
Qed.

(*We use the above to get the arg list (tentatively)*)
Definition get_arg_list (v: val_typevar)
  (f: funsym) (vs: list vty) (ts: list term) 
  (reps: forall (t: term) (ty: vty),
    term_has_type sigma t ty ->
    domain (val v ty))
  (Hty: exists x, term_has_type sigma (Tfun f vs ts) x) : 
  arg_list domain
    (funsym_sigma_args f
      (map (v_subst (v_typevar v)) vs)).
Proof.
  (*assume we have decidable typechecking - no axioms yet*)
  assert ({x: vty | term_has_type sigma (Tfun f vs ts) x}) by (apply typecheck_dec; assumption).
  destruct H as [vty Hty'].
  apply fun_ty_inversion in Hty'. repeat match goal with | H: ?P /\ ?Q |- _ => destruct H end.
  clear H; clear H0; clear H4.
  unfold funsym_sigma_args.
  generalize dependent (s_args f). clear Hty. induction ts; simpl; intros.
  - assert (l = nil). apply length_zero_iff_nil. rewrite H1; reflexivity.
    rewrite H. simpl. apply HL_nil.
  - destruct l as [|a1 atl] eqn : Hargs.
    + inversion H1.
    + simpl in H1. simpl in H3. assert (A:=H3).
      apply Forall_inv in H3. apply Forall_inv_tail in A. simpl.
      apply HL_cons.
      * specialize (reps a _ H3); simpl in reps. 
        rewrite <- funsym_subst_eq; auto. apply s_params_nodup.
      * apply IHts; auto.
Defined.

Require Import Coq.Logic.Eqdep_dec.
Set Bullet Behavior "Strict Subproofs".

Lemma nat_eq_refl {n m: nat} (H1 H2: n = m) : H1 = H2.
Proof.
  destruct H1. apply UIP_dec. apply Nat.eq_dec.
Qed.

(*If the reps are equal only for the terms in the list,
  then the arg_lists are equal, and they are irrelevant
  in the choice of typing proof*)
Lemma get_arg_list_eq (v: val_typevar)
(f: funsym) (vs: list vty) (ts: list term) 
(reps1 reps2: forall (t: term) (ty: vty),
  term_has_type sigma t ty ->
  domain (val v ty))
(Hreps: Forall
(fun tm : term =>
 forall (ty : vty) (Hty1 Hty2: term_has_type sigma tm ty),
 reps1 tm ty Hty1 = reps2 tm ty Hty2) ts)
(Hty1 Hty2: exists x, term_has_type sigma (Tfun f vs ts) x) :
get_arg_list v f vs ts reps1 Hty1 =
get_arg_list v f vs ts reps2 Hty2.
Proof.
  unfold get_arg_list. simpl.
  destruct (typecheck_dec sigma (Tfun f vs ts) Hty1).
  destruct (typecheck_dec sigma (Tfun f vs ts) Hty2).
  assert (x = x0) by
    apply (term_has_type_unique _ _ _ _ t t0).
  subst.
  destruct (fun_ty_inversion sigma f vs ts x0 t).
  destruct (fun_ty_inversion sigma f vs ts x0 t0).
  destruct a as [Hallval1 [Hlents1 [Hlenvs1 [Hallty1 Hx01]]]].
  destruct a0 as [Hallval2 [Hlents2 [Hlenvs2 [Hallty2 Hx02]]]].
  simpl. subst.
  unfold funsym_sigma_args.
  generalize dependent (s_args f).
  clear Hty1 Hty2 t0 t. 
  induction ts; simpl; intros. 
  - f_equal. f_equal. f_equal. apply nat_eq_refl.
  - destruct l.
    + inversion Hlents2.
    + simpl in Hlenvs2. f_equal. 2: apply IHts; inversion Hreps; auto.
      assert (Hlenvs1 = Hlenvs2) by apply nat_eq_refl.
      rewrite H. f_equal.
      inversion Hreps; auto.
Qed.

(*
Lemma get_arg_list_irrel (v: val_typevar)
(f: funsym) (vs: list vty) (ts: list term) 
(reps: forall (t: term) (ty: vty),
  term_has_type sigma t ty ->
  domain (val v ty))
(Hreps: Forall
(fun tm : term =>
 forall (ty : vty)
   (Hty1 Hty2 : term_has_type sigma tm ty),
 reps tm ty Hty1 = reps tm ty Hty2) ts)
(Hty1 Hty2: exists x, term_has_type sigma (Tfun f vs ts) x) :
get_arg_list v f vs ts reps Hty1 =
get_arg_list v f vs ts reps Hty2.
Proof.
  apply get_arg_list_eq; auto.
Qed.*)

 
(*Also need a version for preds (TODO: can we reduce duplication?)*)
Definition get_arg_list_pred (v: val_typevar)
  (p: predsym) (vs: list vty) (ts: list term) 
  (reps: forall (t: term) (ty: vty),
    term_has_type sigma t ty ->
    domain (val v ty))
  (Hval: valid_formula sigma (Fpred p vs ts)) :
  arg_list domain
    (predsym_sigma_args p
      (map (v_subst (v_typevar v)) vs)).
Proof.
  apply pred_ty_inversion in Hval.
  repeat match goal with | H: ?P /\ ?Q |- _ => destruct H end.
  clear H; clear H0.
  unfold predsym_sigma_args.
  generalize dependent (p_args p). induction ts; simpl; intros.
  - assert (l = nil). apply length_zero_iff_nil. rewrite H1; reflexivity.
    rewrite H. simpl. apply HL_nil.
  - destruct l as [|a1 atl] eqn : Hargs.
    + inversion H1.
    + simpl in H1. simpl in H3. assert (A:=H3).
      apply Forall_inv in H3. apply Forall_inv_tail in A. simpl.
      apply HL_cons.
      * specialize (reps a _ H3); simpl in reps. 
        rewrite <- funsym_subst_eq; auto. apply p_params_nodup.
      * apply IHts; auto.
Defined.

Lemma get_arg_list_pred_eq (v: val_typevar)
(p: predsym) (vs: list vty) (ts: list term) 
(reps1 reps2: forall (t: term) (ty: vty),
  term_has_type sigma t ty ->
  domain (val v ty))
(Hreps: Forall
(fun tm : term =>
 forall (ty : vty) (Hty1 Hty2: term_has_type sigma tm ty),
 reps1 tm ty Hty1 = reps2 tm ty Hty2) ts)
 (Hval1 Hval2: valid_formula sigma (Fpred p vs ts)) :
get_arg_list_pred v p vs ts reps1 Hval1 =
get_arg_list_pred v p vs ts reps2 Hval2.
Proof.
  unfold get_arg_list_pred. simpl.
  destruct (pred_ty_inversion sigma p vs ts Hval1).
  destruct (pred_ty_inversion sigma p vs ts Hval2).
  destruct a as [Hallval1 [Hlents1 [Hlenvs1 Hallty1]]].
  destruct a0 as [Hallval2 [Hlents2 [Hlenvs2 Hallty2]]].
  simpl. 
  unfold predsym_sigma_args.
  generalize dependent (p_args p).
  clear Hval1 Hval2. 
  induction ts; simpl; intros. 
  - f_equal. f_equal. f_equal. apply nat_eq_refl. 
  - destruct l.
    + inversion Hlents2.
    + simpl in Hlenvs2. f_equal. 2: apply IHts; inversion Hreps; auto.
      assert (Hlenvs1 = Hlenvs2) by apply nat_eq_refl.
      rewrite H. f_equal.
      inversion Hreps; auto.
Qed.
(*
Lemma get_arg_list_pred_irrel (v: val_typevar)
(p: predsym) (vs: list vty) (ts: list term) 
(reps: forall (t: term) (ty: vty),
  term_has_type sigma t ty ->
  domain (val v ty))
(Hreps: Forall
(fun tm : term =>
 forall (ty : vty)
   (Hty1 Hty2 : term_has_type sigma tm ty),
 reps tm ty Hty1 = reps tm ty Hty2) ts)
(Hval1 Hval2: valid_formula sigma (Fpred p vs ts)) :
get_arg_list_pred v p vs ts reps Hval1 =
get_arg_list_pred v p vs ts reps Hval2.
Proof.
  apply get_arg_list_pred_eq; auto.
Qed.
  unfold get_arg_list_pred. simpl.
  destruct (pred_ty_inversion sigma p vs ts Hval1).
  destruct (pred_ty_inversion sigma p vs ts Hval2).
  destruct a as [Hallval1 [Hlents1 [Hlenvs1 Hallty1]]].
  destruct a0 as [Hallval2 [Hlents2 [Hlenvs2 Hallty2]]].
  simpl. 
  unfold predsym_sigma_args.
  generalize dependent (p_args p).
  clear Hval1 Hval2. 
  induction ts; simpl; intros. 
  - f_equal. f_equal. f_equal. apply nat_eq_refl. 
  - destruct l.
    + inversion Hlents2.
    + simpl in Hlenvs2. f_equal. 2: apply IHts; inversion Hreps; auto.
      assert (Hlenvs1 = Hlenvs2) by apply nat_eq_refl.
      rewrite H. f_equal.
      inversion Hreps; auto.
Qed.*)

(*TODO: move*)
Lemma tfun_params_length {s f vs ts ty}:
  term_has_type s (Tfun f vs ts) ty ->
  length (s_params f) = length vs.
Proof.
  intros. inversion H; subst. rewrite H9. reflexivity.
Qed.

Lemma fpred_params_length {s p vs ts}:
  valid_formula s (Fpred p vs ts) ->
  length (p_params p) = length vs.
Proof.
  intros. inversion H; subst. auto.
Qed.

Lemma has_type_eq {s t t' ty} (Heq: t = t'):
  term_has_type s t ty ->
  term_has_type s t' ty.
Proof.
  subst. auto.
Qed.

Lemma valid_formula_eq {s f f'} (Heq: f = f'):
  valid_formula s f ->
  valid_formula s f'.
Proof.
  subst; auto.
Qed.

Lemma ty_constint_inv {s z ty} (H: term_has_type s (Tconst (ConstInt z)) ty) :
  ty = vty_int.
Proof.
  inversion H; auto.
Qed.

Lemma ty_constreal_inv {s r ty} (H: term_has_type s (Tconst (ConstReal r)) ty) :
ty = vty_real.
Proof.
inversion H; auto.
Qed.

Lemma ty_var_inv {s x ty} (H: term_has_type s (Tvar x) ty):
ty = snd x .
Proof.
  inversion H; auto.
Qed.

Lemma ty_let_inv {s t1 x t2 ty} (H: term_has_type s (Tlet t1 x t2) ty):
term_has_type s t1 (snd x) /\ term_has_type s t2 ty.
Proof.
  inversion H; auto.
Qed.

Lemma ty_if_inv {s f t1 t2 ty} (H: term_has_type s (Tif f t1 t2) ty):
term_has_type s t1 ty /\
term_has_type s t2 ty /\
valid_formula s f.
Proof.
  inversion H; auto.
Qed.

Lemma ty_match_inv {s t ty1 ty2 xs} (H: term_has_type s (Tmatch t ty1 xs) ty2):
  term_has_type s t ty1 /\
  Forall (fun x : pattern * term => term_has_type s (snd x) ty2) xs.
Proof.
  inversion H; subst; split; auto.
  rewrite Forall_forall. auto.
Qed.

Lemma ty_eps_inv {s f x ty'} (H: term_has_type s (Teps f x) ty'):
  valid_formula s f /\ ty' = snd x.
Proof.
  inversion H; subst; auto.
Qed.

Lemma valid_not_inj {s f} (H: valid_formula s (Fnot f)):
  valid_formula s f.
Proof.
  inversion H; auto.
Qed.

Lemma valid_let_inj {s t x f} (H: valid_formula s (Flet t x f)):
term_has_type s t (snd x) /\
valid_formula s f.
Proof.
  inversion H; auto.
Qed.

Lemma valid_binop_inj {s b f1 f2} (H: valid_formula s (Fbinop b f1 f2)):
valid_formula s f1 /\
valid_formula s f2.
Proof.
  inversion H; auto.
Qed.

Lemma valid_if_inj {s f1 f2 f3} (H: valid_formula s (Fif f1 f2 f3)):
valid_formula s f1 /\
valid_formula s f2 /\
valid_formula s f3.
Proof.
  inversion H; auto.
Qed.

Lemma valid_quant_inj {s q x f} (H: valid_formula s (Fquant q x f)):
  valid_formula s f.
Proof.
  inversion H; auto.
Qed.

Lemma valid_match_inv {s t ty1 xs} (H: valid_formula s (Fmatch t ty1 xs)):
  term_has_type s t ty1 /\
  Forall (fun x : pattern * formula => valid_formula s (snd x)) xs.
Proof.
  inversion H; subst; split; auto.
Qed.

Lemma valid_eq_inj {s ty t1 t2} (H: valid_formula s (Feq ty t1 t2)):
  term_has_type s t1 ty /\ term_has_type s t2 ty.
Proof.
  inversion H; auto.
Qed.

(*Dealing with options for patterns*)
(*Since patterns can return "error", we represent this as a term option.
  We will show that in an exhaustive pattern match, we can never reach the
  error state. But we want to reason about types of term options*)
Definition term_option_type (s: sig) (o: option term) (ty: vty) :=
  match o with
  | None => True
  | Some t => term_has_type s t ty
  end.

(*A not-as-typechecked version of [substi]*)
(*Definition add_val (v: valuation gamma_valid i) (x: vsymbol) (vty: vty)
Print valuation.

Check substi.
Print substi.
Print Semantics.substi.

Print valuation.*)

Lemma existsb_exists': forall {A: Type} (f: A -> bool) (l: list A),
  existsb f l = true -> {x | In x l /\ f x = true}.
Proof.
  intros. induction l; simpl in H. inversion H.
  destruct (f a) eqn : Hf.
  - exists a. split; auto. left; auto.
  - specialize (IHl H). destruct IHl as [x [Hinx Hx]].
    + apply (exist _ x). split; auto. right; auto.
Qed.

Definition find_ts_in_mut (ts: typesym) (m: mut_adt) : option alg_datatype :=
  find (fun a => typesym_eq_dec ts (adt_name a)) (typs m).

Lemma find_ts_in_mut_some: forall ts m a,
  find_ts_in_mut ts m = Some a ->
  adt_in_mut a m /\ adt_name a = ts.
Proof.
  intros ts m a Hf. apply find_some in Hf.
  destruct Hf as [Hin Heq].
  split; auto.
  simpl_sumbool.
Qed.

Set Bullet Behavior "Strict Subproofs".

Lemma find_some_nodup: forall {A: Type} (f: A -> bool) (l: list A) (x: A),
  (forall x y, In x l -> In y l -> f x -> f y -> x = y) ->  
  (find f l = Some x <-> In x l /\ f x = true).
Proof.
  intros. induction l; intros; simpl; split; intros.
  - inversion H0.
  - destruct H0. destruct H0.
  - destruct (f a) eqn : Hfa.
    + inversion H0; subst. split; auto.
    + apply IHl in H0. 
      * destruct H0. split; auto.
      * intros; apply H; auto; right; auto.
  - destruct H0. destruct H0; subst. rewrite H1. reflexivity.
    destruct (f a) eqn : Hfa.
    + f_equal. apply H; auto. left; auto. right; auto.
    + apply IHl; [|split; auto].
      intros; apply H; auto; right; auto.
Qed.

Lemma NoDup_map_in: forall {A B: Type} {f: A -> B} {l: list A} {x1 x2: A},
  NoDup (map f l) ->
  In x1 l -> In x2 l ->
  f x1 = f x2 ->
  x1 = x2.
Proof.
  intros. induction l; simpl; intros; auto.
  inversion H0.
  simpl in H0; simpl in H1. simpl in H; inversion H; subst.
  destruct H0; subst; destruct H1; subst.
  - reflexivity.
  - rewrite H2 in H5. exfalso. apply H5. rewrite in_map_iff. 
    exists x2; split; auto.
  - rewrite <- H2 in H5. exfalso. apply H5. rewrite in_map_iff.
    exists x1; split; auto.
  - apply IHl; auto.
Qed.

Lemma find_ts_in_mut_iff: forall ts m a,
  NoDup (map adt_name (typs m)) ->
  (find_ts_in_mut ts m = Some a) <-> (adt_in_mut a m /\ adt_name a = ts).
Proof.
  intros. eapply iff_trans. apply find_some_nodup.
  - intros. repeat simpl_sumbool.
    apply (NoDup_map_in H); auto.
  - simpl. unfold adt_in_mut. apply and_iff_compat_l.
    split; intros; simpl_sumbool.
Qed.

Definition find_ts_in_ctx (ts: typesym) : option (mut_adt * alg_datatype) :=
  fold_right (fun m acc => 
    match (find_ts_in_mut ts m) with
    | Some a => Some (m, a)
    | None => acc
    end) None (mut_of_context gamma).

(*TODO: move?*)
Lemma no_adt_name_dups:
  NoDup (map adt_name (concat (map typs (mut_of_context gamma)))).
Proof.
  assert (forall g, 
    (map adt_name (concat (map typs (mut_of_context g)))) =
  typesyms_of_context g). {
    induction g; unfold typesyms_of_context in *; simpl; auto.
    unfold datatypes_of_context in *.
    destruct a; simpl; auto.
    rewrite !map_app, IHg. f_equal.
    rewrite map_map.
    apply map_ext. intros a. destruct a; reflexivity.
  }
  rewrite H. apply gamma_valid.
Qed.

(*The real spec we want: (TODO: maybe move all this)*)
Lemma find_ts_in_ctx_iff: forall ts m a,
  (find_ts_in_ctx ts = Some (m, a) <-> mut_in_ctx m gamma /\
    adt_in_mut a m /\ adt_name a = ts).
Proof.
  intros. unfold find_ts_in_ctx. rewrite mut_in_ctx_eq.
  assert (forall m, In m (mut_of_context gamma) ->
    NoDup (map adt_name (typs m))). {
      intros m'. rewrite <- mut_in_ctx_eq.
      eapply adts_names_nodups. apply gamma_valid.
    }
  assert (Hnodup:=no_adt_name_dups).
  induction (mut_of_context gamma); simpl; intros; split; intros; auto.
  - inversion H0.
  - destruct H0 as [[] _].
  - destruct (find_ts_in_mut ts a0) eqn : Hmut.
    + inversion H0; subst. apply find_ts_in_mut_iff in Hmut. destruct Hmut.
      repeat split; auto.
      apply H. left; auto.
    + apply IHl in H0. destruct H0 as [Hin [Ha Hn]]. repeat split; auto.
      intros. apply H. right; auto.
      simpl in Hnodup. rewrite map_app in Hnodup. apply NoDup_app in Hnodup.
      apply Hnodup.
  - destruct H0 as [[Ham | Hinm] [Ha Hn]]; subst.
    + assert (find_ts_in_mut (adt_name a) m = Some a). {
        apply find_ts_in_mut_iff. apply H. left; auto. split; auto.
      }
      rewrite H0. reflexivity.
    + simpl in Hnodup. rewrite map_app in Hnodup.
      rewrite NoDup_app_iff in Hnodup.
      destruct (find_ts_in_mut (adt_name a) a0 ) eqn : Hf.
      * apply find_ts_in_mut_iff in Hf. 2: apply H; simpl; auto.
        destruct Hf.
        destruct Hnodup as [Hn1 [Hn2 [Hi1 Hi2]]].
        exfalso. apply (Hi1 (adt_name a1)). rewrite in_map_iff.
        exists a1. split; auto. rewrite H1.
        rewrite in_map_iff. exists a. split; auto.
        rewrite in_concat. exists (typs m). split; auto.
        rewrite in_map_iff. exists m; split; auto.
      * apply IHl; auto.
        intros. apply H. right; auto.
        apply Hnodup.
Qed.

Definition vty_is_cons (v: vty) :=
  match v with
  | vty_cons _ _ => true
  | _ => false
  end.

Lemma null_nil: forall {A: Type} (l: list A),
  null l <-> l = nil.
Proof.
  intros; destruct l; split; intros; auto; inversion H.
Qed.

Lemma is_sort_cons: forall (ts: typesym) (l: list vty),
  is_sort (vty_cons ts l) ->
  forall x, In x l -> is_sort x.
Proof.
  intros. unfold is_sort in *. simpl in H.
  rewrite null_nil in *.
  eapply big_union_nil in H. apply H. assumption.
Qed.

Definition is_sort_cons_sorts (ts: typesym) (l: list vty) 
  (Hall: forall x, In x l -> is_sort x):
  {s: list sort | sorts_to_tys s = l}.
Proof.
  induction l.
  - apply (exist _ nil). reflexivity.
  - simpl in Hall.
    assert (is_sort a). apply Hall. left; auto.
    assert (forall x : vty, In x l -> is_sort x). {
      intros. apply Hall; right; auto.
    }
    specialize (IHl H0). destruct IHl as [tl Htl].
    apply (exist _ ((exist _ a H) :: tl)).
    simpl. rewrite Htl. reflexivity.
Qed.
(*
Definition sort_cons (t: typesym) (l: list vty) (Hsrt: is_sort (vty_cons t l)) :
  { s: list sort | 
    vty_cons t  = vty_cons (fst t) (sorts_to_tys (snd t))}
| _ => unit
end.
Proof.
  destruct s. simpl. destruct x; try solve[apply tt].
  pose proof (is_sort_cons_sorts t l (is_sort_cons t l i0)) as ls.
  destruct ls as [s Hs].
  apply (exist _ (t, s)). simpl. rewrite Hs. reflexivity.
Qed.*)

Definition is_sort_adt (s: sort) : 
  option (mut_adt * alg_datatype * typesym * list sort).
Proof.
  destruct s.
  destruct x.
  - exact None.
  - exact None.
  - exact None.
  - destruct (find_ts_in_ctx t);[|exact None].
    exact (Some (fst p, snd p, t, 
      proj1_sig (is_sort_cons_sorts t l (is_sort_cons t l i)))).
Defined.

(*TODO: do we need other direction?*)
Lemma is_sort_adt_spec: forall s m a ts srts,
  is_sort_adt s = Some (m, a, ts, srts) ->
  s = typesym_to_sort (adt_name a) srts /\
  adt_in_mut a m /\ mut_in_ctx m gamma /\ ts = adt_name a.
Proof.
  intros. unfold is_sort_adt in H.
  destruct s. destruct x; try solve[inversion H].
  destruct (find_ts_in_ctx t) eqn : Hf.
  - inversion H; subst. destruct p as [m a]. simpl.
    apply find_ts_in_ctx_iff in Hf. destruct Hf as [Hmg [Ham Hat]]; 
    repeat split; auto; subst.
    apply sort_inj. simpl. f_equal. clear H. 
    generalize dependent (is_sort_cons (adt_name a) l i).
    intros H.
    destruct (is_sort_cons_sorts (adt_name a) l H). simpl.
    rewrite <- e; reflexivity.
  - inversion H.
Qed.

(*Want to prove: suppose that type is valid and we have valuation, 
  then val v ty is valid*)
Lemma val_valid: forall (v: val_typevar) (ty: vty),
  valid_type sigma ty ->
  valid_type sigma (val v ty).
Proof.
  intros. unfold val. simpl.
  apply valid_type_v_subst; auto.
  intros x.
  destruct v; simpl. apply v_typevar_val.
Qed. 

(*We need info about lengths and validity of the srts list*)
Lemma adt_srts_valid: forall {v: val_typevar}  {ty m a ts srts},
  is_sort_adt (val v ty) = Some (m, a, ts, srts) ->
  valid_type sigma ty ->
  valid_type sigma (typesym_to_sort (adt_name a) srts).
Proof.
  intros v ty m a ts srts H.
  apply is_sort_adt_spec in H.
  destruct H as [Hts [a_in [m_in _]]].
  intros Hval.
  rewrite <- Hts. apply val_valid. assumption.
Qed.

(*We need to know something about the lengths*)
Lemma adt_srts_length_eq: forall {v: val_typevar} {ty m a ts srts},
  is_sort_adt (val v ty) = Some (m, a, ts, srts) ->
  valid_type sigma ty ->
  length srts = length (m_params m).
Proof.
  intros v ty m a ts srts H Hval.
  pose proof (Hval':=adt_srts_valid H Hval).
  apply is_sort_adt_spec in H.
  destruct H as [Hts [a_in [m_in _]]].
  unfold typesym_to_sort in Hval'. 
  simpl in Hval'; inversion Hval'; subst.
  rewrite map_length in H3. rewrite H3.
  f_equal. apply (adt_args gamma_valid). split; auto.
Qed.

(*Assume that all ADTs are uniform for now*)
Variable all_unif: forall m,
  mut_in_ctx m gamma ->
  uniform m.

Lemma val_sort_eq: forall (v: val_typevar) (s: sort),
  s = val v s.
Proof.
  intros. apply subst_sort_eq.
Qed.

(*Need to know that all sorts are valid types*)
Lemma adts_srts_valid: forall {v : val_typevar} {ty m a ts srts c},
  is_sort_adt (val v ty) = Some (m, a, ts, srts) ->
  valid_type sigma ty ->
  constr_in_adt c a ->
  Forall (valid_type sigma) (sorts_to_tys (funsym_sigma_args c srts)).
Proof.
  intros v ty m a ts srts c H Hval c_in.
  pose proof (Hval':=adt_srts_valid H Hval).
  pose proof (Hlen:=adt_srts_length_eq H Hval).
  apply is_sort_adt_spec in H.
  destruct H as [Hts [a_in [m_in _]]].
  rewrite Forall_forall; intros t.
  unfold sorts_to_tys. rewrite in_map_iff; intros [srt [Hsrt Hinsrt]]; subst.
  unfold funsym_sigma_args in Hinsrt.
  unfold ty_subst_list_s in Hinsrt.
  rewrite in_map_iff in Hinsrt.
  destruct Hinsrt as [t [Ht Hint]]; subst.
  unfold ty_subst_s. apply valid_type_v_subst.
  - apply (constr_ret_valid gamma_valid m_in a_in c_in). apply Hint.
  - intros. apply make_val_valid_type.
    + rewrite Hlen. f_equal.
      apply (adt_constr_params gamma_valid m_in a_in c_in).
    + intros s Hsin. simpl in Hval'. inversion Hval'; subst.
      apply H4. rewrite in_map_iff. exists s. split; auto.
Qed.

(*Pattern matches are quite complicated. Rather than compiling down
  to elementary let statements, as in the paper, we instead build up
  the entire valuation (consisting of pairs of vsymbols and domain
  elements for an appropriate type). Doing this is conceptually simple,
  but very difficult in practice due to depenedent type obligations.
  
  The interesting case is the case when we match against a constructor.
  In this case, we determine if the type is an instance of and ADT, 
  and if so, we use [find_constr_rep] (after some casting) to get 
  the constructor and arguments (arg_list) that comprise this instance.
  Then, we check if the constructor equals the one in the pattern match,
  and if so, we iterate through the arg_list and build up the valuation
  entries recursively, returning None if we ever find a non-matching pattern.
  
  We need many of the above lemmas to handle the preconditions for
  [find_constr_rep] and casting.
  *)

Fixpoint match_val_single (v: val_typevar) (ty: vty)
  (Hval: valid_type sigma ty)
  (d: domain (val v ty))
  (p: pattern) {struct p} : 
  (*For a pair (x, d), we just need that there is SOME type t such that
    d has type [domain (val v t)], but we don't care what t is*)
  option (list (vsymbol * {t: vty & domain (val v t) })) :=
  match p with
  | Pvar x =>
    (*TODO: really do want to show that None is never reached*)
    if (vty_eq_dec (snd x) ty) then
    Some [(x, (existT _ ty d))] else None
  | Pwild => Some nil
  | Por p1 p2 => match (match_val_single v ty Hval d p1) with
                  | Some v1 => Some v1
                  | None => match_val_single v ty Hval d p2
                  end
  | Pbind p1 x =>
    (*Binding adds an additional binding at the end for the whole
      pattern*)
    match (match_val_single v ty Hval d p1) with
    | None => None
    | Some l => if (vty_eq_dec (snd x) ty) then 
       Some ((x, (existT _ ty d)) :: l) else None
    end
  | Pconstr f vs ps =>
    (*First, check to see if this type is an ADT*)
    match (is_sort_adt (val v ty)) as o return
      (is_sort_adt (val v ty)) = o -> 
      option (list (vsymbol * {t: vty & domain (val v t) })) 
    with
    | Some (m, a, ts, srts) => fun Hisadt =>
      (*If it is, we get information about a, m, srts 
        from [is_sort_adt_spec]*)
      match (is_sort_adt_spec _ _ _ _ _ Hisadt) with
      | conj Hseq (conj a_in (conj m_in Htseq)) =>
        (*We cast to get an ADT, now that we know that this actually is
          an ADT*)
        let adt : adt_rep m srts (dom_aux pd) a a_in :=
          scast (adts pd m srts a a_in) (dom_cast _ Hseq d) in
       
        (*Need a lemma about lengths for [find_constr_rep]*)
        let lengths_eq : length srts = length (m_params m) := 
          adt_srts_length_eq Hisadt Hval in

        (*The key part: get the constructor c and arg_list a
          such that d = [[c(a)]]*)
        let Hrep := find_constr_rep gamma_valid m m_in srts lengths_eq 
          (dom_aux pd) a a_in (adts pd m srts) 
          (all_unif m m_in) adt in

        (*The different parts of Hrep we need*)
        let c : funsym := projT1 Hrep in
        let c_in : constr_in_adt c a :=
          fst (proj1_sig (projT2 Hrep)) in
        let args : arg_list domain (funsym_sigma_args c srts) := 
          snd (proj1_sig (projT2 Hrep)) in
        (*If the constructors match, check all arguments,
          otherwise, gives None*)
          if funsym_eq_dec c f then
            (*Idea: iterate over arg list, build up valuation, return None
            if we every see None*)
            (*This function is actually quite simple, we just need a bit
              of dependent pattern matching for the [arg_list]*)
            (fix iter_arg_list (tys: list sort) (a: arg_list domain tys)
            (Hall: Forall (valid_type sigma) (sorts_to_tys tys)) 
              (pats: list pattern) {struct pats} :
            option (list (vsymbol * {t: vty & domain (val v t) })) :=
            match tys as t' return arg_list domain t' ->
              Forall (valid_type sigma) (sorts_to_tys t') -> 
              option (list (vsymbol * {t: vty & domain (val v t) }))
            with
            | nil => fun _ _ =>
              (*matches only if lengths are the same*)
              match pats with
              | nil => Some nil
              | _ :: _ => None
              end
            | ty :: tl => fun a' Hall' =>
              match pats with
              | nil => None (*lengths have to be the same*)
              | phd :: ptl =>
                (*We try to evaluate the head against the first pattern.
                  If this succeeds we combine with tail, if either fails
                  we give None*)
                (*Since ty is a sort, val v ty = ty, therefore we can cast*)
                match (match_val_single v ty (Forall_inv Hall') 
                  (dom_cast _ (val_sort_eq _ ty) (hlist_hd a')) phd) with
                | None => None
                | Some l =>
                  match iter_arg_list tl (hlist_tl a') (Forall_inv_tail Hall') ptl with
                  | None => None
                  | Some l' => Some (l ++ l')
                  end
                end
              end
            end a Hall)  _ args (adts_srts_valid Hisadt Hval c_in) ps
          else None
      end 
    (*If not an ADT, does not match*)
    | None => fun _ => None
    end eq_refl
  end.

Lemma match_val_single_typs (v: val_typevar) (ty: vty)
(Hval: valid_type sigma ty)
(d: domain (val v ty))
(p: pattern) l:
match_val_single v ty Hval d p = Some l ->
forall x t, In (x, t) l -> projT1 t = (snd x).
Proof.
  revert Hval d l. generalize dependent ty.
  induction p.
  - simpl; intros.
    destruct (vty_eq_dec (snd v0) ty); subst.
    inversion H; subst. simpl in H0.
    destruct H0; [|destruct H0].
    inversion H0; subst. simpl.
    reflexivity. inversion H.
  - intros ty Hval d.
    (*The hard case: need lots of generalization for dependent types
    and need nested induction*) 
    unfold match_val_single; fold match_val_single.
    generalize dependent (is_sort_adt_spec (val v ty)).
    generalize dependent ((@adt_srts_length_eq v ty)).
    generalize dependent (@adts_srts_valid v ty).
    destruct (is_sort_adt (val v ty)) eqn : Hisadt;
    [|intros _ _ _ ? Hc; inversion Hc].
    intros Hsrtsvalid Hsrtslen Hadtspec.
    destruct p as [[[m adt] ts] srts].
    destruct (Hadtspec m adt ts srts eq_refl) as 
      [Hvaleq [Hinmut [Hincts Htseq]]].
    destruct (funsym_eq_dec
    (projT1
      (find_constr_rep gamma_valid m Hincts srts
          (Hsrtslen m adt ts srts eq_refl Hval) (dom_aux pd) adt
          Hinmut (adts pd m srts) (all_unif m Hincts)
          (scast (adts pd m srts adt Hinmut)
            (dom_cast (dom_aux pd) Hvaleq d)))) f); 
            [|intros ? C; inversion C].
    (*Need nested induction: simplify first*)
    generalize dependent (find_constr_rep gamma_valid m Hincts srts
    (Hsrtslen m adt ts srts eq_refl Hval) 
    (dom_aux pd) adt Hinmut (adts pd m srts)
    (all_unif m Hincts)
    (scast (adts pd m srts adt Hinmut)
      (dom_cast (dom_aux pd) Hvaleq d))).
    intros constr. destruct constr as [f' Hf']. simpl. intros Hf; subst.
    generalize dependent ((Hsrtsvalid m adt (adt_name adt) srts f eq_refl Hval (fst (proj1_sig Hf')))).
    destruct Hf'. simpl. clear e.
    destruct x. simpl. generalize dependent a.
    generalize dependent ps.
    generalize dependent ((funsym_sigma_args f srts)).
    induction l; simpl; intros; auto. 
    + destruct ps. inversion H0; subst. inversion H1.
      inversion H0.
    + revert H0. destruct ps.
      intros Hc; inversion Hc.
      repeat match goal with 
      |- (match ?p with |Some l => ?x | None => ?y end) = ?z -> ?q =>
        let Hp := fresh "Hmatch" in 
        destruct p eqn: Hp end.
      all: intro C; inversion C.
      subst.
      apply in_app_or in H1. destruct H1.
      * inversion H; subst.
        apply H3 with(x:=x) (t:=t) in Hmatch; auto.
      * apply IHl with(x:=x) (t:=t) in Hmatch0; auto.
        inversion H; subst. auto.
  - simpl. intros. inversion H; subst. inversion H0.
  - simpl. intros.
    destruct (match_val_single v ty Hval d p1) eqn : Hm.
    + inversion H; subst.
      apply IHp1 with(x:=x)(t:=t) in Hm; auto.
    + apply IHp2 with(x:=x)(t:=t) in H; auto.
  - simpl. intros.
    destruct (match_val_single v ty Hval d p) eqn : Hm.
    + inversion H; subst.
      destruct (vty_eq_dec (snd v0) ty); subst.
      * inversion H. subst. simpl in H0. destruct H0.
        -- inversion H0; subst. reflexivity.
        -- apply IHp with(x:=x)(t:=t) in Hm; auto.
      * inversion H2.
    + inversion H.
Qed.

Lemma seq_map_map {A B: Type} (f: A -> B) (s: list A):
  seq.map f s = map f s.
Proof.
  reflexivity.
Qed.

  (*TODO: move*)
  (*
Lemma find_constr_rep_irrel (m: mut_adt) (m_in mut_in_ctx m gamma)
  (srts: list sort)
*)
(*TODO: move below prob*)
Lemma match_val_single_irrel (v: val_typevar) (ty: vty)
(Hval1 Hval2: valid_type sigma ty)
(d: domain (val v ty))
(p: pattern) :
  match_val_single v ty Hval1 d p =
  match_val_single v ty Hval2 d p.
Proof.
  revert Hval1 Hval2. revert d. generalize dependent ty.
  induction p; intros; auto.
  - (*The hard case: need lots of generalization for dependent types
      and need nested induction*) 
    unfold match_val_single; fold match_val_single.
    generalize dependent (is_sort_adt_spec (val v ty)).
    generalize dependent ((@adt_srts_length_eq v ty)).
    generalize dependent (@adts_srts_valid v ty).
    destruct (is_sort_adt (val v ty)) eqn : Hisadt; auto.
    intros Hsrtsvalid Hsrtslen Hadtspec.
    destruct p as [[[m adt] ts] srts].
    destruct (Hadtspec m adt ts srts eq_refl) as 
      [Hvaleq [Hinmut [Hincts Htseq]]].
    (*This part is actually easy: all nat equality proofs are equal*)
    assert (Hsrtslen m adt ts srts eq_refl Hval1 =
    Hsrtslen m adt ts srts eq_refl Hval2) by
      apply nat_eq_refl.
    rewrite H0.
    clear H0.
    destruct (funsym_eq_dec
    (projT1
       (find_constr_rep gamma_valid m Hincts srts
          (Hsrtslen m adt ts srts eq_refl Hval2) (dom_aux pd) adt
          Hinmut (adts pd m srts) (all_unif m Hincts)
          (scast (adts pd m srts adt Hinmut)
             (dom_cast (dom_aux pd) Hvaleq d)))) f); auto.
    (*Need nested induction: simplify first*)
    generalize dependent (find_constr_rep gamma_valid m Hincts srts
    (Hsrtslen m adt ts srts eq_refl Hval2) 
    (dom_aux pd) adt Hinmut (adts pd m srts)
    (all_unif m Hincts)
    (scast (adts pd m srts adt Hinmut)
       (dom_cast (dom_aux pd) Hvaleq d))).
    intros constr. destruct constr as [f' Hf']. simpl. intros Hf; subst.
    generalize dependent ((Hsrtsvalid m adt (adt_name adt) srts f eq_refl Hval1 (fst (proj1_sig Hf')))).
    generalize dependent ((Hsrtsvalid m adt (adt_name adt) srts f eq_refl Hval2 (fst (proj1_sig Hf')))).
    destruct Hf'. simpl. clear e.
    destruct x. simpl. generalize dependent a.
    generalize dependent ps.
    generalize dependent ((funsym_sigma_args f srts)).
    induction l; simpl; intros; auto.
    + destruct ps; auto.
    + inversion H; subst. reflexivity.
      (*Don't know why we need to expand map*)
      rewrite (H0 a (dom_cast (dom_aux pd) (val_sort_eq v a) (hlist_hd a0))
        _ ((@Forall_inv vty (valid_type sigma) (sort_to_ty a)
      ((fix map (s : list sort) : list vty :=
          match s return (list vty) with
          | nil => @nil vty
          | cons x0 s' => @cons vty (sort_to_ty x0) (map s')
          end) l) f0))).
      (*Now we can destruct and simplify*)
      destruct (match_val_single v a (@Forall_inv vty (valid_type sigma) (sort_to_ty a)
      ((fix map (s : list sort) : list vty :=
          match s return (list vty) with
          | nil => @nil vty
          | cons x0 s' => @cons vty (sort_to_ty x0) (map s')
          end) l) f0)
      (dom_cast (dom_aux pd) (val_sort_eq v a) (hlist_hd a0)) x) eqn : Hm; auto.
      match goal with 
      | |- match ?o1 with | Some x => ?a | None => ?b end =
        match ?o2 with | Some y => ?c | None => ?d end =>
        assert (Ho: o1 = o2);[|rewrite Ho; reflexivity] end.
      apply IHl. apply H1.
  - simpl. replace (match_val_single v ty Hval1 d p1) with
    (match_val_single v ty Hval2 d p1) by apply IHp1.
    destruct (match_val_single v ty Hval2 d p1); auto.
  - simpl. rewrite (IHp _ d Hval1 Hval2). reflexivity.
Qed.
  
Definition get_assoc_list {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (l: list (A * B)) (x: A) : option B :=
  fold_right (fun y acc => if eq_dec x (fst y) then Some (snd y) else acc) None l.

(*Look up each entry in the list, if the name or type doesn't
  match, default to existing val*)
(*Usefully, Coq can tell that this does not affect v_typevar*)
Definition extend_val_with_list (v: val_typevar) 
  (vv: val_vars pd v)
  (l: list (vsymbol * {t: vty & domain (val v t) })) :
  val_vars pd v.
intros x.
  destruct (get_assoc_list vsymbol_eq_dec l x).
  + destruct (vty_eq_dec (snd x) (projT1 s)).
    * rewrite e. exact (projT2 s).
    * exact (vv x).
  + exact (vv x).
Defined.
(*
Definition extend_val_eq v l ty:
  val (extend_val_with_list v l) ty = val v ty := eq_refl.

(*Compiling a pattern match is now easy*)
(*TODO: prove we never hit the default*)

Fixpoint match_rep {A: Set} (v: valuation gamma_valid i) (ty: vty)
  (Hval: valid_type sigma ty) (d: domain (val v ty))
  (ps: list (pattern * A)) : 
  option (pattern * A * valuation gamma_valid i) :=
  match ps with
  | (p, dat) :: ptl => 
    match (match_val_single v ty Hval d p) with
    | Some l => Some(p, dat, extend_val_with_list v l)
    | None => match_rep v ty Hval d ptl
    end
  | _ => None
  end.

Lemma match_rep_val_eq: forall {A: Set} {v ty p x newv d} 
  {ps: list (pattern * A)} (Hval: valid_type sigma ty) typ,  
  match_rep v ty Hval d ps = Some (p, x, newv) ->
  val newv typ = val v typ.
Proof.
  intros. induction ps; simpl in *.
  inversion H.
  destruct a. destruct (match_val_single v ty Hval d p0).
  inversion H; subst. reflexivity.
  apply IHps. apply H.
Qed.

Lemma match_rep_x_in: forall {A: Set} {v ty p x newv d} 
{ps: list (pattern * A)} (Hval: valid_type sigma ty),
  match_rep v ty Hval d ps = Some (p, x, newv) ->
  In x (map snd ps).
Proof.
  intros. induction ps; simpl in *. inversion H.
  destruct a. destruct (match_val_single v ty Hval d p0).
  inversion H; subst. left; auto. auto.
Qed.

Lemma match_rep_x_type: forall{v ty p x newv d} 
{ps: list (pattern * term)} (Hval: valid_type sigma ty) typ
  (Hall: (forall x, In x ps -> term_has_type sigma (snd x) typ)),
  match_rep v ty Hval d ps = Some (p, x, newv) ->
  term_has_type sigma x typ.
Proof.
  intros.
  apply match_rep_x_in in H. rewrite in_map_iff in H.
  destruct H as [[pat tm] [Hp Hinp]]; subst.
  apply Hall. auto.
Qed.*)

(*TODO: move above?*)
Variable vt: val_typevar.
Section Defs.

Variable (pf: pi_funpred gamma_valid pd).
Notation funs := (funs gamma_valid pd pf).

(*Inversion lemma for patterns*)

(*TODO: need to prove we never hit None on well-typed pattern
  match by exhaustivenss - need relation of [match] with
  [match_val_single]*)
  

(*Terms*)
(* There are many dependent type obligations and casting to ensure that
  the types work out. In each case, we separate the hypotheses and give
  explicit types for clarity. The final result is often quite simple and just
  needs 1 or more casts for dependent type purposes. *)
Fixpoint term_rep (v: val_vars pd vt) (t: term) (ty: vty)
  (Hty: term_has_type sigma t ty) {struct t} : domain (val vt ty) :=
  (match t as tm return t = tm -> domain (val vt ty) with
  | Tconst (ConstInt z) => fun Htm =>
    let Hty' : term_has_type sigma (Tconst (ConstInt z)) ty :=
      has_type_eq Htm Hty in
    let Htyeq : vty_int = ty :=
      eq_sym (ty_constint_inv Hty') in

    cast_dom_vty Htyeq z (*(z_to_dom _ _ _ _ v z)*)
  | Tconst (ConstReal r) => fun Htm =>
    let Hty' : term_has_type sigma (Tconst (ConstReal r)) ty :=
      has_type_eq Htm Hty in
    let Htyeq : vty_real = ty :=
      eq_sym (ty_constreal_inv Hty') in

    cast_dom_vty Htyeq r (*(r_to_dom _ _ _ _ v r)*)
  | Tvar x => fun Htm =>
    let Heq : ty = snd x := ty_var_inv (has_type_eq Htm Hty) in
    (dom_cast _ (f_equal (val vt) (eq_sym Heq)) (var_to_dom _ vt v x))
    (*dom_cast _ (f_equal (v_vars _ v) Heq)*) 
    (*ltac:(rewrite Heq; exact (var_to_dom _ _ v x))*)

  | Tfun f vs ts => fun Htm =>
    (*Some proof we need; we give types for clarity*)
    let Hty': term_has_type sigma (Tfun f vs ts) ty :=
      has_type_eq Htm Hty in
    let Htyeq : ty_subst (s_params f) vs (s_ret f) = ty :=
      eq_sym (ty_fun_ind_ret Hty') in
    (*The main typecast: v(sigma(ty_ret)) = sigma'(ty_ret), where
      sigma sends (s_params f)_i -> vs_i and 
      sigma' sends (s_params f) _i -> v(vs_i)*)
    let Heqret : v_subst (v_typevar vt) (ty_subst (s_params f) vs (s_ret f)) =
      ty_subst_s (s_params f) (map (v_subst (v_typevar vt)) vs) (s_ret f) :=
        funsym_subst_eq (s_params f) vs (v_typevar vt) (s_ret f) (s_params_nodup f)
        (tfun_params_length Hty') in

    (* The final result is to apply [funs] to the [arg_list] created recursively
      from the argument domain values. We need two casts to make the dependent
      types work out*)
  
    cast_dom_vty Htyeq (
      dom_cast (dom_aux pd)
        (eq_sym Heqret)
          ((funs f (map (val vt) vs)) 
            (get_arg_list vt f vs ts (term_rep v) (ex_intro _ ty Hty'))))
  | Tlet t1 x t2 => fun Htm =>
    let Hty' : term_has_type sigma (Tlet t1 x t2) ty :=
      has_type_eq Htm Hty in
    let Ht1 : term_has_type sigma t1 (snd x) :=
      proj1 (ty_let_inv Hty') in
    let Ht2 : term_has_type sigma t2 ty :=
      proj2 (ty_let_inv Hty') in 

    term_rep (substi vt v x (term_rep v t1 (snd x) Ht1)) t2 ty Ht2

  | Tif f t1 t2 => fun Htm =>
    let Hty' : term_has_type sigma (Tif f t1 t2) ty :=
      has_type_eq Htm Hty in
    let Ht1 : term_has_type sigma t1 ty :=
      (proj1 (ty_if_inv Hty')) in
    let Ht2 : term_has_type sigma t2 ty :=
      (proj1 (proj2 (ty_if_inv Hty'))) in
    let Hf: valid_formula sigma f :=
      (proj2 (proj2 (ty_if_inv Hty'))) in

    if (formula_rep v f Hf) then term_rep v t1 ty Ht1 else term_rep v t2 ty Ht2
  | Tmatch t ty1 xs => fun Htm =>
    let Hty' : term_has_type sigma (Tmatch t ty1 xs) ty :=
      has_type_eq Htm Hty in
    let Ht1 : term_has_type sigma t ty1 :=
      proj1 (ty_match_inv Hty') in
    let Hall : Forall (fun x => term_has_type sigma (snd x) ty) xs :=
      proj2 (ty_match_inv Hty') in
    

    let Hval : valid_type sigma ty1 :=
      has_type_valid gamma_valid _ _ Ht1 in

    let dom_t := term_rep v t ty1 Ht1 in

      (*Can't make [match_rep] a separate function or else Coq
      cannot tell structurally decreasing. So we inline it*)
      let fix match_rep (ps: list (pattern * term)) 
        (Hall: Forall (fun x => term_has_type sigma (snd x) ty) ps) :
         domain (val vt ty) :=
      match ps as l' return 
        Forall (fun x => term_has_type sigma (snd x) ty) l' ->
        domain (val vt ty) with
      | (p , dat) :: ptl => fun Hall =>
        match (match_val_single vt ty1 Hval dom_t p) with
        | Some l => term_rep (extend_val_with_list vt v l) dat ty
          (Forall_inv Hall) 
        | None => match_rep ptl (Forall_inv_tail Hall)
        end
      | _ => (*TODO: show we cannot reach this*) fun _ =>
        match domain_ne pd (val vt ty) with
        | DE x =>  x
        end
      end Hall in
      match_rep xs Hall
    | Teps f x => fun Htm =>
      let Hty' : term_has_type sigma (Teps f x) ty :=
        has_type_eq Htm Hty in
      let Hval : valid_formula sigma f := proj1 (ty_eps_inv Hty') in
      let Heq : ty = snd x := proj2 (ty_eps_inv Hty') in
      (*We need to show that domain (val v ty) is inhabited*)
      let def : domain (val vt ty) :=
      match (domain_ne pd (val vt ty)) with
      | DE x => x 
      end in
      (*Semantics for epsilon - use Coq's classical epsilon,
        we get an instance y of [domain (val v ty)]
        that makes f true when x evaluates to y
        TODO: make sure this works*)

      epsilon (inhabits def) (fun (y: domain (val vt ty)) =>
        is_true (formula_rep (substi vt v x (dom_cast _ (f_equal (val vt) Heq) y)) f Hval))


  end) eq_refl

with formula_rep (v: val_vars pd vt) (f: formula) 
  (Hval: valid_formula sigma f) {struct f} : bool :=
  (match f as fmla return f = fmla -> bool with
  | Ftrue => fun _ => true
  | Ffalse => fun _ => false
  | Fnot f' => fun Hf =>
    let Hval' : valid_formula sigma (Fnot f') :=
      valid_formula_eq Hf Hval in
    let Hf' : valid_formula sigma f' :=
      valid_not_inj Hval'
    in 
    
    negb (formula_rep v f' Hf')
  | Fbinop b f1 f2 => fun Hf =>
    let Hval' : valid_formula sigma (Fbinop b f1 f2) :=
      valid_formula_eq Hf Hval in
    let Hf1 : valid_formula sigma f1 :=
     proj1 (valid_binop_inj Hval') in
    let Hf2 : valid_formula sigma f2 :=
      proj2 (valid_binop_inj Hval') in

    bool_of_binop b (formula_rep v f1 Hf1) (formula_rep v f2 Hf2)
  | Flet t x f' => fun Hf =>
    let Hval' : valid_formula sigma (Flet t x f') :=
      valid_formula_eq Hf Hval in
    let Ht: term_has_type sigma t (snd x) :=
      (proj1 (valid_let_inj Hval')) in
    let Hf': valid_formula sigma f' :=
      (proj2 (valid_let_inj Hval')) in

    formula_rep (substi vt v x (term_rep v t (snd x) Ht)) f' Hf'
  | Fif f1 f2 f3 => fun Hf =>
    let Hval' : valid_formula sigma (Fif f1 f2 f3) :=
      valid_formula_eq Hf Hval in
    let Hf1 : valid_formula sigma f1 :=
      proj1 (valid_if_inj Hval') in
    let Hf2 : valid_formula sigma f2 :=
      proj1 (proj2 (valid_if_inj Hval')) in
    let Hf3 : valid_formula sigma f3 :=
      proj2 (proj2 (valid_if_inj Hval')) in

    if formula_rep v f1 Hf1 then formula_rep v f2 Hf2 else formula_rep v f3 Hf3
  (*Much simpler than Tfun case above because we don't need casting*)
  | Fpred p vs ts => fun Hf =>
    let Hval': valid_formula sigma (Fpred p vs ts) :=
      valid_formula_eq Hf Hval in

    preds _ _ pf p (map (val vt) vs)
      (get_arg_list_pred vt p vs ts (term_rep v) Hval')

  | Fquant Tforall x f' => fun Hf =>
    let Hval' : valid_formula sigma (Fquant Tforall x f') :=
      valid_formula_eq Hf Hval in
    let Hf' : valid_formula sigma f' :=
      valid_quant_inj Hval' in

    (*NOTE: HERE is where we need the classical axiom assumptions*)
    all_dec (forall d, formula_rep (substi vt v x d) f' Hf')

  | Fquant Texists x f' => fun Hf =>
    let Hval' : valid_formula sigma (Fquant Texists x f') :=
      valid_formula_eq Hf Hval in
    let Hf' : valid_formula sigma f' :=
      valid_quant_inj Hval' in

    (*NOTE: HERE is where we need the classical axiom assumptions*)
    all_dec (exists d, formula_rep (substi vt v x d) f' Hf')
  | Feq ty t1 t2 => fun Hf =>
    let Hval' : valid_formula sigma (Feq ty t1 t2) :=
      valid_formula_eq Hf Hval in
    let Ht1 : term_has_type sigma t1 ty := 
      proj1 (valid_eq_inj Hval') in
    let Ht2 : term_has_type sigma t2 ty :=
      proj2 (valid_eq_inj Hval') in

    (*TODO: require decidable equality for all domains?*)
    all_dec (term_rep v t1 ty Ht1 = term_rep v t2 ty Ht2)
  | Fmatch t ty1 xs => fun Hf =>
    (*Similar to term case*)
    let Hval' : valid_formula sigma (Fmatch t ty1 xs) :=
      valid_formula_eq Hf Hval in
    let Ht1 : term_has_type sigma t ty1 :=
      proj1 (valid_match_inv Hval') in
    let Hall : Forall (fun x => valid_formula sigma (snd x)) xs :=
      proj2 (valid_match_inv Hval') in
    

    let Hval : valid_type sigma ty1 :=
      has_type_valid gamma_valid _ _ Ht1 in

    let dom_t := term_rep v t ty1 Ht1 in

      (*Can't make [match_rep] a separate function or else Coq
      cannot tell structurally decreasing. So we inline it*)
      let fix match_rep (ps: list (pattern * formula)) 
        (Hall: Forall (fun x => valid_formula sigma (snd x)) ps) :
         bool :=
      match ps as l' return 
        Forall (fun x => valid_formula sigma (snd x)) l' ->
        bool with
      | (p , dat) :: ptl => fun Hall =>
        match (match_val_single vt ty1 Hval dom_t p) with
        | Some l => formula_rep (extend_val_with_list vt v l) dat
          (Forall_inv Hall) 
        | None => match_rep ptl (Forall_inv_tail Hall)
        end
      | _ => (*TODO: show we cannot reach this*) fun _ => false
      end Hall in
      match_rep xs Hall
  end) eq_refl
  .

(*First, rewriting lemmas for formulas*)
(*In other files, things do not simplify/reduce because of the
  dependent types/proofs. These rewrite lemmas ensure we 
  never have to unfold giant proof terms*)
Lemma fbinop_rep (vv: val_vars pd vt)
  (f1 f2: formula) (b: binop) 
  (Hval: valid_formula sigma (Fbinop b f1 f2)) :
  formula_rep vv (Fbinop b f1 f2) Hval =
  bool_of_binop b 
  (formula_rep vv f1 
    (proj1 (valid_binop_inj (valid_formula_eq eq_refl Hval))))
  (formula_rep vv f2 
    (proj2 (valid_binop_inj (valid_formula_eq eq_refl Hval)))).
Proof.
  reflexivity.
Qed.

Lemma fpred_rep (vv: val_vars pd vt)
  (p: predsym) (vs: list vty) (args: list term)
  (Hval: valid_formula sigma (Fpred p vs args)) :
  formula_rep vv (Fpred p vs args) Hval =
  preds gamma_valid pd pf p (map (v_subst (v_typevar vt)) vs)
    (get_arg_list_pred vt p vs args 
    (term_rep vv)
    (valid_formula_eq eq_refl Hval)).
Proof.
  reflexivity.
Qed.

Lemma fforall_rep (vv: val_vars pd vt)
  (f: formula) (v: vsymbol) 
  (Hval: valid_formula sigma (Fquant Tforall v f)) :
  formula_rep vv (Fquant Tforall v f) Hval =
  all_dec (forall d, formula_rep (substi vt vv v d) f
    (valid_quant_inj (valid_formula_eq eq_refl Hval))).
Proof.
  reflexivity.
Qed.

Lemma flet_rep (vv: val_vars pd vt)
  (t: term) (v: vsymbol) (f: formula) 
  (Hval: valid_formula sigma (Flet t v f)) :
  formula_rep vv (Flet t v f) Hval =
  formula_rep
  (substi vt vv v (term_rep vv t (snd v) 
    (proj1 (valid_let_inj (valid_formula_eq eq_refl Hval))))) f
    (proj2(valid_let_inj (valid_formula_eq eq_refl Hval))).
Proof.
  reflexivity.
Qed.

Lemma fexists_rep (vv: val_vars pd vt)
  (f: formula) (v: vsymbol) 
  (Hval: valid_formula sigma (Fquant Texists v f)) :
  formula_rep vv (Fquant Texists v f) Hval =
  all_dec (exists d, formula_rep (substi vt vv v d) f
    (valid_quant_inj (valid_formula_eq eq_refl Hval))).
Proof.
  reflexivity.
Qed.

Lemma fif_rep (vv: val_vars pd vt)
  (f1 f2 f3: formula)
  (Hval: valid_formula sigma (Fif f1 f2 f3)) :
  formula_rep vv (Fif f1 f2 f3) Hval =
  if (formula_rep vv f1 
  (proj1 (valid_if_inj (valid_formula_eq eq_refl Hval))))
  then 
  (formula_rep vv f2 
    (proj1 (proj2 (valid_if_inj (valid_formula_eq eq_refl Hval)))))
  else
  (formula_rep vv f3 
    (proj2 (proj2 (valid_if_inj (valid_formula_eq eq_refl Hval))))).
Proof.
  reflexivity.
Qed.

Lemma fmatch_rep (vv: val_vars pd vt)
  (t: term) (ty: vty) (ps: list (pattern * formula))
  (Hval: valid_formula sigma (Fmatch t ty ps)):
  formula_rep vv (Fmatch t ty ps) Hval =
  (fix match_rep (xs: list (pattern * formula)) 
  (Hall: Forall (fun x => valid_formula sigma (snd x)) xs) :
   bool :=
    match xs as l' return 
      Forall (fun x => valid_formula sigma (snd x)) l' ->
      bool with
    | (p , dat) :: ptl => fun Hall =>
      match (match_val_single vt ty 
        (has_type_valid gamma_valid _ _ 
          (proj1 (valid_match_inv (valid_formula_eq eq_refl Hval)))) (term_rep vv t ty 
        (proj1 (valid_match_inv (valid_formula_eq eq_refl Hval)))) p) with
      | Some l => formula_rep (extend_val_with_list vt vv l) dat
        (Forall_inv Hall) 
      | None => match_rep ptl (Forall_inv_tail Hall)
      end
    | _ => fun _ => false
    end Hall) ps (proj2 (valid_match_inv (valid_formula_eq eq_refl Hval))).
Proof.
  reflexivity.
Qed.
  


(*We need to know that the valid typing proof is irrelevant.
  I believe this should be provable without proof irrelevance,
  but [term_rep] and [formula_rep] already depend on
  classical logic, which implies proof irrelevance.
  We prove without proof irrelevance to limit the use of axioms.
  We need functional extensionality for the epsilon case only*)

Require Import FunctionalExtensionality.
Lemma term_form_rep_irrel: forall (tm: term) (f: formula),
  (forall (v: val_vars pd vt) (ty: vty) (Hty1 Hty2:
    term_has_type sigma tm ty), 
      term_rep v tm ty Hty1 = term_rep v tm ty Hty2) /\
  (forall (v: val_vars pd vt) (Hval1 Hval2:
    valid_formula sigma f), 
      formula_rep v f Hval1 = formula_rep v f Hval2).
Proof.
  apply term_formula_ind; intros; simpl; auto.
  - simpl. destruct c; simpl;
    f_equal; apply UIP_dec; apply vty_eq_dec.
  - f_equal. f_equal. apply UIP_dec; apply vty_eq_dec.
  - f_equal. apply UIP_dec; apply vty_eq_dec.
    f_equal. f_equal. f_equal. apply UIP_dec. apply Nat.eq_dec.
    f_equal. apply get_arg_list_eq.
    rewrite Forall_forall. intros x Hinx ty' H1 H2.
    rewrite Forall_forall in H. apply H. assumption.
  - replace ((term_rep v0 tm1 (snd v) (proj1 (ty_let_inv (has_type_eq eq_refl Hty1)))))
    with  (term_rep v0 tm1 (snd v) (proj1 (ty_let_inv (has_type_eq eq_refl Hty2))))
    by apply H.
    apply H0.
  - replace (formula_rep v f (proj2 (proj2 (ty_if_inv (has_type_eq eq_refl Hty1)))))
    with (formula_rep v f (proj2 (proj2 (ty_if_inv (has_type_eq eq_refl Hty2)))))
    by apply H.
    match goal with | |- context [ if ?b then ?x else ?y] => destruct b end.
    apply H0. apply H1.
  - (*ugh, this one is very annoying*)
    (*We need a nested induction here*)
    generalize dependent (proj1 (ty_match_inv (has_type_eq eq_refl Hty1))).
    generalize dependent (proj2 (ty_match_inv (has_type_eq eq_refl Hty1))).
    generalize dependent (proj1 (ty_match_inv (has_type_eq eq_refl Hty2))).
    generalize dependent (proj2 (ty_match_inv (has_type_eq eq_refl Hty2))).
    clear Hty1 Hty2.
    intros Hall1 Hty1 Hall2 Hty2. (*for better names*)
    revert Hall1 Hty1 Hall2 Hty2. 
    induction ps; simpl; intros; auto.
    destruct a.
    (*Bulk of work done in [match_val_single_irrel]*)
    rewrite (H _ _ Hty1 Hty2) at 1.
    rewrite (match_val_single_irrel _ _ (has_type_valid gamma_valid tm v
    Hty1) (has_type_valid gamma_valid tm v Hty2)).
    destruct (match_val_single vt v
    (has_type_valid gamma_valid tm v Hty2)
    (term_rep v0 tm v Hty2) p).
    + inversion H0; subst. apply (H3 (extend_val_with_list vt v0 l)).
    + inversion H0; subst.
      apply IHps. auto.
  - (*TODO: is this possible without funext?*)
    f_equal. apply functional_extensionality_dep.
    intros x.
    rewrite (H (substi vt v0 v (dom_cast (dom_aux pd)
    (f_equal (val vt) (proj2 (ty_eps_inv (has_type_eq eq_refl Hty1)))) x))
      (proj1 (ty_eps_inv (has_type_eq eq_refl Hty1)))
    (proj1 (ty_eps_inv (has_type_eq eq_refl Hty2)))).
    assert (proj2 (ty_eps_inv (has_type_eq eq_refl Hty1)) =
    (proj2 (ty_eps_inv (has_type_eq eq_refl Hty2)))).
    apply UIP_dec. apply vty_eq_dec. rewrite H0.
    reflexivity.
    - f_equal. apply get_arg_list_pred_eq.
    rewrite Forall_forall. intros x Hinx ty' H1 H2.
    rewrite Forall_forall in H. apply H. assumption.
  - destruct q;
    repeat match goal with |- context [ all_dec ?P ] => 
      destruct (all_dec P); simpl; auto end.
    + exfalso. apply n. intros d.
      erewrite (H (substi vt v0 v d)).
      apply i.
    + exfalso. apply n. intros d.
      erewrite H. apply i.
    + exfalso. apply n. 
      destruct e as [d Hd].
      exists d. erewrite H. apply Hd.
    + exfalso. apply n.
      destruct e as [d Hd].
      exists d. erewrite H. apply Hd.
  - erewrite H. erewrite H0. reflexivity.
  - erewrite H. erewrite H0. reflexivity.
  - erewrite H. reflexivity.
  - erewrite H. erewrite H0. reflexivity.
  - erewrite H. erewrite H0. erewrite H1. reflexivity.
  - (*Match case again - proof almost identical*)
    generalize dependent (proj1 (valid_match_inv (valid_formula_eq eq_refl Hval1))).
    generalize dependent (proj2 (valid_match_inv (valid_formula_eq eq_refl Hval1))).
    generalize dependent (proj1 (valid_match_inv (valid_formula_eq eq_refl Hval2))).
    generalize dependent (proj2 (valid_match_inv (valid_formula_eq eq_refl Hval2))).
    clear Hval1 Hval2.
    intros Hall1 Hty1 Hall2 Hty2. (*for better names*)
    revert Hall1 Hty1 Hall2 Hty2. 
    induction ps; simpl; intros; auto.
    destruct a.
    (*Bulk of work done in [match_val_single_irrel]*)
    rewrite (H _ _ Hty1 Hty2) at 1.
    rewrite (match_val_single_irrel _ _ (has_type_valid gamma_valid tm v
    Hty1) (has_type_valid gamma_valid tm v Hty2)).
    destruct (match_val_single vt v
    (has_type_valid gamma_valid tm v Hty2)
    (term_rep v0 tm v Hty2) p).
    + inversion H0; subst. apply (H3 (extend_val_with_list vt v0 l)).
    + inversion H0; subst.
      apply IHps. auto.
Qed.

Lemma term_rep_irrel (v: val_vars pd vt) (tm: term)
  (ty: vty) (Hty1 Hty2: term_has_type sigma tm ty) :
  term_rep v tm ty Hty1 = term_rep v tm ty Hty2.
Proof.
  apply term_form_rep_irrel. apply Ftrue.
Qed.

Lemma fmla_rep_irrel (v: val_vars pd vt) (f: formula)
    (Hval1 Hval2: valid_formula sigma f) :
  formula_rep v f Hval1 = formula_rep v f Hval2.
Proof.
  apply term_form_rep_irrel. apply (Tconst (ConstInt 0)).
Qed.


(*Later, for IndProp, we need a few things. 
  First is alpha substitution*)

(*First, alpha substitution*)
Section Alpha.

(*Substitute y for all free ocurrences of x*)

(*TODO: remove this: same as pat_fv*)
(*
Fixpoint bnd_p (p: pattern) : list vsymbol :=
  match p with
  | Pvar v => [v]
  | Pconstr f tys ps => concat (map bnd_p ps)
  | Pwild => nil
  | Por p1 p2 => (bnd_p p1) ++ (bnd_p p2)
  | Pbind p1 v => v :: (bnd_p p1)
  end.*)

Lemma or_false_r (P: Prop):
  (P \/ False) <-> P.
Proof.
  split; intros; auto. destruct H; auto. destruct H.
Qed.
(*
Lemma bnd_fv_p (p: pattern):
  forall x, In x (bnd_p p) <-> In x (pat_fv p).
Proof.
  intros x. induction p; simpl; try reflexivity.
  - induction ps; simpl; try reflexivity.
    inversion H; subst. specialize (IHps H3).
    rewrite in_app_iff, H2, union_elts, IHps.
    reflexivity.
  - rewrite in_app_iff, union_elts, IHp1, IHp2.
    reflexivity.
  - rewrite union_elts, or_comm, IHp. simpl. 
    rewrite or_false_r. reflexivity.
Qed.*)

Fixpoint sub_f (x y: vsymbol) (f: formula) : formula :=
  match f with
  | Fpred p tys tms => Fpred p tys (map (sub_t x y) tms)
  | Fquant q v f' =>
    if vsymbol_eq_dec x v then f else
    Fquant q v (sub_f x y f')
  | Feq ty t1 t2 =>
    Feq ty (sub_t x y t1) (sub_t x y t2)
  | Fbinop b f1 f2 =>
    Fbinop b (sub_f x y f1) (sub_f x y f2)
  | Fnot f' => Fnot (sub_f x y f')
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  | Flet tm v f' =>
    Flet (sub_t x y tm) v 
      (if vsymbol_eq_dec x v then f' else
      sub_f x y f')
  | Fif f1 f2 f3 =>
    Fif (sub_f x y f1) (sub_f x y f2) (sub_f x y f3)
  | Fmatch tm ty ps =>
    Fmatch (sub_t x y tm) ty
      (map (fun p => if in_bool vsymbol_eq_dec x (pat_fv (fst p)) then
        p else (fst p, sub_f x y (snd p))) ps)
  end
with sub_t (x y: vsymbol) (t: term) : term :=
  match t with
  | Tconst c => Tconst c
  | Tvar v  => 
    (*The base case*)
    Tvar (if vsymbol_eq_dec x v then y else v)
  | Tfun fs tys tms =>
    Tfun fs tys (map (sub_t x y) tms)
  | Tlet tm1 v tm2 =>
    Tlet (sub_t x y tm1) v
    (if vsymbol_eq_dec x v then tm2 else (sub_t x y tm2))
  | Tif f1 t1 t2 =>
    Tif (sub_f x y f1) (sub_t x y t1) (sub_t x y t2)
  | Tmatch tm ty ps =>
    Tmatch (sub_t x y tm) ty
    (map (fun p => if in_bool vsymbol_eq_dec x (pat_fv (fst p)) then
      p else (fst p, sub_t x y (snd p))) ps)
  | Teps f1 v =>
    (*TODO: is this correct?*)
    if vsymbol_eq_dec x v then t else
    Teps (sub_f x y f1) v
  end.

(*Reinterpret x as y*)
(*
Definition subst_val (v: valuation gamma_valid i) (x y: vsymbol) :
  valuation gamma_valid i.
  apply (Build_valuation gamma_valid i
  (fun var => if vsymbol_eq_dec x var then 
  (v_typevar v y) else v_typevar v x)).
  - intros x'. destruct (vsymbol_eq_dec x x');
    apply (v_typevar_val gamma_valid i v).
  - exact (v_vars gamma_valid i v).
    + rewrite <- e.*)

    (*
Definition val_eq (v1 v2: valuation gamma_valid i)
  (Heq: v1 = v2) (ty: vty) :
  val v2 ty = val v1 ty :=
  fun_args_eq_dep _ _ ty (f_equal (fun x => val x) (eq_sym Heq)).

(*I think we may need this - see*)
Lemma term_val_eq (t: term) (v1 v2: valuation gamma_valid i)
  (Heq: v1 = v2) (ty: vty)
  (Hty: term_has_type sigma t ty) :
  term_rep v1 t ty Hty =
  dom_cast _ (val_eq v1 v2 Heq ty) (term_rep v2 t ty Hty).
Admitted.
*)
(*Prove that substitution is correct: the substituted
  formula is the same as evaluating the original where
  x is substituted for y*)
(*Problem: x and y have some (unique) type in f, but we don't
  know what they are - could add types to variables, let's see*)

(*Need assumption that y not bound in t/f*)
Fixpoint bnd_f (f: formula) : list vsymbol :=
  match f with
  | Fpred p tys tms => concat (map bnd_t tms)
  | Fquant q v f' =>
    v :: bnd_f f'
  | Feq ty t1 t2 =>
    bnd_t t1 ++ bnd_t t2
  | Fbinop b f1 f2 =>
    bnd_f f1 ++ bnd_f f2
  | Fnot f' => bnd_f f'
  | Ftrue => nil
  | Ffalse => nil
  | Flet tm v f' =>
    v :: bnd_t tm ++ bnd_f f' 
  | Fif f1 f2 f3 =>
    bnd_f f1 ++ bnd_f f2 ++ bnd_f f3
  | Fmatch tm ty ps =>
    bnd_t tm ++ concat (map 
      (fun p => pat_fv (fst p) ++ bnd_f (snd p)) ps)
  end
with bnd_t (t: term) : list vsymbol :=
  match t with
  | Tconst c => nil
  | Tvar v  => nil (*v is free*)
    (*[v]*)
  | Tfun fs tys tms =>
    concat (map bnd_t tms)
  | Tlet tm1 v tm2 =>
    v :: bnd_t tm1 ++ bnd_t tm2
  | Tif f1 t1 t2 =>
    bnd_f f1 ++ bnd_t t1 ++ bnd_t t2
  | Tmatch tm ty ps =>
    bnd_t tm ++ concat (map
      (fun p => pat_fv (fst p) ++ bnd_t (snd p)) ps)
  | Teps f1 v =>
    v :: bnd_f f1
    (*TODO: is this correct?*)
  end.

  Ltac solve_bnd :=  
    repeat match goal with
    | H: ~In ?x (bnd_t ?t) |- ~In ?x (bnd_f ?f) =>
      let C := fresh in
      intro C; apply H; simpl
    | H: ~In ?x (bnd_t ?t) |- ~In ?x (bnd_t ?t2) =>
      let C := fresh in
      intro C; apply H; simpl
    | H: ~In ?x (bnd_f ?t) |- ~In ?x (bnd_f ?f) =>
      let C := fresh in
      intro C; apply H; simpl
    | H: ~In ?x (bnd_f ?t) |- ~In ?x (bnd_t ?t2) =>
      let C := fresh in
      intro C; apply H; simpl
    | |- In ?x (?l1 ++ ?l2) => apply in_or_app
    | |- ?P \/ ?Q => (*idtac "x";*)
      first [left; solve[solve_bnd] | right; solve[solve_bnd]]
    | |- In ?x ?y => solve[try assumption; auto]
    end.

Ltac simpl_all_dec_tac :=
  repeat match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end.

Lemma all_dec_eq: forall (P Q: Prop),
  (P <-> Q) ->
  (@eq bool (proj_sumbool _ _ (all_dec P)) (proj_sumbool _ _ (all_dec Q))).
Proof.
  intros. simpl_all_dec_tac; exfalso.
  - apply n. apply H. apply p.
  - apply n. apply H. apply q.
Qed.

Lemma simpl_all_dec (P: Prop):
   (all_dec P) <-> P.
Proof.
  split; intros;
  destruct (all_dec P); auto.
  inversion H.
Qed.

(*Substitution over [get_arg_list]*)
Lemma get_arg_list_sub x y f tys tms 
  (reps1 reps2: forall (t: term) (ty: vty),
  term_has_type sigma t ty ->
  domain (val vt ty))
  (Hreps: Forall (fun tm =>
    forall (ty:vty) Hty1 Hty2,
    ~ In y (bnd_t tm) ->
    reps1 tm ty Hty1 =
    reps2 (sub_t x y tm) ty Hty2) tms)
  (Hfree: ~In y (bnd_t (Tfun f tys tms)))
  (Hex1 : exists typ, term_has_type sigma (Tfun f tys tms) typ)
  (Hex2: exists typ, term_has_type sigma (Tfun f tys (map (sub_t x y) tms)) typ):
  get_arg_list vt f tys tms reps1 Hex1 =
  get_arg_list vt f tys (map (sub_t x y) tms) reps2 Hex2.
Proof.
  unfold get_arg_list. simpl.
  destruct (typecheck_dec sigma (Tfun f tys tms) Hex1).
  destruct (typecheck_dec sigma (Tfun f tys (map (sub_t x y) tms)) Hex2).
  assert (x0 = x1). {
    inversion t; subst. inversion t0; subst. reflexivity.
  }
  subst.
  destruct (fun_ty_inversion sigma f tys tms x1 t).
  destruct (fun_ty_inversion sigma f tys (map (sub_t x y) tms) x1 t0).
  destruct a as [Hallval1 [Hlents1 [Hlenvs1 [Hallty1 Hx01]]]].
  destruct a0 as [Hallval2 [Hlents2 [Hlenvs2 [Hallty2 Hx02]]]].
  simpl. subst.
  unfold funsym_sigma_args.
  generalize dependent (s_args f).
  clear Hex1 Hex2 t0 t. 
  induction tms; simpl; intros. 
  - f_equal. f_equal. f_equal. apply nat_eq_refl.
  - destruct l.
    + inversion Hlents2.
    + simpl in Hlenvs2. f_equal. 2: apply IHtms; inversion Hreps; auto; solve_bnd.
      assert (Hlenvs1 = Hlenvs2) by apply nat_eq_refl.
      rewrite H. f_equal.
      rewrite Forall_forall in Hreps.
      apply Hreps. left; auto.
      solve_bnd.
Qed.

(*Same for [get_arg_list_pred]*)
Lemma get_arg_list_pred_sub x y p tys tms 
  (reps1 reps2: forall (t: term) (ty: vty),
  term_has_type sigma t ty ->
  domain (val vt ty))
  (Hreps: Forall (fun tm =>
    forall (ty:vty) Hty1 Hty2,
    ~ In y (bnd_t tm) ->
    reps1 tm ty Hty1 =
    reps2 (sub_t x y tm) ty Hty2) tms)
  (Hfree: ~In y (bnd_f (Fpred p tys tms)))
  (Hval1 : valid_formula sigma (Fpred p tys tms))
  (Hval2: valid_formula sigma (Fpred p tys (map (sub_t x y) tms))):
  get_arg_list_pred vt p tys tms reps1 Hval1 =
  get_arg_list_pred vt p tys (map (sub_t x y) tms) reps2 Hval2.
Proof.
  unfold get_arg_list_pred. simpl.
  destruct (pred_ty_inversion sigma p tys tms Hval1).
  destruct (pred_ty_inversion sigma p tys (map (sub_t x y) tms) Hval2).
  destruct a as [Hallval1 [Hlents1 [Hlenvs1 Hallty1]]].
  destruct a0 as [Hallval2 [Hlents2 [Hlenvs2 Hallty2]]].
  simpl. subst.
  unfold predsym_sigma_args.
  generalize dependent (p_args p).
  clear Hval1 Hval2. 
  induction tms; simpl; intros. 
  - f_equal. f_equal. f_equal. apply nat_eq_refl.
  - destruct l.
    + inversion Hlents2.
    + simpl in Hlenvs2. f_equal. 2: apply IHtms; inversion Hreps; auto; solve_bnd.
      assert (Hlenvs1 = Hlenvs2) by apply nat_eq_refl.
      rewrite H. f_equal.
      rewrite Forall_forall in Hreps.
      apply Hreps. left; auto.
      solve_bnd.
Qed.

Lemma or_idem (P: Prop):
  (P \/ P) <-> P.
Proof.
  split; intros; auto. destruct H; auto.
Qed.



(*Lemma for [match_val_single]*)
Lemma match_var_single_free_var ty Hval d p l x ty'
  (Hpat: pattern_has_type sigma p ty'):
  match_val_single vt ty Hval d p = Some l ->
  In x (pat_fv p) <-> In x (map fst l).
Proof.
  revert Hval d l. generalize dependent ty'. 
  generalize dependent ty.
  induction p; auto.
  - simpl; intros.
    destruct (vty_eq_dec (snd v) ty). inversion H. subst. reflexivity.
    inversion H.
  - intros ty ty' Hpatty Hval d.
    inversion Hpatty; subst. clear H3 H4 H5 H7 H10 Hpatty. subst sigma0.
    (*replace (map (ty_subst (s_params f) vs) (s_args f))
    with (funsym_sigma_args f) in H9.*)

    (*The hard case: need lots of generalization for dependent types
      and need nested induction*) 
    unfold match_val_single; fold match_val_single.
    generalize dependent (is_sort_adt_spec (val vt ty)).
    generalize dependent ((@adt_srts_length_eq vt ty)).
    generalize dependent (@adts_srts_valid vt ty).
    destruct (is_sort_adt (val vt ty)) eqn : Hisadt;
    [|intros _ _ _ ? Hc; inversion Hc].
    intros Hsrtsvalid Hsrtslen Hadtspec.
    destruct p as [[[m adt] ts] srts].
    destruct (Hadtspec m adt ts srts eq_refl) as 
      [Hvaleq [Hinmut [Hincts Htseq]]].
    destruct (funsym_eq_dec
    (projT1
       (find_constr_rep gamma_valid m Hincts srts
          (Hsrtslen m adt ts srts eq_refl Hval) (dom_aux pd) adt
          Hinmut (adts pd m srts) (all_unif m Hincts)
          (scast (adts pd m srts adt Hinmut)
             (dom_cast (dom_aux pd) Hvaleq d)))) f); 
             [|intros ? C; inversion C].
    (*Need nested induction: simplify first*)
    generalize dependent (find_constr_rep gamma_valid m Hincts srts
    (Hsrtslen m adt ts srts eq_refl Hval) 
    (dom_aux pd) adt Hinmut (adts pd m srts)
    (all_unif m Hincts)
    (scast (adts pd m srts adt Hinmut)
       (dom_cast (dom_aux pd) Hvaleq d))).
    intros constr. destruct constr as [f' Hf']. simpl. intros Hf; subst.
    generalize dependent ((Hsrtsvalid m adt (adt_name adt) srts f eq_refl Hval (fst (proj1_sig Hf')))).
    destruct Hf'. simpl. clear e.
    destruct x0. simpl. generalize dependent a.
    generalize dependent ps.
    (*TODO: do we need to know about length of this?*)
    assert (Hargslen: length (funsym_sigma_args f srts) = length (s_args f)). {
      unfold funsym_sigma_args, ty_subst_list_s.
      rewrite map_length. reflexivity.
    }
    revert Hargslen.
    generalize dependent (s_args f); intros args; revert args.
    generalize dependent ((funsym_sigma_args f srts)).
    induction l; simpl; intros; auto. 
    + destruct ps; inversion H0; subst; reflexivity.
    + revert H0. destruct ps. intro C; inversion C.
      repeat match goal with 
      |- (match ?p with |Some l => ?x | None => ?y end) = ?z -> ?q =>
        let Hp := fresh "Hmatch" in 
        destruct p eqn: Hp end.
      all: intro C; inversion C.
      subst.
      (*Now, just need to handle the pieces*)
      inversion H; subst.
      destruct args. inversion Hargslen.
      inversion H9; subst. simpl in H4.
      apply (H2 _(ty_subst (s_params f) vs v)) in Hmatch; auto.
      apply (IHl args) in Hmatch0; auto.
      simpl. rewrite union_elts, map_app, in_app_iff ,Hmatch, Hmatch0.
      reflexivity.
  - simpl. intros. inversion H; subst. reflexivity.
  - simpl. intros. destruct (match_val_single vt ty Hval d p1) eqn: Hm.
    + inversion H; subst. inversion Hpat; subst.
      apply (IHp1 _ ty') in Hm; auto.
      rewrite union_elts ,<- H6, or_idem, Hm.
      reflexivity.
    + inversion Hpat; subst.
      apply (IHp2 _ ty') in H; auto.
      rewrite union_elts, H6, or_idem, H.
      reflexivity.
  - simpl. intros.
    destruct (match_val_single vt ty Hval d p) eqn : Hm.
    + destruct (vty_eq_dec (snd v) ty); inversion H; subst. simpl.
      inversion Hpat; subst.
      apply (IHp _ (snd v)) in Hm; auto.
      rewrite union_elts; simpl.
      rewrite or_false_r, or_comm, Hm.
      reflexivity.
    + inversion H.
Qed.

Lemma get_assoc_list_some {A B: Set} 
(eq_dec: forall (x y: A), {x = y} + { x <> y}) 
(l: list (A * B)) (x: A) (res: B):
  get_assoc_list eq_dec l x = Some res ->
  In (x, res) l.
Proof.
  induction l; simpl. intro C; inversion C.
  destruct (eq_dec x (fst a)); subst. intro C; inversion C; subst.
  left. destruct a; auto.
  intros. right. apply IHl. assumption.
Qed.

Lemma get_assoc_list_none {A B: Set} 
(eq_dec: forall (x y: A), {x = y} + { x <> y}) 
(l: list (A * B)) (x: A) :
  get_assoc_list eq_dec l x = None <->
  ~ In x (map fst l).
Proof.
  induction l; simpl; split; intros; auto.
  - intro C. destruct (eq_dec x (fst a)); subst.
    inversion H. destruct C. subst. contradiction.
    apply IHl; auto.
  - destruct (eq_dec x (fst a)); subst. exfalso. apply H. left; auto.
    apply IHl. intro C. apply H. right; assumption.
Qed.

Lemma extend_val_with_list_in (vv: val_vars pd vt) 
  (x: vsymbol)
  (d: domain (val vt (snd x))) (l: list (vsymbol * {t : vty & domain (val vt t)}))
  (Hl: forall x y, In (x, y) l -> projT1 y = snd x):
    In x (map fst l) ->
    extend_val_with_list vt (substi vt vv x d) l =
    extend_val_with_list vt vv l.
Proof.
  unfold extend_val_with_list.
  intros Hinl. apply functional_extensionality_dep; intros v.
  destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha.
  - apply get_assoc_list_some in Ha.
    apply Hl in Ha.
    destruct (vty_eq_dec (snd v) (projT1 s)); auto. rewrite Ha in n.
    contradiction.
  - rewrite get_assoc_list_none in Ha.
    unfold substi. 
    destruct (vsymbol_eq_dec v x); auto.
    subst. contradiction.
Qed.

Lemma extend_val_with_list_notin (vv: val_vars pd vt) 
  (x: vsymbol)
  (d: domain (val vt (snd x))) (l: list (vsymbol * {t : vty & domain (val vt t)}))
  (Hl: forall x y, In (x, y) l -> projT1 y = snd x):
    ~In x (map fst l) ->
    extend_val_with_list vt (substi vt vv x d) l =
    substi vt (extend_val_with_list vt vv l) x d.
Proof.
  intros. unfold extend_val_with_list.
  unfold substi.
  apply functional_extensionality_dep; intros v.
  destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha; auto.
  destruct (vsymbol_eq_dec v x); subst; auto.
  exfalso. assert (get_assoc_list vsymbol_eq_dec l x = None).
  apply get_assoc_list_none. auto. rewrite H0 in Ha. inversion Ha.
Qed. 


(*TODO: see if we can get rid of casting in Here*)
Lemma sub_correct (t: term) (f: formula) :
  (forall (x y: vsymbol) (Heq: snd x = snd y) 
    (v: val_vars pd vt) (ty: vty) 
    (Hty1: term_has_type sigma t ty)
    (Hty2: term_has_type sigma (sub_t x y t) ty)
    (Hfree: ~In y (bnd_t t)),
    term_rep (substi vt v x 
    (dom_cast _ (f_equal (val vt) (eq_sym Heq))
      (v y))) t ty Hty1 =
    term_rep v (sub_t x y t) ty Hty2) /\
  (forall (x y: vsymbol) (Heq: snd x = snd y) 
    (v: val_vars pd vt)
    (Hval1: valid_formula sigma f)
    (Hval2: valid_formula sigma (sub_f x y f))
    (Hfree: ~In y (bnd_f f)),
    formula_rep (substi vt v x 
    (dom_cast _ (f_equal (val vt) (eq_sym Heq))
      (v y))) f Hval1 =
    formula_rep v (sub_f x y f) Hval2).
Proof.
  revert t f.
  apply term_formula_ind; intros; simpl; auto.
  - (*constants*) destruct c; auto;
    inversion Hty1;
    inversion Hty2; subst;
    unfold cast_dom_vty, eq_rec_r, eq_rec, eq_rect.
    (*Equality is annoying*)
    + assert (ty_constint_inv (has_type_eq eq_refl Hty1) = eq_refl).
        apply UIP_dec. apply vty_eq_dec.
      rewrite H. simpl.
      assert (ty_constint_inv (@has_type_eq sigma (Tconst (ConstInt z))
        (Tconst (ConstInt z)) vty_int eq_refl Hty2) = eq_refl).
        apply UIP_dec; apply vty_eq_dec.
      rewrite H0. reflexivity.
    + assert (ty_constreal_inv (has_type_eq eq_refl Hty1) = eq_refl).
        apply UIP_dec. apply vty_eq_dec. 
      rewrite H. simpl.
      assert (ty_constreal_inv (@has_type_eq sigma (Tconst (ConstReal r))
        (Tconst (ConstReal r)) vty_real eq_refl Hty2) = eq_refl).
        apply UIP_dec; apply vty_eq_dec.
      rewrite H0. reflexivity.
  - (*vars*) unfold var_to_dom.
    generalize dependent (@has_type_eq sigma (Tvar
      (if vsymbol_eq_dec x v then y else v)) 
     _ ty eq_refl Hty2).
    destruct (vsymbol_eq_dec x v).
    + intros. subst. (*destruct (vsymbol_eq_dec v v); [|contradiction].*)
      unfold dom_cast, f_equal, eq_sym.
      inversion Hty1; subst.
      assert (ty_var_inv (has_type_eq eq_refl Hty1) = eq_refl).
        apply UIP_dec. apply vty_eq_dec.
      rewrite H.
      clear H.
      unfold substi.
      destruct (vsymbol_eq_dec v v); [|contradiction].
      unfold eq_rec_r, eq_rec, eq_rect, eq_sym.
      assert (e = eq_refl).
        apply UIP_dec. apply vsymbol_eq_dec.
      rewrite H. clear H.
      generalize dependent (snd v); intros.
      subst.
      assert (ty_var_inv t = eq_refl).
        apply UIP_dec. apply vty_eq_dec.
      rewrite H. reflexivity.
    + intros. unfold substi.
      destruct (vsymbol_eq_dec v x); subst; try contradiction.
      f_equal. f_equal. f_equal. apply UIP_dec. apply vty_eq_dec.
  - (*function case*) unfold cast_dom_vty, eq_rec_r, eq_rec, eq_rect.
    inversion Hty1; subst.
    assert (ty_fun_ind_ret (has_type_eq eq_refl Hty1) = eq_refl). {
      apply UIP_dec. apply vty_eq_dec.
    }
    rewrite H0. simpl.
    assert ((@ty_fun_ind_ret f1 l (@map term term (sub_t x y) l1)
      (ty_subst (s_params f1) l (s_ret f1)) 
        (@has_type_eq sigma  (Tfun f1 l (@map term term (sub_t x y) l1)) _ _ eq_refl Hty2)) = eq_refl). {
      apply UIP_dec. apply vty_eq_dec.
    }
    rewrite H1. simpl.
    unfold dom_cast at 1. unfold dom_cast at 2.
    assert ((tfun_params_length (has_type_eq eq_refl Hty1)) =
    (tfun_params_length (has_type_eq eq_refl Hty2))). {
      apply UIP_dec. apply Nat.eq_dec.
    }
    rewrite H2.
    clear -H Hfree.
    unfold eq_sym at 1 3.
    generalize dependent (funsym_subst_eq (s_params f1) l (v_typevar vt) 
    (s_ret f1) (s_params_nodup f1)
    (tfun_params_length (has_type_eq eq_refl Hty2))).
    generalize dependent (funsym_subst_eq (s_params f1) l (v_typevar vt) 
    (s_ret f1) (s_params_nodup f1)
    (@tfun_params_length sigma f1 l (@map term term (sub_t x y) l1)
      (ty_subst (s_params f1) l (s_ret f1)) 
      (@has_type_eq sigma (Tfun f1 l (@map term term (sub_t x y) l1))
        _ _ eq_refl Hty2))).
    simpl.
    (*To eliminate eqs*)
    generalize dependent (val vt (ty_subst (s_params f1) l (s_ret f1))).
    intros. subst.
    assert (e0 = eq_refl). { apply UIP_dec. apply sort_eq_dec. }
    rewrite H0.
    f_equal.
    (*Now we show the arg lists equal by a separate lemma*)
    apply get_arg_list_sub; auto.
    eapply Forall_impl. 2: apply H. simpl.
    intros. apply H1. auto.
  - (*term let*) 
    inversion Hty2; subst. 
    rewrite H with(Hty2:=H6) by solve_bnd.
    generalize dependent H7.
    generalize dependent ((@has_type_eq sigma
    (Tlet (sub_t x y tm1) v
    (if vsymbol_eq_dec x v then tm2 else sub_t x y tm2))
    _ ty eq_refl)).
    generalize dependent Hty2.
    simpl.
    destruct (vsymbol_eq_dec x v).
    + intros. subst.
      rewrite substi_same.
      rewrite term_rep_irrel with
        (Hty2:=(proj1 (ty_let_inv (t Hty2)))).
      apply term_rep_irrel.
    + intros.
      rewrite substi_diff; auto.
      inversion Hty1; subst.
      rewrite <- H0 with (Heq:=Heq) (Hty1:=H9) by solve_bnd.
      rewrite term_rep_irrel with (Hty2:=(proj1 (ty_let_inv (t Hty2)))).
      unfold substi at 5.
      destruct (vsymbol_eq_dec y v); subst; simpl.
      * (*Know v <> y because y is not bound*)
        exfalso. apply Hfree. simpl. left; auto.
      * apply term_rep_irrel.
  - (*term if*)
    erewrite H by solve_bnd.
    erewrite H0 by solve_bnd.
    erewrite H1 by solve_bnd.
    reflexivity.
  - (*term match case: TODO (will be hard)*)
    (*Let's see*)
    (*TODO: generalize proofs?*)
    (*Need to know that patterns are well typed*)
    inversion Hty1; subst. clear H4 H8 H9.
    rename H6 into Hallpats.
    generalize dependent (proj1 (ty_match_inv (has_type_eq eq_refl Hty1))).
    generalize dependent (proj2 (ty_match_inv (has_type_eq eq_refl Hty1))).
    clear Hty1.
    simpl in Hty2.
    generalize dependent (proj1 (ty_match_inv (@has_type_eq sigma
    (Tmatch (sub_t x y tm) v
    (map (fun p => if in_bool vsymbol_eq_dec x (pat_fv (fst p)) then
      p else (fst p, sub_t x y (snd p))) ps)) _ _ eq_refl Hty2))).
    generalize dependent (proj2 (ty_match_inv (@has_type_eq sigma
    (Tmatch (sub_t x y tm) v
    (map (fun p => if in_bool vsymbol_eq_dec x (pat_fv (fst p)) then
      p else (fst p, sub_t x y (snd p))) ps)) _ _ eq_refl Hty2))).
    clear Hty2. 
    intros Hall1 Hty1 Hall2 Hty2. (*for better names*)
    revert Hall1 Hty1 Hall2 Hty2 Hallpats. 
    induction ps; simpl; intros; auto.
    simpl. destruct a as [p1 t1]; simpl.
    destruct (match_val_single vt v (has_type_valid gamma_valid tm v Hty2)
    (term_rep
       (substi vt v0 x
          (dom_cast (dom_aux pd) (f_equal (val vt) (eq_sym Heq))
             (v0 y))) tm v Hty2) p1) as [newval |] eqn : Hmatch.
    + revert Hall1. simpl.
      destruct (in_bool vsymbol_eq_dec x (pat_fv p1)) eqn : Hinp1.
      * intros.
        rewrite <- H with(Heq:=Heq) (Hty1:=Hty2) by solve_bnd.
        rewrite match_val_single_irrel with (Hval2:=(has_type_valid gamma_valid tm v Hty2)).
        rewrite Hmatch.
        assert (In x (map fst newval)). {
          apply (match_var_single_free_var) with(x:=x)(ty':=v) in Hmatch.
          apply Hmatch. destruct (in_bool_spec vsymbol_eq_dec x (pat_fv p1)); auto.
          inversion Hinp1.
          specialize (Hallpats (p1, t1)). apply Hallpats. left; auto.
       }
       rewrite extend_val_with_list_in; auto.
       apply term_rep_irrel.
       eapply match_val_single_typs.
       apply Hmatch.
      * intros.
        rewrite <- H with(Heq:=Heq) (Hty1:=Hty2) by solve_bnd.
        rewrite match_val_single_irrel with (Hval2:=(has_type_valid gamma_valid tm v Hty2)).
        rewrite Hmatch.
        (*Again, use other lemma*)
        assert (~In x (map fst newval)). {
          apply (match_var_single_free_var) with(x:=x)(ty':=v) in Hmatch.
          intro C.
          apply Hmatch in C. destruct (in_bool_spec vsymbol_eq_dec x (pat_fv p1)); auto.
          inversion Hinp1.
          specialize (Hallpats (p1, t1)). apply Hallpats. left; auto.
       }
       rewrite extend_val_with_list_notin; auto.
       inversion H0; subst. 
       rewrite <- H4 with(Heq:=Heq)(Hty1:=(Forall_inv Hall2));[|solve_bnd].
       f_equal. f_equal. f_equal.
       (*Need to know that y is not bound (in the list)*)
       unfold extend_val_with_list.
       destruct (get_assoc_list vsymbol_eq_dec newval y) eqn : Ha; auto.
       apply get_assoc_list_some in Ha.
       apply match_var_single_free_var with(x:=y)(ty':=v) in Hmatch.
       exfalso. apply Hfree. simpl.
       assert (In y (pat_fv p1)). apply Hmatch. rewrite in_map_iff.
       exists (y, s). split; auto.
       solve_bnd.
       specialize (Hallpats (p1, t1)). apply Hallpats. left; auto.
       eapply match_val_single_typs.
       apply Hmatch.
        (*TODO: prove this case: if var x not free in match,
          then list does not contain it, and then
          that we can rearrange the order of the substi
          (basically a bigger [substi_diff]), then we apply
          the IH (the Forall one)*)
    + revert Hall1. simpl.  
      destruct (in_bool vsymbol_eq_dec x (pat_fv p1)) eqn : Hinp1.
      * intros.
        rewrite <- H with(Heq:=Heq) (Hty1:=Hty2) by solve_bnd.
        rewrite match_val_single_irrel with (Hval2:=(has_type_valid gamma_valid tm v Hty2)).
        rewrite Hmatch.
        inversion H0; subst.
        specialize (IHps H4).
        assert (~ In y (bnd_t (Tmatch tm v ps))). solve_bnd.
          simpl in H1. apply in_app_or in H1.
          destruct H1;[left; auto |]. solve_bnd.
        specialize (IHps H1).
        inversion Hall1; subst.
        rewrite IHps with(Hall1:=(Forall_inv_tail Hall1))(Hty1:=Hty1).
        (*Need to use term_rep lemma*)
        erewrite H. reflexivity. solve_bnd.
        intros. apply Hallpats. right; auto.
      * intros.
        rewrite <- H with(Heq:=Heq) (Hty1:=Hty2) by solve_bnd.
        rewrite match_val_single_irrel with (Hval2:=(has_type_valid gamma_valid tm v Hty2)).
        rewrite Hmatch.
        inversion H0; subst.
        specialize (IHps H4).
        assert (~ In y (bnd_t (Tmatch tm v ps))). solve_bnd.
          simpl in H1. apply in_app_or in H1.
          destruct H1;[left; auto |]. solve_bnd.
        specialize (IHps H1).
        inversion Hall1; subst.
        rewrite IHps with(Hall1:=(Forall_inv_tail Hall1))(Hty1:=Hty1).
        (*Need to use term_rep lemma*)
        erewrite H. reflexivity. solve_bnd.
        intros. apply Hallpats. right; auto.
  - (*epsilon*) 
    generalize dependent Hty2. simpl. 
    destruct (vsymbol_eq_dec x v); subst; intros; simpl.
    + f_equal. apply functional_extensionality_dep. intros d.
      inversion Hty1; subst.
      rewrite substi_same.
      assert ((proj2 (ty_eps_inv (has_type_eq eq_refl Hty1))) =
      (proj2 (ty_eps_inv (has_type_eq eq_refl Hty2)))). {
        apply UIP_dec. apply vty_eq_dec.
      }
      rewrite H0.
      erewrite fmla_rep_irrel. reflexivity.
    + f_equal. apply functional_extensionality_dep. intros d.
      inversion Hty1; subst.
      rewrite substi_diff; auto.
      rewrite <- H with(Heq:=Heq)(Hval1:=H3) by solve_bnd.
      unfold substi at 5. 
      destruct (vsymbol_eq_dec y v).
      * exfalso. subst. apply Hfree. left. auto.
      * assert ((proj2 (ty_eps_inv (has_type_eq eq_refl Hty1))) =
      (proj2 (ty_eps_inv (has_type_eq eq_refl Hty2)))). {
        apply UIP_dec. apply vty_eq_dec.
      } rewrite H0. 
      
      erewrite fmla_rep_irrel. reflexivity.
  - (*predicate*)
    f_equal.
    apply get_arg_list_pred_sub; auto.
    eapply Forall_impl. 2: apply H. simpl; intros.
    apply H0. auto.
  - (*quantifiers*)
    destruct q; revert Hval2; simpl; destruct (vsymbol_eq_dec x v); 
    intros; subst; simpl;
    apply all_dec_eq.
    (*1st and 3rd cases quite similar, same for 2nd and 4th*)
    + split; intros Hall d; specialize (Hall d); revert Hall;
      rewrite substi_same; intros Hall; erewrite fmla_rep_irrel; apply Hall.
    + split; intros Hall d; specialize (Hall d); revert Hall;
      rewrite substi_diff; auto; inversion Hval1; subst;
      rewrite <- H with(Heq:=Heq) (Hval1:=H5);try solve_bnd;
      [unfold substi at 5| unfold substi at 3];
      destruct (vsymbol_eq_dec y v); 
      try solve[subst; exfalso; apply Hfree; left; reflexivity];
      intros Hrep; erewrite fmla_rep_irrel; apply Hrep.
    + split; intros [d Hex]; exists d; revert Hex;
      rewrite substi_same; intros Hex; erewrite fmla_rep_irrel; apply Hex.
    + split; intros [d Hex]; exists d; revert Hex;
      rewrite substi_diff; auto; inversion Hval1; subst;
      rewrite <- H with(Heq:=Heq) (Hval1:=H5);try solve_bnd;
      [unfold substi at 5| unfold substi at 3];
      destruct (vsymbol_eq_dec y v); 
      try solve[subst; exfalso; apply Hfree; left; reflexivity];
      intros Hrep; erewrite fmla_rep_irrel; apply Hrep.
  - (*eq*)
    apply all_dec_eq. 
    rewrite H with(Hty2:=(proj1 (valid_eq_inj (valid_formula_eq eq_refl Hval2))))
    by solve_bnd.
    rewrite H0 with (Hty2:=(proj2 (valid_eq_inj (valid_formula_eq eq_refl Hval2))))
    by solve_bnd.
    reflexivity.
  - (*binop*)
    f_equal. apply H; solve_bnd. apply H0; solve_bnd.
  - (*not*)
    f_equal. apply H. solve_bnd.
  - (*fmla let*)
    inversion Hval2; subst. 
    rewrite H with(Hty2:=H4) by solve_bnd.
    generalize dependent Hval2. simpl.
    destruct (vsymbol_eq_dec x v); simpl; intros; subst.
    + rewrite substi_same.
      erewrite term_rep_irrel.
      apply fmla_rep_irrel.
    + rewrite substi_diff;auto.
      inversion Hval1; subst.
      rewrite <- H0 with (Heq:=Heq) (Hval1:=H8) by solve_bnd.
      unfold substi at 5.
      destruct (vsymbol_eq_dec y v).
        exfalso. apply Hfree. left; auto.
      erewrite term_rep_irrel.
      apply fmla_rep_irrel.
  - (*fmla if*)
    erewrite H by solve_bnd.
    erewrite H0 by solve_bnd.
    erewrite H1 by solve_bnd.
    reflexivity.
  - (*fmla match - lots of duplication from term*)
    (*Need to know that patterns are well typed*)
    inversion Hval1; subst. clear H4 H7 H8.
    rename H6 into Hallpats.
    generalize dependent (proj1 (valid_match_inv (valid_formula_eq eq_refl Hval1))).
    generalize dependent (proj2 (valid_match_inv (valid_formula_eq eq_refl Hval1))).
    clear Hval1.
    simpl in Hval2.
    generalize dependent (proj1 (valid_match_inv (valid_formula_eq eq_refl Hval2))).
    generalize dependent (proj2 (valid_match_inv (valid_formula_eq eq_refl Hval2))).
    clear Hval2. 
    intros Hall1 Hty1 Hall2 Hty2. (*for better names*)
    revert Hall1 Hty1 Hall2 Hty2 Hallpats. 
    induction ps; simpl; intros; auto.
    simpl. destruct a as [p1 f1]; simpl.
    destruct (match_val_single vt v (has_type_valid gamma_valid tm v Hty2)
    (term_rep
       (substi vt v0 x
          (dom_cast (dom_aux pd) (f_equal (val vt) (eq_sym Heq))
             (v0 y))) tm v Hty2) p1) as [newval |] eqn : Hmatch.
    + revert Hall1. simpl.
      destruct (in_bool vsymbol_eq_dec x (pat_fv p1)) eqn : Hinp1.
      * intros.
        rewrite <- H with(Heq:=Heq) (Hty1:=Hty2) by solve_bnd.
        rewrite match_val_single_irrel with (Hval2:=(has_type_valid gamma_valid tm v Hty2)).
        rewrite Hmatch.
        assert (In x (map fst newval)). {
          apply (match_var_single_free_var) with(x:=x)(ty':=v) in Hmatch.
          apply Hmatch. destruct (in_bool_spec vsymbol_eq_dec x (pat_fv p1)); auto.
          inversion Hinp1.
          inversion Hallpats; subst. exact H3.
       }
       rewrite extend_val_with_list_in; auto.
       apply fmla_rep_irrel.
       eapply match_val_single_typs.
       apply Hmatch.
      * intros.
        rewrite <- H with(Heq:=Heq) (Hty1:=Hty2) by solve_bnd.
        rewrite match_val_single_irrel with (Hval2:=(has_type_valid gamma_valid tm v Hty2)).
        rewrite Hmatch.
        (*Again, use other lemma*)
        assert (~In x (map fst newval)). {
          apply (match_var_single_free_var) with(x:=x)(ty':=v) in Hmatch.
          intro C.
          apply Hmatch in C. destruct (in_bool_spec vsymbol_eq_dec x (pat_fv p1)); auto.
          inversion Hinp1.
          inversion Hallpats; subst. exact H4.
        }
       rewrite extend_val_with_list_notin; auto.
       inversion H0; subst. 
       rewrite <- H4 with(Heq:=Heq)(Hval1:=(Forall_inv Hall2));[|solve_bnd].
       f_equal. f_equal. f_equal.
       (*Need to know that y is not bound (in the list)*)
       unfold extend_val_with_list.
       destruct (get_assoc_list vsymbol_eq_dec newval y) eqn : Ha; auto.
       apply get_assoc_list_some in Ha.
       apply match_var_single_free_var with(x:=y)(ty':=v) in Hmatch.
       exfalso. apply Hfree. simpl.
       assert (In y (pat_fv p1)). apply Hmatch. rewrite in_map_iff.
       exists (y, s). split; auto.
       solve_bnd.
       inversion Hallpats; subst. auto.
       eapply match_val_single_typs.
       apply Hmatch.
        (*TODO: prove this case: if var x not free in match,
          then list does not contain it, and then
          that we can rearrange the order of the substi
          (basically a bigger [substi_diff]), then we apply
          the IH (the Forall one)*)
    + revert Hall1. simpl.  
      destruct (in_bool vsymbol_eq_dec x (pat_fv p1)) eqn : Hinp1.
      * intros.
        rewrite <- H with(Heq:=Heq) (Hty1:=Hty2) by solve_bnd.
        rewrite match_val_single_irrel with (Hval2:=(has_type_valid gamma_valid tm v Hty2)).
        rewrite Hmatch.
        inversion H0; subst.
        specialize (IHps H4).
        assert (~ In y (bnd_f (Fmatch tm v ps))). solve_bnd.
          simpl in H1. apply in_app_or in H1.
          destruct H1;[left; auto |]. solve_bnd.
        specialize (IHps H1).
        inversion Hall1; subst.
        rewrite IHps with(Hall1:=(Forall_inv_tail Hall1))(Hty1:=Hty1).
        (*Need to use term_rep lemma*)
        erewrite H. reflexivity. solve_bnd.
        intros. inversion Hallpats; subst. auto.
      * intros.
        rewrite <- H with(Heq:=Heq) (Hty1:=Hty2) by solve_bnd.
        rewrite match_val_single_irrel with (Hval2:=(has_type_valid gamma_valid tm v Hty2)).
        rewrite Hmatch.
        inversion H0; subst.
        specialize (IHps H4).
        assert (~ In y (bnd_f (Fmatch tm v ps))). solve_bnd.
          simpl in H1. apply in_app_or in H1.
          destruct H1;[left; auto |]. solve_bnd.
        specialize (IHps H1).
        inversion Hall1; subst.
        rewrite IHps with(Hall1:=(Forall_inv_tail Hall1))(Hty1:=Hty1).
        (*Need to use term_rep lemma*)
        erewrite H. reflexivity. solve_bnd.
        intros. inversion Hallpats; auto.
Qed.


(*The useful versions:*)
Corollary sub_t_correct (t: term) (x y: vsymbol)
  (Heq: snd x = snd y)
  (v: val_vars pd vt) (ty: vty)
  (Hty1: term_has_type sigma t ty)
  (Hty2: term_has_type sigma (sub_t x y t) ty)
  (Hfree: ~In y (bnd_t t)):
  term_rep v (sub_t x y t) ty Hty2 =
  term_rep (substi vt v x 
  (dom_cast _ (f_equal (val vt) (eq_sym Heq))
    (v y))) t ty Hty1.
Proof.
  symmetry. apply sub_correct; auto. apply Ffalse.
Qed.

Corollary sub_f_correct (f: formula)
  (x y: vsymbol) (Heq: snd x = snd y) 
  (v: val_vars pd vt)
  (Hval1: valid_formula sigma f)
  (Hval2: valid_formula sigma (sub_f x y f))
  (Hfree: ~In y (bnd_f f)):
  formula_rep v (sub_f x y f) Hval2 =
  formula_rep (substi vt v x 
    (dom_cast _ (f_equal (val vt) (eq_sym Heq))
      (v y))) f Hval1.
Proof.
  symmetry. apply sub_correct; auto. apply (Tconst (ConstInt 0)).
Qed.

(*TODO: move*)
Lemma big_union_elts {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
  {B: Type} (f: B -> list A) (l: list B) x:
  (exists y, In y l /\ In x (f y)) ->
  In x (big_union eq_dec f l).
Proof.
  induction l; simpl; auto; intros.
  - do 3 (destruct H).
  - destruct H as [y [[Hay | Hiny] Hinx]]; subst.
    + apply union_elts. left; auto.
    + apply union_elts. right. apply IHl. exists y. split; auto.
Qed. 

Lemma in_remove_iff {A: Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
  (y : A) (l: list A) (x: A):
  In x (remove eq_dec y l) <-> In x l /\ x <> y.
Proof.
  split; intros.
  - apply (in_remove eq_dec _ _ _ H).
  - apply in_in_remove; apply H.
Qed.

Lemma remove_all_elts {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
(l1 l2: list A) x:
(In x l2 /\ ~In x l1) <-> In x (remove_all eq_dec l1 l2).
Proof.
  induction l1; simpl; split; intros; auto.
  destruct H; auto.
  - destruct H as [Hinx Hnot].
    destruct (eq_dec x a); subst; auto.
    + exfalso. apply Hnot; left; auto.
    + rewrite in_remove_iff, <- IHl1. split_all; auto.
  - rewrite in_remove_iff in H. destruct H.
    apply IHl1 in H. split_all; auto.
    intro C. destruct C; subst; contradiction.
Qed.

(*TODO: move*)
Lemma extend_val_with_list_in_eq
  (v1 v2: val_vars pd vt) l x
  (Htys: forall (x : vsymbol) t,
  In (x, t) l -> projT1 t = snd x):
  In x (map fst l) ->
  extend_val_with_list vt v1 l x =
  extend_val_with_list vt v2 l x.
Proof.
  intros Hin.
  unfold extend_val_with_list.
  destruct (get_assoc_list vsymbol_eq_dec l x) eqn : Hassoc.
  + apply get_assoc_list_some in Hassoc.
    apply Htys in Hassoc.
    destruct (vty_eq_dec (snd x) (projT1 s)); auto; try contradiction.
    rewrite Hassoc in n; contradiction.
  + rewrite get_assoc_list_none in Hassoc. contradiction.
Qed.

(*TODO: rename*)
Lemma extend_val_with_list_notin'  (vv : val_vars pd vt) 
(x : vsymbol) (d : domain (val vt (snd x)))
(l : list (vsymbol * {t : vty & domain (val vt t)})):
~ In x (map fst l) ->
extend_val_with_list vt vv l x = vv x.
Proof.
  intros. unfold extend_val_with_list.
  rewrite <- get_assoc_list_none in H.
  rewrite H.
  reflexivity.
Qed.

(*
Lemma extend_val_with_list_notin_eq
  (v1 v2: val_vars pd vt) l x
  (Hvs: v1 x = v2 x):
  extend_val_with_list vt v1 l x =
  extend_val_with_list vt v2 l x.
Proof.
  unfold extend_val_with_list.
  destruct (in_bool_spec vsymbol_eq_dec x (map fst l)).
  - destruct (get_assoc_list vsymbol_eq_dec l x) eqn : Hassoc.
    + destruct (vty_eq_dec (snd x) (projT1 s)); auto.
    + rewrite get_assoc_list_none in Hassoc. contradiction.
  - rewrite <- get_assoc_list_none in n. rewrite n. auto.
Qed.*)
  
(*Other lemma we need: a term/formula is interpreted the
  same on all valuations that agree on the free variables*)
Lemma val_fv_agree (t: term) (f: formula) :
(forall (v1 v2: val_vars pd vt) (ty: vty) 
  (Hty: term_has_type sigma t ty),
  (forall x, In x (term_fv t) -> v1 x = v2 x) ->
  term_rep v1 t ty Hty = term_rep v2 t ty Hty) /\
(forall (v1 v2: val_vars pd vt) 
  (Hval: valid_formula sigma f),
  (forall x, In x (form_fv f) -> v1 x = v2 x) ->
  formula_rep v1 f Hval = formula_rep v2 f Hval).
Proof.
  revert t f.
  apply term_formula_ind; simpl; intros; auto.
  - f_equal. unfold var_to_dom. apply H. left; auto.
  - f_equal. f_equal. f_equal.
    apply get_arg_list_eq.
    rewrite Forall_forall. intros.
    rewrite Forall_forall in H.
    rewrite term_rep_irrel with (Hty2:=Hty2).
    apply H; intros; auto.
    apply H0.
    apply big_union_elts. exists x; auto.
  - apply H0. intros x Hinx.
    unfold substi. destruct (vsymbol_eq_dec x v); auto; subst.
    f_equal. apply H. intros. apply H1. rewrite union_elts. left; auto.
    apply H1. rewrite union_elts. right.
    apply in_in_remove; auto.
  - rewrite (H _ v2). 
    rewrite (H0 _ v2).
    rewrite (H1 _ v2).
    reflexivity.
    all: intros x Hinx; apply H2; rewrite !union_elts; solve_bnd.
  - generalize dependent (proj2 (ty_match_inv (has_type_eq eq_refl Hty))).
    generalize dependent (proj1 (ty_match_inv (has_type_eq eq_refl Hty))).
    inversion Hty; subst.
    clear Hty H5 H9 H10. revert H7; intros Hallpats; revert Hallpats.
    induction ps; simpl; auto; intros.
    destruct a.
    inversion H0; subst.
    rewrite (H v1 v2) at 1.
    destruct (match_val_single vt v (has_type_valid gamma_valid tm v t) (term_rep v2 tm v t) p) eqn : Hm;
    [|apply IHps].
    + apply H4.
      intros.
      destruct (in_bool_spec vsymbol_eq_dec x (map fst l)).
      *
      (*Need to know about [extend_val_with_list]*)
      apply extend_val_with_list_in_eq.
      apply (match_val_single_typs _ _ _ _ _ _ Hm). auto.
      * (*Now, need to know that map fst l = free vars of p (elementwise)*)
        rewrite !extend_val_with_list_notin'; auto.
        apply H1.
        apply union_elts. right.
        apply big_union_elts.
        exists (p, t0). split; auto. left; auto.
        simpl. apply remove_all_elts.
        split; auto.
        assert (pattern_has_type sigma p v). {
          apply (Hallpats (p, t0)). left; auto.
        }
        rewrite (match_var_single_free_var _ _ _ _ _ _ _ H3 Hm); auto.
    + auto.
    + intros x Hinx.
      apply H1. simpl.
      revert Hinx. rewrite !union_elts; intros.
      destruct Hinx as [Hin1 | Hinx]; [left; auto | right; right; auto].
    + intros. apply Hallpats. right; auto.
    + intros. apply H1. simpl. rewrite union_elts. left; auto.
  - f_equal. apply functional_extensionality_dep; intros.
    erewrite H. reflexivity.
    intros y Hiny.
    unfold substi.
    destruct (vsymbol_eq_dec y v); auto.
    apply H0. apply in_in_remove; auto.
  - f_equal. (*TODO: [get_arg_list_pre] lemma*)
    apply get_arg_list_pred_eq.
    rewrite Forall_forall. intros.
    rewrite Forall_forall in H.
    rewrite term_rep_irrel with (Hty2:=Hty2).
    apply H; intros; auto.
    apply H0.
    apply big_union_elts. exists x; auto.
  - destruct q; apply all_dec_eq.
    + split; intros Hall d; specialize (Hall d);
      erewrite H; try solve[apply Hall]; intros x Hinx;
      unfold substi; destruct (vsymbol_eq_dec x v); auto;
      [symmetry|]; apply H0; apply in_in_remove; auto.
    + split; intros [d Hex]; exists d;
      erewrite H; try solve[apply Hex]; intros x Hinx;
      unfold substi; destruct (vsymbol_eq_dec x v); auto;
      [symmetry|]; apply H0; apply in_in_remove; auto.
  - apply all_dec_eq. rewrite (H _ v2). rewrite (H0 _ v2).
    reflexivity.
    all: intros x Hinx; apply H1; rewrite union_elts; auto.
  - f_equal.
    + apply H; intros x Hinx. apply H1. rewrite union_elts. auto.
    + apply H0. intros x Hinx. apply H1. rewrite union_elts. auto.
  - f_equal. apply H. intros x Hinx. apply H0. auto.
  - apply H0. intros x Hinx.
    unfold substi. destruct (vsymbol_eq_dec x v); auto.
    + f_equal. apply H. intros y Hiny. apply H1.
      rewrite union_elts. auto.
    + apply H1. rewrite union_elts. right.
      apply in_in_remove; auto.
  - rewrite (H _ v2).
    rewrite (H0 _ v2).
    rewrite (H1 _ v2).
    reflexivity. 
    all: intros x Hinx; apply H2; rewrite !union_elts; auto.
  - generalize dependent (proj2 (valid_match_inv (valid_formula_eq eq_refl Hval))).
    generalize dependent (proj1 (valid_match_inv (valid_formula_eq eq_refl Hval))).
    inversion Hval; subst.
    clear Hval H5 H8 H9. revert H7; intros Hallpats; revert Hallpats.
    induction ps; simpl; auto; intros.
    destruct a.
    inversion H0; subst.
    rewrite (H v1 v2) at 1.
    destruct (match_val_single vt v (has_type_valid gamma_valid tm v t) (term_rep v2 tm v t) p) eqn : Hm;
    [|apply IHps].
    + apply H4.
      intros.
      destruct (in_bool_spec vsymbol_eq_dec x (map fst l)).
      * apply extend_val_with_list_in_eq.
        apply (match_val_single_typs _ _ _ _ _ _ Hm). auto.
      * rewrite !extend_val_with_list_notin'; auto.
        apply H1.
        apply union_elts. right.
        apply big_union_elts.
        exists (p, f0). split; auto. left; auto.
        simpl. apply remove_all_elts.
        split; auto.
        inversion Hallpats; subst.
        rewrite (match_var_single_free_var _ _ _ _ _ _ _ H7 Hm); auto.
    + auto.
    + intros x Hinx.
      apply H1. simpl.
      revert Hinx. rewrite !union_elts; intros.
      destruct Hinx as [Hin1 | Hinx]; [left; auto | right; right; auto].
    + intros. inversion Hallpats; subst; auto.
    + intros. apply H1. simpl. rewrite union_elts. left; auto.
Qed. 

(*Corollaries:*)
Corollary term_fv_agree (t: term)
  (v1 v2: val_vars pd vt) (ty: vty) 
  (Hty: term_has_type sigma t ty):
  (forall x, In x (term_fv t) -> v1 x = v2 x) ->
  term_rep v1 t ty Hty = term_rep v2 t ty Hty.
Proof.
  intros. apply val_fv_agree; auto. apply Ftrue.
Qed.

Corollary form_fv_agree (f: formula)
  (v1 v2: val_vars pd vt) 
  (Hval: valid_formula sigma f):
  (forall x, In x (form_fv f) -> v1 x = v2 x) ->
  formula_rep v1 f Hval = formula_rep v2 f Hval.
Proof.
  intros. apply val_fv_agree; auto. apply (Tconst (ConstInt 0)).
Qed.

(*The interpretation of any 
  closed term is equivalent under any valuation*)
Corollary term_closed_val (t: term)
  (v1 v2: val_vars pd vt) (ty: vty)
  (Hty: term_has_type sigma t ty):
  closed_term t ->
  term_rep v1 t ty Hty = term_rep v2 t ty Hty.
Proof.
  unfold closed_term. intros.
  apply term_fv_agree; intros.
  destruct (term_fv t); inversion H; inversion H0.
Qed.

Corollary fmla_closed_val (f: formula)
  (v1 v2: val_vars pd vt) 
  (Hval: valid_formula sigma f):
  closed_formula f ->
  formula_rep v1 f Hval = formula_rep v2 f Hval.
Proof.
  unfold closed_formula; intros.
  apply form_fv_agree; intros.
  destruct (form_fv f); inversion H; inversion H0.
Qed.

(*With this we can prove: we can rename the variables in a quantifier
  to a new variable without changing the truth value*)
(*The proof is a straightforward application of [sub_f_correct]
  and [form_fv_agree], but the casts make it a bit tedious*)
Lemma alpha_convert_quant (v: val_vars pd vt) 
  (q: quant) (v1 v2: vsymbol) (Heq: snd v1 = snd v2) (f: formula)
  (Hval1: valid_formula sigma (Fquant q v1 f))
  (Hval2: valid_formula sigma (Fquant q v2 (sub_f v1 v2 f)))
  (Hbnd: ~In v2 (bnd_f f))
  (Hfree: ~In v2 (form_fv f)):
  formula_rep v (Fquant q v1 f) Hval1 = 
  formula_rep v (Fquant q v2 (sub_f v1 v2 f)) Hval2.
Proof.
  remember (snd v1) as ty.
  simpl. destruct q.
  - apply all_dec_eq.
    split; intros Hall d.
    + inversion Hval1; subst.
      rewrite sub_f_correct with(Heq:=Heq)(Hval1:=H4); auto.
      rewrite (form_fv_agree _ _ (substi vt v v1 (dom_cast (dom_aux pd) (f_equal (val vt) (eq_sym Heq))
      (substi vt v v2 d v2)))).
      2: {
        intros x Hinx. unfold substi. destruct (vsymbol_eq_dec x v2); auto.
        subst. contradiction.
      }
      erewrite fmla_rep_irrel. apply Hall.
    + revert Heq Heqty. inversion Hval1; subst. intros Heq Heqty.
      specialize (Hall (dom_cast _ (f_equal (val vt) (eq_sym (eq_trans (eq_sym Heq) Heqty))) d)).
      revert Hall.
      rewrite sub_f_correct with (Heq:=(eq_sym (eq_trans (eq_sym Heq) Heqty)))(Hval1:=H4); auto.
      rewrite (form_fv_agree _ _ (substi vt v v1 d)); auto.
      * rewrite (fmla_rep_irrel _ _   _ (valid_quant_inj (valid_formula_eq eq_refl Hval1))).
        auto.
      * (*Proof is annoying casting/dependent equality stuff*)
        intros x Hinx. unfold substi.
        destruct (vsymbol_eq_dec x v1). 
        -- unfold eq_rec_r, eq_rec, eq_rect.
          revert Heq Heqty; subst; intros Heq Heqty.
          simpl. unfold dom_cast. subst. simpl. destruct Heqty.
          simpl. destruct (vsymbol_eq_dec v2 v2); auto; try contradiction.
          assert (e = eq_refl). apply UIP_dec. apply vsymbol_eq_dec.
          subst. reflexivity.
        -- destruct (vsymbol_eq_dec x v2); auto.
          subst. contradiction.
  - apply all_dec_eq.
    split; intros [d Hex].
    + exists (dom_cast _ (f_equal (val vt) (eq_sym (eq_trans (eq_sym Heq) Heqty))) d).
      rewrite sub_f_correct with (Heq:=(eq_sym (eq_trans (eq_sym Heq) Heqty))) 
        (Hval1:= (valid_quant_inj (valid_formula_eq eq_refl Hval1))); auto.
      rewrite (form_fv_agree _ _ (substi vt v v1 d)); auto.
      intros x Hinx.
      unfold substi.
      destruct (vsymbol_eq_dec x v1); auto.
      * unfold eq_rec_r, eq_rec, eq_rect. revert Heq Heqty; subst;
        intros Heq Heqty; simpl.
        unfold dom_cast. clear Hex. subst; simpl; destruct Heqty; simpl.
        destruct (vsymbol_eq_dec v2 v2); try contradiction.
        assert (e = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        rewrite H; reflexivity.
      * destruct (vsymbol_eq_dec x v2); auto.
        subst; contradiction.
    + (*TODO: lots of similarities*)
      exists (dom_cast _ (f_equal (val vt) (eq_trans (eq_sym Heq) Heqty)) d).
      revert Hex.
      rewrite sub_f_correct with (Heq:= (eq_sym (eq_trans (eq_sym Heq) Heqty))) 
        (Hval1:= (valid_quant_inj (valid_formula_eq eq_refl Hval1))); auto.
      rewrite (form_fv_agree _ _ (substi vt v v1
      (dom_cast (dom_aux pd)
         (f_equal (val vt) (eq_trans (eq_sym Heq) Heqty)) d))); auto.
      intros x Hinx.
      unfold substi.
      destruct (vsymbol_eq_dec x v1); auto.
      * unfold eq_rec_r, eq_rec, eq_rect. revert Heq Heqty; subst;
        intros Heq Heqty; simpl.
        unfold dom_cast. subst; simpl; destruct Heqty; simpl.
        destruct (vsymbol_eq_dec v2 v2); try contradiction.
        assert (e = eq_refl) by (apply UIP_dec; apply vsymbol_eq_dec).
        rewrite H; reflexivity.
      * destruct (vsymbol_eq_dec x v2); auto.
        subst; contradiction.
Qed.

Definition split {A: Type} (l: list A) (i: nat) : (list A * list A) :=
  (firstn i l, skipn i l).

Lemma split_app {A: Type} (l: list A) (i: nat) :
  l = (fst (split l i)) ++ (snd (split l i)).
Proof.
  simpl. rewrite firstn_skipn. auto.
Qed. 

(*
Definition sublist {A: Type} (l: list A) (lo hi: nat) : list A.
Admitted.*)

(*Split a list into pieces of the appropriate lengths if we can*)
Fixpoint split_lens {A: Type} (l: list A) (lens: list nat) :
  list (list A) :=
  match lens with
  | len :: tl =>
    (fst (split l len)) ::
    split_lens (snd (split l len)) tl
  | nil => nil
  end.

Definition sum (l: list nat) : nat :=
  fold_right (fun x y => x + y) 0 l.

Lemma length_concat {A: Type} (l: list (list A)):
  length (concat l) = sum (map (@length A) l).
Proof.
  induction l; simpl; auto.
  rewrite app_length, IHl; auto.
Qed.

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
  rewrite skipn_length, <- H.
  rewrite minus_plus; auto.
Qed.

Lemma NoDup_firstn {A: Type} (l: list A) (n: nat) :
  NoDup l ->
  NoDup (firstn n l).
Proof.
  rewrite <- (firstn_skipn n) at 1.
  rewrite NoDup_app_iff; intros; split_all; auto.
Qed.

Lemma NoDup_skipn {A: Type} (l: list A) (n: nat) :
  NoDup l ->
  NoDup (skipn n l).
Proof.
  rewrite <- (firstn_skipn n) at 1.
  rewrite NoDup_app_iff; intros; split_all; auto.
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
    + rewrite skipn_length, <- H.
      rewrite minus_plus; auto.
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
    rewrite skipn_length, <- H.
    rewrite minus_plus; auto.
Qed.

Lemma In_firstn {A: Type} (l: list A) (n: nat) x :
  In x (firstn n l) ->
  In x l.
Proof.
  rewrite <- (firstn_skipn n l) at 2; intros.
  apply in_or_app; left; auto.
Qed.

Lemma In_skipn {A: Type} (l: list A) (n: nat) x :
  In x (skipn n l) ->
  In x l.
Proof.
  rewrite <- (firstn_skipn n l) at 2; intros.
  apply in_or_app; right; auto.
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

(*If we know that the bound variable names are unique and do
  not conflict with the free variable names, we can prove the
  correctness of many transformations. We define such a notion
  and provide a function (not necessarily the most efficient one)
  to alpha-convert our term/formula into this form.*)
(*TODO: make names consistent*)
Definition term_wf (t: term) : Prop :=
  NoDup (bnd_t t) /\ forall x, ~ (In x (term_fv t) /\ In x (bnd_t t)).
Definition fmla_wf (f: formula) : Prop :=
  NoDup (bnd_f f) /\ forall x, ~ (In x (form_fv f) /\ In x (bnd_f f)).

  Lemma wf_quant (q: quant) (v: vsymbol) (f: formula) :
  fmla_wf (Fquant q v f) ->
  fmla_wf f.
Proof.
  unfold fmla_wf. simpl. intros. split_all.
  - inversion H; auto.
  - intros x C. split_all.
    apply (H0 x).
    destruct (vsymbol_eq_dec x v); subst; auto.
    + inversion H; subst. contradiction.
    + split. apply in_in_remove; auto. right; auto.
Qed. 

Lemma wf_binop (b: binop) (f1 f2: formula) :
  fmla_wf (Fbinop b f1 f2) ->
  fmla_wf f1 /\ fmla_wf f2.
Proof.
  unfold fmla_wf. simpl. rewrite NoDup_app_iff.
  intros. split_all; auto; intros x C; split_all.
  - apply (H0 x).
    split_all. apply union_elts. left; auto.
    apply in_or_app. left; auto.
  - apply (H0 x).
    split_all. apply union_elts. right; auto.
    apply in_or_app. right; auto.
Qed.

Lemma wf_let (t: term) (v: vsymbol) (f: formula) :
  fmla_wf (Flet t v f) ->
  fmla_wf f.
Proof.
  unfold fmla_wf. simpl. intros; split_all; auto; 
  inversion H; subst; auto.
  - rewrite NoDup_app_iff in H4; apply H4.
  - intros x C. split_all.
    apply (H0 x). split.
    + apply union_elts. right.
      apply in_in_remove; auto. intro Heq; subst.
      inversion H; subst.
      apply H7. apply in_or_app. right; auto.
    + right. apply in_or_app. right; auto.
Qed.

(*Easier to have separate function for pattern*)
(*Hmm, need to think a bit more - how should patterns work?
  *)

(*TODO: want bound variables for patterns because we care about
  lengths*)
Check get_assoc_list.
(*Alpha substitute for patterns only in the given term/formula*)
(*Here, we need to keep the dependencies between pattern variables
  (as, for instance, an "or" pattern should have the same free
  vars on each side, so we use an association list)*)
Fixpoint alpha_p_aux {A: Type} (sub: vsymbol -> vsymbol -> A -> A) 
  (p: pattern) (x: A) (l: list (vsymbol * string)) : (pattern * A) :=
  match p with
  | Pvar v => 
    match (get_assoc_list vsymbol_eq_dec l v) with
    | Some str => 
      let v' := (str, snd v) in
      (Pvar v', sub v v' x)
    | None => (p, x)
    end
  | Pwild => (p, x)
  | Por p1 p2 =>
    (*NOTE: must have same free vars*)
    let t1 := alpha_p_aux sub p1 x l in
    let t2 := alpha_p_aux sub p2 x l in
    (Por (fst t1) (fst t2), (snd t2))
  | Pbind p1 v =>
    match (get_assoc_list vsymbol_eq_dec l v) with
    | Some str =>
      let v' := (str, snd v) in
      let t := (alpha_p_aux sub p1 x l) in
      (Pbind (fst t) v', sub v v' (snd t))
    | None => (p, x)
    end
  | Pconstr f tys pats =>
    let t := 
    ((fix alpha_ps_aux (l1: list pattern) (y: A) : list pattern * A :=
      match l1 with
      | ph :: pt =>
        let t1 := alpha_p_aux sub ph y l in
        let t2 := alpha_ps_aux pt (snd t1) in
        ((fst t1) :: (fst t2), (snd t2))
      | nil => (nil, y)
      end) pats x) in
    (Pconstr f tys (fst t), (snd t))
    end.
(*Proving this correct will not be too fun, but let's see*)

(*This awkward definition satisfies Coq's positivity checker
  for nested induction, unlike the normal one*)
Definition map2 {A B C: Type} :=
  fun (f: A -> B -> C) =>
    fix map2 (l1: list A) : list B -> list C :=
      match l1 with
      | nil => fun l2 => nil
      | x1 :: t1 =>
        fun l2 =>
        match l2 with
        | nil => nil
        | x2 :: t2 => f x1 x2 :: map2 t1 t2
        end
      end.

Lemma in_map2_iff {A B C: Type} (f: A -> B -> C) (l1: list A) 
  (l2: list B) (d1: A) (d2: B) (x: C) :
  length l1 = length l2 ->
  In x (map2 f l1 l2) <->
  (exists (i: nat), i < length l1 /\ x = f (nth i l1 d1) (nth i l2 d2)).
Proof.
  revert l2. induction l1; simpl; intros; destruct l2; inversion H; subst;
  split; intros; auto.
  - destruct H0.
  - destruct H0; lia.
  - simpl in H0. destruct H0; subst.
    + exists 0. split; auto. lia.
    + apply IHl1 in H0; auto.
      destruct H0 as [i1 [Hi1 Hx]]; subst.
      exists (S i1); split; auto; try lia.
  - simpl. destruct H0 as [i [Hi Hx]]; subst.
    destruct i; simpl. left; auto. right.
    apply IHl1; auto. simpl. exists i; split; auto; try lia.
Qed.

Lemma map2_length {A B C: Type} (f: A -> B -> C) l1 l2:
  length (map2 f l1 l2) = Nat.min (length l1) (length l2).
Proof.
  revert l2. induction l1; simpl; intros; destruct l2; simpl; auto.
Qed.

Lemma map2_length_eq {A B C: Type} (f: A -> B -> C) l1 l2:
  length l1 = length l2 ->
  length (map2 f l1 l2) = length l1.
Proof.
  intros Heq. rewrite map2_length, Heq, Nat.min_id; auto.
Qed. 

Lemma map2_nth {A B C: Type} (f: A -> B -> C) (l1: list A) (l2: list B)
  (d1: A) (d2: B) (d3: C) (n: nat):
  length l1 = length l2 ->
  n < length l1 ->
  nth n (map2 f l1 l2) d3 = f (nth n l1 d1) (nth n l2 d2).
Proof.
  revert l2 n. induction l1; simpl; intros; destruct l2; simpl; auto;
  try lia; inversion H.
  destruct n; auto.
  apply IHl1; auto. lia.
Qed.

      (*
      fun l2 =>
      match l

Fixpoint map2 {A B C: Type} (f: A -> B -> C) (l1 : list A) (l2: list B)
  {struct l1} : list C :=
  match l1, l2 with
  | x1 :: t1, x2 :: t2 => f x1 x2 :: map2 f t1 t2
  | _, _ => nil
  end.

  Print map.
  Print map2.*)
Print formula.

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
        alpha_p_aux sub_t (fst x) t2  (combine (pat_fv (fst x)) l1)
        ) ps l_split)
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
        alpha_p_aux sub_f (fst x) f2  (combine (pat_fv (fst x)) l1)
        ) ps l_split)
  | _ => f (*No other bound/recursive cases*)
  end.

(*Prove correctness: 3 lemmas
  1. results in wf term/fmla
  2. preserves interp
  3. has same "shape" (and corollaries: ind form, positive, etc)*)

Lemma NoDup_concat_iff {A: Type} (l: list (list A)) :
  NoDup (concat l) <->
  ((forall x, In x l -> NoDup x) /\
  (forall i1 i2 (d: list A) x, i1 < length l -> i2 < length l ->
    i1 <> i2 -> ~ (In x (nth i1 l d) /\ In x (nth i2 l d)))).
Proof.
  induction l; simpl; split; intros; auto.
  - split.
    + intros x [].
    + intros. lia.
  - constructor.
  - rewrite NoDup_app_iff in H.
    split_all; rewrite IHl in H0; split_all.
    + intros x [Hax | Hinx]; subst; auto.
    + intros i1 i2 d x Hi1 Hi2 Hneq.
      destruct i1; destruct i2; try contradiction; intro C; split_all.
      * apply (H1 x); auto.
        rewrite in_concat. exists (nth i2 l d). split; auto.
        apply nth_In; lia.
      * apply (H1 x); auto. rewrite in_concat.
        exists (nth i1 l d); split; auto.
        apply nth_In; lia.
      * apply (H3 i1 i2 d x); auto; try lia.
  - split_all.
    rewrite NoDup_app_iff. split_all; auto.
    + apply IHl. split_all; auto.
      intros i1 i2 d x Hi1 Hi2 Hi12. 
      apply (H0 (S i1) (S i2) d x); lia. 
    + intros x Hinx.
      rewrite in_concat. intros [l1 [Hinl1 Hinxl1]].
      destruct (In_nth _ _ nil Hinl1) as [i2 [Hi2 Hnth]].
      apply (H0 0 (S i2) nil x); subst; auto; try lia.
    + intros x Hinxc Hinx.
      rewrite in_concat in Hinxc. destruct Hinxc as [l2 [Hinl2 Hinxl2]].
      destruct (In_nth _ _ nil Hinl2) as [i2 [Hi2 Hnth]].
      apply (H0 0 (S i2) nil x); subst; auto; try lia.
Qed.

(*Default term*)
Definition tm_d : term := Tconst (ConstInt 0).

(*Need to know that sub_t and sub_f do not change bound variables*)

Lemma sub_bound_eq (t: term) (f: formula) :
  (forall x y,
    bnd_t (sub_t x y t) = bnd_t t) /\
  (forall x y,
    bnd_f (sub_f x y f) = bnd_f f).
Proof.
  revert t f. apply term_formula_ind; simpl; auto; intros.
  - f_equal. rewrite map_map. apply map_ext_in_iff.
    rewrite Forall_forall in H.
    intros. apply H; auto.
  - f_equal. destruct (vsymbol_eq_dec x v); subst; simpl;
    rewrite H; f_equal; apply H0.
  - rewrite H, H0, H1; auto.
  - rewrite H. f_equal.
    f_equal. rewrite map_map.
    apply map_ext_in_iff. intros.
    destruct (in_bool vsymbol_eq_dec x (pat_fv (fst a))); subst; simpl;
    auto.
    rewrite Forall_forall in H0. rewrite H0; auto.
    rewrite in_map_iff. exists a. auto.
  - destruct (vsymbol_eq_dec x v); subst; simpl; f_equal; apply H.
  - f_equal. rewrite map_map. apply map_ext_in_iff. intros.
    rewrite Forall_forall in H. apply H; auto.
  - destruct (vsymbol_eq_dec x v); simpl; auto; f_equal; apply H.
  - rewrite H, H0; reflexivity.
  - rewrite H, H0; reflexivity.
  - rewrite H; f_equal; f_equal. destruct (vsymbol_eq_dec x v); auto;
    apply H0.
  - rewrite H, H0, H1; reflexivity.
  - rewrite H. f_equal. f_equal. rewrite map_map.
    apply map_ext_in_iff; intros.
    destruct (in_bool vsymbol_eq_dec x (pat_fv (fst a))); auto; simpl.
    rewrite Forall_forall in H0.
    rewrite H0; auto. rewrite in_map_iff. exists a; auto.
Qed.

Lemma bnd_sub_t (t: term):
(forall x y,
  bnd_t (sub_t x y t) = bnd_t t).
Proof.
  apply sub_bound_eq. apply Ftrue.
Qed.

Lemma bnd_sub_f (f: formula):
  forall x y,
    bnd_f (sub_f x y f) = bnd_f f.
Proof.
  apply sub_bound_eq. apply (Tconst (ConstInt 0)).
Qed.

Lemma nodup_firstn_skipn {A: Type} {l: list A} {n} {x: A} :
  In x (firstn n l) ->
  In x (skipn n l) ->
  NoDup l ->
  False.
Proof.
  rewrite <- (firstn_skipn n l) at 3. rewrite NoDup_app_iff.
  intros; split_all.
  apply H3 in H0. contradiction. auto.
Qed.

Lemma NoDup_app_iff' {A: Type} (l1 l2: list A):
  NoDup (l1 ++ l2) <->
  NoDup l1 /\
  NoDup l2 /\
  (forall x, ~ (In x l1 /\ In x l2)).
Proof.
  rewrite NoDup_app_iff. repeat apply and_iff_compat_l.
  split; intros; try intro; split_all; intros; try intro.
  - apply H in H0. contradiction.
  - apply (H x); auto.
  - apply (H x); auto.
Qed.

Lemma NoDup_pat_fv (p: pattern) : NoDup (pat_fv p).
Proof.
  induction p; simpl; try constructor; auto.
  - constructor.
  - apply big_union_nodup.
  - apply union_nodup; auto.
  - apply union_nodup; auto. constructor; auto. constructor.
Qed.
(*TODO: see if we need*)
Lemma alpha_p_aux_wf_aux_gen {A: Type} (p: pattern) 
  (sub: vsymbol -> vsymbol -> A -> A) :
  (forall (l: list (vsymbol * string)),
    (*NoDup (map snd l) ->*)
    (forall v, In v (pat_fv p) -> In v (map fst l)) ->
    (*NoDup (map fst l) ->*)
    (forall x v, In v (pat_fv (fst (alpha_p_aux sub p x l))) ->
      exists v', In (v', (fst v)) l /\
        In v' (pat_fv p))).
Proof.
  intros l (*Hnodups*) Hfvs (*Hnodupf*).
  induction p; simpl; auto; intros.
  - destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha.
    + simpl in H. destruct H as [Heq | []]; subst; simpl.
      apply get_assoc_list_some in Ha.
      exists v. auto.
    + apply get_assoc_list_none in Ha. simpl in H.
      destruct H as [Heq | []]; subst.
      exfalso. apply Ha. apply (Hfvs v0); auto. simpl; auto.
  - generalize dependent x. induction ps; simpl in *; auto; intros. 
    destruct H0.
    inversion H; subst.
    rewrite union_elts in H0. destruct H0.
    + assert (Hv: exists v', In (v', fst v) l /\ In v' (pat_fv a)). {
        apply H3 with(x:=x); auto. intros. apply Hfvs.
        rewrite union_elts. left; auto.
      }
      destruct Hv as [v' [Hinl Hinv']].
      exists v'. split; auto. rewrite union_elts. left; auto.
    + assert (Hv: exists v' : vsymbol,
        In (v', fst v) l /\ In v' (big_union vsymbol_eq_dec pat_fv ps)). {
        apply IHps with (x:=(snd (alpha_p_aux sub a x l))); auto.
        intros. apply Hfvs. rewrite union_elts. right; auto.
      }
      destruct Hv as [v' [Hinl Hinv']]; subst.
      exists v'. split; auto. rewrite union_elts. right; auto.
  - destruct H.
  - rewrite union_elts in H.
    destruct H.
    + assert (Hv: exists v' : vsymbol, In (v', fst v) l /\ In v' (pat_fv p1)). {
        apply IHp1 with(x:=x); auto. intros. apply Hfvs; simpl;
        rewrite union_elts; left; auto.
      }
      destruct Hv as [v' [Hinl Hinv']].
      exists v'. split; auto. rewrite union_elts. left; auto.
    + assert (Hv: exists v' : vsymbol, In (v', fst v) l /\ In v' (pat_fv p2)). {
        apply IHp2 with(x:=x); auto.
        intros; apply Hfvs; simpl; rewrite union_elts; right; auto.
      } destruct Hv as [v' [Hinl Hinv']]; subst.
      exists v'. split; auto. rewrite union_elts; right; auto. 
  - destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha.
    + simpl in H. rewrite union_elts in H.
      destruct H as [Hinv | [Heq | []]]; subst.
      * apply IHp with(x:=x) in Hinv.
        destruct Hinv as [v' [Hl Hv']].
        exists v'; split; auto. rewrite union_elts; left; auto.
        intros. apply Hfvs; simpl; rewrite union_elts; left; auto.
      * apply get_assoc_list_some in Ha.
        exists v. split; auto. rewrite union_elts; right; auto.
        left; auto.
    + simpl in H. apply get_assoc_list_none in Ha.
      exfalso. apply Ha. apply Hfvs. simpl. auto.
      rewrite union_elts. right; left; auto.
Qed. 

Lemma nodup_fst_inj {A B: Type} {l: list (A * B)} {x: A} {y1 y2: B} :
  NoDup (map fst l) ->
  In (x, y1) l ->
  In (x, y2) l ->
  y1 = y2.
Proof.
  induction l; simpl; auto.
  - intros _ [].
  - intros. inversion H; subst.
    destruct H0; destruct H1; subst; auto.
    + inversion H1; subst; auto.
    + exfalso. apply H4. simpl. rewrite in_map_iff. 
      exists (x, y2); simpl; auto.
    + exfalso. apply H4. rewrite in_map_iff. exists (x, y1); auto.
Qed.  

Lemma nodup_snd_inj {A B: Type} {l: list (A * B)} {x1 x2: A} {y: B} :
  NoDup (map snd l) ->
  In (x1, y) l ->
  In (x2, y) l ->
  x1 = x2.
Proof.
  induction l; simpl; auto.
  - intros _ [].
  - intros. inversion H; subst.
    destruct H0; destruct H1; subst; auto.
    + inversion H1; subst; auto.
    + exfalso. apply H4. simpl. rewrite in_map_iff. 
      exists (x2, y); simpl; auto.
    + exfalso. apply H4. rewrite in_map_iff. exists (x1, y); auto.
Qed.  

(*Other direction*)
Lemma alpha_p_aux_wf_aux_gen' {A: Type} (p: pattern) 
  (sub: vsymbol -> vsymbol -> A -> A) :
  (forall (l: list (vsymbol * string)),
    NoDup (map fst l) ->
    (forall v, In v (pat_fv p) -> In v (map fst l)) ->
    (forall x d, 
      In x (pat_fv (fst (alpha_p_aux sub p d l))) <->
      exists v str, 
        In (v, str) l /\
        In v (pat_fv p) /\
        snd x = snd v /\
        fst x = str)).
Proof.
  intros l Hnodup Hfvs (*Hnodupf*).
  induction p; simpl; auto; intros.
  - destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha; simpl; split; intros.
    + destruct H as [Heq | []]; subst; simpl.
      apply get_assoc_list_some in Ha.
      exists v. exists s. split; auto.
    + destruct H as [v1 [str [Hinl [[Heq | []] [Hsnd Hfst]]]]]; subst.
      left. destruct x; simpl in *; subst.
      f_equal. symmetry.
      apply get_assoc_list_some in Ha. 
      apply (nodup_fst_inj Hnodup Hinl Ha).
    + apply get_assoc_list_none in Ha.
      destruct H as [Heq | []]; subst.
      exfalso. apply Ha. apply Hfvs. left; auto.
    + apply get_assoc_list_none in Ha.
      destruct H as [v1 [str [Hinl [[Heq | []] [Hsnd Hfst]]]]]; subst.
      exfalso. apply Ha. rewrite in_map_iff. exists (v1, fst x); auto.
  - generalize dependent d. induction ps; simpl in *; auto; intros; 
    [split; simpl; intros; auto |].
    + destruct H0.
    + destruct H0 as [v1 [str [Hinl [[] _]]]].
    + assert (Hfvs': (forall v : vsymbol,
      In v (big_union vsymbol_eq_dec pat_fv ps) -> In v (map fst l))).
      {
        intros; apply Hfvs; simpl; rewrite union_elts; right; auto.
      } inversion H; subst. split; simpl; intros; auto.  
      rewrite union_elts in H0. inversion H; subst.
      destruct H0.
      * apply H2 in H0; auto.
        destruct H0 as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst.
        exists v1. exists (fst x). split_all; auto.
        rewrite union_elts; left; auto.
        intros. apply Hfvs. rewrite union_elts. left; auto.
      * specialize (IHps H3 Hfvs' (snd (alpha_p_aux sub a d l))).
        apply IHps in H0; clear IHps.
        destruct H0 as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst.
        exists v1. exists (fst x). split_all; auto.
        rewrite union_elts. right; auto.
      * destruct H0 as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst.
        rewrite union_elts in Hinv.
        rewrite union_elts.
        destruct Hinv as [Hinv1 | Hinv1]; [left | right].
        -- apply H2; auto. intros; apply Hfvs; simpl; rewrite union_elts;
          left; auto.
          exists v1. exists (fst x). auto.
        -- apply IHps; auto.
          exists v1. exists (fst x). auto.
  - split; intros; auto. destruct H. 
    destruct H as [_ [_ [_ [[] _]]]].
  - rewrite union_elts. split; intros.
    + destruct H; [apply IHp1 in H | apply IHp2 in H];
      try (intros; apply Hfvs; simpl; rewrite union_elts;
        try(solve[left; auto]); right; auto);
      destruct H as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst;
      exists v1; exists (fst x); split_all; auto;
      rewrite union_elts; [left | right]; auto.
    + destruct H as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst.
      rewrite union_elts in Hinv. destruct Hinv; 
      [left; apply IHp1 | right; apply IHp2]; try (intros; apply Hfvs;
      simpl; rewrite union_elts; try(solve[left; auto]); right; auto);
      exists v1; exists (fst x); split_all; auto.
  - destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha; simpl;
    rewrite union_elts; [split; intros|].
    + destruct H as [Hinx | [Heq | []]]; subst.
      * apply IHp in Hinx.
        destruct Hinx as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst.
        exists v1. exists (fst x). split_all; auto.
        rewrite union_elts; left; auto.
        intros; apply Hfvs; simpl; rewrite union_elts; left; auto.
      * apply get_assoc_list_some in Ha.
        exists v. exists s. split_all; auto. rewrite union_elts.
        right; left;auto.
    + destruct H as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst.
      rewrite union_elts in Hinv. destruct Hinv as [Hinv | [Heq | []]]; subst;
      [left | right; left]; auto.
      * apply IHp. intros. apply Hfvs; simpl; rewrite union_elts; left; auto.
        exists v1. exists (fst x). split_all; auto.
      * apply get_assoc_list_some in Ha.
        destruct x; simpl in *; subst. f_equal.
        apply (nodup_fst_inj Hnodup Ha Hinl).
    + apply get_assoc_list_none in Ha.
      exfalso. apply Ha. apply Hfvs. simpl. rewrite union_elts; right; left;
      auto.
Qed.

Lemma alpha_p_aux_wf_aux {A: Type} (p: pattern) 
  (sub: vsymbol -> vsymbol -> A -> A) :
  (forall (l: list (vsymbol * string)),
    NoDup (map fst l) ->
    (forall v, In v (pat_fv p) -> In v (map fst l)) ->
    (forall x v, In v (pat_fv (fst (alpha_p_aux sub p x l))) ->
      In (fst v) (map snd l))).
Proof.
  intros. pose proof (alpha_p_aux_wf_aux_gen' p sub l H H0 v x).
  apply H2 in H1. destruct H1 as [v1 [str [Hinl [Hinv1 [Hsnd Hfst]]]]]; subst.
  rewrite in_map_iff. exists (v1, fst v). split; auto.
Qed.

(*Second: need to know that [alpha_p_aux] does not change any bound
  variables in t/f*)

Lemma alpha_p_aux_bnd_t_eq  (p: pattern) (t: term) (l: list (vsymbol * string)) :
  bnd_t (snd (alpha_p_aux sub_t p t l)) =
  bnd_t t.
Proof.
  revert t.
  induction p; simpl; intros; auto.
  - destruct (get_assoc_list vsymbol_eq_dec l v); simpl; auto.
    rewrite bnd_sub_t; auto.
  - generalize dependent t. induction ps; simpl; intros; auto. 
    inversion H; subst.
    rewrite IHps; auto.
  - destruct (get_assoc_list vsymbol_eq_dec l v); simpl; auto.
    rewrite bnd_sub_t; auto.
Qed.

Lemma alpha_p_aux_bnd_f_eq (p: pattern) (f: formula) (l: list (vsymbol * string)) :
  bnd_f (snd (alpha_p_aux sub_f p f l)) =
  bnd_f f.
Proof.
  revert f.
  induction p; simpl; intros; auto.
  - destruct (get_assoc_list vsymbol_eq_dec l v); simpl; auto.
    rewrite bnd_sub_f; auto.
  - generalize dependent f0. induction ps; simpl; intros; auto. 
    inversion H; subst.
    rewrite IHps; auto.
  - destruct (get_assoc_list vsymbol_eq_dec l v); simpl; auto.
    rewrite bnd_sub_f; auto.
Qed.

Lemma map_snd_combine {A B: Type} (l1: list A) (l2: list B) :
  length l1 = length l2 ->
  map snd (combine l1 l2) = l2.
Proof.
  revert l2. induction l1; destruct l2; simpl; intros; auto;
  inversion H.
  rewrite IHl1; auto.
Qed.

Lemma map_fst_combine {A B: Type} (l1: list A) (l2: list B) :
  length l1 = length l2 ->
  map fst (combine l1 l2) = l1.
Proof.
  revert l2. induction l1; destruct l2; simpl; intros; auto;
  inversion H.
  rewrite IHl1; auto.
Qed.

(*TODO: add to this*)
(*Solve trivial/repeated goals and simplify*)
Ltac len_tac :=
repeat match goal with
| |- context [length (firstn ?n ?l)] => rewrite firstn_length
| |- context [length (skipn ?n ?l)] => rewrite skipn_length
| H: length ?l = ?x |- context [length ?l] => rewrite H
| |- context [length (?x ++ ?y)] => rewrite app_length
end; try lia.

Ltac wf_tac :=
  repeat(
  assumption +
  solve[len_tac] +
  solve[lia] +
  match goal with
  | |- context [map snd (combine ?l1 ?l2)] =>
    rewrite map_snd_combine
  | |- context [map fst (combine ?l1 ?l2)] =>
    rewrite map_fst_combine
  | |- NoDup (firstn ?n ?l) => apply NoDup_firstn
  | |- NoDup (skipn ?n ?l) => apply NoDup_skipn
  | |- NoDup (nth ?i (split_lens ?a ?b) ?d) =>
    apply split_lens_nodup
  | |- context [length (map ?f ?x)] => rewrite map_length
  | |- context [length (split_lens ?l1 ?l2)] =>
    rewrite split_lens_length
  | |- context [length (firstn ?n ?l)] => rewrite firstn_length
  | |- context [length (skipn ?n ?l)] => rewrite skipn_length
  | |- In (nth ?i ?l ?x) ?l =>
    apply nth_In
  | |- context [length (nth ?l (split_lens ?a ?b) ?d)] =>
    rewrite split_lens_ith
  | |- context [length (map2 ?f ?l1 ?l2)] =>
    rewrite map2_length
  | |- ?i < length ?l -> ?P => intros
  | |- context [Nat.min ?x ?x] =>
    rewrite Nat.min_id
  (*TODO: this is hacky*)
  | |- context [nth ?i (map ?f ?l) ?d] =>
    (rewrite map_nth_inbound with(d2:=tm_d)) ||
    (rewrite map_nth_inbound with (d2:=(Pwild, tm_d))) ||
    (rewrite map_nth_inbound with (d2:=(Pwild, Ftrue)))
  (*Deal with some "In" goals - TODO improve*)
  | H: In ?x (firstn ?n ?l) |- In ?x ?l => apply In_firstn in H
  | H: In ?x (skipn ?n ?l) |- In ?x ?l => apply In_skipn in H
  (*A special case*)
  | |- NoDup (pat_fv ?p) => apply NoDup_pat_fv
  | |- context [concat (split_lens ?l1 ?l2)] =>
    rewrite <- split_lens_concat
  | |- In ?x (map ?g ?l) => rewrite in_map_iff
  | |- exists y, ?f y = ?f ?x /\ ?P => exists x; split
  (*Solve the sum length goal*)
  | H: length ?l = length (concat (map ?f ?l1)) |-
    sum (map ?g ?l1) = length ?l => rewrite length_concat in H;
    rewrite H; f_equal; rewrite map_map; apply map_ext
  | H: length (?x :: ?l) = ?n |- _ => simpl in H
  | H: ?x = length (?l1 ++ ?l2) |- _ => rewrite app_length in H
  end); auto; try lia. 

Lemma in_nth_concat_nodup {A: Type} {l: list (list A)} {i1 i2: nat}
  {x: A} {d: list A}:
  In x (nth i1 l d) ->
  In x (nth i2 l d) ->
  NoDup (concat l) ->
  i1 < length l ->
  i2 < length l ->
  i1 = i2.
Proof.
  intros. rewrite NoDup_concat_iff in H1.
  split_all.
  destruct (Nat.eq_dec i1 i2); subst; auto.
  exfalso.
  apply (H4 i1 i2 d x H2 H3 n); auto.
Qed.

Lemma alpha_aux_wf_aux (t: term) (f: formula) :
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
          apply In_firstn in H3. contradiction.
        -- rewrite bnd_sub_t in H3.
          apply H0 in H3; wf_tac. apply In_skipn in H3.
          contradiction.
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
        right. apply In_firstn in Hinx; auto.
      * rewrite bnd_sub_t in Hinx. apply H0 in Hinx; wf_tac.
        right. apply In_skipn in Hinx; auto.
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
      * apply H0 in Hinx; wf_tac. apply In_firstn in Hinx.
        apply In_skipn in Hinx; auto.
      * apply H1 in Hinx; wf_tac. apply In_skipn in Hinx.
        apply In_skipn in Hinx; auto.
  - (*Tmatch case*)
    assert (Hsum: sum (map
        (fun x : pattern * term =>
        Datatypes.length (pat_fv (fst x)) + Datatypes.length (bnd_t (snd x)))
        ps) = Datatypes.length (skipn (Datatypes.length (bnd_t tm)) l)). {
          wf_tac. rewrite H2,length_concat, 
        map_map, minus_plus. f_equal. apply map_ext_in_iff; intros.
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
          ++ rewrite alpha_p_aux_bnd_t_eq.
            rewrite Forall_forall in H0.
            apply H0; auto; wf_tac.
          ++ intros x.
            rewrite alpha_p_aux_bnd_t_eq.
            intros [Hinx1 Hinx2].
            (*Need this a lot even though it's ugly*)
            apply alpha_p_aux_wf_aux in Hinx1; wf_tac.
            rewrite map_snd_combine in Hinx1; wf_tac.
            rewrite Forall_forall in H0.
            apply H0 in Hinx2; wf_tac.
            apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
        -- intros i1 i2 d x. wf_tac.
          rewrite !map2_nth with(d1:=(Pwild, tm_d)) (d2:=nil); wf_tac.
          intros [Hini1 Hini2].
          apply in_app_or in Hini1, Hini2.
          (*Now we get 4 cases need to show each is impossible*)
          destruct Hini1 as [Hini1 | Hini1].
          ++ apply alpha_p_aux_wf_aux in Hini1; wf_tac.
            revert Hini1. wf_tac. intros Hini1.
            apply In_firstn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** apply alpha_p_aux_wf_aux in Hini2; wf_tac.
              revert Hini2. wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** rewrite alpha_p_aux_bnd_t_eq in Hini2.
              rewrite Forall_forall in H0.
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
          ++ rewrite alpha_p_aux_bnd_t_eq in Hini1.
            rewrite Forall_forall in H0.
            apply H0 in Hini1; wf_tac.
            apply In_skipn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** apply alpha_p_aux_wf_aux in Hini2; wf_tac.
              revert Hini2; wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** rewrite alpha_p_aux_bnd_t_eq in Hini2.
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
        -- apply alpha_p_aux_wf_aux in Hinx2; wf_tac.
          revert Hinx2; wf_tac; intros.
          apply In_firstn in Hinx2.
          apply in_split_lens_ith in Hinx2; wf_tac.
          apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
        -- rewrite alpha_p_aux_bnd_t_eq in Hinx2.
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
        -- apply alpha_p_aux_wf_aux in Hinx; wf_tac.
          revert Hinx; wf_tac; intros.
          apply In_firstn in Hinx.
          apply in_split_lens_ith in Hinx; wf_tac.
        -- rewrite alpha_p_aux_bnd_t_eq in Hinx.
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
        [apply H in Hins | apply H0 in Hins]; wf_tac;
        [apply In_firstn in Hins | apply In_skipn in Hins];
        contradiction.
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
      * apply In_firstn in Hinx. wf_tac.
      * apply In_skipn in Hinx. wf_tac.
  - (*Fmatch case - very similar to Tmatch*)
    assert (Hsum: sum (map
      (fun x : pattern * formula =>
      Datatypes.length (pat_fv (fst x)) + Datatypes.length (bnd_f (snd x)))
      ps) = Datatypes.length (skipn (Datatypes.length (bnd_t tm)) l)). {
        wf_tac. rewrite H2,length_concat, 
      map_map, minus_plus. f_equal. apply map_ext_in_iff; intros.
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
          ++ rewrite alpha_p_aux_bnd_f_eq.
            rewrite Forall_forall in H0.
            apply H0; auto; wf_tac.
          ++ intros x.
            rewrite alpha_p_aux_bnd_f_eq.
            intros [Hinx1 Hinx2].
            (*Need this a lot even though it's ugly*)
            apply alpha_p_aux_wf_aux in Hinx1; wf_tac.
            rewrite map_snd_combine in Hinx1; wf_tac.
            rewrite Forall_forall in H0.
            apply H0 in Hinx2; wf_tac.
            apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
        -- intros i1 i2 d x. wf_tac.
          rewrite !map2_nth with(d1:=(Pwild, Ftrue)) (d2:=nil); wf_tac.
          intros [Hini1 Hini2].
          apply in_app_or in Hini1, Hini2.
          (*Now we get 4 cases need to show each is impossible*)
          destruct Hini1 as [Hini1 | Hini1].
          ++ apply alpha_p_aux_wf_aux in Hini1; wf_tac.
            revert Hini1. wf_tac. intros Hini1.
            apply In_firstn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** apply alpha_p_aux_wf_aux in Hini2; wf_tac.
              revert Hini2. wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** rewrite alpha_p_aux_bnd_f_eq in Hini2.
              rewrite Forall_forall in H0.
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
          ++ rewrite alpha_p_aux_bnd_f_eq in Hini1.
            rewrite Forall_forall in H0.
            apply H0 in Hini1; wf_tac.
            apply In_skipn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** apply alpha_p_aux_wf_aux in Hini2; wf_tac.
              revert Hini2; wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** rewrite alpha_p_aux_bnd_f_eq in Hini2.
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
      -- apply alpha_p_aux_wf_aux in Hinx2; wf_tac.
        revert Hinx2; wf_tac; intros.
        apply In_firstn in Hinx2.
        apply in_split_lens_ith in Hinx2; wf_tac.
        apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
      -- rewrite alpha_p_aux_bnd_f_eq in Hinx2.
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
      -- apply alpha_p_aux_wf_aux in Hinx; wf_tac.
        revert Hinx; wf_tac; intros.
        apply In_firstn in Hinx.
        apply in_split_lens_ith in Hinx; wf_tac.
      -- rewrite alpha_p_aux_bnd_f_eq in Hinx.
        rewrite Forall_forall in H0; apply H0 in Hinx; wf_tac.
        apply In_skipn in Hinx.
        apply in_split_lens_ith in Hinx; wf_tac.
Qed.

Lemma in_combine_iff {A B: Type} (l1: list A) (l2: list B) (x: A * B) :
  length l1 = length l2 ->
  In x (combine l1 l2) <->
  exists i, i < length l1 /\
  forall d1 d2,
  x = (nth i l1 d1, nth i l2 d2).
Proof.
  revert l2. induction l1; simpl; intros; destruct l2; inversion H;
  split; intros; auto; destruct H0; try lia; subst.
  - exists 0; split; auto; lia.
  - apply IHl1 in H0; auto.
    destruct H0 as [i [Hi Hx]].
    exists (S i); simpl. split; auto; try lia.
  - rename x0 into i. destruct H0 as [Hi Hx].
    simpl.
    destruct i; simpl in Hx.
    + left. rewrite Hx; auto.
    + right. apply IHl1; auto. exists i; split; auto; lia.
Qed.

(*TODO: move*)

Lemma null_map {A B: Type} {f: A -> B} {l: list A} :
  null (map f l) = null l.
Proof.
  destruct l; simpl; auto.
Qed.

(*sub_t and sub_f preserve typing*)
Lemma sub_valid (t: term) (f: formula):
  (forall (x y: vsymbol) (ty: vty), 
    term_has_type sigma t ty ->
    snd x = snd y ->
    term_has_type sigma (sub_t x y t) ty) /\
  (forall (x y: vsymbol),
    valid_formula sigma f ->
    snd x = snd y ->
    valid_formula sigma (sub_f x y f)).
Proof.
  revert t f.
  apply term_formula_ind; simpl; auto; intros.
  - destruct (vsymbol_eq_dec x v); subst; auto.
    inversion H; subst. rewrite H0. constructor.
    rewrite <- H0; assumption.
  - (*Tfun*) 
    inversion H0; subst.
    constructor; wf_tac.
    revert H H12; rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H2; wf_tac.
    destruct H2 as [i [Hi Hx0]].
    revert Hi; wf_tac.
    specialize (Hx0 tm_d vty_int); subst; simpl. wf_tac.
    apply H; wf_tac.
    apply (H12 (nth i l1 tm_d, (nth i (map (ty_subst (s_params f1) l) (s_args f1)) vty_int))).
    rewrite in_combine_iff; wf_tac.
    exists i. split; auto. intros.
    f_equal; apply nth_indep; wf_tac.
  - (*Tlet*)
    inversion H1; subst.
    destruct (vsymbol_eq_dec x v); subst; auto; constructor; auto.
  - (*Tif*)
    inversion H2; subst.
    constructor; auto.
  - (*Tmatch*)
    inversion H1; subst.
    constructor; auto.
    + intros pt. rewrite in_map_iff.
      intros [pt' [Hpt Hinpt]].
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst pt'))); subst;
      simpl; auto.
    + intros pt. rewrite in_map_iff.
      intros [pt' [Hpt Hinpt]].
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst pt'))); subst;
      simpl; auto.
      rewrite Forall_forall in H0.
      apply H0; auto. wf_tac.
    + rewrite null_map; auto.
  - (*Teps*) inversion H0; subst.
    destruct (vsymbol_eq_dec x v); subst; constructor; auto.
  - (*Fpred*)
    inversion H0; subst.
    constructor; wf_tac.
    revert H H10; rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H2; wf_tac.
    destruct H2 as [i [Hi Hx0]].
    revert Hi; wf_tac.
    specialize (Hx0 tm_d vty_int); subst; simpl. wf_tac.
    apply H; wf_tac.
    apply (H10 (nth i tms tm_d, (nth i (map (ty_subst (p_params p) tys) (p_args p)) vty_int))).
    rewrite in_combine_iff; wf_tac.
    exists i. split; auto. intros.
    f_equal; apply nth_indep; wf_tac.
  - (*Fquant*)
    inversion H0; subst.
    destruct (vsymbol_eq_dec x v); subst; simpl; constructor; auto.
  - (*Feq*) inversion H1; subst.
    constructor; auto.
  - (*Fbinop*) inversion H1; subst. constructor; auto.
  - (*Fnot*) inversion H0; subst. constructor; auto.
  - (*Flet*) inversion H1; subst.
    destruct (vsymbol_eq_dec x v); subst; auto; constructor; auto.
  - (*Fif*) inversion H2; subst. constructor; auto.
  - (*Fmatch*)
    inversion H1; subst.
    constructor; auto.
    + revert H8. rewrite !Forall_forall; intros Hallpat pt. 
      rewrite in_map_iff.
      intros [pt' [Hpt Hinpt]].
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst pt'))); subst;
      simpl; auto.
    + revert H9. rewrite !Forall_forall; intros Hallval pt. 
      rewrite in_map_iff.
      intros [pt' [Hpt Hinpt]].
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst pt'))); subst;
      simpl; auto.
      rewrite Forall_forall in H0.
      apply H0; auto. wf_tac.
    + rewrite null_map; auto.
Qed.

Corollary sub_t_valid (t: term) (x y: vsymbol) (ty: vty):
  term_has_type sigma t ty ->
  snd x = snd y ->
  term_has_type sigma (sub_t x y t) ty.
Proof.
  apply sub_valid. apply Ftrue.
Qed.

Corollary sub_f_valid (f: formula) (x y: vsymbol):
  valid_formula sigma f ->
  snd x = snd y ->
  valid_formula sigma (sub_f x y f).
Proof.
  apply sub_valid. apply tm_d.
Qed.

(*Need to know that all patterns in constrs are valid*)
(*
Lemma pconstr_ps_valid_pattern f vs ps ty:
  pattern_has_type sigma (Pconstr f vs ps) ty ->
  (forall p, In p ps -> exists ty',
    pattern_has_type sigma p ty').
Proof.
  intros. inversion H; subst. subst sigma0.*)

(*Generalized so it works for terms and formulas*)
Lemma alpha_p_aux_valid {A B: Type} (sub: vsymbol -> vsymbol -> A -> A)
  (valid: A -> B -> Prop)(p: pattern) (a: A)
  (l: list (vsymbol * string))
  (Hnodup1: NoDup (map fst l))
  (Hnodup2: NoDup (map snd l))
  (sub_valid: forall a x y b,
    valid a b ->
    snd x = snd y ->
    valid (sub x y a) b):
  (forall v : vsymbol, In v (pat_fv p) -> In v (map fst l)) ->
  (forall ty, pattern_has_type sigma p ty ->
    pattern_has_type sigma (fst (alpha_p_aux sub p a l)) ty) /\
  (forall b, valid a b ->
    valid (snd (alpha_p_aux sub p a l)) b).
Proof.
  revert a.
  (*revert l t Hnodup1 Hnodup2.*) induction p; simpl; auto; intros.
  - (*Pvar*) 
    destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha; 
    simpl; split; intros; auto.
    inversion H0; subst.
    replace (snd v) with (snd ((s, snd v))) at 2 by auto.
    constructor; auto.
  - (*Pconstr*)
    split; intros.
    + inversion H1; subst. subst sigma0.
      assert (Hlen: 
      Datatypes.length
      (fst
         ((fix alpha_ps_aux (l1 : list pattern) (y : A) {struct l1} :
               list pattern * A :=
             match l1 with
             | [] => ([], y)
             | ph :: pt =>
                 (fst (alpha_p_aux sub ph y l)
                  :: fst (alpha_ps_aux pt (snd (alpha_p_aux sub ph y l))),
                 snd (alpha_ps_aux pt (snd (alpha_p_aux sub ph y l))))
             end) ps a)) = Datatypes.length (s_args f)). {
        rewrite <- H7. clear. revert a. induction ps; simpl; auto.
      }
      constructor; auto.
      * revert H11. rewrite !Forall_forall.
        assert (length (map (ty_subst (s_params f) vs) (s_args f)) = length ps) by wf_tac.
        generalize dependent (map (ty_subst (s_params f) vs) (s_args f)).
        clear -H H0.
        revert a. induction ps; simpl; auto ; intros; destruct l0.
        -- inversion H1.
        -- inversion H; subst. simpl in H1. destruct H1; subst; simpl.
          ++ apply H5; auto.
            intros. apply H0. simpl. rewrite union_elts. left; auto.
            specialize (H11 (a, v)); simpl in H11.
            apply H11; left; auto.
          ++ apply (IHps H6) with (a:=(snd (alpha_p_aux sub a a0 l))) (l:=l0); auto.
            intros. apply H0. simpl. rewrite union_elts. right; auto.
            intros.
            apply H11; right; auto.
      * rewrite Hlen, <- H7.
        clear Hlen. clear -H12 H0 H Hnodup2. revert a.
        (*We need a separate inductive lemma:*)
        assert (Hinnth: forall (ps: list pattern) (j : nat) (x : vsymbol) (d : pattern) (a : A),
        j < Datatypes.length ps ->
        (forall v : vsymbol,
         In v (big_union vsymbol_eq_dec pat_fv ps) -> In v (map fst l)) ->
        In x
          (pat_fv
             (nth j
                (fst
                   ((fix alpha_ps_aux (l1 : list pattern) (y : A) {struct l1} :
                         list pattern * A :=
                       match l1 with
                       | [] => ([], y)
                       | ph :: pt =>
                           (fst (alpha_p_aux sub ph y l)
                            :: fst (alpha_ps_aux pt (snd (alpha_p_aux sub ph y l))),
                           snd (alpha_ps_aux pt (snd (alpha_p_aux sub ph y l))))
                       end) ps a)) d)) ->
        exists v' : vsymbol, In (v', fst x) l /\ In v' (pat_fv (nth j ps Pwild))). {
          clear.
          induction ps; simpl; auto; intros; try lia.
            destruct j.
            - apply alpha_p_aux_wf_aux_gen in H1; auto.
              intros. apply H0. rewrite union_elts. left; auto.
            - eapply IHps; try lia; auto. 2: apply H1.
              intros. apply H0. rewrite union_elts. right; auto.
        }
        intros t i j d x Hi Hj Hij [Hinx1 Hinx2].
        apply Hinnth in Hinx1; auto.
        apply Hinnth in Hinx2; auto.
        destruct Hinx1 as [v1 [Hinl1 Hinv1]].
        destruct Hinx2 as [v2 [Hinl2 Hinv2]].
        assert (v1 = v2) by apply (nodup_snd_inj Hnodup2 Hinl1 Hinl2). 
        subst.
        (*This contradicts the disjointness of free vars*)
        apply (H12 i j Pwild v2); try lia; auto.
    + (*term goal*)
      generalize dependent a.
      revert H. clear - H0.
      induction ps; simpl; auto; intros.
      inversion H; subst.
      apply IHps; auto.
      * intros. apply H0. simpl. rewrite union_elts. right; auto.
      * apply H4; auto. intros. apply H0. simpl. rewrite union_elts.
        left; auto.
  - (*Por case*)
    split; intros.
    + inversion H0; subst.
      constructor; auto.
      * apply IHp1; auto.
        intros. apply H. rewrite union_elts; left; auto.
      * apply IHp2; auto.
        intros; apply H; rewrite union_elts; right; auto.
      * intros x. rewrite !alpha_p_aux_wf_aux_gen'; auto;
        try (intros; apply H; simpl; rewrite union_elts;
          try(solve[left; auto]); right; auto).
        setoid_rewrite H7. reflexivity.
    + apply IHp2; auto.
      intros. apply H. rewrite union_elts; right; auto.
  - (*Pbind case*)
    split; intros.
    + inversion H0; subst. 
      destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha;
      simpl; auto.
      replace (snd v) with (snd ((s, snd v))) at 2 by auto.
      constructor; simpl.
      * intro. 
        rewrite alpha_p_aux_wf_aux_gen' in H1; auto.
        destruct H1 as [v1 [str [Hinl [Hinv1 [Hsnd Hfst]]]]];
        simpl in *; subst.
        apply get_assoc_list_some in Ha.
        assert (v = v1) by apply (nodup_snd_inj Hnodup2 Ha Hinl); subst.
        apply H4. wf_tac.
        intros. apply H. rewrite union_elts; left; auto.
      * apply IHp; auto. intros.
        apply H; rewrite union_elts; left; auto.
    + destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha; simpl; auto.
      apply sub_valid; auto.
      apply IHp; auto.
      intros. apply H. rewrite union_elts; left; auto.
Qed.


Lemma alpha_p_aux_valid_t (p: pattern) (t: term)
  (l: list (vsymbol * string))
  (Hnodup1: NoDup (map fst l))
  (Hnodup2: NoDup (map snd l)):
  (forall v : vsymbol, In v (pat_fv p) -> In v (map fst l)) ->
  (forall ty, pattern_has_type sigma p ty ->
    pattern_has_type sigma (fst (alpha_p_aux sub_t p t l)) ty) /\
  (forall ty, term_has_type sigma t ty ->
    term_has_type sigma (snd (alpha_p_aux sub_t p t l)) ty).
Proof.
  apply alpha_p_aux_valid; auto.
  apply sub_t_valid.
Qed.

Lemma alpha_p_aux_valid_f (p: pattern) (f: formula)
  (l: list (vsymbol * string))
  (Hnodup1: NoDup (map fst l))
  (Hnodup2: NoDup (map snd l)):
  (forall v : vsymbol, In v (pat_fv p) -> In v (map fst l)) ->
  (forall ty, pattern_has_type sigma p ty ->
    pattern_has_type sigma (fst (alpha_p_aux sub_f p f l)) ty) /\
  (valid_formula sigma f ->
    valid_formula sigma (snd (alpha_p_aux sub_f p f l))).
Proof.
  intros Hinfv.
  pose proof (alpha_p_aux_valid sub_f 
    (fun f' (u: unit) => valid_formula sigma f') 
      p f l Hnodup1 Hnodup2);
  split; apply H; auto; try(intros; apply sub_f_valid; auto).
  exact tt.
Qed.

Lemma null_map2 {A B C: Type} (f: A -> B -> C) (l1: list A) (l2: list B):
  length l1 = length l2 ->
  null (map2 f l1 l2) =
  null l1.
Proof.
  revert l2. destruct l1; simpl; destruct l2; simpl; intros; 
  auto; inversion H.
Qed.

(*Part 2: [alpha_t_aux] and [alpha_f_aux] form well-typed
  terms and formulas*)
Lemma alpha_aux_valid (t: term) (f: formula):
  (forall (l: list string) (ty: vty)
    (Hnodup: NoDup l)
    (Hlenl: length l = length (bnd_t t)),
    term_has_type sigma t ty ->
    term_has_type sigma (alpha_t_aux t l) ty) /\
  (forall (l: list string)
    (Hnodup: NoDup l)
    (Hlenl: length l = length (bnd_f f)),
    valid_formula sigma f ->
    valid_formula sigma (alpha_f_aux f l)).
Proof.
  revert t f.
  apply term_formula_ind; simpl; auto; simpl; intros.
  - (*Tfun*)
    inversion H0; subst. constructor; auto.
    wf_tac. revert H11 H.
    rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H1; wf_tac.
    destruct H1 as [i [Hi Hx]].
    revert Hi; wf_tac.
    specialize (Hx tm_d vty_int); subst; simpl.
    rewrite map2_nth with(d1:=tm_d) (d2:=nil); wf_tac.
    apply H; wf_tac.
    rewrite map_nth_inbound with(d2:=vty_int); try lia.
    apply (H11 (nth i l1 tm_d, 
      (ty_subst (s_params f1) l (nth i (s_args f1) vty_int)))).
    rewrite in_combine_iff; wf_tac.
    exists i. split; auto. intros.
    f_equal.
    + apply nth_indep; auto.
    + rewrite map_nth_inbound with (d2:=vty_int); auto. lia.
  - (*Tlet*) destruct l; auto; simpl.
    inversion H1; subst.
    inversion Hnodup; subst.
    wf_tac. inversion Hlenl.
    constructor.
    + apply H; wf_tac.
    + apply sub_t_valid; auto. apply H0; wf_tac.
  - (*Tif*) inversion H2; subst.
    constructor; auto.
    apply H; wf_tac.
    apply H0; wf_tac.
    apply H1; wf_tac.
  - (*Tmatch*)
    assert (Hsum: sum (map
      (fun x : pattern * term =>
      Datatypes.length (pat_fv (fst x)) + Datatypes.length (bnd_t (snd x)))
      ps) = Datatypes.length (skipn (Datatypes.length (bnd_t tm)) l)). {
        wf_tac. rewrite Hlenl,length_concat, 
      map_map, minus_plus. f_equal. apply map_ext_in_iff; intros.
      rewrite app_length; auto.
    }
    inversion H1; subst.
    constructor.
    + apply H; auto; wf_tac.
    + intros x.
      rewrite in_map2_iff with(d1:=(Pwild, tm_d))(d2:=nil); wf_tac.
      intros [i [Hi Hx]]; subst.
      apply alpha_p_aux_valid_t; wf_tac.
      apply H7; wf_tac.
    + intros x.
      rewrite in_map2_iff with(d1:=(Pwild, tm_d))(d2:=nil); wf_tac.
      intros [i [Hi Hx]]; subst.
      apply alpha_p_aux_valid_t; wf_tac.
      rewrite Forall_forall in H0. apply H0; wf_tac.
      apply H9; wf_tac.
    + rewrite null_map2; auto; wf_tac.
  - (*Teps*)
    destruct l; inversion Hlenl.
    inversion H0; subst.
    replace (snd v) with (snd (s, snd v)) at 3 by auto.
    constructor; auto.
    apply sub_f_valid; auto. inversion Hnodup. apply H; wf_tac.
  - (*Fpred*)
    inversion H0; subst.
    constructor; auto; wf_tac.
    revert H9 H.
    rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H1; wf_tac.
    destruct H1 as [i [Hi Hx]].
    revert Hi; wf_tac.
    specialize (Hx tm_d vty_int); subst; simpl.
    rewrite map2_nth with(d1:=tm_d) (d2:=nil); wf_tac.
    apply H; wf_tac.
    rewrite map_nth_inbound with(d2:=vty_int); try lia.
    apply (H9 (nth i tms tm_d, 
      (ty_subst (p_params p) tys (nth i (p_args p) vty_int)))).
    rewrite in_combine_iff; wf_tac.
    exists i. split; auto. intros.
    f_equal.
    + apply nth_indep; auto.
    + rewrite map_nth_inbound with (d2:=vty_int); auto. lia.
  - (*Fquant*)
    destruct l; inversion Hlenl.
    inversion H0; subst.
    constructor; auto.
    apply sub_f_valid; auto.
    apply H; auto. inversion Hnodup; auto.
  - (*Feq*)
    inversion H1; subst.
    constructor; [apply H | apply H0]; wf_tac.
  - (*Fbinop*)
    inversion H1; subst.
    constructor; [apply H | apply H0]; wf_tac.
  - (*Fnot*)
    inversion H0; subst.
    constructor. apply H; wf_tac.
  - (*Flet*)
    destruct l; inversion Hlenl; simpl.
    inversion H1; subst.
    inversion Hnodup; subst.
    constructor; [apply H | apply sub_f_valid]; wf_tac.
    apply H0; wf_tac.
  - (*Fif*)
    inversion H2; subst.
    constructor; [apply H | apply H0 | apply H1]; wf_tac.
  - (*Fmatch*)
    assert (Hsum: sum (map
      (fun x : pattern * formula =>
      Datatypes.length (pat_fv (fst x)) + Datatypes.length (bnd_f (snd x)))
      ps) = Datatypes.length (skipn (Datatypes.length (bnd_t tm)) l)). {
        wf_tac. rewrite Hlenl,length_concat, 
      map_map, minus_plus. f_equal. apply map_ext_in_iff; intros.
      rewrite app_length; auto.
    }
    inversion H1; subst.
    constructor.
    + apply H; auto; wf_tac.
    + rewrite Forall_forall; intros x.
      rewrite in_map2_iff with(d1:=(Pwild, Ftrue))(d2:=nil); wf_tac.
      intros [i [Hi Hx]]; subst.
      apply alpha_p_aux_valid_f; wf_tac.
      rewrite Forall_forall in H7;
      apply H7; wf_tac.
    + rewrite Forall_forall; intros x.
      rewrite in_map2_iff with(d1:=(Pwild, Ftrue))(d2:=nil); wf_tac.
      intros [i [Hi Hx]]; subst.
      apply alpha_p_aux_valid_f; wf_tac.
      rewrite Forall_forall in H0. apply H0; wf_tac.
      rewrite Forall_forall in H8; apply H8; wf_tac.
    + rewrite null_map2; auto; wf_tac.
Qed.

(*Finally, we need to prove that the [alpha] functions
  do not change the meaning of the term/formula (since we
  only rename bound variables)*)


(*
Lemma alpha_t_aux_correct (t: term) (l: list vsymbol),
  NoDup l ->
  (forall x, In x l -> ~ In x (map fst (term_fv t))) ->
  length l = length (bnd_t t) ->
  term_interp (alpha_t_aux t l) Hty =
  term_interp t Hty /\
  term_wf (alpha_t_aux t l).*)


(*Let's try*)
End Alpha.


(*Iterated version of forall, let, and*)
Section Iter.

(*Iterated forall*)
Definition fforalls (vs: list vsymbol) (f: formula) : formula :=
  fold_right (fun x acc => Fquant Tforall x acc) f vs.

Lemma fforalls_valid (vs: list vsymbol) (f: formula) 
  (Hval: valid_formula sigma f)
  (Hall: Forall (fun x => valid_type sigma (snd x)) vs) : 
  valid_formula sigma (fforalls vs f).
Proof.
  induction vs; auto. inversion Hall; subst. 
  simpl. constructor; auto.
Qed.

Lemma fforalls_valid_inj (vs: list vsymbol) (f: formula)
  (Hval: valid_formula sigma (fforalls vs f)):
  valid_formula sigma f /\ Forall (fun x => valid_type sigma (snd x)) vs.
Proof.
  induction vs; auto.
  simpl in Hval. inversion Hval; subst.
  specialize (IHvs H4). split_all; auto.
Qed.

(*Substitute in a bunch of values for a bunch of variables,
  using an hlist to ensure they have the correct type*)
Fixpoint substi_mult (vt: val_typevar) (vv: @val_vars sigma pd vt) 
  (vs: list vsymbol)
  (vals: hlist (fun x =>
  domain (v_subst (v_typevar vt) x)) (map snd vs)) :
  val_vars pd vt :=
  (match vs as l return hlist  
    (fun x => domain (v_subst (v_typevar vt) x)) 
    (map snd l) -> val_vars pd vt with
  | nil => fun _ => vv
  | x :: tl => fun h' => 
     (substi_mult vt (substi vt vv x (hlist_hd h')) tl (hlist_tl h')) 
  end) vals.
  
(*And we show that we can use this multi-substitution
  to interpret [fforalls_val]*)
Lemma fforalls_val (vv: val_vars pd vt) 
  (vs: list vsymbol) (f: formula) 
  (Hval: valid_formula sigma f)
  (Hall: Forall (fun x => valid_type sigma (snd x)) vs):
  formula_rep vv (fforalls vs f) 
    (fforalls_valid vs f Hval Hall) =
    all_dec (forall (h: hlist  (fun x =>
      domain (v_subst (v_typevar vt) x)) (map snd vs)),
      formula_rep (substi_mult vt vv vs h) f Hval).
Proof.
  revert vv.
  generalize dependent (fforalls_valid vs f Hval Hall).
  induction vs; simpl; intros Hval' vv.
  - destruct (formula_rep vv f Hval') eqn : Hrep; 
    match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end; simpl.
    + exfalso. apply n; intros. erewrite fmla_rep_irrel. apply Hrep.
    + rewrite <- Hrep. erewrite fmla_rep_irrel. apply i. constructor.
  - inversion Hall; subst. specialize (IHvs H2).
    specialize (IHvs (valid_quant_inj (valid_formula_eq eq_refl Hval'))).
    apply all_dec_eq.
    split; intros Hforall.
    + intros h. 
      specialize (Hforall (hlist_hd h)).
      rewrite IHvs in Hforall.
      revert Hforall.
      match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end; simpl.
    + intros d.
      rewrite IHvs. 
      match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end; simpl.
      exfalso. apply n; clear n. intros h.
      specialize (Hforall (HL_cons _ (snd a) (map snd vs) d h)).
      apply Hforall.
Qed.

Lemma fforalls_val' (vv: val_vars pd vt) 
  (vs: list vsymbol) (f: formula) 
  Hval1 Hval2:
  formula_rep vv (fforalls vs f) 
    Hval2 =
    all_dec (forall (h: hlist  (fun x =>
      domain (v_subst (v_typevar vt) x)) (map snd vs)),
      formula_rep (substi_mult vt vv vs h) f Hval1).
Proof.
  assert (A:=Hval2).
  apply fforalls_valid_inj in A. split_all.
  rewrite fmla_rep_irrel with(Hval2:=(fforalls_valid vs f Hval1 H0)).
  apply fforalls_val.
Qed.

(*Next we give the valuation for an iterated let. This time,
  we don't need to worry about hlists*)
Fixpoint substi_multi_let (vv: @val_vars sigma pd vt) 
(vs: list (vsymbol * term)) 
  (Hall: Forall (fun x => term_has_type sigma (snd x) (snd (fst x))) vs) :
val_vars pd vt := 
  match vs as l return
  Forall (fun x => term_has_type sigma (snd x) (snd (fst x))) l ->
  val_vars pd vt
  with
  | nil => fun _ => vv
  | (v, t) :: tl => fun Hall =>
    substi_multi_let 
      (substi vt vv v 
        (term_rep vv t (snd v) 
      (Forall_inv Hall))) tl (Forall_inv_tail Hall)
  end Hall.

Definition iter_flet (vs: list (vsymbol * term)) (f: formula) :=
  fold_right (fun x acc => Flet (snd x) (fst x) acc) f vs.

Lemma iter_flet_valid (vs: list (vsymbol * term)) (f: formula)
  (Hval: valid_formula sigma f)
  (Hall: Forall (fun x => term_has_type sigma (snd x) (snd (fst x))) vs) :
  valid_formula sigma (iter_flet vs f).
Proof.
  induction vs; simpl; auto.
  inversion Hall; subst.
  constructor; auto.
Qed.

Lemma iter_flet_valid_inj (vs: list (vsymbol * term)) (f: formula)
(Hval: valid_formula sigma (iter_flet vs f)):
(valid_formula sigma f) /\
(Forall (fun x => term_has_type sigma (snd x) (snd (fst x))) vs).
Proof.
  induction vs; simpl in *; auto.
  inversion Hval; subst. specialize (IHvs H4).
  split_all; auto.
Qed.

Lemma iter_flet_val (vv: @val_vars sigma pd vt) 
  (vs: list (vsymbol * term)) (f: formula)
  (Hval: valid_formula sigma f)
  (Hall: Forall (fun x => term_has_type sigma (snd x) (snd (fst x))) vs) :
  formula_rep vv (iter_flet vs f) 
    (iter_flet_valid vs f Hval Hall) =
  formula_rep (substi_multi_let vv vs Hall) f Hval.
Proof.
  generalize dependent (iter_flet_valid vs f Hval Hall).
  revert vv.
  induction vs; intros vv Hval'; simpl.
  - apply fmla_rep_irrel.
  - destruct a. simpl.
    inversion Hall; subst.
    rewrite (IHvs (Forall_inv_tail Hall)).
    f_equal.
    (*Separately, show that substi_multi_let irrelevant
      in choice of proofs*)
      clear.
      erewrite term_rep_irrel. reflexivity.
Qed.

Definition iter_fand (l: list formula) : formula :=
    fold_right (fun f acc => Fbinop Tand f acc) Ftrue l.

Lemma iter_fand_valid (l: list formula) 
  (Hall: Forall (valid_formula sigma) l) :
  valid_formula sigma (iter_fand l).
Proof.
  induction l; simpl; constructor; inversion Hall; subst; auto.
Qed.

Lemma iter_fand_rep (vv: val_vars pd vt) 
(l: list formula)
(Hall: valid_formula sigma (iter_fand l)) :
formula_rep vv (iter_fand l) Hall <->
(forall (f: formula) (Hvalf: valid_formula sigma f),
  In f l -> formula_rep vv f Hvalf).
Proof.
  revert Hall.
  induction l; simpl; intros; auto; split; intros; auto.
  - simpl in H. unfold is_true in H. rewrite andb_true_iff in H.
    destruct H.
    destruct H0; subst.
    + erewrite fmla_rep_irrel. apply H.
    + inversion Hall; subst.
      specialize (IHl H7).
      apply IHl; auto.
      erewrite fmla_rep_irrel. apply H1.
  - inversion Hall; subst.
    specialize (IHl H5).
    apply andb_true_iff. split.
    + erewrite fmla_rep_irrel. apply H. left; auto.
    + erewrite fmla_rep_irrel. apply IHl. intros.
      apply H. right; auto.
      Unshelve.
      auto.
Qed.

End Iter.

(*Some other results we need for IndProp*)

(*true -> P is equivalent to P*)
Lemma true_impl (vv: val_vars pd vt) (f: formula) (Hval1: valid_formula sigma f)
  (Hval2: valid_formula sigma (Fbinop Timplies Ftrue f)) :
  formula_rep vv f Hval1 =
  formula_rep vv (Fbinop Timplies Ftrue f) Hval2.
Proof.
  simpl. apply fmla_rep_irrel.
Qed. 

(*(f1 /\ f2) -> f3 is equivalent to f1 -> f2 -> f3*)
Lemma and_impl (vv: val_vars pd vt) 
  (f1 f2 f3: formula) Hval1 Hval2:
  formula_rep vv (Fbinop Timplies (Fbinop Tand f1 f2) f3) Hval1 =
  formula_rep vv (Fbinop Timplies f1 (Fbinop Timplies f2 f3)) Hval2.
Proof.
  simpl. rewrite implb_curry.
  f_equal. apply fmla_rep_irrel.
  f_equal; apply fmla_rep_irrel.
Qed.

(*Lemma to rewrite both a term/formula and a proof at once*)
Lemma fmla_rewrite vv (f1 f2: formula) (Heq: f1 = f2)
  (Hval1: valid_formula sigma f1)
  (Hval2: valid_formula sigma f2):
  formula_rep vv f1 Hval1 = formula_rep vv f2 Hval2.
Proof.
  subst. apply fmla_rep_irrel.
Qed.

Lemma bool_of_binop_impl: forall b1 b2,
  bool_of_binop Timplies b1 b2 = all_dec (b1 -> b2).
Proof.
  intros. destruct b1; destruct b2; simpl;
  match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end;
  exfalso; apply n; auto.
Qed.

(*Some larger transformations we need for IndProp*)

(*We can push an implication across a forall if no free variables
  become bound*)
Lemma distr_impl_forall
(vv: @val_vars sigma pd vt)  
(f1 f2: formula) (x: vsymbol)
(Hval1: valid_formula sigma (Fbinop Timplies f1 (Fquant Tforall x f2)))
(Hval2: valid_formula sigma (Fquant Tforall x (Fbinop Timplies f1 f2))):
~In x (form_fv f1) ->
formula_rep vv
  (Fbinop Timplies f1 (Fquant Tforall x f2)) Hval1 =
formula_rep vv
  (Fquant Tforall x (Fbinop Timplies f1 f2)) Hval2.
Proof.
  intros Hnotin.
  rewrite fforall_rep, fbinop_rep, bool_of_binop_impl.
  apply all_dec_eq. rewrite fforall_rep. split; intros.
  - rewrite fbinop_rep, bool_of_binop_impl, simpl_all_dec.
    intros.
    assert (formula_rep vv f1
    (proj1 (valid_binop_inj (valid_formula_eq eq_refl Hval1)))). {
      erewrite form_fv_agree. erewrite fmla_rep_irrel. apply H0.
      intros. unfold substi.
      destruct (vsymbol_eq_dec x0 x); subst; auto. contradiction.
    }
    specialize (H H1).
    rewrite simpl_all_dec in H.
    specialize (H d).
    erewrite fmla_rep_irrel. apply H.
  - rewrite simpl_all_dec. intros d.
    specialize (H d).
    revert H. rewrite fbinop_rep, bool_of_binop_impl, simpl_all_dec;
    intros.
    erewrite fmla_rep_irrel.
    apply H. erewrite form_fv_agree. erewrite fmla_rep_irrel. apply H0.
    intros. unfold substi. destruct (vsymbol_eq_dec x0 x); subst; auto.
    contradiction.
Qed.

(*We can push an implication across a let, again assuming no
  free variables become bound*)
Lemma distr_impl_let (vv: @val_vars sigma pd vt)  
(f1 f2: formula) (t: term) (x: vsymbol)
(Hval1: valid_formula sigma (Fbinop Timplies f1 (Flet t x f2)))
(Hval2: valid_formula sigma (Flet t x (Fbinop Timplies f1 f2))):
~In x (form_fv f1) ->
formula_rep vv
  (Fbinop Timplies f1 (Flet t x f2)) Hval1 =
formula_rep vv
  (Flet t x (Fbinop Timplies f1 f2)) Hval2.
Proof.
  intros.
  rewrite flet_rep, !fbinop_rep, !bool_of_binop_impl.
  apply all_dec_eq.
  rewrite flet_rep.
  erewrite form_fv_agree.
  erewrite (form_fv_agree f2).
  erewrite fmla_rep_irrel.
  erewrite (fmla_rep_irrel _ f2).
  reflexivity.
  all: intros; unfold substi;
  destruct (vsymbol_eq_dec x0 x); subst; auto; try contradiction.
  unfold eq_rec_r, eq_rec, eq_rect. simpl.
  apply term_rep_irrel.
Qed.
  

(*TODO: move*)
(*If the formula is wf, we can move an implication
  across lets and foralls *)
(*NOTE: know no overlap because all vars in quants and lets
  come from f2 - must be bound vars in f2 (TODO: prove)
  so this is safe*)
Lemma distr_impl_let_forall (vv: @val_vars sigma pd vt)  
  (f1 f2: formula)
  (q: list vsymbol) (l: list (vsymbol * term))
  (Hval1: valid_formula sigma (fforalls q (iter_flet l (Fbinop Timplies f1 f2))))
  (Hval2: valid_formula sigma (Fbinop Timplies f1 (fforalls q (iter_flet l f2))))
  (Hq: forall x, ~ (In x q /\ In x (form_fv f1)))
  (Hl: forall x, ~ (In x l /\ In (fst x) (form_fv f1))) :
  formula_rep vv
    (fforalls q (iter_flet l (Fbinop Timplies f1 f2))) Hval1 =
  formula_rep vv
    (Fbinop Timplies f1 (fforalls q (iter_flet l f2))) Hval2.
Proof.
  revert vv.
  induction q.
  - (*Prove let case here*)
    induction l; auto.
    + simpl; intros. erewrite fmla_rep_irrel.
      erewrite (fmla_rep_irrel _ f2).
      reflexivity.
    + intros. simpl fforalls. erewrite distr_impl_let.
      * erewrite !flet_rep, IHl.
        f_equal. f_equal. apply term_rep_irrel.
        intros x C. apply (Hl x). split_all; auto. right; auto.
        (*Go back and do [valid_formula]*)
        Unshelve.
        simpl in Hval1. simpl in Hval2.
        inversion Hval1; subst.
        constructor; auto.
        inversion Hval2; subst.
        constructor; auto.
        inversion H6; subst; auto.
      * intro C. apply (Hl a). split_all; auto. left; auto.
  - intros vv. simpl fforalls.
    erewrite distr_impl_forall.
    + rewrite !fforall_rep. apply all_dec_eq.
      split; intros.
      * erewrite  <- IHq. apply H.
        intros. intro C. apply (Hq x). split_all; auto.
        right; auto.
      * erewrite IHq. apply H. intros. intro C. apply (Hq x).
        split_all; auto. right; auto.
        (*Go back and do [valid_formula]*)
        Unshelve.
        simpl in Hval1; simpl in Hval2; inversion Hval1; 
        inversion Hval2; subst.
        constructor; auto. constructor; auto.
        inversion H10; subst. auto.
    + intro C.
      apply (Hq a). split; auto. left; auto.
Qed.

(*Kind of a silly lemma, but we need to be able
  to rewrite the first of an implication without
  unfolding all bound variables
  *)
Lemma and_impl_bound  (vv: @val_vars sigma pd vt)  
(f1 f2 f3: formula)
(q: list vsymbol) (l: list (vsymbol * term))
Hval1 Hval2: 
formula_rep vv
  (fforalls q (iter_flet l (Fbinop Timplies (Fbinop Tand f1 f2) f3))) Hval1 =
formula_rep vv
  (fforalls q (iter_flet l (Fbinop Timplies f1 (Fbinop Timplies f2 f3)))) Hval2.
Proof.
  assert (A:=Hval1).
  assert (B:=Hval2).
  apply fforalls_valid_inj in A.
  apply fforalls_valid_inj in B. split_all.
  rewrite (fforalls_val') with(Hval1:=H1).
  rewrite (fforalls_val') with(Hval1:=H).
  assert (A:=H1).
  apply iter_flet_valid_inj in A.
  assert (B:=H).
  apply iter_flet_valid_inj in B.
  split_all.
  apply all_dec_eq. split; intros Hrep h.
  - specialize (Hrep h).
    rewrite fmla_rep_irrel with (Hval1:=H) 
      (Hval2:=iter_flet_valid  l _ H3 H4).
    rewrite fmla_rep_irrel with (Hval1:=H1)
      (Hval2:=iter_flet_valid l _ H5 H4) in Hrep.
    revert Hrep. rewrite !iter_flet_val.
    rewrite and_impl with(Hval2:=H3).
    intros C; apply C.
  - specialize (Hrep h).
    rewrite fmla_rep_irrel with (Hval1:=H) 
      (Hval2:=iter_flet_valid  l _ H3 H4) in Hrep.
    rewrite fmla_rep_irrel with (Hval1:=H1)
      (Hval2:=iter_flet_valid l _ H5 H4).
    revert Hrep. rewrite !iter_flet_val.
    rewrite and_impl with(Hval2:=H3).
    intros C; apply C.
Qed.

(*Last (I hope) intermediate lemma: we can
  push a let outside of foralls if the variable does not
  appear quantified and no free variables in the term appear in
  the list either*)
Lemma distr_let_foralls (vv: @val_vars sigma pd vt)  
(t: term) (x: vsymbol) (f: formula)
(q: list vsymbol) Hval1 Hval2:
(~ In x q) ->
(forall y, In y (term_fv t) -> ~ In y q) ->
formula_rep vv (fforalls q (Flet t x f)) Hval1 =
formula_rep vv (Flet t x (fforalls q f)) Hval2.
Proof.
  intros. revert vv. induction q; intros vv.
  - simpl fforalls. apply fmla_rep_irrel.
  - simpl fforalls. (*Here, we prove the single transformation*)
    rewrite fforall_rep, flet_rep, fforall_rep.
    assert (Hval3: valid_formula sigma (Flet t x (fforalls q f))). {
        simpl in Hval2. inversion Hval2; subst.
        inversion H6; subst. constructor; auto.
      }
    assert (Hnotx: ~ In x q). {
      intro C. apply H. right; auto.
    }
    assert (Hinq: forall y : vsymbol, In y (term_fv t) -> ~ In y q). {
      intros y Hy C. apply (H0 y); auto. right; auto.
    }
    apply all_dec_eq. split; intros Hrep d; specialize (Hrep d).
    + rewrite IHq with (Hval2:=Hval3) in Hrep; auto.
      rewrite flet_rep in Hrep.
      rewrite substi_diff.
      rewrite term_rep_irrel with(Hty2:=(proj1 (valid_let_inj (valid_formula_eq eq_refl Hval3)))).
      rewrite fmla_rep_irrel with (Hval2:=(proj2 (valid_let_inj (valid_formula_eq eq_refl Hval3)))).
      erewrite term_fv_agree in Hrep. apply Hrep.
      intros. unfold substi. destruct (vsymbol_eq_dec x0 a); subst; auto.
      exfalso. apply (H0 a); auto. left; auto.
      intro; subst. apply H. left; auto.
    + rewrite IHq with (Hval2:=Hval3); auto.
      rewrite flet_rep.
      rewrite substi_diff.
      rewrite term_rep_irrel with(Hty2:=(proj1 (valid_let_inj (valid_formula_eq eq_refl Hval2)))).
      rewrite fmla_rep_irrel with (Hval2:=(valid_quant_inj
      (valid_formula_eq eq_refl
         (proj2 (valid_let_inj (valid_formula_eq eq_refl Hval2)))))).
      erewrite term_fv_agree in Hrep. apply Hrep.
      intros. unfold substi. destruct (vsymbol_eq_dec x0 a); subst; auto.
      exfalso. apply (H0 a); auto. left; auto.
      intro; subst. apply H. left; auto.
Qed.

End Defs.

(*We need different pf's*)


(*Suppose we have a term/fmla and 2 pi_funpreds which agree
  on all predicates that are used. Then, their interp is equiv*)
(*TODO: maybe separate out funs and preds? Meh, prob not needed*)
(*This proof is not interesting, since we never adjust the
  pre-interp like we do the valuation. We just need to push through
  the induction*)
Lemma pi_predsym_agree (t: term) (f: formula) :
(forall (p1 p2: pi_funpred gamma_valid pd) 
  (v: val_vars pd vt) (ty: vty) 
  (Hty: term_has_type sigma t ty),
  (forall p, predsym_in_term p t -> 
    preds gamma_valid pd p1 p = preds gamma_valid pd p2 p) ->
  (forall f, funs gamma_valid pd p1 f = funs gamma_valid pd p2 f) ->
  term_rep p1 v t ty Hty = term_rep p2 v t ty Hty) /\
(forall (p1 p2: pi_funpred gamma_valid pd) (v: val_vars pd vt) 
  (Hval: valid_formula sigma f),
  (forall p, predsym_in p f -> 
    preds gamma_valid pd p1 p = preds gamma_valid pd p2 p) ->
  (forall f, funs gamma_valid pd p1 f = funs gamma_valid pd p2 f) ->
  formula_rep p1 v f Hval = formula_rep p2 v f Hval).
Proof.
  revert t f.
  apply term_formula_ind; simpl; intros; auto.
  - rewrite H1. f_equal. f_equal. f_equal.
    apply get_arg_list_eq.
    revert H; rewrite !Forall_forall; intros.
    rewrite (term_rep_irrel) with(Hty2:=Hty2).
    apply H; auto.
    intros p Hinp.
    apply H0. apply existsb_exists. exists x; auto. 
  - erewrite H. apply H0; auto. all: auto.
    all: intros; apply H1; rewrite H3; auto.
    rewrite orb_true_r. auto.
  - erewrite H. erewrite H1. erewrite H0. reflexivity.
    all: auto.
    all: intros p Hinp; apply H2; rewrite Hinp; simpl; auto;
    rewrite orb_true_r; auto.
  - (*match*) 
    inversion Hty; subst. clear H6 H10 H11.
    rename H8 into Hallpats.
    generalize dependent (proj1 (ty_match_inv (has_type_eq eq_refl Hty))).
    generalize dependent (proj2 (ty_match_inv (has_type_eq eq_refl Hty))).
    clear Hty.
    revert v0.
    induction ps; simpl; intros; auto.
    destruct a as [pat1 t1]; simpl.
    rewrite H with(p2:=p2) at 1; auto.
    destruct (match_val_single vt v (has_type_valid gamma_valid tm v t) (term_rep p2 v0 tm v t) pat1) eqn : Hm.
    + inversion H0; subst.
      apply H5; auto.
      intros. apply H1. simpl. rewrite H3; simpl. 
      rewrite orb_true_r; auto.
    + apply IHps; auto.
      * inversion H0; subst; auto.
      * intros. apply H1. simpl.
        rewrite orb_assoc, (orb_comm (predsym_in_term p tm)), <- orb_assoc, H3,
        orb_true_r; auto.
      * intros. apply Hallpats. right; auto.
    + intros. apply H1. rewrite H3; auto.
  - f_equal. apply functional_extensionality_dep.
    intros. erewrite H. reflexivity. all: auto.
  - (*Here, we use fact that predsym in*)
    rewrite H0; [|destruct (predsym_eq_dec p p); auto; contradiction].
    f_equal.
    apply get_arg_list_pred_eq.
    revert H; rewrite !Forall_forall; intros.
    rewrite (term_rep_irrel) with(Hty2:=Hty2).
    apply H; auto.
    intros p' Hinp'.
    apply H0. apply orb_true_iff. right. 
    apply existsb_exists. exists x; auto. 
  - destruct q; apply all_dec_eq.
    + split; intros Hall d; specialize (Hall d);
      erewrite H; try apply Hall; auto.
      intros. rewrite H0; auto.
    + split; intros [d Hall]; exists d;
      erewrite H; try apply Hall; auto.
      intros. rewrite H0; auto.
  - erewrite H. erewrite H0. reflexivity.
    all: auto. all: intros; apply H1; rewrite H3; auto;
    rewrite orb_true_r; auto.
  - erewrite H. erewrite H0. reflexivity.
    all: auto. all: intros p Hinp; apply H1; rewrite Hinp; auto;
    rewrite orb_true_r; auto.
  - erewrite H; auto.
  - erewrite H. apply H0.
    all: auto. all: intros p Hinp; apply H1; rewrite Hinp; auto;
    rewrite orb_true_r; auto.
  - erewrite H. erewrite H0. erewrite H1. reflexivity.
    all: auto. all: intros p Hinp; apply H2; rewrite Hinp; auto;
    rewrite !orb_true_r; auto.
  - (*match*) 
    inversion Hval; subst. clear H6 H9 H10.
    rename H8 into Hallpats.
    generalize dependent (proj1 (valid_match_inv (valid_formula_eq eq_refl Hval))).
    generalize dependent (proj2 (valid_match_inv (valid_formula_eq eq_refl Hval))).
    clear Hval.
    revert v0.
    induction ps; simpl; intros; auto.
    destruct a as [pat1 f1]; simpl.
    rewrite H with(p2:=p2) at 1; auto.
    destruct (match_val_single vt v (has_type_valid gamma_valid tm v t) (term_rep p2 v0 tm v t) pat1) eqn : Hm.
    + inversion H0; subst.
      apply H5; auto.
      intros. apply H1. simpl. rewrite H3; simpl. 
      rewrite orb_true_r; auto.
    + apply IHps; auto.
      * inversion H0; subst; auto.
      * intros. apply H1. simpl.
        rewrite orb_assoc, (orb_comm (predsym_in_term p tm)), <- orb_assoc, H3,
        orb_true_r; auto.
      * inversion Hallpats; subst; auto.
    + intros. apply H1. rewrite H3; auto.
Qed.

Lemma term_predsym_agree (t: term):
(forall (p1 p2: pi_funpred gamma_valid pd) 
  (v: val_vars pd vt) (ty: vty) 
  (Hty: term_has_type sigma t ty),
  (forall p, predsym_in_term p t -> 
    preds gamma_valid pd p1 p = preds gamma_valid pd p2 p) ->
  (forall f, funs gamma_valid pd p1 f = funs gamma_valid pd p2 f) ->
  term_rep p1 v t ty Hty = term_rep p2 v t ty Hty).
Proof.
  apply pi_predsym_agree. apply Ftrue.
Qed.

Lemma fmla_predsym_agree (f: formula):
(forall (p1 p2: pi_funpred gamma_valid pd) (v: val_vars pd vt) 
  (Hval: valid_formula sigma f),
  (forall p, predsym_in p f -> 
    preds gamma_valid pd p1 p = preds gamma_valid pd p2 p) ->
  (forall f, funs gamma_valid pd p1 f = funs gamma_valid pd p2 f) ->
  formula_rep p1 v f Hval = formula_rep p2 v f Hval).
Proof.
  apply pi_predsym_agree. apply (Tconst (ConstInt 0)).
Qed.

(*TODO: organization*)



  
End Denot.

(*
Section InterpEq.

Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma).


Definition val_val_eq {i1 i2: pre_interp gamma_valid}
{v1: valuation gamma_valid i1}
{v2: valuation gamma_valid i2}
(Heq1: (v_typevar gamma_valid i1 v1) =
(v_typevar gamma_valid i2 v2)) :
(forall x, valid_type sigma (v_typevar gamma_valid i2 v2 x)) =
(forall x, valid_type sigma (v_typevar gamma_valid i1 v1 x)).
destruct Heq1.
exact eq_refl.
Defined.

Definition pcast {P1 P2: Prop} (H: P1 = P2) (x: P1) : P2 :=
  match H with
  | eq_refl => x
  end.

(*TODO: move*)
(*Notion of when 2 valuations on equal (but not necessarily convertible)
  interpretations are the same*)
Definition val_equiv (i1 i2: pre_interp gamma_valid)
  (Hieq: i1 = i2)
  (v1: valuation gamma_valid i1)
  (v2: valuation gamma_valid i2) : Prop :=
  { Heq1: (v_typevar gamma_valid _ v1)=
  (v_typevar gamma_valid _ v2) &
  (v_typevar_val gamma_valid _ v1) =
  (pcast (val_val_eq Heq1) (v_typevar_val gamma_valid _ v2)) /\
  (v_vars gamma_valid _ v1) =
  (v_vars gamma_valid _ v2)
  
  }.
  /\
   /\
  .



(*Annoying to state (and hopefully not prove)*)
Lemma term_form_rep_interp_eq: forall (i1 i2: pre_interp gamma_valid)
  (Hieq: i1 = i2) (tm: term) (f: formula),
  (forall (v1: valuation gamma_valid i1) (ty: vty) (Hty1 Hty2:
    term_has_type sigma tm ty), 
      term_rep v tm ty Hty1 = term_rep v tm ty Hty2) /\
  (forall (v: valuation gamma_valid i) (Hval1 Hval2:
    valid_formula sigma f), 
      formula_rep v f Hval1 = formula_rep v f Hval2).

  
End Denot.
*)


(*Print Assumptions term_rep.*)