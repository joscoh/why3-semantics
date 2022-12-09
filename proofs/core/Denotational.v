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
Fixpoint bnd_p (p: pattern) : list vsymbol :=
  match p with
  | Pvar v => [v]
  | Pconstr f tys ps => concat (map bnd_p ps)
  | Pwild => nil
  | Por p1 p2 => (bnd_p p1) ++ (bnd_p p2)
  | Pbind p1 v => v :: (bnd_p p1)
  end.

Lemma or_false_r (P: Prop):
  (P \/ False) <-> P.
Proof.
  split; intros; auto. destruct H; auto. destruct H.
Qed.

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
Qed.

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
      (map (fun p => if in_bool vsymbol_eq_dec x (bnd_p (fst p)) then
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
    (map (fun p => if in_bool vsymbol_eq_dec x (bnd_p (fst p)) then
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
      (fun p => bnd_p (fst p) ++ bnd_f (snd p)) ps)
  end
with bnd_t (t: term) : list vsymbol :=
  match t with
  | Tconst c => nil
  | Tvar v  => 
    [v]
  | Tfun fs tys tms =>
    concat (map bnd_t tms)
  | Tlet tm1 v tm2 =>
    v :: bnd_t tm1 ++ bnd_t tm2
  | Tif f1 t1 t2 =>
    bnd_f f1 ++ bnd_t t1 ++ bnd_t t2
  | Tmatch tm ty ps =>
    bnd_t tm ++ concat (map
      (fun p => bnd_p (fst p) ++ bnd_t (snd p)) ps)
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

Ltac simpl_all_dec :=
  repeat match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end.

Lemma all_dec_eq: forall (P Q: Prop),
  (P <-> Q) ->
  (@eq bool (proj_sumbool _ _ (all_dec P)) (proj_sumbool _ _ (all_dec Q))).
Proof.
  intros. simpl_all_dec; exfalso.
  - apply n. apply H. apply p.
  - apply n. apply H. apply q.
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
  In x (bnd_p p) <-> In x (map fst l).
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
      simpl. rewrite map_app, !in_app_iff, Hmatch, Hmatch0.
      reflexivity.
  - simpl. intros. inversion H; subst. reflexivity.
  - simpl. intros. destruct (match_val_single vt ty Hval d p1) eqn: Hm.
    + inversion H; subst. inversion Hpat; subst.
      apply (IHp1 _ ty') in Hm; auto.
      rewrite in_app_iff, Hm, bnd_fv_p. 
      rewrite <- H6, <- bnd_fv_p, Hm, or_idem. 
      reflexivity.
    + inversion Hpat; subst.
      apply (IHp2 _ ty') in H; auto.
      rewrite in_app_iff, H, bnd_fv_p. 
      rewrite H6, <- bnd_fv_p, H, or_idem.
      reflexivity.
  - simpl. intros.
    destruct (match_val_single vt ty Hval d p) eqn : Hm.
    + destruct (vty_eq_dec (snd v) ty); inversion H; subst. simpl.
      inversion Hpat; subst.
      apply (IHp _ (snd v)) in Hm; auto.
      rewrite Hm. reflexivity.
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
    (map (fun p => if in_bool vsymbol_eq_dec x (bnd_p (fst p)) then
      p else (fst p, sub_t x y (snd p))) ps)) _ _ eq_refl Hty2))).
    generalize dependent (proj2 (ty_match_inv (@has_type_eq sigma
    (Tmatch (sub_t x y tm) v
    (map (fun p => if in_bool vsymbol_eq_dec x (bnd_p (fst p)) then
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
      destruct (in_bool vsymbol_eq_dec x (bnd_p p1)) eqn : Hinp1.
      * intros.
        rewrite <- H with(Heq:=Heq) (Hty1:=Hty2) by solve_bnd.
        rewrite match_val_single_irrel with (Hval2:=(has_type_valid gamma_valid tm v Hty2)).
        rewrite Hmatch.
        assert (In x (map fst newval)). {
          apply (match_var_single_free_var) with(x:=x)(ty':=v) in Hmatch.
          apply Hmatch. destruct (in_bool_spec vsymbol_eq_dec x (bnd_p p1)); auto.
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
          apply Hmatch in C. destruct (in_bool_spec vsymbol_eq_dec x (bnd_p p1)); auto.
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
       assert (In y (bnd_p p1)). apply Hmatch. rewrite in_map_iff.
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
      destruct (in_bool vsymbol_eq_dec x (bnd_p p1)) eqn : Hinp1.
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
      destruct (in_bool vsymbol_eq_dec x (bnd_p p1)) eqn : Hinp1.
      * intros.
        rewrite <- H with(Heq:=Heq) (Hty1:=Hty2) by solve_bnd.
        rewrite match_val_single_irrel with (Hval2:=(has_type_valid gamma_valid tm v Hty2)).
        rewrite Hmatch.
        assert (In x (map fst newval)). {
          apply (match_var_single_free_var) with(x:=x)(ty':=v) in Hmatch.
          apply Hmatch. destruct (in_bool_spec vsymbol_eq_dec x (bnd_p p1)); auto.
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
          apply Hmatch in C. destruct (in_bool_spec vsymbol_eq_dec x (bnd_p p1)); auto.
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
       assert (In y (bnd_p p1)). apply Hmatch. rewrite in_map_iff.
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
      destruct (in_bool vsymbol_eq_dec x (bnd_p p1)) eqn : Hinp1.
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
  - (*TODO: match case*)
    admit.
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
  - (*other match*)
    admit.
Admitted.

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

Definition sublist {A: Type} (l: list A) (lo hi: nat) : list A.
Admitted.

(*Split a list into pieces of the appropriate lengths if we can*)
Fixpoint split_lens {A: Type} (l: list A) (lens: list nat) :
  list (list A) :=
  match lens with
  | len :: tl => sublist l 0 len :: 
    split_lens (sublist l (len + 1) (length l)) tl
  | nil => nil
  end.

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

(*Easier to have separate function for pattern*)
(*Hmm, need to think a bit more - how should patterns work?
  *)

(*TODO: want bound variables for patterns because we care about
  lengths*)

(*Alpha substitute for patterns only in the given term/formula*)
Fixpoint alpha_p_aux {A: Type} (sub: vsymbol -> vsymbol -> A -> A) 
  (p: pattern) (x: A) (l: list string) : (pattern * A) :=
  match p with
  | Pvar v => 
    match l with
    | nil => (p, x)
    | str :: tl =>
      let v' := (str, snd v) in
      (Pvar v', sub v v' x)
    end
  | Pwild => (p, x)
  | Por p1 p2 =>
    (*NOTE: must have same free vars*)
    let (p1', x1) := alpha_p_aux sub p1 x l in
    let (p2', x2) := alpha_p_aux sub p2 x l in
    (Por p1 p2, x2)
  | Pbind p1 v =>
    match l with
    |nil => (p, x)
    | str :: tl =>
      let v' := (str, snd v) in
      let (p2, x1) := (alpha_p_aux sub p1 x tl) in
      (p2, sub v v' x1)
    end
  | Pconstr f tys pats =>
    (*Split list into lists of appropriate length*)
    (*Split up the list into pieces of appropriate lengths 
      (size (bnd_t tm))*)
      let lens := map (fun tm => length (bnd_p tm)) pats in
      let l_split := split_lens l lens in
      let (ps', xnew) := ((fix alpha_ps_aux (l1: list pattern) (l2: list (list string)) (y: A) :
        (list pattern * A) :=
        match l1, l2 with
        | (ph :: pt), (s1 :: st) =>
            let (pnew, y1) := alpha_p_aux sub ph y s1 in
            let (prest, y2) := alpha_ps_aux pt st y1 in
            (pnew :: prest, y2)
        | _, _ =>
          (nil, y)
        end) pats l_split x) in
      (Pconstr f tys ps', xnew)
    end.
(*Proving this correct will not be too fun, but let's see*)
(*
Print term.
Print bnd_t.
Print sub_t.
(*TOOD: might not be able to use map, see*)
Fixpoint alpha_t_aux (t: term) (l: list string) {struct t} : term :=
  (*We only care about the bound variable and inductive cases*)
  match t with
  | Tlet t1 x t2 => 
    match l with
    | str :: _ => Tlet t1 (str, snd x) (sub_t x (str, snd x) t2)
    | _ => t
    end
  | Tfun fs tys tms =>
    (*Split up the list into pieces of appropriate lengths 
      (size (bnd_t tm))*)
    let lens := map (fun tm => length (bnd_t tm)) tms in
    let l_split := split_lens l lens in
    Tfun fs tys (map (fun (t: term * list string) =>
      let (tm, l') := t in alpha_t_aux tm l') (combine tms l_split))
  | Tif f t1 t2 =>
    let f_sz := length (bnd_f f) in
    let t1_sz := length (bnd_t t1) in
    Tif (alpha_f_aux f (sublist l 0 f_sz)) 
      (alpha_t_aux t1 (sublist l (f_sz + 1) (f_sz + 1 + t1_sz)))
      (alpha_t_aux t2 (sublist l (f_sz + 1 + t1_sz + 1) (length l)))
  | Tmatch t1 ty ps =>
    (*First do the pattern substitutions, then do the terms
      recursively*)
    let lens := map (fun x => length (bnd_p (fst x)) + 
      length (bnd_t (snd x))) ps in
    let l_split := split_lens l lens in
    let t1_sz := length (bnd_t t1) in
    Tmatch (alpha_t_aux t1 (sublist l 0 t1_sz)) ty
      (map (fun (t: (pattern * term) * list string) => let (x, strs):= t in
        let p_sz := length (bnd_p (fst x)) in
        let l1 := sublist strs 0 p_sz in
        let l2 := sublist strs p_sz (length strs) in
        let (p1, y) := alpha_p_aux sub_t (fst x) (snd x) l1 in
        (p1, alpha_t_aux y l2)
        ) (combine ps l_split))
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
    Fpred ps tys (map (fun (t: term * list string) =>
      let (tm, l') := t in alpha_t_aux tm l') (combine tms l_split))
  | _ => f
  end.

    (fix alpha_ts_aux (l: list (pattern * term)) :
      list (pattern * term)
    let ps_p

    (*harder*)
    
    Tmatch (alpha_t_aux t1 (sublist l 0 t1_sz)) ty
      (fun (p: pattern * term) =>



      
      )




    Tfun fs tys 
  | Tconst _ => t
  | Tvar v => t

Lemma alpha_t_aux_correct (t: term) (l: list vsymbol),
  NoDup l ->
  (forall x, In x l -> ~ In x (map fst (term_fv t))) ->
  length l = length (bnd_t t) ->
  term_interp (alpha_t_aux t l) Hty =
  term_interp t Hty /\
  term_wf (alpha_t_aux t l).


(*Let's try*)
Definition 
*)
End Alpha.

(*TODO: move rewrite lemmas*)

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

(*TODO: maybe move above*)
(*Lemma to rewrite both a term/formula and a proof at once*)
Lemma fmla_rewrite vv (f1 f2: formula) (Heq: f1 = f2)
  (Hval1: valid_formula sigma f1)
  (Hval2: valid_formula sigma f2):
  formula_rep vv f1 Hval1 = formula_rep vv f2 Hval2.
Proof.
  subst. apply fmla_rep_irrel.
Qed.

End Defs.

(*We need different pf's*)
Check formula_rep.
Check predsym_in_term.
(*TODO: move*)
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