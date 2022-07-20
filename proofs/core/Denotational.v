(*Here we give a denotational semantics for Why3, assuming some classical axioms*)
Require Import Syntax.
Require Import Types.
Require Import Typing.
Require Import Semantics.
Require Import Coq.Program.Equality.

(*The axioms we need: excluded middle and definite description*)
Require Import Coq.Logic.ClassicalDescription.

(*This gives us the following (we give a shorter name)*)
Definition all_dec : forall (P : Prop), {P} + {~P} := excluded_middle_informative.

(*Can we interpret ADTs as Coq inductive types?*)

Section Denot.

Variable sigma : sig.
Variable gamma: context.
Variable gamma_valid: valid_context sigma gamma.
Variable i: pre_interp sigma gamma gamma_valid.

(*Representation of terms, formulas, patterns*)

Notation dom x := (domain sigma gamma gamma_valid i x).
Notation val x := (v_subst (v_typevar sigma gamma gamma_valid i x)). 

(*TODO: 2 options: can take in hypothesis that term has type ty and then use
  dependent type obligations
  OR just match on type and return option (but then we need options everywhere)
  
  for now, use typing hypothesis - this makes the function stuff a bit easier
  and we shouldn't have to match on types everywhere
  *)

Definition cast_dom_vty {v: valuation sigma gamma gamma_valid i} 
{v1 v2: vty} (Heq: v1 = v2) (x: dom (val v v1)) : dom (val v v2).
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
     + assert (Hin:=i0). 
       apply (ty_subst_fun_in params args vty_int v0 H) in i0; auto.
       destruct i0 as [ty [Hinty Hty]]. rewrite !Hty.
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
    
(*We use the above to get the arg list (tentatively)*)
Definition get_arg_list (v: valuation sigma gamma gamma_valid i)
  (f: funsym) (vs: list vty) (ts: list term) (reps: forall
    (v: valuation sigma gamma gamma_valid i) (t: term) (ty: vty),
    term_has_type sigma t ty ->
    dom (val v ty))
  (Hty: exists x, term_has_type sigma (Tfun f vs ts) x) : 
  arg_list (domain sigma gamma gamma_valid i)
    (funsym_sigma_args f
      (map (v_subst (v_typevar sigma gamma gamma_valid i v)) vs)).
Proof.
  (*assume we have decidable typechecking - no axioms yet*)
  assert ({x: vty | term_has_type sigma (Tfun f vs ts) x}) by admit.
  destruct X as [vty Hty'].
  apply fun_ty_inversion in Hty'. repeat match goal with | H: ?P /\ ?Q |- _ => destruct H end.
  specialize (reps v).
  unfold funsym_sigma_args.
  generalize dependent (s_args f). induction ts; simpl; intros.
  - assert (l = nil). apply length_zero_iff_nil. rewrite H1; reflexivity.
    rewrite H5. simpl. apply AL_nil.
  - destruct l as [|a1 atl] eqn : Hargs.
    + inversion H1.
    + simpl in H1. simpl in H3. assert (A:=H3).
      apply Forall_inv in H3. apply Forall_inv_tail in A. simpl.
      apply AL_cons.
      * specialize (reps a). simpl in H3.
        specialize (reps _ H3).
        rewrite <- funsym_subst_eq; auto. destruct f; simpl in *.
        eapply reflect_iff. apply nodup_NoDup. apply s_params_nodup.
      * apply IHts; auto.
Admitted.

Fixpoint term_rep (v: valuation sigma gamma gamma_valid i) (t: term) (ty: vty)
  (Hty: term_has_type sigma t ty) : dom (val v ty) :=
  match t with
  (*| Tconst (ConstInt z) =>
    (*TODO: should we rule out w dependent type or continue with option?*)
    match ty as s return s = ty -> option (dom (val v ty)) with
    | vty_int => fun Heq => Some (cast_dom_vty Heq (z_to_dom sigma gamma gamma_valid i v z))
    | _ => fun _ => None
    end eq_refl
  | Tconst (ConstReal r) =>
    match ty as s return s = ty -> option (dom (val v ty)) with
    | vty_real => fun Heq => Some (cast_dom_vty Heq (r_to_dom sigma gamma gamma_valid i v r))
    | _ => fun _ => None
    end eq_refl
  | Tvar x ty' =>
    match (vty_eq_dec ty' ty) with
    | left _ => Some (var_to_dom sigma gamma gamma_valid i v x ty)
    | _ => None
    end*)
  | Tfun f vs ts =>
    (*TODO: remove axioms - will be hypothesis and need uniqueness of types*)
    match (all_dec (exists x, term_has_type sigma (Tfun f vs ts) x)) with
    | left Hty => 
      (*In real one, do with proof*)
      match (vty_eq_dec ty (funsym_sigma_ret f (map (val v) vs))) with
      | left Heq => (*(cast_dom_vty _ *) 
        (*TODO: start with this - get types to work out, see if induction does
          Then go back to typechecker, injectivity of types,
          inversion lemmas most likely*)
      
      ((funs _ _ _ i) f (map (val v) vs) 
          (get_arg_list v f vs ts term_rep Hty))
      | _ => match domain_ne sigma gamma gamma_valid i (val v ty) with
            | DE _ _ x => x
            end
      end
    
    
    | _ => None
    end
  | _ => match domain_ne sigma gamma gamma_valid i (val v ty) with
          | DE _ _ x => x
          end
  end.

Check excluded_middle_informative.
Print Assumptions excluded_middle_informative.

