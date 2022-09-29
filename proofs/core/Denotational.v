(*Here we give a denotational semantics for Why3, assuming some classical axioms*)
Require Import Syntax.
Require Import Types.
Require Import Typing.
Require Import IndTypes.
Require Import Semantics.
Require Import Hlist.
Require Import Coq.Program.Equality.

(*The axioms we need: excluded middle and definite description*)
Require Import Coq.Logic.ClassicalDescription.

(*This gives us the following (we give a shorter name)*)
Definition all_dec : forall (P : Prop), {P} + {~P} := excluded_middle_informative.

(*Can we interpret ADTs as Coq inductive types?*)

Section Denot.

Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma)
  (i: pre_interp gamma_valid).

(*Representation of terms, formulas, patterns*)

Notation domain := (domain (dom_aux gamma_valid i)).
Notation val x :=  (v_subst (v_typevar gamma_valid i x)).
Notation v_typevar := (v_typevar gamma_valid i).
Notation funs := (funs gamma_valid i).
Notation substi := (substi gamma_valid i).

(*TODO: 2 options: can take in hypothesis that term has type ty and then use
  dependent type obligations
  OR just match on type and return option (but then we need options everywhere)
  
  for now, use typing hypothesis - this makes the function stuff a bit easier
  and we shouldn't have to match on types everywhere
  *)

Definition cast_dom_vty {v: valuation gamma_valid i} 
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

Axiom typecheck_dec: forall s t,
  (exists x, term_has_type s t x) ->
  { x | term_has_type s t x}.

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
Definition get_arg_list (v: valuation gamma_valid i)
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

(*Also need a version for preds (TODO: can we reduce duplication?)*)
Definition get_arg_list_pred (v: valuation gamma_valid i)
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

(*TODO: move*)
Lemma tfun_params_length {s f vs ts ty}:
  term_has_type s (Tfun f vs ts) ty ->
  length (s_params f) = length vs.
Proof.
  intros. inversion H; subst. rewrite H8. reflexivity.
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

Lemma ty_var_inv {s x ty ty'} (H: term_has_type s (Tvar x ty') ty):
ty = ty'.
Proof.
  inversion H; auto.
Qed.

Lemma ty_let_inv {s t1 x ty1 t2 ty} (H: term_has_type s (Tlet t1 x ty1 t2) ty):
term_has_type s t1 ty1 /\ term_has_type s t2 ty.
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

(*TODO: add stuff about xs*)
Lemma ty_match_inv {s t ty1 ty2 xs} (H: term_has_type s (Tmatch t ty1 xs) ty2):
  term_has_type s t ty1.
Proof.
  inversion H; auto.
Qed.

Lemma valid_not_inj {s f} (H: valid_formula s (Fnot f)):
  valid_formula s f.
Proof.
  inversion H; auto.
Qed.

Lemma valid_let_inj {s t x ty f} (H: valid_formula s (Flet t x ty f)):
term_has_type s t ty /\
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

Lemma valid_quant_inj {s q x ty f} (H: valid_formula s (Fquant q x ty f)):
  valid_formula s f.
Proof.
  inversion H; auto.
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

Check find.
Search find.
Locate find.

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
      proj1_sig (is_sort_cons_sorts t l (is_sort_cons t l i0)))).
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
    generalize dependent (is_sort_cons (adt_name a) l i0).
    intros H.
    destruct (is_sort_cons_sorts (adt_name a) l H). simpl.
    rewrite <- e; reflexivity.
  - inversion H.
Qed.

Check find_constr_rep.
Print pre_interp.
Check adts.

(*We handle pattern matches slightly differently than in the paper.
  We build up a complete valuation that binds all of the pattern
  variables to the domain values, then interpret the resulting term
  or formula using this valuation. We provide a function that gives
  the valuation and the term/formula to abstract out the common
  functionality.*)
Fixpoint match_val_single (v: valuation gamma_valid i) (ty: vty)
  (d: domain (val v ty))
  (p: pattern) : option (valuation gamma_valid i) :=
  match p with
  | Pvar x _ => Some (substi v x ty d)
  | Pwild => Some v
  | Por p1 p2 => match (match_val_single v ty d p1) with
                  | Some v1 => Some v1
                  | None => match_val_single v ty d p2
                  end
  | Pbind p1 x _ => match_val_single (substi v x ty d) ty d p1 
    (*TODO: is this right - do we evaluation pattern with additional binding?*)
  | Pconstr f vs ps =>
    match (is_sort_adt (val v ty)) as o return
      (is_sort_adt (val v ty)) = o -> option (valuation gamma_valid i)
    with
    | Some (m, a, ts, srts) => fun Hisadt =>
      (*So now (with result about, we know that sort is ADT)*)
      (*Now we need to cast this to adt_rep*)
      (*First, get info about a, m, srts from [is_sort_adt_spec]*)
      match (is_sort_adt_spec _ _ _ _ _ Hisadt) with
      | conj Hseq (conj a_in (conj m_in Htseq)) =>
        (*We cast to get an ADT, now that we know that this actually is
          an ADT*)
        let adt : adt_rep m srts (dom_aux gamma_valid i) a a_in :=
          scast (adts gamma_valid i m srts a a_in) (dom_cast _ Hseq d) in
          None
        (*TODO: need to know that length of srts is correct - need to know
          that type itself is well-typed (then use separate lemma to show
          this, need to know that args are same for all which I believe is
          current assumption)*)
        (*let f := find_constr_rep gamma_valid m m_in srts (*TODO*) _ 
          _ a a_in (adts gamma_valid i m srts a a_in)*)
          (*TODO: need uniformity*)
          (*TODO: need to cast this to [adt_rep m srts domain_aux a a_in]*)
      (*let f := find_constr_rep gamma_valid m *)
      end 



      
    | None => fun _ => None
    end eq_refl
    (*Idea: see if sort is ADT - need function to do this + get parts*)
    (*if not, give None*)
    (*if so, get constr_rep and see if equals f, if not None*)
    (*if equals f, then take arg list, eval list of patterns on this
      will need to know that this is (val v ty) for each ty - hopefully
      not too hard to show*)
  end.


(*First, we handle matches - we will take in isf and projf as predicates
  and give them later - TODO: hopefully it works*)
(*This makes dependent types much nicer*)
(*TODO: factor out term/formula parts*)
Fixpoint match_rep (isf: funsym -> term -> bool) 
  (projf: forall (f: funsym) (tm: term) (Hisf: isf f tm), list term)
  (t: term) (p: pattern) (b h: option term) {struct p} : option term :=
  match p with
  | Pvar v ty => option_map (fun t2 => Tlet t v ty t2) b
  | Pwild => b
  | Por p1 p2 => match_rep isf projf t p1 b (match_rep isf projf t p2 b h)
  | Pbind p1 v ty => option_map (fun t2 => Tlet t v ty t2) (match_rep isf projf t p1 b h) 
  | Pconstr f nil ps => if (isf f t) then b else h
  | Pconstr f vs ps =>
    (*This case is a bit ugly - maybe try to remove dependent types*)
    (match (isf f t) as b return (isf f t) = b -> option term with
    | true => fun Hisf =>
      let ts := projf f t Hisf in
      (fix match_reps (tms: list term) (pats: list pattern) {struct pats} : option term :=
      match tms, pats with
      | t1 :: ttl, p1 :: ptl => match_rep isf projf t1 p1 (match_reps ttl ptl) h
      | _, _ => None
      end) ts ps
    | false => fun _ => h
    end) eq_refl
  end.

(* There are many dependent type obligations and casting to ensure that
  the types work out. In each case, we separate the hypotheses and give
  explicit types for clarity. The final result is often quite simple and just
  needs 1 or more casts for dependent type purposes. *)
Fixpoint term_rep (v: valuation gamma_valid i) (t: term) (ty: vty)
  (Hty: term_has_type sigma t ty) {struct t} : domain (val v ty) :=
  (match t as tm return t = tm -> domain (val v ty) with
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
  | Tvar x ty' => fun Htm =>

    var_to_dom _ _ v x ty
  | Tfun f vs ts => fun Htm =>
    (*Some proof we need; we give types for clarity*)
    let Hty': term_has_type sigma (Tfun f vs ts) ty :=
      has_type_eq Htm Hty in
    let Htyeq : ty_subst (s_params f) vs (s_ret f) = ty :=
      eq_sym (ty_fun_ind_ret Hty') in
    (*The main typecast: v(sigma(ty_ret)) = sigma'(ty_ret), where
      sigma sends (s_params f)_i -> vs_i and 
      sigma' sends (s_params f) _i -> v(vs_i)*)
    let Heqret : v_subst (v_typevar v) (ty_subst (s_params f) vs (s_ret f)) =
      ty_subst_s (s_params f) (map (v_subst (v_typevar v)) vs) (s_ret f) :=
        funsym_subst_eq (s_params f) vs (v_typevar v) (s_ret f) (s_params_nodup f)
        (tfun_params_length Hty') in

    (* The final result is to apply [funs] to the [arg_list] created recursively
      from the argument domain values. We need two casts to make the dependent
      types work out*)
  
    cast_dom_vty Htyeq (
      dom_cast (dom_aux gamma_valid i)
        (eq_sym Heqret)
          ((funs f (map (val v) vs)) 
            (get_arg_list v f vs ts (term_rep v) (ex_intro _ ty Hty'))))
  | Tlet t1 x ty1 t2 => fun Htm =>
    let Hty' : term_has_type sigma (Tlet t1 x ty1 t2) ty :=
      has_type_eq Htm Hty in
    let Ht1 : term_has_type sigma t1 ty1 :=
      proj1 (ty_let_inv Hty') in
    let Ht2 : term_has_type sigma t2 ty :=
      proj2 (ty_let_inv Hty') in 

    term_rep (substi v x ty1 (term_rep v t1 ty1 Ht1)) t2 ty Ht2

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
(*
  | Tmatch t ty1 xs => fun Htm =>
    let Hty' : term_has_type sigma (Tmatch t ty1 xs) ty :=
      has_type_eq Htm Hty in
    let Ht1 : term_has_type sigma t ty1 :=
      ty_match_inv Hty' in
    (*t has type vty_cons ts vs*)
    (*Doesn't work: not structurally decreasing*)
    (*I think we will have to go directly - dependent types will be ugly*)
    (*May need assumption about alg type*)
    (*TODO: start here*)

    let isf (f: funsym) (tm: term) (ty: vty) (Htm: term_has_type sigma tm ty) : bool :=
      all_dec (exists vs ts (H: term_has_type sigma (Tfun f vs ts) ty), 
        term_rep v tm ty Htm = term_rep v (Tfun f vs ts) ty H)
    in
(*

      all_dec (exists t (Hf: In f constrs) (Hlen: length (s_params c) = 
        length (map val vs)),
      term_rep v tm (vty_cons ts vs) = 
      (adt_typesym_funsym _ Hadt Hc Hlen) ((funs c (map val vs)) t))  in
  *)
      match domain_ne sigma gamma gamma_valid i (val v ty) with
      | DE _ _ x => if (isf id_fs t ty1 Ht1) then x else x
      end



     (* (forall (x: domain (typesym_to_sort a srts)), 
      exists c t (Hc: In c constrs) (Hlen: length (s_params c) = length srts),
      x = (dom_cast_aux domain _ _
        (adt_typesym_funsym _ Hadt Hc Hlen) ((funs c srts) t)))*)
  *)
  (*For cases not handled yet*)
  | _ => match domain_ne gamma_valid i (val v ty) with
          | DE x => fun _ => x
          end
  end) eq_refl

with formula_rep (v: valuation gamma_valid i) (f: formula) 
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
  | Flet t x ty f' => fun Hf =>
    let Hval' : valid_formula sigma (Flet t x ty f') :=
      valid_formula_eq Hf Hval in
    let Ht: term_has_type sigma t ty :=
      (proj1 (valid_let_inj Hval')) in
    let Hf': valid_formula sigma f' :=
      (proj2 (valid_let_inj Hval')) in

    formula_rep (substi v x ty (term_rep v t ty Ht)) f' Hf'
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

    preds _ _ p (map (val v) vs)
      (get_arg_list_pred v p vs ts (term_rep v) Hval')

  | Fquant Tforall x ty f' => fun Hf =>
    let Hval' : valid_formula sigma (Fquant Tforall x ty f') :=
      valid_formula_eq Hf Hval in
    let Hf' : valid_formula sigma f' :=
      valid_quant_inj Hval' in

    (*NOTE: HERE is where we need the classical axiom assumptions*)
    all_dec (forall d, formula_rep (substi v x ty d) f' Hf')

  | Fquant Texists x ty f' => fun Hf =>
    let Hval' : valid_formula sigma (Fquant Texists x ty f') :=
      valid_formula_eq Hf Hval in
    let Hf' : valid_formula sigma f' :=
      valid_quant_inj Hval' in

    (*NOTE: HERE is where we need the classical axiom assumptions*)
    all_dec (exists d, formula_rep (substi v x ty d) f' Hf')
  | Feq ty t1 t2 => fun Hf =>
    let Hval' : valid_formula sigma (Feq ty t1 t2) :=
      valid_formula_eq Hf Hval in
    let Ht1 : term_has_type sigma t1 ty := 
      proj1 (valid_eq_inj Hval') in
    let Ht2 : term_has_type sigma t2 ty :=
      proj2 (valid_eq_inj Hval') in

    (*TODO: require decidable equality for all domains?*)
    all_dec (term_rep v t1 ty Ht1 = term_rep v t2 ty Ht2)
  (*TODO*)
  | _ => fun _ => true
  end) eq_refl
  

  .

(*Let's be better about dependent types - will say we have term of
  type vty_cons ts vs, where ts is an ADT.
  Then, from restriction, we know there exists some constructor and values
  such that [[t]]_v = [[f]][[ts]] - this predicate holds exactly when f = constr
  Maybe dont need dep types, maybe just prove later that 1 is always true
  based on semantics, and exhaustive match ensures no errors
  may need some casting

  will be independent of valuation because we only care about the type of the term
  ie: [[t]]_v gives some element of [[v(ts(alpha))]] = [[ts(v(alpha))]]
  I am wrong: this should affect it: but we know that there is some (constructor)
  f and ts
  such that [[t]]_v = [[f(v(alpha))]](ts)

  isf should return true iff f = constr

  projf f ts' should return true iff f = constr and ts = [[ts']]
  *)
(*with isf (v: valuation sigma gamma gamma_valid i) 
  (t: term) (ts: typesym) (vs: list vty) (Hty: term_has_type sigma t (vty_cons ts vs)) 
  (constr: funsym) : bool :=
  all_dec (exists tms (Htms: term_has_type sigma (Tfun constr vs tms) (vty_cons ts vs)), 
    term_rep v t (vty_cons ts vs) Hty = 
    term_rep v (Tfun constr vs tms) _ Htms).
    funs constr*) 

End Denot.

