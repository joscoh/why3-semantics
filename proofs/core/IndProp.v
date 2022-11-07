Inductive even : nat -> Prop :=
  | ev0: even 0
  | evSS: forall n, even n -> even (S (S n)).

Definition even_ind_ty : Prop :=
forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, even n -> P n -> P (S (S n))) ->
    forall n : nat, even n -> P n.

(*Let's see*)
Definition test1 : nat -> Prop :=
  fun m => forall (P: nat -> Prop),
    P 0 ->
    (forall n, P n -> P(S (S n))) ->
    P m.

Lemma see: forall n, even n -> test1 n.
Proof.
  intros n He. unfold test1. intros P Hp0 Hps. induction He.
  auto. subst. apply Hps. auto.
Qed.

Lemma see2: forall n, test1 n -> even n.
Proof.
  intros n. unfold test1. intros Htest.
  specialize (Htest even). apply Htest; constructor. auto.
Qed.

Lemma equiv: forall n, even n <-> test1 n.
Proof.
  intros n. split. apply see. apply see2.
Qed.

(*Prove least fixpoint*)
Lemma least_fp : forall (P: nat -> Prop),
  P 0 ->
  (forall n, P n -> P(S (S n))) ->
  (forall m, test1 m -> P m).
Proof.
  intros P H0 Hs m. unfold test1; intros. apply H; auto.
Qed.
(*Other direction does not hold (as it shouldn't)*)
Lemma least_fp' : forall (P: nat -> Prop),
  P 0 ->
  (forall n, P n -> P(S (S n))) ->
  (forall m, P m -> test1 m).
Proof.
  intros P H0 Hs m Hp. unfold test1. intros.
Abort.

(*What if we had something non strictly positive?*)
Fail Inductive bad : nat -> Prop :=
  | Bad1: forall n, (bad n <-> bad n) -> bad (S n).

Definition bad1 : nat -> Prop :=
    fun m => forall (P: nat -> Prop),
      (forall n, (P n <-> P n) -> P (S m)).
(*So this is definable - problem is that it isn't really usable?*)
(*So i think the idea is: if non strictly positive, this Prop may
not be inhabited - but yeah, where do we need this info?*)

(*Now let's try*)
Require Import Common.
Require Import Syntax.
Require Import Types.
Require Import Typing.
Require Import IndTypes.
Require Import Semantics.
Require Import Denotational.

Section IndPropRep.

Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma)
  (i: pre_interp gamma_valid).

Variable all_unif: forall m,
  mut_in_ctx m gamma ->
  uniform m.

Lemma valid_ind_pred: forall p p' (tys: list vty) tms,
  valid_ind_form p (Fpred p' tys tms) ->
  tys = map vty_var (p_params p) /\
  length (p_args p) = length tms /\
  p = p'.
Proof.
  intros. inversion H; subst; auto.
Qed.
(*See*)

Print pre_interp.
Print scast.
Print i.
(*Alternate approach*)

Definition interp_with_P (pi: pre_interp gamma_valid) (p: predsym) 
  (P: forall srts, 
    arg_list (domain (dom_aux _ pi)) (predsym_sigma_args p srts) -> bool) :
  pre_interp gamma_valid :=
  {|
  dom_aux := dom_aux gamma_valid pi;
  domain_ne := domain_ne gamma_valid pi;
  funs := funs gamma_valid pi;
  preds :=
    fun pr : predsym =>
    match predsym_eq_dec p pr with
    | left Heq =>
        match Heq with
        | eq_refl => P
        end
    | _ => preds gamma_valid pi pr
    end;
  adts := adts gamma_valid pi;
  constrs := constrs gamma_valid pi
|}.

(*Any valuation is equivalent under each interpretation*)
Definition interp_P_val pi p P (v: valuation gamma_valid pi):
  valuation gamma_valid (interp_with_P pi p P).
apply (Build_valuation gamma_valid _ 
  (v_typevar _ _ v) 
  (v_typevar_val _ _ v)).
apply (v_vars _ _ v).
Defined.

Definition iter_and (l: list Prop) : Prop :=
  fold_right and True l.

Fixpoint dep_map {A B: Type} {P: A -> Prop} (f: forall x, P x -> B)
  (l: list A) (Hall: Forall P l) : list B :=
  match l as l' return Forall P l' -> list B with
  | nil => fun _ => nil
  | x :: tl => fun Hforall => f x (Forall_inv Hforall) ::
    dep_map f tl (Forall_inv_tail Hforall)
  end Hall.

  (*The encoding we want*)
Definition indpred_rep (v: valuation gamma_valid i) (p: predsym)
  (fs: list formula) (Hform: Forall (valid_formula sigma) fs) (srts: list sort) 
  (a: arg_list (domain (dom_aux gamma_valid i)) 
  (predsym_sigma_args p srts)) : Prop :=
  (forall (P: forall (srts: list sort), 
    arg_list (domain (dom_aux gamma_valid i)) 
    (predsym_sigma_args p srts) -> bool),
    iter_and (map is_true (dep_map (@formula_rep _ _ gamma_valid 
      (interp_with_P i p P) all_unif (interp_P_val i p P v)) 
      fs Hform)) -> P srts a).
  
(*Get a valuation where the v_typevar maps the typevars in a list
  to a list of sorts*)
  (*TODO: assume all valid for now, need to add to funs/preds*)
(*
Definition val_of_srts (v: valuation gamma_valid i) (vars: list typevar)
  (srts: list sort) (Hall: Forall (fun x => valid_type sigma x) (sorts_to_tys srts)) : 
  valuation gamma_valid i.
Proof.
  apply (Build_valuation gamma_valid i (fun (var: typevar) =>
    ty_subst_fun_s vars srts (v_typevar gamma_valid i v var) var (*default to old value*))).
  - intros x. unfold ty_subst_fun_s; simpl.
    admit.
  - (*ugh, need to adjust vars too*)
  (*need to think about this more - is this what we want?*)
*)

(*Ex: Fquant Tforall n nat (Fbinop Timplies (Fpred p nil (Tvar n)))
                                            (Fpred p nil (Tfun S S n))
    should give (forall n, P n -> P (S S n)) - need notion of prop with hole
    kind of? Or arg list?
    should basicallybe formula rep right? but with special case for P
    maybe take in or adjust valuation*)

Set Bullet Behavior "Strict Subproofs".
  (*Get the rep for a single formula*)
  (*Ah, should not be any sort - should be according to valuation,
    can have many arg lists but sorts are fixed*)
    (*But preds work on arbitrary sorts - ned to see*)
(*Idea: we know that sort list is map (val v) vs for some vs*)
Definition indpred_rep_f (v: valuation gamma_valid i) (p: predsym)
(f: formula) (Hf: valid_formula sigma f) (Hform: valid_ind_form p f) 
 (P: forall srts, arg_list (domain (dom_aux gamma_valid i)) 
(predsym_sigma_args p srts) 
-> Prop) : Prop.
Proof.
  revert Hf Hform P.
(*TODO: write as function first, not dep type*)
induction f using formula_rect with (P1:=fun _ => True) (P2:=fun f => valid_formula sigma f ->
  valid_ind_form p f -> (forall srts, arg_list (domain (dom_aux gamma_valid i)) 
  (predsym_sigma_args p srts) 
  -> Prop) -> Prop ); try solve[exfalso; inversion Hform]; auto; intros
  Hf Hform P; try solve[exfalso; inversion Hform].
- apply valid_ind_pred in Hform. destruct Hform as [Hl [Hlo Hp]].
  eapply P. unfold predsym_sigma_args.
  apply (@get_arg_list_pred sigma gamma gamma_valid i) with(ts:=tms).
  intros t ty Hty. exact (term_rep gamma_valid i all_unif v t ty Hty).
  rewrite Hp.
  apply Hf.
- (*Need forall here - think about this*) 

(*TODO - remove inversion*)
  apply IHf. inversion Hf; auto. inversion Hform; auto.
  apply P.
- apply IHf2. inversion Hf; auto. inversion Hform; auto.
  apply P.
- apply IHf0. apply 


Print valid_ind_form.


Print valid_ind_form. 
  (*ugh, at same point: Need to know vs = l0 by some sort of uniformity
    argument*)
  (*hmm i really need to see - maybe [get_arg_list_pred] is too strong?*)
  Check get_arg_list_pred.
    Print valid_formula.
  exact Hf.
  unfold predsym_sigma_args in H.
  Print valuation.
  Search v_subst v_typevar.
  Check get_arg_list_pred.
  (*We need [get_arg_list_pred] with the valuation mapping each
    variable to the corresponding sort in srts*)
  *)
(*Problem: we need to know that inner ones applied to sorts also
  other*)
(*Let's give the condition as: apply predsym to sort - ugh how to do this?
cant wait until end because we need actual Sets for sorts, but
no info at beginning

so instaed let's say: give Prop for (Fpred p srts ts)
but cant do that because we are giving val for ts
ugh - can we take in additional assumptions about srts and (p_args p)?

*)
Definition indpred_rep (v: valuation gamma_valid i) (p: predsym)
  (fs: list formula) (Hform: Forall (fun f => valid_formula sigma f /\
    valid_ind_form p f) fs) (srts: list sort) 
  (a: arg_list (domain (dom_aux gamma_valid i)) 
  (predsym_sigma_args p srts)) : Prop.
  refine (forall (P: 
    arg_list (domain (dom_aux gamma_valid i)) 
      (predsym_sigma_args p srts) -> Prop), _ ).



Print valid_ind_form.



1
15

(*Let's try to generalize*)

