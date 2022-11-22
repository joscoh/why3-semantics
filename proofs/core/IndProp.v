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
Require Import Hlist.

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
(*
Check preds.*)
(*For the list of predsyms, we need to search through the list
  to apply the correct pred. The dependent types make this
  complicated, so we use a separate function*)
Fixpoint find_apply_pred (pi: pre_interp gamma_valid)
(ps: list predsym)
(*Our props are an hlist, where we have a Pi for each pi
of type (srts -> arg_list pi srts -> bool)*)
(Ps: hlist (fun p => forall srts, 
  arg_list (domain (dom_aux _ pi)) 
  (predsym_sigma_args p srts) -> bool) ps) (p: predsym) :
  (forall srts : list sort,
    arg_list (domain (dom_aux gamma_valid pi)) 
      (predsym_sigma_args p srts) -> bool) :=
  (match ps as ps' return
  (hlist (fun p : predsym =>
    forall srts : list sort,
    arg_list (domain (dom_aux gamma_valid pi))
      (predsym_sigma_args p srts) -> bool) ps') ->
    forall srts : list sort,
      arg_list (domain (dom_aux gamma_valid pi)) 
        (predsym_sigma_args p srts) -> bool with
  (*Underneath the depednent types, this is quite
    simple: iterate through the list, compare for equality
    and if so, apply the correct Pi function*)
  | nil => fun _ => (preds gamma_valid pi p)
  | p' :: ptl =>  fun Hp =>
    match (predsym_eq_dec p p') with
    | left Heq => ltac:(rewrite Heq; exact (hlist_hd Hp))
    | right _ => (find_apply_pred pi ptl (hlist_tl Hp) p)
    end
  end) Ps.

(*Do the same for a list of predsyms*)
Definition interp_with_Ps (pi: pre_interp gamma_valid)
  (ps: list predsym)
  (*Our props are an hlist, where we have a Pi for each pi
  of type (srts -> arg_list pi srts -> bool)*)
  (Ps: hlist (fun p => forall srts, 
    arg_list (domain (dom_aux _ pi)) 
    (predsym_sigma_args p srts) -> bool) ps) :
  pre_interp gamma_valid :=
  {|
  dom_aux := dom_aux gamma_valid pi;
  domain_ne := domain_ne gamma_valid pi;
  funs := funs gamma_valid pi;
  preds := find_apply_pred pi ps Ps;
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

Definition interp_Ps_val pi p Pi (v: valuation gamma_valid pi):
  valuation gamma_valid (interp_with_Ps pi p Pi).
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

(*TODO: move*)
(*Given an element in a list and an hlist, get the corresponding element
  of the hlist*)
Print hlist.
Definition get_hlist_elt {A: Type} {f: A -> Type} {l: list A}
  (h: hlist f l) (x: A)
  (Hinx: In x l) : f x.
Admitted.

(*Since inductive predicates can be mutually recursive, we need
  a list of predsyms and formula lists. This makes the dependent
  types tricky, since we need a (P: forall srts, arg_list srts -> bool)
  for each such predsym*)

Definition indpred_rep (v: valuation gamma_valid i) 
  (indpred : list (predsym * list formula))
  (Hform: Forall (Forall (valid_formula sigma)) (map snd indpred)) 
  (p: predsym)
  (Hin: In p (map fst indpred))
  (srts: list sort)
  (a: arg_list (domain (dom_aux gamma_valid i)) 
  (predsym_sigma_args p srts)) : Prop :=
  (*Our props are an hlist, where we have a Pi for each pi
  of type (srts -> arg_list pi srts -> bool)*)
  (forall (Ps: hlist (fun (p': predsym) => 
    (forall (srts: list sort), 
    arg_list (domain (dom_aux gamma_valid i)) 
    (predsym_sigma_args p' srts) -> bool)) (map fst indpred)),
    (*The precondition is the conjunction of all of the
      inductive hypotheses from the list of formulas, with
      each recursive instance using the appropriate Pi*)
    ((fix build_indpred (l: list (list formula)) 
      (Hl: Forall (Forall (valid_formula sigma)) l) : Prop :=
      match l as l' return 
        Forall (Forall (valid_formula sigma)) l' -> Prop 
      with
      | nil => fun _ => True
      | fs :: ftl => fun Hall =>
        iter_and (map is_true (dep_map (@formula_rep _ _ gamma_valid
          (interp_with_Ps i _ Ps) all_unif
          (interp_Ps_val i _ Ps v))
           fs (Forall_inv Hall))) /\
          build_indpred ftl (Forall_inv_tail Hall)
      end Hl) _ Hform)
       -> 
      
      (get_hlist_elt Ps p Hin) srts a).

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

(*Now prove least fixpoint: For any other P 
  such that all constructor formulas hold when p is
  interpreted as P and for all x, indpred_rep x -> P x*)
Lemma indpred_least_fp (v: valuation gamma_valid i) (p: predsym)
(fs: list formula) (Hform: Forall (valid_formula sigma) fs) 
(P: forall (srts: list sort),
  arg_list (domain (dom_aux gamma_valid i)) 
  (predsym_sigma_args p srts) -> bool):
  iter_and (map is_true (dep_map (@formula_rep _ _
    gamma_valid (interp_with_P i p P) 
    all_unif (interp_P_val i p P v)) fs Hform)) ->
  forall (srts: list sort) 
  (a: arg_list (domain (dom_aux gamma_valid i)) 
  (predsym_sigma_args p srts)),
  indpred_rep v p fs Hform srts a -> P srts a.
Proof.
  intros Hand srts a. unfold indpred_rep; intros. apply H. apply Hand.
Qed.

(*Need to deal with mutually recursive inductive predicates*)

(*Test: even and odd*)
Unset Elimination Schemes.
Inductive ev : nat -> Prop :=
  | ev0': ev 0
  | ev_odd: forall n, odd n -> ev (S n)
with odd: nat -> Prop :=
  | odd_ev: forall n, ev n -> odd (S n).
Set Elimination Schemes.

Scheme ev_ind := Minimality for ev Sort Prop
with odd_ind := Minimality for odd Sort Prop.

Check ev_ind.

Set Bullet Behavior "Strict Subproofs".

(*Prove equivalent first (just to see)*)
Lemma ev_eq: forall n, 
  (ev n <-> even n) /\
  (odd n <-> ~ (even n)).
Proof.
  intros n. induction n using lt_wf_ind; simpl; split; intros; split; intros.
  - destruct n; try constructor.
    destruct n; inversion H0; subst; inversion H2; subst.
    constructor. apply H; auto.
  - destruct n; constructor. destruct n; inversion H0; subst.
    constructor. apply H; auto.
  - destruct n; inversion H0; subst.
    destruct n; inversion H2; subst;
    intro C; inversion C; subst.
    assert (~ even n). apply H; auto. auto.
  - destruct n. exfalso. apply H0; constructor.
    constructor. destruct n; constructor.
    apply H; auto. intro C.
    apply H0. constructor; auto.
Qed.

(*Now give the predicate*)
Definition test_ev: nat -> Prop :=
  fun m => forall (P1 P2: nat -> Prop),
    P1 0 ->
    (forall n, P2 n -> P1 (S n)) ->
    (forall n, P1 n -> P2 (S n)) ->
    P1 m.

Definition test_odd: nat -> Prop :=
  fun m => forall (P1 P2: nat -> Prop),
    P1 0 ->
    (forall n, P2 n -> P1 (S n)) ->
    (forall n, P1 n -> P2 (S n)) ->
    P2 m.

Lemma test_ev_correct: forall n,
  ev n <-> test_ev n.
Proof.
  intros n. unfold test_ev; split; intros.
  - apply (ev_ind) with(P:=P1) (P0:=P2); auto.
  - specialize (H ev odd). apply H; constructor; auto.
Qed.

Lemma test_odd_correct: forall n,
  odd n <-> test_odd n.
Proof.
  intros n. unfold test_odd; split; intros.
  - apply odd_ind with(P:=P1)(P0:=P2); auto.
  - specialize (H ev odd). apply H; constructor; auto.
Qed.

induction H. (P0:=P2).
  
  
  unfold test_ev


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



(*Let's see*)
Definition test1 : nat -> Prop :=
  fun m => forall (P: nat -> Prop),
    P 0 ->
    (forall n, P n -> P(S (S n))) ->
    P m.
 

(*Test case: semantics for simple terms and formulas*)

Inductive tm : Set :=
  | tm_nat : nat -> tm
  | tm_plus: tm -> tm -> tm
  | tm_if: fmla -> tm -> tm -> tm
with fmla : Set :=
  | fm_tru : fmla
  | fm_flse: fmla
  | fm_not: fmla -> fmla
  | fm_and: fmla -> fmla -> fmla
  | fm_eq: tm -> tm -> fmla.

Inductive tm_sem : tm -> nat -> Prop :=
  | 

  
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

