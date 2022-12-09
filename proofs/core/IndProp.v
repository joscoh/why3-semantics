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

Lemma constr_test1: test1 0.
Proof.
  unfold test1. intros. apply H.
Qed.

Lemma constr_test2: forall n, test1 n -> test1 (S (S n)).
Proof.
  intros n Hn. unfold test1. intros P Hp0 Hpss.
  apply Hpss.
  apply least_fp; assumption.
Qed.

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



(*What if we had something non strictly positive?*)
Fail Inductive bad : nat -> Prop :=
  | Bad1: forall n, (bad n -> False) -> bad (S n).

Definition bad1 : nat -> Prop :=
    fun m => forall (P: nat -> Prop),
      (forall n, (P n -> False) -> P (S n)) -> P m.
(*So this is definable - problem is that it isn't really usable?*)
(*So i think the idea is: if non strictly positive, this Prop may
not be inhabited - but yeah, where do we need this info?*)

(*Test*)
Lemma bad1_bad: forall n, (bad1 n -> False) -> bad1 (S n).
Proof.
  intros n Hfalse. unfold bad1. intros P Hfalse'.
  apply Hfalse'.
  (*Here is where it should fail: it is NOT the case that (~bad1 n) -> ~(P n)*)
  intros Hp. apply Hfalse. unfold bad1. intros P' Hp'.
  (*???*)
  Abort.

Definition odd n := ~(even n).
Fixpoint evenb (n: nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n) => evenb n
  end.
(*We assume this*)
Require Import Coq.Arith.Wf_nat.
Lemma evenb_spec: forall n, even n <-> evenb n = true.
Proof.
  intros n.
  apply  lt_wf_ind with(P:= (fun n => even n <-> evenb n = true)).
  intros n' IH.
  destruct n'; simpl; auto; split; intros; auto.
  constructor.
  destruct n'. inversion H. inversion H; subst.
  apply IH; auto. destruct n'. inversion H.
  constructor. apply IH; auto.
Qed.

(*2 properties about evenness and oddness*)
Lemma even_alt: forall n, ~(even n) -> even (S n).
Proof.
induction n.
- intro C. assert (even 0) by constructor. contradiction.
- intro C. constructor.
  destruct (evenb n) eqn : He.
  + apply evenb_spec; auto.
  + assert (~ even n). {
    intro C'. apply evenb_spec in C'. rewrite C' in He; inversion He.
  }
  specialize (IHn H). contradiction.
Qed.

Lemma even_alt': forall n, (even n) -> ~(even (S n)).
Proof.
  induction n; intros; intro C; inversion C; subst.
  apply IHn in H1. contradiction.
Qed.

Lemma odd_alt: forall n, ~(odd n) -> odd (S n).
Proof.
  intros n. unfold odd. intros He.
  apply even_alt'.
  destruct (evenb n) eqn : Heb.
  - apply evenb_spec; auto.
  - assert (~ (even n)). intro C. apply evenb_spec in C.
    rewrite C in Heb; inversion Heb. contradiction.
Qed.

(*This shows why we need strict positivity : if we don't have it,
  the constructors may not be true/inhabited*)
Lemma bad1_bad: ~(forall n, (bad1 n -> False) -> bad1 (S n)).
Proof.
  intros Hc. unfold bad1 in Hc.
  assert (even 1). {
    apply Hc.
    - intros. specialize (H odd).
      assert (odd 0). { 
        apply H.
        apply odd_alt.
      }
      unfold odd in H0.
      apply H0. constructor.
    - apply even_alt.
  }
  inversion H.
Qed.


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

Context {sigma: sig} {gamma: context} 
  (gamma_valid: valid_context sigma gamma)
  (pd: pi_dom).
  (*(i: pre_interp gamma_valid).*)

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

(*Alternate approach*)

Definition interp_with_P (pi: pi_funpred gamma_valid pd) (p: predsym) 
  (P: forall srts, 
    arg_list (domain (dom_aux pd)) (predsym_sigma_args p srts) -> bool) :
  pi_funpred gamma_valid pd :=
  {|
  funs := funs gamma_valid pd pi;
  preds :=
    fun pr : predsym =>
    match predsym_eq_dec p pr with
    | left Heq =>
        match Heq with
        | eq_refl => P
        end
    | _ => preds gamma_valid pd pi pr
    end;
  constrs := constrs gamma_valid pd pi
|}.
(*
Check preds.*)
(*For the list of predsyms, we need to search through the list
  to apply the correct pred. The dependent types make this
  complicated, so we use a separate function*)
Fixpoint find_apply_pred (pi: pi_funpred gamma_valid pd)
(ps: list predsym)
(*Our props are an hlist, where we have a Pi for each pi
of type (srts -> arg_list pi srts -> bool)*)
(Ps: hlist (fun p => forall srts, 
  arg_list (domain (dom_aux pd)) 
  (predsym_sigma_args p srts) -> bool) ps) (p: predsym) :
  (forall srts : list sort,
    arg_list (domain (dom_aux pd)) 
      (predsym_sigma_args p srts) -> bool) :=
  (match ps as ps' return
  (hlist (fun p : predsym =>
    forall srts : list sort,
    arg_list (domain (dom_aux pd))
      (predsym_sigma_args p srts) -> bool) ps') ->
    forall srts : list sort,
      arg_list (domain (dom_aux pd)) 
        (predsym_sigma_args p srts) -> bool with
  (*Underneath the depednent types, this is quite
    simple: iterate through the list, compare for equality
    and if so, apply the correct Pi function*)
  | nil => fun _ => (preds gamma_valid pd pi p)
  | p' :: ptl =>  fun Hp =>
    match (predsym_eq_dec p p') with
    | left Heq => ltac:(rewrite Heq; exact (hlist_hd Hp))
    | right _ => (find_apply_pred pi ptl (hlist_tl Hp) p)
    end
  end) Ps.

(*Do the same for a list of predsyms*)
Definition interp_with_Ps (pi: pi_funpred gamma_valid pd)
  (ps: list predsym)
  (*Our props are an hlist, where we have a Pi for each pi
  of type (srts -> arg_list pi srts -> bool)*)
  (Ps: hlist (fun p => forall srts, 
    arg_list (domain (dom_aux pd)) 
    (predsym_sigma_args p srts) -> bool) ps) :
  pi_funpred gamma_valid pd :=
  {|
  funs := funs gamma_valid pd pi;
  preds := find_apply_pred pi ps Ps;
  constrs := constrs gamma_valid pd pi
|}.

Require Import FunctionalExtensionality.
Require Import Coq.Logic.Eqdep_dec.
Set Bullet Behavior "Strict Subproofs".

Lemma interp_with_Ps_single (pi: pi_funpred gamma_valid pd)
  (p: predsym)
  (Ps: hlist (fun p => forall srts, 
    arg_list (domain (dom_aux pd)) 
    (predsym_sigma_args p srts) -> bool) [p]) :
  interp_with_Ps pi [p] Ps =
  interp_with_P pi p (hlist_hd Ps).
Proof.
  unfold interp_with_Ps. simpl.
  unfold interp_with_P. f_equal.
  apply functional_extensionality_dep. intros p'.
  destruct (predsym_eq_dec p' p).
  - subst. destruct (predsym_eq_dec p p); simpl; [|contradiction].
    assert (e = eq_refl) by (apply UIP_dec; apply predsym_eq_dec).
    rewrite H. reflexivity.
  - destruct (predsym_eq_dec p p'); subst; auto.
    contradiction.
Qed.


(*Any valuation is equivalent under each interpretation*)
(*
Definition interp_P_val pi p P (v: val_ gamma_valid pi):
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
Defined.*)

Definition iter_and (l: list Prop) : Prop :=
  fold_right and True l.

Fixpoint dep_map {A B: Type} {P: A -> Prop} (f: forall x, P x -> B)
  (l: list A) (Hall: Forall P l) : list B :=
  match l as l' return Forall P l' -> list B with
  | nil => fun _ => nil
  | x :: tl => fun Hforall => f x (Forall_inv Hforall) ::
    dep_map f tl (Forall_inv_tail Hforall)
  end Hall.

Lemma dep_map_in {A B: Type} {P: A -> Prop} (f: forall x, P x -> B)
  (l: list A) (Hall: Forall P l) (x: B):
  In x (dep_map f l Hall) ->
  exists y H, In y l /\ f y H = x.
Proof.
  revert Hall. induction l; simpl; intros. destruct H.
  inversion Hall; subst.
  destruct H.
  - subst. exists a. exists (Forall_inv Hall). split; auto.
  - specialize (IHl _ H). destruct IHl as [y [Hy [Hiny Hxy]]].
    exists y. exists Hy. split; auto.
Qed.

Lemma in_dep_map {A B: Type} {P: A -> Prop} (f: forall x, P x -> B)
  (l: list A) (Hall: Forall P l) (x: A):
  In x l ->
  exists H,
    In (f x H) (dep_map f l Hall).
Proof.
  revert Hall. induction l; simpl; intros. destruct H.
  inversion Hall; subst. destruct H; subst.
  - exists (Forall_inv Hall). left. reflexivity.
  - specialize (IHl (Forall_inv_tail Hall) H).
    destruct IHl as [Hx Hinx]. exists Hx. right. assumption.
Qed.

Lemma dep_map_irrel {A B: Type} {P: A -> Prop} (f: forall x, P x -> B)
  (l: list A) (Hall1 Hall2: Forall P l):
  (forall x H1 H2, f x H1 = f x H2) ->
  dep_map f l Hall1 = dep_map f l Hall2.
Proof.
  intros Hirrel.
  revert Hall1 Hall2.
  induction l; intros; simpl; auto.
  erewrite IHl. f_equal. apply Hirrel.
Qed. 

(*TODO: move*)
(*Given an element in a list and an hlist, get the corresponding element
  of the hlist*)

Fixpoint get_hlist_elt {A: Type} (eq_dec: forall x y, {x = y} + {x <> y}) 
  {f: A -> Type} {l: list A}
  (h: hlist f l) (x: A)
  (Hinx: in_bool eq_dec x l) : f x :=
  (match l as l' return in_bool eq_dec x l' -> hlist f l' -> f x with
  | nil => fun Hin _ => False_rect _ (not_false Hin)
  | y :: tl => fun Hin h' =>
    (match (eq_dec x y) as b return b || in_bool eq_dec x tl ->
      f x with
    | left Heq => fun _ => ltac:(rewrite Heq; exact (hlist_hd h'))
    | right Hneq => fun Hin' => 
      get_hlist_elt eq_dec (hlist_tl h') x Hin'
    end) Hin
  end) Hinx h.

(*Since inductive predicates can be mutually recursive, we need
  a list of predsyms and formula lists. This makes the dependent
  types tricky, since we need a (P: forall srts, arg_list srts -> bool)
  for each such predsym*)
Check @formula_rep.
Definition indpred_rep (pf: pi_funpred gamma_valid pd) 
  (vt: val_typevar) (vv: val_vars pd vt)
  (indpred : list (predsym * list formula))
  (Hform: Forall (Forall (valid_formula sigma)) (map snd indpred)) 
  (p: predsym)
  (Hin: in_bool predsym_eq_dec p (map fst indpred))
  (*(Hin: In p (map fst indpred))*)
  (srts: list sort)
  (a: arg_list (domain (dom_aux pd)) 
  (predsym_sigma_args p srts)) : Prop :=
  (*Our props are an hlist, where we have a Pi for each pi
  of type (srts -> arg_list pi srts -> bool)*)
  (forall (Ps: hlist (fun (p': predsym) => 
    (forall (srts: list sort), 
    arg_list (domain (dom_aux pd)) 
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
        iter_and (map is_true (dep_map (@formula_rep _ _ gamma_valid pd all_unif
          vt (interp_with_Ps pf _ Ps) vv)
           fs (Forall_inv Hall))) /\
          build_indpred ftl (Forall_inv_tail Hall)
      end Hl) _ Hform)
       -> 
      (*All of this together implies Pi srts a, for the
        i corresponding to p*)
      (get_hlist_elt predsym_eq_dec Ps p Hin)
        (*(In_in_bool predsym_eq_dec _ _ Hin))*) srts a).

  (*The encoding we want*)
(*The version for non-mutual-recursion is a lot simpler*)
Definition indpred_rep_single (pf: pi_funpred gamma_valid pd) 
(vt: val_typevar) (vv: val_vars pd vt) (p: predsym)
  (fs: list formula) (Hform: Forall (valid_formula sigma) fs) (srts: list sort) 
  (a: arg_list (domain (dom_aux pd)) 
  (predsym_sigma_args p srts)) : bool :=
  (*TODO: change preds to Prop instead of bool?*)
  all_dec
  (forall (P: forall (srts: list sort), 
    arg_list (domain (dom_aux pd)) 
    (predsym_sigma_args p srts) -> bool),
    iter_and (map is_true (dep_map (@formula_rep _ _ gamma_valid 
      pd  all_unif vt (interp_with_P pf p P) vv) 
      fs Hform)) -> P srts a).

Definition Forall_single {A: Type} {P: A -> Prop} {x: list A}
  (Hform: Forall P x) :
  Forall (Forall P) [x] :=
  Forall_cons _  Hform (@Forall_nil (list A) (Forall P)).

Lemma temp {A} p (fs: list A): is_true (in_bool predsym_eq_dec p (map fst [(p, fs)])).
Proof.
  simpl. destruct (predsym_eq_dec); auto.
Defined.

Definition dom_cast' {aux1 aux2: sort -> Set} {v: sort} (Heq: aux1 = aux2) 
  (d: domain aux1 v) : domain aux2 v :=
  match Heq with
  | eq_refl => d
  end.
(*
Definition dom_aux_eq (i1 i2: pre_interp gamma_valid)
  (Hieq: i1 = i2) : (dom_aux gamma_valid i1 = dom_aux gamma_valid i2).
destruct Hieq. exact eq_refl.
Defined.

Lemma val_from_eq (i1 i2: pre_interp gamma_valid) (Hieq: i1 = i2)
  (v1: valuation gamma_valid i1) :
  valuation gamma_valid i2.
Proof.
  apply (Build_valuation)with(v_typevar:=(v_typevar gamma_valid i1 v1)).
  - exact (v_typevar_val gamma_valid i1 v1).
  - intros vs v.
    apply (dom_cast' (dom_aux_eq i1 i2 Hieq) (v_vars gamma_valid i1 v1 vs v)).
Defined. 

Lemma interp_P_Ps_val (p: predsym)
  (Ps: hlist
  (fun p' : predsym =>
   forall srts : list sort,
   arg_list (domain (dom_aux gamma_valid i)) (predsym_sigma_args p' srts) -> bool)
  [p]) (v: valuation gamma_valid i) :
  (v_typevar gamma_valid _ (interp_Ps_val i [p] Ps v)) =
  (v_typevar gamma_valid _ (interp_P_val i p (hlist_hd Ps) v)) /\
  (v_typevar_val gamma_valid _ (interp_Ps_val i [p] Ps v)) =
  (v_typevar_val gamma_valid _ (interp_P_val i p (hlist_hd Ps) v)) /\
  (v_vars gamma_valid _ (interp_Ps_val i [p] Ps v)) =
  (v_vars gamma_valid _ (interp_P_val i p (hlist_hd Ps) v)).
Proof.
  simpl. auto.
Qed. 

Axiom UIP: forall {A: Type} {x: A} (H1: x = x), H1 = eq_refl.

Definition uip_diff {A B: Type} (x y : A) (H: x = y) (z: B) :
  match H with
  | eq_refl => z
  end = z.
Proof.
  destruct H. reflexivity.
Qed.
(*
Definition uip {A B: Type} (x y : A) (H: x = y) (z1: B): 
              match H return (@eq B z1 z1) with
              | eq_refl => (@eq_refl B z1)
              end = (@eq_refl B z1).
Proof.
  destruct H. reflexivity.
Qed.
*)*)

(*TODO: this is very, very hard to prove.
  Dependent types are a nightmare*)
Lemma indpred_rep_single_equiv (pf: pi_funpred gamma_valid pd) 
(vt: val_typevar) (vv: val_vars pd vt) (p: predsym)
(fs: list formula) (Hform: Forall (valid_formula sigma) fs) (srts: list sort) 
(a: arg_list (domain (dom_aux pd)) 
(predsym_sigma_args p srts)) :
  indpred_rep_single pf vt vv p fs Hform srts a <->
  indpred_rep pf vt vv [(p, fs)] (Forall_single Hform) p (temp p fs) srts a.
Proof.
  unfold indpred_rep_single.
  unfold indpred_rep. simpl.
  split; intros.
  - generalize dependent (temp p fs). simpl.
    destruct (predsym_eq_dec p p); simpl; auto.
    intros _. unfold eq_rect_r, eq_rect.
    assert (e = eq_refl) by (apply UIP_dec; apply predsym_eq_dec).
    rewrite H1. simpl.
    revert H.
    match goal with |- context [all_dec ?P] => destruct (all_dec P); auto end.
    intros _. apply i.
    destruct H0 as [Hand _].
    revert Hand.
    rewrite (interp_with_Ps_single pf p Ps); intros Hand.
    erewrite dep_map_irrel. apply Hand. intros.
    apply fmla_rep_irrel.
  - match goal with |- context [all_dec ?P] => destruct (all_dec P); auto end.
    exfalso; apply n; clear n.
    revert H. generalize dependent (temp p fs); simpl.
    destruct (predsym_eq_dec p p); simpl; auto.
    intros _ Hmult.
    intros P.
    specialize (Hmult (HL_cons (fun p' : predsym =>
    forall srts : list sort,
    arg_list (domain (dom_aux pd)) (predsym_sigma_args p' srts) -> bool)
    p nil P (@HL_nil _ _))).
    intros Hand.
    revert Hmult. simpl. unfold eq_rect_r, eq_rect.
    assert (e = eq_refl). apply UIP_dec. apply predsym_eq_dec.
    rewrite H. simpl. intros Hmult.
    apply Hmult; clear Hmult. split; auto.
    rewrite (interp_with_Ps_single pf p _). simpl.
    erewrite dep_map_irrel. apply Hand.
    intros. apply fmla_rep_irrel.
Qed.
  
(*Prove that this is the least fixpoint*)
(*TODO: what is the actual definition*)
(*We must show the following: 
  1. When our intepretations inteprets the predicate(s) P 
    as [indpred_rep], then 
    all of the constructor reps should imply P(x)
  2: TODO
    *)

(*TODO: move to denotational*)
Lemma fpred_rep (pd': pi_dom) (pf: pi_funpred gamma_valid pd') 
  (vt: val_typevar) (vv: val_vars pd' vt)
(p: predsym) (vs: list vty) (args: list term)
  (Hval: valid_formula sigma (Fpred p vs args)) :
  formula_rep gamma_valid pd' all_unif vt pf vv (Fpred p vs args) Hval =
  preds gamma_valid pd' pf p (map (v_subst (v_typevar vt)) vs)
    (get_arg_list_pred pd' vt p vs args 
    (term_rep gamma_valid pd' all_unif vt pf vv)
    (valid_formula_eq eq_refl Hval)).
Proof.
  reflexivity.
Qed.

(*Quick test*)


(*Will prove:
  1. For p = f1 | .. fn,
    all fn's are true
  2. Suppose that f1 /\ f2 /\ ... fn -> q.
    Then p -> q*)

Lemma prove_iter_and (ps: list Prop):
  (forall x, In x ps -> x) <-> iter_and ps.
Proof.
  induction ps; simpl; split; intros; auto.
  - destruct H0.
  - split. apply H. left. reflexivity.
    rewrite <- IHps. intros x Hinx. apply H. right. assumption.
  - destruct H. destruct H0; subst; auto.
    apply IHps; auto.
Qed. 

Lemma simpl_all_dec (P: Prop):
   (all_dec P) <-> P.
Proof.
  split; intros;
  destruct (all_dec P); auto.
  inversion H.
Qed.

Scheme Minimality for valid_ind_form Sort Prop.

(*First, we do the proofs for the non-mutually recursive case,
  since they are simpler and don't involve hlists*)
Section Single.

(*Prove second part first - this is easy*)
Theorem indpred_least_pred_single (pf: pi_funpred gamma_valid pd) 
  (vt: val_typevar) (vv: val_vars pd vt)
  (p: predsym) (fs: list formula) (Hform: Forall (valid_formula sigma) fs):
  forall (P:
    forall srts : list sort,
    arg_list (domain (dom_aux pd)) 
      (predsym_sigma_args p srts) ->
    bool
  ),  
  (*If P holds of all of the constructors*)
  iter_and
  (map is_true
     (dep_map
        (formula_rep gamma_valid pd 
          all_unif vt (interp_with_P pf p P)  vv) fs Hform)) ->
(*Then indpred_rep p fs x -> P x*)  
  forall (srts : list sort)
  (a: arg_list (domain (dom_aux pd)) 
    (predsym_sigma_args p srts)),
    indpred_rep_single pf vt vv p fs Hform srts a -> P srts a.
Proof.
  intros P Hand srts a. unfold indpred_rep_single.
  rewrite simpl_all_dec. intros.
  apply H. apply Hand.
Qed.

(*TODO: prove this later, will require strict positivity*)
(*A key corollary: if any formula is true under the interpretation
  where p is sent to [indpred_rep_single], then it is true
  under any interpretation where p is sent to P, for any P
  which satisfies all of the constructors*)
  (*
Lemma indpred_single_implies (pf: pi_funpred gamma_valid pd) 
(vt: val_typevar) (vv: val_vars pd vt)
(p: predsym) (fs: list formula) (Hform: Forall (valid_formula sigma) fs):
  forall (P:
    forall srts : list sort,
    arg_list (domain (dom_aux pd)) 
      (predsym_sigma_args p srts) ->
    bool
  ),  
  (*If P holds of all of the constructors*)
  iter_and
  (map is_true
    (dep_map
        (formula_rep gamma_valid pd (interp_with_P pf p P) 
          all_unif vt vv) fs Hform)) ->
  forall (f: formula) (Hvalf: valid_formula sigma f), 
    formula_rep gamma_valid pd (interp_with_P pf p 
      (indpred_rep_single pf vt vv p fs Hform)) all_unif vt vv f Hvalf ->
    formula_rep gamma_valid pd (interp_with_P pf p P) all_unif vt vv f Hvalf.
Proof.
  intros P Hallp.
  apply formula_ind with (P1:= fun t => 
    forall (ty: vty) (Hty1: term_has_type sigma t ty),
    (*TODO: not true - what about if? what about "if"?*)
    term_rep gamma_valid pd (interp_with_P pf p (indpred_rep_single pf vt vv p fs Hform))
      all_unif vt vv t ty Hty1 =
    term_rep gamma_valid pd (interp_with_P pf p P) all_unif vt vv t ty Hty1); auto; simpl; intros.
  - admit.
  - admit.
  -  simpl.
    *)

(*On the other hand, the first part is hard (showing that [indpred_rep]
  holds of all constructors). Here is an approach to show it:
  1. Prove that any constructor is equivalent to one where we
    have a bunch of forall quantifiers, followed by a bunch
    of let statements, followed by a chain of impliciations
    ending in indpred_rep p fs x for some x
  2. From this, unfold the definition of indpred_rep
    and TODO
    
  The first step is not easy. We need to define alpha
  substitution and some quantifier elimination/prenex normal form*)

(*First, we define this transformation*)
Print formula.

Definition tup_1 {A B C D: Type} (x: A * B * C * D) :=
  match x with
  | (a, _, _, _) => a
  end.
Definition tup_2 {A B C D: Type} (x: A * B * C * D) :=
  match x with
  | (_, b, _, _) => b
  end.
Definition tup_3 {A B C D: Type} (x: A * B * C * D) :=
  match x with
  | (_, _, c, _) => c
  end.
Definition tup_4 {A B C D: Type} (x: A * B * C * D) :=
  match x with
  | (_, _, _, d) => d
  end.


Fixpoint indpred_decomp (f: formula) : 
  (list vsymbol * list (vsymbol * term) * list formula * formula) :=
  match f with
  | Fquant Tforall x f1 =>
    let t := indpred_decomp f1 in
    (x :: tup_1 t, tup_2 t, tup_3 t, tup_4 t)
  | Fbinop Timplies f1 f2 =>
    let t := indpred_decomp f2 in
    (tup_1 t, tup_2 t, f1 :: tup_3 t, tup_4 t)
  | Flet t1 v f1 =>
    let t := indpred_decomp f1 in
    (tup_1 t, (v, t1) :: tup_2 t, tup_3 t, tup_4 t)
  | _ => (nil, nil, nil, f)
  end.

(*Now we prove that for [valid_ind_form] formulas with
  well-formed bound variables, [indpred_decomp] produces
  an equivalent formula when interpreted.*)

  Ltac split_all :=
  repeat match goal with
  | H: ?P /\ ?Q |- _ => destruct H
  | |- ?P /\ ?Q => split
  end.

(*Iterated forall - TODO: maybe move to Denotational*)
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
  domain (dom_aux pd) (v_subst (v_typevar vt) x)) (map snd vs)) :
  val_vars pd vt :=
  (match vs as l return hlist  
    (fun x => domain (dom_aux pd) (v_subst (v_typevar vt) x)) 
    (map snd l) -> val_vars pd vt with
  | nil => fun _ => vv
  | x :: tl => fun h' => 
     (substi_mult vt (substi pd vt vv x (hlist_hd h')) tl (hlist_tl h')) 
  end) vals.
  
(*And we show that we can use this multi-substitution
  to interpret [fforalls_val]*)
Lemma fforalls_val (pf: pi_funpred gamma_valid pd)
  (vt: val_typevar) (vv: val_vars pd vt) 
  (vs: list vsymbol) (f: formula) 
  (Hval: valid_formula sigma f)
  (Hall: Forall (fun x => valid_type sigma (snd x)) vs):
  formula_rep gamma_valid pd all_unif vt pf vv (fforalls vs f) 
    (fforalls_valid vs f Hval Hall) =
    all_dec (forall (h: hlist  (fun x =>
      domain (dom_aux pd) (v_subst (v_typevar vt) x)) (map snd vs)),
      formula_rep gamma_valid pd all_unif vt pf
        (substi_mult vt vv vs h) f Hval).
Proof.
  revert vv.
  generalize dependent (fforalls_valid vs f Hval Hall).
  induction vs; simpl; intros Hval' vv.
  - destruct (formula_rep gamma_valid pd all_unif vt pf vv f Hval') eqn : Hrep; 
    match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end; simpl.
    + exfalso. apply n; intros. erewrite fmla_rep_irrel. apply Hrep.
    + rewrite <- Hrep. erewrite fmla_rep_irrel. apply i. constructor.
  - inversion Hall; subst. specialize (IHvs H2).
    specialize (IHvs (valid_quant_inj (valid_formula_eq eq_refl Hval'))).
    rewrite fforall_rep. apply all_dec_eq.
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

Lemma fforalls_val' (pf: pi_funpred gamma_valid pd)
  (vt: val_typevar) (vv: val_vars pd vt) 
  (vs: list vsymbol) (f: formula) 
  Hval1 Hval2:
  formula_rep gamma_valid pd all_unif vt pf vv (fforalls vs f) 
    Hval2 =
    all_dec (forall (h: hlist  (fun x =>
      domain (dom_aux pd) (v_subst (v_typevar vt) x)) (map snd vs)),
      formula_rep gamma_valid pd all_unif vt pf
        (substi_mult vt vv vs h) f Hval1).
Proof.
  assert (A:=Hval2).
  apply fforalls_valid_inj in A. split_all.
  rewrite fmla_rep_irrel with(Hval2:=(fforalls_valid vs f Hval1 H0)).
  apply fforalls_val.
Qed.

(*Next we give the valuation for an iterated let. This time,
  we don't need to worry about hlists*)
Fixpoint substi_multi_let (pf: pi_funpred gamma_valid pd) (vt: val_typevar) (vv: @val_vars sigma pd vt) 
(vs: list (vsymbol * term)) 
  (Hall: Forall (fun x => term_has_type sigma (snd x) (snd (fst x))) vs) :
val_vars pd vt := 
  match vs as l return
  Forall (fun x => term_has_type sigma (snd x) (snd (fst x))) l ->
  val_vars pd vt
  with
  | nil => fun _ => vv
  | (v, t) :: tl => fun Hall =>
    substi_multi_let pf vt 
      (substi pd vt vv v 
        (term_rep gamma_valid pd all_unif vt pf vv t (snd v) 
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

Lemma iter_flet_val (pf: pi_funpred gamma_valid pd) 
  (vt: val_typevar) (vv: @val_vars sigma pd vt) 
  (vs: list (vsymbol * term)) (f: formula)
  (Hval: valid_formula sigma f)
  (Hall: Forall (fun x => term_has_type sigma (snd x) (snd (fst x))) vs) :
  formula_rep gamma_valid pd all_unif vt pf vv (iter_flet vs f) 
    (iter_flet_valid vs f Hval Hall) =
  formula_rep gamma_valid pd all_unif vt pf 
    (substi_multi_let pf vt vv vs Hall) f Hval.
Proof.
  generalize dependent (iter_flet_valid vs f Hval Hall).
  revert vv.
  induction vs; intros vv Hval'; simpl.
  - apply fmla_rep_irrel.
  - rewrite flet_rep. destruct a. simpl.
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



(*A few results about [indpred_decomp]*)

(*First, validity results we need - this proof is very easy*)
Lemma indpred_decomp_valid (f: formula) (Hval: valid_formula sigma f) :
  Forall (fun x : string * vty => valid_type sigma (snd x)) (tup_1 (indpred_decomp f)) /\
  Forall (fun x : string * vty * term => term_has_type sigma (snd x) (snd (fst x)))
    (tup_2 (indpred_decomp f)) /\
  Forall (valid_formula sigma) (tup_3 (indpred_decomp f)) /\
  valid_formula sigma (tup_4 (indpred_decomp f)).
Proof.
  revert Hval.
  apply (term_formula_ind) with(P1:=fun _ => True) (P2:= fun f =>
    valid_formula sigma f ->
    Forall (fun x : string * vty => valid_type sigma (snd x)) (tup_1 (indpred_decomp f)) /\
    Forall (fun x : string * vty * term => term_has_type sigma (snd x) (snd (fst x)))
      (tup_2 (indpred_decomp f)) /\
    Forall (valid_formula sigma) (tup_3 (indpred_decomp f)) /\
    valid_formula sigma (tup_4 (indpred_decomp f))); simpl; auto; intros.
  - destruct q; simpl; auto.
    inversion H0; subst. specialize (H H6).
    split_all; auto.
  - destruct b; simpl; auto.
    inversion H1; subst. specialize (H H5).
    specialize (H0 H7). split_all; auto.
  - inversion H1; subst.
    specialize (H0 H7). split_all; auto.
  - apply (Tconst (ConstInt 0)).
Qed.

Ltac triv_fls :=
  split_all; intros; 
    match goal with | H: False |- _ => destruct H end.

Lemma indpred_decomp_bound (f: formula) :
  (forall x, In x (tup_1 (indpred_decomp f)) -> In x (bnd_f f)) /\
  (forall x, In x (tup_2 (indpred_decomp f)) -> In (fst x) (bnd_f f)).
Proof.
  apply (term_formula_ind) with(P1:=fun _ => True) (P2:= fun f =>
  (forall x : vsymbol, In x (tup_1 (indpred_decomp f)) -> In x (bnd_f f)) /\
  (forall x : vsymbol * term,
   In x (tup_2 (indpred_decomp f)) -> In (fst x) (bnd_f f))); simpl; auto; intros;
   try solve[triv_fls]. 
  - destruct q; simpl;[|triv_fls].
    split_all; intros.
    + destruct H1; subst. left; auto. right. apply H. auto.
    + apply H0 in H1. right; auto.
  - destruct b; simpl; try triv_fls. split; intros; simpl;
    apply in_or_app; right; apply H0; auto.
  - split_all; intros. right. apply in_or_app. right. apply H0; auto.
    destruct H2; subst. left; auto. right. apply in_or_app. right. 
    apply H1. auto.
  - apply (Tconst (ConstInt 0)).
Qed.


(*TODO: move*)
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


Lemma indpred_decomp_wf (f: formula) (Hwf: fmla_wf f):
  (forall x, ~ (In x (tup_1 (indpred_decomp f)) /\ 
    In x (map fst (tup_2 (indpred_decomp f))))).
Proof.
  revert Hwf.
  apply (term_formula_ind) with(P1:=fun _ => True) (P2:= fun f =>
  fmla_wf f ->
  forall x : vsymbol,
  ~
  (In x (tup_1 (indpred_decomp f)) /\ In x (map fst (tup_2 (indpred_decomp f)))));
  auto; simpl; auto; intros; try solve[intro C; triv_fls].
  - destruct q; simpl; [|intro C; triv_fls].
    intro C. split_all.
    destruct H1; subst.
    + specialize (H (wf_quant _ _ _ H0)).
      unfold fmla_wf in H0.
      simpl in H0. split_all. inversion H0; subst.
      rewrite in_map_iff in H2. destruct H2 as [y [Hy Hiny]].
      assert (In (fst y) (bnd_f f0)).  
      apply indpred_decomp_bound. auto. subst. contradiction.
    + apply (H (wf_quant _ _ _ H0) x); auto.
  - destruct b; simpl; intro C; try triv_fls.
    apply (H0 (proj2 (wf_binop _ _ _ H1)) x). auto.
  - specialize (H0 (wf_let _ _ _ H1)).
    intro C. split_all.
    destruct H3; subst.
    + unfold fmla_wf in H1. simpl in H1. split_all. inversion H1; subst.
      apply H6. apply in_or_app. right. apply indpred_decomp_bound; auto.
    + apply (H0 x); auto.
  - apply (Tconst (ConstInt 0)).
Qed. 

(*How we transform this decomposition into a formula*)
Definition indpred_transform (f: formula) : formula :=
  (fforalls (tup_1 (indpred_decomp f))
      (iter_flet (tup_2 (indpred_decomp f))
        (Fbinop Timplies
          (iter_fand (tup_3 (indpred_decomp f)))
          (tup_4 (indpred_decomp f))))).

Lemma indpred_transform_valid (f: formula) (Hval: valid_formula sigma f) :
  valid_formula sigma (indpred_transform f).
Proof.
  unfold indpred_transform.
  apply fforalls_valid;[|apply indpred_decomp_valid; auto].
  apply iter_flet_valid; [| apply indpred_decomp_valid; auto].
  constructor; [|apply indpred_decomp_valid; auto].
  apply iter_fand_valid; auto.
  apply indpred_decomp_valid; auto.
Qed.

Lemma bool_of_binop_impl: forall b1 b2,
  bool_of_binop Timplies b1 b2 = all_dec (b1 -> b2).
Proof.
  intros. destruct b1; destruct b2; simpl;
  match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end;
  exfalso; apply n; auto.
Qed.

(*TODO: move*)
Lemma distr_impl_forall (pf: pi_funpred gamma_valid pd) 
(vt: val_typevar) (vv: @val_vars sigma pd vt)  
(f1 f2: formula) (x: vsymbol)
(Hval1: valid_formula sigma (Fbinop Timplies f1 (Fquant Tforall x f2)))
(Hval2: valid_formula sigma (Fquant Tforall x (Fbinop Timplies f1 f2))):
~In x (form_fv f1) ->
formula_rep gamma_valid pd all_unif vt pf vv
  (Fbinop Timplies f1 (Fquant Tforall x f2)) Hval1 =
formula_rep gamma_valid pd all_unif vt pf vv
  (Fquant Tforall x (Fbinop Timplies f1 f2)) Hval2.
Proof.
  intros Hnotin.
  rewrite fforall_rep, fbinop_rep, bool_of_binop_impl.
  apply all_dec_eq. rewrite fforall_rep. split; intros.
  - rewrite fbinop_rep, bool_of_binop_impl, simpl_all_dec.
    intros.
    assert (formula_rep gamma_valid pd all_unif vt pf vv f1
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

(*TODO: move*)
Lemma distr_impl_let (pf: pi_funpred gamma_valid pd) 
(vt: val_typevar) (vv: @val_vars sigma pd vt)  
(f1 f2: formula) (t: term) (x: vsymbol)
(Hval1: valid_formula sigma (Fbinop Timplies f1 (Flet t x f2)))
(Hval2: valid_formula sigma (Flet t x (Fbinop Timplies f1 f2))):
~In x (form_fv f1) ->
formula_rep gamma_valid pd all_unif vt pf vv
  (Fbinop Timplies f1 (Flet t x f2)) Hval1 =
formula_rep gamma_valid pd all_unif vt pf vv
  (Flet t x (Fbinop Timplies f1 f2)) Hval2.
Proof.
  intros.
  rewrite flet_rep, !fbinop_rep, !bool_of_binop_impl.
  apply all_dec_eq.
  rewrite flet_rep.
  erewrite form_fv_agree.
  erewrite (form_fv_agree _ _ _ _ _ f2).
  erewrite fmla_rep_irrel.
  erewrite (fmla_rep_irrel _ _ _ _ _ _ f2).
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
Lemma distr_impl_let_forall (pf: pi_funpred gamma_valid pd) 
  (vt: val_typevar) (vv: @val_vars sigma pd vt)  
  (f1 f2: formula)
  (q: list vsymbol) (l: list (vsymbol * term))
  (Hval1: valid_formula sigma (fforalls q (iter_flet l (Fbinop Timplies f1 f2))))
  (Hval2: valid_formula sigma (Fbinop Timplies f1 (fforalls q (iter_flet l f2))))
  (Hq: forall x, ~ (In x q /\ In x (form_fv f1)))
  (Hl: forall x, ~ (In x l /\ In (fst x) (form_fv f1))) :
  formula_rep gamma_valid pd all_unif vt pf vv
    (fforalls q (iter_flet l (Fbinop Timplies f1 f2))) Hval1 =
  formula_rep gamma_valid pd all_unif vt pf vv
    (Fbinop Timplies f1 (fforalls q (iter_flet l f2))) Hval2.
Proof.
  revert vv.
  induction q.
  - simpl.
    (*Prove let case here*)
    induction l; simpl; auto.
    + intros. apply fmla_rep_irrel.
    + intros. erewrite distr_impl_let.
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
  - intros vv. simpl.
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
(*TODO: move*)
Lemma and_impl_bound (pf: pi_funpred gamma_valid pd) 
(vt: val_typevar) (vv: @val_vars sigma pd vt)  
(f1 f2 f3: formula)
(q: list vsymbol) (l: list (vsymbol * term))
Hval1 Hval2: 
formula_rep gamma_valid pd all_unif vt pf vv
  (fforalls q (iter_flet l (Fbinop Timplies (Fbinop Tand f1 f2) f3))) Hval1 =
formula_rep gamma_valid pd all_unif vt pf vv
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
Lemma distr_let_foralls (pf: pi_funpred gamma_valid pd) 
(vt: val_typevar) (vv: @val_vars sigma pd vt)  
(t: term) (x: vsymbol) (f: formula)
(q: list vsymbol) Hval1 Hval2:
(~ In x q) ->
(forall y, In y (term_fv t) -> ~ In y q) ->
formula_rep gamma_valid pd all_unif vt pf vv
  (fforalls q (Flet t x f)) Hval1 =
formula_rep gamma_valid pd all_unif vt pf vv
  (Flet t x (fforalls q f)) Hval2.
Proof.
  intros. revert vv. induction q; intros vv.
  - simpl. apply fmla_rep_irrel.
  - simpl. (*Here, we prove the single transformation*)
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


      (*Now need to simplify let and generalize v*)
      (*TODO: start here - should be doable, just need to push through*)
(*After, finish following lemma, equal interp
  THEN prove that for valid_ind_form, last is p tys tms for tys and
  tms we can get in a function
  THEN prove (probably) that this is still strictly positive
  THEN try to prove main theorem, see where we get stuck
  and see if assuming SP -> (indpred -> P) lets us prove it
  if so, go back to that lemma and prove
  finally, deal with alpha substitution (can assume as
    axiom for now)
  also fix those admitted cases in denot
  *)

(*Now, we prove that any formula which is valid and whose bound
  variables are well-formed is equivalent to the one formed
  by [indpred_decomp]*)
Lemma indpred_decomp_equiv (pf: pi_funpred gamma_valid pd) 
  (vt: val_typevar) (vv: @val_vars sigma pd vt)  
  (f: formula) (Hval: valid_formula sigma f)
  (Hwf: fmla_wf f) :
  formula_rep gamma_valid pd all_unif vt pf vv f Hval =
  formula_rep gamma_valid pd all_unif vt pf vv 
    (indpred_transform f) (indpred_transform_valid f Hval).
Proof.
  revert vv.
  generalize dependent (indpred_transform_valid f Hval).
  (*TODO: we need a better way to do induction with formulas*)
  revert Hval Hwf.
  apply term_formula_ind with(P1:=fun _ => True)
  (P2:= fun f => forall Hval : valid_formula sigma f,
  fmla_wf f -> forall (v : valid_formula sigma (indpred_transform f))
  (vv : val_vars pd vt),
  formula_rep gamma_valid pd all_unif vt pf vv f Hval =
  formula_rep gamma_valid pd all_unif vt pf vv (indpred_transform f) v); 
  unfold indpred_transform; simpl; auto; intros; try solve[apply true_impl].
  - destruct q; simpl; auto; [|apply true_impl].
    simpl in v0. 
    rewrite !fforall_rep. apply all_dec_eq.
    split; intros Hall d.
    + rewrite <- H with (Hval:=(valid_quant_inj (valid_formula_eq eq_refl Hval))). 
      apply (Hall d).
      apply wf_quant in H0; auto.
    + erewrite H. apply (Hall d).
      apply wf_quant in H0; auto.
  - destruct b; try solve[apply true_impl].
    simpl.
    simpl in v.
    (*We need to know that we can push a let and a quantifier
      across an implication. This is why we need the wf assumption*)
    rewrite !fbinop_rep, bool_of_binop_impl.
    assert (Hval1 : valid_formula sigma
    (fforalls (tup_1 (indpred_decomp f2))
       (iter_flet (tup_2 (indpred_decomp f2))
          (Fbinop Timplies (iter_fand (tup_3 (indpred_decomp f2)))
             (tup_4 (indpred_decomp f2)))))). {
      apply fforalls_valid_inj in v. split_all.
      apply fforalls_valid; auto.
      apply iter_flet_valid_inj in H2. split_all.
      apply iter_flet_valid; auto.
      inversion H2; subst.
      constructor; auto.
      inversion H8; subst. auto.
    }
    rewrite H0 with(v:=Hval1); [| apply (wf_binop _ _ _ H1)].
    assert (Hval2: valid_formula sigma
    (fforalls (tup_1 (indpred_decomp f2))
       (iter_flet (tup_2 (indpred_decomp f2))
          (Fbinop Timplies f1 (Fbinop Timplies 
            (iter_fand (tup_3 (indpred_decomp f2))) 
            (tup_4 (indpred_decomp f2))))))). {
      inversion Hval; subst.
      apply fforalls_valid_inj in Hval1. split_all.
      apply iter_flet_valid_inj in H2. split_all.
      inversion H2; subst.
      apply fforalls_valid; auto.
      apply iter_flet_valid; auto.
      constructor; auto.
    }
    rewrite and_impl_bound with(Hval2:=Hval2).
    assert (Hval3: valid_formula sigma (Fbinop Timplies f1
      (fforalls (tup_1 (indpred_decomp f2))
      (iter_flet (tup_2 (indpred_decomp f2))
            (Fbinop Timplies (iter_fand (tup_3 (indpred_decomp f2)))
                (tup_4 (indpred_decomp f2))))))). {
      apply fforalls_valid_inj in Hval2; split_all.
      apply iter_flet_valid_inj in H2; split_all.
      inversion H2; subst. constructor; auto. 
    }
    rewrite (distr_impl_let_forall _ _ _ f1) with(Hval2:=Hval3).
    + rewrite fbinop_rep, bool_of_binop_impl.
      apply all_dec_eq. split; intros;
      erewrite fmla_rep_irrel;
      apply H2; erewrite fmla_rep_irrel; apply H3.
    + (*Now, prove that everything in tup_1 is a bound variable in formula*)
      intros. intro C. split_all.
      unfold fmla_wf in H1. split_all. apply (H4 x).
      split_all; simpl; auto. apply union_elts. left; auto.
      apply in_or_app. right. apply indpred_decomp_bound; auto.
    + intros x C. unfold fmla_wf in H1. split_all.
      apply (H4 (fst x)). split_all.
      simpl. apply union_elts. left; auto.
      simpl. apply in_or_app. right. apply indpred_decomp_bound; auto.
  - (*On to let case*)
    rewrite flet_rep.
    assert (Hval1: valid_formula sigma
    (fforalls (tup_1 (indpred_decomp f0))
       (iter_flet (tup_2 (indpred_decomp f0))
          (Fbinop Timplies (iter_fand (tup_3 (indpred_decomp f0)))
             (tup_4 (indpred_decomp f0)))))). {
      apply fforalls_valid_inj in v0; split_all.
      inversion H2; subst.
      apply fforalls_valid; auto.
    }
    rewrite H0 with(v:=Hval1); [| apply (wf_let _ _ _ H1)].
    (*We showed that we can push a let through a fforalls as long
      as v is not in any of those bound variables*) 
    assert (Hval2: valid_formula sigma (Flet tm v 
    (fforalls (tup_1 (indpred_decomp f0))
       (iter_flet (tup_2 (indpred_decomp f0))
          (Fbinop Timplies (iter_fand (tup_3 (indpred_decomp f0)))
             (tup_4 (indpred_decomp f0))))))). {
      apply fforalls_valid_inj in v0; split_all.
      inversion H2; subst.
      constructor; auto.
    } 
    erewrite distr_let_foralls with(Hval2:=Hval2).
    rewrite flet_rep.
    erewrite term_rep_irrel.
    erewrite fmla_rep_irrel. reflexivity.
    (*These contradict wf*)
    intro C.
    assert (In v (bnd_f f0)). {
      apply indpred_decomp_bound; auto.
    }
    unfold fmla_wf in H1. split_all. simpl in H1. inversion H1; subst.
    apply H6. apply in_or_app; right; auto.
    intros y Hy C.
    assert (In y (bnd_f f0)). {
      apply indpred_decomp_bound; auto.
    }
    unfold fmla_wf in H1. split_all. simpl in H3.
    apply (H3 y). 
    split_all; auto.
    apply union_elts. left; auto.
    right. apply in_or_app. right; auto.
  - apply (Tconst (ConstInt 0)).
Qed.

Print valid_ind_form.
(*Finally, we need to reason about the last part of the formula.
  We show that, for [valid_ind_form]s, this is Fpred p tys tms, for
  tys and tms given by the following function *)
Fixpoint get_indprop_args (f: formula) : (list vty * list term) :=
  match f with
  | Fpred p tys tms => (tys, tms)
  | Fquant Tforall x f1 => get_indprop_args f1
  | Flet t x f1 => get_indprop_args f1
  | Fbinop Timplies f1 f2 => get_indprop_args f2
  | _ => (nil ,nil)
  end.

Lemma ind_form_decomp (p: predsym) (f: formula) 
  (Hval: valid_ind_form p f) :
  (tup_4 (indpred_decomp f)) = Fpred p (fst (get_indprop_args f))
    (snd (get_indprop_args f)).
Proof.
  induction Hval; simpl; auto.
Qed.

(** Results based on Positivity/Strict Positivity *)
(*TODO: move maybe*)
Lemma positive_fforalls (ps: list predsym) (q: list vsymbol) (f: formula):
  ind_positive ps f <->
  ind_positive ps (fforalls q f).
Proof.
  split; intros.
  - induction q; intros; simpl; auto. constructor; auto.
  - induction q; simpl; auto; intros. inversion H; subst; auto.
Qed.
(*
Lemma positive_fforalls (ps: list predsym) (q: list vsymbol) (f: formula):
  ind_positive ps (fforalls q f) ->
  ind_positive ps f.
Proof.
  induction q; simpl; auto. intros.
  inversion H; subst. auto.
Qed.*)

Lemma positive_iter_flet (ps: list predsym) (l: list (vsymbol * term))
  (f: formula):
  ind_positive ps (iter_flet l f) <->
  (Forall (fun x => (forall p, In p ps -> negb (predsym_in_term p (snd x)))) l) /\
  ind_positive ps f.
Proof.
  split; intros.
  - induction l; simpl; auto.
    simpl in H. inversion H; subst.
    specialize (IHl H4). split_all; auto.
  - induction l; simpl; auto. apply H.
    split_all. inversion H; subst.
    constructor; auto.
Qed.

(*First, if p appears in f positively, then p
  appears in [indpred_transform] positively *)
Lemma indpred_transform_positive (ps: list predsym) (f: formula)
  (Hpos: ind_positive ps f):
  ind_positive ps (indpred_transform f).
Proof.
  unfold indpred_transform.
  apply positive_fforalls.
  (*lets are harder because we need to know doesnt appear in term*)
  induction Hpos; simpl; auto.
  - constructor. constructor. auto. constructor; auto.
  - constructor; auto.
  - rewrite positive_iter_flet in IHHpos.
    rewrite positive_iter_flet. split_all; auto.
    clear H0.
    inversion H1; subst.
    constructor; auto.
    apply ISP_and; auto.
Qed.

(*TODO: move*)
Lemma strict_pos_and (ps: list predsym) (f1 f2: formula):
  ind_strictly_positive ps (Fbinop Tand f1 f2) ->
  ind_strictly_positive ps f1 /\
  ind_strictly_positive ps f2.
Proof.
  intros. inversion H; subst.
  - simpl in H0.
    split; apply ISP_notin; intros p Hinp; specialize (H0 p Hinp);
    rewrite negb_orb in H0; apply andb_true_iff in H0; apply H0.
  - auto.
Qed.

Lemma iter_and_strict_pos (ps: list predsym) (fs: list formula):
  ind_strictly_positive ps (iter_fand fs) ->
  forall f, In f fs ->
  ind_strictly_positive ps f.
Proof.
  induction fs; simpl; auto.
  - intros; triv_fls.
  - intros.
    apply strict_pos_and in H. split_all. 
    destruct H0; subst; auto.
Qed.
  
(*From this, we prove that p appears in the "and" part
  strictly positively*)
Lemma indpred_decomp_and_strict_pos (ps: list predsym) (f: formula)
  (Hpos: ind_positive ps f):
  (forall f1, In f1 (tup_3 (indpred_decomp f)) -> ind_strictly_positive ps f1).
Proof.
  intros.
  apply indpred_transform_positive in Hpos.
  unfold indpred_transform in Hpos.
  apply positive_fforalls in Hpos.
  apply positive_iter_flet in Hpos.
  split_all.
  inversion H1; subst.
  apply (iter_and_strict_pos _ _ H4); auto.
Qed.

(*We also conclude that p appears in the last part
  positively*)
Lemma indpred_decomp_last_pos (ps: list predsym) (f: formula)
  (Hpos: ind_positive ps f):
  ind_positive ps (tup_4 (indpred_decomp f)).
Proof.
  apply indpred_transform_positive in Hpos.
  unfold indpred_transform in Hpos.
  apply positive_fforalls in Hpos.
  apply positive_iter_flet in Hpos.
  split_all. inversion H0; subst. auto.
Qed.

(*We also need the fact that everything in (tup_2) does not include
  anything in ps*)
Lemma indpred_decomp_let_notin (ps: list predsym) (f: formula)
  (Hpos: ind_positive ps f):
  Forall (fun x =>
    forall (p: predsym), In p ps -> 
      negb (predsym_in_term p (snd x))) (tup_2 (indpred_decomp f)).
Proof.
  apply indpred_transform_positive in Hpos.
  unfold indpred_transform in Hpos.
  apply positive_fforalls in Hpos.
  apply positive_iter_flet in Hpos.
  split_all; auto.
Qed.

(*We need the following: since all of the constructor
  formulas are closed, they are equivalent under any valuation;
  accordingly, so is [indpred_rep]*)
Lemma constrs_val_eq (pf: pi_funpred gamma_valid pd)
(vt: val_typevar) (v1 v2: val_vars pd vt) 
(fs: list formula)
(Hform: Forall (valid_formula sigma) fs)
(Hclosed: Forall closed_formula fs) :
  iter_and (map is_true (dep_map
    (formula_rep gamma_valid pd  
      all_unif vt pf v1) fs Hform)) =
  iter_and (map is_true (dep_map
    (formula_rep gamma_valid pd  
      all_unif vt pf v2) fs Hform)).
Proof.
  f_equal. f_equal.
  revert Hform.
  induction fs; simpl; auto.
  intros. inversion Hform; subst. inversion Hclosed; subst. 
  f_equal; auto.
  apply fmla_closed_val; auto.
Qed.

Lemma indpred_rep_single_val_eq (pf: pi_funpred gamma_valid pd)
(vt: val_typevar) (v1 v2: val_vars pd vt) (p: predsym)
(fs: list formula) 
(Hform: Forall (valid_formula sigma) fs)
(Hclosed: Forall closed_formula fs) :
  indpred_rep_single pf vt v1 p fs Hform =
  indpred_rep_single pf vt v2 p fs Hform.
Proof.
  unfold indpred_rep_single. 
  repeat(apply functional_extensionality_dep; intros).
  apply all_dec_eq.
  split; intros Hand P; specialize (Hand P);
  erewrite constrs_val_eq; auto; apply Hand.
Qed.

(*Let us prove the following: for a closed formula, the interpretation
  is equivalent under any valuation. Basically, we want to prove
  that [indpred_rep_single], as well as the [formula_rep]s for the
  constructors, can be evaluated under any valuation with the same
  results*)
(*Now we prove our key intermediate lemma that we need:
  suppose f is a formula in which p appears strictly positiviely,
  then [[f]]_(p->indpred_rep p) implies [[f]]_(p->P) for any P*)
Lemma strict_pos_impred_implies_P (pf: pi_funpred gamma_valid pd) 
(vt: val_typevar) (vv: val_vars pd vt)
(p: predsym) (ps: list predsym) 
(fs: list formula) 
(Hinp: In p ps)
(f: formula)
(Hvalf: valid_formula sigma f)
(Hpos: ind_strictly_positive ps f)
(Hform: Forall (valid_formula sigma) fs)
(Hclosed: Forall closed_formula fs)
(Hindpred: preds gamma_valid pd pf p = indpred_rep_single pf vt vv p fs Hform)
:
forall (P: forall srts : list sort,
  arg_list (domain (dom_aux pd)) (predsym_sigma_args p srts) ->
  bool),  
(*If P holds of all of the constructors*)
iter_and (map is_true (dep_map
  (formula_rep gamma_valid pd all_unif vt 
    (interp_with_P pf p P) vv) fs Hform)) ->
(*Then [[f]]_(p->indpred_rep p) implies [[f]]_(p->P)*) 
formula_rep gamma_valid pd all_unif vt pf vv f Hvalf ->
formula_rep gamma_valid pd all_unif vt (interp_with_P pf p P) vv f Hvalf.
Proof.
  intros P HandP.
  generalize dependent vv.
  induction Hpos; simpl; intros vv Hindpred HandP; auto.
  - intros Hrep. erewrite fmla_predsym_agree. apply Hrep.
    all: auto.
    intros p' Hinp'.
    unfold interp_with_P; simpl.
    destruct (predsym_eq_dec p p'); subst; auto.
    specialize (H p' Hinp). rewrite Hinp' in H. inversion H.
  - rewrite !fpred_rep. simpl.
    (*Show arg lists are the same: because P cannot appear
      in list by strict positivity*)
    assert ((get_arg_list_pred pd vt p0 vs ts
    (term_rep gamma_valid pd all_unif vt pf vv)
    (valid_formula_eq eq_refl Hvalf)) =  (get_arg_list_pred pd vt p0 vs ts
    (term_rep gamma_valid pd all_unif vt (interp_with_P pf p P) vv)
    (valid_formula_eq eq_refl Hvalf))). {
      apply get_arg_list_pred_eq.
      rewrite Forall_forall. intros.
      rewrite term_rep_irrel with(Hty2:=Hty2).
      apply term_predsym_agree; simpl; auto.
      intros p' Hinp'.
      destruct (predsym_eq_dec p p'); subst; auto; simpl.
      specialize (H0 _ _ H1 Hinp).
      rewrite Hinp' in H0. inversion H0.
    }
    destruct (predsym_eq_dec p p0); subst; simpl; auto.
    + rewrite Hindpred, H1.
      apply indpred_least_pred_single with(P:=P); auto. 
    + rewrite H1. auto.
  - rewrite !fbinop_rep, !bool_of_binop_impl, !simpl_all_dec.
    intros Hinpl Hval.
    apply IHHpos; auto.
    apply Hinpl. 
    (*Now we use the fact that P is not in f1*)
    rewrite (fmla_predsym_agree) with(p2:=(interp_with_P pf p P)); auto.
    intros p' Hinp'.
    simpl. destruct (predsym_eq_dec p p'); subst; auto.
    specialize (H _ Hinp). rewrite Hinp' in H. inversion H.
  - destruct q.
    + rewrite !fforall_rep, !simpl_all_dec; intros Hall d; specialize (Hall d).
      apply IHHpos; auto.
      (*Use closed fmla assumptions*)
      erewrite indpred_rep_single_val_eq; auto. apply Hindpred.
      erewrite constrs_val_eq; auto. apply HandP.
    + rewrite !fexists_rep, !simpl_all_dec; intros [d Hex]; exists d.
      apply IHHpos; auto.
      erewrite indpred_rep_single_val_eq; auto. apply Hindpred.
      erewrite constrs_val_eq; auto. apply HandP.
  - rewrite !fbinop_rep; simpl; unfold is_true; rewrite !andb_true_iff;
    intros [Hf1 Hf2].
    split; [apply IHHpos1 | apply IHHpos2]; auto.
  - rewrite !fbinop_rep; simpl; unfold is_true; rewrite !orb_true_iff;
    intros [Hf1 | Hf2]; 
    [left; apply IHHpos1 | right; apply IHHpos2]; auto.
  - rewrite !flet_rep; intros Hf.
    apply IHHpos; auto. 
    + erewrite indpred_rep_single_val_eq; auto. apply Hindpred.
    + erewrite constrs_val_eq; auto. apply HandP.
    + (*Need fact that p doesn't appear in let term*)
      erewrite term_predsym_agree. apply Hf. all: auto.
      intros p' Hinp'. unfold interp_with_P; simpl.
      destruct (predsym_eq_dec p p'); subst; auto.
      specialize (H _ Hinp). rewrite Hinp' in H. inversion H.
  - rewrite !fif_rep.
    (*First, know that [[f1]] eq in both cases because P cannot be
      present*)
    assert (Hf1: formula_rep gamma_valid pd all_unif vt pf vv f1
    (proj1 (valid_if_inj (valid_formula_eq eq_refl Hvalf))) =
    formula_rep gamma_valid pd all_unif vt (interp_with_P pf p P) vv f1
    (proj1 (valid_if_inj (valid_formula_eq eq_refl Hvalf)))). {
      apply fmla_predsym_agree; auto; simpl; intros p' Hinp'.
      destruct (predsym_eq_dec p p'); subst; auto.
      specialize (H _ Hinp). rewrite Hinp' in H; inversion H.
    }
    rewrite <- Hf1.
    destruct (formula_rep gamma_valid pd all_unif vt pf vv f1
    (proj1 (valid_if_inj (valid_formula_eq eq_refl Hvalf))));
    [apply IHHpos1 | apply IHHpos2]; auto.
  - (*Hmm, this is the hardest one - need rewrite lemma for match*)
    rewrite !fmatch_rep.
    (*Here, we need a nested induction*)
    generalize dependent (proj2 (valid_match_inv (valid_formula_eq eq_refl Hvalf))).
    generalize dependent  (proj1 (valid_match_inv (valid_formula_eq eq_refl Hvalf))).
    clear Hvalf.
    induction pats; simpl; auto.
    intros Hty Hallval. destruct a as [fh ph].
    (*Show that [term_rep] is equal because P cannot appear*)
    assert (Hteq: 
    (term_rep gamma_valid pd all_unif vt pf vv t ty Hty) =
    (term_rep gamma_valid pd all_unif vt (interp_with_P pf p P) vv t ty Hty)). {
      apply term_predsym_agree; auto. intros p' Hinp'; simpl.
      destruct (predsym_eq_dec p p'); subst; auto.
      specialize (H _ Hinp). rewrite Hinp' in H. inversion H.
    }
    rewrite <- Hteq at 1.
    destruct (match_val_single gamma_valid pd all_unif vt ty
    (has_type_valid gamma_valid t ty Hty)
    (term_rep gamma_valid pd all_unif vt pf vv t ty Hty) fh) eqn : Hm.
    + (*First case follows from original IH*) 
      apply H1; simpl; auto.
      * erewrite indpred_rep_single_val_eq; auto. apply Hindpred.
      * erewrite constrs_val_eq; auto. apply HandP.
    + (*From nested IH*)
      apply IHpats; auto.
      * intros h Hinf. apply H0. right; auto.
      * intros. apply H1; auto. right; auto.
Qed.

(*We axiomatize alpha substitution, we will do it later*)
Axiom alpha_f : formula -> formula.

Axiom alpha_valid : forall (f: formula) (Hval: valid_formula sigma f),
  valid_formula sigma (alpha_f f).

Axiom alpha_f_equiv : forall (pf: pi_funpred gamma_valid pd)
  (vt: val_typevar) (vv: val_vars pd vt) 
  (f: formula) (Hvalf: valid_formula sigma f),
  formula_rep gamma_valid pd all_unif vt pf vv f Hvalf =
  formula_rep gamma_valid pd all_unif vt pf vv (alpha_f f) 
    (alpha_valid f Hvalf).

Axiom alpha_f_wf: forall (f: formula), fmla_wf (alpha_f f).

Axiom alpha_valid_ind_form: forall (p: predsym) (f: formula),
  valid_ind_form p f ->
  valid_ind_form p (alpha_f f).

Axiom alpha_pos: forall (ps: list predsym) (f: formula),
  ind_positive ps f ->
  ind_positive ps (alpha_f f).

(*TODO: move*)
(*If some pred P does not appear in any terms for [substi_multi_let],
  then valuations are equal no matter what P is*)

Lemma substi_mult_notin_eq (pf1 pf2: pi_funpred gamma_valid pd) 
  (vt: val_typevar) (vv: val_vars pd vt) (l: list (vsymbol * term))
  (ps: list predsym) Hall
  (Hallnotin: Forall (fun x => (forall p, In p ps -> 
    negb (predsym_in_term p (snd x)))) l) :
  (forall p, ~ In p ps -> (preds gamma_valid pd pf1 p) = (preds gamma_valid pd pf2 p)) ->
  (forall f, funs gamma_valid pd pf1 f = funs gamma_valid pd pf2 f) ->
  substi_multi_let pf1 vt vv l Hall =
  substi_multi_let pf2 vt vv l Hall.
Proof.
  revert Hall vv.
  induction l; simpl; auto; intros.
  inversion Hallnotin; subst.
  destruct a.
  assert (substi pd vt vv v
  (term_rep gamma_valid pd all_unif vt pf1 vv t (snd v) (Forall_inv Hall)) =
  (substi pd vt vv v
     (term_rep gamma_valid pd all_unif vt pf2 vv t (snd v) (Forall_inv Hall)))). {
    unfold substi. apply functional_extensionality_dep; intros; simpl.
    destruct (vsymbol_eq_dec x v); subst; auto.
    unfold eq_rec_r, eq_rec, eq_rect. simpl.
    apply term_predsym_agree; auto.
    intros p Hinp.
    apply H. intro Hinp'.
    simpl in H3. apply H3 in Hinp'.
    rewrite Hinp in Hinp'. inversion Hinp'.
  }
  rewrite H1.
  apply IHl; auto.
Qed.

(*TODO: move*)
Lemma iter_fand_rep (pd': pi_dom) (pf: pi_funpred gamma_valid pd') 
(vt: val_typevar) (vv: val_vars pd' vt) 
(l: list formula)
(Hall: valid_formula sigma (iter_fand l)) :
formula_rep gamma_valid pd' all_unif vt pf vv (iter_fand l) Hall <->
(forall (f: formula) (Hvalf: valid_formula sigma f),
  In f l -> formula_rep gamma_valid pd' all_unif vt pf vv f Hvalf).
Proof.
  revert Hall.
  induction l; simpl; intros; auto; split; intros; auto.
  - rewrite fbinop_rep in H.
    simpl in H. unfold is_true in H. rewrite andb_true_iff in H.
    destruct H.
    destruct H0; subst.
    + erewrite fmla_rep_irrel. apply H.
    + inversion Hall; subst.
      specialize (IHl H7).
      apply IHl; auto.
      erewrite fmla_rep_irrel. apply H1.
  - rewrite fbinop_rep. simpl.
    inversion Hall; subst.
    specialize (IHl H5).
    apply andb_true_iff. split.
    + erewrite fmla_rep_irrel. apply H. left; auto.
    + erewrite fmla_rep_irrel. apply IHl. intros.
      apply H. right; auto.
      Unshelve.
      auto.
Qed.

(*Now we (at least state) the main theorem*)
(*This is the non-mutual version, mutual should be similar*)
(*TODO: will need to show that [indpred_rep_single] is
  equal on all valuations even if their values for (preds p) 
  are different (not hard)*)
Theorem indpred_constrs_true
  (pf: pi_funpred gamma_valid pd)
  (vt: val_typevar) (vv: val_vars pd vt)
  (p: predsym) (fs: list formula)
  (Hform: Forall (valid_formula sigma) fs)
  (Hvalind: Forall (fun f => valid_ind_form p f) fs)
  (Hpos: Forall (fun f => ind_positive [p] f) fs)
  (Hclosed: Forall closed_formula fs)
  (Hindpred: (preds gamma_valid pd pf) p = 
    indpred_rep_single pf vt vv p fs Hform) :
  (forall (f: formula) (Hvalf: valid_formula sigma f), 
    In f fs ->
    formula_rep gamma_valid pd all_unif vt pf vv f Hvalf).
Proof.
  intros f Hvalf Hinf.
  (*Part 1: work with alpha to get wf*)
  rewrite alpha_f_equiv.
  assert (Hvalindf: valid_ind_form p f). rewrite Forall_forall in Hvalind.
    apply Hvalind; auto.
  assert (Hposf: ind_positive [p] f). rewrite Forall_forall in Hpos.
    apply Hpos; auto.
  assert (Hvalinda:=(alpha_valid_ind_form p f Hvalindf)).
  assert (Hwfa:=(alpha_f_wf f)).
  assert (Hposa:=(alpha_pos [p] f Hposf)).
  (*Part 2: Work with [indpred_transform] *)
  rewrite indpred_decomp_equiv; auto.
  assert (Hvaldec:=(indpred_transform_valid _ (alpha_valid _ Hvalf))).
  (*Then we can unfold manually*)
  unfold indpred_transform in *.
  assert (A:=Hvaldec).
  apply fforalls_valid_inj in A.
  destruct A as [Hval1 Halltup1].
  rewrite fmla_rep_irrel with
    (Hval2:= (fforalls_valid (tup_1 (indpred_decomp (alpha_f f))) _ Hval1 Halltup1)).
  rewrite fforalls_val. rewrite simpl_all_dec. intros h.
  assert (A:=Hval1).
  apply iter_flet_valid_inj in A.
  destruct A as [Hval2 Halltup2].
  rewrite (fmla_rep_irrel) with(Hval2:=(iter_flet_valid _ _ Hval2 Halltup2)).
  rewrite iter_flet_val, fbinop_rep, bool_of_binop_impl, simpl_all_dec.
  intros Hconstrs.
  (*Might need lemma about equality of fmlas*)
  assert (Hval3: valid_formula sigma (Fpred p (fst (get_indprop_args (alpha_f f))) (snd (get_indprop_args (alpha_f f))))). {
    rewrite <- ind_form_decomp; auto.
    inversion Hval2; subst; auto.
  }
  rewrite fmla_rewrite with(Hval2:=Hval3); [|apply ind_form_decomp; auto].
  rewrite fpred_rep, Hindpred.
  (*Now we can unfold the definition of [indpred_rep_single]*)
  unfold indpred_rep_single.
  rewrite simpl_all_dec; intros P Hallconstrs.
  (*Now, we need to know that this constructor (f) is true
    under p->P interp*)
  assert (Hformf: formula_rep gamma_valid pd 
    all_unif vt (interp_with_P pf p P) vv f Hvalf). {
      rewrite <- prove_iter_and in Hallconstrs.
      apply Hallconstrs.
      rewrite in_map_iff. exists (formula_rep gamma_valid pd 
        all_unif vt (interp_with_P pf p P) vv f Hvalf).
      split; auto.
      assert (Hex:=(in_dep_map (formula_rep gamma_valid pd  all_unif vt (interp_with_P pf p P) vv) _ Hform _ Hinf)).
      destruct Hex as [Hval4 Hinf'].
      erewrite fmla_rep_irrel. apply Hinf'.
  }
  (*Now we repeat the process again (alpha, [indpred_transform, etc])*)
  revert Hformf.
  rewrite alpha_f_equiv, indpred_decomp_equiv; auto.
  unfold indpred_transform.
  rewrite fmla_rep_irrel with
    (Hval2:= (fforalls_valid _ _ Hval1 Halltup1)).
  rewrite fforalls_val, simpl_all_dec.
  intros. specialize (Hformf h).
  revert Hformf.
  rewrite (fmla_rep_irrel) with(Hval2:=(iter_flet_valid _ _ Hval2 Halltup2)).
  rewrite iter_flet_val, fbinop_rep, bool_of_binop_impl, simpl_all_dec.
  rewrite fmla_rewrite with(f1:=(tup_4 _))(Hval2:=Hval3); [|apply ind_form_decomp; auto].
  rewrite fpred_rep. simpl.
  destruct (predsym_eq_dec p p); auto; try contradiction.
  assert (e= eq_refl). apply UIP_dec. apply predsym_eq_dec.
  rewrite H. intros.
  (*Need this in multiple places*)
  assert ((substi_multi_let (interp_with_P pf p P) vt
    (substi_mult vt vv (tup_1 (indpred_decomp (alpha_f f))) h)
    (tup_2 (indpred_decomp (alpha_f f))) Halltup2) =
    (substi_multi_let pf vt
     (substi_mult vt vv (tup_1 (indpred_decomp (alpha_f f))) h)
     (tup_2 (indpred_decomp (alpha_f f))) Halltup2)). {
      apply substi_mult_notin_eq with(ps:=[p]); simpl; auto.
      - apply indpred_decomp_let_notin with(ps:=[p]); auto.
      - intros p'. destruct (predsym_eq_dec p p'); auto; subst.
        intros. exfalso. apply H. left; auto.
  }
  (*Now, we need to show that the arguments to P are actually the same
    because these terms cannot involve P*)
  (*Ugly but oh well*)
  match goal with | H: _ -> is_true (P ?y ?z) |- is_true (P ?y ?a) => assert (z = a) end.
  - apply get_arg_list_pred_eq.
    rewrite Forall_forall. intros x Hinx ty Hty1 Hty2.
    rewrite H0.
    rewrite term_rep_irrel with(Hty2:=Hty2).
    apply term_predsym_agree; auto.
    intros p' Hinp'.
    unfold interp_with_P; simpl.
    destruct (predsym_eq_dec p p'); subst; auto.
    exfalso.
    (*Use fact that p' not in x*)
    assert (Hindt: ind_positive [p'] (tup_4 (indpred_decomp (alpha_f f)))).
      apply indpred_decomp_last_pos; auto.
    rewrite ind_form_decomp with(p:=p') in Hindt; auto.
    inversion Hindt; subst.
    specialize (H4 p' x Hinx H2).
    rewrite Hinp' in H4. inversion H4.
  - rewrite <- H1. apply Hformf.
    clear H1 Hformf.
    rewrite H0. clear H0.
    (*TODO: need to prove that this valuation is the
      same on all free vars of f' to get equivalence
      Basically, know because everything in quants list + let
      list is a bound variable and term is wf. But need to show*)
    remember (substi_multi_let pf vt
    (substi_mult vt vv (tup_1 (indpred_decomp (alpha_f f))) h)
    (tup_2 (indpred_decomp (alpha_f f))) Halltup2) as vv'.
    clear Heqvv'.
    (*Now, we just need to prove that the [iter_and] of all of 
      these constructors is true, when we interpre p with P
      instead of [pf]. Here we will use the strict positivity
      lemma TODO*)
    rewrite iter_fand_rep.
    rewrite iter_fand_rep in Hconstrs.
    intros f' Hvalf' Hinf'.
    specialize (Hconstrs f' Hvalf' Hinf').
    revert Hconstrs.
    eapply strict_pos_impred_implies_P with(ps:=[p])(Hform:=Hform); auto.
    + left; auto.
    + apply (indpred_decomp_and_strict_pos _ _ Hposa); auto.
    + erewrite indpred_rep_single_val_eq; auto.
      apply Hindpred.
    + erewrite constrs_val_eq; auto. apply Hallconstrs.
Qed.

(*
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
Qed.*)