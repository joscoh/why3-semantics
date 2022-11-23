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

Lemma constr_test1: test1 0.
Proof.
  unfold test1. intros. apply H.
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

Require Import FunctionalExtensionality.
Require Import Coq.Logic.Eqdep_dec.
Set Bullet Behavior "Strict Subproofs".

Lemma interp_with_Ps_single (pi: pre_interp gamma_valid)
  (p: predsym)
  (Ps: hlist (fun p => forall srts, 
    arg_list (domain (dom_aux _ pi)) 
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

Search in_bool In.

(*Since inductive predicates can be mutually recursive, we need
  a list of predsyms and formula lists. This makes the dependent
  types tricky, since we need a (P: forall srts, arg_list srts -> bool)
  for each such predsym*)

Definition indpred_rep (v: valuation gamma_valid i) 
  (indpred : list (predsym * list formula))
  (Hform: Forall (Forall (valid_formula sigma)) (map snd indpred)) 
  (p: predsym)
  (Hin: in_bool predsym_eq_dec p (map fst indpred))
  (*(Hin: In p (map fst indpred))*)
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
      (*All of this together implies Pi srts a, for the
        i corresponding to p*)
      (get_hlist_elt predsym_eq_dec Ps p Hin)
        (*(In_in_bool predsym_eq_dec _ _ Hin))*) srts a).

  (*The encoding we want*)
(*The version for non-mutual-recursion is a lot simpler*)
Definition indpred_rep_single (v: valuation gamma_valid i) (p: predsym)
  (fs: list formula) (Hform: Forall (valid_formula sigma) fs) (srts: list sort) 
  (a: arg_list (domain (dom_aux gamma_valid i)) 
  (predsym_sigma_args p srts)) : bool :=
  (*TODO: change preds to Prop instead of bool?*)
  all_dec
  (forall (P: forall (srts: list sort), 
    arg_list (domain (dom_aux gamma_valid i)) 
    (predsym_sigma_args p srts) -> bool),
    iter_and (map is_true (dep_map (@formula_rep _ _ gamma_valid 
      (interp_with_P i p P) all_unif (interp_P_val i p P v)) 
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
*)
(*
(*TODO: this is very, very hard to prove.
  Dependent types are a nightmare*)
Lemma indpred_rep_single_equiv (v: valuation gamma_valid i) (p: predsym)
(fs: list formula) (Hform: Forall (valid_formula sigma) fs) (srts: list sort) 
(a: arg_list (domain (dom_aux gamma_valid i)) 
(predsym_sigma_args p srts)) :
  indpred_rep_single v p fs Hform srts a <->
  indpred_rep v [(p, fs)] (Forall_single Hform) p (temp p fs) srts a.
Proof.
  unfold indpred_rep_single.
  unfold indpred_rep. simpl.
  split; intros.
  - generalize dependent (temp p fs). simpl.
    destruct (predsym_eq_dec p p); simpl; auto.
    intros _. unfold eq_rect_r. unfold eq_rect.
    assert (e = eq_refl) by (apply UIP_dec; apply predsym_eq_dec).
    rewrite H1. simpl.
    apply H.
    destruct H0 as [Hand _].
    assert (Heq: dep_map
    (formula_rep gamma_valid (interp_with_Ps i [p] Ps) all_unif
       (interp_Ps_val i [p] Ps v)) fs (Forall_inv (Forall_single Hform)) =
       (dep_map
        (formula_rep gamma_valid (interp_with_P i p (hlist_hd Ps)) all_unif
           (interp_P_val i p (hlist_hd Ps) v)) fs Hform)); [| rewrite <- Heq; auto].
    (*unfold interp_P_val, interp_Ps_val. simpl.*)
    rewrite (dep_map_irrel) with(Hall1:=Hform)(Hall2:= (Forall_inv (Forall_single Hform))).
    2 : {
      intros x Hval1 Hval2.
      apply term_form_rep_irrel. apply (Tconst (ConstInt 0)).
    }
    f_equal.
    assert (Hieq:= (interp_with_Ps_single i p Ps)).
    (*I don't know if this is provable, even with UIP*)
    assert (interp_P_val i p (hlist_hd Ps) v = val_from_eq _ _ Hieq
      (interp_Ps_val i [p] Ps v)). {
      (*TODO: if it works, separate lemma**)
      unfold val_from_eq. unfold interp_P_val.
      f_equal. repeat(apply functional_extensionality_dep; intros).
      unfold dom_cast'. unfold dom_aux_eq.
      (* Can i use UIP to do this? *)
      assert (match
        Hieq in (_ = y)
        return (dom_aux gamma_valid (interp_with_Ps i [p] Ps) = dom_aux gamma_valid y)
      with
      | eq_refl => eq_refl
      end = eq_refl). {
Admitted.
*)
(*Prove that this is the least fixpoint*)
(*TODO: what is the actual definition*)
(*We must show the following: 
  1. When our intepretations inteprets the predicate(s) P 
    as [indpred_rep], then 
    all of the constructor reps should imply P(x)
  2: TODO
    *)

(*TODO: move to denotational*)
Lemma fpred_rep (pi: pre_interp gamma_valid) (v: valuation gamma_valid pi) 
(p: predsym) (vs: list vty) (args: list term)
  (Hval: valid_formula sigma (Fpred p vs args)) :
  formula_rep gamma_valid pi all_unif v (Fpred p vs args) Hval =
  preds gamma_valid pi p (map (v_subst (v_typevar gamma_valid pi v)) vs)
    (get_arg_list_pred gamma_valid pi v p vs args 
    (term_rep gamma_valid pi all_unif v)
    (valid_formula_eq eq_refl Hval)).
Proof.
  reflexivity.
Qed.

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


(*First prove for single bc dependent types suck*)
Lemma indpred_constrs_true (v: valuation gamma_valid i)
  (p: predsym) (fs: list formula) (Hall: Forall (valid_formula sigma) fs)
  (*(srts: list sort) (args: list term)
  (Hval: valid_formula sigma (Fpred p (sorts_to_tys srts) args))*)
  (*
  (a: arg_list (domain (dom_aux gamma_valid i)) (predsym_sigma_args p srts))*)
  (*TODO: is this right? We will be changing, although valuation
    won't change*)
  (Hindpred: preds gamma_valid i p = 
    indpred_rep_single v p fs Hall) :
  (iter_and (map is_true (dep_map 
    (@formula_rep _ _ gamma_valid i all_unif v) fs Hall))).
Proof.
  rewrite <- prove_iter_and. intros P.
  rewrite in_map_iff. intros [b [Hb Hinb]].
  apply dep_map_in in Hinb. destruct Hinb as [f [Hvalf [Hinf Hfrep]]].
  rewrite <- Hb. rewrite <- Hfrep.
  assert (valid_ind_form p f) by admit.
  inversion H; subst.
  - rewrite fpred_rep.
    rewrite Hindpred. unfold indpred_rep_single.
    rewrite simpl_all_dec. intros P Hconstrs.
    (*Know this is true because in the list*)
    rewrite <- prove_iter_and in Hconstrs.
    specialize (Hconstrs (all_dec (P (map (v_subst (v_typevar gamma_valid i v)) (map vty_var (p_params p)))
    (get_arg_list_pred gamma_valid i v p (map vty_var (p_params p)) tms
       (term_rep gamma_valid i all_unif v) (valid_formula_eq eq_refl Hvalf))))).
    rewrite <- simpl_all_dec. apply Hconstrs.
    rewrite in_map_iff.
    exists (all_dec
    (P (map (v_subst (v_typevar gamma_valid i v)) (map vty_var (p_params p)))
       (get_arg_list_pred gamma_valid i v p (map vty_var (p_params p)) tms
          (term_rep gamma_valid i all_unif v)
          (valid_formula_eq eq_refl Hvalf)))). split; auto.
    pose proof (in_dep_map (formula_rep gamma_valid (interp_with_P i p P) all_unif
    (interp_P_val i p P v)) fs Hall _ Hinf).
    destruct H0 as [Hval Hin].
    assert (formula_rep gamma_valid (interp_with_P i p P) all_unif
    (interp_P_val i p P v) (Fpred p (map vty_var (p_params p)) tms)
    Hval = (all_dec
    (P
       (map (v_subst (v_typevar gamma_valid i v)) (map vty_var (p_params p)))
       (get_arg_list_pred gamma_valid i v p (map vty_var (p_params p)) tms
          (term_rep gamma_valid i all_unif v)
          (valid_formula_eq eq_refl Hvalf))))). {
      rewrite fpred_rep.
      (*Hmm, need some additional info about how [interp_with_P]
        relates to our interp (which of course has [indpred_rep])
        We want [indpred_rep] to imply P
        We should also work with Props, not bools, so we can use iff*)
      assert (forall (P1 P2: Prop), (P1 <-> P2) = (P1 = P2)) by admit.
      simpl. destruct (predsym_eq_dec p p); simpl;[|contradiction].
      assert (e = eq_refl). apply UIP_dec. apply predsym_eq_dec.
      rewrite H2.
      (*OK, now just need to know something about relation between
        interp_with_P and i applied to P*)
        
      
      rewrite <- H0.

      rewrite <- H0.

          }




    Check in_dep_map.

    in_dep_map

    
    
    exists ((P (map (v_subst (v_typevar gamma_valid i v)) (map vty_var (p_params p)))
    (get_arg_list_pred gamma_valid i v p (map vty_var (p_params p)) tms
       (term_rep gamma_valid i all_unif v)
       (valid_formula_eq eq_refl Hvalf)))).
    split.
    
    rewrite simpl_all_dec. 


    




    unfold all_dec.
    intros. intros.




  destruct b; rewrite <- Hb; auto.
  (*Now we need to show that this formula is actually true*)
  (*Here, we might need the valid_ind_form*)
  assert (valid_ind_form p f) by admit.
  inversion H; subst.
  - rewrite fpred_rep in Hfrep.
    rewrite Hindpred in Hfrep.
    rewrite <- Hfrep.
    unfold indpred_rep_single.
    

 
    match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end.
    exfalso. apply n. intros P Hiter.
    intros _.
    exfalso. apply 



    match goal with | H: (proj_sumbool _ (all_dec ?P)) = false |- _ => destruct (all_dec P); auto end.




  rewrite <- Hfrep.



  clear Hfrep.



  inversion Hvalf.



  
  


  Print iter_and.

    formula_rep _ _  all_unif v (Fpred p (sorts_to_tys srts) args) Hval.
Proof.
  intros Hconstrs.
  rewrite fpred_rep.
  rewrite Hindpred.
  unfold indpred_rep_single.
  match goal with |- context [all_dec ?P] => destruct (all_dec P); auto end.
  exfalso. apply n. intros P Hallp. clear n.
  Print indpred_rep_single.
  apply indpred_rep_single.


  intros iter.


  cbn.

  vm_compute.
  simpl.
  Print formula_rep.
  unfold formula_rep. simpl.
  simpl.

  () srts a.
  (interp_with_P i p P) all_unif (interp_P_val i p P v)) 
  fs Hform))


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

