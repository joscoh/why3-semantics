Require Import Common.
Require Import Types.
Require Import Syntax.

(** Typechecking **)

(*Signature*)
Record sig :=
  {
    sig_t : list typesym;
    sig_f: list funsym;
    sig_p: list predsym
  }.

(* Typing rules for types *)
Inductive valid_type : sig -> vty -> Prop :=
  | vt_int: forall s,
    valid_type s vty_int
  | vt_real: forall s,
    valid_type s vty_real
  | vt_tycons: forall s ts vs,
    In ts (sig_t s) ->
    length vs = (ts_arity ts) ->
    Forall (fun x => valid_type s x) vs ->
    valid_type s (vty_cons ts vs).
(*Notation "s '|-' t" := (valid_type s t) (at level 40).*)

(* Typing rules for terms *)
Inductive term_has_type: sig -> term -> vty -> Prop :=
  | T_int: forall s z,
    term_has_type s (Tconst (ConstInt z)) vty_int
  | T_real: forall s r,
    term_has_type s (Tconst (ConstReal r)) vty_real
  | T_Var: forall s x ty,
    valid_type s ty ->
    term_has_type s (Tvar x ty) ty
  | T_Fun: forall s (params : list vty) (tms : list term) (f: funsym),
    In f (sig_f s) ->
    Forall (valid_type s) params ->
    length tms = length (s_args f) ->
    length params = length (s_params f) ->
    (* For all i, [nth i tms] has type [sigma(nth i (s_args f))], where
      sigma is the type substitution that maps f's type vars to [params] *)
    Forall (fun x => term_has_type s (fst x) (snd x)) (combine tms
      (map (ty_subst (s_params f) params) (s_args f))) ->
    term_has_type s (Tfun f params tms) (s_ret f)
  | T_Let: forall s t1 x ty t2 ty2,
    term_has_type s t1 ty ->
    term_has_type s t2 ty2 ->
    term_has_type s (Tlet t1 x ty t2) ty2
    (*TODO: make sure this works with nats as vars*)
  | T_If: forall s f t1 t2 ty,
    valid_formula s f ->
    term_has_type s t1 ty ->
    term_has_type s t2 ty ->
    term_has_type s (Tif f t1 t2) ty

(* Typing rules for formulas *)
with valid_formula: sig -> formula -> Prop :=
  | F_True: forall s,
    valid_formula s Ftrue
  | F_False: forall s,
    valid_formula s Ffalse
  | F_Binop: forall s b f1 f2,
    valid_formula s f1 ->
    valid_formula s f2 ->
    valid_formula s (Fbinop b f1 f2)
  | F_Not: forall s f,
    valid_formula s f ->
    valid_formula s (Fnot f)
  | F_Quant: forall s q x ty f,
    valid_type s ty ->
    valid_formula s f ->
    valid_formula s (Fquant q x ty f)
  | F_Pred: forall s (params: list vty) (tms: list term) (p: predsym),
    (*Very similar to function case*)
    In p (sig_p s) ->
    Forall (valid_type s) params ->
    length tms = length (p_args p) ->
    length params = length (p_params p) ->
    Forall (fun x => term_has_type s (fst x) (snd x))
      (combine tms (map (ty_subst (p_params p) params) (p_args p))) ->
    valid_formula s (Fpred p params tms)
  | F_Let: forall s t x ty f,
    term_has_type s t ty ->
    valid_formula s f ->
    valid_formula s (Flet t x ty f)
  | F_If: forall s f1 f2 f3,
    valid_formula s f1 ->
    valid_formula s f2 ->
    valid_formula s f3 ->
    valid_formula s (Fif f1 f2 f3)
  | F_Eq: forall s ty t1 t2,
    term_has_type s t1 ty ->
    term_has_type s t2 ty ->
    valid_formula s (Feq ty t1 t2).
(*
Notation "s '|-' t ':' ty" := (term_has_type s t ty) (at level 40).
Notation "s '|-' f" := (valid_formula s f) (at level 40).*)

Lemma bool_dec: forall {A: Type} (f: A -> bool),
  (forall x : A, {is_true (f x)} + {~ is_true (f x)}).
Proof.
  intros A f x. destruct (f x) eqn : Hfx; auto.
  right. intro C. inversion C.
Qed.

(* Let's try to build a typechecker *)
Fixpoint typecheck_type (s:sig) (v: vty) : bool :=
  match v with
  | vty_int => true
  | vty_real => true
  | vty_var tv => false
  | vty_cons ts vs => 
      In_dec typesym_eq_dec ts (sig_t s) &&
      Nat.eqb (length vs) (ts_arity ts) &&
      (fix check_list (l: list vty) : bool :=
      match l with
      | nil => true
      | x :: t => typecheck_type s x && check_list t
      end) vs
  end.

(*We would like to prove this correct*)
Lemma typecheck_type_correct: forall (s: sig) (v: vty),
  valid_type s v <-> typecheck_type s v = true.
Proof.
  intros s. induction v; simpl; try solve[split; auto; constructor].
  - split; intros Hty; inversion Hty.
  - split; intros Hty.
    + inversion Hty; subst. repeat(apply andb_true_intro; split).
      simpl_sumbool. apply Nat.eqb_eq. auto.
      clear Hty H2 H4. induction vs; simpl; auto; intros.
      inversion H; subst. inversion H5; subst.
      apply andb_true_intro; split; auto. apply H2; auto.
    + apply andb_true_iff in Hty; destruct Hty.
      apply andb_true_iff in H0; destruct H0.
      simpl_sumbool. apply Nat.eqb_eq in H2. constructor; auto.
      clear i H2. induction vs; simpl; auto; intros.
      apply andb_true_iff in H1; destruct H1.
      inversion H; subst. constructor; auto.
      apply H4; auto.
      
      Qed. 
(*
Fixpoint typecheck_term (t: term) : option vty :=
  match t with
  | Tconst (ConstInt _) => Some vty_int
  | Tconst (ConstReal _) => Some vty_real
  | Tconst _ => None (*for now*)
  | Tvar n v => if typecheck_type v then Some v else None
  (*TODO: later*)
*)