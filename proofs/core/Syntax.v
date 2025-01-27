Require Import Coq.QArith.QArith_base.
Require Export Types.
From stdpp Require infinite.
Set Bullet Behavior "Strict Subproofs".

(** Function and Predicate Symbols **)

(*We use bools rather than props so that we get decidable equality (like ssreflect)*)

(*Check for sublist (to enable building these structures)*)
(* Definition check_sublist (l1 l2: list typevar) : bool :=
  forallb (fun x => in_dec typevar_eq_dec x l2) l1.

Lemma check_sublist_correct: forall l1 l2,
  reflect (sublist l1 l2) (check_sublist l1 l2).
Proof.
  intros. destruct (check_sublist l1 l2) eqn : Hsub.
  - unfold check_sublist in Hsub. rewrite forallb_forall in Hsub.
    apply ReflectT. unfold sublist; intros.
    apply Hsub in H. simpl_sumbool.
  - apply ReflectF. unfold sublist. intro.
    assert (check_sublist l1 l2 = true). {
      apply forallb_forall. intros. simpl_sumbool.
    }
    rewrite H0 in Hsub; inversion Hsub.
Qed. *)

Definition check_args (params: list typevar) (args: list vty) : bool :=
  forallb (fun x => check_asubset (type_vars x) (list_to_aset params)) args.

(*Would be easier with ssreflect*)
Lemma check_args_correct: forall params args,
  reflect (forall x, In x args -> asubset (type_vars x) (list_to_aset params)) (check_args params args).
Proof.
  intros. unfold check_args. apply iff_reflect.
  rewrite forallb_forall. split; intros Hall x Hinx; [|specialize (Hall x Hinx)];
  destruct (check_asubset (type_vars x) (list_to_aset params)); simpl; auto.
  discriminate.
Qed.

(*Easy corollaries, need these for arguments to other functions which don't know
  about the decidable versions*)

Lemma check_args_prop {params args} :
  check_args params args -> forall x, In x args -> asubset (type_vars x) (list_to_aset params).
Proof.
  intros Hcheck. apply (reflect_iff _ _ (check_args_correct params args)).
  apply Hcheck.
Qed.

(* Lemma check_sublist_prop {l1 l2}:
  check_sublist l1 l2 ->
  sublist l1 l2.
Proof.
  intros. apply (reflect_iff _ _ (check_sublist_correct l1 l2)), H.
Qed. *)

(*We separate out the name, args, and params because they
  are common; this helps us avoid duplicating some results.
  The difference is in the return types*)
Record fpsym : Set :=
  { s_name: string;
    s_params: list typevar;
    s_args: list vty;
    (*Well-formed - all type variables appear in params*)
    s_args_wf: check_args s_params s_args;
    s_params_nodup: nodupb typevar_eq_dec s_params}.

Record funsym: Set :=
  { f_sym: fpsym;
    f_ret: vty;
    f_is_constr : bool; (*is the funsym a constructor?*)
    f_num_constrs : nat; (*if so, how many constrs in ADT?*)
    f_ret_wf : is_true (check_asubset (type_vars f_ret) 
      (list_to_aset (s_params f_sym))) }.

Coercion f_sym : funsym >-> fpsym.

Record predsym: Set :=
    { p_sym : fpsym }.

Coercion p_sym : predsym >-> fpsym.

Lemma s_params_Nodup: forall (s: fpsym),
  NoDup (s_params s).
Proof.
  intros. eapply reflect_iff. apply nodup_NoDup. 
  apply s_params_nodup.
Qed.

Lemma f_params_Nodup: forall (f: funsym),
  NoDup (s_params f).
Proof.
  intros.
  apply s_params_Nodup.
Qed.

Lemma p_params_Nodup: forall (p: predsym),
  NoDup (s_params p).
Proof.
  intros. apply s_params_Nodup.
Qed.


(*As an example, we define the polymorphic identity function*)
Section ID.

Definition id_name : string := "id".
Definition a_var : string := "a".
Definition id_params : list typevar := [a_var].
Definition id_args: list vty := [vty_var a_var].
Definition id_ret: vty := vty_var a_var.

Definition id_sym : fpsym := Build_fpsym id_name id_params id_args eq_refl eq_refl.

Definition id_fs : funsym := Build_funsym id_sym id_ret false 0 eq_refl.

End ID.

Ltac destruct_triv p :=
  destruct p; try solve[apply ReflectF; intro C; inversion C].

Section SymEqDec.

Lemma fpsym_eq: forall (s1 s2: fpsym),
  s_name s1 = s_name s2 ->
  s_params s1 = s_params s2 ->
  s_args s1 = s_args s2 ->
  s1 = s2.
Proof.
  intros. destruct s1; destruct s2; simpl in *; subst.
  f_equal; apply bool_irrelevance.
Qed.

Definition fpsym_eqb (s1 s2: fpsym): bool :=
  (String.eqb (s_name s1) (s_name s2)) &&
  (list_eqb String.eqb (s_params s1) (s_params s2)) &&
  (list_eqb vty_eqb (s_args s1) (s_args s2)).

Lemma fpsym_eqb_spec: forall (f1 f2: fpsym),
  reflect (f1 = f2) (fpsym_eqb f1 f2).
Proof.
  intros. unfold fpsym_eqb.
  dec (String.eqb_spec (s_name f1) (s_name f2)).
  dec (list_eqb_spec _ String.eqb_spec (s_params f1) (s_params f2)).
  dec (list_eqb_spec _ vty_eq_spec (s_args f1) (s_args f2)).
  apply ReflectT. apply fpsym_eq; auto.
Qed.

Definition fpsym_eq_dec (f1 f2: fpsym) : {f1 = f2} + {f1 <> f2} :=
  reflect_dec' (fpsym_eqb_spec f1 f2).

Lemma funsym_eq: forall (f1 f2: funsym),
  f_sym f1 = f_sym f2 ->
  f_ret f1 = f_ret f2 ->
  f_is_constr f1 = f_is_constr f2 ->
  f_num_constrs f1 = f_num_constrs f2 ->
  f1 = f2.
Proof.
  intros. destruct f1; destruct f2; simpl in *; subst.
  f_equal; apply bool_irrelevance.
Qed.

Definition funsym_eqb (f1 f2: funsym) : bool :=
  (fpsym_eqb (f_sym f1) (f_sym f2)) &&
  (vty_eqb (f_ret f1) (f_ret f2)) &&
  (Bool.eqb (f_is_constr f1) (f_is_constr f2)) &&
  (Nat.eqb (f_num_constrs f1) (f_num_constrs f2)).

Lemma funsym_eqb_spec: forall (f1 f2: funsym),
  reflect (f1 = f2) (funsym_eqb f1 f2).
Proof.
  intros. unfold funsym_eqb.
  dec (fpsym_eqb_spec (f_sym f1) (f_sym f2)).
  dec (vty_eq_spec (f_ret f1) (f_ret f2)).
  dec (Bool.eqb_spec (f_is_constr f1) (f_is_constr f2)).
  dec (Nat.eqb_spec (f_num_constrs f1) (f_num_constrs f2)).
  apply ReflectT. apply funsym_eq; auto.
Qed.

Definition funsym_eq_dec (f1 f2: funsym) : {f1 = f2} + {f1 <> f2} :=
  reflect_dec' (funsym_eqb_spec f1 f2).

(*We do the same for predicate symbols*)

Definition predsym_eqb (p1 p2: predsym) : bool :=
  fpsym_eqb (p_sym p1) (p_sym p2).

Lemma predsym_eqb_spec: forall (p1 p2: predsym),
  reflect (p1 = p2) (predsym_eqb p1 p2).
Proof.
  intros. unfold predsym_eqb.
  dec (fpsym_eqb_spec p1 p2).
  apply ReflectT. destruct p1; destruct p2; simpl in *; subst; auto.
Qed.

Definition predsym_eq_dec (p1 p2: predsym) : {p1 = p2} + {p1 <> p2} :=
  reflect_dec' (predsym_eqb_spec p1 p2).

End SymEqDec.

(*Countable*)

(*Do in 2 layers (similarly to how they do sigma types - first show injective to send to tuple*)

Definition fpsym_to_tup (f: fpsym) : (string * list typevar * list vty) :=
  (s_name f, s_params f, s_args f).

Definition tup_to_fpsym (x: string * list typevar * list vty) : option fpsym :=
  let n := fst (fst x) in
  let p := snd (fst x) in
  let a := snd x in
  match (check_args p a) as b1 return check_args p a = b1 -> option fpsym with
  | true => fun a_wf =>
      match (nodupb typevar_eq_dec p) as b2 return nodupb typevar_eq_dec p = b2 -> option fpsym with
      | true => fun p_nodup => Some (Build_fpsym n p a a_wf p_nodup)
      | false => fun _ => None
      end eq_refl
  | false => fun _ => None
  end eq_refl.

Lemma fpsym_to_tup_inj: forall x,
  tup_to_fpsym (fpsym_to_tup x) = Some x.
Proof.
  intros [n p a a_wf p_nodup].
  unfold fpsym_to_tup. simpl. unfold tup_to_fpsym.
  simpl.
  generalize dependent (@eq_refl bool (check_args p a)).
  generalize dependent (@eq_refl bool (nodupb typevar_eq_dec p)).
  generalize dependent ((Build_fpsym n p a)).
  rewrite a_wf, p_nodup; intros; subst; auto.
  f_equal; f_equal; apply bool_irrelevance.
Qed.

Instance fpsym_EqDecision : @base.RelDecision fpsym fpsym eq.
Proof. unfold base.RelDecision. apply fpsym_eq_dec. Defined.

Instance fpsym_Countable : countable.Countable fpsym :=
  countable.inj_countable fpsym_to_tup tup_to_fpsym fpsym_to_tup_inj.

(*Now for fun and predsyms*)

Definition funsym_to_tup (f: funsym) : fpsym * vty * bool * nat :=
  (f_sym f, f_ret f, f_is_constr f, f_num_constrs f).
Definition tup_to_funsym (x: fpsym * vty * bool * nat) : option funsym :=
  let s := fst (fst (fst x)) in
  let r := snd (fst (fst x)) in
  let i := snd (fst x) in
  let n := snd x in
  match proj_sumbool _ _ (check_asubset (type_vars r) (list_to_aset (s_params s))) as b return
    proj_sumbool _ _ (check_asubset (type_vars r) (list_to_aset (s_params s))) = b -> option funsym with
  | true => fun r_wf => Some (Build_funsym s r i n r_wf)
  | false => fun _ => None
  end eq_refl.

Lemma funsym_to_tup_inj: forall x,
  tup_to_funsym (funsym_to_tup x) = Some x.
Proof.
  intros [s r i n r_wf].
  unfold funsym_to_tup. simpl. unfold tup_to_funsym.
  simpl.
  generalize dependent (@eq_refl bool (proj_sumbool _ _ (check_asubset (type_vars r) (list_to_aset (s_params s))))).
  generalize dependent (Build_funsym s r i n).
  rewrite r_wf. intros; f_equal; f_equal; apply bool_irrelevance.
Qed.

Instance funsym_EqDecision : @base.RelDecision funsym funsym eq.
Proof. unfold base.RelDecision. apply funsym_eq_dec. Defined.

Instance funsym_Countable : countable.Countable funsym :=
  countable.inj_countable funsym_to_tup tup_to_funsym funsym_to_tup_inj.

(*Predsym much easier*)

Instance predsym_EqDecision : @base.RelDecision predsym predsym eq.
Proof. unfold base.RelDecision. apply predsym_eq_dec. Defined.

Instance predsym_Countable : countable.Countable predsym :=
  countable.inj_countable' p_sym Build_predsym (ltac:(intros [x]; reflexivity)).

(*Create function symbols*)
Definition find_args (l: list vty) : list typevar :=
  aset_to_list (aset_big_union type_vars l).


Lemma find_args_nodup l:
  nodupb typevar_eq_dec (find_args l).
Proof.
  unfold find_args.
  apply (ssrbool.introT (nodup_NoDup _ _)).
  apply aset_to_list_nodup.
Qed.


Lemma find_args_check_args_l l1 l2:
  (forall x, In x l1 -> In x l2) ->
  check_args (find_args l2) l1.
Proof.
  intros.
  apply (ssrbool.introT (check_args_correct _ _)).
  intros.
  unfold find_args. rewrite asubset_def. intros.
  simpl_set.
  exists x. split; auto.
Qed.

Lemma find_args_check_args_in x l:
  In x l ->
  check_asubset (type_vars x) (list_to_aset (find_args l)).
Proof.
  intros. destruct (check_asubset _ _); simpl; auto.
  exfalso; apply n. rewrite asubset_def. intros y Hiny.
  simpl_set. unfold find_args. simpl_set.
  exists x; auto.
Qed.

Definition funsym_noconstr_noty (name: string) (args: list vty) 
  (ret: vty)  : funsym :=
  Build_funsym (Build_fpsym name (find_args (ret :: args)) args
    (find_args_check_args_l _ _ (fun x => in_cons _ x _)) (find_args_nodup _)) 
    ret false 0 (find_args_check_args_in _ _ (in_eq _ _)).

(** Syntax - Terms and Formulas **)

Inductive constant : Set :=
  | ConstInt : Z -> constant
  (*Only rational numbers can be represented by why3 - represent
    using whole part, decimal part, and exponent*)
  | ConstReal : Q -> constant
  (*| ConstStr : string -> constant*).

Inductive quant : Set :=
    | Tforall
    | Texists.

Inductive binop : Set :=
    | Tand
    | Tor
    | Timplies
    | Tiff.

Definition vsymbol : Set := (string * vty).

Definition vsymbol_eqb (x y: vsymbol) :=
  tuple_eqb String.eqb vty_eqb x y.

Lemma vsymbol_eqb_spec (x y: vsymbol) :
  reflect (x = y) (vsymbol_eqb x y).
Proof.
  apply tuple_eqb_spec.
  apply String.eqb_spec.
  apply vty_eq_spec.
Qed.

Definition vsymbol_eq_dec (x y: vsymbol): 
  {x = y} + {x <> y} := reflect_dec' (vsymbol_eqb_spec x y).

Instance vsymbol_inf : base.Infinite vsymbol.
Proof.
apply infinite.prod_infinite_l.
Defined.

(*Useful for inference*)
Instance vsymbol_EqDecision : @base.RelDecision vsymbol vsymbol eq.
Proof.
  unfold vsymbol.
  apply decidable.prod_eq_dec.
Defined.

(*TODO: do we even need this?*)
(* Instance vsymbol_countable : countable.Countable vsymbol := countable.prod_countable. *)

Unset Elimination Schemes.
Inductive pattern : Set :=
  | Pvar : vsymbol -> pattern
  | Pconstr : funsym -> list vty -> list pattern -> pattern
  | Pwild : pattern
  | Por: pattern -> pattern -> pattern
  | Pbind: pattern -> vsymbol -> pattern.

Inductive term : Set :=
  | Tconst: constant -> term
  | Tvar : vsymbol -> term
  | Tfun: funsym -> list vty -> list term -> term
  | Tlet: term -> vsymbol -> term -> term
  | Tif: formula -> term -> term -> term
  | Tmatch: term -> vty -> list (pattern * term) -> term
  | Teps: formula -> vsymbol ->term
with formula : Set :=
  | Fpred: predsym -> list vty -> list term -> formula
  | Fquant: quant -> vsymbol -> formula -> formula
  | Feq: vty -> term -> term -> formula
  | Fbinop: binop -> formula -> formula -> formula
  | Fnot: formula -> formula
  | Ftrue: formula
  | Ffalse: formula
  | Flet: term -> vsymbol -> formula -> formula
  | Fif: formula -> formula -> formula -> formula
  | Fmatch: term -> vty -> list (pattern * formula) -> formula.
Set Elimination Schemes.

(*Default values*)
Definition tm_d : term := Tconst (ConstInt 0).
Definition vs_d : vsymbol := (EmptyString, vty_int).

(*Induction principles*)
Section PatternInd.

Variable P: pattern -> Prop.
Variable Hvar: forall (v: vsymbol),
  P (Pvar v).
Variable Hconstr: forall (f: funsym) (vs: list vty) (ps: list pattern),
  Forall P ps ->
  P (Pconstr f vs ps).
Variable Hwild: P Pwild.
Variable Hor: forall p1 p2, P p1 -> P p2 -> P (Por p1 p2).
Variable Hbind: forall p v,
  P p -> P (Pbind p v).

Fixpoint pattern_ind (p: pattern) : P p :=
  match p with
  | Pvar x => Hvar x
  | Pconstr f tys ps => Hconstr f tys ps
    ((fix all_patterns (l: list pattern) : Forall P l :=
    match l with
    | nil => @Forall_nil _ P
    | x :: t => @Forall_cons _ P _ _ (pattern_ind x) (all_patterns t)
    end) ps)
  | Pwild => Hwild
  | Por p1 p2 => Hor p1 p2 (pattern_ind p1) (pattern_ind p2)
  | Pbind p x  => Hbind p x (pattern_ind p)
  end.

End PatternInd.

(*Version for Type*)
Section PatternRect.

Variable P: pattern -> Type.
Variable Hvar: forall (v: vsymbol),
  P (Pvar v).
Variable Hconstr: forall (f: funsym) (vs: list vty) (ps: list pattern),
  ForallT P ps ->
  P (Pconstr f vs ps).
Variable Hwild: P Pwild.
Variable Hor: forall p1 p2, P p1 -> P p2 -> P (Por p1 p2).
Variable Hbind: forall p v,
  P p -> P (Pbind p v).

Fixpoint pattern_rect (p: pattern) : P p :=
  match p with
  | Pvar x => Hvar x
  | Pconstr f tys ps => Hconstr f tys ps
    ((fix all_patterns (l: list pattern) : ForallT P l :=
    match l with
    | nil => @ForallT_nil _ P
    | x :: t => @ForallT_cons _ P _ _ (pattern_rect x) (all_patterns t)
    end) ps)
  | Pwild => Hwild
  | Por p1 p2 => Hor p1 p2 (pattern_rect p1) (pattern_rect p2)
  | Pbind p x => Hbind p x (pattern_rect p)
  end.

End PatternRect.

(*Induction for terms and formulas*)
Section TermFormInd.

Variable P1: term -> Prop.
Variable P2: formula -> Prop.

Variable tconst: forall c: constant, P1 (Tconst c).
Variable tvar: forall (v: vsymbol),
  P1 (Tvar v).
Variable tfun: forall (f1: funsym) (l: list vty) (l1: list term),
  Forall P1 l1 ->
  P1 (Tfun f1 l l1).
Variable tlet: forall (tm1 : term) (v: vsymbol) (tm2: term),
  P1 tm1 -> P1 tm2 -> P1 (Tlet tm1 v tm2).
Variable tif: forall (f: formula) (t1 t2: term),
  P2 f -> P1 t1 -> P1 t2 -> P1 (Tif f t1 t2).
Variable tmatch: forall (tm: term) (v: vty) (ps: list (pattern * term)),
  P1 tm -> Forall P1 (map snd ps) -> P1 (Tmatch tm v ps).
Variable teps: forall (f: formula) (v: vsymbol),
  P2 f -> P1 (Teps f v).

Variable fpred: forall (p: predsym) (tys: list vty) (tms: list term),
  Forall P1 tms -> P2 (Fpred p tys tms).
Variable fquant: forall (q: quant) (v: vsymbol) (f: formula),
  P2 f -> P2 (Fquant q v f).
Variable feq: forall (v: vty) (t1 t2: term),
  P1 t1 -> P1 t2 -> P2 (Feq v t1 t2).
Variable fbinop: forall (b: binop) (f1 f2: formula),
  P2 f1 -> P2 f2 -> P2 (Fbinop b f1 f2).
Variable fnot: forall (f: formula),
  P2 f -> P2 (Fnot f).
Variable ftrue : P2 Ftrue.
Variable ffalse: P2 Ffalse.
Variable flet: forall (tm: term) (v: vsymbol) (f: formula),
  P1 tm -> P2 f -> P2 (Flet tm v f).
Variable fif: forall (f1 f2 f3: formula),
  P2 f1 -> P2 f2 -> P2 f3 -> P2 (Fif f1 f2 f3).
Variable fmatch: forall (tm: term) (v: vty) (ps: list (pattern * formula)),
  P1 tm ->
  Forall P2 (map snd ps) ->
  P2 (Fmatch tm v ps).

Fixpoint term_ind (tm: term) : P1 tm :=
  match tm with
  | Tconst c => tconst c
  | Tvar v => tvar v
  | Tfun f vs tms => tfun f vs tms 
    ((fix term_list_ind (l: list term) : Forall P1 l :=
    match l with
    | nil => (@Forall_nil _ P1)
    | x :: t => Forall_cons _ _ _ (term_ind x) (term_list_ind t)
    end) tms)
  | Tlet t1 v t2 => tlet t1 v t2 (term_ind t1) (term_ind t2)
  | Tif f t1 t2 => tif f t1 t2 (formula_ind f) (term_ind t1) (term_ind t2)
  | Tmatch tm ty ps => tmatch tm ty ps (term_ind tm)
    ((fix snd_ind (l: list (pattern * term)) : Forall P1 (map snd l) :=
    match l as l' return Forall P1 (map snd l') with
    | nil => (@Forall_nil _ P1)
    | (x, y) :: t => Forall_cons _ _ _ (term_ind y) (snd_ind t)
    end) ps)
  | Teps f v => teps f v (formula_ind f)
  end
with formula_ind (f: formula) : P2 f :=
  match f with
  | Fpred p vs tms => fpred p vs tms
    ((fix term_list_ind (l: list term) : Forall P1 l :=
    match l with
    | nil => (@Forall_nil _ P1)
    | x :: t => Forall_cons _ _ _ (term_ind x) (term_list_ind t)
    end) tms)
  | Fquant q v f => fquant q v f (formula_ind f)
  | Feq ty t1 t2 => feq ty t1 t2 (term_ind t1) (term_ind t2)
  | Fbinop b f1 f2 => fbinop b f1 f2 (formula_ind f1) (formula_ind f2)
  | Fnot f => fnot f (formula_ind f)
  | Ftrue => ftrue
  | Ffalse => ffalse
  | Flet tm v f1 => flet tm v f1 (term_ind tm) (formula_ind f1)
  | Fif f1 f2 f3 => fif f1 f2 f3 (formula_ind f1) (formula_ind f2)
    (formula_ind f3)
  | Fmatch tm ty ps => fmatch tm ty ps (term_ind tm)
    ((fix snd_ind (l: list (pattern * formula)) : Forall P2 (map snd l) :=
    match l as l' return Forall P2 (map snd l') with
    | nil => (@Forall_nil _ P2)
    | (x, y) :: t => Forall_cons _ _ _(formula_ind y) (snd_ind t)
    end) ps)
  end.

(*Also, we can prove things about both, only needing the 
  assumptions once:*)
Definition term_formula_ind: forall (tm: term) (f: formula),
  P1 tm /\ P2 f := fun tm f => (conj (term_ind tm) (formula_ind f)).

End TermFormInd.

(*A way to get out the tm and fmla parts of a theorem*)
Notation proj_tm H t := (proj1 (H t Ftrue)).
Notation proj_fmla H f := (proj2 (H tm_d f)).

(*The _rect version*)
Section TermFormRect.

Variable P1: term -> Type.
Variable P2: formula -> Type.

Variable tconst: forall c: constant, P1 (Tconst c).
Variable tvar: forall (v: vsymbol),
  P1 (Tvar v).
Variable tfun: forall (f1: funsym) (l: list vty) (l1: list term),
  ForallT P1 l1 ->
  P1 (Tfun f1 l l1).
Variable tlet: forall (tm1 : term) (v: vsymbol) (tm2: term),
  P1 tm1 -> P1 tm2 -> P1 (Tlet tm1 v tm2).
Variable tif: forall (f: formula) (t1 t2: term),
  P2 f -> P1 t1 -> P1 t2 -> P1 (Tif f t1 t2).
Variable tmatch: forall (tm: term) (v: vty) (ps: list (pattern * term)),
  P1 tm -> ForallT P1 (map snd ps) -> P1 (Tmatch tm v ps).
Variable teps: forall (f: formula) (v: vsymbol),
  P2 f -> P1 (Teps f v).

Variable fpred: forall (p: predsym) (tys: list vty) (tms: list term),
  ForallT P1 tms -> P2 (Fpred p tys tms).
Variable fquant: forall (q: quant) (v: vsymbol) (f: formula),
  P2 f -> P2 (Fquant q v f).
Variable feq: forall (v: vty) (t1 t2: term),
  P1 t1 -> P1 t2 -> P2 (Feq v t1 t2).
Variable fbinop: forall (b: binop) (f1 f2: formula),
  P2 f1 -> P2 f2 -> P2 (Fbinop b f1 f2).
Variable fnot: forall (f: formula),
  P2 f -> P2 (Fnot f).
Variable ftrue : P2 Ftrue.
Variable ffalse: P2 Ffalse.
Variable flet: forall (tm: term) (v: vsymbol) (f: formula),
  P1 tm -> P2 f -> P2 (Flet tm v f).
Variable fif: forall (f1 f2 f3: formula),
  P2 f1 -> P2 f2 -> P2 f3 -> P2 (Fif f1 f2 f3).
Variable fmatch: forall (tm: term) (v: vty) (ps: list (pattern * formula)),
  P1 tm ->
  ForallT P2 (map snd ps) ->
  P2 (Fmatch tm v ps).

Fixpoint term_rect (tm: term) : P1 tm :=
  match tm with
  | Tconst c => tconst c
  | Tvar v => tvar v
  | Tfun f vs tms => tfun f vs tms 
    ((fix term_list_rect (l: list term) : ForallT P1 l :=
    match l with
    | nil => (@ForallT_nil _ P1)
    | x :: t => ForallT_cons _ (term_rect x) (term_list_rect t)
    end) tms)
  | Tlet t1 v t2 => tlet t1 v t2 (term_rect t1) (term_rect t2)
  | Tif f t1 t2 => tif f t1 t2 (formula_rect f) (term_rect t1) (term_rect t2)
  | Tmatch tm ty ps => tmatch tm ty ps (term_rect tm)
    ((fix snd_rect (l: list (pattern * term)) : ForallT P1 (map snd l) :=
    match l as l' return ForallT P1 (map snd l') with
    | nil => (@ForallT_nil _ P1)
    | (x, y) :: t => ForallT_cons _ (term_rect y) (snd_rect t)
    end) ps)
  | Teps f v => teps f v (formula_rect f)
  end
with formula_rect (f: formula) : P2 f :=
  match f with
  | Fpred p vs tms => fpred p vs tms
    ((fix term_list_rect (l: list term) : ForallT P1 l :=
    match l with
    | nil => (@ForallT_nil _ P1)
    | x :: t => ForallT_cons _ (term_rect x) (term_list_rect t)
    end) tms)
  | Fquant q v f => fquant q v f (formula_rect f)
  | Feq ty t1 t2 => feq ty t1 t2 (term_rect t1) (term_rect t2)
  | Fbinop b f1 f2 => fbinop b f1 f2 (formula_rect f1) (formula_rect f2)
  | Fnot f => fnot f (formula_rect f)
  | Ftrue => ftrue
  | Ffalse => ffalse
  | Flet tm v f1 => flet tm v f1 (term_rect tm) (formula_rect f1)
  | Fif f1 f2 f3 => fif f1 f2 f3 (formula_rect f1) (formula_rect f2)
    (formula_rect f3)
  | Fmatch tm ty ps => fmatch tm ty ps (term_rect tm)
    ((fix snd_rect (l: list (pattern * formula)) : ForallT P2 (map snd l) :=
    match l as l' return ForallT P2 (map snd l') with
    | nil => (@ForallT_nil _ P2)
    | (x, y) :: t => ForallT_cons _ (formula_rect y) (snd_rect t)
    end) ps)
  end.

(*Also, we can prove things about both, only needing the 
  assumptions once:*)
Definition term_formula_rect: forall (tm: term) (f: formula),
  P1 tm * P2 f := fun tm f => ((term_rect tm), (formula_rect f)).

End TermFormRect.

(*We have decidable equality on terms and formulas because
  we use rationals to model real numbers, as why3 does*)
Section EqDec.

Definition binop_eqb (b1 b2: binop) : bool :=
  match b1, b2 with
  | Tand, Tand => true
  | Tor, Tor => true
  | Timplies, Timplies => true
  | Tiff, Tiff => true
  | _, _ => false
  end.

Lemma binop_eqb_spec (b1 b2: binop):
  reflect (b1 = b2) (binop_eqb b1 b2).
Proof.
  destruct (binop_eqb b1 b2) eqn : Hbinop.
  - apply ReflectT.
    destruct b1; destruct b2; simpl in Hbinop; auto; inversion Hbinop.
  - apply ReflectF. intro C; subst.
    destruct b2; inversion Hbinop.
Qed.

Definition binop_eq_dec (b1 b2: binop) :
  {b1 = b2} + {b1 <> b2} := reflect_dec' (binop_eqb_spec b1 b2).

Definition quant_eqb (q1 q2: quant) : bool :=
  match q1, q2 with
  | Tforall, Tforall => true
  | Texists, Texists => true
  | _, _ => false
  end.

Lemma quant_eqb_spec q1 q2:
  reflect (q1 = q2) (quant_eqb q1 q2).
Proof.
  destruct q1; destruct q2; simpl; try refl_t;
  apply ReflectF; intro C; inversion C.
Qed.

Definition quant_eq_dec q1 q2 := reflect_dec' (quant_eqb_spec q1 q2).


(*First, decidable equality on Q - we do not care about
  two rationals being equivalent but not equal (for now)*)
  Definition Q_eq_dec (q1 q2: Q): {q1 = q2} + {q1 <> q2}.
  destruct q1 as [qd1 qp1]. destruct q2 as [qd2 qp2].
  destruct (Z.eq_dec qd1 qd2); subst.
  2: { right; intro C; injection C; intros; subst; auto. }
  destruct (Pos.eq_dec qp1 qp2); subst; auto.
  right; intro C; injection C; intros; subst; auto.
Defined.

Fixpoint pattern_eqb (p1 p2: pattern) : bool :=
  match p1, p2 with
  | Pvar v1, Pvar v2 => vsymbol_eqb v1 v2
  | Pconstr f1 vs1 ps1, Pconstr f2 vs2 ps2 =>
    funsym_eqb f1 f2 && list_eqb vty_eqb vs1 vs2 &&
    (length ps1 =? length ps2) &&
    all2 (fun p1 p2 => pattern_eqb p1 p2) ps1 ps2
  | Pwild, Pwild => true
  | Por pa1 pa2, Por pb1 pb2 => pattern_eqb pa1 pb1 &&
    pattern_eqb pa2 pb2
  | Pbind p1 v1, Pbind p2 v2 => pattern_eqb p1 p2 &&
    vsymbol_eqb v1 v2
  | _, _ => false
  end.

Lemma pattern_eqb_spec (p1 p2: pattern) :
  reflect (p1 = p2) (pattern_eqb p1 p2).
Proof.
  revert p1 p2. 
  apply (pattern_rect (fun p => forall p2,
    reflect (p = p2) (pattern_eqb p p2))); intros; simpl.
  - destruct_triv p2.
    dec (vsymbol_eqb_spec v v0). refl_t.
  - destruct_triv p2. dec (funsym_eqb_spec f f0).
    dec (list_eqb_spec vty_eqb vty_eq_spec vs l).
    dec (Nat.eqb_spec (length ps) (length l0)).
    subst.
    assert (all2 (fun p1 p2 : pattern => pattern_eqb p1 p2) ps l0 <->
    ps = l0). {
      generalize dependent ps. induction l0; intros; simpl.
      - destruct ps; inversion e1; simpl.
        split; auto.
      - destruct ps; inversion e1; simpl.
        rewrite all2_cons. inversion H; subst.
        destruct (H3 a); subst; simpl; auto.
        2: {split; auto; intros C; inversion C; subst; auto. }
        rewrite IHl0; auto. split; intros; subst; auto.
        inversion H0; subst; auto.
    }
    destruct (all2 (fun p1 p2 : pattern => pattern_eqb p1 p2) ps l0).
    + apply ReflectT. f_equal. apply H0; auto.
    + apply ReflectF. intro C; inversion C; subst; auto.
      assert (false) by (apply H0; auto). inversion H1.
  - destruct_triv p2. refl_t.
  - destruct_triv p0.
    dec (H p0_1); subst; simpl.
    dec (H0 p0_2); subst; simpl.
    refl_t.
  - destruct_triv p2.
    dec (H p2). dec (vsymbol_eqb_spec v v0). subst.
    refl_t.
Qed.

Definition pattern_eq_dec (p1 p2: pattern) : {p1 = p2} + {p1 <> p2} :=
  reflect_dec' (pattern_eqb_spec p1 p2).

Definition const_eqb (c1 c2: constant) :=
  match c1, c2 with
  | ConstInt z1, ConstInt z2 =>
    Z.eqb z1 z2
  | ConstReal q1, ConstReal q2 =>
    Q_eq_dec q1 q2 (*NOTE: this fails if we use Coq classical reals*)
  | _, _ => false
  end.

Lemma const_eqb_spec: forall c1 c2,
  reflect (c1 = c2) (const_eqb c1 c2).
Proof.
  intros [z1 | r1] [z2 | r2]; simpl; try
  (apply ReflectF; intro C; inversion C).
  - dec (Z.eqb_spec z1 z2).
    apply ReflectT. subst; auto.
  - dec (Q_eq_dec r1 r2).
    apply ReflectT. subst; auto.
Qed.

Definition const_eq_dec (c1 c2: constant) : {c1 = c2} + {c1 <> c2} :=
  reflect_dec' (const_eqb_spec c1 c2).

Fixpoint term_eqb (t1 t2: term) {struct t1} : bool :=
  match t1, t2 with
  | Tconst c1, Tconst c2 => const_eqb c1 c2
  | Tvar v1, Tvar v2 => vsymbol_eqb v1 v2
  | Tfun f1 tys1 tms1, Tfun f2 tys2 tms2 =>
    funsym_eqb f1 f2 &&
    list_eqb vty_eqb tys1 tys2 &&
    (length tms1 =? length tms2) &&
    all2 (fun t1 t2 => term_eqb t1 t2) tms1 tms2
  | Tlet ta1 v1 ta2, Tlet tb1 v2 tb2 =>
    term_eqb ta1 tb1 &&
    vsymbol_eqb v1 v2 &&
    term_eqb ta2 tb2
  | Tif f1 ta1 ta2, Tif f2 tb1 tb2 =>
    formula_eqb f1 f2 &&
    term_eqb ta1 tb1 &&
    term_eqb ta2 tb2
  | Tmatch t1 v1 ps1, Tmatch t2 v2 ps2 =>
    term_eqb t1 t2 &&
    vty_eqb v1 v2 &&
    (length ps1 =? length ps2) &&
    all2 (fun x y => pattern_eqb (fst x) (fst y) &&
      term_eqb (snd x) (snd y)) ps1 ps2
  | Teps f1 v1, Teps f2 v2 =>
    formula_eqb f1 f2 &&
    vsymbol_eqb v1 v2
  | _, _ => false
  end
with formula_eqb (f1 f2: formula) {struct f1} : bool :=
  match f1, f2 with
  | Fpred p1 tys1 tms1, Fpred p2 tys2 tms2 =>
    predsym_eqb p1 p2 &&
    list_eqb vty_eqb tys1 tys2 &&
    (length tms1 =? length tms2) &&
    all2 (fun t1 t2 => term_eqb t1 t2) tms1 tms2
  | Fquant q1 v1 f1, Fquant q2 v2 f2 =>
    quant_eqb q1 q2 &&
    vsymbol_eqb v1 v2 &&
    formula_eqb f1 f2
  | Feq ty1 ta1 ta2, Feq ty2 tb1 tb2 =>
    vty_eqb ty1 ty2 &&
    term_eqb ta1 tb1 &&
    term_eqb ta2 tb2
  | Fbinop b1 fa1 fa2, Fbinop b2 fb1 fb2 =>
    binop_eqb b1 b2 &&
    formula_eqb fa1 fb1 &&
    formula_eqb fa2 fb2
  | Fnot f1, Fnot f2 =>
    formula_eqb f1 f2
  | Ftrue, Ftrue => true
  | Ffalse, Ffalse => true
  | Flet t1 v1 f1, Flet t2 v2 f2 =>
    term_eqb t1 t2 &&
    vsymbol_eqb v1 v2 &&
    formula_eqb f1 f2
  | Fif fa1 fa2 fa3, Fif fb1 fb2 fb3 =>
    formula_eqb fa1 fb1 &&
    formula_eqb fa2 fb2 &&
    formula_eqb fa3 fb3
  | Fmatch t1 v1 ps1, Fmatch t2 v2 ps2 =>
    term_eqb t1 t2 &&
    vty_eqb v1 v2 &&
    (length ps1 =? length ps2) &&
    all2 (fun x y => pattern_eqb (fst x) (fst y) &&
      formula_eqb (snd x) (snd y)) ps1 ps2
  | _, _ => false
  end.

Lemma term_fmla_eqb_spec (t1: term) (f1: formula) :
  (forall (t2: term),
    reflect (t1 = t2) (term_eqb t1 t2)) *
  (forall (f2: formula),
    reflect (f1 = f2) (formula_eqb f1 f2)).
Proof.
  revert t1 f1; apply term_formula_rect; intros; simpl.
  - destruct_triv t2.
    dec (const_eqb_spec c c0).
    subst. apply ReflectT; auto.
  - destruct_triv t2. dec (vsymbol_eqb_spec v v0). refl_t.
  - destruct_triv t2. 
    dec (funsym_eqb_spec f1 f).
    dec (list_eqb_spec _ vty_eq_spec l l0).
    dec (Nat.eqb_spec (length l1) (length l2)).
    subst.
    assert ((all2 (fun t1 t2 : term => term_eqb t1 t2) l1 l2) <-> l1 = l2). {
      generalize dependent l2. induction l1; simpl; intros; destruct l2;
      inversion e1; auto. split; auto.
      rewrite all2_cons. inversion H; subst.
      destruct (H3 t); subst; simpl; [| split; intros C; inversion C; subst; auto]. 
      rewrite IHl1; auto. split; intros C; inversion C; auto.
    }
    destruct (all2 (fun t1 t2 : term => term_eqb t1 t2) l1 l2).
    + apply ReflectT. f_equal. apply H0; auto.
    + apply ReflectF. intro C; inversion C; subst.
      assert (false) by (apply H0; auto). inversion H1.
  - destruct_triv t2.
    dec (H t2_1).
    dec (vsymbol_eqb_spec v v0).
    dec (H0 t2_2). refl_t.
  - destruct_triv t0.
    dec (H f0).
    dec (H0 t0_1).
    dec (H1 t0_2).
    refl_t.
  - destruct_triv t2.
    dec (H t2). dec (vty_eq_spec v v0).
    dec (Nat.eqb_spec (length ps) (length l)). subst.
    assert ((all2
    (fun x y : pattern * term =>
     pattern_eqb (fst x) (fst y) && term_eqb (snd x) (snd y)) ps l) <-> ps = l).
    {
      generalize dependent l. induction ps; simpl; intros; destruct l;
      inversion e1; try solve [split; auto].
      rewrite all2_cons. destruct (pattern_eqb_spec (fst a) (fst p)).
      2: { simpl; split; intro C; inversion C; subst; auto. }
      inversion H0; subst.
      destruct (H4 (snd p)).
      2: { simpl; split; intro C; inversion C; subst; auto. }
      simpl. destruct a; destruct p; simpl in *; subst.
      rewrite IHps; auto. split; intros C; inversion C; subst; auto.
    }
    destruct (all2
    (fun x y : pattern * term =>
     pattern_eqb (fst x) (fst y) && term_eqb (snd x) (snd y)) ps l).
    + apply ReflectT. f_equal. apply H1; auto.
    + apply ReflectF. intros C; inversion C; subst; auto.
      assert (false) by (apply H1; auto). inversion H2.
  - destruct_triv t2.
    dec (H f0).
    dec (vsymbol_eqb_spec v v0). refl_t.
  - destruct_triv f2.
    dec (predsym_eqb_spec p p0).
    dec (list_eqb_spec _ vty_eq_spec tys l).
    dec (Nat.eqb_spec (length tms) (length l0)).
    subst.
    (*could generalize this - maybe write list_eqb with all2*)
    assert ((all2 (fun t1 t2 : term => term_eqb t1 t2) tms l0) <-> tms = l0). {
      generalize dependent l0. induction tms; simpl; intros; destruct l0;
      inversion e1; auto. split; auto.
      rewrite all2_cons. inversion H; subst.
      destruct (H3 t); subst; simpl; [| split; intros C; inversion C; subst; auto]. 
      rewrite IHtms; auto. split; intros C; inversion C; auto.
    }
    destruct (all2 (fun t1 t2 : term => term_eqb t1 t2) tms l0).
    + apply ReflectT. f_equal. apply H0; auto.
    + apply ReflectF. intro C; inversion C; subst.
      assert (false) by (apply H0; auto). inversion H1.
  - destruct_triv f2.
    dec (quant_eqb_spec q q0).
    dec (vsymbol_eqb_spec v v0).
    dec (H f2). refl_t.
  - destruct_triv f2.
    dec (vty_eq_spec v v0).
    dec (H t). dec (H0 t0). refl_t.
  - destruct_triv f0.
    dec (binop_eqb_spec b b0).
    dec (H f0_1). dec (H0 f0_2).
    refl_t.
  - destruct_triv f2.
    dec (H f2). refl_t.
  - destruct_triv f2. refl_t.
  - destruct_triv f2. refl_t.
  - destruct_triv f2.
    dec (H t). dec (vsymbol_eqb_spec v v0).
    dec (H0 f2). refl_t.
  - destruct_triv f0.
    dec (H f0_1). dec (H0 f0_2). dec (H1 f0_3). refl_t.
  - destruct_triv f2.
    dec (H t). dec (vty_eq_spec v v0).
    dec (Nat.eqb_spec (length ps) (length l)). subst.
    assert ((all2
    (fun x y : pattern * formula =>
     pattern_eqb (fst x) (fst y) && formula_eqb (snd x) (snd y)) ps l) <-> ps = l).
    {
      generalize dependent l. induction ps; simpl; intros; destruct l;
      inversion e1; try solve [split; auto].
      rewrite all2_cons. destruct (pattern_eqb_spec (fst a) (fst p)).
      2: { simpl; split; intro C; inversion C; subst; auto. }
      inversion H0; subst.
      destruct (H4 (snd p)).
      2: { simpl; split; intro C; inversion C; subst; auto. }
      simpl. destruct a; destruct p; simpl in *; subst.
      rewrite IHps; auto. split; intros C; inversion C; subst; auto.
    }
    destruct (all2
    (fun x y : pattern * formula =>
     pattern_eqb (fst x) (fst y) && formula_eqb (snd x) (snd y)) ps l).
    + apply ReflectT. f_equal. apply H1; auto.
    + apply ReflectF. intros C; inversion C; subst; auto.
      assert (false) by (apply H1; auto). inversion H2.
Qed.

Definition term_eqb_spec t := fst (term_fmla_eqb_spec t Ftrue).
Definition formula_eqb_spec f := snd (term_fmla_eqb_spec tm_d f).

Definition term_eq_dec (t1 t2: term) := reflect_dec' (term_eqb_spec t1 t2).
Definition formula_eq_dec (f1 f2: formula) := reflect_dec' (formula_eqb_spec f1 f2).

End EqDec.

(*Definitions: functions, predicates, algebraic data types, inductive predicates*)

Inductive alg_datatype : Set :=
  | alg_def: typesym -> ne_list funsym -> alg_datatype.

Inductive funpred_def : Set :=
  | fun_def: funsym -> list vsymbol -> term -> funpred_def
  | pred_def: predsym -> list vsymbol -> formula -> funpred_def.

Inductive indpred_def : Set :=
  | ind_def: predsym -> list (string * formula) -> indpred_def.

Record mut_adt := mk_mut {typs : list alg_datatype;
                          m_params: list typevar;
                          m_nodup: nodupb typevar_eq_dec m_params }.

(*NOTE: we require that every mutually recursive type has the same
  type variable parameters. That simplifies some of the proofs.*)

(*Our definitions can be abstract or concrete*)
Inductive def : Set :=
  (*concrete defs*)
  | datatype_def : mut_adt -> def
  | recursive_def: list funpred_def -> def
  | inductive_def : list indpred_def -> def
  | nonrec_def : funpred_def -> def (*non-recursive function or predicate def*)
  (*abstract defs*)
  | abs_type : typesym -> def
  | abs_fun : funsym -> def
  | abs_pred : predsym -> def.

(*These definitions can be unwieldy, so we provide nicer functions*)

Definition adt_name (a: alg_datatype) : typesym :=
  match a with
  | alg_def t _ => t
  end.

Definition adt_constrs (a: alg_datatype) : ne_list funsym :=
  match a with
  | alg_def _ c => c
  end.

Definition adt_constr_list (a: alg_datatype) : list funsym :=
  ne_list_to_list (adt_constrs a).

Definition typesyms_of_mut (m: mut_adt) : list typesym :=
  map adt_name (typs m).

Definition funsyms_of_mut (m: mut_adt) : list funsym :=
  (concat (map adt_constr_list (typs m))).

Definition predsyms_of_indprop (l: list indpred_def) : list predsym :=
  map (fun x => match x with | ind_def p _ => p end) l.

Definition funsyms_of_nonrec (f: funpred_def) : list funsym :=
  match f with
  | fun_def fs _ _ => [fs]
  | _ => nil
  end.

Definition predsyms_of_nonrec (f: funpred_def) : list predsym :=
  match f with
  | pred_def ps _ _ => [ps]
  | _ => nil
  end.
  
Definition funsyms_of_rec (l: list funpred_def) : list funsym :=
  omap (fun f =>
    match f with
    | fun_def fs _ _ => Some fs
    | _ => None
    end) l.

Definition predsyms_of_rec (l: list funpred_def) : list predsym :=
  omap (fun f =>
    match f with
    | pred_def ps _ _ => Some ps
    | _ => None
    end) l.

Definition funsyms_of_def (d: def) : list funsym :=
  match d with
  | datatype_def m => funsyms_of_mut m
  | recursive_def fs => funsyms_of_rec fs
  | abs_fun f => [f]
  | nonrec_def f => funsyms_of_nonrec f
  | _ => nil
  end.

Definition predsyms_of_def (d: def) : list predsym :=
  match d with
  | inductive_def l => predsyms_of_indprop l
  | recursive_def fs => predsyms_of_rec fs
  | abs_pred p => [p]
  | nonrec_def p => predsyms_of_nonrec p
  | _ => nil
  end.

Definition typesyms_of_def (d: def) : list typesym :=
  match d with
  | datatype_def m => typesyms_of_mut m
  | abs_type t => [t]
  | _ => nil
  end.

(*Concrete only fun/pred syms*)

Definition def_concrete_funsyms (d: def) : list funsym :=
  match d with
  | datatype_def m => funsyms_of_mut m
  | recursive_def l => funsyms_of_rec l
  | nonrec_def f => funsyms_of_nonrec f
  | _ => nil
  end.

Definition def_concrete_predsyms (d: def) : list predsym :=
  match d with
  | inductive_def l => predsyms_of_indprop l
  | recursive_def l => predsyms_of_rec l
  | nonrec_def f => predsyms_of_nonrec f
  | _ => nil
  end.

Lemma concrete_in_def_funsym: forall x d,
  In x (def_concrete_funsyms d) ->
  In x (funsyms_of_def d).
Proof.
  unfold def_concrete_funsyms, funsyms_of_def.
  intros. destruct d; auto. destruct H.
Qed.

Lemma concrete_in_def_predsym: forall x d,
  In x (def_concrete_predsyms d) ->
  In x (predsyms_of_def d).
Proof.
  unfold def_concrete_predsyms, predsyms_of_def.
  intros. destruct d; auto. destruct H.
Qed.

(*Decidable equality*)
Local Ltac reflF := solve[apply ReflectF; intro C; inversion C; subst; auto; contradiction].

Definition adt_eqb (a1 a2: alg_datatype) : bool :=
  typesym_eqb (adt_name a1) (adt_name a2) &&
  list_eqb funsym_eqb (adt_constr_list a1) (adt_constr_list a2).

Lemma adt_eqb_spec a1 a2: reflect (a1 = a2) (adt_eqb a1 a2).
Proof.
  unfold adt_eqb.
  destruct a1 as [t1 c1]; destruct a2 as [t2 c2]; simpl.
  destruct (typesym_eqb_spec t1 t2); subst; [|reflF].
  destruct (list_eqb_spec _ funsym_eqb_spec 
    (adt_constr_list (alg_def t2 c1)) (adt_constr_list (alg_def t2 c2))) as [Hl |];
  [apply ReflectT | reflF].
  apply ne_list_list_inj in Hl; simpl in Hl; subst; reflexivity.
Qed.

Definition adt_dec (a1 a2: alg_datatype) : {a1 = a2} + {a1 <> a2} :=
  reflect_dec' (adt_eqb_spec a1 a2).

Definition mut_adt_eqb (m1 m2: mut_adt) : bool :=
  (list_eqb adt_eqb (typs m1) (typs m2)) &&
  (list_eqb typevar_eqb (m_params m1) (m_params m2)).

Lemma mut_adt_eqb_spec (m1 m2: mut_adt) :
  reflect (m1 = m2) (mut_adt_eqb m1 m2).
Proof.
  destruct m1 as [t1 p1 n1]; destruct m2 as [t2 p2 n2];
  unfold mut_adt_eqb; simpl.
  destruct (list_eqb_spec _ adt_eqb_spec t1 t2); subst; [|reflF].
  destruct (list_eqb_spec _ typevar_eqb_spec p1 p2); subst; [|reflF].
  apply ReflectT. f_equal. apply bool_irrelevance.
Qed.

Definition mut_adt_dec (m1 m2: mut_adt): {m1 = m2} + {m1 <> m2} :=
  reflect_dec' (mut_adt_eqb_spec m1 m2).

Definition funpred_def_eqb (f1 f2: funpred_def) : bool :=
  match f1, f2 with
  | fun_def f1 v1 t1, fun_def f2 v2 t2 =>
    funsym_eqb f1 f2 &&
    list_eqb vsymbol_eqb v1 v2 &&
    term_eqb t1 t2
  | pred_def p1 v1 f1, pred_def p2 v2 f2 =>
    predsym_eqb p1 p2 &&
    list_eqb vsymbol_eqb v1 v2 &&
    formula_eqb f1 f2
  | _, _ => false
  end.

Lemma funpred_def_eqb_spec (f1 f2: funpred_def) :
  reflect (f1 = f2) (funpred_def_eqb f1 f2).
Proof.
  destruct f1; destruct_triv f2; simpl.
  - dec (funsym_eqb_spec f f0).
    dec (list_eqb_spec _ vsymbol_eqb_spec l l0).
    dec (term_eqb_spec t t0).
    refl_t.
  - dec (predsym_eqb_spec p p0).
    dec (list_eqb_spec _ vsymbol_eqb_spec l l0).
    dec (formula_eqb_spec f f0).
    refl_t.
Qed.

Definition funpred_def_eq_dec (f1 f2: funpred_def) :
  {f1 = f2} + {f1 <> f2} := reflect_dec' (funpred_def_eqb_spec f1 f2).

Definition indpred_def_eqb (f1 f2: indpred_def) : bool :=
  match f1, f2 with
  | ind_def p1 f1, ind_def p2 f2 =>
    predsym_eqb p1 p2 &&
    list_eqb (tuple_eqb String.eqb formula_eqb) f1 f2
  end.

Lemma indpred_def_eqb_spec f1 f2:
  reflect (f1 = f2) (indpred_def_eqb f1 f2).
Proof.
  destruct f1; destruct_triv f2; simpl.
  dec (predsym_eqb_spec p p0).
  dec (list_eqb_spec (tuple_eqb String.eqb formula_eqb) 
    (tuple_eqb_spec String.eqb_spec formula_eqb_spec) l l0).
  subst. apply ReflectT. reflexivity.
Qed.

Definition indpred_def_eq_dec (f1 f2: indpred_def) :
  {f1 = f2} + {f1 <> f2} := reflect_dec' (indpred_def_eqb_spec f1 f2).

Definition def_eqb (d1 d2: def) : bool :=
  match d1, d2 with
  | datatype_def m1, datatype_def m2 => mut_adt_dec m1 m2
  | recursive_def l1, recursive_def l2 =>
    list_eqb funpred_def_eqb l1 l2
  | inductive_def l1, inductive_def l2 =>
    list_eqb indpred_def_eqb l1 l2
  | nonrec_def f1, nonrec_def f2 => funpred_def_eqb f1 f2
  | abs_type t1, abs_type t2 => typesym_eqb t1 t2
  | abs_fun f1, abs_fun f2 => funsym_eqb f1 f2
  | abs_pred p1, abs_pred p2 => predsym_eqb p1 p2
  | _, _ => false
  end.

Ltac by_dec H := dec H; subst; apply ReflectT; reflexivity.

Lemma def_eqb_spec (d1 d2: def):
  reflect (d1 = d2) (def_eqb d1 d2).
Proof.
  unfold def_eqb.
  destruct d1; destruct d2; try solve[apply ReflectF; intro C; inversion C].
  - by_dec (mut_adt_dec m m0).
  - by_dec (list_eqb_spec _ funpred_def_eqb_spec l l0).
  - by_dec (list_eqb_spec _ indpred_def_eqb_spec l l0). 
  - by_dec (funpred_def_eqb_spec f f0). 
  - by_dec (typesym_eqb_spec t t0).
  - by_dec (funsym_eqb_spec f f0). 
  - by_dec (predsym_eqb_spec p p0).
Qed.
  
Definition def_eq_dec (d1 d2: def) : {d1 = d2} + {d1 <> d2} :=
  reflect_dec' (def_eqb_spec d1 d2).

(*And countable instances*)

(*ne_list*)
(*TODO: move?*)
Section NEListCount.
Context {A: Set} `{A_count: countable.Countable A}.

#[global] Instance ne_list_EqDecision: @base.RelDecision (ne_list A) (ne_list A) eq.
Proof. unfold base.RelDecision. apply ne_list_eq_dec. apply EqDecision0. Defined.

(*Injection to list*)

Definition list_to_ne_list' (l: list A): option (ne_list A) :=
  match negb (null l) as b return negb (null l) = b -> _ with
  | true => fun Hn => Some (list_to_ne_list l Hn)
  | _ => fun _ => None
  end eq_refl.

Lemma list_to_ne_list_inj' l:
  list_to_ne_list' (ne_list_to_list l) = Some l.
Proof.
  unfold list_to_ne_list'.
  generalize dependent (@eq_refl bool (negb (null (ne_list_to_list l)))).
  (*Need a property of [list_to_ne_list] before we generalize*)
  pose proof (@ne_list_list_inv A l) as Hinv.
  generalize dependent (ne_list_to_list_size l).
  generalize dependent (@list_to_ne_list A (ne_list_to_list l)).
  (*Finally, can destruct*)
  destruct (negb (null (ne_list_to_list l))); simpl; [|discriminate].
  intros. subst. f_equal. f_equal. apply bool_irrelevance.
Qed.

#[global]Instance ne_list_Countable : countable.Countable (ne_list A) :=
  countable.inj_countable ne_list_to_list list_to_ne_list' list_to_ne_list_inj'.

End NEListCount.



(*ADT*)
Definition adt_to_tup (a: alg_datatype) : typesym * ne_list funsym :=
  (adt_name a, adt_constrs a).
Definition tup_to_adt (x: typesym * ne_list funsym) : alg_datatype :=
  alg_def (fst x) (snd x).
Lemma adt_to_tup_inj a: tup_to_adt (adt_to_tup a) = a.
Proof.
destruct a; auto.
Qed.

Instance alg_datatype_EqDecision: @base.RelDecision alg_datatype alg_datatype eq.
Proof. unfold base.RelDecision. apply adt_dec. Defined.

Instance alg_datatype_Countable : countable.Countable alg_datatype :=
  countable.inj_countable' adt_to_tup tup_to_adt adt_to_tup_inj.

(*mut adt*)

Definition mut_to_tup (m: mut_adt) : list alg_datatype * list typevar :=
  (typs m, m_params m).
Definition tup_to_mut (x: list alg_datatype * list typevar) : option mut_adt :=
  let t := fst x in
  let p := snd x in
  match (nodupb typevar_eq_dec p) as b return (nodupb typevar_eq_dec p) = b -> _ with
  | true => fun m_nodup => Some (mk_mut t p m_nodup)
  | false => fun _ => None
  end eq_refl.

Lemma mut_to_tup_inj: forall x,
  tup_to_mut (mut_to_tup x) = Some x.
Proof.
  intros [t p p_nodup].
  unfold mut_to_tup, tup_to_mut. simpl.
  generalize dependent (@eq_refl bool (nodupb typevar_eq_dec p)).
  generalize dependent ((mk_mut t p)).
  rewrite p_nodup. intros; subst; auto.
  f_equal; f_equal; apply bool_irrelevance.
Qed.

Instance mut_adt_EqDecision : @base.RelDecision mut_adt mut_adt eq.
Proof. unfold base.RelDecision. apply mut_adt_dec. Defined.

Instance mut_adt_Countable : countable.Countable mut_adt :=
  countable.inj_countable mut_to_tup tup_to_mut mut_to_tup_inj.


(*In many cases, it is inconvenient to use terms and formulas
  separately. With a bit of dependent typing, we can generalize.
  This will be very useful, particularly for pattern-matching:*)
Definition gen_sym (b: bool) : Set := if b then funsym else predsym.
Definition gen_term (b: bool) := if b then term else formula.
Definition gen_type (b: bool) := if b then vty else unit.

Definition gen_term_eq_dec {b: bool} (x y: gen_term b) : {x = y} + {x <> y} :=
  match b return forall (x y: gen_term b), {x = y} + {x <> y} with
  | true => term_eq_dec
  | false => formula_eq_dec
  end x y.

Definition gen_match {b: bool} (t: term) (ty: vty) (l: list (pattern * gen_term b)) : gen_term b :=
  match b return list (pattern * gen_term b) -> gen_term b with
  | true => fun pats => Tmatch t ty pats
  | false => fun pats => Fmatch t ty pats
  end l.
Definition gen_let {b: bool} (v: vsymbol) (t: term) (g: gen_term b) : gen_term b :=
  match b return gen_term b -> gen_term b with
  | true => fun t2 => Tlet t v t2
  | false => fun f => Flet t v f
  end g.

Definition gen_d (b: bool) : gen_term b :=
  match b return gen_term b with
  | true => tm_d
  | false => Ftrue
  end.

Definition gen_fun {b: bool} (s: gen_sym b) (tys: list vty) (tms: list term) : gen_term b :=
  match b return gen_sym b -> gen_term b with
  | true => fun f => Tfun f tys tms
  | false => fun p => Fpred p tys tms
  end s.

Definition gen_if {b: bool} (f: formula) (t1 t2: gen_term b) : gen_term b :=
  match b return gen_term b -> gen_term b -> gen_term b with
  | true => fun t1 t2 => Tif f t1 t2
  | false => fun f1 f2 => Fif f f1 f2
  end t1 t2.

(*More for [gen_sym]*)

Definition gen_fpsym {b: bool} (ls: gen_sym b) : fpsym :=
  match b return gen_sym b -> fpsym with
  | true => f_sym
  | false =>p_sym
  end ls.

Definition gen_sym_name {b: bool} (f: gen_sym b) : string :=
  match b return gen_sym b -> string with
  | true => fun f => s_name f
  | false => fun f => s_name f
  end f.

Definition gen_sym_params {b: bool} (f: gen_sym b) : list typevar :=
  match b return gen_sym b -> list typevar with
  | true => s_params
  | false => s_params
  end f.

Definition gen_sym_args {b: bool} (f: gen_sym b) : list vty :=
  match b return gen_sym b -> list vty with
  | true => s_args
  | false => s_args
  end f.

Definition gen_sym_ret {b: bool} (f: gen_sym b) : gen_type b :=
  match b return gen_sym b -> gen_type b with
  | true => f_ret
  | false => fun _ => tt
  end f.

Lemma typevars_in_params (s: fpsym) i:
(i < length (s_args s))%nat ->
forall v : typevar,
aset_mem v (type_vars (nth i (s_args s) vty_int)) -> In v (s_params s).
Proof.
  intros. destruct s; simpl in *.
  assert (Hwf:=s_args_wf0).
  apply check_args_prop with(x:=List.nth i s_args0 vty_int) in Hwf; auto; [|apply nth_In; auto].
  rewrite asubset_def in Hwf. apply Hwf in H0.
  simpl_set. auto.
Qed.

Lemma gen_typevars_in_params {x v b} (ls: gen_sym b)
  (Hinx: In x (gen_sym_args ls))
  (Hinv: aset_mem v (type_vars x)):
  In v (gen_sym_params ls).
Proof.
  destruct (In_nth _ _ vty_int Hinx) as [i [Hi Hx]]; subst.
  destruct b; simpl in *; apply (typevars_in_params _ _ Hi _ Hinv).
Qed.

(*Generalize [funpred_def]*)

Definition gen_funpred_def (b: bool) (f: gen_sym b) (l: list vsymbol) (t: gen_term b) : funpred_def :=
  match b return gen_sym b -> gen_term b -> funpred_def with
  | true => fun ls t => fun_def ls l t
  | false => fun ls f => pred_def ls l f
  end f t.

Definition gen_funpred_def_match (x: funpred_def) : {b: bool & (gen_sym b * list vsymbol * gen_term b)%type} :=
  match x with
  | fun_def ls vs t => existT true (ls, vs, t)
  | pred_def ls vs f => existT false (ls, vs, f)
  end.

Lemma gen_funpred_def_match_eq (x: funpred_def) b ls vs tms:
  gen_funpred_def_match x = existT b (ls, vs, tms) <-> gen_funpred_def b ls vs tms = x.
Proof.
  unfold gen_funpred_def_match, gen_funpred_def. destruct x; simpl.
  - split; intros Hex; [|destruct b]; inversion Hex; subst; auto.
    apply inj_pair2_eq_dec in Hex; [inversion Hex; subst; auto | apply Bool.bool_dec].
  - split; intros Hex; [|destruct b]; inversion Hex; subst; auto.
    apply inj_pair2_eq_dec in Hex; [inversion Hex; subst; auto | apply Bool.bool_dec].
Qed.

Definition gen_abs {b: bool} (f: gen_sym b) : def :=
  match b return gen_sym b -> def with
  | true => abs_fun
  | false => abs_pred
  end f.