Require Import Coq.QArith.QArith_base.
Require Export Types.
Set Bullet Behavior "Strict Subproofs".

(** Function and Predicate Symbols **)

(*We use bools rather than props so that we get decidable equality (like ssreflect)*)

(*Check for sublist (to enable building these structures)*)
Definition check_sublist (l1 l2: list typevar) : bool :=
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
Qed.

Definition check_args (params: list typevar) (args: list vty) : bool :=
  forallb (fun x => check_sublist (type_vars x) params) args.

(*Would be easier with ssreflect*)
Lemma check_args_correct: forall params args,
  reflect (forall x, In x args -> sublist (type_vars x) params) (check_args params args).
Proof.
  intros. destruct (check_args params args) eqn : Hargs.
  - unfold check_args in Hargs. rewrite forallb_forall in Hargs.
    apply ReflectT. intros. apply Hargs in H.
    apply (reflect_iff _  _ (check_sublist_correct (type_vars x) params)) in H. auto.
  - apply ReflectF. intro C.
    assert (check_args params args = true). {
      apply forallb_forall. intros. apply C in H.
      apply (reflect_iff _ _ (check_sublist_correct (type_vars x) params)). auto.
    }
    rewrite H in Hargs; inversion Hargs.
Qed.

(*Easy corollaries, need these for arguments to other functions which don't know
  about the decidable versions*)

Lemma check_args_prop {params args} :
  check_args params args -> forall x, In x args -> sublist (type_vars x) params.
Proof.
  intros Hcheck. apply (reflect_iff _ _ (check_args_correct params args)).
  apply Hcheck.
Qed.

Lemma check_sublist_prop {l1 l2}:
  check_sublist l1 l2 ->
  sublist l1 l2.
Proof.
  intros. apply (reflect_iff _ _ (check_sublist_correct l1 l2)), H.
Qed.

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
    f_ret_wf : check_sublist (type_vars f_ret) 
      (s_params f_sym) }.

Coercion f_sym : funsym >-> fpsym.

Record predsym: Set :=
    { p_sym : fpsym }.

Coercion p_sym : predsym >-> fpsym.

(*Record funsym : Set :=
  {
    s_name : string;
    s_params : list typevar;
    s_args: list vty;
    s_ret: vty;
    
    s_ret_wf: check_sublist (type_vars s_ret) s_params;
    s_args_wf: check_args s_params s_args;
    s_params_nodup: nodupb typevar_eq_dec s_params
  }.

Record predsym : Set :=
  {
    p_name: string;
    p_params: list typevar;
    p_args : list vty;
    p_args_wf: check_args p_params p_args;
    p_params_nodup: nodupb typevar_eq_dec p_params
  }.*)

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

Definition id_fs : funsym := Build_funsym id_sym id_ret eq_refl.

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
  f1 = f2.
Proof.
  intros. destruct f1; destruct f2; simpl in *; subst.
  f_equal; apply bool_irrelevance.
Qed.

Definition funsym_eqb (f1 f2: funsym) : bool :=
  (fpsym_eqb (f_sym f1) (f_sym f2)) &&
  (vty_eqb (f_ret f1) (f_ret f2)).

Lemma funsym_eqb_spec: forall (f1 f2: funsym),
  reflect (f1 = f2) (funsym_eqb f1 f2).
Proof.
  intros. unfold funsym_eqb.
  dec (fpsym_eqb_spec (f_sym f1) (f_sym f2)).
  dec (vty_eq_spec (f_ret f1) (f_ret f2)).
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
    | x :: t => Forall_cons _ (term_ind x) (term_list_ind t)
    end) tms)
  | Tlet t1 v t2 => tlet t1 v t2 (term_ind t1) (term_ind t2)
  | Tif f t1 t2 => tif f t1 t2 (formula_ind f) (term_ind t1) (term_ind t2)
  | Tmatch tm ty ps => tmatch tm ty ps (term_ind tm)
    ((fix snd_ind (l: list (pattern * term)) : Forall P1 (map snd l) :=
    match l as l' return Forall P1 (map snd l') with
    | nil => (@Forall_nil _ P1)
    | (x, y) :: t => Forall_cons _ (term_ind y) (snd_ind t)
    end) ps)
  | Teps f v => teps f v (formula_ind f)
  end
with formula_ind (f: formula) : P2 f :=
  match f with
  | Fpred p vs tms => fpred p vs tms
    ((fix term_list_ind (l: list term) : Forall P1 l :=
    match l with
    | nil => (@Forall_nil _ P1)
    | x :: t => Forall_cons _ (term_ind x) (term_list_ind t)
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
    | (x, y) :: t => Forall_cons _ (formula_ind y) (snd_ind t)
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


Fixpoint term_eqb (t1 t2: term) {struct t1} : bool :=
  match t1, t2 with
  | Tconst (ConstInt z1), Tconst (ConstInt z2) =>
    Z.eqb z1 z2
  | Tconst (ConstReal q1), Tconst (ConstReal q2) =>
    Q_eq_dec q1 q2 (*TODO: this fails if we use Coq classical reals*)
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
  - destruct t2; destruct_triv c; destruct_triv c0.
    + dec (Z.eqb_spec z z0); refl_t.
    + dec (Q_eq_dec q q0). refl_t.
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
    (*TODO: generalize this - maybe write list_eqb with all2*)
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
Inductive def : Set :=
  | datatype_def : mut_adt -> def (*for mutual recursion*)
  | recursive_def: list funpred_def -> def
  | inductive_def : list indpred_def -> def.

(*These definitions can be unwieldy, so we provide nicer functions*)

Definition adt_name (a: alg_datatype) : typesym :=
  match a with
  | alg_def t _ => t
  end.

Definition adt_constrs (a: alg_datatype) : ne_list funsym :=
  match a with
  | alg_def _ c => c
  end.

Definition datatypes_of_def (d: def) : list (typesym * list funsym) :=
  match d with
  | datatype_def m => map (fun a =>
      match a with
      | alg_def ts fs => (ts, ne_list_to_list fs)
      end) (typs m)
  | recursive_def _ => nil
  | inductive_def _ => nil
  end.

Definition funpreds_of_def (d: def) : option (list funpred_def) :=
  match d with
  | recursive_def lf => Some lf
  | _ => None
  end.

(*Definition fundefs_of_def (d: def) : list (funsym * list vsymbol * term) :=
  match d with
  | recursive_def lf =>
    fold_right (fun x acc => match x with
      | fun_def fs vs t => (fs, vs, t) :: acc
      | _ => acc
      end) nil lf
  | _ => nil
  end.

Definition preddefs_of_def (d: def) : list (predsym * list vsymbol * formula) :=
  match d with
  | recursive_def lf =>
    fold_right (fun x acc => match x with
      | pred_def ps vs f => (ps, vs, f) :: acc
      | _ => acc
      end) nil lf
  | _ => nil
  end.*)

Definition indpreds_of_def (d: def) : list (predsym * list formula) :=
  match d with
  | inductive_def li =>
    fold_right (fun x acc => 
    match x with
    | ind_def p fs => (p, (map snd fs)) :: acc
    end) nil li
  | _ => nil
  end.

Definition funsyms_of_def (d: def) : list funsym :=
  match d with
  | datatype_def m => concat ((map (fun a =>
    match a with
    | alg_def _ fs => ne_list_to_list fs
    end)) (typs m))
  | recursive_def lf =>
    fold_right (fun x acc => match x with
      | fun_def fs _ _ => fs :: acc
      | _ => acc
      end) nil lf
  | inductive_def _ => nil
  end.

Definition predsyms_of_def (d: def) : list predsym :=
  match d with
  | datatype_def _ => nil
  | recursive_def lf =>
    fold_right (fun x acc => match x with
    | pred_def ps _ _ => ps :: acc
    | _ => acc
    end) nil lf
  | inductive_def is => (map (fun a =>
    match a with
    | ind_def ps fs => ps
    end) is)
  end.

(*Some utilities we need:*)

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
