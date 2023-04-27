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

(*Our definitions can be abstract or concrete*)
Inductive def : Set :=
  (*concrete defs*)
  | datatype_def : mut_adt -> def
  | recursive_def: list funpred_def -> def
  | inductive_def : list indpred_def -> def
  (*abstract defs*)
  | abs_type : typesym -> def
  | abs_fun : funsym -> def
  | abs_pred : predsym -> def.

Definition context := list def.

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

(*TODO: move*)

Definition omap {A B: Type} (f: A -> option B) (l: list A):
list B :=
fold_right (fun x acc => 
  match f x with
  | None => acc
  | Some y => y :: acc
  end) nil l.

Lemma in_omap_iff {A B: Type} (f: A -> option B) (l: list A) (y: B):
  In y (omap f l) <-> exists x, In x l /\ f x = Some y.
Proof.
  split; intros; induction l; simpl in *.
  - destruct H.
  - destruct (f a) eqn : Hfa.
    + simpl in H. destruct H as [Hby | ]; subst; auto.
      * exists a; auto.
      * destruct (IHl H) as [x [Hinx Hfx]]; exists x; auto.
    + destruct (IHl H) as [x [Hinx Hfx]]; exists x; auto.
  - destruct H as [_ [[] _]].
  - destruct H as [x [[Hax | Hinx] Hfx]]; subst.
    + rewrite Hfx. simpl; auto.
    + specialize (IHl (ex_intro _ x (conj Hinx Hfx))).
      destruct (f a); simpl; auto.
Qed.

Definition typesyms_of_mut (m: mut_adt) : list typesym :=
  map adt_name (typs m).

Definition funsyms_of_mut (m: mut_adt) : list funsym :=
  (concat (map adt_constr_list (typs m))).

Definition predsyms_of_indprop (l: list indpred_def) : list predsym :=
  map (fun x => match x with | ind_def p _ => p end) l.

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
  | _ => nil
  end.

Definition predsyms_of_def (d: def) : list predsym :=
  match d with
  | inductive_def l => predsyms_of_indprop l
  | recursive_def fs => predsyms_of_rec fs
  | abs_pred p => [p]
  | _ => nil
  end.

Definition typesyms_of_def (d: def) : list typesym :=
  match d with
  | datatype_def m => typesyms_of_mut m
  | abs_type t => [t]
  | _ => nil
  end.

(*The signature consists of all type symbols, function symbols,
  and predicate symbols given in a context *)
Definition sig_t (ctx: context) : list typesym :=
  concat (map typesyms_of_def ctx).

(*The funsyms in the signature are those from ADT constructors,
  recursive function definitions, and abstract definitions*)
Definition sig_f (ctx: context) : list funsym :=
  concat (map funsyms_of_def ctx).

(*Predsyms are similar, but include indprops instead of
  ADT constructors*)
Definition sig_p (ctx: context) : list predsym :=
  concat (map predsyms_of_def ctx).

(*Now we give some helpful utilities for the defined
  funsyms, predsyms, and bodies*)

(*TODO: should we just use this?*)
Definition mut_of_context (c: context) : list mut_adt :=
  omap (fun d =>
    match d with
    | datatype_def m => Some m
    | _ => None
    end) c.

(*TODO: see if we can get rid of these*)
Definition mutrec_datatypes_of_context (ctx: context) : 
  list(list (typesym * list funsym)) :=
  map (fun m => map (fun a => (adt_name a, adt_constr_list a)) (typs m))
    (mut_of_context ctx).

Definition datatypes_of_context (ctx: context) :=
  concat (mutrec_datatypes_of_context ctx).

Definition mutfuns_of_context (c: context) : list (list funpred_def) :=
  fold_right (fun o acc =>
    match o with
    | recursive_def lf => lf :: acc
    | _ => acc
    end) nil c.

Definition indpreds_of_context (c: context) : 
list (list (predsym * list formula)) :=
omap (fun d =>
  match d with
  |inductive_def il => 
    Some (map (fun x => 
      match x with
      | ind_def p fs => (p, map snd fs)
      end) il)
  | _ => None
  end) c. 

(*The concrete list of typesyms, funsyms, and predsyms*)
(*TODO: change names*)
Definition typesyms_of_context (c: context) : list typesym :=
  map fst (datatypes_of_context c).

Definition funsyms_of_context (c: context) : list funsym :=
  concat (omap (fun d =>
    match d with
    | datatype_def m => Some (funsyms_of_mut m)
    | recursive_def l => Some (funsyms_of_rec l)
    | _ => None
    end) c).

Definition predsyms_of_context (c: context) : list predsym :=
  concat (omap (fun d =>
    match d with
    | inductive_def l => Some (predsyms_of_indprop l)
    | recursive_def l => Some (predsyms_of_rec l)
    | _ => None
    end) c).

(*Definition predsyms_of_context (c: context) : list predsym :=
  concat (map predsyms_of_def c).*)
(*TODO: will have to move most or all of this*)

(*TODO: dont duplicate*)
Ltac right_dec := 
  solve[let C := fresh "C" in right; intro C; inversion C; try contradiction].

Definition adt_dec: forall (x1 x2: alg_datatype), {x1 = x2} + {x1 <> x2}.
intros [t1 c1] [t2 c2].
destruct (typesym_eq_dec t1 t2); [|right_dec].
destruct (ne_list_eq_dec funsym_eq_dec c1 c2); [|right_dec].
left. rewrite e, e0; reflexivity.
Defined.

Definition mut_adt_dec: forall (m1 m2: mut_adt), {m1 = m2} + {m1 <> m2}.
intros m1 m2. destruct m1, m2.
destruct (list_eq_dec adt_dec typs0 typs1); subst; [|right_dec].
destruct (list_eq_dec typevar_eq_dec m_params0 m_params1); subst;[|right_dec].
left. f_equal. apply bool_irrelevance.
Defined.

(*Utilities for dealing with mutual types and context*)
(*We want booleans for proof irrelevance*)
Section MutADTUtil.

Definition mut_in_ctx (m: mut_adt) (gamma: context) :=
  in_bool mut_adt_dec m (mut_of_context gamma).

Lemma mut_in_ctx_eq: forall m gamma,
  mut_in_ctx m gamma <-> In m (mut_of_context gamma).
Proof.
  intros. symmetry. 
  apply (reflect_iff _ _ (in_bool_spec mut_adt_dec m (mut_of_context gamma))).
Qed.

Lemma mut_in_ctx_eq2: forall m gamma,
  mut_in_ctx m gamma <-> In (datatype_def m) gamma.
Proof.
  intros. rewrite mut_in_ctx_eq. symmetry.
  unfold mut_of_context, mut_in_ctx.
  rewrite in_omap_iff.
  split; intros.
  - exists (datatype_def m). auto.
  - destruct H as [d [Hind Hm]].
    destruct d; inversion Hm; subst; auto.
Qed.

Definition mut_typs_in_ctx (l: list alg_datatype) (gamma: context) :=
  exists (vars: list typevar) (H: nodupb typevar_eq_dec vars), 
  In (datatype_def (mk_mut l vars H)) gamma.

(*For recursive functions, it is VERY helpful for this to be
  a (proof irrelevant) boolean*)
Definition adt_in_mut (a: alg_datatype) (m: mut_adt) :=
  in_bool adt_dec a (typs m).

Definition ts_in_mut_list (ts: typesym) (m: list alg_datatype) : bool :=
  in_bool typesym_eq_dec ts (map adt_name m).

Lemma ts_in_mut_list_ex: forall ts m,
  ts_in_mut_list ts (typs m) -> { a | ts = adt_name a /\ 
  adt_in_mut a m}.
Proof.
  unfold adt_in_mut, ts_in_mut_list; intros. induction (typs m); simpl.
  - simpl in H. inversion H.
  - simpl in H.
    destruct (typesym_eq_dec ts (adt_name a)); subst.
    + apply (exist _ a). rewrite eq_dec_refl. split; auto.
    + specialize (IHl H).
      destruct IHl as [a' [Ha' Hina']].
      apply (exist _ a'). rewrite Hina'. subst; simpl_bool; split; auto.
Qed.

Lemma ts_in_mut_list_spec: forall ts m,
  ts_in_mut_list ts (typs m) <-> exists a, ts = adt_name a /\ 
  adt_in_mut a m.
Proof.
  intros. unfold adt_in_mut, ts_in_mut_list. induction (typs m); simpl.
  - split; intros; auto. inversion H. destruct H as [a [H]]; inversion H0.
  - split; intros.
    + destruct (typesym_eq_dec ts (adt_name a)).
      * subst. exists a. rewrite eq_dec_refl. split; auto.
      * apply IHl in H. destruct H as [a' [Ha' Hina']].
        subst. exists a'. rewrite Hina'. simpl_bool. split; auto.
    + destruct H as [a' [Ha' Hina']]; subst.
      destruct (adt_dec a' a); subst; simpl in Hina'.
      * rewrite eq_dec_refl. reflexivity.
      * apply orb_true_iff. right. apply IHl.
        exists a'. split; auto.
Qed.

Definition adt_mut_in_ctx (a: alg_datatype) (m: mut_adt) (gamma: context) :=
  adt_in_mut a m /\ mut_in_ctx m gamma.

Definition adt_in_ctx (a: alg_datatype) (gamma: context) :=
  exists (m: mut_adt), adt_mut_in_ctx a m gamma.

Definition constr_in_adt (c: funsym) (a: alg_datatype) :=
  in_bool_ne funsym_eq_dec c (adt_constrs a).

Definition constr_adt_mut_in_ctx (c: funsym) (a: alg_datatype) 
  (m: mut_adt) (gamma: context) :=
  constr_in_adt c a /\ adt_mut_in_ctx a m gamma.

Definition constr_adt_in_ctx (c: funsym) (a: alg_datatype) (gamma: context) :=
  constr_in_adt c a /\ adt_in_ctx a gamma.

(*Now we need utilities for finding the ADT/mutual adt that a
  type belongs to*)

(*For pattern matches (and for typing info), 
  we need to look at an element of type s, 
  determine if s is an ADT type, and if so,
  extract the components (constructor and args). We need
  a lot of machinery to do this; we do this here.*)

Definition find_ts_in_mut (ts: typesym) (m: mut_adt) : option alg_datatype :=
  find (fun a => typesym_eq_dec ts (adt_name a)) (typs m).

Lemma find_ts_in_mut_none: forall ts m,
  find_ts_in_mut ts m = None <->
  forall a, adt_in_mut a m -> adt_name a <> ts.
Proof.
  intros. unfold find_ts_in_mut.
  rewrite find_none_iff.
  split; intros Hall x Hin.
  - intro C; subst.
    apply in_bool_In in Hin.
    specialize (Hall _ Hin). simpl_sumbool. contradiction.
  - apply (In_in_bool adt_dec) in Hin.
    specialize (Hall _ Hin).
    destruct (typesym_eq_dec ts (adt_name x)); auto; subst;
    contradiction.
Qed.

Lemma find_ts_in_mut_some: forall ts m a,
  find_ts_in_mut ts m = Some a ->
  adt_in_mut a m /\ adt_name a = ts.
Proof.
  intros ts m a Hf. apply find_some in Hf.
  destruct Hf as [Hin Heq].
  split; auto. apply In_in_bool; auto.
  simpl_sumbool.
Qed.

Lemma find_ts_in_mut_iff: forall ts m a,
  NoDup (map adt_name (typs m)) ->
  (find_ts_in_mut ts m = Some a) <-> (adt_in_mut a m /\ adt_name a = ts).
Proof.
  intros. eapply iff_trans. apply find_some_nodup.
  - intros. repeat simpl_sumbool.
    apply (NoDup_map_in H); auto.
  - simpl. unfold adt_in_mut. split; intros [Hin Hname];
    repeat simpl_sumbool; split; auto; try simpl_sumbool;
    apply (reflect_iff _ _ (in_bool_spec adt_dec a (typs m))); auto.
Qed.

Definition vty_in_m (m: mut_adt) (vs: list vty) (v: vty) : bool :=
  match v with
  | vty_cons ts vs' => 
    ssrbool.isSome (find_ts_in_mut ts m) &&
    list_eq_dec vty_eq_dec vs' vs
  | _ => false
  end.

Definition vty_m_adt (m: mut_adt) (vs: list vty) (v: vty) : option (alg_datatype) :=
  match v with
  | vty_cons ts vs' =>
      if list_eq_dec vty_eq_dec vs' vs then
         find_ts_in_mut ts m
      else None
  | _ => None
  end.

Lemma vty_in_m_spec (m: mut_adt) (vs: list vty) (v: vty):
  reflect 
  (exists a, adt_in_mut a m /\ v = vty_cons (adt_name a) vs)
  (vty_in_m m vs v) .
Proof.
  unfold vty_in_m. destruct v; try solve[apply ReflectF; intros [a [Ha Heq]]; inversion Heq].
  destruct (find_ts_in_mut t m) eqn : Hfind; simpl.
  - apply find_ts_in_mut_some in Hfind.
    destruct Hfind; subst.
    destruct (list_eq_dec vty_eq_dec l vs); subst; simpl.
    + apply ReflectT. exists a. split; auto.
    + apply ReflectF. intros [a' [Ha' Heq]]; inversion Heq; subst;
      contradiction.
  - apply ReflectF. rewrite find_ts_in_mut_none in Hfind.
    intros [a [Ha Heq]]; subst.
    inversion Heq; subst.
    apply (Hfind a Ha); auto.
Qed. 

Definition vsym_in_m (m: mut_adt) (vs: list vty) (x: vsymbol) : bool :=
  vty_in_m m vs (snd x).


(*From a list of vsymbols, keep those which have type vty_cons a ts
  for some a in mut_adt m*)
Definition vsyms_in_m (m: mut_adt) (vs: list vty) (l: list vsymbol) :
  list vsymbol :=
  filter (vsym_in_m m vs) l.

(*A more useful formulation*)
Lemma vsyms_in_m_in (m: mut_adt) (vs: list vty) (l: list vsymbol):
  forall x, In x (vsyms_in_m m vs l) <-> In x l /\ exists a,
    adt_in_mut a m /\ snd x = vty_cons (adt_name a) vs.
Proof.
  intros. unfold vsyms_in_m, vsym_in_m, vty_in_m.
  rewrite in_filter. rewrite and_comm. bool_to_prop.
  destruct x; simpl in *. destruct v; try (solve[split; [intro C; inversion C | 
    intros [a [a_in Hty]]; inversion Hty]]).
  unfold ssrbool.isSome.
  destruct (find_ts_in_mut t m) eqn : Hts; simpl.
  - destruct (list_eq_dec vty_eq_dec l0 vs); subst; simpl; split;
    intros; auto; try tf.
    + exists a. apply find_ts_in_mut_some in Hts. destruct Hts.
      subst. split; auto.
    + destruct H as [a' [Ha' Hty]]. inversion Hty; subst; auto.
  - split; [intro C; inversion C | intros [a [Ha Hty]]].
    rewrite find_ts_in_mut_none in Hts.
    inversion Hty; subst.
    apply Hts in Ha. contradiction.
Qed.

Definition constr_in_m (f: funsym) (m: mut_adt) : bool :=
  existsb (fun a => constr_in_adt f a) (typs m).

End MutADTUtil.

(*Similar defs for recursive functions and inductive predicates*)
Section RecFunUtil.

Definition funsym_in_mutfun (f: funsym) (l: list funpred_def) : bool :=
  in_bool funsym_eq_dec f (funsyms_of_rec l).

Definition get_mutfun_fun (f: funsym) (gamma': context) : option (list funpred_def) :=
  find (funsym_in_mutfun f) (mutfuns_of_context gamma').

Definition predsym_in_mutfun (p: predsym) (l: list funpred_def) : bool :=
  in_bool predsym_eq_dec p (predsyms_of_rec l).

Definition get_mutfun_pred (p: predsym) (gamma': context) : option (list funpred_def) :=
  find (predsym_in_mutfun p) (mutfuns_of_context gamma').

Lemma in_mutfuns gamma (l: list funpred_def) :
  In l (mutfuns_of_context gamma) <->
  In (recursive_def l) gamma.
Proof.
  induction gamma; simpl; auto; try reflexivity.
  destruct a; simpl in *; split; intros; destruct_all;
  try discriminate; try (rewrite IHgamma); auto;
  try (rewrite <- IHgamma); auto.
  inversion H; subst; auto.
Qed.

Lemma in_fun_def l f a b:
  In (fun_def f a b) l ->
  In f (funsyms_of_rec l).
Proof.
  simpl; induction l; simpl; auto; intros.
  destruct H; subst; simpl; auto.
  destruct a0; simpl; try right; auto.
Qed.

Lemma in_pred_def l p a b:
  In (pred_def p a b) l ->
  In p (predsyms_of_rec l).
Proof.
  simpl; induction l; simpl; auto; intros.
  destruct H; subst; simpl; auto.
  destruct a0; simpl; try right; auto.
Qed.

Definition pred_in_indpred (p: predsym) (l: list (predsym * list formula)) :=
  in_bool predsym_eq_dec p (map fst l).

Definition indpred_def_to_indpred (i: indpred_def) : 
  predsym * list formula :=
  match i with
  | ind_def p l => (p, map snd l)
  end.

Definition get_indpred (l: list indpred_def) :
  list (predsym * list formula) :=
  map indpred_def_to_indpred l.

Lemma in_inductive_ctx gamma l: In (inductive_def l) gamma ->
  In (get_indpred l) (indpreds_of_context gamma).
Proof.
  clear.
  intros. induction gamma; simpl in *; auto.
  destruct a; destruct H; try discriminate; auto.
  - inversion H; subst. simpl. left.
    reflexivity.
  - simpl. right. auto.
Qed.

Lemma pred_in_indpred_iff p l:
  pred_in_indpred p (get_indpred l) <->
  In p (predsyms_of_indprop l).
Proof.
  unfold pred_in_indpred.
  induction l; simpl; split; auto; try discriminate; bool_to_prop;
  intros; destruct_all; auto.
  - simpl_sumbool. destruct a; auto.
  - apply IHl in H. auto.
  - destruct a; simpl. left. destruct (predsym_eq_dec p p); auto.
  - right. apply IHl; auto.
Qed.

End RecFunUtil.

(*Definition datatypes_of_def (d: def) : list (typesym * list funsym) :=
  match d with
  | datatype_def m => map (fun a =>
      match a with
      | alg_def ts fs => (ts, ne_list_to_list fs)
      end) (typs m)
  | _ => nil
  end.
  | recursive_def _ => nil
  | inductive_def _ => nil
  end.*)

(*Definition funpreds_of_def (d: def) : option (list funpred_def) :=
  match d with
  | recursive_def lf => Some lf
  | _ => None
  end.*)

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

(*Definition indpreds_of_def (d: def) : list (predsym * list formula) :=
  match d with
  | inductive_def li =>
    fold_right (fun x acc => 
    match x with
    | ind_def p fs => (p, (map snd fs)) :: acc
    end) nil li
  | _ => nil
  end.*)

(*Definition funsyms_of_def (d: def) : list funsym :=
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
  end.*)

(*Definition predsyms_of_def (d: def) : list predsym :=
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
  end.*)

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