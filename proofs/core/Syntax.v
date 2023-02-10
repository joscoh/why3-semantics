Require Import Types.
Require Import Common.
Require Export Coq.Reals.Reals.

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

Record funsym : Set :=
  {
    s_name : string;
    s_params : list typevar;
    s_args: list vty;
    s_ret: vty;
    (*Well-formed - all type variables appear in params*)
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
  }.

Lemma s_params_Nodup: forall (f: funsym),
  NoDup (s_params f).
Proof.
  intros. eapply reflect_iff. apply nodup_NoDup. 
  apply s_params_nodup.
Qed.

Lemma p_params_Nodup: forall (p: predsym),
  NoDup (p_params p).
Proof.
  intros. eapply reflect_iff. apply nodup_NoDup. 
  apply p_params_nodup.
Qed.


(*As an example, we define the polymorphic identity function*)
Section ID.

Definition id_name : string := "id".
Definition a_var : string := "a".
Definition id_params : list typevar := [a_var].
Definition id_args: list vty := [vty_var a_var].
Definition id_ret: vty := vty_var a_var.

Definition id_fs : funsym := Build_funsym id_name id_params id_args id_ret eq_refl eq_refl eq_refl.

End ID.

Section SymEqDec.

Lemma funsym_eq: forall (f1 f2: funsym),
  (s_name f1) = (s_name f2) ->
  (s_params f1) = (s_params f2) ->
  (s_args f1) = (s_args f2) ->
  (s_ret f1) = (s_ret f2) ->
  f1 = f2.
Proof.
  intros. destruct f1; destruct f2; simpl in *; subst.
  assert (s_params_nodup0 = s_params_nodup1) by apply bool_irrelevance; subst.
  assert (s_ret_wf0=s_ret_wf1) by apply bool_irrelevance; subst.
  assert (s_args_wf0=s_args_wf1) by apply bool_irrelevance; subst.
  reflexivity.
Qed.

Ltac dec H :=
  destruct H; [ simpl | apply ReflectF; intro C; inversion C; subst; contradiction].

Definition funsym_eqb (f1 f2: funsym) : bool :=
  (String.eqb (s_name f1) (s_name f2)) &&
  (list_eqb String.eqb (s_params f1) (s_params f2)) &&
  (list_eqb vty_eqb (s_args f1) (s_args f2)) &&
  (vty_eqb (s_ret f1) (s_ret f2)).

Lemma funsym_eqb_spec: forall (f1 f2: funsym),
  reflect (f1 = f2) (funsym_eqb f1 f2).
Proof.
  intros. unfold funsym_eqb.
  dec (String.eqb_spec (s_name f1) (s_name f2)).
  dec (list_eqb_spec _ String.eqb_spec (s_params f1) (s_params f2)).
  dec (list_eqb_spec _ vty_eq_spec (s_args f1) (s_args f2)).
  dec (vty_eq_spec (s_ret f1) (s_ret f2)).
  apply ReflectT. apply funsym_eq; auto.
Qed.

Definition funsym_eq_dec (f1 f2: funsym) : {f1 = f2} + {f1 <> f2} :=
  reflect_dec' (funsym_eqb_spec f1 f2).

(*We do the same for predicate symbols*)
Lemma predsym_eq: forall (p1 p2: predsym),
  (p_name p1) = (p_name p2) ->
  (p_params p1) = (p_params p2) ->
  (p_args p1) = (p_args p2) ->
  p1 = p2.
Proof.
  intros; destruct p1; destruct p2; simpl in *; subst.
  assert (p_params_nodup0=p_params_nodup1) by apply bool_irrelevance; subst.
  assert (p_args_wf0=p_args_wf1) by apply bool_irrelevance; subst. reflexivity.
Qed.

Definition predsym_eqb (p1 p2: predsym) : bool :=
  (String.eqb (p_name p1) (p_name p2)) &&
  (list_eq_dec typevar_eq_dec (p_params p1) (p_params p2)) &&
  (list_eq_dec vty_eq_dec (p_args p1) (p_args p2)).

Lemma predsym_eqb_spec: forall (p1 p2: predsym),
  reflect (p1 = p2) (predsym_eqb p1 p2).
Proof.
  intros. unfold predsym_eqb.
  dec (String.eqb_spec (p_name p1) (p_name p2)).
  dec (list_eq_dec typevar_eq_dec (p_params p1) (p_params p2)).
  dec (list_eq_dec vty_eq_dec (p_args p1) (p_args p2)).
  apply ReflectT. apply predsym_eq; auto.
Qed.

Definition predsym_eq_dec (p1 p2: predsym) : {p1 = p2} + {p1 <> p2} :=
  reflect_dec' (predsym_eqb_spec p1 p2).

End SymEqDec.

(** Syntax - Terms and Formulas **)

Inductive constant : Set :=
  | ConstInt : Z -> constant
  | ConstReal : R -> constant
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

Definition vsymbol_eq_dec : forall (x y: vsymbol), 
  {x = y} + {x <> y} := tuple_eq_dec string_dec vty_eq_dec.

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


Section FreeVars.

Local Notation union' := (union vsymbol_eq_dec).
Local Notation big_union' := (big_union vsymbol_eq_dec).
Local Notation remove' := (remove vsymbol_eq_dec).
Local Notation remove_all' := (remove_all vsymbol_eq_dec).

(*Free variables of a pattern*)
Fixpoint pat_fv (p: pattern) : list vsymbol :=
  match p with
  | Pvar x => [x]
  | Pwild => []
  | Pconstr _ _ ps => big_union' pat_fv ps
  | Por p1 p2 => union' (pat_fv p1) (pat_fv p2)
  | Pbind p x => union' (pat_fv p) [x]
  end.

(*Free variables of a term (all variables that appear free at least once)*)
Fixpoint term_fv (t: term) : list vsymbol :=
  match t with
  | Tconst _ => nil
  | Tvar x => [x]
  | Tfun f vtys tms => big_union' term_fv tms
  | Tlet t1 v t2 => union' (term_fv t1) (remove' v (term_fv t2))
  | Tif f t1 t2 => union' (form_fv f) (union' (term_fv t1) (term_fv t2))
  | Tmatch t ty l => union' (term_fv t) (big_union' (fun x => remove_all' (pat_fv (fst x)) (term_fv (snd x))) l)
  | Teps f x  => remove' x (form_fv f)
  end

with form_fv (f: formula) : list vsymbol :=
  match f with
  | Fpred p tys tms => big_union' term_fv tms
  | Fquant q v f => remove' v (form_fv f)
  | Feq _ t1 t2 => union' (term_fv t1) (term_fv t2)
  | Fbinop b f1 f2 => union' (form_fv f1) (form_fv f2)
  | Fnot f => form_fv f
  | Ftrue => nil
  | Ffalse => nil
  | Flet t v f => union' (term_fv t) (remove' v (form_fv f))
  | Fif f1 f2 f3 => union' (form_fv f1) (union' (form_fv f2) (form_fv f3))
  | Fmatch t ty l => union' (term_fv t) (big_union' (fun x => remove_all' (pat_fv (fst x)) (form_fv (snd x))) l)
  end.

Definition closed_term (t: term) : bool :=
  null (term_fv t).
Definition closed_formula (f: formula) : bool :=
  null (form_fv f).

Lemma NoDup_pat_fv (p: pattern) : NoDup (pat_fv p).
Proof.
  induction p; simpl; try constructor; auto.
  - constructor.
  - apply big_union_nodup.
  - apply union_nodup; auto.
  - apply union_nodup; auto. constructor; auto. constructor.
Qed.

End FreeVars.

(*We do NOT have decidable equality on terms and formulas,
  because of real numbers (TODO: see how we should model these)
  But we need some of the pieces*)
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
  destruct q1; destruct q2; simpl; try solve[apply ReflectT; auto];
  apply ReflectF; intro C; inversion C.
Qed.

Definition quant_eq_dec q1 q2 := reflect_dec' (quant_eqb_spec q1 q2).

End EqDec.

(*Definitions: functions, predicates, algebraic data types, inductive predicates*)

Inductive alg_datatype : Set :=
  | alg_def: typesym -> ne_list funsym -> alg_datatype.

Inductive funpred_def : Set :=
  | fun_def: funsym -> list vsymbol -> term -> funpred_def
  | pred_def: predsym -> list vsymbol -> formula -> funpred_def.

Inductive indpred_def : Set :=
  | ind_def: predsym -> list formula -> indpred_def.

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

Definition fundefs_of_def (d: def) : list (funsym * list vsymbol * term) :=
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
  end.

Definition indpreds_of_def (d: def) : list (predsym * list formula) :=
  match d with
  | inductive_def li =>
    fold_right (fun x acc => 
    match x with
    | ind_def p fs => (p, fs) :: acc
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
  | inductive_def is => map (fun a =>
    match a with
    | ind_def ps _ => ps
    end) is
  end.