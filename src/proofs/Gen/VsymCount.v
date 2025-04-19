(*Prove that vsymbols are countable. This is a lot of work*)
Require Import TermFuncs.
From Proofs Require Typing. (*not great just for 1 lemma*)
From Proofs Require Import Types.

Local Open Scope Z_scope.

Lemma eqb_eq_reflect {A: Type} {eqb: A -> A -> bool} (eqb_eq: forall x y, x = y <-> eqb x y):
  forall x y, reflect (x = y) (eqb x y).
Proof.
  intros x y. apply iff_reflect. auto.
Qed.

Definition unit_eqb (_ _: unit) := true.
Lemma unit_eqb_eq: forall x y, x = y <-> unit_eqb x y.
Proof.
  intros [] []. split; auto.
Qed. 

(*attribute*)

Instance attr_EqDecision: @base.RelDecision attribute _ eq.
Proof.
  unfold base.RelDecision. intros x y. eapply reflect_dec'.
  eapply eqb_eq_reflect. apply attr_eqb_eq.
Qed.

Definition attr_to_tup (a: attribute) : string * Z := (attr_string a, attr_tag a).
Definition attr_of_tup (x: string * Z) : attribute := Build_attribute (fst x) (snd x).
Lemma attr_to_tup_inj: forall x, attr_of_tup (attr_to_tup x) = x.
Proof.
  intros [x1 x2]; simpl. reflexivity.
Qed.

Instance attr_countable : countable.Countable attribute :=
  countable.inj_countable' attr_to_tup attr_of_tup attr_to_tup_inj.

(*Sattr.t*)
Instance sattr_EqDecision: @base.RelDecision Sattr.t _ eq :=
  (@decidable.sig_eq_dec (zmap.Zmap (list (attribute * unit))) (@Attr.M.gmap_wf unit)
    (fun x b1 b2 => bool_irrelevance _ b1 b2) zmap.Zmap_eq_dec).

Instance sattr_countable : countable.Countable Sattr.t.
Proof.
  unfold Sattr.t, Sattr.M.t. unfold sattr_EqDecision.
  apply countable.countable_sig.
  intros x. unfold base.Decision. 
  apply (Typing.bool_dec (fun x => x) _).
Qed.


(*CoqInt.int*)

Instance coqint_EqDecision: @base.RelDecision CoqInt.int _ eq :=
  (@decidable.sig_eq_dec Z (fun z => (- Integer.ocaml_int_size <=? z) && (z <? Integer.ocaml_int_size))
    (fun x b1 b2 => bool_irrelevance _ b1 b2) _).

Instance coqint_countable: countable.Countable CoqInt.int.
Proof.
  apply countable.countable_sig.
  intros x. 
  apply (Typing.bool_dec (fun x => x) _).
Qed.

(*LocTy.position*)
Definition pos_to_tup (x: LocTy.position) : (CoqInt.int * CoqInt.int * CoqInt.int) :=
  (LocTy.pos_file_tag x, LocTy.pos_start x, LocTy.pos_end x).
Definition pos_of_tup (x: CoqInt.int * CoqInt.int * CoqInt.int) : LocTy.position :=
  LocTy.Build_position (fst (fst x)) (snd (fst x)) (snd x).

Lemma pos_to_tup_inj x: pos_of_tup (pos_to_tup x) = x.
Proof.
  destruct x as [s a p]; reflexivity.
Qed.

Instance position_EqDecision : @base.RelDecision LocTy.position _ eq.
Proof.
  intros x y. eapply reflect_dec'.
  eapply eqb_eq_reflect. apply LocTy.position_eqb_eq.
Qed.

Instance position_countable : countable.Countable LocTy.position :=
  countable.inj_countable' pos_to_tup pos_of_tup pos_to_tup_inj.


(* ident*)

Definition ident_to_tup (i: ident) : (string * Sattr.t * option LocTy.position * Z) :=
  (id_string i, id_attrs i, id_loc i, id_tag i).
Definition ident_of_tup (x: (string * Sattr.t * option LocTy.position * Z)) : ident :=
  Build_ident (fst (fst (fst x))) (snd (fst (fst x))) (snd (fst x)) (snd x).

Lemma ident_to_tup_inj x: ident_of_tup (ident_to_tup x) = x.
Proof.
  destruct x as [s a p i]; reflexivity.
Qed.

Instance ident_EqDecision : @base.RelDecision ident _ eq.
Proof. unfold base.RelDecision. intros x y. eapply reflect_dec'.
eapply eqb_eq_reflect. apply ident_eqb_eq.
Qed. (*NOTE: OK Qed, we don't compute with this*)

Instance ident_countable : countable.Countable ident :=
  countable.inj_countable' ident_to_tup ident_of_tup ident_to_tup_inj.

(*Now ty - this is very tricky*)
(*Since ty_c is mutually recursive, we do in 2 steps: first, unroll the type into
  a non-mutually-recursive type, then convert to gen_tree*)

Definition unroll_data := (unit + NumberDefs.int_range + NumberDefs.float_format)%type.

Definition type_def_to_unroll {A B: Type} (f: A -> B) (t: type_def A) : B + unroll_data :=
  match t with
  | NoDef => inr (inl (inl tt))
  | Alias x => inl (f x)
  | Range r => inr (inl (inr r))
  | Float f => inr (inr f)
  end.

Definition type_def_of_unroll {A B: Type} (f: B -> A) (x: B + unroll_data) : type_def A :=
  match x with
  | inl y => Alias (f y)
  | inr (inl (inl _)) => NoDef
  | inr (inl (inr r)) => Range r
  | inr (inr f) => Float f
  end.


(*The unrolled type*)
Unset Elimination Schemes.
Inductive unroll_ty : Type :=
  | Uvar : tvsymbol -> unroll_ty
  | Uapp: ident * list tvsymbol * (unroll_ty * Z + unroll_data) -> list (unroll_ty * Z) -> unroll_ty.
Set Elimination Schemes.

(*Induction principle*)
Section UnrollInd.

Variable (P: unroll_ty -> Prop).
Variable (Pvar: forall v, P (Uvar v)).
Variable (Papp1: forall i vs t z l,
  P t -> Forall P (map fst l) -> P (Uapp (i, vs, inl (t, z)) l)).
Variable (Papp2: forall i vs d l,
  Forall P (map fst l) -> P (Uapp (i, vs, inr d) l)).

Fixpoint unroll_ty_ind (t: unroll_ty) : P t :=
  match t return P t with
  | Uvar v => Pvar v
  | Uapp (i, vs, inl (t, z)) l => Papp1 i vs t z l (unroll_ty_ind t) 
    (proj2 (Forall_map _ _ _) (mk_Forall (fun x => unroll_ty_ind (fst x)) l))
  | Uapp (i, vs, inr d) l => Papp2 i vs d l
    (proj2 (Forall_map _ _ _) (mk_Forall (fun x => unroll_ty_ind (fst x)) l))
  end.

End UnrollInd.

(*Convert between ty and unroll*)

Fixpoint ty_to_unroll (t: ty_c) : unroll_ty * Z :=
  (ty_node_to_unroll (ty_node_of t), ty_tag_of t)
with ty_node_to_unroll (n: ty_node_c) : unroll_ty :=
  match n with
  | Tyvar ts => Uvar ts
  | Tyapp ts tys => Uapp (tysymbol_to_unroll ts) (map ty_to_unroll tys)
  end
with tysymbol_to_unroll (t: tysymbol_c) : ident * list tvsymbol * (unroll_ty * Z + unroll_data) :=
  (ts_name_of t, ts_args_of t, type_def_to_unroll ty_to_unroll (ts_def_of t)).

Fixpoint ty_node_of_unroll (t: unroll_ty) : ty_node_c :=
  (*Use nested, not mutual*)
  let ty_of_unroll (t1: unroll_ty * Z) : ty_c :=
    mk_ty_c (ty_node_of_unroll (fst t1)) (snd t1) in
  let typesym_of_unroll (x: ident * list tvsymbol * (unroll_ty * Z + unroll_data)) : tysymbol_c :=
  mk_ts_c (fst (fst x)) (snd (fst x)) (type_def_of_unroll ty_of_unroll (snd x)) in
  match t with
  | Uvar tv => Tyvar tv
  | Uapp ts tys => Tyapp (typesym_of_unroll ts) (map ty_of_unroll tys)
  end.

(*Simulate mutual*)
Definition ty_of_unroll (t1: unroll_ty * Z) : ty_c :=
    mk_ty_c (ty_node_of_unroll (fst t1)) (snd t1).
Definition  typesym_of_unroll (x: ident * list tvsymbol * (unroll_ty * Z + unroll_data)) : tysymbol_c :=
  mk_ts_c (fst (fst x)) (snd (fst x)) (type_def_of_unroll ty_of_unroll (snd x)).

Lemma ty_node_of_unroll_eq (t: unroll_ty) :
  ty_node_of_unroll t =
  match t with
  | Uvar tv => Tyvar tv
  | Uapp ts tys => Tyapp (typesym_of_unroll ts) (map ty_of_unroll tys)
  end.
Proof.
  destruct t; simpl; auto.
Qed.

(*Now prove lemmas*)
Lemma ty_to_unroll_inj x: ty_of_unroll (ty_to_unroll x) = x.
Proof.
  revert x.
  apply ty_c_ind with (P1:=fun x => ty_of_unroll (ty_to_unroll x) = x)
  (P2:=fun n => ty_node_of_unroll (ty_node_to_unroll n) = n) 
  (P3:=fun t => typesym_of_unroll (tysymbol_to_unroll t) = t); auto.
  - intros [n z]; simpl. unfold ty_of_unroll. simpl.
    intros Heq. rewrite Heq. reflexivity.
  - (*Node is trickiest*)
    intros ts tys IH1 IH2. simpl.
    f_equal.
    + destruct ts as [i tvs d]; simpl in *.
      f_equal. unfold type_def_of_unroll, type_def_to_unroll. destruct d; simpl; auto.
      f_equal. destruct t; simpl in *. f_equal. unfold typesym_of_unroll in IH1. simpl in IH1.
      injection IH1. auto.
    + clear -IH2. induction tys as [| h1 tl1 IH]; simpl in *; auto.
      inversion IH2 as [| ? ? Hall1 Hall2]; subst. f_equal; auto.
  - intros [i tvs d]; simpl. destruct d; simpl; auto.
    intros Ht. unfold typesym_of_unroll. simpl. f_equal. f_equal; auto.
Qed.

(*2nd step: unroll to gen_tree*)

Definition unroll_nonind := (tvsymbol + (ident * list tvsymbol * (Z + unroll_data) * list Z))%type.
Fixpoint unroll_to_gen_tree (u: unroll_ty) : countable.gen_tree unroll_nonind :=
  match u with
  | Uvar tv => countable.GenLeaf (inl tv)
  | Uapp (i, vs, inl (u, z)) tys => countable.GenNode 0 (countable.GenLeaf (inr (i, vs, inl z, map snd tys)) :: 
     unroll_to_gen_tree u :: (map (fun x => unroll_to_gen_tree (fst x)) tys))
  | Uapp (i, vs, inr d) tys => countable.GenNode 1 (countable.GenLeaf (inr (i, vs, inr d, map snd tys)) ::
      (map (fun x => unroll_to_gen_tree (fst x)) tys))
  end.

(*And now the reverse*)
Fixpoint gen_tree_to_unroll (g: countable.gen_tree unroll_nonind) : option unroll_ty :=
  match g with
  | countable.GenLeaf (inl tv) => Some (Uvar tv)
  | countable.GenNode 0 (countable.GenLeaf (inr (i, vs, inl z, l)) :: t1 :: ts) =>
      option_bind (fold_list_option (map gen_tree_to_unroll ts))
        (fun tys => option_bind (gen_tree_to_unroll t1) (fun u => 
          if Nat.eqb (length tys) (length l) then Some (Uapp (i, vs, inl (u, z)) (combine tys l)) else None))
  | countable.GenNode 1 (countable.GenLeaf (inr (i, vs, inr d, l)) :: ts) =>
      option_bind (fold_list_option (map gen_tree_to_unroll ts))
        (fun tys => 
          if Nat.eqb (length tys) (length l) then Some (Uapp (i, vs, inr d) (combine tys l)) else None)
  | _ => None
  end.


(*And prove the partial injectivity*)
Lemma unroll_to_gen_tree_inj: forall x,
  gen_tree_to_unroll (unroll_to_gen_tree x) = Some x.
Proof.
  induction x; simpl; auto.
  - (*Do option first*)
    rewrite Forall_map in H.
    rewrite map_map. 
    assert (Hopt: fold_list_option (map (fun x => gen_tree_to_unroll (unroll_to_gen_tree (fst x))) l) =
      Some (map fst l)).
    {
      clear -H. induction l; simpl in *; auto.
      inversion H as [| ? ? Heq1 Heq2]; subst; clear H.
      rewrite Heq1. simpl. rewrite IHl; simpl; auto.
    }
    rewrite Hopt. simpl.
    rewrite IHx. simpl.
    rewrite !length_map, Nat.eqb_refl, combine_eq.
    reflexivity.
  - (*almost same proof*)
    rewrite Forall_map in H.
    rewrite map_map. 
    assert (Hopt: fold_list_option (map (fun x => gen_tree_to_unroll (unroll_to_gen_tree (fst x))) l) =
      Some (map fst l)).
    {
      clear -H. induction l; simpl in *; auto.
      inversion H as [| ? ? Heq1 Heq2]; subst; clear H.
      rewrite Heq1. simpl. rewrite IHl; simpl; auto.
    }
    rewrite Hopt. simpl.
    rewrite !length_map, Nat.eqb_refl, combine_eq.
    reflexivity.
Qed.

(*And finally, combine*)
Definition ty_c_to_gen_tree (t: ty_c) : countable.gen_tree unroll_nonind * Z :=
  (unroll_to_gen_tree (fst (ty_to_unroll t)), (snd (ty_to_unroll t))).
Definition gen_tree_to_ty_c (t: countable.gen_tree unroll_nonind * Z) : option ty_c :=
  option_map (fun (u: unroll_ty) => (ty_of_unroll (u, snd t))) (gen_tree_to_unroll (fst t)) .

Lemma ty_c_to_gen_tree_inj: forall x,
  gen_tree_to_ty_c (ty_c_to_gen_tree x) = Some x.
Proof.
  intros x. unfold ty_c_to_gen_tree, gen_tree_to_ty_c.
  simpl. rewrite unroll_to_gen_tree_inj. simpl.
  rewrite <- surjective_pairing. f_equal; apply ty_to_unroll_inj.
Qed.

Instance ty_c_EqDecision : @base.RelDecision ty_c _ eq.
Proof. unfold base.RelDecision. intros x y. eapply reflect_dec'.
eapply eqb_eq_reflect. apply ty_eqb_eq.
Qed. 

(*need [unroll_nonind] to be countable*)

Definition int_range_to_tup (i: NumberDefs.int_range) : (Z * Z) :=
  (NumberDefs.ir_lower i, NumberDefs.ir_upper i).
Definition int_range_of_tup (x: Z * Z) : NumberDefs.int_range :=
  NumberDefs.Build_int_range (fst x) (snd x).

Lemma int_range_to_tup_inj x: int_range_of_tup (int_range_to_tup x) = x.
Proof.
  destruct x as [s a]; reflexivity.
Qed.

Instance int_range_EqDecision : @base.RelDecision NumberDefs.int_range _ eq.
Proof.
  intros x y. eapply reflect_dec'.
  eapply eqb_eq_reflect. apply NumberDefs.int_range_eqb_eq.
Qed.

Instance int_range_countable : countable.Countable NumberDefs.int_range :=
  countable.inj_countable' int_range_to_tup int_range_of_tup int_range_to_tup_inj.

(*float format*)

Definition float_format_to_tup (i: NumberDefs.float_format) : (Z * Z) :=
  (NumberDefs.fp_exponent_digits i, NumberDefs.fp_significand_digits i).
Definition float_format_of_tup (x: Z * Z) : NumberDefs.float_format :=
  NumberDefs.Build_float_format (fst x) (snd x).

Lemma float_format_to_tup_inj x: float_format_of_tup (float_format_to_tup x) = x.
Proof.
  destruct x as [s a]; reflexivity.
Qed.

Instance float_format_EqDecision : @base.RelDecision NumberDefs.float_format _ eq.
Proof.
  intros x y. eapply reflect_dec'.
  eapply eqb_eq_reflect. apply NumberDefs.float_format_eqb_eq.
Qed.

Instance float_format_countable : countable.Countable NumberDefs.float_format :=
  countable.inj_countable' float_format_to_tup float_format_of_tup float_format_to_tup_inj.

(*tvsymbol*)

Lemma tvsymbol_to_ident_inj x: Build_tvsymbol (tv_name x) = x.
Proof. destruct x; reflexivity. Qed.

Instance tvsymbol_EqDecision : @base.RelDecision tvsymbol _ eq.
Proof.
  intros x y. eapply reflect_dec'.
  eapply eqb_eq_reflect. apply tvsymbol_eqb_eq.
Qed.

Instance tvsymbol_countable : countable.Countable tvsymbol :=
  countable.inj_countable' tv_name Build_tvsymbol tvsymbol_to_ident_inj.


(*Finally, ty countable*)
(*And countable*)
Instance ty_c_countable : countable.Countable ty_c :=
  countable.inj_countable ty_c_to_gen_tree gen_tree_to_ty_c ty_c_to_gen_tree_inj.

(*And now vsymbol*)

Definition vsym_to_tup (v: TermDefs.vsymbol) : ident * ty_c :=
  (vs_name v, vs_ty v).

Definition vsym_of_tup (t: ident * ty_c) : TermDefs.vsymbol :=
  Build_vsymbol (fst t) (snd t).

Lemma vsym_to_tup_inj: forall x, vsym_of_tup (vsym_to_tup x) = x.
Proof.
  intros [x1 x2]; simpl. reflexivity.
Qed.

Instance vsymbol_EqDecision : @base.RelDecision TermDefs.vsymbol _ eq.
Proof. unfold base.RelDecision. intros x y. eapply reflect_dec'.
eapply eqb_eq_reflect. apply vsymbol_eqb_eq.
Qed. (*NOTE: OK Qed, we don't compute with this*)

Instance vsymbol_countable : countable.Countable TermDefs.vsymbol :=
  countable.inj_countable' vsym_to_tup vsym_of_tup vsym_to_tup_inj.
