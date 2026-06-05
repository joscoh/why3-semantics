(*An interpretation of an ADT should satisfy the following properties:
  1. Constructor interps are injective
  2. Constructor interps are disjoint (across types)
  3. An inversion principle holds
  4. A generalized induction principle holds
  
Plan:
X 1. Define these properties generally
2. Refactor existing proofs to use these properties instead of fixing to W-types
  NOTE: I think this will require the isomorphism already to give us the changing-context theorems
  TODO: let's start with the isomorphism
X 3. Prove that W-types satisfy these properties (probably need construction)
  NOTE: might involve following
x  a. define construction
x  b. prove it satisfies fixed point property
x  c. prove we can construct pre-interp
x  d. modify full interp proofs
4. Prove that any two interps satisfying these conditions are isomorphic (need similar construction)
5. Prove that (via isomorphism) any two interps that differ only on ADTs preserve denotation
6. Prove that we can give a fixed interp to prove validity
7. Turn this into a Rocq-based proof system

Goal: sound reasoning about Why3 proof terms via shallowly embedded Rocq terms
  *)
Require Export Hlist Typing Domain. (*TODO: remove*)

Set Bullet Behavior "Strict Subproofs".



Definition fun_interp (pd: sort -> Set) := forall (f:funsym) (srts: list sort)
    (a: arg_list (domain pd) (sym_sigma_args f srts)),
    (domain pd (funsym_sigma_ret f srts)).

Definition adt_rep pd a srts := ((domain pd) (s_cons (adt_name a) srts)).

Definition constr_rep {gamma: context} (gamma_valid: valid_context gamma) 
  (pd: sort -> Set) (pf: fun_interp pd)
  {m : mut_adt} {a: alg_datatype} {c: funsym} {srts: list sort}
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a)
  (srts_len: length srts = length (m_params m))
  (args: arg_list (domain pd) (sym_sigma_args c srts))
  : adt_rep pd a srts :=
  dom_cast _ (Logic.eq_sym (adt_typesym_funsym gamma_valid m_in a_in c_in srts_len)) 
      (pf c srts args).

(*Useful for defaults*)
Definition dom_int (pd: sort -> Set) : domain pd s_int := 0%Z.
Record adt_interp_props {gamma: context} (gamma_valid: valid_context gamma) 
  (pd: sort -> Set) (pf: fun_interp pd) :=
  {
    constrs_inj: forall {m: mut_adt} {a: alg_datatype} {f: funsym} 
    (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (f_in: constr_in_adt f a) 
    {srts: list sort} (srts_len: length srts = length (m_params m))
    (a1 a2: arg_list (domain pd) (sym_sigma_args f srts)),
    constr_rep gamma_valid pd pf m_in a_in f_in srts_len a1 =
    constr_rep gamma_valid pd pf m_in a_in f_in srts_len a2 ->
    a1 = a2;
    (*Have eq hypothesis which is read as: even if the domains are equal for the two
      constructors, the two values cannot be. Of course if domains are different,
      inequality is assured*)
    (*Let's assume we only deal with one: it could be ok for 2 isomorphic types to have
      the same interp, I think(?)*)
    constrs_disj: forall {m: mut_adt} {a: alg_datatype} {f1 f2: funsym} 
    (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) 
    (f1_in: constr_in_adt f1 a) (f2_in: constr_in_adt f2 a) 
    {srts: list sort} (srts_len: length srts = length (m_params m))
    (a1: arg_list (domain pd) (sym_sigma_args f1 srts))
    (a2: arg_list (domain pd) (sym_sigma_args f2 srts)),
    f1 <> f2 ->
    constr_rep gamma_valid pd pf m_in a_in f1_in srts_len a1 <>
    constr_rep gamma_valid pd pf m_in a_in f2_in srts_len a2;
    (*Inversion*)
    find_constr_rep: forall {m: mut_adt} {a: alg_datatype}
    (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) {srts: list sort}
    (srts_len: length srts = length (m_params m))
    (x: adt_rep pd a srts),
    {f: funsym & {Hf: constr_in_adt f a * arg_list (domain pd) (sym_sigma_args f srts) |
    x = constr_rep gamma_valid pd pf m_in a_in (fst Hf) srts_len (snd Hf)}};
    (*Induction*)
    adt_ind: forall {m: mut_adt} (m_in: mut_in_ctx m gamma) {srts: list sort}
    (srts_len: length srts = length (m_params m))
    (P: forall t t_in, adt_rep pd t srts -> Prop)
    (IH: forall t t_in (x: adt_rep pd t srts) (c: funsym) (c_in: constr_in_adt c t)
      (a: arg_list (domain pd) (sym_sigma_args c srts))
      (Hx: x = constr_rep gamma_valid pd pf m_in t_in c_in srts_len a),
      (forall i t' t_in' 
        (Heq : nth i (sym_sigma_args c srts) s_int =
          s_cons (adt_name t') srts), 
        i < length (s_args c) ->
      (*If nth i a has type adt_rep ..., then P holds of it*)
      P t' t_in' (dom_cast _ Heq (hnth i a s_int (dom_int _)))
      ) ->
    P t t_in x
    ),
    forall t t_in (x: adt_rep pd t srts), P t t_in x;
  }.

Definition pf_same_constrs {g1 g2: context} (gamma_valid1: valid_context g1) (gamma_valid2: valid_context g2)
  {pd : sort -> Set} (pf1 pf2: fun_interp pd) : Prop :=
  forall {m a c srts} (m_in1: mut_in_ctx m g1) (m_in2: mut_in_ctx m g2) (a_in: adt_in_mut a m) (c_in: constr_in_adt c a)
    (srts_len: length srts = length (m_params m)) (args: arg_list (domain pd) (sym_sigma_args c srts)),
    constr_rep gamma_valid1 pd pf1 m_in1 a_in c_in srts_len args =
      constr_rep gamma_valid2 pd pf2 m_in2 a_in c_in srts_len args.

(*TODO: move*)
(*We need a transparent version*)
Definition f_equal2 {A1 A2 B: Type} (f: A1 -> A2 -> B) {x1 y1: A1} {x2 y2: A2} (Heq1: x1 = y1) (Heq2: x2 = y2):
  f x1 x2 = f y1 y2.
Proof.
  f_equal.
  - exact Heq1.
  - exact Heq2.
Defined.

(*Any two instances of [adt_interp_props] for the same pd have the same [find_constr_rep]*)
Lemma find_constr_rep_equiv  {g1 g2: context} (gamma_valid1: valid_context g1) (gamma_valid2: valid_context g2) 
  {pd: sort -> Set} {pf1 pf2: fun_interp pd} (pf_eq: pf_same_constrs gamma_valid1 gamma_valid2 pf1 pf2)
  (a1: adt_interp_props gamma_valid1 pd pf1) (a2: adt_interp_props gamma_valid2 pd pf2):
  forall {m a} (m_in1: mut_in_ctx m g1) (m_in2: mut_in_ctx m g2) (a_in: adt_in_mut a m) {srts1 srts2}
    (srts_eq: srts1 = srts2)
    (srts_len1: length srts1 = length (m_params m))
    (srts_len2: length srts2 = length (m_params m))
    (x1: adt_rep pd a srts1)
    (x2: adt_rep pd a srts2)
    (x_eq: x2 = scast (f_equal (adt_rep pd a) srts_eq) x1),
    let y1 := find_constr_rep gamma_valid1 _ _ a1 m_in1 a_in srts_len1 x1 in
    let y2 := find_constr_rep gamma_valid2 _ _ a2 m_in2 a_in srts_len2 x2 in
    exists (Heq: projT1 y1 = projT1 y2),
      snd (proj1_sig (projT2 y1)) = cast_arg_list (f_equal2 (fun (x: funsym) (s: list sort) =>
                                                               sym_sigma_args x s) (eq_sym Heq) (eq_sym srts_eq))
                                      (snd (proj1_sig (projT2 y2))).
Proof.
  intros m a m_in1 m_in2 a_in srts1 srts2 srts_eq srts_len1 srts_len2 x1 x2 x_eq y1 y2.
  subst. assert (srts_len1 = srts_len2) by (apply UIP_dec, Nat.eq_dec). subst.
  destruct a1 as [inj1 disj1 find1 ind1].
  destruct a2 as [inj2 disj2 find2 ind2].
  simpl in y1, y2.
  (*Idea: if funsyms not equal, then contradicts disjointness*)
  destruct y1 as [c1 [[c1_in a1] Hx1]].
  destruct y2 as [c2 [[c2_in a2] Hx2]].
  simpl.
  unfold pf_same_constrs in pf_eq.
  assert (Hrep:=pf_eq m a c1 srts2 m_in1 m_in2 a_in c1_in srts_len2 a1).
  simpl in Hx1, Hx2.
  rewrite Hrep in Hx1.
  rewrite Hx1 in Hx2.
  (*Idea: if constrs same, use inj, else use disjoint*)
  destruct (funsym_eq_dec c1 c2).
  - subst. assert (c1_in = c2_in) by (apply bool_irrelevance). subst.
    apply inj2 in Hx2. subst. exists eq_refl. reflexivity.
  - apply disj2 in Hx2; auto. contradiction.
Qed.
