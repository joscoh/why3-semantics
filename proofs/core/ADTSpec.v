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


