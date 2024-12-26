Require Import Pattern.
Require Import Denotational.
Require Import Coq.Sorting.Permutation.
Require Import GenElts.
From Equations Require Import Equations. 
Set Bullet Behavior "Strict Subproofs".

Ltac simpl_len_extra ::= rewrite !gen_strs_length.

Section CompileCorrect.
(*NOTE: want gamma, but only gamma, in context. Typing should
  not rely on interpretations, and it is easier to prove it
  together with the semantic result*)

Context {gamma: context} (gamma_valid: valid_context gamma).
Variable (b: bool). (*Generic over terms and formulas*)
Variable (ret_ty : gen_type b). (*The return type of the values*)

(*Prove lemmas for semantic result*)

Section PatSemanticsLemmas.
Context (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
(pf: pi_funpred gamma_valid pd pdf) (vt: val_typevar).

Notation gen_rep := (gen_rep gamma_valid pd pdf pf vt).

Definition pat_matrix := list (list pattern * gen_term b).

(*Typing of Pattern Matrices*)
Section PatMatrixTyping.

(*Typing for row*)
Definition row_typed (tys: list vty) (p: list pattern) : Prop :=
  Forall2 (fun p t => pattern_has_type gamma p t) p tys.

Lemma row_typed_length {tys ps}:
  row_typed tys ps ->
  length tys = length ps.
Proof.
  unfold row_typed. intros Hall2.
  apply Forall2_length in Hall2; auto.
Qed.

Lemma row_typed_rev tys ps:
  row_typed tys ps ->
  row_typed (rev tys) (rev ps).
Proof.
  apply Forall2_rev.
Qed.


(*Typing for matrix*)
Definition pat_matrix_typed (tys: list vty) (p: pat_matrix) : Prop :=
  Forall (fun row => row_typed tys (fst row)) p /\
  Forall (fun row => gen_typed gamma b (snd row) ret_ty) p.

Lemma pat_matrix_typed_tail {tys p ps}:
  pat_matrix_typed tys (p :: ps) ->
  pat_matrix_typed tys ps.
Proof.
  intros Hp. destruct Hp as [Hp1  Hp2]; inversion Hp1; inversion Hp2; subst; split; auto.
Qed.

Lemma pat_matrix_typed_head {tys p ps}:
  pat_matrix_typed tys (p :: ps) ->
  row_typed tys (fst p) /\ gen_typed gamma b (snd p) ret_ty.
Proof.
  intros Hp. destruct Hp as [Hp1  Hp2]; inversion Hp1; inversion Hp2; subst; split; auto.
Qed.

Lemma pat_matrix_typed_app {tys: list vty} {p1 p2}:
  pat_matrix_typed tys p1 ->
  pat_matrix_typed tys p2 ->
  pat_matrix_typed tys (p1 ++ p2).
Proof.
  unfold pat_matrix_typed; rewrite !Forall_app; intros; destruct_all; auto.
Qed.

Lemma pat_matrix_typed_app_inv {tys p1 p2}:
  pat_matrix_typed tys (p1 ++ p2) ->
  pat_matrix_typed tys p1 /\ pat_matrix_typed tys p2.
Proof.
  unfold pat_matrix_typed.
  rewrite !Forall_app. intros; destruct_all; split_all; auto.
Qed.

Lemma prove_pat_matrix_typed_cons {tys p ps}:
  row_typed tys (fst p) ->
  gen_typed gamma b (snd p) ret_ty ->
  pat_matrix_typed tys ps ->
  pat_matrix_typed tys (p :: ps).
Proof.
  intros. unfold pat_matrix_typed in *.
  destruct_all; split; constructor; auto.
Qed.

Lemma pat_matrix_typed_nil l:
  pat_matrix_typed l nil.
Proof.
  split; auto.
Qed.

End PatMatrixTyping.

(*Semantics of multiple pattern matching*)
Section MultipleMatchSemantics.
Variable (v: val_vars pd vt).

(*Much, much easier with Equations*)
Equations matches_row (tys: list vty) 
  (al: arg_list (domain (dom_aux pd)) (map (v_subst vt) tys))
  (p: list pattern) 
  (Htys: row_typed tys p) :
  option ((list (vsymbol * {s: sort & domain (dom_aux pd) s }))) :=
matches_row nil al nil Htys := Some [];
matches_row (t1 :: tys1) al (p :: ps) Htys :=
  option_bind ((match_val_single gamma_valid pd pdf vt _ p (Forall2_inv_head Htys) (hlist_hd al)))
      (fun l => option_bind (matches_row tys1 (hlist_tl al) ps (Forall2_inv_tail Htys)) (fun l1 => Some (l ++ l1))).

(*Semantics for whole matrix matching*)
Equations matches_matrix  (tys: list vty) 
  (al: arg_list (domain (dom_aux pd)) (map (v_subst vt) tys))
  (p: pat_matrix)
  (Hty: pat_matrix_typed tys p) :
  option (gen_ret pd vt b ret_ty):=
matches_matrix tys al nil Hty := None;
matches_matrix tys al (row :: ps) Hty :=
  match (matches_row tys al (fst row) (Forall_inv (proj1 Hty))) with
    | Some l => Some (gen_rep (extend_val_with_list pd vt v l) ret_ty (snd row) (Forall_inv (proj2 Hty)))
    | None => matches_matrix tys al ps (pat_matrix_typed_tail Hty)
  end.

(*One more version, when we start with terms*)
Equations terms_to_hlist (ts: list term) (tys: list vty)
  (Hty: Forall2 (fun t ty => term_has_type gamma t ty) ts tys) :
  arg_list (domain (dom_aux pd)) (map (v_subst vt) tys) :=
terms_to_hlist nil nil Hty := HL_nil _;
terms_to_hlist (t :: ts) (ty :: tys) Hty :=
  HL_cons _ _ _ (term_rep gamma_valid pd pdf vt pf v t ty (Forall2_inv_head Hty)) 
    (terms_to_hlist ts tys (Forall2_inv_tail Hty)).
  (*Wow equations is magic*)

Definition matches_matrix_tms (tms: list term) (tys: list vty) (P: pat_matrix)
  (Hty: Forall2 (term_has_type gamma) tms tys)
  (Hp: pat_matrix_typed tys P) : option (gen_ret pd vt b ret_ty) :=
  matches_matrix tys (terms_to_hlist tms tys Hty) P Hp.

(*Some simple lemmas:*)

Lemma terms_to_hlist_tl t ts ty tys Hty:
  hlist_tl (terms_to_hlist (t :: ts) (ty :: tys) Hty) =
  terms_to_hlist ts tys (Forall2_inv_tail Hty).
Proof.
  simp terms_to_hlist. reflexivity.
Qed.

Lemma terms_to_hlist_irrel ts tys H1 H2:
  terms_to_hlist ts tys H1 = terms_to_hlist ts tys H2.
Proof.
  revert tys H1 H2. induction ts as [| tm ts IH]; simpl; intros [| ty1 tys];
  intros Hall1 Hall2; auto; try solve[inversion Hall1].
  simp terms_to_hlist.
  rewrite term_rep_irrel with (Hty2:=(Forall2_inv_head Hall2)).
  f_equal. apply IH.
Qed.

Lemma terms_to_hlist_app (tys1 tys2 : list vty) (tms1 tms2 : list term) Hty Hty1 Hty2:
  length tys1 = length tms1 ->
  terms_to_hlist (tms1 ++ tms2) (tys1 ++ tys2)  Hty =
  cast_arg_list (eq_sym (map_app (v_subst vt) tys1 tys2))
    (hlist_app _ _ _ (terms_to_hlist tms1 tys1 Hty1) (terms_to_hlist tms2 tys2 Hty2)).
Proof.
  intros Hlen.
  generalize dependent (eq_sym (map_app (v_subst vt) tys1 tys2)).
  generalize dependent tms1.
  induction tys1 as [| ty1 tys1 IH]; simpl; intros [| tm1 tms1]; intros; simpl; simp hlist_app; auto;
  try discriminate.
  - assert (e = eq_refl). { apply UIP_dec, list_eq_dec, sort_eq_dec.  } subst.
    erewrite terms_to_hlist_irrel. reflexivity.
  - simp terms_to_hlist.
    simp hlist_app.
    rewrite cast_arg_list_cons. erewrite IH; auto. f_equal.
    generalize dependent (cons_inj_hd e). intros Heq.
    assert (Heq = eq_refl). { apply UIP_dec, sort_eq_dec. } subst.
    simpl. apply term_rep_irrel.
Qed.

Lemma terms_to_hlist_rev tys tms Hty Htyrev:
  terms_to_hlist (rev tms) (rev tys) Htyrev =
  cast_arg_list (eq_sym (map_rev _ _))
    (hlist_rev _ _ (terms_to_hlist tms tys Hty)).
Proof.
  generalize dependent (eq_sym (map_rev (v_subst vt) tys)).
  revert Hty Htyrev.
  revert tms.
  induction tys as [| ty tys IH]; simpl; intros[| tm1 tms]; intros; simpl; try solve[inversion Hty].
  - simp hlist_rev. assert (e = eq_refl). { apply UIP_dec, list_eq_dec, sort_eq_dec. } subst.
    reflexivity.
  - simp terms_to_hlist. simp hlist_rev.
    rewrite terms_to_hlist_app with (Hty1:=Forall2_rev (Forall2_inv_tail Hty))
      (Hty2:=(Forall2_cons _ _ (Forall2_inv_head Hty) (Forall2_nil _))).
    2: { simpl_len; auto. apply Forall2_length in Hty. simpl in Hty. lia. }
    assert (Happeq: rev (map (v_subst vt) tys) = map (v_subst vt) (rev tys)).
    {
      rewrite map_app in e. simpl in e.
      apply app_inj_tail_iff in e. destruct_all; auto.
    }
    rewrite IH with (Hty:=(Forall2_inv_tail Hty))(e:=Happeq).
    simpl in *.
    rewrite hlist_app_cast1.
    simp terms_to_hlist. simpl.
    erewrite term_rep_irrel with (Hty2:=Forall2_inv_head Hty).
    rewrite cast_arg_list_compose.
    apply cast_arg_list_eq.
Qed.

Lemma matches_row_irrel tys h ps Hr1 Hr2:
  matches_row tys h ps Hr1 = matches_row tys h ps Hr2.
Proof.
  revert Hr1 Hr2.
  revert ps.
  induction tys as [| ty tys IH]; intros; assert (Hlen:=row_typed_length Hr1);
  destruct ps as [| phd ptl]; try discriminate; simp matches_row; [reflexivity|].
  rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hr2)).
  apply option_bind_ext.
  intros x. erewrite IH. reflexivity.
Qed.

(*TODO: do we really need both? Probably not; as this shows, they are the same*)
Lemma iter_arg_list_matches_row (tys: list vty) (ps: list pattern)
  (Hrow: row_typed tys ps)
  (Htys: Forall (fun x => pattern_has_type gamma (fst x) (snd x)) (combine ps tys))
  (a: arg_list (domain (dom_aux pd)) (map (v_subst vt) tys)):
  iter_arg_list gamma_valid pd pdf tys a ps Htys =
  matches_row tys a ps Hrow.
Proof.
  revert Hrow Htys. revert ps. induction tys as [| thd ttl IH]; 
  intros [| phd ptl]; intros; auto; try solve[inversion Hrow].
  simp matches_row. simpl.
  rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hrow)).
  destruct_match_single m1 Hmatch1; auto.
  rewrite IH with (Hrow:=(Forall2_inv_tail Hrow)).
  reflexivity.
Qed.

Lemma matches_row_vars {tys al ps Hty l}:
  matches_row tys al ps Hty = Some l ->
  forall v, In v (map fst l) <-> In v (big_union vsymbol_eq_dec pat_fv ps).
Proof.
  intros Hmatch. generalize dependent l.
  generalize dependent ps. induction tys as [|ty1 tys IH]; simpl; intros [|phd ptl]; intros;
  try solve [inversion Hty]; simp matches_row in Hmatch.
  - inversion Hmatch; subst. reflexivity.
  - destruct (match_val_single _ _ _ _ _ phd _) as [m1|] eqn : Hmatch1; simpl in Hmatch; try discriminate.
    destruct (matches_row _ _ ptl _) as [m2|] eqn : Hmatch2; try discriminate. simpl in Hmatch.
    inversion Hmatch; subst. simpl.
    rewrite map_app, in_app_iff, union_elts,
      (match_val_single_free_var _ _ _ _ _ _ _ _ _ _ Hmatch1), (IH _ _ _ _ Hmatch2).
    reflexivity.
Qed.

Lemma matches_matrix_irrel tys al p Hty1 Hty2:
  matches_matrix tys al p Hty1 =
  matches_matrix tys al p Hty2.
Proof.
  revert Hty1 Hty2. induction p; simpl; auto.
  intros. simp matches_matrix.
  rewrite (matches_row_irrel) with (Hr2:=(Forall_inv (proj1 Hty2))).
  destruct (matches_row _ _ _ _); simpl; auto. f_equal.
  apply gen_rep_irrel.
Qed.

Lemma matches_matrix_app tys al P1 P2 Hp1 Hp2 Hp12:
  matches_matrix tys al (P1 ++ P2) Hp12 =
  match (matches_matrix tys al P1 Hp1) with
  | None => matches_matrix tys al P2 Hp2
  | x => x
  end.
Proof.
  revert Hp1 Hp2 Hp12. induction P1 as [| rhd P1' IH]; simpl; intros; auto;
  simp matches_matrix;[apply matches_matrix_irrel|].
  rewrite matches_row_irrel with (Hr2:=(Forall_inv (proj1 Hp1))).
  destruct (matches_row _ _ _ _); simpl; auto.
  f_equal. apply gen_rep_irrel.
Qed.

End MultipleMatchSemantics.

Section SpecDefaultLemmas.
Variable (v: val_vars pd vt).

(*Prove the key intermediate results for the S and D matrices.
  First, we give nicer definitions*)

Definition spec(P: pat_matrix) (c: funsym) : pat_matrix :=
  omap (fun x =>
      let ps := fst x in
      let a := snd x in
      match ps with
      | p :: ps =>
        match p with
        | Pwild => Some (repeat Pwild (length (s_args c)) ++ ps, a)
        | Pconstr fs tys pats =>
            if funsym_eqb fs c then Some (rev pats ++ ps, a) else None
        | _ => None
        end
      | _ => None
      end
) P.

(*The specifications: let ts = t :: tl. By typing, know [[t]] = [[c]](al)
  1. If c is in first column of P, then [[match((rev al) ++ [[tl]], S(P, c))]] = 
    [[match(ts, P)]] 
  2. If c is not in the first column of P, then [[match(tl, D(P, c))]] = [[match(ts, P)]]*)

(*A predicate that says "term t has semantic meaning c(al), where c is a constructor
  in ADT a in mutual m"*)
Definition tm_semantic_constr (t: term) {m: mut_adt} (m_in : mut_in_ctx m gamma)
  {a: alg_datatype} (a_in: adt_in_mut a m) {c: funsym} (c_in: constr_in_adt c a) 
  {args: list vty} (args_len: length args = length (m_params m))
  (Hty: term_has_type gamma t (vty_cons (adt_name a) args))
  (al: arg_list (domain (dom_aux pd)) (sym_sigma_args c (map (v_subst vt) args)))
   : Prop :=
  (*[[t]] =*)
  term_rep gamma_valid pd pdf vt pf v t _ Hty = dom_cast (dom_aux pd) (*Need 2 casts*)
    (eq_sym (v_subst_cons (adt_name a) args)) 
  (scast 
    (eq_sym (adts pdf m (map (v_subst vt) args) a m_in a_in))
  (* [[c]](al)*)
  (constr_rep gamma_valid m m_in 
    (map (v_subst vt) args) (eq_trans (map_length _ _) args_len) (dom_aux pd) a a_in 
      c c_in (adts pdf m (map (v_subst vt) args)) 
         al)).

(*If a term has type a(args) for ADT a, then we can find the constructor and arguments
  that its term_rep is equal to. This is a nicer, higher level interface for [find_constr_rep];
  it is a straightforward application*)
Lemma find_semantic_constr (t: term) {m: mut_adt} (m_in : mut_in_ctx m gamma)
  {a: alg_datatype} (a_in: adt_in_mut a m)  
  {args: list vty} (args_len: length args = length (m_params m))
  (Hty: term_has_type gamma t (vty_cons (adt_name a) args)) :
  {f : funsym & {Hf: constr_in_adt f a * arg_list (domain (dom_aux pd)) (sym_sigma_args f (map (v_subst vt) args))
    |  tm_semantic_constr t m_in a_in (fst Hf) args_len Hty (snd Hf) }}.
Proof.
  unfold tm_semantic_constr.
  assert (srts_len: length (map (v_subst vt) args) = length (m_params m)) by solve_len.
  assert (Hunif: uniform m) by (apply (gamma_all_unif gamma_valid); auto). 
  (*Of course, use [find_constr_rep]*)
  destruct (find_constr_rep gamma_valid _ m_in (map (v_subst vt) args) srts_len (dom_aux pd) a a_in
    (adts pdf m (map (v_subst vt) args)) Hunif
    (scast (adts pdf m (map (v_subst vt) args) a m_in a_in) (dom_cast (dom_aux pd) (v_subst_cons (adt_name a) args) 
      (term_rep gamma_valid pd pdf vt pf v t
  (vty_cons (adt_name a) args) Hty)))) as [f [[c_in al] Hrep]]. simpl in Hrep.
  apply (existT _ f).
  apply (exist _ (c_in , al)). simpl.
  assert (Heq: srts_len = (eq_trans (map_length (v_subst vt) args) args_len)). { apply UIP_dec, Nat.eq_dec.  }
  subst.
  rewrite <- Hrep, scast_eq_sym.
  unfold dom_cast.
  rewrite <- eq_sym_map_distr, scast_eq_sym.
  reflexivity.
Qed.

Section SpecProof.

(*TODO: write this up more formally and remove comment in Coq code*)
(*The specialization proof is very involved. Recall that we want to prove
  that [[match((rev al) ++ [[tl]], S(P, c))]] = [[match(ts, P)]] if c is in the first column.
  We first consider the case when P is (c(ps) :: ptl) :: P'.
  Then S(P, c) = ((rev ps) ++ ptl) :: P'.
  For the LHS, we have that [[match(rev al ++ [tl], S(P, c))]] is decomposed into
    (match_row (rev al ++ [tl], (rev ps ++ ptl))) and (match(rev al ++ [tl], P'))
    We prove (1) that we can split up the first [match_row] into
    (match_row(rev al, rev ps)) and (match_row [tl], ptl)
    We then prove (2) that [match_row(rev al, rev ps)] is a permutation of [match_row(al, ps)]
      (NOTE: it is NOT true that they are equal)
  For the RHS, we have that [[match(ts, P)]] is decomposed into
    (match_row (t :: tl, (c(ps) :: ptl))) and (match(t :: tl, P'))
    the first [match_row] simplifies to [match_val_single c(ps) (term_rep t)]
      and (match_row(tl, ptl))
    We then prove (3) that [match_val_single c(ps) (term_rep t)], when [[t]] = c(al)
      equals [match_row(al, ps)] (i.e. we just match the arguments)
  Thus, we have that both sides are equivalent up to a permutation of the first list
  (from [match_row(al, ps)] = [match_val_single c(ps) (term_rep t)])
  Finally, we use known properties (NoDup) of [match_val_single] to show that the
  resulting valuation is equal, and conclude using the IH.

  Simple case: if c'(ps) where c!=c', need (4) that [match_val_single] is None here,
    and the rest is easy

  In the second case, P = (Pwild :: ptl) :: P'.
  Then S(P, c) = (repeat Pwild m ++ ptl) :: P'. (where m is the size of (s_args c)/al)
  For the LHS, we have that [[match(rev al) ++ [tl], (repeat Pwild m ++ ptl) :: P']]
  decomposes into (match_row (rev al ++ [tl], repeat Pwild m ++ ptl)) and 
    (match((rev al) ++ [tl], P')).
    The first row is again decomposed by (1) into (match_row(rev al, repeat Pwild m))
      and (match_row([tl], ptl)).
    We prove (5) that the first [match_row] is Some [] because all patterns are wilds.
  For the RHD, we have that [[match(t :: tl, (Pwild :: ptl) :: P')]] is decomposed int
    (match_row(t :: tl, Pwild :: ptl)) and (match(t :: tl, P'))
    The first simplifies to [match_val_single Pwild (term_rep t)] and (match_row(tl, ptl))
    and the [match_val_single] simplifies to Some [] as well. Thus, we get the desired equality.

Therefore, we need 4 intermediate lemmas:
(1) decomposing [match_row] for [app]
(2) relating [match_val_single c(ps) [[t]]] with [match_row ps al] where [[t]] = c(al)
(3) relating [match_row(l1, l2)] and [match_row(rev l1, rev l2)] (permutation)
(4) if [[t]] = c(al), then [match_val_single c'(ps), [[t]]] = None
(5) proving that matching a row of all wildcards gives Some []*)


(*1. Decompose [match_row] for [app]*)

Lemma matches_row_app (tys1 tys2: list vty) 
  (h1: arg_list (domain (dom_aux pd)) (map (v_subst vt) tys1))
  (h2: arg_list (domain (dom_aux pd)) (map (v_subst vt) tys2))
  (h3: arg_list (domain (dom_aux pd)) (map (v_subst vt) (tys1 ++ tys2)))
  (Hheq: h3 = cast_arg_list (eq_sym (map_app _ _ _)) (hlist_app _ _ _ h1 h2))
  (ps1 ps2: list pattern)
  (Hlen1: length tys1 = length ps1)
  (Hlen2: length tys2 = length ps2)
  (Hr1: row_typed (tys1 ++ tys2) (ps1 ++ ps2))
  (*duplicate*)
  (Hr2: row_typed tys1 ps1)
  (Hr3: row_typed tys2 ps2):
  matches_row (tys1 ++ tys2) h3 (ps1 ++ ps2) Hr1 =
  option_bind (matches_row tys1 h1 ps1 Hr2) (fun l => 
    option_bind (matches_row tys2 h2 ps2 Hr3) (fun l1 => Some (l ++ l1))).
Proof.
  generalize dependent (eq_sym (map_app (v_subst vt) tys1 tys2)).
  revert Hr1 Hr2 Hr3.
  generalize dependent Hlen1. revert ps1. induction tys1 as [| ty tys1 IH]; simpl.
  - intros ps1 Hlen1. destruct ps1; try discriminate. simpl.
    intros. subst. simp matches_row. simpl. simp hlist_app.
    rewrite option_bind_id.
    assert (e = eq_refl) by (apply UIP_dec, list_eq_dec, sort_eq_dec).
    subst. unfold cast_arg_list; simpl.
    apply matches_row_irrel.
  - intros [| phd ps1] Hlen1; try discriminate. intros. subst. simpl.
    simp matches_row.
    rewrite hlist_hd_cast with (Heq2:=eq_refl). simpl.
    rewrite (hlist_hd_app1 (v_subst vt ty)) .
    rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hr2)).
    simpl in *.
    (*Unfortunately, for some reason Coq cannot unify the two*)
    destruct_match_single m1 Hmatch1; auto.
    erewrite IH with (h1:=hlist_tl h1) (Hr2:=(Forall2_inv_tail Hr2)) (Hr3:=Hr3); simpl.
    + apply option_bind_appcomp.
    + lia.
    + rewrite hlist_tl_cast.
      rewrite (hlist_tl_app1 (v_subst vt ty)). reflexivity.
Qed.

(*2. if we have a constructor which matches,
  then [match_val_single] is the same as [matches_row] on the argument list.
  This lemma needs UIP*)
Lemma match_val_single_constr_row 
  (t: term) {m: mut_adt} (m_in : mut_in_ctx m gamma)
  {a: alg_datatype} (a_in: adt_in_mut a m) {c: funsym} (c_in: constr_in_adt c a) 
  {args: list vty} (args_len: length args = length (m_params m))
  (Hty: term_has_type gamma t (vty_cons (adt_name a) args))
  (al1: arg_list (domain (dom_aux pd)) (sym_sigma_args c (map (v_subst vt) args)))
  (Ht: tm_semantic_constr t m_in a_in c_in args_len Hty al1)
  params tms 
  (Hp :  pattern_has_type gamma (Pconstr c params tms) (vty_cons (adt_name a) args)) 
  (Hty1 : term_has_type gamma t (vty_cons (adt_name a) args)) Heq
  (Hrow: row_typed (ty_subst_list (s_params c) args (s_args c)) tms):
  match_val_single gamma_valid pd pdf vt (vty_cons (adt_name a) args) (Pconstr c params tms) Hp 
    (term_rep gamma_valid pd pdf vt pf v t (vty_cons (adt_name a) args) Hty1) =
  matches_row (ty_subst_list (s_params c) args (s_args c))
    (cast_arg_list Heq al1) tms Hrow.
Proof.
  rewrite match_val_single_rewrite.
  set (ty1:= (vty_cons (adt_name a) args)) in *.
  generalize dependent (@is_vty_adt_some gamma ty1).
  generalize dependent (@adt_vty_length_eq gamma gamma_valid ty1).
  generalize dependent (@constr_length_eq gamma gamma_valid ty1).
  assert (Hisadt: is_vty_adt gamma ty1 = Some (m, a, args)) by
    (apply is_vty_adt_iff; auto).
  rewrite Hisadt.
  intros Hvslen1 Hvslen2 Hadtspec.
  destruct (Hadtspec m a args eq_refl)
    as [Htyeq [Hinmut Hinctx]].
  assert (Hinmut = a_in) by (apply bool_irrelevance).
  assert (Hinctx = m_in) by (apply bool_irrelevance).
  subst.
  simpl.
  generalize dependent (Hvslen2 m a args eq_refl
  (pat_has_type_valid gamma (Pconstr c params tms) ty1 Hp)).
  intros.
  assert (e = args_len) by (apply UIP_dec, Nat.eq_dec). subst.
  (*We need to know things about the [find_constr_rep]. *)
  case_find_constr.
  intros s.
  destruct s as [f' Hf']. destruct Hf' as [[f_in1 arg1] Haarg]. simpl in *; subst.
  (*Need info about how [tm_semantic_constr] interacts with this [find_constr_rep]*)
  unfold tm_semantic_constr in Ht.
  erewrite term_rep_irrel in Haarg.
  unfold ty1 in Haarg.
  rewrite Ht in Haarg.
  unfold dom_cast in Haarg.
  rewrite !scast_scast in Haarg. 
  revert Haarg.
  match goal with |- context [scast ?E ?x] => generalize dependent E end.
  intros Heq1.
  rewrite scast_refl_uip; intros Hconstr.
  (*Then, know f' = c and arg1 = al by disjointness/injectivity*)
  destruct (funsym_eq_dec f' c); [|apply constr_rep_disjoint in Hconstr; auto; contradiction].
  subst.
  assert (f_in1 = c_in) by (apply bool_irrelevance). subst.
  apply constr_rep_inj in Hconstr; auto; [|apply (gamma_all_unif gamma_valid); auto].
  subst. clear Heq1. simpl.
  (*Now it is simple: prove that [matches_row] and [iter_arg_list] are equal
    (TODO: do we really need both? Prob not) *)
  match goal with | |- context [cast_arg_list ?Heq ?x] => generalize dependent Heq end.
  (*Why we needed to state the lemma with this exact type/cast for the matches_row: we need
    these two equality proofs to be equal - we CANNOT have casting
    Reason: in [match_val_single], it is NOT enough to know that val(ty1) = val(ty2), the
    types must be equal (say, if one is a variable that maps to same ADT as another, different
    result from matching)*)
  intros Heq1. assert (Heq = Heq1) by (apply UIP_dec, list_eq_dec, sort_eq_dec).
  subst.
  apply iter_arg_list_matches_row.
Qed.

(*4. If the [term_rep] matches a different constructor [match_val_single] gives None*)
Lemma match_val_single_constr_nomatch
  (t: term) {m: mut_adt} (m_in : mut_in_ctx m gamma)
  {a: alg_datatype} (a_in: adt_in_mut a m) {c1 c2: funsym} (c1_in: constr_in_adt c1 a) 
  {args: list vty} (args_len: length args = length (m_params m))
  (Hty: term_has_type gamma t (vty_cons (adt_name a) args))
  (al1: arg_list (domain (dom_aux pd)) (sym_sigma_args c1 (map (v_subst vt) args)))
  (Ht: tm_semantic_constr t m_in a_in c1_in args_len Hty al1)
  params tms 
  (Hp :  pattern_has_type gamma (Pconstr c2 params tms) (vty_cons (adt_name a) args)) 
  (Hty1 : term_has_type gamma t (vty_cons (adt_name a) args)) 
  (Hneq: c1 <> c2):
  match_val_single gamma_valid pd pdf vt (vty_cons (adt_name a) args) (Pconstr c2 params tms) Hp 
    (term_rep gamma_valid pd pdf vt pf v t (vty_cons (adt_name a) args) Hty1) =
  None.
Proof.
  rewrite match_val_single_rewrite.
  set (ty1:= (vty_cons (adt_name a) args)) in *.
  generalize dependent (@is_vty_adt_some gamma ty1).
  generalize dependent (@adt_vty_length_eq gamma gamma_valid ty1).
  generalize dependent (@constr_length_eq gamma gamma_valid ty1).
  assert (Hisadt: is_vty_adt gamma ty1 = Some (m, a, args)) by
    (apply is_vty_adt_iff; auto).
  rewrite Hisadt.
  intros Hvslen1 Hvslen2 Hadtspec.
  destruct (Hadtspec m a args eq_refl)
    as [Htyeq [Hinmut Hinctx]].
  assert (Hinmut = a_in) by (apply bool_irrelevance).
  assert (Hinctx = m_in) by (apply bool_irrelevance).
  subst.
  simpl.
  generalize dependent (Hvslen2 m a args eq_refl
  (pat_has_type_valid gamma (Pconstr c2 params tms) ty1 Hp)).
  intros.
  assert (e = args_len) by (apply UIP_dec, Nat.eq_dec). subst.
  (*We need to know things about the [find_constr_rep]. *)
  case_find_constr.
  intros s.
  destruct s as [f' Hf']. destruct Hf' as [[f_in1 arg1] Haarg]. simpl in *; subst.
  (*Need info about how [tm_semantic_constr] interacts with this [find_constr_rep]*)
  unfold tm_semantic_constr in Ht.
  erewrite term_rep_irrel in Haarg.
  unfold ty1 in Haarg.
  rewrite Ht in Haarg.
  unfold dom_cast in Haarg.
  rewrite !scast_scast in Haarg. 
  revert Haarg.
  match goal with |- context [scast ?E ?x] => generalize dependent E end.
  intros Heq1.
  rewrite scast_refl_uip; intros Hconstr.
  (*Result follows by disjointness*)
  destruct (funsym_eq_dec f' c2); auto.
  subst. apply constr_rep_disjoint in Hconstr; auto. contradiction.
Qed.

(*3. We can reverse the lists in [match_row]; the result is a permutation*)

(*The relationship is annoying: they are permutations*)
Lemma matches_row_rev tys al ps Hty1 Hty2:
  opt_related (@Permutation _) 
    (matches_row tys al ps Hty1)
    (matches_row (rev tys) 
    (cast_arg_list (eq_sym (map_rev _ _)) (hlist_rev _ _ al)) (rev ps) Hty2).
Proof.
  generalize dependent (eq_sym (map_rev (v_subst vt) tys)).
  revert Hty1 Hty2.
  revert ps. induction tys as [| ty1 tys IH]; simpl; intros [| p1 ps]; simpl; intros; auto;
  try solve[inversion Hty1];  unfold opt_related; simp matches_row; auto.
  assert (Hty2':=Hty2).
  assert (Hlen: length ps = length tys). {
    inversion Hty1; subst. eapply Forall2_length; eauto.
  }
  apply Forall2_app_inv in Hty2'; [| solve_len].
  destruct Hty2' as [Hrowrev Hrowhd].
  (*Need correct typecast*)
  set (h2:=(HL_cons (domain (dom_aux pd)) (v_subst vt ty1) (map (v_subst vt) nil) 
    (hlist_hd al) (HL_nil _)) : arg_list (domain (dom_aux pd)) (map (v_subst vt) [ty1])).

  rewrite matches_row_app with (h1:=cast_arg_list (eq_sym (map_rev _ _)) 
    (hlist_rev _ (map (v_subst vt) tys) (hlist_tl al)))(h2:=h2)(Hr2:=Hrowrev)(Hr3:=Hrowhd); auto; [| | solve_len].
  2: {
    rewrite hlist_app_cast1. rewrite !cast_arg_list_compose.
    simpl in *. rewrite (hlist_inv al) at 1.
    simp hlist_rev. simpl.
    apply cast_arg_list_eq.
  }
  simp matches_row. simpl.
  (*Using the IH is a bit complicated*)
  unfold option_bind.
  specialize (IH (hlist_tl al) ps (Forall2_inv_tail Hty1) Hrowrev (eq_sym (map_rev (v_subst vt) tys))).
  unfold opt_related in IH.
  (*Now lots of destructing*)
  destruct (matches_row tys (hlist_tl al) ps
    (Forall2_inv_tail Hty1)) as [m1|] eqn : Hmatch1.
  - destruct (matches_row (rev tys)
      (cast_arg_list (eq_sym (map_rev (v_subst vt) tys))
      (hlist_rev (domain (dom_aux pd)) (map (v_subst vt) tys)
      (hlist_tl al)))
      (rev ps) Hrowrev) as [m2|] eqn : Hmatch2; [|contradiction].
    (*Left with only [match_val_single]*)
    rewrite match_val_single_irrel with (Hval2:=Forall2_inv_head Hrowhd).
    destruct (match_val_single gamma_valid pd pdf vt ty1 p1
      (Forall2_inv_head Hrowhd) (hlist_hd al)); auto.
    rewrite app_nil_r. eapply Permutation_trans. apply Permutation_app_comm.
    apply Permutation_app_tail; assumption.
  - destruct (matches_row (rev tys)
      (cast_arg_list (eq_sym (map_rev (v_subst vt) tys))
      (hlist_rev (domain (dom_aux pd)) (map (v_subst vt) tys)
      (hlist_tl al)))
      (rev ps) Hrowrev) as [m2|] eqn : Hmatch2; [contradiction|].
    destruct (match_val_single gamma_valid pd pdf vt ty1 p1
      (Forall2_inv_head Hty1) (hlist_hd al)); auto.
Qed.

(*5. If a pattern list is all wilds, everything matches it and gives no bound vars*)
Lemma matches_row_all_wilds tys h ps Hty (Hall: forall p, In p ps -> p = Pwild):
  matches_row tys h ps Hty = Some [].
Proof.
  generalize dependent ps.
  induction tys; simpl in *; intros [| p ps]; intros; try solve[inversion Hty]; auto.
  simp matches_row. simpl in Hall.
  assert (p = Pwild) by (apply Hall; auto). subst. simpl.
  rewrite IHtys; auto.
Qed.

(*An easy cast, just a bunch of maps, revs, and apps together*)
Lemma spec_prop_cast c  args tys : 
  length (s_params c) = length args ->
  rev (sym_sigma_args c (map (v_subst vt) args)) ++
map (v_subst vt) tys =
map (v_subst vt)
  (rev (ty_subst_list (s_params c) args (s_args c)) ++
tys).
Proof.
  intros Hlen.
  unfold sym_sigma_args, ty_subst_list, ty_subst_list_s.
  rewrite map_app. f_equal.
  rewrite !map_rev, !map_map. f_equal. apply map_ext.
  intros. symmetry. apply funsym_subst_eq; auto. apply s_params_Nodup.
Qed.


(*And we can finally prove the result for S(c, P)*)
Theorem spec_match_eq 
  (*Info about first term*)
  (t: term) {m: mut_adt} (m_in : mut_in_ctx m gamma)
  {a: alg_datatype} (a_in: adt_in_mut a m) {c: funsym} (c_in: constr_in_adt c a) 
  {args: list vty} (args_len: length args = length (m_params m))
  (params_len: length (s_params c) = length args)
  (Hty: term_has_type gamma t (vty_cons (adt_name a) args))
  (al1: arg_list (domain (dom_aux pd)) (sym_sigma_args c (map (v_subst vt) args)))
  (Ht: tm_semantic_constr t m_in a_in c_in args_len Hty al1)
  (*Info about rest of terms*)
  (ts: list term) (tys: list vty)
  (Htsty: Forall2 (term_has_type gamma) (t :: ts) (vty_cons (adt_name a) args :: tys)) (*duplicate proof for irrelevance*)
  (*Info about pattern matrix*)
  (P: pat_matrix) (Hpsimp: simplified P)
  (Htyp: pat_matrix_typed (vty_cons (adt_name a) args :: tys) P)
  (Htyp': pat_matrix_typed (rev (ty_subst_list (s_params c) args (s_args c)) ++ tys)
    (spec P c)):

  matches_matrix_tms v (t :: ts) (vty_cons (adt_name a) args :: tys) P
    Htsty Htyp =

  matches_matrix v
  (*Type list more complicated: args of c + rest*)
  (rev (ty_subst_list (s_params c) args (s_args c)) ++ tys)
    (cast_arg_list (spec_prop_cast c args _ params_len)
   (hlist_app _ _ _ (hlist_rev _ _ al1) (terms_to_hlist v ts tys (Forall2_inv_tail Htsty))))
    (spec P c) Htyp'.
Proof.
  unfold matches_matrix_tms.
  generalize dependent (spec_prop_cast c args tys params_len).
  generalize dependent (Forall2_inv_tail Htsty).
  revert Htsty Htyp Htyp'.
  unfold matches_matrix_tms. 
  induction P as [| rhd rtl]; intros; simpl; simp matches_matrix; [reflexivity|].
  destruct rhd as [ps a1]; simpl.

  (*Useful "inversion" on equality proof*)
  assert (Heq1: rev (sym_sigma_args c (map (v_subst vt) args)) =
          (map (v_subst vt) (rev (ty_subst_list (s_params c) args (s_args c))))).
  {
    rewrite map_app in e.
    apply app_inv_tail in e. auto.
  }
  assert (Heq2: sym_sigma_args c (map (v_subst vt) args) =
          map (v_subst vt) (ty_subst_list (s_params c) args (s_args c))).
  {
    rewrite map_app in e. apply app_inv_tail in e.
    rewrite map_rev in e.
    apply CommonList.rev_inj in e. auto.
  }

  (*Case on patterns*)
  destruct ps as [| phd ptl].
  - assert (Htyph:=Htyp). apply pat_matrix_typed_head in Htyph.
    simpl in Htyph. destruct Htyph as [Hrow _]; inversion Hrow. 
  - destruct phd as [| f' params tms | | |]; try discriminate.
    + (*Interesting case: Pconstr*) 
      revert Htyp'. simpl.

      (*Info from typing*)
      assert (Htyt:=pat_matrix_typed_head Htyp).
      destruct Htyt as [Htyr Htyt]; simpl in Htyr.
      assert (Htyconstr:=Forall2_inv_head Htyr).
      assert (Hlentms: length (s_args f') = length tms) by (inversion Htyconstr; auto).

      destruct (funsym_eqb_spec f' c); subst; simpl; intros.
      -- simp matches_matrix. simpl.
        (*Step 1: decompose [matches_row] and [app]*)
      
        (*Get [row_typed] info*)
        assert (Hr1:=pat_matrix_typed_head Htyp'). simpl in Hr1.
        destruct Hr1 as [Hr1 _].
        apply Forall2_app_inv in Hr1.
        2: {  unfold sorts_to_tys, ty_subst_list. solve_len. }
        destruct Hr1 as [Hrow1 Hrow2].
        (*Now we can split the [app]*)
        rewrite matches_row_app with(h1:=cast_arg_list Heq1 (hlist_rev _ _ al1))(h2:=terms_to_hlist v ts tys f)
          (Hr2:=Hrow1)(Hr3:=Hrow2).
        (*We prove the easy goals first*)
        2: rewrite hlist_app_cast1, cast_arg_list_compose; apply cast_arg_list_eq.
        2: unfold ty_subst_list; solve_len.
        2: symmetry; apply (Forall2_length (Forall2_inv_tail Htyr)).

        (*Now we need to transform the [matches_row] into the corresponding
          [match_val_single] and the rest of the row; we then prove that
          [match_val_single] for a constructor is equivalent to [matches_row] 
          on the arg_list*)
        simp matches_row. simp terms_to_hlist. simpl hlist_hd.
        (*Coq is just awful at unifying things; this is really annoying*)
        match goal with
        | |- context [match_val_single ?v ?pd ?pdf ?vt ?ty ?p ?Hp (term_rep _ _ _ _ _ _ _ _ ?Hty)] =>
          pose proof (match_val_single_constr_row _ m_in a_in c_in args_len _ al1 Ht params tms
          Hp Hty Heq2 (Forall2_rev_inv Hrow1)) as Hconstreq; rewrite Hconstreq
        end.
        (*Remove the [rev] by using the permutation result*)
        pose proof (matches_row_rev (ty_subst_list (s_params c) args (s_args c)) 
          (cast_arg_list Heq2 al1) tms (Forall2_rev_inv Hrow1)
          Hrow1) as Hrev.
        unfold opt_related in Hrev.
        assert (Heqarglist: cast_arg_list (eq_sym (map_rev _ _))
            (hlist_rev _  _ (cast_arg_list Heq2 al1)) =
            cast_arg_list Heq1 (hlist_rev _ _ al1)).
          {
            rewrite hlist_rev_cast.
            rewrite cast_arg_list_compose.
            apply cast_arg_list_eq.
          }
        rewrite Heqarglist in Hrev. clear Heqarglist.
        (*Now, time to destruct everything*)
        destruct (matches_row (ty_subst_list (s_params c) args (s_args c))
          (cast_arg_list Heq2 al1) tms (Forall2_rev_inv Hrow1)) as [m1 |] eqn : Hmatch1.
        ++ simpl.
          destruct (matches_row
            (rev (ty_subst_list (s_params c) args (s_args c)))
            (cast_arg_list Heq1
            (hlist_rev (domain (dom_aux pd))
            (sym_sigma_args c (map (v_subst vt) args)) al1))
            (rev tms) Hrow1) as [m2 |] eqn : Hm2; [| contradiction].
          simpl.
          (*Now, some proof irrelevance to show equality of the next two matches*)
          rewrite terms_to_hlist_irrel with (H2:=f).
          rewrite matches_row_irrel with (Hr2:=Hrow2).
          destruct (matches_row tys (terms_to_hlist v ts tys f) ptl Hrow2) as [m3|] eqn : Hmatch3; simpl.
          ** (*Here, use permutation result*) 
            assert (Hn: NoDup (map fst m1)). {
              eapply match_val_single_nodup. apply Hconstreq.
            } 
            f_equal. rewrite gen_rep_irrel with (Hty2:=(Forall_inv (proj2 Htyp'))). 
            apply gen_rep_change_vv.
            intros x Hinx.
            apply extend_val_app_perm; assumption.
          ** (*IH case*)
            erewrite <- IHrtl with (Htyp:=(pat_matrix_typed_tail Htyp))(Htsty:=Htsty); [| apply 
              (simplified_tl _ _ Hpsimp)].
            simp terms_to_hlist.
            erewrite terms_to_hlist_irrel; reflexivity.
        ++ (*first match is None - by Hrev, know second is as well*)
          destruct (matches_row
            (rev (ty_subst_list (s_params c) args (s_args c)))
            (cast_arg_list Heq1
            (hlist_rev (domain (dom_aux pd))
            (sym_sigma_args c (map (v_subst vt) args)) al1))
            (rev tms) Hrow1) as [m2 |] eqn : Hm2; [contradiction|].
          simpl.
          (*Another IH case*)
          erewrite <- IHrtl with (Htyp:=(pat_matrix_typed_tail Htyp))(Htsty:=Htsty); [| apply 
              (simplified_tl _ _ Hpsimp)].
          simp terms_to_hlist.
          erewrite terms_to_hlist_irrel; reflexivity. Unshelve. auto.
      -- (*funsym doesn't match - here, we do not have a match with the [match_val_single]*)
        simp matches_row terms_to_hlist. simpl hlist_hd. 
        (*Use nomatch result*) 
        rewrite match_val_single_constr_nomatch with (m_in := m_in) (a_in:=a_in)(c1_in:=c_in)
          (args_len:=args_len)(al1:=al1)(Hty:=Hty); auto.
        simpl.
        (*Thus, IH case*)
        erewrite <- IHrtl with (Htyp:=(pat_matrix_typed_tail Htyp))(Htsty:=Htsty); [| apply 
              (simplified_tl _ _ Hpsimp)].
        simp terms_to_hlist.
        erewrite terms_to_hlist_irrel; reflexivity. Unshelve. auto.
    + (*Pwild case*) 
      (*Idea: we add n terms and n wilds, that is the same (always matches) as 1 term and 1 wild*)
      simp matches_row matches_matrix. simpl.
      (*First, some typing*)
      assert (Htyp'':=Htyp').
      apply pat_matrix_typed_head in Htyp''. simpl in Htyp''.
      destruct Htyp'' as [Hrowty _].
      apply Forall2_app_inv in Hrowty.
      2: unfold ty_subst_list; solve_len.
      destruct Hrowty as [Hr1 Hr2].
      (*Again decompose the row via append*)
      simpl.
      rewrite matches_row_app  with (h1:=cast_arg_list Heq1 (hlist_rev (domain (dom_aux pd))
          (sym_sigma_args c (map (v_subst vt) args)) al1) )
        (h2:=(terms_to_hlist v ts tys f))(Hr2:=Hr1)(Hr3:=Hr2).
      (*First, prove the side conditions*)
      2: {
        rewrite (hlist_app_cast1) with (Heq:=Heq1).
        rewrite !cast_arg_list_compose.
        apply cast_arg_list_eq.
      }
      2: unfold ty_subst_list; solve_len.
      2: apply Forall2_length in Hr2; auto.
      (*Then simplify first because all wilds*)
      rewrite matches_row_all_wilds with (ps:=(repeat Pwild (Datatypes.length (s_args c)))); [| apply repeat_spec].
      simpl.
      (*A bit of simplification to get things together*)
      rewrite terms_to_hlist_tl.
      rewrite terms_to_hlist_irrel with (H2:=f).
      rewrite matches_row_irrel with (Hr2:=Hr2).
      destruct (matches_row tys (terms_to_hlist v ts tys f) ptl Hr2) as [m1|] eqn : Hmatch1; simpl; auto.
      f_equal. apply gen_rep_irrel.
Qed.

End SpecProof.

(*The proof for the default matrix is much easier*)
Theorem default_match_eq 
  (*Info about first term*)
  (t: term) {m: mut_adt} (m_in : mut_in_ctx m gamma)
  {a: alg_datatype} (a_in: adt_in_mut a m) {c: funsym} (c_in: constr_in_adt c a) 
  {args: list vty} (args_len: length args = length (m_params m))
  (params_len: length (s_params c) = length args)
  (Hty: term_has_type gamma t (vty_cons (adt_name a) args))
  (al1: arg_list (domain (dom_aux pd)) (sym_sigma_args c (map (v_subst vt) args)))
  (Ht: tm_semantic_constr t m_in a_in c_in args_len Hty al1)
  
  (*Info about rest of terms*)
  (ts: list term) (tys: list vty)
  (Htsty: Forall2 (term_has_type gamma) (t :: ts) (vty_cons (adt_name a) args :: tys)) (*duplicate proof for irrelevance*)
  (*Info about pattern matrix*)
  (P: pat_matrix) (Hpsimp: simplified P)
  (c_notin: constr_at_head_ex c P = false)
  (Htyp: pat_matrix_typed (vty_cons (adt_name a) args :: tys) P)
  (Htyp': pat_matrix_typed tys (default P)):

  matches_matrix_tms v (t :: ts) (vty_cons (adt_name a) args :: tys) P
    Htsty Htyp =

  matches_matrix v tys (terms_to_hlist v ts tys (Forall2_inv_tail Htsty)) (default P) Htyp'.
Proof.
  unfold matches_matrix_tms.
  generalize dependent (Forall2_inv_tail Htsty).
  revert Htsty Htyp Htyp'.
  induction P as [| rhd rtl]; intros; simpl; simp matches_matrix; [reflexivity|].
  destruct rhd as [ps a1]; simpl.
  (*Case on patterns*)
  destruct ps as [| phd ptl].
  - assert (Htyph:=Htyp). apply pat_matrix_typed_head in Htyph.
    simpl in Htyph. destruct Htyph as [Hrow _]; inversion Hrow. 
  - destruct phd as [| f' params tms | | |]; try discriminate.
    + (*Pconstr*)
      simpl in c_notin. apply orb_false_iff in c_notin.
      unfold constr_at_head in c_notin.
      simpl in c_notin.
      destruct c_notin as [c_eq c_notin].
      destruct (funsym_eqb_spec f' c); try discriminate.
      simp matches_row.
      (*Use fact that different constructor gives None*)
      rewrite terms_to_hlist_equation_4 at 1. simpl hlist_hd.
      rewrite match_val_single_constr_nomatch with (m_in:=m_in)(a_in:=a_in)(c1_in:=c_in)
        (args_len:=args_len)(Hty:=Hty)(al1:=al1); auto.
      simpl. apply IHrtl; auto.
    + (*Pwild*)
      simp matches_row. simpl.
      rewrite terms_to_hlist_tl.
      simp matches_matrix; simpl.
      rewrite terms_to_hlist_irrel with (H2:=f).
      rewrite matches_row_irrel with (Hr2:=(Forall_inv (proj1 Htyp'))). simpl.
      simpl in *.
      unfold option_bind.
      match goal with |- context [matches_row ?tys ?hl ?ptl ?H] =>
        destruct (matches_row tys hl ptl H) as [m1|] eqn : Hmatch1
      end.
      * match goal with |- context [matches_row ?tys ?hl ?ptl ?H] =>
          replace (matches_row tys hl ptl H) with (Some m1) by (symmetry; apply Hmatch1); auto
        end.
        f_equal. apply gen_rep_irrel.
      * match goal with |- context [matches_row ?tys ?hl ?ptl ?H] =>
          replace (matches_row tys hl ptl H) with (@None (list (vsymbol * {s: sort & domain (dom_aux pd) s }))) by (symmetry; apply Hmatch1); auto
        end.
Qed.

(*Another version: if the term is not a constructor at all*)
Theorem default_match_eq_nonadt 
  (*Info about first term*)
  (t: term) (ty: vty) (Htm: term_has_type gamma t ty) (Hnotadt: is_vty_adt gamma ty = None)
  (*Info about rest of terms*)
  (ts: list term) (tys: list vty)
  (Htsty: Forall2 (term_has_type gamma) (t :: ts) (ty :: tys)) (*duplicate proof for irrelevance*)
  (*Info about pattern matrix*)
  (P: pat_matrix) (Hpsimp: simplified P)
  (Htyp: pat_matrix_typed (ty :: tys) P)
  (Htyp': pat_matrix_typed tys (default P)):
   matches_matrix_tms v (t :: ts) (ty :: tys) P
    Htsty Htyp =

  matches_matrix v tys (terms_to_hlist v ts tys (Forall2_inv_tail Htsty)) (default P) Htyp'.
Proof.
  unfold matches_matrix_tms.
  generalize dependent (Forall2_inv_tail Htsty).
  revert Htsty Htyp Htyp'.
  induction P as [| rhd rtl]; intros; simpl; simp matches_matrix; [reflexivity|].
  destruct rhd as [ps a1]; simpl.
  (*Case on patterns*)
  destruct ps as [| phd ptl].
  - assert (Htyph:=Htyp). apply pat_matrix_typed_head in Htyph.
    simpl in Htyph. destruct Htyph as [Hrow _]; inversion Hrow. 
  - destruct phd as [| f' params tms | | |]; try discriminate.
    + (*Pconstr*)
      simp matches_row. rewrite terms_to_hlist_equation_4 at 1. simpl hlist_hd.
      rewrite match_val_single_rewrite.
      generalize dependent (@is_vty_adt_some gamma ty).
      generalize dependent (@adt_vty_length_eq gamma gamma_valid ty).
      generalize dependent (@constr_length_eq gamma gamma_valid ty).
      rewrite Hnotadt. simpl. auto. 
    + (*Pwild*)
      (*Same as above, should change*)
      simp matches_row. simpl.
      rewrite terms_to_hlist_tl.
      simp matches_matrix; simpl.
      rewrite terms_to_hlist_irrel with (H2:=f).
      rewrite matches_row_irrel with (Hr2:=(Forall_inv (proj1 Htyp'))). simpl.
      simpl in *.
      unfold option_bind.
      match goal with |- context [matches_row ?tys ?hl ?ptl ?H] =>
        destruct (matches_row tys hl ptl H) as [m1|] eqn : Hmatch1
      end.
      * match goal with |- context [matches_row ?tys ?hl ?ptl ?H] =>
          replace (matches_row tys hl ptl H) with (Some m1) by (symmetry; apply Hmatch1); auto
        end.
        f_equal. apply gen_rep_irrel.
      * match goal with |- context [matches_row ?tys ?hl ?ptl ?H] =>
          replace (matches_row tys hl ptl H) with (@None (list (vsymbol * {s: sort & domain (dom_aux pd) s }))) by 
          (symmetry; apply Hmatch1); auto
        end.
Qed.

(*The last big result we need before the main proof: simplifying the pattern matrix
  does not change the semantics*)


(*We need the condition that no variable free in the list of terms we match on
  also appears free in a pattern. To see why, consider:
   match Tvar y, Tvar z with
  | Pvar x, Pvar y -> f (x, y)
  end
  should be: f(y, z)
  But if we match by iterating over each term and binding in a "let", we get:
  let x = y in (let y = z in f(x, y))
  let (y = z in f(y, y)) -> f(z, z)*)

(*Two notions of disjointness*)

(* Definition pat_row_vars_disj (ts: list term) (ps: list pattern) : Prop :=
  disj (big_union vsymbol_eq_dec tm_fv ts) (big_union vsymbol_eq_dec pat_fv ps).

Definition pat_matrix_vars_disj (ts: list term) (P: pat_matrix) : Prop :=
  Forall (fun row => pat_row_vars_disj ts (fst row)) P. *)

Definition row_fv {B: Type} (row: list pattern * B) : list vsymbol :=
  big_union vsymbol_eq_dec pat_fv (fst row).
Definition pat_mx_fv (P: pat_matrix) : list vsymbol :=
  big_union vsymbol_eq_dec row_fv P.

Definition pat_row_vars_disj {B: Type} (ts: list term) (ps: list pattern * B) : Prop :=
  disj (big_union vsymbol_eq_dec tm_fv ts) (row_fv ps).

Definition pat_matrix_vars_disj (tms: list term) (P: pat_matrix) : Prop :=
  disj (big_union vsymbol_eq_dec tm_fv tms) (pat_mx_fv P).

Lemma pat_matrix_vars_disj_equiv tms P:
  (pat_matrix_vars_disj tms P) <-> Forall (pat_row_vars_disj tms) P.
Proof.
  unfold pat_matrix_vars_disj. split.
  - unfold pat_mx_fv. intros Hdisj.
    rewrite Forall_forall. intros row Hinrow x [Hxin1 Hinx2].
    revert Hxin1. rewrite <- big_union_elts. intros [t [Hint Hinx1]].
    apply (Hdisj x); split; auto. simpl_set. exists t; auto.
    simpl_set. exists row. split; auto.
  - intros Hall. intros x [Hinx1 Hinx2].
    unfold pat_mx_fv in Hinx2.
    revert Hinx2. rewrite <- big_union_elts.
    intros [row [Hinrow Hinx2]].
    rewrite Forall_forall in Hall.
    apply Hall in Hinrow.
    apply (Hinrow x). auto.
Qed.

Lemma pat_matrix_vars_disj_inv_tail tms p P:
  pat_matrix_vars_disj tms (p :: P) ->
  pat_matrix_vars_disj tms P.
Proof.
  rewrite !pat_matrix_vars_disj_equiv. intros Hall; inversion Hall; auto.
Qed.

(*The interesting part: expanding with [simplify_single] is the same as matching the
  row, then substituting*)
Lemma simplify_single_match_eq t ts ty1 tys Htmty (row : list pattern * gen_term b) Hp1 Hp2
  (Htyrow: gen_typed gamma b (snd row) ret_ty)
  (Htty: term_has_type gamma t ty1)
  (Hvars: pat_row_vars_disj (t :: ts) row):
  opt_related (fun d l => d = gen_rep (extend_val_with_list pd vt v l) ret_ty (snd row) Htyrow) 
  (matches_matrix v (ty1 :: tys) (terms_to_hlist v (t :: ts) (ty1 :: tys) Htmty)
    (simplify_single gen_let t row) Hp1)
  (matches_row (ty1 :: tys) (terms_to_hlist v (t :: ts) (ty1 :: tys) Htmty) (fst row) Hp2).
Proof.
  destruct row as [row a]; simpl in *.
  destruct row as [| rhd rtl]; simpl in *.
  - simp matches_matrix; simpl.
    inversion Hp2.
  - simp terms_to_hlist matches_row. simpl hlist_hd.
    (*Let's try this*)
    generalize dependent a.
    induction rhd; auto; intros.
    + (*Pvar*) 
      simpl in *. simp matches_matrix; simpl. simp matches_row; simpl.
      assert (Hletty := proj2 (pat_matrix_typed_head Hp1)); simpl in Hletty.
      rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hp2)).
      destruct (matches_row _ _ rtl _) as [m1|] eqn : Hmatch1; simpl; auto.
      assert (Hty1: term_has_type gamma t (snd v0)). {
        apply gen_let_typed_inv in Hletty; apply Hletty.
      }
      erewrite gen_rep_let with (Hty1:=proj1 (gen_let_typed_inv _ Hletty))
        (Hty3:=Htyrow).
      apply gen_rep_change_vv.
      (*Prove that valuations are the same*)
      intros x Hinx.
      unfold substi. destruct (vsymbol_eq_dec x v0); subst.
      * unfold extend_val_with_list at 2. simpl.
          destruct (vsymbol_eq_dec v0 v0); try contradiction.
        simpl.
        assert (ty1 = (snd v0)). {
          inversion Hp2; subst. inversion H2; subst. reflexivity.
        }
        subst. destruct (sort_eq_dec (v_subst vt (snd v0))
          (v_subst vt (snd v0))); try contradiction.
        assert (e0 = eq_refl). apply UIP_dec. apply sort_eq_dec. subst.
        simpl. unfold dom_cast; simpl.
        rewrite term_rep_irrel with (Hty2:=(Forall2_inv_head Htmty)).
        apply tm_change_vv.
        intros v1 Hinv1.
        apply extend_val_notin.
        rewrite (matches_row_vars Hmatch1).
        unfold pat_row_vars_disj in Hvars.
        intros Hinv1'.
        apply (Hvars v1). unfold row_fv. simpl fst.
        rewrite !big_union_cons, !union_elts. auto.
      * unfold extend_val_with_list at 2. simpl.
        destruct (vsymbol_eq_dec x v0); subst; try contradiction.
        unfold extend_val_with_list. reflexivity.
    + (*Pconstr case*)
      (*constr not simplified so case is easy*)
      simpl simplify_aux.
      simpl hlist_tl. simpl map.
      simp matches_matrix.
      simpl fst. simpl snd.
      simp matches_row.
      simpl hlist_tl.
      simpl hlist_hd.
      rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hp2)).
      destruct (match_val_single _ _ _ _ _ _ _) as [m1|] eqn : Hmatch1; simpl; auto.
      rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hp2)).
      destruct (matches_row _ _ _ _) as [m2|] eqn : Hmatch2; simpl; auto.
      apply gen_rep_irrel.
    + (*Pwild case -easy*)
      simpl simplify_aux. simpl map.
      simp matches_matrix.
      simpl fst. simpl snd. 
      simp matches_row. simpl.
      rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hp2)).
      destruct (matches_row _ _ _ _) as [m1|] eqn : Hmatch1; simpl; auto.
      apply gen_rep_irrel.
    + (*Por case - interesting one*)
      generalize dependent Hp1.
      simpl simplify_aux.
      rewrite map_app. intros Hp1.
      assert (Hrtemp := (pat_matrix_typed_app_inv Hp1)).
      destruct Hrtemp as [Hr1 Hr2].
      rewrite matches_matrix_app with (Hp1:=Hr1)(Hp2:=Hr2).
      simpl hlist_tl.
      (*from IH*)
      assert (Hp2' : row_typed (ty1 :: tys) (rhd1 :: rtl)).
      {
        inversion Hp2; subst; constructor; auto.
        inversion H2; auto.
      }
      assert (Hdisj1: pat_row_vars_disj (t :: ts) (rhd1 :: rtl, a)). {
        clear -Hvars.
        unfold pat_row_vars_disj in *.
        unfold row_fv,fst in *.
        unfold disj in *.
        intros x [Hinx1 Hinx2].
        apply (Hvars x).
        simpl_set_small. destruct_all; split; auto.
      } 
      specialize (IHrhd1 Hp2' a Hr1 Htyrow Hdisj1).
      destruct (matches_matrix _ _ _ _ Hr1) as [m1 |] eqn : Hmatch1.
      * (*First pattern matches*) simpl.
        simpl in IHrhd1.
        (*Make everything in goal match IH, need to destruct, all other cases contradictions*)
        rewrite match_val_single_irrel with (Hval2:=Forall2_inv_head Hp2').
        destruct (match_val_single _ _ _ _ _ _ (Forall2_inv_head Hp2') _) as [m2 |] eqn : Hmatch2;
        [|contradiction].
        simpl in IHrhd1 |- *.
        rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hp2')).
        destruct (matches_row _ _ rtl _) as [m3 |] eqn : Hmatch3; [|contradiction].
        simpl in IHrhd1 |- *. apply IHrhd1.
      * (*First pattern does not match - use second IH similarly*)
        assert (Hp2'': row_typed (ty1 :: tys) (rhd2 :: rtl)). {
          inversion Hp2; subst; constructor; auto.
          inversion H2; auto.
        }
        assert (Hdisj2: pat_row_vars_disj (t :: ts) (rhd2 :: rtl, a)). {
          clear -Hvars.
          unfold pat_row_vars_disj in *.
          unfold row_fv, fst in *.
          unfold disj in *.
          intros x [Hinx1 Hinx2].
          apply (Hvars x).
          simpl_set_small. destruct_all; split; auto.
        }
        specialize (IHrhd2 Hp2'' a Hr2 Htyrow Hdisj2).
        simpl hlist_tl in *.
        destruct (matches_matrix _ _ _ _ Hr2) as [m2|] eqn : Hmatch2.
        --(*Second pattern matches*)
          simpl in *.
          (*Still need info from first IH - cannot match*)
          rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hp2')).
          destruct (match_val_single _ _ _ _ _ rhd1 (Forall2_inv_head Hp2') _) as [m3|] eqn : Hmatch3; simpl in *.
          ++ (*Get contradiction from first IH*)
            rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hp2')).
            destruct (matches_row _ _ rtl _) as [m4|] eqn : Hmatch4; simpl in *; [contradiction|].
            (*Now use second IH*)
            destruct (match_val_single _ _ _ _ _ rhd2 _ _) as [m5|] eqn : Hmatch5;
            simpl in IHrhd2; [|contradiction].
            erewrite matches_row_irrel in Hmatch4; rewrite Hmatch4 in IHrhd2.
            contradiction.
          ++ (*Otherwise rhd does not match - no more info from IH1. rest of case is like first*)
            rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hp2'')).
            destruct (match_val_single _ _ _ _ _ rhd2 _ _) as [m4|] eqn : Hmatch4; simpl in *;
            [|contradiction]. 
            rewrite matches_row_irrel with (Hr2:=Forall2_inv_tail Hp2'').
            destruct (matches_row _ _ rtl _) as [m5|] eqn : Hmatch5; [|contradiction].
            simpl in *. apply IHrhd2.
        -- (*Neither matches*)
          simpl in *.
          (*Use info from both IHs*)
          rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hp2')).
          destruct (match_val_single _ _ _ _ _ rhd1 _ _) as [m3|] eqn : Hmatch3; simpl in *.
          ++ (*If rhd1 matches, by IH1, rtl cannot*)
            rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hp2')).
            destruct (matches_row _ _ rtl _) as [m4|] eqn : Hmatch4; [contradiction| auto].
          ++ (*see if rh2 matches*) 
            rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hp2'')).
            destruct (match_val_single _ _ _ _ _ rhd2 _ _) as [m4|] eqn : Hmatch4; simpl in *; auto.
            (*If rh2 matches, rtl cannot by IH2*)
            rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hp2'')).
            destruct (matches_row _ _ rtl) as [m5|] eqn : Hmatch5; [contradiction| auto].
    + (*Pbind case - recursive + Pvar case*)
      simpl simplify_aux.
      assert (Hr2: row_typed (ty1 :: tys) (rhd :: rtl)). {
        inversion Hp2; subst; constructor; auto.
        inversion H2; subst; auto.
      }
      assert (Hdisj: pat_row_vars_disj (t :: ts) (rhd :: rtl, a)).
      {
        clear -Hvars.
        unfold pat_row_vars_disj in *.
        unfold row_fv, fst in *.
        unfold disj in *.
        intros x [Hinx1 Hinx2].
        apply (Hvars x).
        simpl_set_small. destruct_all; split; auto.
      } 
      assert (Htty': term_has_type gamma t (snd v0)). {
        inversion Hp2; subst.
        inversion H2; subst. auto.
      }
      assert (Hletty: gen_typed gamma b (gen_let v0 t a) ret_ty).
      {
        apply gen_let_ty; auto.
      }
      specialize (IHrhd Hr2 (gen_let v0 t a) Hp1 Hletty Hdisj).
      (*Now destruct LHS and use IH*)
      (*Coq has trouble again*)
      match goal with 
      | |- context [matches_matrix ?a ?b ?c ?d] => destruct (matches_matrix a b c d) as [m1|]
        eqn : Hmatch1; simpl in *
      end.
      * (*Case 1: LHS matches, by IH we know that RHS matches also*)
        rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hr2)).
        destruct (match_val_single _ _ _ _ _ rhd _ _) as [m2|] eqn : Hmatch2; simpl in *;[|contradiction].
        rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hr2)).
        destruct (matches_row _ _ rtl _) as [m3|] eqn : Hmatch3; simpl in *;[|contradiction].
        subst.
        rewrite gen_rep_let with (Hty1:=Htty')(Hty3:=Htyrow).
        (*Now deal with variable stuff*)
        apply gen_rep_change_vv.
        intros x Hinx.
        unfold substi.
        destruct (vsymbol_eq_dec x v0); subst.
        -- simpl. unfold extend_val_with_list at 2. simpl. destruct (vsymbol_eq_dec v0 v0); try contradiction; simpl.
          assert (ty1 = (snd v0)). {
            inversion Hp2; subst. inversion H2; subst. reflexivity.
          }
          subst. destruct (sort_eq_dec _ _); [| contradiction].
          assert (e0 = eq_refl). apply UIP_dec. apply sort_eq_dec. subst.
          simpl. unfold dom_cast; simpl.
          rewrite term_rep_irrel with (Hty2:=(Forall2_inv_head Htmty)).
          apply tm_change_vv.
          intros v1 Hinv1.
          apply extend_val_notin.
          rewrite map_app, in_app_iff.
          rewrite (matches_row_vars Hmatch3).
          rewrite <- (match_val_single_free_var _ _ _ _ _ _ _ _ _ _ Hmatch2).
          unfold pat_row_vars_disj in Hdisj.
          unfold row_fv, fst in Hdisj.
          intros Hinv1'.
          apply (Hdisj v1).
          rewrite !big_union_cons.
          rewrite !union_elts. auto.
        -- unfold extend_val_with_list at 2. simpl.
          destruct (vsymbol_eq_dec x v0); subst; try contradiction.
          unfold extend_val_with_list. reflexivity.
      * (*Case 2: LHS doesnt match. Show same for RHS*)
        rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hr2)).
        destruct (match_val_single _ _ _ _ _ rhd _ _) as [m2|] eqn : Hmatch2; simpl in *; [| auto].
        (*If rhd matches, know rtl does not*)
        rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hr2)).
        destruct (matches_row _ _ rtl _) as [m3|] eqn : Hmatch3; simpl in *; [contradiction| auto].
Qed.

(*And the full result*)
Theorem simplify_match_eq (t: term) (ts: list term) (tys: list vty) (P: pat_matrix)
  Htmty Hty1 Hty2
  (Hdisj: pat_matrix_vars_disj (t :: ts) P):
  matches_matrix_tms v (t :: ts) tys (simplify gen_let t P) Htmty Hty1 =
  matches_matrix_tms v (t :: ts) tys P Htmty Hty2.
Proof.
  revert Htmty Hty1 Hty2.
  induction P as [| rhd P' IH]; simpl; intros.
  - unfold simplify. simpl. apply matches_matrix_irrel.
  - unfold simplify in *. simpl.
    unfold matches_matrix_tms.
    simpl in Hty1.
    assert (Htemp:=pat_matrix_typed_app_inv Hty1).
    destruct Htemp as [Hp1 Hp2].
    rewrite matches_matrix_app with (Hp1:=Hp1)(Hp2:=Hp2).
    simp matches_matrix.
    destruct tys as [| ty1 tys]; [inversion Htmty|].
    assert (Hdisj1: pat_row_vars_disj (t :: ts) rhd ). {
      apply pat_matrix_vars_disj_equiv in Hdisj.
      inversion Hdisj; auto.
    }
    (*Bulk is [simplify_single_match_eq] can't rewrite bc not rewritable relation*)
    pose proof (simplify_single_match_eq t ts ty1 tys Htmty rhd Hp1 (Forall_inv (proj1 Hty2))
      (Forall_inv (proj2 Hty2)) (Forall2_inv_head Htmty) Hdisj1) as Hrelated.
    destruct (matches_matrix _ _ _ _ Hp1) as [m1 |] eqn : Hmatch1; simpl in *.
    + (*If LHS matches, easy from lemma*)
      destruct (matches_row _ _ (fst rhd) _) as [m2|] eqn : Hmatch2; [|contradiction].
      subst. reflexivity.
    + (*If LHS doesn't match, use lemma to show RHS doesn't, then use IH*)
      destruct (matches_row _ _ (fst rhd) _) as [m2|] eqn : Hmatch2;[contradiction|].
      apply IH.
      apply pat_matrix_vars_disj_inv_tail in Hdisj; auto.
Qed.

End SpecDefaultLemmas.

End PatSemanticsLemmas.

(*Proving the correctness of [compile]*)

Notation get_constructors := (get_constructors gamma).

(*Part 1: Lemmas for Typing Contradictions*)
(*We need to know that if e.g. populate_all gives None, this gives a contradiction
  with the well-typedeness of the pattern matrix. We need several results for this*)

(*If populate is None, there is a Pconstr that is not a constructor*)
Lemma populate_none_simpl (is_constr: funsym -> bool) acc p:
  simplified_aux p ->
  populate is_constr acc p = None ->
  exists c tys ps, p = Pconstr c tys ps /\ is_constr c = false.
Proof.
  destruct p; try discriminate. simpl. intros _.
  destruct acc as [css csl]; simpl.
  destruct (is_constr f) eqn : Hf.
  + destruct (amap_mem funsym_eq_dec f css ); discriminate.
  + intros _. exists f. exists l. exists l0. auto.
Qed.

(*Some results about [get_heads]*)

(*Anything in the result of [get_heads] is well-typed, assuming the matrix is*)
Lemma in_get_heads_tys (ty: vty) (tys: list vty) (P: pat_matrix) (p: pattern) l
  (Hp: pat_matrix_typed (ty :: tys) P)
  (Hheads: get_heads P = Some l)
  (Hinp: In p l):
  pattern_has_type gamma p ty.
Proof.
  generalize dependent l.
  induction P as [| [ps a] P' IH]; simpl; intros l.
  - inv Hsome. contradiction.
  - destruct ps as [| phd ptl]; [discriminate|].
    destruct (get_heads P') as [l'|]; [|discriminate].
    simpl. inv Hsome. simpl.
    intros [Hpeq | Hinp]; subst.
    + apply pat_matrix_typed_head in Hp.
      destruct Hp as [Hrow _].
      apply Forall2_inv_head in Hrow. auto.
    + apply pat_matrix_typed_tail in Hp. eauto.
Qed.


Lemma get_heads_simplified (rl: pat_matrix) l p:
  simplified rl ->
  get_heads rl = Some l ->
  In p l -> simplified_aux p.
Proof.
  generalize dependent l.
  induction rl as [| [ps a] rtl IH]; simpl; intros l.
  - intros _. inv Hsome. contradiction.
  - destruct ps as [| phd ptl]; [discriminate|].
    intros Hsimp. apply andb_prop in Hsimp.
    destruct Hsimp as [Hsimphd Hsimptl].
    destruct (get_heads rtl); simpl in *;[|discriminate].
    inv Hsome. simpl. intros [Hp | Hinp]; subst; eauto.
Qed.

Lemma get_heads_none_iff {B: Type} (l: list (list pattern * B)):
  get_heads l = None <-> existsb (fun x => null (fst x)) l.
Proof.
  induction l as [| [ps a] t IH]; simpl; auto.
  - split; discriminate.
  - destruct ps; simpl; auto.
    + split; auto.
    + destruct (get_heads t); simpl; auto.
      rewrite <- IH. split; discriminate.
Qed.

(*And a few more lemmas for typing contradictions*)
Lemma pat_matrix_typed_row_lengths tys rl p:
  pat_matrix_typed tys rl ->
  In p rl ->
  length (fst p) = length tys.
Proof.
  induction rl as [| h t IH]; simpl; auto; [contradiction|].
  intros Htyped. assert (Htl:=Htyped). apply pat_matrix_typed_head in Htyped.
  apply pat_matrix_typed_tail in Htl. destruct Htyped as [Hrow Hty].
  intros [Hhp | Hinp]; subst; eauto.
  apply Forall2_length in Hrow; auto.
Qed.

Lemma pat_matrix_typed_not_null {ty tys rl}:
  pat_matrix_typed (ty :: tys) rl ->
  existsb (fun x => null (fst x)) rl = false.
Proof.
  intros Htyped.
  destruct (existsb _ rl) eqn : Hex; auto.
  apply existsb_exists in Hex.
  destruct Hex as [row [Hinrow Hnullrow]].
  exfalso.
  apply pat_matrix_typed_row_lengths with (p:=row) in Htyped; auto.
  destruct (fst row); discriminate.
Qed.

(* Part 2: Results about [simplify] (disjointness, well-typed)*)
(*One of the first things we do is eliminate the [simplify], but we need some well-formedness
  results first*)


(*All variables in simplification are in original matrix - the converse does not hold*)
Lemma simplify_subset mk_let t rl:
  forall x, In x (pat_mx_fv (simplify mk_let t rl)) -> In x (pat_mx_fv rl).
Proof.
  intros x.
  induction rl as [| rhd rtl IH]; simpl; auto.
  unfold pat_mx_fv in *; simpl. unfold simplify in *. simpl.
  rewrite big_union_app. simpl_set_small.
  intros [Hinx | Hinx]; auto.
  (*The inner lemma we need*)
  clear -Hinx. destruct rhd as [[| phd ptl] a]; simpl; [contradiction|].
  unfold simplify_single in Hinx. unfold row_fv at 1. simpl.
  simpl_set_small.
  generalize dependent a.
  induction phd; simpl in *; intros; unfold row_fv in Hinx; simpl in Hinx; simpl_set_small;
  try (destruct Hinx as [Hinx | Hf]; [|contradiction]); simpl_set_small; auto.
  - rewrite map_app in Hinx. apply big_union_app in Hinx.
    simpl_set_small. destruct Hinx as [Hinx | Hinx]; auto.
    + apply IHphd1 in Hinx. destruct_all; auto.
    + apply IHphd2 in Hinx. destruct_all; auto.
  - apply IHphd in Hinx. destruct_all; auto.
Qed.

(*We need a stronger notion of disjointness: the names are disjoint, not just the variables*)

Definition pat_matrix_var_names_disj (tms: list term) (P: pat_matrix) :=
  disj (map fst (big_union vsymbol_eq_dec tm_fv tms)) (map fst (pat_mx_fv P)).

Lemma pat_matrix_var_names_vars_disj tms P:
  pat_matrix_var_names_disj tms P ->
  pat_matrix_vars_disj tms P.
Proof.
  apply disj_map_inv.
Qed.

Lemma pat_matrix_vars_subset tms P1 P2:
  (forall x, In x (pat_mx_fv P2) -> In x (pat_mx_fv P1)) (*could weaken to map fst i think*) ->
  pat_matrix_var_names_disj tms P1 -> 
  pat_matrix_var_names_disj tms P2.
Proof.
  intros Hall.
  unfold pat_matrix_var_names_disj.
  intros Hdisj x [Hx1 Hx2].
  rewrite in_map_iff in Hx1, Hx2.
  destruct Hx1 as [x1 [Hx Hinx1]]; subst.
  destruct Hx2 as [x2 [Hx Hinx2]]; subst.
  apply (Hdisj (fst x1)).
  rewrite !in_map_iff; split; [exists x1 | exists x2]; auto.
Qed.

(*And so we get the disjointness result we want*)
Lemma simplify_disj mk_let tms t rl:
  pat_matrix_var_names_disj tms rl ->
  pat_matrix_var_names_disj tms (simplify mk_let t rl).
Proof.
  apply pat_matrix_vars_subset.
  apply simplify_subset.
Qed.

(*[simplify] is well-typed if the original pattern matrix is and if the term has the 
  correct type*)
Lemma simplify_typed {tys t ty rl}:
  term_has_type gamma t ty ->
  pat_matrix_typed (ty :: tys) rl ->
  pat_matrix_typed (ty :: tys) (simplify gen_let t rl).
Proof.
  intros Htm.
  induction rl as [| rhd rtl IH].
  - unfold simplify. simpl. auto.
  - unfold simplify in *. simpl.
    intros Htyped.
    pose proof (pat_matrix_typed_head Htyped) as Hhd.
    pose proof (pat_matrix_typed_tail Htyped) as Htl.
    apply pat_matrix_typed_app; auto.
    clear -Hhd Htm.
    (*Inner result*)
    destruct Hhd as [Hrow Htm1].
    destruct rhd as [[| phd ptl] a]; simpl in *.
    + apply prove_pat_matrix_typed_cons; simpl; auto.
      inversion Hrow; subst.
    + assert (Hrowtl:=Hrow). apply Forall2_inv_tail in Hrowtl.
      apply Forall2_inv_head in Hrow. rename Hrow into Hphdty. simpl in Hphdty.
      generalize dependent a.
      induction phd; simpl in *; intros; try (apply prove_pat_matrix_typed_cons; simpl; auto);
      inversion Hphdty; subst;
      try(solve[constructor; auto]); try solve[apply pat_matrix_typed_nil];
      try solve[apply gen_let_ty; auto].
      * repeat(constructor; auto).
      * rewrite map_app. apply pat_matrix_typed_app; auto.
      * apply IHphd; auto. apply gen_let_ty; auto.
Qed.

(*Part 3: Typing for [default] and [spec]*)

(*First, prove equivalent to dispatch*)


(*Specialize is more complicated because we need some assumptions that will come
  from typing*)
(*Idea: need to show that lengths are the same, so need to know that whatever
  f maps to in (fst o) is actually in P. Thus, it is well-typed, so the lengths are equal.
  But the end result is that we have a functional spec that does NOT refer to o, t, etc at all*)
Lemma dispatch1_equiv_spec mk_let is_constr t {f tys o P}:
  simplified P ->
  populate_all is_constr P = Some o ->
  pat_matrix_typed tys P ->
  amap_mem funsym_eq_dec f (fst o) ->
  amap_get funsym_eq_dec (fst (dispatch1 mk_let t (fst o) P)) f = Some (spec P f).
Proof.
  intros Hsimp Hpop Hty Hinf.
  rewrite dispatch_equiv.
  unfold dispatch2. rewrite simplified_simplify; auto.
  rewrite amap_mem_spec in Hinf.
  destruct (amap_get funsym_eq_dec (fst o) f) as [ys|] eqn : Hget; [|discriminate].
  rewrite dispatch2_gen_fst_in with (ys:=ys); auto.
  2: {
    apply orb_true_iff. left. apply (populate_all_in _ _ _ f Hsimp Hpop).
    rewrite amap_mem_spec. rewrite Hget; auto.
  }
  unfold spec.
  replace (length ys) with (length (s_args f)); [auto|].
  (*The reason we need the typing*)
  pose proof (populate_all_in_strong _ _ _ _ _ Hsimp Hpop Hget) as Hex.
  apply existsb_exists in Hex.
  destruct Hex as [[ps a] [Hinrow Hconstr]].
  destruct Hty as [Hrows _].
  rewrite Forall_forall in Hrows.
  specialize (Hrows _ Hinrow).
  unfold constr_args_at_head in Hconstr.
  simpl in *.
  destruct ps as [| p ps]; [discriminate|].
  destruct p as [| c tys1 pats1 | | |]; try discriminate.
  inversion Hrows; subst.
  destruct (funsym_eqb_spec c f); try discriminate. subst.
  destruct (list_eqb_spec _ pattern_eqb_spec ys pats1); [|discriminate]. subst.
  inversion H1; subst; auto.
Qed.

(*Prove [disj] for default*)

Lemma default_vars_subset rl:
  sublist (pat_mx_fv (default rl)) (pat_mx_fv rl).
Proof.
  unfold sublist, pat_mx_fv. induction rl as [| [ps a] rtl IH]; auto.
  intros x. simpl.
  destruct ps as [| p ptl]; simpl; auto.
  destruct p; simpl; auto; intros Hinx; unfold row_fv at 1; simpl_set_small; auto.
  simpl fst. rewrite big_union_cons. simpl.
  unfold row_fv at 1 in Hinx; destruct_all; auto.
Qed.

Lemma disj_default t ts rl:
  pat_matrix_var_names_disj (t :: ts) rl ->
  pat_matrix_var_names_disj ts (default rl).
Proof.
  unfold pat_matrix_var_names_disj.
  intros Hdisj.
  eapply disj_sublist_lr.
  - apply Hdisj.
  - rewrite big_union_cons. apply sublist_map. apply union_sublist_r.
  - apply sublist_map. apply default_vars_subset.
Qed.

Lemma default_typed {t ts rl}:
  pat_matrix_typed (t :: ts) rl ->
  pat_matrix_typed ts (default rl).
Proof.
  induction rl as [| [ps a] rtl IH]; intros Hpat.
  - apply pat_matrix_typed_nil.
  - simpl.
    pose proof (pat_matrix_typed_tail Hpat) as Htl.
    pose proof (pat_matrix_typed_head Hpat) as Hhd; simpl in Hhd;
    destruct Hhd as [Hrow Hty].
    destruct ps as [| phd ptl]; auto.
    inversion Hrow; subst.
    destruct phd; auto.
    apply prove_pat_matrix_typed_cons; auto.
Qed.

(*Typing for [spec P c]*)
Lemma spec_typed P (f: funsym) ts tys args
  (Hf: Forall (valid_type gamma) (s_args f))
  (Hp: pat_matrix_typed (vty_cons ts args :: tys) P):
  pat_matrix_typed (rev (ty_subst_list (s_params f) args (s_args f)) ++ tys) (spec P f).
Proof.
  induction P as [| [ps a] rtl IH].
  - apply pat_matrix_typed_nil.
  - simpl.  pose proof (pat_matrix_typed_tail Hp) as Htl.
    pose proof (pat_matrix_typed_head Hp) as Hhd; simpl in Hhd;
    destruct Hhd as [Hrow Hty].
    destruct ps as [| phd ptl]; auto.
    inversion Hrow; subst.
    destruct phd as [| f1 tys1 ps1 | | |]; auto. 
    + (*constr case*)
      destruct (funsym_eqb_spec f1 f); auto. subst.
      apply prove_pat_matrix_typed_cons; auto. simpl.
      apply Forall2_app; auto.
      apply Forall2_rev.
      inversion H2; subst.
      unfold sigma in H3.
      destruct H13 as [m [a1 [m_in [a_in c_in]]]].
      rewrite (adt_constr_ret gamma_valid m_in a_in c_in) in H3.
      rewrite ty_subst_cons in H3.
      assert (Hparams: s_params f = m_params m) by
        apply (adt_constr_params gamma_valid m_in a_in c_in).
      rewrite Hparams in H3.
      assert (Heq: ts = adt_name a1 /\ args = tys1). {
        rewrite map_ty_subst_var in H3; auto.
        - inversion H3; subst; auto.
        - rewrite <- Hparams; auto.
        - rewrite <- Hparams. apply s_params_Nodup.
      }
      destruct Heq; subst; clear H3.
      (*And now we just have to unify the "Forall"s - should really make everything Forall2*) 
      (*replace (map vty_var (m_params m)) with (seq.map vty_var (m_params m)) in H3 by auto.*)
      rewrite <- Forall_forall in H11.
      apply Forall2_combine.
      split; auto. unfold ty_subst_list; solve_len.
    + apply prove_pat_matrix_typed_cons; auto. simpl.
      apply Forall2_app; auto.
      (*This is pretty easy because Pwild can have any (valid) type*)
      assert (Hval: Forall (valid_type gamma) (rev (ty_subst_list (s_params f) args (s_args f)))). {
        apply Forall_rev. unfold ty_subst_list. rewrite Forall_map.
        rewrite Forall_forall. intros x Hinx.
        apply valid_type_ty_subst; auto.
        - rewrite Forall_forall in Hf; auto.
        - inversion H2; subst. inversion H; subst. rewrite Forall_forall; auto.
      }
      assert (Hlen: length (repeat Pwild (Datatypes.length (s_args f))) =
        length (rev (ty_subst_list (s_params f) args (s_args f)))) by
        (unfold ty_subst_list; solve_len).
      clear -Hval Hlen.
      generalize dependent (rev (ty_subst_list (s_params f) args (s_args f))).
      simpl_len. generalize dependent (length (s_args f)).
      intros n l Hval Hn; subst. induction l; simpl; auto.
      inversion Hval; subst.
      do 2(constructor; auto).
Qed.

(*And a corollary for ADTs*)
Lemma spec_typed_adt {a m f} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (f_in: constr_in_adt f a)
  {P tys args}
  (Hp: pat_matrix_typed (vty_cons (adt_name a) args :: tys) P):
  pat_matrix_typed (rev (ty_subst_list (s_params f) args (s_args f)) ++ tys) (spec P f).
Proof.
  apply spec_typed with (ts:=adt_name a); auto.
  rewrite Forall_forall.
  apply (constr_ret_valid gamma_valid m_in a_in f_in).
Qed.

(*disj for [spec] - we need 2 results*)

Lemma spec_vars_subset rl f:
  sublist (pat_mx_fv (spec rl f)) (pat_mx_fv rl).
Proof.
  unfold sublist, pat_mx_fv. induction rl as [| [ps a] rtl IH]; auto.
  intros x. simpl.
  destruct ps as [| p ptl]; simpl; auto.
  destruct p as [| f1 tys ps | | |]; simpl; auto; intros Hinx; unfold row_fv at 1; simpl_set_small; auto.
  - (*Pconstr*) simpl fst. rewrite big_union_cons. simpl.
    destruct (funsym_eqb_spec f1 f); subst; auto.
    revert Hinx. simpl. unfold row_fv at 1; simpl.
    simpl_set_small.
    rewrite big_union_app. simpl_set_small.
    rewrite big_union_rev. intros; destruct_all; auto.
  - (*Pwild*) simpl fst.
    rewrite big_union_cons. revert Hinx. unfold row_fv at 1. simpl.
    rewrite big_union_app. simpl_set_small.
    assert (Hrep: (big_union vsymbol_eq_dec pat_fv
      (repeat Pwild (Datatypes.length (s_args f)))) = nil).
    {
      generalize dependent (length (s_args f)). clear.
      induction n; simpl; auto.
    }
    rewrite Hrep. simpl.
    intros; destruct_all; auto. contradiction.
Qed.

Lemma spec_names_subset rl f:
  sublist (map fst (pat_mx_fv (spec rl f))) (map fst (pat_mx_fv rl)).
Proof.
  apply sublist_map, spec_vars_subset.
Qed.

Lemma disj_spec {f args tms tl rl}:
  pat_matrix_var_names_disj
    (Tfun f args tms :: tl) rl ->
  pat_matrix_var_names_disj
    (rev tms ++ tl) (spec rl f).
Proof.
  unfold pat_matrix_var_names_disj.
  intros Hdisj.
  eapply disj_sublist_lr.
  - apply Hdisj.
  - rewrite big_union_cons. simpl.
    intros x. rewrite in_map_big_union_app, in_map_union. rewrite in_map_big_union_rev. auto.
  - apply spec_names_subset.
Qed.

Lemma disj_spec1 {f t tms tl rl}:
  pat_matrix_var_names_disj (t :: tl) rl ->
  disj (map fst (big_union vsymbol_eq_dec tm_fv tms)) (map fst (pat_mx_fv rl)) ->
  pat_matrix_var_names_disj (tms ++ tl) (spec rl f).
Proof.
  unfold pat_matrix_var_names_disj.
  unfold disj. rewrite big_union_cons. setoid_rewrite in_map_big_union_app.
  intros Hdisj1 Hdisj2 x [Hinx1 Hinx2].
  simpl_set_small.
  apply spec_names_subset in Hinx2.
  destruct Hinx1 as [Hinx1 | Hinx1]; [apply (Hdisj2 x) | apply (Hdisj1 x)]; simpl_set_small; auto.
  rewrite in_map_union. auto.
Qed.

(*Part 4: Proofs for [Tfun] case*)

(*NOTE: don't need but keep in case I add back full compile*)

(*Express [get_arg_list] via [terms_to_hlist]*)
Lemma get_arg_list_eq (pd: pi_dom) (pdf: pi_dom_full gamma pd)
  (pf: pi_funpred gamma_valid pd pdf) vt v (f: funsym) (ty: vty) (tys: list vty) (tms: list term) 
  (Hty: term_has_type gamma (Tfun f tys tms) ty) Hp Hlents Hlenvs Hall Htms constrs_len:
  get_arg_list pd vt tys tms (term_rep gamma_valid pd pdf vt pf v) Hp Hlents Hlenvs Hall =
  cast_arg_list  (eq_sym (sym_sigma_args_map vt f tys constrs_len))
    (terms_to_hlist pd pdf pf vt v tms ((ty_subst_list (s_params f) tys (s_args f))) Htms).
Proof.
  revert Hp Hlents Hlenvs Hall Htms.
  generalize dependent (eq_sym (sym_sigma_args_map vt f tys constrs_len)).
  unfold sym_sigma_args.
  generalize dependent (s_args f).
  intros args; revert args. clear.
  induction tms as [| thd ttl IH]; simpl; intros.
  - destruct args as [| ahd atl]; auto; [| inversion Htms].
    simpl in *. assert (e = eq_refl). { apply UIP_dec, list_eq_dec, sort_eq_dec. }
    subst. reflexivity.
  - destruct args as [| ahd atl]; auto; [inversion Htms|].
    simpl.
    simp terms_to_hlist.
    rewrite cast_arg_list_cons.
    erewrite IH. f_equal. unfold dom_cast.
    repeat match goal with
    | |- context [scast (f_equal _ ?Heq)] => generalize dependent Heq 
    end.
    intros Heq1 Heq2. assert (Heq1 = Heq2). { apply UIP_dec, sort_eq_dec. }
    subst.
    erewrite term_rep_irrel. reflexivity.
Qed.

Lemma fun_arg_list_eq (pd: pi_dom) (pdf: pi_dom_full gamma pd)
  (pf: pi_funpred gamma_valid pd pdf) vt (v: val_vars pd vt) (f: funsym) (ty: vty) (tys: list vty) (tms: list term) 
  (Hty: term_has_type gamma (Tfun f tys tms) ty) Htms constrs_len:
  fun_arg_list pd vt f tys tms (term_rep gamma_valid pd pdf vt pf v) Hty =
  cast_arg_list  (eq_sym (sym_sigma_args_map vt f tys constrs_len))
    (terms_to_hlist pd pdf pf vt v tms ((ty_subst_list (s_params f) tys (s_args f))) Htms).
Proof.
  unfold fun_arg_list.
  eapply get_arg_list_eq. apply Hty.
Qed.

(*If (Tfun f args tms) is a semantic constr of c(al), then f = c, and
  al = terms_to_hlist tms (with the appropriate cast)*)
Lemma tfun_semantic_constr
  (pd: pi_dom) (pdf: pi_dom_full gamma pd)
  (pf: pi_funpred gamma_valid pd pdf) vt 
  {m a c f} (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m) (c_in : constr_in_adt c a) (f_in: constr_in_adt f a)
  (v: val_vars pd vt)
  (args: list vty) (tms: list term)
  (al : arg_list (domain (dom_aux pd)) (sym_sigma_args c (map (v_subst vt) args)))
  (Htty : term_has_type gamma (Tfun f args tms) (vty_cons (adt_name a) args))
  (constrs_len : length (s_params f) = length args)
  (args_len : length args = length (m_params m))
  (Htms : Forall2 (term_has_type gamma) tms (ty_subst_list (s_params f) args (s_args f)))
  (Hsem: tm_semantic_constr pd pdf pf vt v (Tfun f args tms) m_in a_in c_in args_len Htty al):
  exists Heq : c = f,
  al =
  cast_arg_list
    (f_equal
    (fun x : funsym =>
  sym_sigma_args x (map (v_subst vt) args))
    (eq_sym Heq))
    (cast_arg_list
    (eq_sym (sym_sigma_args_map vt f args constrs_len))
    (terms_to_hlist pd pdf pf vt v tms
    (ty_subst_list (s_params f) args (s_args f)) Htms)).
Proof.
  unfold tm_semantic_constr in Hsem.
  simp term_rep in Hsem.
  erewrite fun_arg_list_eq with (constrs_len:=constrs_len) (Htms:=Htms) in Hsem .
  (*Now lots of casting until we can get to injectivity*)
  rewrite (constrs gamma_valid pd pdf pf m a f m_in a_in f_in (map (v_subst vt) args) 
    (eq_trans (map_length (v_subst vt) args) args_len)) in Hsem.
  unfold constr_rep_dom in Hsem. 
  unfold cast_dom_vty, dom_cast in Hsem.
  rewrite !scast_scast in Hsem.
  revert Hsem.
  repeat match goal with 
  |- context [scast ?Heq _] => generalize dependent Heq
  end.
  intros Heq1 Heq2. assert (Heq1 = Heq2). { (*use UIP*) apply Cast.UIP. }
  subst.
  intros Hconstr; apply scast_inj in Hconstr.
  (*First, prove c = f*)
  assert (c = f). {
    destruct (funsym_eq_dec c f); auto.
    apply constr_rep_disjoint in Hconstr; auto. contradiction.
  }
  subst.
  exists eq_refl. unfold cast_arg_list at 1; simpl.
  (*Now use injectivity*)
  assert (c_in = f_in) by (apply bool_irrelevance); subst.
  apply constr_rep_inj in Hconstr; auto.
  apply (gamma_all_unif gamma_valid); auto.
Qed.

(*Part 5: Relationship between [types] and [cslist] (parts of [populate_all])*)

Definition constr_args_at_head_strong {B: Type} (c: funsym) (tys: list vty) (ps: list pattern)
  (P: list pattern * B) : bool :=
  match (fst P) with
  | Pconstr f tys1 pats1 :: _ => funsym_eqb f c && list_eqb vty_eqb tys tys1 && list_eqb pattern_eqb ps pats1
  | _ => false
  end.

Lemma populate_all_fst_snd_full {B: Type} (is_constr: funsym -> bool)
  (P: list (list pattern * B)) y:
  simplified P ->
  populate_all is_constr P = Some y ->
  NoDup (map (fun x => fst (fst x)) (snd y)) /\
  forall c ps,
    amap_get funsym_eq_dec (fst y) c = Some ps <->
    exists tys,
    In (c, tys, ps) (snd y).
Proof.
  intros Hsimpl. unfold populate_all.
  destruct (get_heads P) as[heads|] eqn : Hhead; [|discriminate].
  rewrite fold_left_right_opt.
  assert (Hhead1: get_heads (rev P) = Some (rev heads)). {
    rewrite get_heads_rev, Hhead. reflexivity.
  }
  clear Hhead.
  rewrite <- simplified_rev in Hsimpl.
  generalize dependent (rev heads). clear heads.
  revert y.
  induction (rev P) as [| [ps a] t IH]; simpl; auto; intros y head.
  - inv Hhead. simpl. inv Hsome. simpl. split; [constructor|]. 
    intros c ps. rewrite amap_empty_get.
    split; [discriminate| intros; destruct_all; contradiction].
  - simpl in Hsimpl. apply andb_prop in Hsimpl.
    destruct Hsimpl as [Hsimphd Hsimptl]. destruct ps as [| p ps]; [discriminate|].
    destruct (get_heads t); simpl in *; [|discriminate].
    inv Hhead. simpl.
    destruct (fold_right_opt _ l _) as [y1|] eqn : Hfold; simpl; [|discriminate].
    specialize (IH Hsimptl _ _ eq_refl Hfold).
    destruct IH as [IH1 IH2].
    destruct p as [| f1 tys1 pats1 | | |]; simpl in *; try discriminate.
    + destruct y1 as [css csl]; simpl in *.
      destruct (is_constr f1); [|discriminate].
      destruct (amap_mem funsym_eq_dec f1 css) eqn : Hmem.
      * inv Hsome. simpl; auto.
      * inv Hsome. simpl in *.
        (*First, prove NoDup*)
        split.
        -- constructor; [|apply IH1].
          intros Hinf1. rewrite in_map_iff in Hinf1.
          destruct Hinf1 as [[[f2 tys2] pats2] [Hf2 Hinf2]]; subst; simpl in *.
          (*contradiction with [amap_mem]*)
          assert (Hget: amap_get funsym_eq_dec css f2 = Some pats2). {
            apply IH2. exists tys2; auto.
          }
          rewrite amap_mem_spec in Hmem.
          rewrite Hget in Hmem.
          discriminate.
        -- (*Now prove, iff*)
          intros c ps1.
          destruct (funsym_eqb_spec c f1); subst.
          ++ rewrite amap_set_get_same.
            split.
            ** inv Hsome. exists tys1. auto.
            ** intros [tys [Hex | Hin]].
              { inversion Hex; auto. }
              (*Why we need iff - show that f1 cannot be csl if f1 not in css*)
              rewrite amap_mem_spec in Hmem.
              assert (Hget: amap_get funsym_eq_dec css f1 = Some ps1). {
                apply IH2. exists tys. auto.
              }
              rewrite Hget in Hmem. discriminate.
          ++ rewrite amap_set_get_diff; auto.
            rewrite IH2. 
            split; intros [tys Hintys].
            ** exists tys; auto.
            ** destruct Hintys as [Heq | Hin]; exists tys; auto; inversion Heq; subst; contradiction.
    + (*Pwild case*)
      inv Hsome. split; assumption.
Qed.

Lemma populate_all_snd_strong {B: Type} (is_constr: funsym -> bool)
  (P: list (list pattern * B)) y (f: funsym) tys ps:
  simplified P ->
  populate_all is_constr P = Some y ->
  In (f, tys, ps) (snd y) ->
  existsb (constr_args_at_head_strong f tys ps) P.
Proof.
  intros Hsimpl. unfold populate_all.
  destruct (get_heads P) as[heads|] eqn : Hhead; [|discriminate].
  rewrite fold_left_right_opt.
  (* unfold constr_args_at_head_strong. *)
  rewrite <- (rev_involutive P) at 1.
  rewrite existsb_rev. 
  assert (Hhead1: get_heads (rev P) = Some (rev heads)). {
    rewrite get_heads_rev, Hhead. reflexivity.
  }
  clear Hhead.
  rewrite <- simplified_rev in Hsimpl.
  (*Now, same direction*)
  generalize dependent (rev heads).
  revert y f tys ps. 
  induction (rev P) as [| [ps a] t IH]; simpl; auto; intros y cs tys pats hds1.
  - inv Hsome. simpl. inv Hsome. simpl. contradiction.
  - simpl in *. destruct ps as [| p ps]; [discriminate|].
    apply andb_prop in Hsimpl.
    destruct Hsimpl as [Hsimphd Hsimptl].
    destruct (get_heads t) as [tl|] eqn : Hheadtl; simpl in *; [|discriminate].
    inv Hsome. simpl.
    specialize (IH Hsimptl).
    destruct (fold_right_opt _ tl _) as [y1|] eqn : Hfold; simpl; [|discriminate].
    specialize (IH y1 cs tys pats tl eq_refl Hfold).
    intros Hpop Hin.
    destruct p as [| f1 tys1 pats1 | | |]; simpl in *; try discriminate.
    + (*Pconstr*)
      destruct y1 as [css csl]; simpl in *.
      destruct (is_constr f1) eqn : Hconstr; [|discriminate].
      destruct (amap_mem funsym_eq_dec f1 css) eqn : Hmem.
      * inversion Hpop; subst; simpl in *.
        apply IH in Hin. rewrite Hin, orb_true_r. auto.
      * inversion Hpop; subst; simpl in *.
        destruct Hin as [Heq | Hin].
        -- inversion Heq; subst.
          unfold constr_args_at_head_strong. simpl.
          destruct (funsym_eqb_spec cs cs); [|contradiction].
          destruct (list_eqb_spec _ vty_eq_spec tys tys); [|contradiction].
          destruct (list_eqb_spec _ pattern_eqb_spec pats pats); [|contradiction].
          reflexivity.
        -- rewrite IH; auto. rewrite orb_true_r; auto.
    + (*Pwild*)
      inversion Hpop; subst; auto.
Qed.

(*Part 6: Dealing with [match_rep] (iterated pattern matching)*)

(*If everything in the first list does not match, we can ignore it in [match_rep]*)
Lemma match_rep_app2 pd pdf pf vt v ps1 ps2 ty dom_t Hty1 Hty2
  (Hps1: forall p Hp, In p ps1 -> match_val_single gamma_valid pd pdf vt ty (fst p) Hp dom_t = None):
  match_rep gamma_valid pd pdf vt v (term_rep gamma_valid pd pdf vt pf) (formula_rep gamma_valid pd pdf vt pf) b ret_ty ty dom_t 
    (ps1 ++ ps2) Hty1 Hty2 =
  match_rep gamma_valid pd pdf vt v (term_rep gamma_valid pd pdf vt pf) (formula_rep gamma_valid pd pdf vt pf) b ret_ty ty dom_t 
    ps2 (Forall_app_snd Hty1) (Forall_app_snd Hty2).
Proof.
  generalize dependent (Forall_app_snd Hty1). generalize dependent (Forall_app_snd Hty2). revert Hty1 Hty2.
  induction ps1 as [|[p t] ptl IH]; simpl; auto.
  - intros. apply match_rep_irrel.
  - simpl in *. intros Hty1 Hty2 Hty3 Hty4. rewrite (Hps1 (p, t)); auto.
Qed.

(*Alt version with [gen_rep] (can't use before because term_rep/formula_rep were not defined)*)
Definition match_rep' pd pdf pf vt v (ty: gen_type b) ty1 dom_t :=
  fix match_rep (ps: list (pattern * (gen_term b)))
    (Hps: Forall (fun x => pattern_has_type gamma (fst x) ty1) ps)
    (Hall: Forall (fun x => gen_typed gamma b (snd x) ty) ps) :
      (gen_ret pd vt b ty) :=
    match ps as l' return
      Forall (fun x => pattern_has_type gamma (fst x) ty1) l' ->
      Forall (fun x => gen_typed gamma b (snd x) ty) l' ->
      gen_ret pd vt b ty with
    | (p , dat) :: ptl => fun Hpats Hall =>
      match (match_val_single gamma_valid pd pdf vt ty1 p (Forall_inv Hpats) dom_t) with
      | Some l => 
          gen_rep gamma_valid pd pdf pf vt (extend_val_with_list pd vt v l) ty dat (Forall_inv Hall)
      | None => match_rep ptl (Forall_inv_tail Hpats) (Forall_inv_tail Hall)
      end
    | _ => (*Will not reach if exhaustive*) fun _ _ => gen_default pd vt b ty 
    end Hps Hall .

Lemma match_rep_equiv pd pdf pf vt v ty ty1 dom_t ps Hps Hall:
  match_rep gamma_valid pd pdf vt v (term_rep gamma_valid pd pdf vt pf) (formula_rep gamma_valid pd pdf vt pf) b ty ty1 dom_t ps Hps Hall =
  match_rep' pd pdf pf vt v ty ty1 dom_t ps Hps Hall.
Proof.
  unfold match_rep'.
  reflexivity.
Qed.


(*Part 7: Lemmas about [gen_getvars]*)

(*We need a lemma: verything in gen_getvars of a row in (spec rl c) is in
  gen_getvars of a row in rl*)
Lemma gen_getvars_spec {rl c row x}:
  In row (spec rl c) -> In x (gen_getvars (snd row)) ->
  exists row1, In row1 rl /\ In x (gen_getvars (snd row1)).
Proof.
  induction rl as [| rhd rtl IH]; simpl; [contradiction|].
  destruct rhd as [ps a]; simpl in *.
  destruct ps as [| phd ptl]; auto.
  - intros Hinr Hinx. destruct (IH Hinr Hinx) as [r1 [Hinr1 Hinx1]].
    exists r1. auto.
  - destruct phd; auto; try solve[intros Hinr Hinx; destruct (IH Hinr Hinx) as [r1 [Hinr1 Hinx1]];
    exists r1; auto].
    + destruct (funsym_eqb_spec f c); subst; 
      [|solve[intros Hinr Hinx; destruct (IH Hinr Hinx) as [r1 [Hinr1 Hinx1]]; exists r1; auto]].
      simpl. intros [Hr | Hinr] Hinx;
      [|solve[destruct (IH Hinr Hinx) as [r1 [Hinr1 Hinx1]]; exists r1; auto]].
      subst. simpl in Hinx. exists ((Pconstr c l l0 :: ptl, a)). auto.
    + simpl. intros [Hr | Hinr] Hinx; (*WAY too repetitive*)
      [|solve[destruct (IH Hinr Hinx) as [r1 [Hinr1 Hinx1]]; exists r1; auto]].
      subst. simpl in Hinx. exists (Pwild :: ptl, a); auto.
Qed.

(*Part 8: Dealing with valuations*)
Section Val.

Context (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
  (pf: pi_funpred gamma_valid pd pdf)
  (vt: val_typevar).

(*If we have [matches_row] of a list of variables and arg list al,
  [extend_val_with_list] of the result is just [val_with_args] (map each var to the 
  corresponding element of the arg_list)*)
Lemma matches_row_allvars v tys1 (tys2 : list sort) (Heq: tys2 = map (v_subst vt) tys1) (*ugh*) (al: arg_list (domain (dom_aux pd)) tys2) vars Hvarsty:
  exists l, matches_row pd pdf vt tys1 (cast_arg_list Heq al) (map Pvar vars) Hvarsty = Some l /\
  forall x, extend_val_with_list pd vt v l x = val_with_args pd vt v vars al x.
Proof.
  subst. unfold cast_arg_list. simpl.
  generalize dependent Hvarsty.
  revert vars.
  induction tys1 as [| ty tys1 IH]; simpl; intros [| var1 vars] Hvarsty; try solve[inversion Hvarsty]; simpl.
  - simp matches_row. exists nil. split; auto.
  - simpl in *. simp matches_row. simpl.
    rewrite (hlist_inv al). simpl.
    specialize (IH (hlist_tl al) vars (Forall2_inv_tail Hvarsty)).
    destruct IH as [l1 [Hl1 Hvals]]. rewrite Hl1. simpl.
    eexists. split; [reflexivity|].
    intros x.
    inversion Hvarsty; subst. inversion H2; subst.
    destruct (vsymbol_eq_dec var1 x); subst.
    + destruct (vty_eq_dec _ _); [|contradiction].
      unfold extend_val_with_list; simpl. destruct (vsymbol_eq_dec x x); [|contradiction]. simpl.
      destruct (sort_eq_dec _ _); [|contradiction].
      apply dom_cast_eq.
    + (*Both cases identical*)
      assert (extend_val_with_list pd vt v
        ((var1, existT (domain (dom_aux pd)) (v_subst vt (snd var1)) (hlist_hd al)) :: l1) x =
        val_with_args pd vt v vars (hlist_tl al) x).
      {
        unfold extend_val_with_list. simpl.
        destruct (vsymbol_eq_dec x var1); subst; [contradiction|].
        apply Hvals.
      }
      destruct (vty_eq_dec _ _); auto.
Qed.

Lemma terms_to_hlist_change_vv v1 v2 ts tys Hall:
  (forall t x, In t ts -> In x (tm_fv t) -> v1 x = v2 x) ->
  terms_to_hlist pd pdf pf vt v1 ts tys Hall = terms_to_hlist pd pdf pf vt v2 ts tys Hall.
Proof.
  intros Halleq. generalize dependent tys. induction ts as [| t ts IH]; intros [| ty1 tys] Hall;
  try solve[inversion Hall]; auto.
  simp terms_to_hlist. simpl in *.
  rewrite tm_change_vv with (v2:=v2) by (intros x Hinx; apply (Halleq t); auto).
  rewrite IH; auto.
  intros t1 x Hint1 Hinx; apply (Halleq t1 x); auto.
Qed.

(*[terms_to_hlist] on vars vs under valuation (vs -> al) is just al*)
Lemma terms_to_hlist_val_with_args v vars tys {srts1} (Heq: srts1 = map (v_subst vt) tys) al Htys (Hn: NoDup vars):
  terms_to_hlist pd pdf pf vt (val_with_args pd vt v vars al) (map Tvar vars) tys Htys = 
  cast_arg_list Heq al.
Proof.
  subst. unfold cast_arg_list; simpl.
  generalize dependent tys. induction vars as [| v1 vars IH]; intros [| ty1 tys]; simpl; intros
  al Htys; try solve[inversion Htys]; auto.
  - simp terms_to_hlist. symmetry. apply hlist_nil.
  - simp terms_to_hlist. simpl. simp term_rep. simpl.
    unfold var_to_dom. rewrite (hlist_inv al). simpl.
    inversion Htys; subst. inversion H2; subst.
    destruct (vty_eq_dec _ _); [|contradiction].
    destruct (vsymbol_eq_dec _ _); [| contradiction].
    inversion Hn; subst; auto.
    erewrite terms_to_hlist_change_vv with (v2:=val_with_args pd vt v vars (hlist_tl al)).
    + rewrite IH; auto. f_equal. rewrite !dom_cast_compose. apply dom_cast_refl.
    + intros t x Hint Hinx.
      rewrite in_map_iff in Hint. destruct Hint as [y [Ht Hiny]]; subst.
      destruct Hinx as [Hx | []]; subst.
      destruct (vsymbol_eq_dec v1 x); subst; [contradiction|].
      destruct (vty_eq_dec _ _); auto.
Qed.

(*We can change the valuation for [matches_matrix] as long
  as they agree on all free variables in the matrix actions*)
Lemma matches_matrix_change_vv (v1 v2: val_vars pd vt) tys al P Hp
  (Heq: forall x row, In row P -> In x (gen_getvars (snd row)) -> v1 x = v2 x):
  matches_matrix pd pdf pf vt v1 tys al P Hp = 
  matches_matrix pd pdf pf vt v2 tys al P Hp.
Proof.
  revert Hp. induction P; intros Hp; simp matches_matrix; auto.
  simpl in *.
  destruct (matches_row _ _ _ _); auto.
  - f_equal. apply gen_rep_change_vv.
    intros x Hinx. simpl in *.
    assert (Hv12: v1 x = v2 x). {
      apply (Heq x a); auto. apply gen_fv_getvars; auto.
    }
    unfold extend_val_with_list.
    destruct (get_assoc_list vsymbol_eq_dec l x); auto.
    destruct (sort_eq_dec _ _); auto.
  - apply IHP; auto. intros x row Hinrow Hinx; apply (Heq x row); auto.
Qed.

End Val.

(*Part 9: 2 more typing lemmas*)

Lemma constr_typed_row {c tys ps ty}:
  pattern_has_type gamma (Pconstr c tys ps) ty ->
  row_typed (ty_subst_list (s_params c) tys (s_args c)) ps.
Proof.
  intros Hp; inversion Hp; subst.
  apply Forall2_nth.
  unfold ty_subst_list; simpl_len. split; auto. intros i d1 d2 Hi.
  apply (H8 (nth i ps d1, (nth i (seq.map (ty_subst (s_params c) tys) (s_args c)) d2))).
  rewrite in_combine_iff by solve_len.
  exists i. split; auto. intros. f_equal; apply nth_indep; auto. solve_len.
Qed.

(*A constructor at the head of a well-typed pattern matrix has the first type*)
Lemma constr_at_head_ex_type {ty tys rl c}:
  pat_matrix_typed (ty :: tys) rl ->
  constr_at_head_ex c rl ->
  exists tys ps, pattern_has_type gamma (Pconstr c tys ps) ty.
Proof.
  unfold pat_matrix_typed. intros [Hrows _] Hex.
  apply existsb_exists in Hex.
  destruct Hex as [row [Hinrow Hconstr]].
  unfold constr_at_head in Hconstr.
  rewrite Forall_forall in Hrows.
  specialize (Hrows _ Hinrow).
  destruct row as [[| phd ptl] a]; simpl in *; [discriminate|].
  destruct phd as [| f' tys1 ps1 | | |]; try discriminate.
  destruct (funsym_eqb_spec f' c); subst; [|discriminate].
  inversion Hrows; subst.
  exists tys1. exists ps1. auto.
Qed.

(*Meta-theorems about [compile]*)




(*Before we prove the main theorem, we take a detour and 
  reason about "simple" patterns.
  We need to prove this anyway, and in order to prove typing,
  we need to reason about [compile_bare_single] within the proof
  of [compile] (which is annoying). To do this, 
  we show that [compile] results in something that is simple
  and that if a simple match is (syntactically) exhaustive, then 
  [compile] succeeds*)

Section SimplePat.

(*Definition of a simple pattern*)
(*A simple pattern consists of only c(vs) or _ *)
(*A simple pattern match consists only of simple patterns, and no repeated constructors/redundant
  matches*)
(*We prove that compilation results in a simple pattern match, though the result is a bit complicated
  because the action terms might not have simple matches.
  As a corollary, every pattern match is semantically equivalent to a simple one*)

Definition simple_pat (p: pattern) : bool :=
  match p with
  | Pconstr c tys ps => forallb (fun p => match p with | Pvar _ => true | _ => false end) ps
  | Pwild => true
  | _ => false
  end.

Definition simple_pat_match (ps: list pattern) : bool :=
  forallb simple_pat ps &&
  nodupb funsym_eq_dec (omap 
    (fun p => match p with | Pconstr c _ _ => Some c | _ => None end) ps) &&
  (*At least 1 constructor - or else we compiled the whole match away*)
  (existsb (fun p => match p with | Pconstr _ _ _ => true | _ => false end) ps).

Fixpoint term_simple_pats (t: term) : bool :=
  match t with
  | Tfun c tys tms => forallb term_simple_pats tms
  | Tlet t1 x t2 => term_simple_pats t1 && term_simple_pats t2
  | Tif f t1 t2 => fmla_simple_pats f && term_simple_pats t1 && term_simple_pats t2
  | Teps f v => fmla_simple_pats f
  | Tmatch t ty pats => term_simple_pats t && forallb (fun x => term_simple_pats (snd x)) pats &&
    simple_pat_match (map fst pats)
  | _ => true
  end
with fmla_simple_pats (f: formula) : bool :=
  match f with
  | Fpred p tys tms => forallb term_simple_pats tms
  | Flet t x f => term_simple_pats t && fmla_simple_pats f
  | Fif f1 f2 f3 => fmla_simple_pats f1 && fmla_simple_pats f2 && fmla_simple_pats f3
  | Feq ty t1 t2 => term_simple_pats t1 && term_simple_pats t2
  | Fbinop b f1 f2 => fmla_simple_pats f1 && fmla_simple_pats f2
  | Fmatch t ty pats => term_simple_pats t && forallb (fun x => fmla_simple_pats (snd x)) pats &&
    simple_pat_match (map fst pats)
  | Fnot f => fmla_simple_pats f
  | _ => true
  end.

Definition gen_simple_pats (t: gen_term b) : bool :=
  match b return gen_term b -> bool with
  | true => term_simple_pats
  | false => fmla_simple_pats
  end t.

Lemma gen_simple_pats_let v t1 t2:
  term_simple_pats t1 ->
  gen_simple_pats t2 ->
  gen_simple_pats (gen_let v t1 t2).
Proof.
  unfold gen_simple_pats, gen_let. destruct b; simpl; intros Hsimp1 Hsimp2;
  rewrite Hsimp1; auto.
Qed.

Lemma gen_simple_pats_simplify_single t x:
  term_simple_pats t ->
  gen_simple_pats (snd x) ->
  forallb gen_simple_pats (map snd (simplify_single gen_let t x)).
Proof.
  intros Hsimp1 Hsimp2. unfold simplify_single. destruct x as [ps t1]; simpl in *.
  destruct ps as [| phd ptl]; simpl; [rewrite Hsimp2|]; auto.
  rewrite !map_map. simpl. rewrite forallb_map. generalize dependent t1.
  induction phd; simpl; intros t1 Hsimp2; try solve[rewrite Hsimp2; auto].
  - rewrite gen_simple_pats_let; auto.
  - rewrite forallb_app, IHphd1, IHphd2; auto.
  - apply IHphd. apply gen_simple_pats_let; auto.
Qed.


Lemma gen_simple_pats_simplify t rl:
  term_simple_pats t ->
  forallb gen_simple_pats (map snd rl) ->
  forallb gen_simple_pats (map snd (simplify gen_let t rl)).
Proof.
  intros Hsimp1 Hsimp2. unfold simplify.
  rewrite concat_map.
  rewrite forallb_concat. rewrite !map_map.
  rewrite !forallb_map.
  apply forallb_forall. intros x Hinx.
  apply gen_simple_pats_simplify_single; auto.
  unfold is_true in Hsimp2.
  rewrite forallb_forall in Hsimp2; apply Hsimp2; auto.
  rewrite in_map_iff. exists x; auto.
Qed.

Lemma gen_simple_pats_default rl:
  forallb gen_simple_pats (map snd rl) ->
  forallb gen_simple_pats (map snd (default rl)).
Proof.
  induction rl; simpl; auto.
  intros Hsimp. apply andb_prop in Hsimp.
  destruct Hsimp as [Ha Hrl].
  destruct a as [ps a]; simpl in *.
  destruct ps as [| phd ptl]; simpl; auto.
  destruct phd; auto. simpl.
  rewrite Ha; auto.
Qed.

(*Don't use spec directly because don't assume typing - very tedious*)
Lemma gen_simple_pats_spec rl t types cs ys
  (Hsimpl: simplified rl)
  (Hsimp1: forallb gen_simple_pats (map snd rl))
  (Hget: amap_get funsym_eq_dec (fst (dispatch1 gen_let t types rl)) cs = Some ys):
  forallb gen_simple_pats (map snd ys).
Proof.
  rewrite dispatch_equiv in Hget.
  unfold dispatch2 in Hget.
  rewrite simplified_simplify in Hget; auto.
  clear t. generalize dependent ys.
  induction rl as [| rhd rtl IH]; simpl in *; intros ys Hget.
  - rewrite amap_empty_get in Hget. discriminate.
  - apply andb_prop in Hsimp1. destruct Hsimp1 as [Hhd Htl]. 
    unfold dispatch2_aux in Hget. destruct rhd as [ps a]; simpl in *.
    destruct (dispatch2_gen types rtl)  as [cases wilds] eqn : Hdis1; simpl in *.
    apply andb_prop in Hsimpl. destruct Hsimpl as [Hsimphd Hsimptl].
    destruct ps as [| phd ptl]; auto.
    destruct phd; try discriminate; simpl in *.
    + unfold add_case, amap_change in Hget. 
      destruct (funsym_eq_dec f cs); subst.
      * destruct (amap_get funsym_eq_dec cases cs) as [y2|] eqn : Hget1.
        -- rewrite amap_replace_get_same1 with (y1:=y2) in Hget; auto.
          revert Hget. inv Hsome. simpl. rewrite Hhd; auto. apply IH; auto.
        -- rewrite amap_replace_get_same2 in Hget; auto. revert Hget. inv Hget.
          simpl. rewrite Hhd; auto.
      * rewrite amap_replace_get_diff in Hget; auto.
    + unfold union_cases in Hget.
      destruct (amap_get funsym_eq_dec cases cs) as [y2|] eqn : Hget1.
      * destruct (amap_get funsym_eq_dec types cs) as [y3|] eqn : Hget2.
        -- erewrite amap_union_inboth in Hget; eauto.
          2: { erewrite amap_map_key_get_some; eauto. }
          simpl in Hget. revert Hget. inv Hsome. simpl.
          rewrite Hhd; apply IH; auto.
        -- rewrite amap_union_inr with(y:=y2) in Hget; auto.
          rewrite amap_map_key_get_none; auto.
      * destruct (amap_get funsym_eq_dec types cs) as [y3|] eqn : Hget2.
        -- erewrite amap_union_inl in Hget; auto.
          2: { erewrite amap_map_key_get_some; eauto. }
          revert Hget. inv Hget. simpl. rewrite Hhd; auto.
        -- rewrite amap_union_notin in Hget; auto.
          rewrite amap_map_key_get_none; auto.
Qed.

Lemma gen_simple_pats_match t ty pats:
  term_simple_pats t ->
  forallb gen_simple_pats (map snd pats) ->
  simple_pat_match (map fst pats) ->
  gen_simple_pats (gen_match t ty pats).
Proof.
  intros Hsimp1. unfold gen_simple_pats, gen_match. destruct b; simpl; bool_to_prop;
  rewrite !forallb_map; intros; destruct_all; split_all; auto.
Qed.

(*TODO: do other version in terms of this*)
Lemma map_fst_combine_eq {A B: Type} (l1: list A) (l2: list B):
  map fst (combine l1 l2) = firstn (Nat.min (length l1) (length l2)) l1.
Proof.
  revert l2. induction l1 as [| h1 t1 IH]; simpl; auto; intros [| h2 t2]; auto.
  simpl. f_equal. auto.
Qed.

Lemma map_snd_combine_eq {A B: Type} (l1: list A) (l2: list B):
  map snd (combine l1 l2) = firstn (Nat.min (length l1) (length l2)) l2.
Proof.
  revert l2. induction l1 as [| h1 t1 IH]; simpl; auto; intros [| h2 t2]; auto.
  simpl. f_equal. auto.
Qed.

Lemma forallb_firstn {A: Type} (p: A -> bool) (n: nat) (l: list A):
  forallb p l ->
  forallb p (firstn n l).
Proof.
  revert n. induction l as [| h t IH]; simpl; intros [| n']; simpl; auto.
  destruct (p h); simpl; auto.
Qed.

(*Move?*)
(*Without typing, we don't know that getting a constr in the map gives [spec].
  But we can prove that it gives the weaker version*)
Lemma spec_noty {A} {is_constr glet t cs tys pats types_cslist} {rl: list (list pattern * A)}
  (Hsimpl: simplified rl)
  (Hpop: populate_all is_constr rl = Some types_cslist):
  In (cs, tys, pats) (snd types_cslist) ->
  amap_get funsym_eq_dec (fst (dispatch1 glet t (fst types_cslist) rl)) cs = 
  Some
     (omap
        (fun x =>
         match fst x with
         | Pconstr fs _ pats0 :: ps2 =>
             if funsym_eqb fs cs then Some (rev pats0 ++ ps2, snd x) else None
         | Pwild :: ps2 => Some (repeat Pwild (Datatypes.length pats) ++ ps2, snd x)
         | _ => None
         end) rl).
Proof.
  intros Hinc.
  rewrite dispatch_equiv.
  unfold dispatch2. rewrite simplified_simplify; auto.
  assert (Htypes: amap_get funsym_eq_dec (fst types_cslist) cs = Some pats)
   by (eapply populate_all_fst_snd_full; eauto).
  assert (Hex: constr_at_head_ex cs rl || wild_at_head_ex rl). {
    pose proof (populate_all_snd_strong _ _ _ _ _ _ Hsimpl Hpop Hinc) as Hex.
    unfold constr_at_head_ex.
    apply orb_true_iff; left.
    revert Hex. apply existsb_impl. intros [x1 x2] Hinx.
    unfold constr_args_at_head_strong, constr_at_head. simpl.
    destruct x1 as [| phd ptl]; auto.
    destruct phd as [ | f1 ? ? | | | ]; auto. intros; bool_hyps; auto.
  }
  rewrite dispatch2_gen_fst_in with (ys:=pats); auto.
Qed.

Lemma compile_simple_pats bare simpl_constr (tms: list (term * vty)) (P: pat_matrix) t
  (Hsimp: forallb term_simple_pats (map fst tms) /\ forallb gen_simple_pats (map snd P)):
  compile get_constructors gen_match gen_let gen_getvars bare simpl_constr tms P = Some t ->
  gen_simple_pats t.
Proof.
  intros Hcomp.
  revert t Hsimp Hcomp.
  apply (compile_prove_some get_constructors gen_match gen_let gen_getvars gen_getvars_let
    bare simpl_constr (fun tms P => forallb term_simple_pats (map fst tms) /\ forallb gen_simple_pats (map snd P))
    (fun tms P t => gen_simple_pats t)); clear tms P; try discriminate.
  - (*invariance under [simplify]*)
    intros. destruct Hhyps as [Hsimp1 Hsimp2]. 
    assert (Hsimpsimp: forallb gen_simple_pats (map snd (simplify gen_let t rl))).
    { apply gen_simple_pats_simplify; auto. simpl in Hsimp1. bool_hyps; auto. }
    auto.
  - (*Empty list*)
    intros. destruct Hhyps as [Hsimp1 Hsimp2]. simpl in Hsimp2. apply andb_prop in Hsimp2. apply Hsimp2.
  - (*wilds case*)
    intros. destruct Hhyps as [Hsimp1 Hsimp2]. subst rl; set (rl := rhd :: rtl) in *. apply IHwilds; auto. split.
    + simpl in Hsimp1. bool_hyps. auto.
    + apply gen_simple_pats_default. auto.
  - (*full case*)
    intros. destruct Hhyps as [Hsimp1 Hsimp2]. simpl in Hsimp1. apply andb_true_iff in Hsimp1. destruct Hsimp1 as [Hsimpt Hsimptl].
    apply gen_simple_pats_match; auto.
    + (*First, prove all are simple (from IHconstrs)*)
      assert (Hall1: Forall (fun x => forall y, snd x = Some y -> gen_simple_pats y) 
        (map (fun x => (fst x, Some (snd x)))  ps)).
      2: {
        rewrite forallb_map.
        apply forallb_forall. intros x Hinx.
        rewrite Forall_map in Hall1. simpl in Hall1.
        rewrite Forall_forall in Hall1.
        specialize (Hall1 _ Hinx _ eq_refl); apply Hall1.
      }
      (*Now prove the obligation*)
      rewrite <- Hopt. apply Forall_app; split.
      * apply Forall_rev. apply Forall_map.
        rewrite Forall_forall.
        intros [[c tys] pats1] Hinx y. simpl. 
        unfold rev_map. rewrite !map_rev, !rev_involutive.
        unfold comp_cases.
        destruct (amap_get funsym_eq_dec cases c ) as [y1|] eqn : Hget; [|discriminate].
        eapply IHconstrs; eauto; split; [|solve[subst; eapply gen_simple_pats_spec; eauto]].
        rewrite map_app, forallb_app, Hsimptl, andb_true_r.
        rewrite map_rev, forallb_rev.
        set (new_vars := (combine (gen_strs (length pats1) (compile_fvs gen_getvars ((t, ty) :: tl) rl)))
          (map (ty_subst (s_params c) tys) (s_args c))) in *.
        rewrite map_fst_combine; auto; [| solve_len].
        (*Easy: all added are vars*)
        rewrite forallb_map. simpl. apply forallb_t.
      * (*Now case on [ps1] for end*)
        destruct Hps1' as [[Hps1 Hiswilds] | [Hiswilds [t2 [Hwilds Hps1]]]]; subst; simpl; auto.
        constructor; auto. simpl. rewrite <- Hwilds. intros y. apply IHwilds; split; auto.
        apply gen_simple_pats_default; auto.
    + (*Simple follows from nodups of cslist*)
      replace (map fst ps) with (map fst (map
        (fun x => (fst x, Some (snd x))) ps)) by
        (rewrite !map_map; simpl; reflexivity).
      rewrite <- Hopt. rewrite map_app. simpl.
      rewrite !map_rev, !map_map.
      unfold simple_pat_match.
      repeat (apply andb_true_iff; split).
      * rewrite forallb_app. apply andb_true_iff; split.
        -- (*Prove all pats are simple - they are vars*)
          rewrite forallb_rev, forallb_map.
          apply forallb_forall.
          intros [[c tys1] pats1] Hinc. simpl.
          unfold rev_map. rewrite map_rev, rev_involutive.
          rewrite forallb_map. apply forallb_t.
        -- simpl. (*easy - just a wild*)
          destruct Hps1' as [[Hps1 Hiswilds] | [Hiswilds [t2 [Hwilds Hps1]]]]; subst; simpl; auto.
      * unfold cslist. apply (reflect_iff _ _ (nodup_NoDup _ _)).
        rewrite omap_app, !omap_rev, !omap_map. simpl.
        (*second list is nil*)
        assert (Hsnd: (omap
          (fun x : pattern * gen_term b => match fst x with
        | Pconstr c _ _ => Some c
        | _ => None
        end) ps1) = nil); [| rewrite Hsnd, app_nil_r].
        {
          destruct Hps1' as [[Hps1 Hiswilds] | [Hiswilds [t2 [Hwilds Hps1]]]]; subst; simpl; auto.
        }
        apply NoDup_rev.
        apply populate_all_fst_snd_full in Hpop; [|assumption].
        destruct Hpop as [Hnodup Hpop].
        revert Hnodup.
        match goal with |- NoDup ?l1 -> NoDup ?l2 => 
          replace l1 with l2; [solve[auto]|]
        end.
        clear.
        induction (snd (types_cslist)) as [| x xs IH]; simpl; auto.
        destruct x as [[cs tys1] pats1]; simpl in *. rewrite IH; auto.
      * rewrite existsb_app. apply orb_true_iff; left.
        rewrite existsb_rev, existsb_map.
        (*Idea: cslist not null, so there must be a constr, cslist not null because types not empty*)
        destruct cslist as [| [[c tys] pats] csl] eqn : Hcslist; [|solve[auto]].
        exfalso. rewrite (amap_not_empty_exists funsym_eq_dec) in Hisemp.
        destruct Hisemp as [f [pats Hget]].
        assert (Hex: exists tys, In (f, tys, pats) cslist). {
          unfold cslist. apply (populate_all_fst_snd_full _ _ _ Hsimpl Hpop). auto.
        }
        rewrite Hcslist in Hex. destruct_all; contradiction.
  - (*constr case*)
    intros.  destruct Hhyps as [Hsimp1 Hsimp2]. simpl in Hsimp1. 
    apply andb_prop in Hsimp1. destruct Hsimp1 as [Hsimpt Hsimptl]. 
    revert Hcomp.
    unfold comp_cases.
    destruct (amap_get funsym_eq_dec cases cs) as [y|] eqn : Hget; [|discriminate].
    eapply IHconstrs; eauto; split.
    + subst t. simpl in Hsimpt. 
      rewrite map_app, forallb_app, Hsimptl, andb_true_r.
      rewrite map_rev, map_fst_combine_eq, map_length, forallb_rev.
      apply forallb_firstn; auto.
    + (*use gen_simple_pats_spec*)
      revert Hget.
      unfold cases.
      rewrite Hcasewild. 
      apply gen_simple_pats_spec; auto.
Qed.

(*The second part: exhaustive*)
(*Define an exhaustive simple pattern - wrt ADT*)
Definition simple_exhaust (ps: list pattern) (a: alg_datatype) : bool :=
  forallb (fun (c: funsym) =>
    existsb (fun p => 
      match p with
      | Pconstr f _ _ => funsym_eqb f c
      | _ => false
      end) ps ) (adt_constr_list a) ||
  existsb (fun p => match p with | Pwild => true | _ => false end) ps.

(*Not sure where to put this - need for [compile_simple_exhaust]
  and [compile_correct]*)
(*Useful in multiple places: if everything is well-typed, then
  [populate_all] is [Some]*)
Lemma typed_populate_all_true (bare : bool) ty tys rl
  (Hp: pat_matrix_typed (ty :: tys) rl)
  (Hsimp: simplified rl):
  let is_bare_css := match ty with
    | vty_cons ts _ => if bare then (true, []) else (false, get_constructors ts)
    | _ => (false, [])
    end in
  let is_bare := fst is_bare_css in
  let css := snd is_bare_css in 
  let is_constr := fun fs => f_is_constr fs && (is_bare || in_bool funsym_eq_dec fs css) in
  populate_all is_constr rl <> None.
Proof.
  intros is_bare_css is_bare css is_constr Hpop.
  unfold populate_all in Hpop.
  destruct (get_heads rl) as [l|] eqn : Hget.
  * (*Case 1: [get_heads] is Some, [fold_left_opt] is None*)
    apply fold_left_opt_none in Hpop.
    destruct Hpop as [ps1 [p [ps2 [acc1 [Hl [Hfold Hpop]]]]]].
    subst. apply populate_none_simpl in Hpop.
    2: {
      apply (get_heads_simplified rl (ps1 ++ p :: ps2)); auto.
      rewrite in_app_iff; simpl; auto.
    }
    (*Idea: contradiction, by None we found a constructor in 1st column that is
      not [is_constr]. But by tying, it has to be*)
    destruct Hpop as [c [tys1 [ps [Hpeq Hnotconstr]]]]; subst.

    assert (Htyp: pattern_has_type gamma (Pconstr c tys1 ps) ty). {
      eapply in_get_heads_tys. apply Hp. apply Hget.
      rewrite !in_app_iff; simpl; auto.
    }
    (*if bare is true, easy*)
    inversion Htyp; subst.
    unfold sigma in *.
    destruct H11 as [m [a [m_in [a_in c_in]]]].
    destruct bare.
    {
      exfalso.
      revert Hnotconstr.
      unfold is_constr, is_bare, is_bare_css.
      rewrite (adt_constr_ret gamma_valid m_in a_in c_in).
      rewrite ty_subst_cons. simpl.
      assert (f_constr: f_is_constr c) by (rewrite is_constr_iff; eauto).
      rewrite f_constr.
      discriminate.   
    }
    (*The contradiction*)
    assert (Hconstr: is_constr c). {
      unfold is_constr. unfold css, is_bare, is_bare_css.
      rewrite (adt_constr_ret gamma_valid m_in a_in c_in).
      rewrite ty_subst_cons. simpl. 
      assert (f_constr: f_is_constr c) by (rewrite is_constr_iff; eauto).
      rewrite f_constr.
      apply In_in_bool, (in_get_constructors gamma_valid m_in a_in); auto.
    }
    rewrite Hnotconstr in Hconstr; discriminate.
  * (*Second typing contradiction: if get_heads is None*)
    (*By typing, cannot have an empty pattern list in a row*)
    apply get_heads_none_iff in Hget.
    rewrite (pat_matrix_typed_not_null Hp) in Hget.
    discriminate.
Qed.

(*If our pattern matrix is full of only variables and wildcards,
  the match always succeeds*)

Definition var_or_wild (p: pattern) : bool :=
  match p with
  | Pwild => true
  | Pvar _ => true
  | _ => false
  end.

(*If a constructor is in [simplify], then that constructor is in the 
  original pattern matrix*)

(*If all elements in P are [var_or_wild], then
  all element in [simplify _ _ P] are [var_or_wild]*)
Lemma var_or_wild_simplify glet t (P: pat_matrix):
  (forall p : pattern, In p (concat (map fst P)) -> var_or_wild p) ->
  (forall p : pattern, In p (concat (map fst (simplify glet t P))) -> var_or_wild p).
Proof.
  intros Hwilds p.
  (*No easy way to do this*)
  revert Hwilds.
  setoid_rewrite in_concat. setoid_rewrite in_map_iff.
  intros Hwilds [ps [[[ps1 t1] [Hps Hinpt]] Hinp]]; simpl in Hps; subst.
  unfold simplify in Hinpt.
  revert Hinpt. rewrite in_concat. setoid_rewrite in_map_iff.
  intros [ps1 [[[ps2 t2] [Hps1 Hinpt]] Hinps1]]; subst.
  unfold simplify_single in Hinps1.
  destruct ps2 as [| phd ptl].
  { destruct Hinps1 as [Heq | []]; inversion Heq; subst; contradiction. }
  rewrite in_map_iff in Hinps1. destruct Hinps1 as [[p3 t3] [Heq Hinpt3]];
  simpl in Heq; inversion Heq; subst; clear Heq.
  (*2 cases: either in P or in result of [simplify]*)
  simpl in Hinp. destruct Hinp as [Hpeq | Hinp]; subst.
  - (*Case 1: in simplify_aux*)
    (*Know phd is var or wild*)
    assert (Hhd: var_or_wild phd). {
      apply Hwilds. eexists. split. eexists. split; [|apply Hinpt].
      reflexivity. simpl; auto.
    }
    destruct phd; try discriminate; simpl in Hinpt3;
    destruct Hinpt3 as [Heq | []]; inversion Heq; subst; auto.
  - (*Case 2: in ptl, easier*)
    apply Hwilds. exists (phd :: ptl); split; simpl; auto.
    exists (phd :: ptl, t2); auto.
Qed.

Lemma var_wilds_default rl:
  simplified rl ->
  forallb (fun x : list pattern * gen_term b => negb (null (fst x))) rl ->
  (forall p, In p (concat (map fst rl)) -> var_or_wild p) ->
  map fst (default rl) = map (fun x => match (fst x) with
                              | nil => nil
                              | _ :: y => y
  end) rl.
Proof.
  intros Hsimp Hnotnull Hvarwild.
  induction rl as [| [ps a] rtl IH]; simpl in *; auto.
  destruct ps as [| phd ptl]; simpl in *; auto; [discriminate|].
  destruct phd; simpl in *; try discriminate.
  - exfalso. specialize (Hvarwild _ (ltac:(left; reflexivity))).
    discriminate.
  - f_equal; auto. apply IH; auto. intros p Hp.
    apply Hvarwild. right. rewrite in_app_iff. auto.
Qed.

(*Here we do NOT use simpl_constr - even though we could
  prove for both, only need for exhaustiveness check*)
Lemma compile_all_wild constrs (tms: list (term * vty)) (P: pat_matrix)
  (Hwilds: forall p, In p (concat (map fst P)) ->
    var_or_wild p)
  (Htys: Forall2 (term_has_type gamma) (map fst tms) (map snd tms))
  (Hp: pat_matrix_typed (map snd tms) P)
  (Hnotnull: negb (null P)):
  compile constrs gen_match gen_let gen_getvars true false tms P <> None.
Proof.
  revert Hwilds Htys Hp Hnotnull.
  apply (compile_ind constrs gen_match gen_let gen_getvars gen_getvars_let
  true false (fun tms P o =>
      forall (Hwilds: forall p, In p (concat (map fst P)) ->
      var_or_wild p)
    (Htys: Forall2 (term_has_type gamma) (map fst tms) (map snd tms))
    (Hp: pat_matrix_typed (map snd tms) P)
    (Hnotnull: negb (null P)),
    o <> None)); clear tms P ; auto.
  - intros. (*Prove preserved by simplify*)
    rewrite compile_simplify by (apply gen_getvars_let). apply H; auto.
    2: apply simplify_typed; auto; inversion Htys; subst; auto.
    apply var_or_wild_simplify; auto.
    rewrite null_simplify; auto.
  - (*Some case*)
    simpl. discriminate.
  - (*Ill typed*)
    intros t ty tl rl is_bare_css is_bare css is_constr Hsimp Htype Hwilds Htys Hp Hnotnull.
    destruct Htype as [Hpop | Hdisp].
    + pose proof (typed_populate_all_true true ty (map snd tl) rl
      Hp Hsimp) as Hpop2.
      simpl in Hpop2.
      unfold is_constr, is_bare, css, is_bare_css in Hpop.
      rewrite Hpop in Hpop2. contradiction.
    + destruct Hdisp as [types_cslist [Hpop Hdisp]].
      (*Show disp is Some*)
      apply dispatch1_opt_none in Hdisp.
      rewrite (pat_matrix_typed_not_null Hp) in Hdisp.
      discriminate.
  - (*Interesting case*)
    intros t ty tl rl rhd rtl is_bare_css is_bare css is_constr Hsimpl
      Hrl types_cslist Hpop types cslist casewild Hdisp cases wilds
      [IHwilds IHconstrs] Hvarwild Htys Hp Hnotnull.
    set (comp_wilds := fun _ : unit => compile constrs gen_match gen_let gen_getvars true false tl wilds) in *.
    set (comp_cases :=
      fun (cs : funsym) (al : list (term * vty)) =>
      comp_cases (compile constrs gen_match gen_let gen_getvars true false) cases tl cs al) in *.
    simpl.
    set (comp_full :=
      comp_full gen_match gen_getvars is_bare comp_wilds comp_cases types cslist css t ty
      tl rl) in *.
    apply dispatch1_opt_some in Hdisp.
    destruct Hdisp as [Hallnotnull Hcasewild]; subst casewild.
    (*Case 1: wilds case*)
    assert (Hwilds: comp_wilds tt <> None).
    {
      unfold comp_wilds.
      (*Use IH - default also needs to have only vars or wilds*)
      apply IHwilds; auto.
      - unfold wilds; rewrite dispatch1_equiv_default; auto.
        rewrite var_wilds_default; auto.
        (*Now we know that everything is in rl already*)
        intros p.
        rewrite in_concat.
        setoid_rewrite in_map_iff.
        intros [ps [[[ps1 t1] [Hps Hinpt]] Hinp]]; subst ps.
        simpl in Hinp.
        destruct ps1 as [|phd ptl]; [contradiction|].
        apply Hvarwild.
        rewrite in_concat. setoid_rewrite in_map_iff.
        exists (phd :: ptl). simpl; split; eauto.
        eexists. split; eauto. reflexivity.
      - inversion Htys; subst; auto.
      - unfold wilds; rewrite dispatch1_equiv_default; auto. 
        eapply default_typed; eauto.
      - unfold wilds; rewrite dispatch1_equiv_default; auto.
        rewrite Hrl. simpl.
        destruct rhd as [ps a]; simpl.
        destruct ps as [| phd ptl].
        + rewrite Hrl in Hallnotnull; discriminate.
        + specialize (Hvarwild phd).
          forward Hvarwild.
          {
            rewrite in_concat. setoid_rewrite in_map_iff.
            exists (phd :: ptl). simpl; split; auto.
            exists ((phd :: ptl), a); subst; simpl; auto.
          }
          rewrite Hrl in Hsimpl. simpl in Hsimpl.
          destruct phd; try discriminate. reflexivity.
    }
    (*Now this is easy, because amap_is_empty is true*)
    destruct (amap_is_empty types) eqn : Hisemp; [exact Hwilds |].
    rewrite amap_not_empty_mem with (eq_dec:=funsym_eq_dec) in Hisemp.
    destruct Hisemp as [cs Hmem].
    unfold types in Hmem.
    erewrite populate_all_in in Hmem; eauto.
    (*contradiction - no constrs in rl*)
    unfold constr_at_head_ex in Hmem.
    apply existsb_exists in Hmem.
    destruct Hmem as [[ps a] [Hinps Hconstr]].
    unfold constr_at_head in Hconstr.
    destruct ps as [| phd ptl]; [discriminate|].
    simpl in Hconstr.
    destruct phd as [| f1 tys1 ps1 | | |]; try discriminate.
    assert (var_or_wild (Pconstr f1 tys1 ps1)); [|discriminate].
    apply Hvarwild. rewrite in_concat. setoid_rewrite in_map_iff.
    exists (Pconstr f1 tys1 ps1 :: ptl). split; simpl; auto.
    eexists. split; [|apply Hinps]. reflexivity.
Qed.

Lemma populate_all_in_adt {cs rl types_cslist y m a vs tys constr}
  (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m)
  (Hsimp: simplified rl)
  (Hp: pat_matrix_typed (vty_cons (adt_name a) vs :: tys) rl)
  (Hpop: populate_all constr rl = Some types_cslist)
  (Hget: amap_get funsym_eq_dec (fst types_cslist) cs = Some y):
  constr_in_adt cs a.
Proof.
  assert (Hmem: amap_mem funsym_eq_dec cs (fst types_cslist)). {
    rewrite amap_mem_spec, Hget; auto.
  }
  rewrite (populate_all_in _ _ _ _ Hsimp Hpop) in Hmem.
  destruct (constr_at_head_ex_type Hp Hmem) as [tys1 [ps1 Hpty]].
  inversion Hpty; subst.
  destruct H11 as [m1 [a1 [m1_in [a1_in cs_in]]]].
  (*Show m = m1 and a = a1*)
  unfold sigma in H2.
  rewrite (adt_constr_subst_ret gamma_valid m1_in a1_in cs_in) in H2 by auto.
  inversion H2; subst.
  assert (m1 = m) by (apply (mut_adts_inj (valid_context_wf _ gamma_valid) m1_in m_in a1_in a_in); auto).
  subst.
  assert (a1 = a) by (apply (adt_names_inj' gamma_valid a1_in a_in); auto).
  subst; auto.
Qed.

(*The key result that lets us relate [compile] and [compile_bare]:
Checking the size of [f_num_constrs] is exactly equivalent to checking
that all constructors appear in the list*)
Lemma size_check_equal {m a cs vs tys y} {rl: pat_matrix} 
  {types_cslist} (m_in: mut_in_ctx m gamma) 
  (a_in: adt_in_mut a m) (c_in: constr_in_adt cs a)
  (Hsimp: simplified rl)
  (Hp: pat_matrix_typed (vty_cons (adt_name a) vs :: tys) rl)
  (Hpop: populate_all (fun fs => f_is_constr fs) rl = Some types_cslist)
  (Hget: amap_get funsym_eq_dec (fst types_cslist) cs = Some y):
  amap_size (fst types_cslist) =? f_num_constrs cs =
  forallb (fun f => amap_mem funsym_eq_dec f (fst types_cslist))
  (adt_constr_list a).
Proof.
  rewrite (num_constrs_correct _ gamma_valid m_in a_in) by (apply (populate_all_in_adt m_in a_in Hsimp Hp Hpop Hget)).
  (*Now use results about sublists and NoDups*)
  (*First, rewrite in terms of the constr list of types*)
  unfold amap_size, amap_mem.
  set (tys':=proj1_sig (fst types_cslist)) in *.
  replace (forallb (fun f : funsym => map_contains funsym_eq_dec tys' f) (adt_constr_list a))
    with (forallb (fun f => in_dec funsym_eq_dec f (map fst tys')) (adt_constr_list a)).
  2: {
    apply forallb_ext. intros x. unfold map_contains.
    unfold map_get_aux.
    destruct (get_assoc_list funsym_eq_dec tys' x) eqn : Hget1.
    - apply get_assoc_list_some in Hget1. destruct (in_dec _ _); auto.
      exfalso. apply n. rewrite in_map_iff. eexists. split; [| apply Hget1]; auto.
    - rewrite get_assoc_list_none in Hget1. destruct (in_dec _ _); auto.
      contradiction.
  }
  rewrite <-(map_length fst tys').
  (*Now sublists and NoDups*)
  assert (Hnodup1: NoDup (map fst tys')).
  {
    unfold tys'.
    destruct (fst types_cslist) as [types types_wf]. auto. 
  }
  assert (Hsub1: sublist (map fst tys') (adt_constr_list a)).
  {
    intros x.
    unfold tys'; intros Hinx.
    rewrite in_map_iff in Hinx.
    destruct Hinx as [[cs1 y1] [Hcsy Hincs]]; simpl in Hcsy; subst.
    assert (Hget1: amap_get funsym_eq_dec (fst types_cslist) x = Some y1). {
      unfold amap_get, map_get_aux.
      apply get_assoc_list_nodup; auto.
    }
    apply (populate_all_in_adt m_in a_in Hsimp Hp Hpop) in Hget1.
    apply constr_in_adt_eq; auto.
  }
  assert (Hlen1: length (map fst tys') <= length (adt_constr_list a)). {
    apply NoDup_incl_length; auto.
  }
  assert (Hnodup2: NoDup (adt_constr_list a)).
  {
    unfold adt_constr_list.
    apply (reflect_iff _ _ (nodup_NoDup funsym_eq_dec _)).
    eapply (constrs_nodups gamma_valid). Unshelve. all: eauto.
    rewrite in_map_iff. exists a. split; auto.
    apply in_bool_In in a_in; apply a_in.
  }
  (*Now case analysis*)
  destruct (forallb (fun f : funsym => in_dec funsym_eq_dec f (map fst tys')) (adt_constr_list a)) eqn : Hall.
  - apply Nat.eqb_eq. rewrite forallb_forall in Hall.
    assert (Hsub2: sublist (adt_constr_list a) (map fst tys')).
    {
      intros x Hinx.
      apply Hall in Hinx.
      destruct (in_dec funsym_eq_dec x (map fst tys')); auto.
      discriminate.
    }
    assert (Hlen2: length (adt_constr_list a) <= length (map fst tys')). {
      apply NoDup_incl_length; auto.
    }
    lia.
  - (*And the other direction*)
    apply Nat.eqb_neq.
    intros Hlen.
    rewrite forallb_false in Hall.
    assert (Hsub2: sublist (adt_constr_list a) (map fst tys')).
    {
      apply NoDup_length_incl; auto. lia.
    }
    destruct Hall as [x [Hinx Hnotx]].
    destruct (in_dec funsym_eq_dec x (map fst tys')); [discriminate|].
    apply n.
    apply (Hsub2 x); auto.
Qed.

Lemma populate_all_ext {A: Type} f1 f2 (rl : list (list pattern * A)):
  (forall x, f1 x = f2 x) ->
  populate_all f1 rl = populate_all f2 rl.
Proof.
  intros Hext.
  unfold populate_all.
  destruct (get_heads rl); auto.
  apply fold_left_opt_change_f.
  intros b1 p. revert b1.
  induction p; simpl; intros; auto.
  - destruct b1 as [css csl].
    rewrite Hext. auto.
  - rewrite IHp1. destruct (populate f2 b1 p1); simpl; auto.
Qed.

Lemma in_cslist_typed {c ps ty tys vs rl types_cslist constr}
  (Hp: pat_matrix_typed (ty :: tys) rl)
  (Hpop: populate_all constr rl = Some types_cslist)
  (Hsimp: simplified rl):
  In (c, vs, ps) (snd (types_cslist)) ->
  pattern_has_type gamma (Pconstr c vs ps) ty.
Proof.
  intros Hinc.
  assert (Hconstrc: existsb (constr_args_at_head_strong c vs ps) rl).
  {
    eapply populate_all_snd_strong; auto.
    apply Hpop. auto.
  }
  apply existsb_exists in Hconstrc.
  destruct Hconstrc as [row [Hinrow Hstrong]].
  revert Hp. simpl.
  unfold pat_matrix_typed. intros [Hrows _].
  rewrite Forall_forall in Hrows.
  specialize (Hrows _ Hinrow).
  unfold constr_args_at_head_strong in Hstrong.
  destruct row as [[| p1 row1] a1]; [discriminate|].
  simpl in Hstrong.
  destruct p1 as [| f1 tys1 pats1 | | |]; try discriminate.
  destruct (funsym_eqb_spec f1 c); subst; [|discriminate].
  destruct (list_eqb_spec _ vty_eq_spec vs tys1); subst; [|discriminate].
  destruct (list_eqb_spec _ pattern_eqb_spec ps pats1); subst; [|discriminate].
  inversion Hrows; subst; auto.
Qed.

Lemma in_cslist_args {c ps tys m a vs args rl types_cslist constr}
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (Hp: pat_matrix_typed ((vty_cons (adt_name a) vs) :: tys) rl)
  (Hpop: populate_all constr rl = Some types_cslist)
  (Hsimp: simplified rl):
  In (c, args, ps) (snd (types_cslist)) ->
  constr_in_adt c a /\ args = vs.
Proof.
  intros Hinc. pose proof (in_cslist_typed Hp Hpop Hsimp Hinc) as Hclist_types.
  inversion Hclist_types; subst.
  destruct H11 as [m1 [a1 [m_in1 [a_in1 c_in1]]]].
  rewrite (adt_constr_ret gamma_valid m_in1 a_in1) in H2; auto.
  unfold sigma in H2. rewrite ty_subst_cons in H2.
  inversion H2; subst.
  assert (m1 = m) by (apply (mut_adts_inj (valid_context_wf _ gamma_valid) m_in1 m_in a_in1 a_in); auto).
  subst.
  assert (a1 = a) by (apply (adt_names_inj' gamma_valid a_in1 a_in m_in); auto). subst.
  split; [exact c_in1 |].
  rewrite <- (adt_constr_params gamma_valid m_in a_in c_in1).
  rewrite map_ty_subst_var; auto. apply s_params_Nodup.
Qed.

Lemma in_cslist_val {c ps ty tys vs rl types_cslist constr}
  (Hp: pat_matrix_typed (ty :: tys) rl)
  (Hpop: populate_all constr rl = Some types_cslist)
  (Hsimp: simplified rl):
  In (c, vs, ps) (snd (types_cslist)) ->
  Forall (valid_type gamma) (map (ty_subst (s_params c) vs) (s_args c)).
Proof.
  intros Hin. pose proof (in_cslist_typed Hp Hpop Hsimp Hin) as Hclist_types.
  inversion Hclist_types; subst. rewrite Forall_nth. intros i d. simpl_len; intros Hi.
  apply pat_has_type_valid with (p:=nth i ps Pwild).
  specialize (H8 (nth i ps Pwild, nth i 
    (map (ty_subst (s_params c) vs) (s_args c)) d)).
  apply H8. rewrite in_combine_iff by solve_len.
  exists i. split; [lia|]. intros d1 d2.
  f_equal; apply nth_indep; [| solve_len]; lia.
Qed.

Lemma compile_bare_single_pat_typed {ty ps}
  (Htyps1: Forall (fun p => pattern_has_type gamma p ty) (map fst ps))
  (Htyps2: Forall (fun t => gen_typed gamma b t ret_ty) (map snd ps)):
  pat_matrix_typed [ty] (map (fun x => ([fst x], snd x)) ps).
Proof.
  unfold pat_matrix_typed.
  split.
  - rewrite Forall_forall.
    intros x Hinx.
    unfold row_typed.
    rewrite in_map_iff in Hinx.
    destruct Hinx as [y [Hx Hiny]]; subst.
    rewrite Forall2_combine.
    split; auto; simpl.
    rewrite Forall_map in Htyps1.
    rewrite Forall_forall in Htyps1.
    constructor; simpl; auto.
  - rewrite Forall_forall. intros x Hinx.
    rewrite Forall_map, Forall_forall in Htyps2.
    rewrite in_map_iff in Hinx.
    destruct Hinx as [y [Hx Hiny]]; subst.
    apply Htyps2; auto.
Qed.

Lemma populate_all_snd_hd_none {A: Type} {constr} 
  {rl: list (list pattern * A)} {o}:
  simplified rl ->
  populate_all constr rl = Some o ->
  hd_error (snd o) = None ->
  amap_is_empty (fst o).
Proof.
  intros Hsimp Hpop Hhd. apply hd_error_null_iff in Hhd.
  rewrite (amap_is_empty_get funsym_eq_dec).
  intros f.
  destruct (amap_get funsym_eq_dec (fst o) f) as [y|] eqn : Hget; auto.
  rewrite (proj2 (populate_all_fst_snd_full  _ _ _ Hsimp Hpop)) in Hget.
  rewrite Hhd in Hget. destruct_all; contradiction.
Qed.

Lemma populate_all_snd_hd_some {A: Type} {constr cs tys ps} 
  {rl: list (list pattern * A)} {o}:
  simplified rl ->
  populate_all constr rl = Some o ->
  hd_error (snd o) = Some (cs, tys, ps) ->
  amap_get funsym_eq_dec (fst o) cs = Some ps.
Proof.
  intros Hsimp Hpop Hhd.
  rewrite (proj2 (populate_all_fst_snd_full  _ _ _ Hsimp Hpop)).
  exists tys. destruct (snd o); simpl in Hhd; [discriminate|];
  inversion Hhd; subst; simpl; auto.
Qed.
  

(*Now we prove that if we have a simple, exhaustive pattern match, 
  then [compile] returns Some*)
Lemma compile_simple_exhaust {m: mut_adt} {a: alg_datatype} {vs: list vty} 
  {t: term} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (ps: list (pattern * gen_term b))
  (Hsimp: simple_pat_match (map fst ps))
  (Hex: simple_exhaust (map fst ps) a)
  (Hty: term_has_type gamma t (vty_cons (adt_name a) vs))
  (Htyps1: Forall (fun p => pattern_has_type gamma p (vty_cons (adt_name a) vs)) (map fst ps))
  (Htyps2: Forall (fun t => gen_typed gamma b t ret_ty) (map snd ps))
  (Hnull: negb (null ps)):
  compile_bare_single b false t (vty_cons (adt_name a) vs) ps <> None.
Proof.
  Opaque dispatch1_opt. Opaque comp_cases. Opaque comp_full.
  unfold compile_bare_single, compile_bare.
  (*Don't think I need induction here, let's see*)
  destruct ps as [|[phd tm1] ptl]; [discriminate|].
  simpl. simp compile.
  set (ps:=(phd, tm1) :: ptl) in *.
  set (rl:=( map (fun x : pattern * gen_term b => ([fst x], snd x)) ps)) in *.
  replace (([phd], tm1) :: map (fun x  => ([fst x], snd x)) ptl) with rl by reflexivity.
  simpl.
  assert (Hmxty: pat_matrix_typed [vty_cons (adt_name a) vs] rl).
  { apply compile_bare_single_pat_typed; auto. }
  assert (Hsimp_pat: forall p,
    simple_pat p -> simplified_aux p).
  {
    intros p. unfold simple_pat, simplified_aux.
    destruct p; auto.
  }
  (*Want lemma: simple_pat_match implies simplified*)
  assert (Hsimpl: simplified rl).
  {
    unfold rl, simplified.
    apply forallb_forall.
    setoid_rewrite in_map_iff.
    unfold simple_pat_match in Hsimp.
    do 2 (apply andb_true_iff in Hsimp; destruct Hsimp as [Hsimp _]).
    rewrite forallb_forall in Hsimp.
    intros x [y [Hx Hiny]]; subst. simpl. apply Hsimp_pat, Hsimp.
    rewrite in_map_iff. exists y; unfold ps; simpl; auto. 
  }
  (*First, show [populate_all] is Some*)
  pose proof (typed_populate_all_true true (vty_cons (adt_name a) vs) nil rl
    Hmxty Hsimpl) as Hpop.
  simpl in Hpop.
  destruct (populate_all (fun fs : funsym => f_is_constr fs && true) rl) as [types_cslist|] eqn : Hpop2;
  [| contradiction]. clear Hpop.
  (*Now show that [dispatch1] is Some*)
  destruct (dispatch1_opt gen_let t (fst types_cslist) rl) as [casewild|] eqn : Hdisp.
  2: {
    apply dispatch1_opt_none in Hdisp.
    rewrite (pat_matrix_typed_not_null Hmxty) in Hdisp.
    discriminate.
  }
  assert (Hwilds: snd casewild = default rl). {
    apply dispatch1_opt_some in Hdisp.
    destruct Hdisp as [Hnotnull Hcasewild]; subst.
    rewrite dispatch1_equiv_default; auto.
  }
  set (comp_wilds :=compile (fun _ => nil) gen_match gen_let gen_getvars true false nil (snd casewild)) in *.
  set (comp_cases :=
    fun (cs : funsym) (al : list (term * vty)) =>
    match (amap_get funsym_eq_dec (fst casewild) cs ) as o return amap_get funsym_eq_dec (fst casewild) cs = o -> _ with
    | None => fun _ => None (*impossible*)
    | Some l => fun Hget => compile (fun _ => nil) gen_match gen_let gen_getvars true false
      (rev al ++ nil) l
    end eq_refl).
  simpl.
  set (comp_full :=
    comp_full gen_match gen_getvars true (fun _ => comp_wilds) comp_cases (fst types_cslist) 
      (snd types_cslist) nil t (vty_cons (adt_name a) vs)
    nil rl) in *.
  assert (Hcompwilds: negb (null (default rl)) -> comp_wilds <> None).
  {
    intros Hnotnull.
    unfold comp_wilds; rewrite Hwilds.
    apply compile_all_wild; auto.
    - (*Prove that all [var_or_wild]*)
      unfold rl. unfold default.
      rewrite omap_map. simpl fst. cbv iota.
      intros p. rewrite in_concat. setoid_rewrite in_map_iff.
      setoid_rewrite in_omap_iff.
      intros [ps1 [[[ps2 t2] [Hps1 [[p3 t3] [Hinpt Hp3]]]] Hinp]];
      simpl in Hps1, Hp3; subst ps2.
      destruct p3; try discriminate.
      inversion Hp3; subst. contradiction.
    - eapply default_typed; eauto.
  }
  (*Useful result for proving negb (null (default rl))*)
  assert (Hdefaultnull: forall cs,
    constr_in_adt cs a ->
    amap_mem funsym_eq_dec cs (fst types_cslist) = false ->
    negb (null (default rl))).
  {
    intros cs Hincs Hmem.
    unfold simple_exhaust in Hex.
    apply orb_true_iff in Hex.
    destruct Hex as [Hallconstrs | Hhaswild].
    - (*contradict not mem*)
      rewrite forallb_forall in Hallconstrs.
      rewrite constr_in_adt_eq in Hincs.
      specialize (Hallconstrs _ Hincs).
      rewrite existsb_exists in Hallconstrs.
      destruct Hallconstrs as [p [Hinp Hp]].
      destruct p as [| f1 tys1 ps1 | | |]; try discriminate.
      destruct (funsym_eqb_spec f1 cs); [|discriminate]; subst.
      assert (Hconstr: constr_at_head_ex cs rl).
      {
        unfold constr_at_head_ex. apply existsb_exists.
        unfold rl.
        setoid_rewrite in_map_iff.
        rewrite in_map_iff in Hinp.
        destruct Hinp as [[p1 t1] [Hp1 Hinpt]];
        simpl in Hp1; subst.
        exists ([Pconstr cs tys1 ps1],t1 ). split; simpl; auto.
        - exists (Pconstr cs tys1 ps1, t1); split; auto.
        - unfold constr_at_head. simpl. destruct (funsym_eqb_spec cs cs); auto.
      }
      rewrite <- populate_all_in in Hconstr; eauto.
      rewrite Hmem in Hconstr. discriminate.
    - (*If there is a wild, clearly default cannot be nil*)
      destruct (default rl) eqn : Hdef; auto.
      unfold default in Hdef.
      rewrite (omap_nil (fun x =>
        match fst x with
        | Pwild :: ps0 => Some (ps0, snd x)
        | _ => None
        end) rl) in Hdef. (*We have to give the function for some reason*)
      rewrite existsb_exists in Hhaswild.
      destruct Hhaswild as [p [Hinp Hp]].
      destruct p; try discriminate.
      rewrite in_map_iff in Hinp.
      destruct Hinp as [[p1 t1] [Hp1 Hinpt]]; simpl in Hp1; subst.
      specialize (Hdef ([Pwild], t1)).
      forward Hdef.
      { unfold rl. rewrite in_map_iff. exists (Pwild, t1); auto. }
      discriminate.
  }
  (*And a lemma for spec*)
  assert (Hspecnull: forall cs,
    amap_mem funsym_eq_dec cs (fst types_cslist) ->
    negb (null (spec rl cs))).
  {
    intros f Hmemf.
    erewrite populate_all_in in Hmemf; eauto.
    clear -Hmemf.
    induction rl as [| [h a] t IH]; simpl in *; auto.
    apply orb_true_iff in Hmemf.
    destruct Hmemf as [Hhd | Htl].
    - unfold constr_at_head in Hhd.
      simpl in Hhd.
      destruct h as [| phd1 ptl1]; [discriminate|].
      destruct phd1 as [| f1 tys1 ps1 | | |]; try discriminate.
      destruct (funsym_eqb_spec f1 f); [| discriminate].
      reflexivity.
    - apply IH in Htl.
      destruct h as [| phd1 ptl1]; auto.
      destruct phd1 as [| f1 tys1 ps1 | | |]; auto.
      destruct (funsym_eqb f1 f); auto.
  }
  (*Prove [var_or_wild] for [spec]*)
  assert (Hspecvarwild: forall cs,
    forall x, In x (concat (map fst (spec rl cs))) ->
      var_or_wild x).
  {
    intros cs.
    clear -Hsimp.
    unfold simple_pat_match in Hsimp.
    apply andb_true_iff in Hsimp.
    destruct Hsimp as [Hsimp _].
    apply andb_true_iff in Hsimp.
    destruct Hsimp as [Hsimp _].
    subst rl.
    induction ps as [| phd1 ptl1]; simpl; [contradiction|].
    simpl in Hsimp.
    apply andb_true_iff in Hsimp.
    destruct Hsimp as [Hhd Hsimp].
    unfold simple_pat in Hhd.
    intros p.
    destruct phd1 as [phd1 a].
    simpl in Hhd |- *.
    destruct phd1 as [| f1 tys1 ps1 | | |]; auto.
    - (*funsym case*)
      destruct (funsym_eqb_spec f1 cs); simpl; auto.
      rewrite app_nil_r.
      rewrite in_app_iff, <- In_rev.
      intros [Hinp | Hinp]; auto.
      rewrite forallb_forall in Hhd.
      apply Hhd in Hinp.
      destruct p; auto.
    - (*Pwild case*)
      simpl. rewrite app_nil_r, in_app_iff.
      intros [Hp | Hp]; subst; auto.
      apply repeat_spec in Hp; subst; auto.
  }
  destruct (amap_is_empty (fst types_cslist)) eqn : Htypesemp.
  { 
    (*If empty, use wilds and prove default cannot be empty*)
    apply Hcompwilds.
    destruct (ne_list_nonemp (adt_constrs a)) as [cs Hincs].
    apply Hdefaultnull with (cs:=cs); auto.
    - apply constr_in_adt_eq; auto.
    - apply amap_is_empty_mem; auto.
  }
  assert (Hpop3: populate_all (fun fs => f_is_constr fs) rl = Some types_cslist).
  {
    erewrite populate_all_ext. apply Hpop2. simpl. intros. rewrite andb_true_r.
    reflexivity. 
  }
  assert (Hallconstr: forall cs y,
    amap_get funsym_eq_dec (fst types_cslist) cs = Some y ->
    constr_in_adt cs a).
  {
    intros cs1 y1 Hget1.
    apply (populate_all_in_adt m_in a_in Hsimpl Hmxty Hpop3 Hget1).
  }
  (*The big case: [comp_full] succeeds*)
  assert (Hcompfull: comp_full tt <> None).
  {
    Transparent Pattern.comp_full.
    unfold comp_full, Pattern.comp_full.
    destruct (hd_error (snd types_cslist)) as [[[cs tys2] ps2]|] eqn : Hchoose.
    2: {
      apply (populate_all_snd_hd_none Hsimpl Hpop2) in Hchoose.
      rewrite Htypesemp in Hchoose; discriminate.
    }
    simpl. apply (populate_all_snd_hd_some Hsimpl Hpop2) in Hchoose.
    (*First, prove that cs in adt*)
    assert (cs_in: constr_in_adt cs a) by (apply Hallconstr in Hchoose; auto).  
    rewrite (size_check_equal m_in a_in cs_in Hsimpl Hmxty Hpop3 Hchoose).
    set (no_wilds := forallb (fun f : funsym => amap_mem funsym_eq_dec f (fst types_cslist))
      (adt_constr_list a)) in *.
    set (base :=(if no_wilds then Some [] else option_map (fun x : gen_term b => [(Pwild, x)]) comp_wilds)) in *.
    destruct base as [bse|] eqn : Hbase.
    2: {
      (*contradiction - wilds is Some*)
      unfold base in Hbase. destruct no_wilds eqn : Hnowild; try discriminate.
      destruct comp_wilds; try discriminate.
      exfalso. forward Hcompwilds; [| contradiction].
      unfold no_wilds in Hnowild.
      apply forallb_false in Hnowild.
      destruct Hnowild as [f [f_in Hnotmem]].
      apply Hdefaultnull with (cs:=f).
      - apply constr_in_adt_eq; auto.
      - apply ssrbool.negbTE; auto.
    }
    simpl.
    (*Now make [fold_left_opt] easier to work with*)
    destruct (fold_left_opt (add gen_getvars comp_cases t (vty_cons (adt_name a) vs) rl [])
      (snd types_cslist) bse) as [pats|] eqn : Hadd; [discriminate|].
    (*Need to prove that None gives us contradiction*)
    apply fold_left_opt_none in Hadd.
    destruct Hadd as [l1 [x [l2 [y1 [Htypes [Hfold Hadd]]]]]].
    (*the contradiction arises from the "add" - it cannot be None*)
    destruct x as [[cs1 tys1] ps1].
    revert Hadd.
    simpl.
    unfold rev_map. rewrite !map_rev, !rev_involutive.
    destruct (comp_cases _ _) eqn : Hcomp; [discriminate|].
    unfold comp_cases in Hcomp.
    (*Need to prove that get cs1 is true - because cs1 is in [ snd types_cslist]*)
    revert Hcomp. 
    apply dispatch1_opt_some in Hdisp.
    destruct Hdisp as [Hnotnull Hcasewild]; subst casewild.
    assert (Hinc: In (cs1, tys1, ps1) (snd types_cslist)).
    { rewrite Htypes. rewrite !in_app_iff; simpl; auto.  }
    assert (Hgettypes: amap_get funsym_eq_dec (fst types_cslist) cs1 = Some ps1).
    {
      apply (populate_all_fst_snd_full _ _ _ Hsimpl Hpop3).
      exists tys1; assumption. 
    }
    erewrite (dispatch1_equiv_spec); eauto;
    [|rewrite amap_mem_spec, Hgettypes; auto].
    (*Info from typing*)
    assert (Hpty: pattern_has_type gamma (Pconstr cs1 tys1 ps1) (vty_cons (adt_name a) vs))
      by (eapply in_cslist_typed; eauto).
    destruct (in_cslist_args m_in a_in Hmxty Hpop2 Hsimpl Hinc) as [c_in Htys];
    subst tys1.
    pose proof (in_cslist_val Hmxty Hpop2 Hsimpl Hinc) as Hallval.
    assert (Hlenps1: Datatypes.length ps1 = Datatypes.length (s_args cs1)).
    { inversion Hpty; auto. }
    rewrite map_snd_combine by solve_len.
    intros Hcomp.
    (*Now use [compile_all_wild]*)
    exfalso. eapply compile_all_wild.
    5: apply Hcomp. all: auto.
    - apply Hspecvarwild.
    - (*prove term typing*)
      rewrite app_nil_r.
      rewrite !map_rev, map_fst_combine, map_snd_combine; [| solve_len | solve_len].
      apply Forall2_rev.
      apply Forall2_nth. simpl_len. rewrite <- Hlenps1, Nat.min_id.
      split; auto. intros i d1 d2 Hi.
      rewrite map_nth_inbound with (d2:=(""%string, vty_int)) by solve_len.
      rewrite combine_nth by solve_len.
      apply T_Var'; auto; [| simpl; apply nth_indep; solve_len].
      rewrite Forall_nth in Hallval.
      apply Hallval; solve_len.
    - (*prove pat matrix typed*)
      rewrite app_nil_r, map_rev, map_snd_combine by solve_len.
      pose proof (spec_typed_adt m_in a_in c_in Hmxty) as Hmx.
      rewrite app_nil_r in Hmx. apply Hmx.
    - (*Prove not null*)
      apply Hspecnull.
      rewrite amap_mem_spec, Hgettypes.
      reflexivity.
  }
  exact Hcompfull.
Qed.

End SimplePat.

(*Meta-theorem for proving results about well-typed things
  We only give the "Some" version*)
Section ProvedTyped.
Variable (bare: bool).
Variable (simpl_constr: bool).

(*Prove typing list equality for full case*)
Lemma constr_case_tys {P: term -> vty -> Prop} 
  {vars typs tl} (Hlen: length vars = length typs) (Hty: Forall2 P (map Tvar vars) typs)
  (Htytl: Forall2 P (map fst tl) (map snd tl)):
  Forall2 P (map fst (rev (combine (map Tvar vars) typs) ++ tl))
    (map snd (rev (combine (map Tvar vars) typs) ++ tl)).
Proof.
  rewrite !map_app. apply Forall2_app; auto. 
  rewrite !map_rev. apply Forall2_rev.
  rewrite map_fst_combine, map_snd_combine by solve_len. auto.
Qed. 

(*And similar to pattern*)
Lemma constr_case_patty {cs tys1 n t ty args tl rl rl'} (Hn: n = length (s_args cs)) (Htysargs: tys1 = args):
  let new_typs := (map (ty_subst (s_params cs) tys1) (s_args cs)) in
  let new_vars :=(combine (gen_strs n
    (compile_fvs (@gen_getvars b) ((t, ty) :: tl) rl)) new_typs) in
  pat_matrix_typed (rev (ty_subst_list (s_params cs) args (s_args cs)) ++ map snd tl) rl' ->
  pat_matrix_typed (map snd (rev (combine (map Tvar new_vars) new_typs) ++ tl)) rl'.
Proof.
  simpl. rewrite !map_app. intros Hp.
  rewrite !map_rev. rewrite map_snd_combine; [| unfold vsymbol in *; solve_len].
  subst. auto.
Qed.

Lemma Forall2_firstn {A B: Type} (P: A -> B -> Prop) (n: nat) (l1: list A) (l2: list B):
  Forall2 P l1 l2 ->
  Forall2 P (firstn n l1) (firstn n l2).
Proof.
  revert n l2. induction l1 as [| h1 t1 IH]; intros [| n'] [| h2 t2]; simpl; auto; intros Hall;
  inversion Hall; subst. constructor; auto.
Qed.

Lemma tfun_case_tys {cs args tl tms} {P: term -> vty -> Prop}:
let new_typs := (map (ty_subst (s_params cs) args) (s_args cs)) in
forall
(Htms': Forall2 P tms new_typs)
(Htytl: Forall2 P (map fst tl) (map snd tl)),
Forall2 P (map fst (rev (combine tms new_typs) ++ tl))
   (map snd (rev (combine tms new_typs) ++ tl)).
Proof.
  simpl. intros Hall1 Hall2. rewrite !map_app. apply Forall2_app; auto.
  rewrite !map_rev. apply Forall2_rev. rewrite !map_fst_combine_eq, !map_snd_combine_eq, !map_length.
  apply Forall2_firstn; auto.
Qed.

Lemma tfun_case_patty {cs args rl} {tms : list term} {tl} (Hlen: length tms = length (s_args cs)):
  let new_typs := (map (ty_subst (s_params cs) args) (s_args cs)) in
  forall (Hpat: pat_matrix_typed (rev new_typs ++ map snd tl) rl),
    pat_matrix_typed (map snd (rev (combine tms new_typs) ++ tl)) rl.
Proof.
  intros new_typs Hp.
  rewrite map_app, map_rev, map_snd_combine; [| subst new_typs; solve_len].
  auto.
Qed.  

(*Get ADT info - need in multiple places*)
Lemma amap_empty_get_adt
  {ty tl rl} {is_constr: funsym -> bool} {types_cslist}
  (Hsimpl: simplified rl)
  (Hpop: populate_all is_constr rl = Some types_cslist)
  (Hisemp: amap_is_empty (fst types_cslist) = false)
  (Hp: pat_matrix_typed (ty :: tl) rl):
  exists (m : mut_adt) (a : alg_datatype) (args : list vty),
  mut_in_ctx m gamma /\
  adt_in_mut a m /\
  ty = vty_cons (adt_name a) args /\ Datatypes.length args = Datatypes.length (m_params m).
Proof.
  rewrite (amap_not_empty_mem funsym_eq_dec) in Hisemp.
  destruct Hisemp as [c Hintypes].
  (*From [types], know that c is in first column*)
  apply (populate_all_in _ _ _ _ Hsimpl Hpop) in Hintypes.
  destruct (constr_at_head_ex_type Hp Hintypes) as [tys [pats Hcty]].
  simpl in Hcty.
  inversion Hcty; subst.
  (*Use fact that constructor patterns must arise from ADT*)
  destruct H11 as [m [a [m_in [a_in c_in]]]].
  exists m. exists a. unfold sigma.
  rewrite (adt_constr_ret gamma_valid m_in a_in c_in).
  rewrite ty_subst_cons. rewrite !map_map.
  eexists. split_all; try assumption. reflexivity.
  solve_len.
Qed.

(*And info about Tfun case*)
Lemma tfun_case_typing_info {cs params tms args a m tl}
  (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m)
  (args_len: length args = length (m_params m))
  (f_constr: f_is_constr cs)
  (Htmtys1: Forall2 (term_has_type gamma) (Tfun cs params tms :: map fst tl)
    (vty_cons (adt_name a) args :: map snd tl)):
  term_has_type gamma (Tfun cs params tms) (vty_cons (adt_name a) args) /\
  constr_in_adt cs a /\
  length (s_params cs) = length args /\
  Forall2 (term_has_type gamma) tms (ty_subst_list (s_params cs) params (s_args cs)) /\ params = args.
Proof.
  pose proof (Forall2_inv_head Htmtys1) as Htyt. simpl in Htyt. split; auto.
  assert (f_in: constr_in_adt cs a). {
    
    assert (f_constr': f_is_constr cs) by auto.
    rewrite (is_constr_iff gamma gamma_valid) in f_constr'.
    2: solve[inversion Htyt; subst; auto].
    destruct f_constr' as [m1 [a1 [m1_in [a1_in f_in]]]].
    (*Show that they are the same y relating [adt_name]*)
    inversion Htyt; subst.
    rewrite (adt_constr_subst_ret gamma_valid m1_in a1_in f_in) in H2 by auto.
    inversion H2; subst.
    assert (Hm: m1 = m) by
      (apply (mut_adts_inj (valid_context_wf _ gamma_valid) m1_in m_in a1_in a_in); auto).
    subst.
    assert (Ha: a1 = a) by (apply (adt_names_inj' gamma_valid a1_in a_in); auto).
    subst. assumption.
  }
  assert (constrs_len: length (s_params cs) = length args).
  {
    rewrite args_len. f_equal. apply (adt_constr_params gamma_valid m_in a_in f_in).
  }
  assert (Htms': Forall2 (term_has_type gamma) tms
    (ty_subst_list (s_params cs) params (s_args cs))).
  {
    inversion Htyt; subst. unfold ty_subst_list.
    rewrite Forall2_combine. split; [solve_len|]. assumption.
  }
  assert (Heqty: params = args). {
    inversion Htyt; subst.
    rewrite (adt_constr_ret gamma_valid m_in a_in f_in) in H2.
    rewrite ty_subst_cons in H2.
    assert (Hparams: s_params cs = m_params m) by
      apply (adt_constr_params gamma_valid m_in a_in f_in).
    rewrite <- Hparams in H2.
    rewrite map_ty_subst_var in H2; auto.
    - inversion H2; subst; auto.
    - apply s_params_Nodup.
  }
  split_all; auto.
Qed.

    (*Idea, need ADT in lots of places, we want the following:
      1. for emp case, prove wilds
      2. for rest, assume ADT and get info, need to prove the following
        a. comp_full case (unconditionally, only assuming not emp/ADT/etc)
        b. constr case, assuming simpl_constr and is_fun and everything else
        c. wild case, assuming simpl_constr, constr, but not in types
     should reduce duplication this way
      basically goal of this should be to provide
    1. typing proofs for IH so we dont have to prove each time
    2. ADT info in non-empty case
    3. info about cslist/more convenient IH with cslist
    so let's change this

*)
Lemma compile_prove_some_typed (P_hyps: list (term * vty) -> pat_matrix -> Prop) 
  (P_goal: forall (tms: list (term * vty)) (P: pat_matrix) (t: gen_term b)
    (Htmtys: Forall2 (term_has_type gamma) (map fst tms) (map snd tms))
    (Hp: pat_matrix_typed (map snd tms) P), Prop)
  (P_goal_irrel: forall tms P t Hty1 Hty2 Hp1 Hp2,
    P_goal tms P t Hty1 Hp1 -> P_goal tms P t Hty2 Hp2)
  (P_simp: forall t ty tms rl
    (Htmtys: Forall2 (term_has_type gamma) (map fst  ((t, ty) :: tms)) (map snd  ((t, ty) :: tms)))
    (Hp: pat_matrix_typed (ty :: map snd tms) rl)
    tm1
    (Hcomp: (compile get_constructors gen_match gen_let gen_getvars bare simpl_constr ((t, ty) :: tms) rl) = Some tm1)
    (Hsimpl:
        P_hyps ((t, ty) :: tms) (simplify gen_let t rl) -> 
      P_goal ((t, ty) :: tms) (simplify gen_let t rl) tm1 Htmtys (simplify_typed (Forall2_inv_head Htmtys) Hp))
    (Hhyps: P_hyps ((t, ty) :: tms) rl),
    P_goal ((t, ty) :: tms) rl tm1 Htmtys Hp)
  (Hemp: forall a l (Hhyps: P_hyps nil ((nil, a) :: l)) (Htyp: pat_matrix_typed nil ((nil, a) :: l)), 
      P_goal nil ((nil, a) :: l) a (Forall2_nil _) Htyp)
  (*Separate out cases*)
  (Hwildcase: forall t ty tl rl rhd rtl,
    let is_bare_css :=
    match ty with
    | vty_cons ts _ => if bare then (true, nil) else (false, get_constructors ts)
    | _ => (false, nil)
    end in
    let is_bare := fst is_bare_css in
    let css := snd is_bare_css in
    let is_constr fs := 
      f_is_constr fs && (is_bare || in_bool funsym_eq_dec fs css) in
    forall (Hsimpl: simplified rl) (Hrl: rl = rhd :: rtl) 
      types_cslist (Hpop: (populate_all is_constr rl) = Some types_cslist),
    let types := fst types_cslist in
    let cslist := snd types_cslist in
    forall casewild (Hcasewild : casewild = dispatch1 gen_let t types rl) (Hnotnull: forallb (fun x => negb (null (fst x))) rl),
    let cases := fst casewild in
    let wilds := snd casewild in
    forall (Hwilds: wilds = default rl) 
    (*Of course these are provable but we assume these as hypotheses for the user*)
    (Htytl: Forall2 (term_has_type gamma) (map fst tl) (map snd tl))
    (Htywild: pat_matrix_typed (map snd tl) (default rl))
    (IHwilds: forall tm1, P_hyps tl (default rl) -> 
      compile get_constructors gen_match gen_let gen_getvars bare simpl_constr tl wilds = Some tm1 -> 
      P_goal tl (default rl) tm1 Htytl Htywild)
    (Hisemp: amap_is_empty types) tm1
    (Hcomp: compile get_constructors gen_match gen_let gen_getvars bare simpl_constr tl wilds = Some tm1)
    (Hhyps: P_hyps ((t, ty) :: tl) rl)
    (Htmtys: Forall2 (term_has_type gamma) (map fst ((t, ty) :: tl)) (map snd ((t, ty) :: tl)))
    (Hp: pat_matrix_typed (map snd ((t, ty) :: tl)) rl),
    P_goal ((t, ty) :: tl) rl tm1 Htmtys Hp)
  (*Rest of cases all have ADT, don't want to duplicate lots of proofs*)
  (Hfullcase: forall t ty tl rl rhd rtl,
    let is_bare_css :=
    match ty with
    | vty_cons ts _ => if bare then (true, nil) else (false, get_constructors ts)
    | _ => (false, nil)
    end in
    let is_bare := fst is_bare_css in
    let css := snd is_bare_css in
    let is_constr fs := 
      f_is_constr fs && (is_bare || in_bool funsym_eq_dec fs css) in
    forall (Hsimpl: simplified rl) (Hrl: rl = rhd :: rtl) 
      types_cslist (Hpop: (populate_all is_constr rl) = Some types_cslist),
    let types := fst types_cslist in
    let cslist := snd types_cslist in
    forall casewild (Hcasewild : casewild = dispatch1 gen_let t types rl) (Hnotnull: forallb (fun x => negb (null (fst x))) rl),
      let cases := fst casewild in
      let wilds := snd casewild in
      forall
      (*Here, we can assume that our type is an ADT*)
      (m : mut_adt) (a : alg_datatype) (args : list vty) (m_in : mut_in_ctx m gamma)
      (a_in : adt_in_mut a m)
      (Hty : ty = vty_cons (adt_name a) args)
      (args_len : length args = length (m_params m))
      (Htytl: Forall2 (term_has_type gamma) (map fst tl) (map snd tl))
      (Htywild: pat_matrix_typed (map snd tl) (default rl))
      (*Full typing*)
      (*redundant*)
      (Htmty: Forall2 (term_has_type gamma) (t :: (map fst tl)) (ty :: (map snd tl)))
      (Hp: pat_matrix_typed ((vty_cons (adt_name a) args) :: map snd tl) rl)
      (*Info about [cslist] we will need*)
      (Hclist_types: forall {c tys pats},
        In (c, tys, pats) cslist ->
        pattern_has_type gamma (Pconstr c tys pats) (vty_cons (adt_name a) args))
      (Hclist_len: forall {c tys pats},
        In (c, tys, pats) cslist ->
        length pats = length (s_args c) (*follows directly from prvious but need in IH*))
      (Hclist_in: forall {c tys pats},
        In (c, tys, pats) cslist ->
        constr_in_adt c a)
      (Hclist_tys: forall {c tys pats},
        In (c, tys, pats) cslist ->
        tys = args)
      (*And finally, info about new types and vars*)
      (Hclist_new: forall {c tys1 ps1},
        In (c, tys1, ps1) cslist ->
        let new_typs := (map (ty_subst (s_params c) tys1) (s_args c)) in
        let new_vars :=(combine (gen_strs (Datatypes.length ps1) 
          (compile_fvs gen_getvars ((t, ty) :: tl) rl)) new_typs) in
        length new_vars = length new_typs /\
        Forall2 (term_has_type gamma) (map Tvar new_vars) new_typs /\
        pat_matrix_typed (rev new_typs ++ map snd tl) (spec rl c))

      (IHwilds: forall tm1, P_hyps tl (default rl) -> 
        compile get_constructors gen_match gen_let gen_getvars bare simpl_constr tl wilds = Some tm1 -> 
        P_goal tl (default rl) tm1 Htytl Htywild)
      (IHconstrs: forall (cs: funsym) (tys1: list vty) (ps1: list pattern)
        (*We do 3 things here 1. use In cslist instead of get for cases 2. prove typing once and for all 3. use spec,
          not l in list *)
        (Hinc: In (cs, tys1, ps1) cslist),
        let new_typs := (map (ty_subst (s_params cs) tys1) (s_args cs)) in
        let new_vars :=(combine (gen_strs (Datatypes.length ps1) 
          (compile_fvs gen_getvars ((t, ty) :: tl) rl)) new_typs) in
        forall tm1 (Hhyps: P_hyps (rev (combine (map Tvar new_vars) new_typs) ++ tl) (spec rl cs))
          (Hcomp: compile get_constructors gen_match gen_let gen_getvars bare simpl_constr 
            (rev (combine (map Tvar new_vars) new_typs) ++ tl) (spec rl cs) = Some tm1),
          P_goal  (rev (combine (map Tvar new_vars) new_typs) ++ tl) (spec rl cs) tm1 
            (constr_case_tys (proj1 (Hclist_new Hinc)) (proj1 (proj2 (Hclist_new Hinc))) Htytl) 
            (constr_case_patty (Hclist_len Hinc) (Hclist_tys Hinc) (spec_typed_adt m_in a_in (Hclist_in Hinc) Hp)))
      (Hisemp: amap_is_empty types = false)
      (ps ps1 : list (pattern * gen_term b))
      (Hopt : rev
         (map
            (add_map gen_getvars
               (fun (cs0 : funsym) (al0 : list (term * vty)) =>
                comp_cases (compile get_constructors gen_match gen_let gen_getvars bare simpl_constr)
                  cases tl cs0 al0) t ty tl rl) cslist) ++
       map (fun x : pattern * gen_term b => (fst x, Some (snd x))) ps1 =
       map (fun x : pattern * gen_term b => (fst x, Some (snd x))) ps)
      (no_wilds : option bool)
      (*NOTE: from typing, prove equivalent no matter if bare or not*)
      (Hnowilds: no_wilds = Some (forallb (fun f : funsym => amap_mem funsym_eq_dec f types) 
        (match ty with
          | vty_cons ts _ => get_constructors ts
          | _ => nil
        end)))
      (*Much more useful than destructing and simplifying each time*)
      (Hps1' : (ps1 = [] /\ no_wilds = Some true) \/ (no_wilds = Some false /\
              (exists t2 : gen_term b,
                 compile get_constructors gen_match gen_let gen_getvars bare simpl_constr tl wilds = Some t2 /\
                 ps1 = [(Pwild, t2)])))
      
      (Hhyps: P_hyps ((t, ty) :: tl) rl)
      (*silly*)
      (Hp': pat_matrix_typed (ty :: map snd tl) rl),
    P_goal ((t, ty) :: tl) rl (gen_match t ty ps) Htmty Hp')
  (*The case when we have a constr, but not in types. Also wild.
    If wild is unconditional, this is easy, but might not be - but we DO want ADT stuff here*)
  (Hconstrnotincase: forall t ty tl rl rhd rtl cs params tms,
    let is_bare_css :=
    match ty with
    | vty_cons ts _ => if bare then (true, nil) else (false, get_constructors ts)
    | _ => (false, nil)
    end in
    let is_bare := fst is_bare_css in
    let css := snd is_bare_css in
    let is_constr fs := 
      f_is_constr fs && (is_bare || in_bool funsym_eq_dec fs css) in
    forall (Hsimpl: simplified rl) (Hrl: rl = rhd :: rtl) 
      types_cslist (Hpop: (populate_all is_constr rl) = Some types_cslist),
      (*NOTE: we don't have maps, not ideal*)
      let types := fst types_cslist in
      let cslist := snd types_cslist in
      forall casewild (Hcasewild : casewild = dispatch1 gen_let t types rl) (Hnotnull: forallb (fun x => negb (null (fst x))) rl),
        let cases := fst casewild in
        let wilds := snd casewild in
      forall (*Here, we can assume that our type is an ADT*)
      (m : mut_adt) (a : alg_datatype) (args : list vty) (m_in : mut_in_ctx m gamma)
      (a_in : adt_in_mut a m)
      (Hty : ty = vty_cons (adt_name a) args)
      (args_len : length args = length (m_params m))
      (Htytl: Forall2 (term_has_type gamma) (map fst tl) (map snd tl))
      (Htywild: pat_matrix_typed (map snd tl) (default rl))
      (*Full typing*)
      (Htmty: Forall2 (term_has_type gamma) (t :: (map fst tl)) (ty :: (map snd tl)))
      (Hp: pat_matrix_typed ((vty_cons (adt_name a) args) :: map snd tl) rl)
      (*Info about the specific constructor*)
      (Hcsty: term_has_type gamma (Tfun cs params tms) (vty_cons (adt_name a) args))
      (f_in: constr_in_adt cs a)
      (constrs_len: length (s_params cs) = length args)
      (Heqty: params = args)
      (Htms': Forall2 (term_has_type gamma) tms (ty_subst_list (s_params cs) args (s_args cs)))
      (*Only need wild case*)
      (IHwilds: forall tm1, P_hyps tl (default rl) -> 
        compile get_constructors gen_match gen_let gen_getvars bare simpl_constr tl wilds = Some tm1 -> 
        P_goal tl (default rl) tm1 Htytl Htywild)
      (Hisemp: amap_is_empty types = false)
      (Hsimplconstr: simpl_constr = true)
      (Ht: t = Tfun cs params tms)
      (Hisconstr: is_constr cs)
      (Hmem: amap_mem funsym_eq_dec cs types = false) tm1
      (Hcomp: compile get_constructors gen_match gen_let gen_getvars bare simpl_constr tl wilds = Some tm1)
      (Hhyps: P_hyps ((t, ty) :: tl) rl)
      (*silly*)
      (Hp': pat_matrix_typed (ty :: map snd tl) rl), 
     P_goal ((t, ty) :: tl) rl tm1 Htmty Hp')
  (Hconstrcase: forall t ty tl rl rhd rtl cs params tms,
    let is_bare_css :=
    match ty with
    | vty_cons ts _ => if bare then (true, nil) else (false, get_constructors ts)
    | _ => (false, nil)
    end in
    let is_bare := fst is_bare_css in
    let css := snd is_bare_css in
    let is_constr fs := 
      f_is_constr fs && (is_bare || in_bool funsym_eq_dec fs css) in
    forall (Hsimpl: simplified rl) (Hrl: rl = rhd :: rtl) 
      types_cslist (Hpop: (populate_all is_constr rl) = Some types_cslist),
      let types := fst types_cslist in
      let cslist := snd types_cslist in
      forall casewild (Hcasewild : casewild = dispatch1 gen_let t types rl) (Hnotnull: forallb (fun x => negb (null (fst x))) rl),
        let cases := fst casewild in
        let wilds := snd casewild in
      forall (*Here, we can assume that our type is an ADT*)
      (m : mut_adt) (a : alg_datatype) (args : list vty) (m_in : mut_in_ctx m gamma)
      (a_in : adt_in_mut a m)
      (Hty : ty = vty_cons (adt_name a) args)
      (args_len : length args = length (m_params m))
      (Htytl: Forall2 (term_has_type gamma) (map fst tl) (map snd tl))
      (Htywild: pat_matrix_typed (map snd tl) (default rl))
      (*Full typing*)
      (Htmty: Forall2 (term_has_type gamma) (t :: (map fst tl)) (ty :: (map snd tl)))
      (Hp: pat_matrix_typed ((vty_cons (adt_name a) args) :: map snd tl) rl)
      (*Info about the specific constructor*)
      (Hcsty: term_has_type gamma (Tfun cs params tms) (vty_cons (adt_name a) args))
      (f_in: constr_in_adt cs a)
      (constrs_len: length (s_params cs) = length args)
      (tms_len: length tms = length (s_args cs))
      (Heqty: params = args)
      (Htms': Forall2 (term_has_type gamma) tms (ty_subst_list (s_params cs) args (s_args cs)))
      (*The IH we need*)
      (IHfun: 
        let new_typs := (map (ty_subst (s_params cs) args) (s_args cs)) in
        forall tm1
        (Hhyps: P_hyps (rev (combine tms new_typs) ++ tl) (spec rl cs))
        (Hcomp: compile get_constructors gen_match gen_let gen_getvars bare simpl_constr 
            (rev (combine tms new_typs) ++ tl) (spec rl cs) = Some tm1),
         P_goal  (rev (combine tms new_typs) ++ tl) (spec rl cs) tm1 (tfun_case_tys Htms' Htytl) 
            (tfun_case_patty tms_len (spec_typed_adt m_in a_in f_in Hp))) 
      (Hisemp: amap_is_empty types = false)
      (Hsimplconstr: simpl_constr = true)
      (Ht: t = Tfun cs params tms)
      (Hisconstr: is_constr cs)
      (Hmem: amap_mem funsym_eq_dec cs types) tm1
      (Hcomp: comp_cases (compile get_constructors gen_match gen_let gen_getvars bare simpl_constr) cases tl cs (combine tms
            (map (ty_subst (s_params cs) params) (s_args cs))) = Some tm1)
      (Hhyps: P_hyps ((t, ty) :: tl) rl)
      (*silly*)
      (Hp': pat_matrix_typed (ty :: map snd tl) rl), 
     P_goal ((t, ty) :: tl) rl tm1 Htmty Hp'):

    forall ts p tm1 (Hhyps: P_hyps ts p)
      (Htmtys: Forall2 (term_has_type gamma) (map fst ts) (map snd ts))
      (Hp: pat_matrix_typed (map snd ts) p)
      (Hcomp: (compile get_constructors gen_match gen_let gen_getvars bare simpl_constr ts p) = Some tm1), 
      P_goal ts p tm1 Htmtys Hp.
Proof.
  intros.
   eapply (compile_prove_some get_constructors gen_match gen_let gen_getvars
    gen_getvars_let bare simpl_constr (fun ts p =>P_hyps ts p /\
    Forall2 (term_has_type gamma) (map fst ts) (map snd ts) /\ pat_matrix_typed (map snd ts) p)
  (fun ts p tm1 => forall Htmtys Hp, P_goal ts p tm1 Htmtys Hp)); auto; clear -P_simp P_goal_irrel Hemp
    Hwildcase Hfullcase Hconstrnotincase Hconstrcase.
  - intros. destruct Hhyps as [Hhyps [Htmtys1 Hp1]]. apply P_simp; auto.
    intros Hhyps2. apply Hsimpl; split_all; auto.
    (*Prove simplify typed*)
    apply (simplify_typed (Forall2_inv_head Htmtys) Hp).
  - (*Prove nil case*)
    intros. destruct Hhyps as [Hhyps [Htmtys1 Hp1]].
    destruct ps as [| phd ptl].
    + eapply P_goal_irrel. eapply Hemp; eauto. Unshelve. auto.
    + (*Cannot have non-null row in this case*)
      exfalso.
      apply pat_matrix_typed_head in Hp.
      destruct Hp as [Hrow _]; inversion Hrow.
  - (*Prove wild cases*) 
    intros. destruct Hhyps as [Hhyps [Htmtys1 Hp1]].
    destruct (amap_is_empty types) eqn : Hisemp.
    + (*First case: empty types*)
      pose proof (Forall2_inv_tail Htmtys1) as Htytl.
      eapply Hwildcase with (Htywild := default_typed Hp)(Htytl:=Htytl); eauto.
      intros tm2 Hhyps2 Hcomp2. apply IHwilds; auto. split_all; auto.
      eapply default_typed; eauto.
      Unshelve. 
    + (*Second case: match on constr not in types*) 
      destruct Hwildcases as [? | Hwildcases];[discriminate|].
      destruct Hwildcases as [_ [Hsimplconstr [cs [params [tms [Ht [Hisconstr Hmem]]]]]]].
      destruct (amap_empty_get_adt Hsimpl Hpop Hisemp Hp) as [m [a [args [m_in [a_in [Hty args_len]]]]]].
      simpl in Hty; subst. (* eapply Hconstrnotincase; eauto. *)
      (*Crucially, need [f_is_constr] here*)
      assert (f_constr: f_is_constr cs) (*TODO: just need this, prove*).
      { unfold is_constr, is_bare, css, is_bare_css in Hisconstr. 
        apply andb_true_iff in Hisconstr; apply Hisconstr. }
      (*Get typing info*)
      destruct (tfun_case_typing_info m_in a_in args_len f_constr Htmtys1) as [Htyt [f_in [Hargslen [Htms' Hparams]]]].
      subst args.
      pose proof (Forall2_inv_tail Htmtys1) as Htytl.
      eapply Hconstrnotincase with (Htywild := default_typed Hp)(Htytl:=Htytl); eauto.
      (*Need to prove wilds again*)
      intros tm2 Hhyps2 Hcomp2. apply IHwilds; auto. split_all; auto.
      eapply default_typed; eauto.
  - intros. (*full case*)
    destruct Hhyps as [Hhyps [Htmtys1 Hp1]].
    (*Get the ADT*)
    destruct (amap_empty_get_adt Hsimpl Hpop Hisemp Hp) as [m [a [args [m_in [a_in [Hty args_len]]]]]].
    simpl in Hty; subst.
    pose proof (Forall2_inv_tail Htmtys1) as Htytl.
    assert (Hclist_types: forall {c tys pats},
      In (c, tys, pats) cslist ->
      pattern_has_type gamma (Pconstr c tys pats) (vty_cons (adt_name a) args)) by
      (intros c tys pats1 Hinc1; subst; apply (in_cslist_typed Hp Hpop Hsimpl Hinc1)).
    eapply Hfullcase with (Htywild := default_typed Hp)(Htytl:=Htytl); eauto. Unshelve. all: eauto.
    + (*Prove wilds again*)
      intros tm2 Hhyps2 Hcomp2. apply IHwilds; auto. split_all; auto.
      eapply default_typed; eauto.
    + (*Prove IH*) intros cs tys1 pats Hinc new_typs new_vars tm2 Hhyps2 Hcomp2.
      set (rl := rhd :: rtl) in *.
      specialize (IHconstrs cs (combine (map Tvar new_vars) new_typs) (spec rl cs)).
      forward IHconstrs.
      { unfold cases. eapply dispatch1_equiv_spec; eauto.
        rewrite amap_mem_spec.
        replace (amap_get funsym_eq_dec (fst types_cslist) cs) with (Some pats); auto.
        symmetry. apply (proj2 (populate_all_fst_snd_full _ _ _ Hsimpl Hpop)).
        exists tys1; apply Hinc.
      }
      assert (Hvarstyps: length new_vars = length new_typs). {
        unfold new_vars. simpl_len.
        assert (length pats = length new_typs); try lia.
        unfold new_typs. simpl_len; auto.
        specialize (Hclist_types _ _ _ Hinc); inversion Hclist_types; auto.
      }
      specialize (IHconstrs tm2).
      assert (Hlen: length pats = length (s_args cs)). {
        specialize (Hclist_types _ _ _ Hinc); inversion Hclist_types; subst; auto.
      }
      apply IHconstrs; auto.
            (*Simplify lists in IHConstrs*)
      rewrite !rev_combine, !map_app, !map_fst_combine, !map_snd_combine by solve_len.
      split_all; [rewrite <- rev_combine; auto; solve_len | |].
      * (*Prove terms are typed correctly*) 
        unfold vsymbol in *.
        apply Forall2_app.
        2: { inversion Htmtys; auto. }
        apply Forall2_rev.
        (*Prove all variables have correct type*)
        apply Forall2_nth; simpl_len; split; [auto|].
        intros i d1 d2 Hi.
        assert (Hi': i < length (s_args cs)) by
          (rewrite Hvarstyps in Hi; unfold new_typs in Hi; rewrite map_length in Hi; exact Hi).
        rewrite map_nth_inbound with (d2:=(""%string, vty_int)) by auto. 
        apply T_Var'.
        -- (*We proved [valid_type] already*)
          specialize (in_cslist_val Hp Hpop Hsimpl Hinc) as Hallval.
          rewrite Forall_forall in Hallval; apply Hallval, nth_In. solve_len.
        -- unfold new_vars, new_typs. rewrite combine_nth by solve_len.
            simpl. apply nth_indep; solve_len.
      * (*prove pat mx typed*)
        destruct (in_cslist_args m_in a_in Hp Hpop Hsimpl Hinc) as [c_in Htys1]; subst.
        apply (spec_typed_adt m_in a_in); auto.
    + set (ty := vty_cons (adt_name a) args) in *. 
      assert (Hiswilds : is_wilds = Some
        (forallb (fun f : funsym => amap_mem funsym_eq_dec f (fst types_cslist))
           (get_constructors (adt_name a)))).
      {
        unfold is_wilds.
        assert (Hisbare: is_bare -> bare). {
          unfold is_bare, is_bare_css.
          destruct bare; auto.
        }
        unfold is_bare, is_bare_css. subst ty.
        destruct bare; simpl; auto.
        (*Idea: if bare is true:
        1. amap_choose is Some
        2. result is well-typed so equal to [get_constructors]*)
        unfold cslist.
        destruct (hd_error (snd types_cslist)) as [[[cs tys2] ps2]|] eqn : Hchoose.
        2: {
          apply (populate_all_snd_hd_none Hsimpl Hpop) in Hchoose.
          unfold types in Hisemp.
          rewrite Hisemp in Hchoose; discriminate.
        }
        simpl. apply (populate_all_snd_hd_some Hsimpl Hpop) in Hchoose.
        f_equal.
        unfold types.
        assert (c_in: constr_in_adt cs a). {
          unfold types in Hchoose.
          apply (populate_all_in_adt m_in a_in Hsimpl Hp Hpop Hchoose).
        }
        erewrite (size_check_equal m_in a_in c_in Hsimpl Hp); [| | eauto].
        2: {
          erewrite populate_all_ext. apply Hpop.
          unfold is_constr, is_bare, is_bare_css. simpl.
          intros. rewrite andb_true_r; reflexivity.
        }
        rewrite (get_constructors_eq gamma_valid m_in a_in).
        reflexivity.
      }
      rewrite Hiswilds in Hps1'; apply Hps1'.
    + (*Prove patslen*)
      intros cs tys1 pats1 Hinc; specialize (Hclist_types _ _ _ Hinc); inversion Hclist_types; auto.
    + (*Prove all constrs in*)
      intros cs tys1 pats1 Hinc. apply (in_cslist_args m_in a_in Hp Hpop Hsimpl Hinc).
    + (*Prove tys = args*)
      intros cs tys1 pats1 Hinc. apply (in_cslist_args m_in a_in Hp Hpop Hsimpl Hinc).
    + (*Prove length and typing for elements*)
      intros cs tys1 pats1 Hinc new_typs new_vars.
      (*Use info from previous*)
      specialize (Hclist_types _ _ _ Hinc).
      assert (Hpatslen: length pats1 = length (s_args cs)) by (inversion Hclist_types; auto).
      assert (Hlenvars: length new_typs = length (s_args cs)) by (unfold new_typs; solve_len).
      assert (Hlen: length new_vars = length new_typs) by (unfold new_vars, new_typs; solve_len).
      split_all; auto.
      * (*Prove term types*)
        apply Forall2_nth; simpl_len; split; [auto|].
        intros i d1 d2 Hi.
        assert (Hi': i < length (s_args cs)) by (unfold vsymbol in *; lia).
        rewrite map_nth_inbound with (d2:=(""%string, vty_int)) by auto. 
        apply T_Var'.
        -- (*We proved [valid_type] already*)
          specialize (in_cslist_val Hp Hpop Hsimpl Hinc) as Hallval.
          rewrite Forall_forall in Hallval; apply Hallval, nth_In. solve_len.
        -- unfold new_vars, new_typs. rewrite combine_nth by solve_len.
            simpl. apply nth_indep; solve_len.
      * destruct (in_cslist_args m_in a_in Hp Hpop Hsimpl Hinc) as [c_in Hargs]; subst args.
        unfold new_typs.
        apply (spec_typed_adt m_in a_in c_in Hp).
  - (*Tfun case*)
    intros. destruct Hhyps as [Hhyps [Htmtys1 Hp1]].
    (*Get the ADT*)
    destruct (amap_empty_get_adt Hsimpl Hpop Hisemp Hp) as [m [a [args [m_in [a_in [Hty args_len]]]]]].
    simpl in Hty; subst. (* eapply Hconstrnotincase; eauto. *)
    (*Crucially, need [f_is_constr] here*)
    assert (f_constr: f_is_constr cs) (*TODO: just need this, prove*).
    { unfold is_constr, is_bare, css, is_bare_css in Hisconstr. 
      apply andb_true_iff in Hisconstr; apply Hisconstr. }
    (*Get typing info*)
    destruct (tfun_case_typing_info m_in a_in args_len f_constr Htmtys1) as [Htyt [f_in [Hargslen [Htms' Hparams]]]].
    subst args.
    pose proof (Forall2_inv_tail Htmtys1) as Htytl.
    eapply Hconstrcase with (Htytl:=Htytl); eauto; [eapply default_typed; eauto |].
    (*Prove IH goal*)
    intros new_typs tm2 Hhyps2 Hcomp2.
    apply IHconstrs with (cs:=cs); auto; [ eapply dispatch1_equiv_spec; solve[eauto] |].
    assert (Hlentms: length tms = length new_typs). {
      unfold new_typs. inversion Htyt; solve_len. }
    rewrite !map_app,!map_rev, !map_fst_combine, !map_snd_combine by solve_len.
    split_all; auto.
    + (*Term typing*)
      apply Forall2_app; [| inversion Htmtys1; solve[auto]].
      apply Forall2_rev, Htms'.
    + (*Pattern matrix typing*)
      apply (spec_typed_adt m_in a_in); auto.
    Unshelve. all: eauto.
    inversion Htyt; lia.
Qed.

End ProvedTyped.

Section CompileTheorem.

(*Do [comp_full case separately because it is very complicated*)
Lemma comp_full_correct (t : term) (ty : vty) (tl : list (term * vty)) 
  (rl : list (list pattern * gen_term b))
  (rhd : list pattern * gen_term b) (rtl : list (list pattern * gen_term b))
  (bare: bool) (simpl_constr: bool)
(Hsimp: simplified rl)
(Hrl: rl = rhd :: rtl):
let is_bare_css :=
  match ty with
  | vty_cons ts _ => if bare then (true, []) else (false, get_constructors ts)
  | _ => (false, [])
  end in
let is_bare := fst is_bare_css in
let css := snd is_bare_css in
let is_constr := fun fs : funsym => f_is_constr fs && (is_bare || in_bool funsym_eq_dec fs css) in
forall types_cslist  (Hpop: populate_all is_constr rl = Some types_cslist),
let types := fst types_cslist in
let cslist := snd types_cslist in
forall casewild (Hcasewild: casewild = dispatch1 gen_let t types rl)
  (Hnotnull: forallb (fun x : list pattern * gen_term b => negb (null (fst x))) rl),
let cases := fst casewild in
let wilds := snd casewild in
forall (m : mut_adt) (a : alg_datatype) (args : list vty) (m_in : mut_in_ctx m gamma)
  (a_in : adt_in_mut a m) (Hty: ty = vty_cons (adt_name a) args)
(args_len: length args = length (m_params m))
(Htytl : Forall2 (term_has_type gamma) (map fst tl) (map snd tl))
  (Htywild : pat_matrix_typed (map snd tl) (default rl))
  (Htmty : Forall2 (term_has_type gamma) (t :: map fst tl) (ty :: map snd tl))
  (Hp : pat_matrix_typed (vty_cons (adt_name a) args :: map snd tl) rl)
(Hclist_types: forall (c : funsym) (tys : list vty) (pats : list pattern),
 In (c, tys, pats) cslist -> pattern_has_type gamma (Pconstr c tys pats) (vty_cons (adt_name a) args))
  (Hclist_len : forall (c : funsym) (tys : list vty) (pats : list pattern),
                In (c, tys, pats) cslist -> Datatypes.length pats = Datatypes.length (s_args c))
  (Hclist_in : forall (c : funsym) (tys : list vty) (pats : list pattern),
               In (c, tys, pats) cslist -> constr_in_adt c a)
  (Hclist_tys : forall (c : funsym) (tys : list vty) (pats : list pattern),
                In (c, tys, pats) cslist -> tys = args)
  (Hclist_new : forall (c : funsym) (tys1 : list vty) (ps1 : list pattern),
                In (c, tys1, ps1) cslist ->
                let new_typs := map (ty_subst (s_params c) tys1) (s_args c) in
                let new_vars :=
                  combine (gen_strs (Datatypes.length ps1) (compile_fvs gen_getvars ((t, ty) :: tl) rl))
                    new_typs in
                Datatypes.length new_vars = Datatypes.length new_typs /\
                Forall2 (term_has_type gamma) (map Tvar new_vars) new_typs /\
                pat_matrix_typed (rev new_typs ++ map snd tl) (spec rl c))
(IHwilds: forall tm1 : gen_term b,
 True ->
 compile get_constructors gen_match gen_let gen_getvars bare simpl_constr tl wilds = Some tm1 ->
 exists Hty : gen_typed gamma b tm1 ret_ty,
   forall (pd : pi_dom) (pdf : pi_dom_full gamma pd) (pf : pi_funpred gamma_valid pd pdf)
     (vt : val_typevar) (v : val_vars pd vt),
   pat_matrix_var_names_disj (map fst tl) (default rl) ->
   matches_matrix_tms pd pdf pf vt v (map fst tl) (map snd tl) (default rl) Htytl Htywild =
   Some (gen_rep gamma_valid pd pdf pf vt v ret_ty tm1 Hty))
(IHconstrs: forall (cs : funsym) (tys1 : list vty) (ps1 : list pattern) (Hinc : In (cs, tys1, ps1) cslist),
 let new_typs := map (ty_subst (s_params cs) tys1) (s_args cs) in
 let new_vars :=
   combine (gen_strs (Datatypes.length ps1) (compile_fvs gen_getvars ((t, ty) :: tl) rl)) new_typs in
 forall tm1 : gen_term b,
 True ->
 compile get_constructors gen_match gen_let gen_getvars bare simpl_constr
   (rev (combine (map Tvar new_vars) new_typs) ++ tl) (spec rl cs) = Some tm1 ->
 exists Hty : gen_typed gamma b tm1 ret_ty,
   forall (pd : pi_dom) (pdf : pi_dom_full gamma pd) (pf : pi_funpred gamma_valid pd pdf)
     (vt : val_typevar) (v : val_vars pd vt),
   pat_matrix_var_names_disj (map fst (rev (combine (map Tvar new_vars) new_typs) ++ tl)) (spec rl cs) ->
   matches_matrix_tms pd pdf pf vt v (map fst (rev (combine (map Tvar new_vars) new_typs) ++ tl))
     (map snd (rev (combine (map Tvar new_vars) new_typs) ++ tl)) (spec rl cs)
     (constr_case_tys (proj1 (Hclist_new cs tys1 ps1 Hinc))
        (proj1 (proj2 (Hclist_new cs tys1 ps1 Hinc))) Htytl)
     (constr_case_patty (Hclist_len cs tys1 ps1 Hinc) (Hclist_tys cs tys1 ps1 Hinc)
        (spec_typed_adt m_in a_in (Hclist_in cs tys1 ps1 Hinc) Hp)) =
   Some (gen_rep gamma_valid pd pdf pf vt v ret_ty tm1 Hty))
(Htypesemp: amap_is_empty types = false) ps ps1
(Hpats: rev
  (map
     (add_map gen_getvars
        (fun (cs0 : funsym) (al0 : list (term * vty)) =>
         comp_cases (compile get_constructors gen_match gen_let gen_getvars bare simpl_constr) cases tl
           cs0 al0) t ty tl rl) cslist) ++
map (fun x : pattern * gen_term b => (fst x, Some (snd x))) ps1 =
map (fun x : pattern * gen_term b => (fst x, Some (snd x))) ps)
(no_wilds : option bool)
(Hnowilds: no_wilds =
Some
  (forallb (fun f : funsym => amap_mem funsym_eq_dec f types)
     match ty with
     | vty_cons ts _ => get_constructors ts
     | _ => []
     end))
(Hps: ps1 = [] /\ no_wilds = Some true \/
no_wilds = Some false /\
(exists t2 : gen_term b,
   compile get_constructors gen_match gen_let gen_getvars bare simpl_constr tl wilds = Some t2 /\
   ps1 = [(Pwild, t2)]))
(Hpty : pat_matrix_typed (ty :: map snd tl) rl),
exists Hty : gen_typed gamma b (gen_match t ty ps) ret_ty,
  forall (pd : pi_dom) (pdf : pi_dom_full gamma pd) (pf : pi_funpred gamma_valid pd pdf)
    (vt : val_typevar) (v : val_vars pd vt),
  pat_matrix_var_names_disj (map fst ((t, ty) :: tl)) rl ->
  matches_matrix_tms pd pdf pf vt v (map fst ((t, ty) :: tl)) (map snd ((t, ty) :: tl)) rl Htmty Hpty =
  Some (gen_rep gamma_valid pd pdf pf vt v ret_ty (gen_match t ty ps) Hty).
Proof.
  intros.
  (*Show that [bare] makes no difference - separate lemma?*)
  set (css':= (match ty with
      | vty_cons ts _ => get_constructors ts
      | _ => nil
    end)) in *.
  (*Instantiate IHconstrs for each possible constructor so that we don't need to
    do it multiple times*)
  assert (IHconstrs' : forall (c: funsym) tys1 ps1,
    In (c, tys1, ps1) cslist ->
    let ty := vty_cons (adt_name a) args in
    let new_typs := (map (ty_subst (s_params c) tys1) (s_args c)) in
    let new_vars :=(combine (gen_strs (length ps1) (compile_fvs gen_getvars ((t, ty) :: tl) rl)) new_typs) in
    forall (t: gen_term b),
        compile get_constructors gen_match gen_let gen_getvars bare simpl_constr (rev (combine (map Tvar new_vars) new_typs) ++ tl) (spec rl c) = Some t ->
    (*Exists so we only have to prove once*)
    exists (Htys: Forall2 (term_has_type gamma) ((rev (map Tvar new_vars)) ++ map fst tl)
      (rev new_typs ++ map snd tl))
      (Hp: pat_matrix_typed (rev new_typs ++ map snd tl) (spec rl c))
      (Hty: gen_typed gamma b t ret_ty),
      forall (pd : pi_dom) (pdf : pi_dom_full gamma pd) (pf : pi_funpred gamma_valid pd pdf)
          (vt : val_typevar) (v : val_vars pd vt),
          pat_matrix_var_names_disj ((rev (map Tvar new_vars)) ++ map fst tl) (spec rl c)->
          matches_matrix_tms pd pdf pf vt v ((rev (map Tvar new_vars)) ++ map fst tl) (rev new_typs ++ map snd tl) (spec rl c) Htys Hp =
          Some (gen_rep gamma_valid pd pdf pf vt v ret_ty t Hty)).
  {
    intros c tys2 ps2 Hinc ty2 new_typs new_vars t1 Hcompile.
    specialize (IHconstrs _ _ _ Hinc t1 (ltac:(auto)) Hcompile).
    assert (Hvarstyps: length new_vars = length new_typs). {
      unfold new_vars. simpl_len.
      assert (length ps2 = length new_typs); try lia.
      unfold new_typs. simpl_len; auto.
      specialize (Hclist_types _ _ _ Hinc); inversion Hclist_types; auto.
    }
    assert (Hlen: length ps2 = length (s_args c)). {
      specialize (Hclist_types _ _ _ Hinc); inversion Hclist_types; subst; auto.
    }
    revert IHconstrs.
    (*Need to rewrite in IH*)
    generalize dependent (constr_case_tys (proj1 (Hclist_new c tys2 ps2 Hinc)) (proj1 (proj2 (Hclist_new c tys2 ps2 Hinc)))
        Htytl).
    generalize dependent (@constr_case_patty _ _ _ t ty _ _ rl _ (Hclist_len c tys2 ps2 Hinc) (Hclist_tys c tys2 ps2 Hinc)
        (spec_typed_adt m_in a_in (Hclist_in c tys2 ps2 Hinc) Hp)).
    subst ty ty2. set (ty := vty_cons (adt_name a) args) in *.
    subst new_typs; subst new_vars.

    set (new_typs := (map (ty_subst (s_params c) tys2) (s_args c))) in *.
    set (new_vars :=(combine (gen_strs (length ps2) (compile_fvs gen_getvars ((t, ty) :: tl) rl)) new_typs)) in *.
    rewrite !map_app, !map_rev, !map_fst_combine, !map_snd_combine by solve_len.
    intros Htyp1 Htyall1 IH.
    eexists. eexists. apply IH.
  }
  (*The stronger typing result we need in multiple places:*)
  (*Now we use previous result about [pats]*)
  rename ps into pats.
  assert (Hallty: Forall (fun x =>
    pattern_has_type gamma (fst x) (vty_cons (adt_name a) args) /\
    forall y, snd x = Some y -> gen_typed gamma b y ret_ty)
    (map (fun x => (fst x, Some (snd x))) pats)).
  {
    rewrite <- Hpats.
    rewrite Forall_app. split.
    - (*Prove constrs*)
      rewrite Forall_forall.
      intros x. rewrite <- List.in_rev, in_map_iff.
      intros [y [Hx Hiny]]; subst. simpl. 
      destruct y as [[c tys] ps]; simpl.
      unfold rev_map.
      specialize (Hclist_types _ _ _ Hiny).
      split.
      + (*Prove pattern has correct type*)
        inversion Hclist_types; subst.
        apply P_Constr'; auto.
        2: { unfold rev_map. (*prove disj by uniqueness of generated variable names*)
          rewrite !map_rev, !rev_involutive; simpl_len. 
          rewrite H6, Nat.min_id.
          intros i j d Hi Hj Hij.
          rewrite !map_nth_inbound with (d2:=(""%string, vty_int)) by solve_len.
          simpl.
          rewrite !combine_nth by solve_len.
          intros x. simpl. intros [[Hx1 | []] [Hx2 | []]]; subst.
          inversion Hx2; subst.
          pose proof (gen_strs_nodup (length (s_args c)) (compile_fvs gen_getvars ((t, sigma (f_ret c)) :: tl) (rhd :: rtl))) as Hnodup.
          rewrite NoDup_nth in Hnodup.
          rewrite gen_strs_length in Hnodup.
          specialize (Hnodup i j Hi Hj (eq_sym H0)). subst; contradiction.
        }
        unfold rev_map. rewrite !map_rev, !rev_involutive. 
        (*Prove all variables have correct type: not too hard*)
        apply Forall2_nth; unfold ty_subst_list; simpl_len.
        rewrite H6, Nat.min_id. split; [reflexivity|].
        intros i d1 d2 Hi.
        rewrite !map_nth_inbound with (d2:=(""%string, vty_int)) by solve_len.
        apply P_Var'.
        * (*We proved valid above*)
          specialize (in_cslist_val Hp Hpop Hsimp Hiny) as Hcallval; rewrite Forall_forall in Hcallval; apply Hcallval.
          apply nth_In. solve_len.
        * rewrite combine_nth; auto.
          -- simpl. apply nth_indep. solve_len.
          -- solve_len.
      + (*Now prove that pattern row action is valid - follows from IH, we proved above*)
        specialize (IHconstrs' c tys ps Hiny).
        inversion Hclist_types; subst.
        intros y. unfold comp_cases, Pattern.comp_cases.
        destruct (amap_get funsym_eq_dec cases c) as [c_spec|] eqn : Hccase;
        [|discriminate].
        unfold cases in Hccase.
        assert (Hget:=Hccase).
        erewrite (dispatch1_equiv_spec _ _ _ Hsimp Hpop Hp) in Hccase.
        2: { eapply constrs_in_types. apply Hccase. apply Hpop. }
        revert Hccase; inv Hsome.
        unfold rev_map. rewrite !map_rev, !rev_involutive, !map_snd_combine by solve_len.
        intros Hcompile.
        specialize (IHconstrs' _ Hcompile).
        destruct IHconstrs' as [Htys [Hp' [Hty Heq]]].
        apply Hty.
    - (*Prove typing for base - easier*)
      rewrite Forall_forall. intros x.
      destruct Hps as [  [Hps1 Hnowilds1]| [Hnowilds1 [tm2 [Hcomp2 Hps1]]]]; subst; [contradiction|].
      intros [Hx | []]; subst. simpl.
      split.
      2: { intros y Hy. inv Hy. specialize (IHwilds y (ltac:(auto)) Hcomp2).
          destruct IHwilds as [Hty ?]; exact Hty.  }
      (*Idea: some pattern has the type we need, since cslist is not empty*)
      rewrite amap_not_empty_exists in Htypesemp. destruct Htypesemp as  [fs [pats1 Hget]].
      unfold types in Hget.
      rewrite (proj2 (populate_all_fst_snd_full _ _ _ Hsimp Hpop)) in Hget.
      destruct Hget as [tys1 Hinc].
      apply Hclist_types in Hinc. constructor; auto. eapply pat_has_type_valid. apply Hinc.
  }
  set (comp_cases := fun (cs : funsym) (al : list (term * vty)) =>
  comp_cases (compile get_constructors gen_match gen_let gen_getvars bare simpl_constr) cases tl cs al) in *.
  set (comp_wilds := compile get_constructors gen_match gen_let gen_getvars bare simpl_constr tl wilds) 
    in *.
  (*Prove typing*)
  assert (Htyall: gen_typed gamma b
    (gen_match t (vty_cons (adt_name a) args) pats) ret_ty).
  {
    apply gen_match_typed; auto.
    - subst ty. clear -Htmty. apply Forall2_inv_head in Htmty; auto.
    - revert Hallty. rewrite Forall_map. apply Forall_impl. simpl.
      intros x [Hall1 Hall2]. split; auto.
    - (*Use fact that types not empty to show pats not null*)
      assert (Hlen: length pats <> 0). {
        erewrite <- map_length, <- Hpats. simpl_len.
        rewrite amap_not_empty_exists in Htypesemp. destruct Htypesemp as  [fs [pats1 Hget]].
        unfold types in Hget.
        rewrite (proj2 (populate_all_fst_snd_full _ _ _ Hsimp Hpop)) in Hget.
        destruct Hget as [tys1 Hincs]. unfold cslist.
        destruct (snd types_cslist); simpl; auto.
      }
      (*To prove the [compile_bare] goal, we need to show that
        pats is simple and syntactically exhaustive and use 
        [compile_simple_exhaust]*)
      assert (Hiswild: exists b, no_wilds = Some b). { destruct Hps; destruct_all; subst; auto; eauto. }
      destruct Hiswild as [now Hnow].
      
      assert (Hmapfstpats: map fst pats =
        map fst (rev (map (add_map gen_getvars comp_cases t (vty_cons (adt_name a) args) tl rl)
          cslist) ++ (if now then [] else [(Pwild, comp_wilds)]))).
      {
        replace (map fst pats) with (map fst (map (fun x : pattern * gen_term b => (fst x, Some (snd x))) pats))
          by (rewrite !map_map; auto).
        rewrite <- Hpats, !map_app. subst ty; f_equal. rewrite !map_map.
        destruct Hps as [  [Hps1 Hnowilds1]| [Hnowilds1 [tm2 [Hcomp2 Hps1]]]]; subst; auto; rewrite Hnow in Hnowilds1;
        inversion Hnowilds1; subst; simpl; reflexivity.
      }
      (*TODO: we proved this for [simple] already - can we use?
        copied for now*)
      assert (Hsimpl: (simple_pat_match (map fst pats))).
      {
        rewrite Hmapfstpats.
        rewrite map_app, map_rev, map_map.
        unfold simple_pat_match.
        repeat (apply andb_true_iff; split).
        + rewrite forallb_app. apply andb_true_iff; split.
          * (*Prove all pats are simple - they are vars*)
            rewrite forallb_rev, forallb_map.
            apply forallb_forall.
            intros [[c tys1] pats1] Hinc. simpl.
            unfold rev_map. rewrite map_rev, rev_involutive.
            rewrite forallb_map. apply forallb_t.
          * simpl.
            destruct now; auto. (*easy - just a wild*)
        +  apply (reflect_iff _ _ (nodup_NoDup _ _)).
          rewrite omap_app, !omap_rev, !omap_map. simpl.
          (*second list is nil*)
          assert (Hsnd: (omap
            (fun x : pattern * option (gen_term b) => match fst x with
          | Pconstr c _ _ => Some c
          | _ => None
          end) (if now then [] else [(Pwild, comp_wilds)])) = nil); [| rewrite Hsnd, app_nil_r].
          {
            destruct now; auto.
          }
          apply NoDup_rev.
          apply populate_all_fst_snd_full in Hpop; [|assumption].
          destruct Hpop as [Hnodup Hpop].
          revert Hnodup.
          match goal with |- NoDup ?l1 -> NoDup ?l2 => 
            replace l1 with l2; [solve[auto]|]
          end.
          clear.
          induction (snd (types_cslist)) as [| x xs IH]; simpl; auto.
          destruct x as [[cs tys1] pats1]; simpl in *. rewrite IH; auto.
        + (*constructor exists again by cslist nonempty*)
          rewrite existsb_app. apply orb_true_iff; left.
          rewrite existsb_rev, existsb_map.
          (*Idea: cslist not null, so there must be a constr, cslist not null because types not empty*)
          destruct cslist as [| [[c tys] pats1] csl] eqn : Hcslist; [|solve[auto]].
          exfalso. rewrite (amap_not_empty_exists funsym_eq_dec) in Htypesemp.
          destruct Htypesemp as [f [pats1 Hget]].
          assert (Hex: exists tys, In (f, tys, pats1) cslist). {
            unfold cslist. apply (populate_all_fst_snd_full _ _ _ Hsimp Hpop). auto.
          }
          rewrite Hcslist in Hex. destruct_all; contradiction.
      }
      (*Now prove that this match is exhaustive*)
      assert (Hexhaust: (simple_exhaust (map fst pats) a)).
      {
        rewrite Hmapfstpats.
        rewrite map_app, map_rev, map_map.
        unfold simple_pat_match.
        destruct now eqn : Hwilds.
        - (*Case 1: no_wilds is true, so constrs all in*)
          simpl; rewrite app_nil_r.
          apply orb_true_iff.
          left.
          apply forallb_forall.
          intros cs Hincs.
          rewrite existsb_rev.
          revert Hnow. rewrite Hnowilds.
          intros Hnow; injection Hnow.
          unfold css'. subst ty.
          rewrite (get_constructors_eq gamma_valid m_in a_in).
          rewrite forallb_forall.
          intros Hallin.
          specialize (Hallin _ Hincs).
          (*Since cs in types, cs is cslist, so we can get the element*)
          rewrite amap_mem_spec in Hallin.
          destruct (amap_get funsym_eq_dec types cs) as [ps2 |] eqn : Hget; [|discriminate].
          unfold types in Hget.
          rewrite (proj2 (populate_all_fst_snd_full _ _ _ Hsimp Hpop)) in Hget.
          destruct Hget as [tys1 Hincs1].
          unfold cslist.
          apply existsb_exists.
          setoid_rewrite in_map_iff.
          eexists. split.
          eexists. split; [| apply Hincs1]. reflexivity.
          simpl. destruct (funsym_eqb_spec cs cs); auto.
        - (*Case 2: we have a wild*)
          apply orb_true_iff. right.
          rewrite existsb_app. simpl. rewrite orb_true_r.
          reflexivity.
      }
      assert (Htty: term_has_type gamma t (vty_cons (adt_name a) args)) by (subst ty; inversion Htmty; auto).
      (*Now we can use [compile_simple_exhaust]*)
      pose proof (compile_simple_exhaust m_in a_in pats Hsimpl Hexhaust 
        Htty) as Hcomp.
      destruct (compile_bare_single b false t (vty_cons (adt_name a) args) pats); auto.
      exfalso.
      (*Last two typing results are easy*)
      forward Hcomp.
      {
        revert Hallty. rewrite !Forall_map. apply Forall_impl.
        simpl. intros p1 Hps1; apply Hps1.
      }
      forward Hcomp.
      {
        revert Hallty. rewrite !Forall_map. apply Forall_impl.
        simpl. intros p1 Hps1. apply Hps1; reflexivity.
      }
      (*Use length*)
      forward Hcomp.
      { destruct pats; auto. }
      contradiction.
  }
  (*Typing proof complete, now prove semantics*)
  subst ty.
  exists Htyall.
  intros pd pdf pf vt v Hdisj.
  assert (Htty: term_has_type gamma t (vty_cons (adt_name a) args)).
  { inversion Htmty; auto. }
  assert (Hpatsty: Forall (fun x => pattern_has_type gamma (fst x) (vty_cons (adt_name a) args)) pats). {
    revert Hallty. rewrite Forall_map. apply Forall_impl. intros x [Hpat _]; auto. }
  assert (Hactty: Forall (fun x : pattern * gen_term b => gen_typed gamma b (snd x) ret_ty) pats). {
    revert Hallty. rewrite Forall_map. apply Forall_impl. intros x [_ Htys]. specialize (Htys (snd x)); auto. }
  erewrite gen_match_rep with (Hty1:=Htty)(Hpats1:=Hpatsty)(Hpats2:=Hactty).
  (*Proof sketch:
      [match_rep] is equivalent to [matches_matrix] with single-valued columns.
    then show tha we can split pats into l1 ++ x ++ l2 for any x in l1 st x not in l1.
    Then we get the constructor of [term_rep t].
    Case 1: constructor is in types
      Then we split pats as above and use matches_matrix_app. We know that the result on l1 must be none,
      so we use x, which is [compile] - use IH for the result
    Case 2: constructor not in types
      Then we know all of pats list (before base) is nil, then use base, use default lemma*)
  
  (*One more simplification of [pats] - we can split it into [pats1] and [pats2] corresponding to each list*)
  symmetry in Hpats.
  apply map_eq_app in Hpats. destruct Hpats as [pats1 [pats2 [Hpats [Hpats1 Hpats2]]]]. subst pats.
  destruct (find_semantic_constr pd pdf pf vt v t m_in a_in args_len Htty) as [c [[c_in al] Hsem]]; simpl in Hsem.
  destruct (in_dec funsym_eq_dec c (map (fun x => fst (fst x)) cslist)).
  - (*Case 1: c is in [cslist]*)
    rewrite in_map_iff in i.
    destruct i as [[[f1 tys1] ps2] [Hc Hinc]]; simpl in Hc; subst f1.
    set (ty := (vty_cons (adt_name a) args)) in *.
    assert (Hinpats: In (add_map gen_getvars comp_cases t ty tl rl (c, tys1, ps2)) 
      (map (fun x : pattern * gen_term b => (fst x, Some (snd x))) pats1)).
    {
      rewrite Hpats1, <- In_rev, in_map_iff. exists (c, tys1, ps2); auto.
    }
    rewrite in_map_iff in Hinpats. destruct Hinpats as [[p1 tm1] [Hadd Hinx]].
    (*simplify Hadd*)
    revert Hadd. simpl. unfold rev_map. rewrite !map_rev, !rev_involutive, map_snd_combine.
    2: { simpl_len; auto. apply Hclist_types in Hinc; inversion Hinc; auto. }
    set (new_typs := (map (ty_subst (s_params c) tys1) (s_args c))) in *.
    set (new_vars :=(combine (gen_strs (Datatypes.length ps2) (compile_fvs gen_getvars ((t, ty) :: tl) rl)) new_typs)) in *.
    intros Hadd; inversion Hadd; subst p1.
    (*Now we know that Pconstr c tys1... is in pats. So we can split pats here - the [NoDup] is important*)
    assert (Hsplitpats1: exists patsa patsb, pats1 = patsa ++ (Pconstr c tys1 (map Pvar new_vars), tm1) :: patsb /\
      forall x y, In (x, y) patsa -> exists c1 tys1 ps2, x = (Pconstr c1 tys1 ps2) /\ c1 <> c).
    {
      apply in_split in Hinx. destruct Hinx as [patsa [patsb Hpats1eq]]; subst. exists patsa. exists patsb.
      split; auto.
      (*Now we need to prove NoDups from NoDups of cslist*)
      revert Hpats1.
      rewrite map_app. simpl. rewrite <- map_rev. intros Hpats1; symmetry in Hpats1.
      apply map_eq_app in Hpats1. destruct Hpats1 as [cl1 [cl2 [Hrev [Hmapc1 Hmapc2]]]].
      subst. intros x y Hinxy.
      assert (Hin2: In (x, Some y) (map (add_map gen_getvars comp_cases t ty tl (rhd :: rtl)) cl1)). {
        rewrite Hmapc1, in_map_iff. exists (x, y); auto.
      }
      rewrite in_map_iff in Hin2.
      destruct Hin2 as [[[f2 vs2] ps3] [Hxy Hinxy1]]; simpl in Hxy.
      inversion Hxy; subst. exists f2. exists vs2. eexists. split; [reflexivity|].
      intros Hceq.
      (*Contradiction arises from NoDups of cslist*)
      pose proof (proj1 (populate_all_fst_snd_full _ _ _ Hsimp Hpop)) as Hnodup.
      unfold cslist in Hrev.
      apply NoDup_rev in Hnodup. rewrite <- map_rev in Hnodup.
      rewrite Hrev in Hnodup.
      destruct cl2 as [|chd cl2]; [discriminate | inversion Hmapc2; subst; clear Hmapc2].
      revert Hnodup. rewrite map_app. simpl. rewrite NoDup_app_iff'.
      intros [_ [_ Hnotin]]. apply (Hnotin c).
      simpl. split.
      -(*  rewrite in_map_iff in Hin2. destruct Hin2 as [y [Hy Hiny]]. *)
        rewrite in_map_iff. exists (c, vs2, ps3). split; auto.
      - left. destruct chd as [[y1 y2] y3]; simpl in H0; inversion H0; subst; auto.
    }
    destruct Hsplitpats1 as [patsa [patsb [Hpats1eq Hcnotin]]].
    subst pats1.
    assert (forall p Hp, In p patsa -> match_val_single gamma_valid pd pdf vt ty (fst p) Hp
      (term_rep gamma_valid pd pdf vt pf v t ty Htty) = None).
    {
      (*Use [match_val_single_constr_nomatch] to show that all None*)
      intros [p1 a1] Hp' Hinp'.
      destruct (Hcnotin _ _ Hinp') as [f2 [vs2 [ps3 [Hx Hf12]]]]; subst. simpl fst.
      eapply (match_val_single_constr_nomatch _ _ _ _ _ _ m_in a_in c_in args_len); eauto.
    }
    (*So patsa is irrelevant, and we can manually simplify [match_rep]*)
    revert Hpatsty Hactty.
    rewrite <- app_assoc. intros.
    rewrite match_rep_app2; [|assumption].
    rewrite match_rep_equiv. 
    (*And the thing we care about is the [match_val_single] here*)
    (*Awful hack*) Opaque match_val_single.
    simpl match_rep'. Transparent match_val_single. unfold ty.
    assert (Heq: sym_sigma_args c (map (v_subst vt) args) = map (v_subst vt) (ty_subst_list (s_params c) args (s_args c))).
    { apply sym_sigma_args_map. rewrite (adt_constr_params gamma_valid m_in a_in c_in). auto. }
    (*Useful to know*)
    assert (Hpcty: pattern_has_type gamma (Pconstr c tys1 (map Pvar new_vars)) ty). {
      rewrite Forall_forall in Hallty.
      specialize (Hallty (Pconstr c tys1 (map Pvar new_vars), Some tm1)).
      forward Hallty. 
      { rewrite in_map_iff. exists (Pconstr c tys1 (map Pvar new_vars), tm1); split; auto.
        rewrite !in_app_iff; simpl; auto.
      }
      apply Hallty.
    }
    assert (Heqty: tys1 = args). {
      inversion Hpcty; subst.
      unfold sigma in H4. subst ty.
      rewrite (adt_constr_subst_ret gamma_valid m_in a_in c_in) in H4 by auto.
      inversion H4; subst; auto.
    }
    subst tys1.
    assert (Hvarsty: row_typed (ty_subst_list (s_params c) args (s_args c)) (map Pvar new_vars)).
    {
      apply constr_typed_row in Hpcty. auto.
    }
    (*Now we have all the typing info to rewrite the [match_val_single]*)
    rewrite (match_val_single_constr_row _ _ _ _ _ _ m_in a_in c_in args_len Htty al Hsem _ _ _ _ Heq Hvarsty).
    (*We can solve this explicitly: we know that [matches_row] succeeds here (these are all variables)
      and each variable is mapped to the corresponding element of the hlist*)
    (*Rest of proof (sketch):
      We can directly simplify the [matches_row] into the valuation vs -> al
      We want to show that matches_matrix v (t :: tl) rl = Some (gen_rep (vs -> al) tm1)
        where compile (vs ++ tl) (spec c rl) = Some tm1.
      From the IH, we have that matches_matrix (vs -> al) (vs ++ tl) (spec c rl) =
        Some (gen_rep (vs -> al) tm1) (NOTE: we need to adjust v here!)
      From our spec lemma, we know that matches_matrix v (t :: tl) rl =
        matches_matrix v (al ++ rl) (spec c rl).
        Thus, it remains to show that
        matches_matrix v (al ++ rl) P = matches_matrix (vs -> al) (vs ++ rl) P
        This follows by considering each row - the terms only matter based on what they
          become under (domain (v_subst vt)), and by the definition of the valuation, 
          the resulting domain values are equivalent (as long as rl does not have any variables in vs)
    *)
    (*First, rewrite this [matches_row]*)
    destruct (matches_row_allvars _ pdf _ v _ _ Heq al new_vars Hvarsty) as [l [Hl Hvall]].
    rewrite Hl.
    (*Need to reverse here to match to ending result of [compile]**)
    assert (params_len : Datatypes.length (s_params c) = Datatypes.length args). {
      specialize (Hclist_types _ _ _ Hinc); inversion Hclist_types; auto.
    }
    assert (Hlenps: length ps2 = length new_typs). {
      unfold new_typs. simpl_len; auto. 
      specialize (Hclist_types _ _ _ Hinc); inversion Hclist_types; auto.
    }
    assert (Hvarstyps: length new_vars = length new_typs). {
      unfold new_vars. solve_len.
    }
    assert (Hnodup: NoDup new_vars). {
      unfold new_vars. apply NoDup_combine_l. apply gen_strs_nodup.
    }
    rewrite gen_rep_change_vv with (v2:=val_with_args pd vt v (rev new_vars) (hlist_rev _ _ al)).
    2: { 
      intros x Hinx'. rewrite val_with_args_rev; auto.
      rewrite Heq. unfold new_vars. rewrite map_snd_combine; auto. solve_len.
    }
    (*Step 2: We already simplified IHconstrs, now we destruct - need to change v!*)
    specialize (IHconstrs' _ _ _ Hinc tm1).
    (* specialize (IHconstrs' _ _ _ Hinc (val_with_args pd vt v (rev new_vars) (hlist_rev _ _ al)) tm1). *)
    forward IHconstrs'. (*prove the compile equivalence*)
    {
      rewrite H1. unfold comp_cases, Pattern.comp_cases. (*some duplication too*)
      unfold cases. rewrite Hcasewild.
      erewrite (dispatch1_equiv_spec _ _ _ Hsimp Hpop Hp); auto. 
      unfold cslist in Hinc.
      rewrite amap_mem_spec.
      replace (amap_get funsym_eq_dec (fst types_cslist) c) with (Some ps2); auto.
      symmetry.
      rewrite (proj2 (populate_all_fst_snd_full _ _ _ Hsimp Hpop)). exists args; assumption.
    }
    (*Need to simplify again - bad*)
    subst new_typs new_vars.
    set (new_typs := (map (ty_subst (s_params c) args) (s_args c))) in *.
    set (new_vars :=(combine (gen_strs (Datatypes.length ps2) (compile_fvs gen_getvars ((t, ty) :: tl) rl)) new_typs)) in *.
    (*Why we needed the "exists" in the alternate IHconstrs: now we don't need to prove typing again*)
    destruct IHconstrs' as [Htys [Hp' [Hty IHmatch]]].
    (*NOTE: use different valuation for IH!*)
    specialize (IHmatch pd pdf pf vt (val_with_args pd vt v (rev new_vars) (hlist_rev _ _ al))).
    forward IHmatch.
    {
      (*Prove disjoint*) unfold vsymbol in *.
      (*Different [disj] lemma*)
      eapply disj_spec1. apply Hdisj.
      assert (Hlen: length ps2 = length (s_args c)). {
        specialize (Hclist_types _ _ _ Hinc); inversion Hclist_types; subst; auto.
      }
      revert Hdisj; clear -Hlen. (*need to know length ps = length (s_argcs c)*) simpl. 
      unfold pat_matrix_var_names_disj; intros Hdisj.
      intros x [Hinx1 Hinx2].
      rewrite in_map_big_union with (eq_dec1:=string_dec)  in Hinx1 .
      simpl_set. destruct Hinx1 as [t1 [Hint1 Hinx1]]. rewrite <- List.in_rev in Hint1.
      rewrite in_map_iff in Hint1. destruct Hint1 as [[n ty1] [Ht1 Hiny]]; subst. simpl in Hinx1.
      destruct Hinx1 as [Hx | []]; subst.
      unfold new_vars, new_typs in Hiny.
      (*Contradiction, x cannot be in names of rl and in [gen_strs]*)
      rewrite in_combine_iff in Hiny by solve_len; rewrite gen_strs_length in *.
      destruct Hiny as [i [Hi Hxty]]. specialize (Hxty ""%string vty_int).
      inversion Hxty.
      assert (Hnotin: ~ In x (map fst (compile_fvs gen_getvars ((t, ty) :: tl) rl))). {
        apply (gen_strs_notin' (length ps2)). subst. apply nth_In. solve_len. }
      apply Hnotin. unfold compile_fvs. rewrite !map_app. rewrite !in_app_iff; auto.
    }
    erewrite gen_rep_irrel.
    rewrite <- IHmatch.
    (*Step 3: Use spec lemma to rewrite*)
    rewrite (spec_match_eq pd pdf pf vt v t m_in a_in c_in args_len params_len Htty al Hsem _ _ _ _ Hsimp _ Hp').
    (*Step 4: Show that we can change the valuation in this case*)
    clear -Hvarstyps Hnodup Hlenps.
    revert Hp' Htys. generalize dependent (spec_prop_cast vt c args (map snd tl) params_len).
    unfold ty_subst_list.
    unfold matches_matrix_tms.
    change (seq.map (ty_subst (s_params c) args) (s_args c)) with new_typs.
    (*NOTE: first, prove that none of new_vars are in terms, so we can replace
      second [terms_to_hlist] with just v*)

    intros Heq Hp' Htys.
    (*We can use [terms_to_hlist app] to split and prove directly*)
    assert (Hlen: length (rev (map Tvar new_vars)) = length (rev new_typs)) by solve_len.
    rewrite terms_to_hlist_app with (Hty2:=Forall2_inv_tail Htmty)
      (Hty1:=proj1(Forall2_app_inv Htys Hlen)) by auto.
    (*Now we know that [terms_to_hlist] on (map Tvar new_vars) is just al*)
    assert (Heqrev: rev (sym_sigma_args c (map (v_subst vt) args)) =
      map (v_subst vt) (rev new_typs)).
    {
      rewrite map_app in Heq. apply app_inv_tail in Heq. exact Heq.
    }
    generalize dependent (proj1 (Forall2_app_inv Htys Hlen)).
    replace (rev (map Tvar new_vars)) with (map Tvar (rev new_vars)) by (rewrite map_rev; reflexivity).
    intros Hall.
    rewrite (terms_to_hlist_val_with_args pd pdf pf vt v (rev new_vars) (rev new_typs)) with (Heq:=Heqrev);
    [| apply NoDup_rev; assumption].

    rewrite matches_matrix_change_vv with (v1:=val_with_args _ _ _ _ _) (v2:=v).
    2: {
      (*Prove these valuations are equivalent for all action vars -relies on fresh vars*)
      intros x row Hinrow Hinx.
      rewrite val_with_args_notin; auto.
      rewrite <- In_rev. unfold new_vars. unfold vsymbol in *.
      rewrite in_combine_iff; simpl_len; [|solve[auto]].
      intros [i [Hi Hx]]. specialize (Hx ""%string vty_int).
      assert (Hinget: In (fst x)((gen_strs (length ps2) (compile_fvs gen_getvars ((t, ty) :: tl) rl) ))).
      { subst. simpl. apply nth_In. solve_len. }
      apply gen_strs_notin in Hinget.
      apply Hinget.
      (*contradiction - in action vars, so must be in [compile_fvs]*)
      unfold compile_fvs. rewrite !in_app_iff. right. right.
      unfold pat_mx_act_vars. simpl_set.
      apply (gen_getvars_spec Hinrow Hinx).
    }

    f_equal.
    (*Get all casts to beginning*)
    rewrite hlist_app_cast1.
    rewrite (terms_to_hlist_change_vv pd pdf pf vt (val_with_args pd vt v (rev new_vars)
      (hlist_rev (domain (dom_aux pd))
      (sym_sigma_args c (map (v_subst vt) args)) al)) v).
    2: {
      (*Last subgoal: prove no intersection between vars and terms*)
      intros tm x Htm Hx.
      rewrite val_with_args_notin; auto.
      rewrite <- In_rev.
      unfold new_vars, vsymbol. rewrite in_combine_iff; simpl_len; [|solve[auto]].
      intros [i [Hi Hxeq]].
      specialize (Hxeq ""%string vty_int).
      assert (Hinget: In (fst x)((gen_strs (length ps2) (compile_fvs gen_getvars ((t, ty) :: tl) rl) ))).
      { subst. simpl. apply nth_In. solve_len. }
      apply gen_strs_notin in Hinget.
      apply Hinget.
      (*contradiction - in action vars, so must be in [compile_fvs]*)
      unfold compile_fvs. rewrite !in_app_iff. left.
      unfold tmlist_vars. rewrite in_concat. simpl.
      exists ((tm_fv tm ++ tm_bnd tm)). rewrite in_map_iff, in_app_iff. split; auto.
      right. rewrite in_map_iff in Htm. destruct Htm as [y [Htm Hiny]]. subst.
      exists y. auto. 
    }
    (*Only need to prove casts equivalent now*)
    rewrite !cast_arg_list_compose.
    apply cast_arg_list_eq.
- (*Second case: constructor is NOT in list - then we fall through to defaults*)
  (*Similar, show pats1 has constructors which are not c*)
  assert (Hpats1c: forall x y, In (x, y) pats1 -> 
    exists c1 tys1 ps1, x = (Pconstr c1 tys1 ps1) /\ c1 <> c).
  {
    intros x y Hinxy.
    assert (Hinxy1: In (x, Some y) (map (fun x => (fst x, Some (snd x))) pats1)) by
      (rewrite in_map_iff; exists (x, y); auto).
    rewrite Hpats1 in Hinxy1. rewrite <- List.in_rev in Hinxy1.
    rewrite in_map_iff in Hinxy1. destruct Hinxy1 as [[[f1 tys1] ps2] [Hxy Hinfs]]; simpl in Hxy.
    inversion Hxy; subst.
    exists f1. exists tys1. eexists. split; [reflexivity| auto]. 
    (*Show not c by notin*)
    intro Heq; subst. apply n. rewrite in_map_iff.
    eexists; split; [| apply Hinfs]; reflexivity.
  }
  set (ty := vty_cons (adt_name a) args) in *.
  assert (forall p Hp, In p pats1 -> match_val_single gamma_valid pd pdf vt ty (fst p) Hp
    (term_rep gamma_valid pd pdf vt pf v t ty Htty) = None).
  {
    (*Use [match_val_single_constr_nomatch] to show that all None*)
    intros [p1 a1] Hp' Hinp'.
    destruct (Hpats1c _ _ Hinp') as [f2 [vs2 [ps2 [Hx Hf12]]]]; subst. simpl fst.
    eapply (match_val_single_constr_nomatch _ _ _ _ _ _ m_in a_in c_in args_len); eauto.
  }
  (*Similarly, pats1 is irrelevant, so we go to pats2 (wild)*)
  rewrite match_rep_app2; [|assumption].
  (*Now we show that [no_wilds] is false, so that pats2 = (Pwild, comp_wilds)*)
  assert (Hno: no_wilds = Some false). {
    (*If true, impossible - we know that c is in constructors but not cslist*)
    rewrite Hnowilds. f_equal.
    apply forallb_false.
    exists c. split; auto.
    - unfold css'. apply (in_get_constructors gamma_valid m_in a_in); auto.
    - unfold types.
      rewrite amap_mem_spec.
      destruct (amap_get funsym_eq_dec (fst types_cslist) c) as [y|] eqn : Hget; auto.
      rewrite (proj2 (populate_all_fst_snd_full _ _ _ Hsimp Hpop)) in Hget.
      destruct Hget as [tys Hincslist]. exfalso.
      apply n. rewrite in_map_iff. exists (c, tys, y); auto.
  }
  destruct Hps as [[? Hwildt] | [_ [tm2 [Hcomp2 Hps1]]]]; [rewrite Hwildt in Hno; discriminate|].
  subst ps1. simpl in Hpats2.
  (*Now explicitly get parts of pats2*)
  destruct pats2 as [| [y1 y2] [|]]; try discriminate.
  simpl in Hpats2. injection Hpats2. intros Hcompwilds Hy1; subst y1.
  rewrite match_rep_equiv.
  simpl.
  unfold extend_val_with_list. simpl.
  (*Now use IH and show default*)
  symmetry in Hcompwilds; unfold comp_wilds in Hcompwilds. subst tm2.
  specialize (IHwilds y2 (ltac:(auto)) Hcomp2). destruct IHwilds as [Hty IHmatch].
  erewrite gen_rep_irrel.
  rewrite <- IHmatch by (eapply disj_default; eauto). subst wilds.
  (*And now we use [default_match_eq]*)
  unfold matches_matrix_tms at 2.
  unfold ty. clear IHmatch.
  erewrite terms_to_hlist_irrel.
  apply (default_match_eq pd pdf pf vt v t m_in a_in c_in args_len) with (Hty:=Htty) (al1:=al); auto.
  + rewrite (adt_constr_params gamma_valid m_in a_in c_in); auto.
  + (*Last goal: show that since not in cslist, constr_at_head_ex is false*)
    destruct (constr_at_head_ex c rl) eqn : Hconstr; auto.
    apply (populate_all_in _ _ _ _ Hsimp Hpop) in Hconstr.
    rewrite amap_mem_spec in Hconstr.
    destruct (amap_get funsym_eq_dec (fst types_cslist) c) as [y|] eqn : Hget; auto.
    apply (proj2 (populate_all_fst_snd_full _ _ _ Hsimp Hpop)) in Hget.
    destruct Hget as [tys Hinc].
    (*Contradiction from not in cslist*)
    exfalso. apply n.
    rewrite in_map_iff. exists (c, tys, y). auto.
Qed.

(*Finally, Our main correctness theorem: if [compile is_constr gen_let gen_case tms tys P] =
  Some t, then [matches_matrix_tms tms tys P] = Some (term_rep v t).
  We CANNOT prove the converse; it does not hold, as semantic exhaustiveness is undecidable*)
Theorem compile_correct (bare: bool) (simpl_constr: bool) (tms: list (term * vty)) 
  (P: pat_matrix) 
  (Htmtys: Forall2 (term_has_type gamma) (map fst tms) (map snd tms))
  (Hp: pat_matrix_typed (map snd tms) P)
  t :
  compile get_constructors gen_match gen_let gen_getvars bare simpl_constr tms P = Some t ->
  exists (Hty : gen_typed gamma b t ret_ty), 
    forall (pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
      (vt: val_typevar) (v: val_vars pd vt)
    (Hdisj: pat_matrix_var_names_disj (map fst tms) P),
    matches_matrix_tms pd pdf pf vt v (map fst tms) (map snd tms) P Htmtys Hp = 
    Some (gen_rep gamma_valid pd pdf pf vt v ret_ty t Hty).
Proof.
  revert Htmtys Hp. assert (Ht: True) by auto; revert Ht.
  revert t. apply (compile_prove_some_typed bare simpl_constr (fun _ _ => True) 
  (fun tms P t Htmtys Hp => exists Hty : gen_typed gamma b t ret_ty,
    forall (pd : pi_dom) (pdf : pi_dom_full gamma pd) (pf : pi_funpred gamma_valid pd pdf)
      (vt : val_typevar) (v : val_vars pd vt),
    pat_matrix_var_names_disj (map fst tms) P ->
    matches_matrix_tms pd pdf pf vt v (map fst tms) (map snd tms) P Htmtys Hp =
    Some (gen_rep gamma_valid pd pdf pf vt v ret_ty t Hty))); auto; clear tms P.
  - (*irrelevance*)
    intros tms P t Hty1 Hty2 Hp1 Hp2 [Hty Hrep].
    exists Hty. intros pd pdf pf vt v Hdisj.
    unfold matches_matrix_tms.
    erewrite terms_to_hlist_irrel. erewrite matches_matrix_irrel.
    apply Hrep; auto.
  - (*simplify*)
    intros. specialize (Hsimpl (ltac:(auto))).
    destruct Hsimpl as [Hty Hrep]. exists Hty. intros pd pdf pf vt vv Hdisj.
    specialize (Hrep pd pdf pf vt vv). simpl in Hdisj.
    specialize (Hrep (simplify_disj _ _ _ _ Hdisj)). simpl in Hrep.
    erewrite simplify_match_eq in Hrep; eauto.
    apply pat_matrix_var_names_vars_disj; assumption.
  -  (*P not nil, ts is nil*) intros a P' _ Hp.
    simpl in *. eexists. intros pd pdf pf vt v.
    unfold matches_matrix_tms.
    simp terms_to_hlist. simp matches_matrix. simp matches_row.
    unfold extend_val_with_list. simpl. reflexivity.
  - (*wild case*) intros.
    (*Case 1: types is empty*)
    (*We know:
      1. All elements are Pwild in first column
      2. No matter what type ty is, it cannot be a constructor that is in the first column.
      3. Thus, we can use either of our default lemmas*)
    (*First, use lemma so we get typing*)
    specialize (IHwilds tm1 (ltac:(auto)) Hcomp).
    destruct IHwilds as [IHty Hallrep].
    exists IHty. intros pd pdf pf vt v Hdisj.
    specialize (Hallrep pd pdf pf vt v (disj_default _ _ _ Hdisj)).
    destruct (is_vty_adt gamma ty) as [[[m a] args]|] eqn : Hisadt.
     (*case 1: ADT. Know constructor not in first column*)
    +  assert (args_len: length args = length (m_params m)). {
        apply adt_vty_length_eq in Hisadt; auto.
        clear -Htmtys.
        apply Forall2_inv_head in Htmtys.
        apply has_type_valid in Htmtys; auto.
      }
      apply is_vty_adt_some in Hisadt.
      destruct Hisadt as [Hty [a_in m_in]]; subst. set (rl:=(rhd :: rtl)) in *.
      destruct (find_semantic_constr pd pdf pf vt v t m_in a_in args_len (Forall2_inv_head Htmtys))
      as [f [[c_in al] Hrep]].
      simpl in Hrep.
      assert (Hnotin: constr_at_head_ex f rl = false).
      {
        destruct (constr_at_head_ex f rl) eqn : Hconstr; auto.
        apply (populate_all_in _ _ _ _ Hsimpl Hpop) in Hconstr.
        unfold types in Hisemp.
        assert (Hconstrf: amap_mem funsym_eq_dec f (fst types_cslist) = false).
          apply amap_is_empty_mem; auto.
        rewrite Hconstrf in Hconstr; discriminate.
      }
      (*Now we apply default lemma 1*)
      simpl in Hdisj.
      assert (constrs_len: length (s_params f) = length args).
      { rewrite args_len. f_equal. apply (adt_constr_params gamma_valid m_in a_in c_in). }
      simpl in Htmtys. simpl.
      rewrite (default_match_eq pd pdf pf vt v _ m_in a_in c_in args_len constrs_len (Forall2_inv_head Htmtys) al Hrep _ 
        _ Htmtys rl Hsimpl Hnotin Hp (default_typed Hp)).
      (*And use IH about wilds*)
      unfold matches_matrix_tms.
      erewrite terms_to_hlist_irrel, matches_matrix_irrel.
      apply Hallrep. 
    + (*Case 2: not ADT at all. Similar but use second default lemma*)
      simpl in Htmtys |- *.
      rewrite (default_match_eq_nonadt pd pdf pf vt _ _ _ (Forall2_inv_head Htmtys) Hisadt _ _ Htmtys
        rl Hsimpl Hp (default_typed Hp)).
      erewrite terms_to_hlist_irrel, matches_matrix_irrel. apply Hallrep.
  - (*comp_full case*)
    intros.
    eapply comp_full_correct; eauto.
  - (*Second wild case*)
    intros. subst params.
    assert (Hsem: forall pd pdf pf vt v,
      tm_semantic_constr pd pdf pf vt v (Tfun cs args tms) 
        m_in a_in f_in args_len Hcsty 
      (cast_arg_list (eq_sym (sym_sigma_args_map vt cs args constrs_len))
        (terms_to_hlist pd pdf pf vt v tms
        (ty_subst_list (s_params cs) args (s_args cs)) Htms'))).
    {
      intros pd pdf pf vt v.
      (*First, destruct [find_semantic_constr], then use [tfun_semantic_constr]*)
      destruct (find_semantic_constr pd pdf pf vt v (Tfun cs args tms) m_in a_in args_len Hcsty) as 
        [c [[c_in al] Hrep]]; simpl in Hrep.
      destruct (tfun_semantic_constr _ _ _ _ _ _ _ f_in _ _ _ _ _ constrs_len _ Htms'  Hrep) as [Heq Hal];
      subst. simpl in Hrep. unfold cast_arg_list at 1 in Hrep; simpl in Hrep.
      assert (f_in = c_in) by (apply bool_irrelevance); subst; apply Hrep.
    }
    (*If not in types, similar to above, use default result*)
    assert (Hnotin: constr_at_head_ex cs rl = false).
    {
      destruct (constr_at_head_ex cs rl) eqn : Hconstr1; auto.
      apply (populate_all_in _ _ _ _ Hsimpl Hpop) in Hconstr1.
      unfold types in Hmem.
      rewrite Hmem in Hconstr1.
      discriminate.
    }
    apply IHwilds in Hcomp; [| solve[auto]].
    destruct Hcomp as [Htyw Hrep]. exists Htyw.
    intros pd pdf pf vt v Hdisj.
    subst ty.
    specialize (Hrep pd pdf pf vt v ((disj_default _ _ _ Hdisj))).
    clear IHwilds.
    specialize (Hsem pd pdf pf vt v). simpl. subst t.
    rewrite (default_match_eq pd pdf pf vt v _ m_in a_in f_in args_len constrs_len Hcsty _ Hsem _ 
      _ Htmty rl Hsimpl Hnotin Hp' (default_typed Hp)).
    (*And use IH about wilds*)
    revert Hrep.
    unfold matches_matrix_tms.
    erewrite terms_to_hlist_irrel, matches_matrix_irrel; intros Hrep; apply Hrep.
  - (*constr case*)
    intros. subst params.
    assert (Hsem: forall pd pdf pf vt v,
      tm_semantic_constr pd pdf pf vt v (Tfun cs args tms) 
        m_in a_in f_in args_len Hcsty 
      (cast_arg_list (eq_sym (sym_sigma_args_map vt cs args constrs_len))
        (terms_to_hlist pd pdf pf vt v tms
        (ty_subst_list (s_params cs) args (s_args cs)) Htms'))).
    {
      intros pd pdf pf vt v.
      (*First, destruct [find_semantic_constr], then use [tfun_semantic_constr]*)
      destruct (find_semantic_constr pd pdf pf vt v (Tfun cs args tms) m_in a_in args_len Hcsty) as 
        [c [[c_in al] Hrep]]; simpl in Hrep.
      destruct (tfun_semantic_constr _ _ _ _ _ _ _ f_in _ _ _ _ _ constrs_len _ Htms'  Hrep) as [Heq Hal];
      subst. simpl in Hrep. unfold cast_arg_list at 1 in Hrep; simpl in Hrep.
      assert (f_in = c_in) by (apply bool_irrelevance); subst; apply Hrep.
    }
    (*If f is in types, then we use specialization result and IH*)
    revert Hcomp.
    unfold comp_cases, Pattern.comp_cases.
    assert (Hgetf: amap_get funsym_eq_dec cases cs = Some (spec rl cs)) by
      (unfold cases; rewrite Hcasewild; apply (dispatch1_equiv_spec _ _ _ Hsimpl Hpop Hp Hmem)).
    rewrite Hgetf.
    (*Now can use [spec] lemma*)
    subst ty.
    pose proof (@spec_typed_adt _ _ _ m_in a_in f_in _ (map snd tl) _ Hp) as Hspecty.
    (*And we need the IH*)
    intros Hcomp.
    specialize (IHfun tm1 (ltac:(auto)) Hcomp).
    destruct IHfun as [IHty IHmatch].
    exists IHty. intros pd pdf pf vt v Hdisj. subst t. simpl in Hdisj.
    assert (Hfsteq: (rev tms ++ map fst tl) =
      (map fst (rev (combine tms (map (ty_subst (s_params cs) args) (s_args cs))) ++ tl))).
    { rewrite map_app; f_equal; auto. rewrite !map_rev, map_fst_combine by solve_len. reflexivity. }
    assert (Hsndeq: rev (map (ty_subst (s_params cs) args) (s_args cs)) ++ map snd tl =
      (map snd (rev (combine tms (map (ty_subst (s_params cs) args) (s_args cs))) ++ tl))).
    { rewrite map_app; f_equal; auto. rewrite !map_rev, map_snd_combine by solve_len. reflexivity. }
    pose proof (Hdisj':=disj_spec Hdisj).
    rewrite Hfsteq in Hdisj'.
    specialize (IHmatch pd pdf pf vt v Hdisj'). simpl.
    revert IHmatch.
    generalize dependent (tfun_case_tys Htms' Htytl).
    generalize dependent (tfun_case_patty tms_len (spec_typed_adt m_in a_in f_in Hp)).
    rewrite <- Hfsteq, <- Hsndeq.
    set (new_typs := (map (ty_subst (s_params cs) args) (s_args cs))) in *.
    intros Hspecp1 Hspecty1 IHmatch.
    (*Now we use spec lemma*)
    specialize (Hsem pd pdf pf vt v).
    rewrite (spec_match_eq pd pdf pf vt v (Tfun cs args tms) m_in a_in f_in args_len constrs_len Hcsty _
      Hsem _ _ Htmty rl Hsimpl Hp' Hspecty).
    (*Now, we use the IH*)
    unfold matches_matrix_tms in IHmatch.
    revert IHmatch.
    unfold matches_matrix_tms.
    match goal with 
    | |- matches_matrix _ _ _ _ _ ?l1 ?al1 ?P ?H1 = Some ?x ->
         matches_matrix _ _ _ _ _ ?l2 ?al2 ?P2 ?H2 = Some ?y =>
      replace al1 with al2; auto
    end.
    { erewrite matches_matrix_irrel; intros Hrep; apply Hrep. }
    (*And now, use [al] equality result*)
    rewrite terms_to_hlist_app with (Hty1:=(Forall2_rev Htms'))(Hty2:= (Forall2_inv_tail Htmty)).
    2: unfold ty_subst_list; solve_len. 
    rewrite terms_to_hlist_rev with (Hty:=Htms').
    (*Bring all casts to front*)
    rewrite hlist_rev_cast,  !hlist_app_cast1.
    rewrite !cast_arg_list_compose.
    apply cast_arg_list_eq.
Qed.

End CompileTheorem.

(*Some corollaries*)
(*NOTE: we do NOT assume any interp here*)
Corollary compile_typed (bare: bool) (simpl_constr: bool) (tms: list (term * vty)) 
  (P: pat_matrix) 
  (Htys: Forall2 (term_has_type gamma) (map fst tms) (map snd tms))
  (Hp: pat_matrix_typed (map snd tms) P)
  t :
  compile get_constructors gen_match gen_let gen_getvars bare simpl_constr tms P = Some t ->
  gen_typed gamma b t ret_ty.
Proof.
  intros Hcomp. apply compile_correct in Hcomp; auto.
Qed.

Corollary compile_rep (bare: bool) (simpl_constr: bool)  (pd: pi_dom) (pdf: pi_dom_full gamma pd)
  (pf: pi_funpred gamma_valid pd pdf) (vt: val_typevar) 
  (v: val_vars pd vt) (tms: list (term * vty)) 
  (P: pat_matrix) 
  (Htys: Forall2 (term_has_type gamma) (map fst tms) (map snd tms))
  (Hp: pat_matrix_typed (map snd tms) P)
  (Hdisj: pat_matrix_var_names_disj (map fst tms) P) t
  (Hty: gen_typed gamma b t ret_ty) :
  compile get_constructors gen_match gen_let gen_getvars bare simpl_constr tms P = Some t ->
  matches_matrix_tms pd pdf pf vt v (map fst tms) (map snd tms) P Htys Hp = 
  Some (gen_rep gamma_valid pd pdf pf vt v ret_ty t Hty).
Proof.
  intros Hcomp.
  destruct (compile_correct bare simpl_constr tms P Htys Hp t Hcomp) as [Hty' Hrep].
  rewrite Hrep. f_equal. apply gen_rep_irrel. assumption.
Qed.

(*A corollary: If [matches_matrix] is None (i.e., no semantic match), 
  then [compile] returns None, indicating an error.
  We cannot prove the converse; it does not hold*)
Corollary exhaustiveness_correct (bare: bool) (simpl_constr: bool)  (pd: pi_dom) (pdf: pi_dom_full gamma pd)
  (pf: pi_funpred gamma_valid pd pdf) (vt: val_typevar) 
  (v: val_vars pd vt) (tms: list (term * vty))  
  (P: pat_matrix) 
  (Htys: Forall2 (term_has_type gamma) (map fst tms) (map snd tms))
  (Hp: pat_matrix_typed (map snd tms) P)
  (Hdisj: pat_matrix_var_names_disj (map fst tms) P):
  matches_matrix_tms pd pdf pf vt v (map fst tms) (map snd tms) P Htys Hp = None ->
  compile get_constructors gen_match gen_let gen_getvars bare simpl_constr tms P = None.
Proof.
  intros Hmatch.
  destruct (compile get_constructors gen_match gen_let gen_getvars bare simpl_constr tms P) as [t|] eqn : Hcomp; auto.
  destruct (compile_correct bare simpl_constr tms P Htys Hp t Hcomp) as [Hty' Hrep].
  rewrite Hrep in Hmatch. discriminate. apply Hdisj.
Qed. 

End CompileCorrect.

(*Robustness of Exhaustiveness Checking*)

(*Because [compile] is part of our typecheck, we need to prove
  that modified terms are still well-typed.
  The main result is that if the two pattern matrices have
  the same "shape", then exhaustiveness checking doesn't change.
  NOTE: this is why we need to take out the optimization for
  functions; otherwise this is not true,
  ex: match [1] with | _ :: _ -> end vs match x with | _ :: _ -> end
  2nd not exhaustive*)

(*ty_rel ty1 ty2 is (if ty1 is an ADT, then so is ty2)*)
Definition ty_rel (ty1 ty2: vty) : bool :=
  match ty1 with
  | vty_cons _ _ =>
    match ty2 with 
    | vty_cons _ _ => true
    | _ => false
    end
  | _ => true
  end.

(*Slightly weaker than [shape_p] in Alpha.v*)
Section ShapeP.
Variable (rel: vty -> vty -> bool).
Fixpoint shape_p (p1 p2: pattern) :=
  match p1, p2 with
  | Pwild, Pwild => true
  | Por pa pb, Por pc pd => shape_p pa pc && shape_p pb pd
  | Pbind p1 v1, Pbind p2 v2 => shape_p p1 p2
  | Pvar v1, Pvar v2 => true
  | Pconstr f1 tys1 ps1, Pconstr f2 tys2 ps2 =>
    (funsym_eq_dec f1 f2) &&
    (length tys1 =? length tys2) &&
    (all2 rel tys1 tys2) &&
    (*(list_eq_dec vty_eq_dec tys1 tys2) &&*)
    (length ps1 =? length ps2) &&
    all2 (fun p1 p2 => shape_p p1 p2) ps1 ps2
  | _, _ => false
  end.


Definition lens_mx {A B: Type} (p1: list (list pattern * A))
  (p2: list (list pattern * B)) : bool :=
  ((length p1) =? (length p2)) &&
  (all2 (fun r1 r2 => length (fst r1) =? length (fst r2)) p1 p2).

Definition shape_mx {A B: Type} (p1: list (list pattern * A))
  (p2: list (list pattern * B)) : bool :=
  all2 (fun r1 r2 => 
    all2 shape_p (fst r1) (fst r2)) p1 p2.

Lemma length_simplify_aux {A B: Type} {let1 let2}
  (p1 p2: pattern) t1 t2 (a1: A) (a2: B):
  shape_p p1 p2 ->
  length (simplify_aux let1 t1 a1 p1) = length (simplify_aux let2 t2 a2 p2).
Proof.
  revert p2 t1 t2 a1 a2.
  induction p1; intros p2; destruct p2;
  try discriminate; simpl; auto.
  intros t1 t2 a1 a2. unfold is_true. rewrite andb_true_iff.
  intros [Hshape1 Hshape2].
  solve_len.
Qed.

Lemma shape_mx_simplify {A B let1 let2 t1 t2} 
  (P1: list (list pattern * A)) 
  (P2: list (list pattern * B)):
  lens_mx P1 P2 ->
  shape_mx P1 P2 ->
  shape_mx (simplify let1 t1 P1) (simplify let2 t2 P2) &&
  lens_mx (simplify let1 t1 P1) (simplify let2 t2 P2).
Proof.
  unfold lens_mx, simplify, shape_mx. unfold is_true at 1.
  rewrite andb_true_iff. intros [Hlen1 Halllen].
  apply Nat.eqb_eq in Hlen1.
  rewrite fold_is_true in Halllen. revert Halllen.
  generalize dependent P2.
  induction P1 as [| phd1 ptl1 IH].
  - intros [| phd2 ptl2]; [|discriminate]; auto.
  - intros [| phd2 ptl2]; [discriminate|simpl].
    unfold all2 in *. simpl.
    intros Hlen Hallen Hshape.
    apply andb_true_iff in Hallen, Hshape.
    destruct Hallen as [Hlenhd Hlentl];
    destruct Hshape as [Hshapeh Hshapet].
    simpl_len.
    assert (Hlensingle: length (simplify_single let1 t1 phd1) =
      length (simplify_single let2 t2 phd2)).
    {
      unfold simplify_single.
      destruct phd1 as [[| p1 ps1] a1];
      destruct phd2 as [[| p2 ps2] a2]; try discriminate; auto.
      simpl_len.
      apply length_simplify_aux.
      simpl in Hshapeh.
      apply andb_true_iff in Hshapeh.
      apply Hshapeh.
    }
    rewrite Hlensingle.
    rewrite !map2_app by (apply Hlensingle).
    rewrite !forallb_app.
    specialize (IH ptl2 (ltac:(lia)) Hlentl Hshapet).
    apply andb_true_iff in IH.
    destruct IH as [IH1 IH2].
    apply andb_true_iff in IH2.
    destruct IH2 as [IH2 IH3].
    apply Nat.eqb_eq in IH2.
    rewrite IH1, IH2, Nat.eqb_refl, IH3. simpl.
    rewrite !andb_true_r.
    (*Now just prove the [simplify_single] conditions*)
    clear -Hshapeh Hlenhd.
    unfold simplify_single.
    destruct phd1 as [[| p1 ps1] a1];
    destruct phd2 as [[| p2 ps2] a2]; try discriminate; auto.
    simpl in Hshapeh, Hlenhd.
    apply andb_true_iff in Hshapeh.
    destruct Hshapeh as [Hshape Htl].
    revert a1 a2.
    generalize dependent p2.
    induction p1; simpl; intros p2; destruct p2; try discriminate; intros; simpl;
    try rewrite !andb_true_r; try rewrite Htl; auto.
    + rewrite Hshape; auto.
    +  (*or*)
      apply andb_true_iff in Hshape.
      destruct Hshape as [Hshape1 Hshape2].
      rewrite !map_app, !map2_app, !forallb_app; auto;
      try solve[simpl_len; apply length_simplify_aux; auto].
      specialize (IHp1_1 _ Hshape1 a1 a2).
      apply andb_true_iff in IHp1_1.
      destruct IHp1_1 as [IH1 IH2]; rewrite IH1, IH2.
      simpl; auto.
Qed.


Lemma lens_mx_cons {A B: Type} {h1 : list pattern * A} 
  {h2: list pattern * B} {t1 t2}:
  lens_mx (h1 :: t1) (h2 :: t2) =
  (length (fst h1) =? length (fst h2)) && (lens_mx t1 t2).
Proof.
  unfold lens_mx. simpl.
  unfold all2. simpl.
  rewrite andb_comm, <- !andb_assoc. f_equal.
  apply andb_comm.
Qed.

Lemma shape_mx_cons {A B: Type}{h1 : list pattern * A} 
  {h2: list pattern * B} {t1 t2}:
  shape_mx (h1 :: t1) (h2 :: t2) =
  all2 shape_p (fst h1) (fst h2) && shape_mx t1 t2.
Proof.
  reflexivity.
Qed.


Lemma simplified_shape {A B: Type} 
  (P1: list (list pattern * A)) 
  (P2: list (list pattern * B)):
  lens_mx P1 P2 ->
  shape_mx P1 P2 ->
  simplified P1 ->
  simplified P2.
Proof.
  unfold simplified, shape_mx, lens_mx.
  generalize dependent P2.
  induction P1 as [| h1 t1 IH]; intros [| h2 t2]; simpl; try discriminate; auto.
  rewrite !all2_cons.
  unfold is_true; rewrite !andb_true_iff.
  intros [Hlent [Hlenh Hlens]] [Hshapeh Hshapet].
  destruct h1 as [ps1 a1]; destruct h2 as [ps2 a2]; simpl fst in *;
  try discriminate.
  destruct ps1 as [| p1 tl1]; destruct ps2 as [| p2 tl2]; intros [Hfst Hrest]; try discriminate; simpl; auto.
  - split; auto. apply IH; auto. rewrite Hlent; auto.
  - split; auto.
    2: { apply IH; auto. rewrite Hlent; auto. }
    (*The interesting case*)
    rewrite all2_cons in Hshapeh.
    rewrite andb_true_iff in Hshapeh. destruct Hshapeh as [Hshapep Hshapetl].
    clear -Hshapep Hfst.
    destruct p1; destruct p2; auto.
Qed.

Lemma lens_mx_rev {A B: Type} 
  (P1: list (list pattern * A)) 
  (P2: list (list pattern * B)):
  lens_mx (rev P1) (rev P2) = lens_mx P1 P2.
Proof.
  unfold lens_mx. simpl_len.
  destruct (Nat.eqb_spec (length P1) (length P2)); simpl; auto.
  rewrite <- all2_rev; auto.
Qed.


(*Equivalence of [populate_all] under [lens_mx] and [shape_mx]*)


(*Equivalence of [get_heads] under [lens_mx] and [shape_mx]*)
Lemma get_heads_shape {A B} (P1: list (list pattern * A)) 
  (P2 : list (list pattern * B))
  (Hlen: lens_mx P1 P2)
  (Hshape: shape_mx P1 P2):
  opt_related (fun l1 l2 =>
    length l1 = length l2 /\
    all2 shape_p l1 l2)
  (get_heads P1) (get_heads P2).
Proof.
  generalize dependent P2.
  induction P1 as [| h1 t1 IH]; simpl;
  intros [| h2 t2]; try discriminate; simpl; auto.
  rewrite lens_mx_cons, shape_mx_cons.
  unfold is_true. rewrite !andb_true_iff.
  intros [Hlen Hlens] [Hshape Hshapes].
  apply Nat.eqb_eq in Hlen.
  destruct h1 as [ps1 a1]; destruct h2 as [ps2 a2].
  simpl fst in *. destruct ps1 as [| phd1 ptl1];
  destruct ps2 as [| phd2 ptl2]; try discriminate; simpl; auto.
  specialize (IH _ Hlens Hshapes).
  destruct (get_heads t1) as [l1|]; simpl in IH |- *.
  - destruct (get_heads t2) as [l2|]; [|contradiction].
    simpl. destruct IH as [Hlenls Halll].
    rewrite Hlenls. split; auto.
    rewrite all2_cons in Hshape |- * .
    rewrite andb_true_iff in Hshape.
    destruct Hshape as [Hshape _].
    rewrite Hshape, Halll. reflexivity.
  - destruct (get_heads t2); [contradiction|auto].
Qed.

Lemma populate_all_shape {constrs A B} 
  (P1: list (list pattern * A)) 
  (P2 : list (list pattern * B))
  (Hsimpl: simplified P1) (*easier*)
  (Hlen: lens_mx P1 P2)
  (Hshape: shape_mx P1 P2):
  opt_related (fun o1 o2 =>
    map (fun x => fst (fst x)) (snd o1) =
    map (fun x => fst (fst x)) (snd o2) /\
    (all2 (fun x y => 
      (length (snd (fst x)) =? length (snd (fst y))) &&
      all2 rel (snd (fst x)) (snd (fst y)) &&
      (*Do we need these?*)
      (length (snd x) =? length (snd y)) &&
      all2 shape_p (snd x) (snd y)) (snd o1) (snd o2)) /\
    forall cs,
    opt_related (fun ps1 ps2 => 
      length ps1 = length ps2 /\
      all2 shape_p ps1 ps2)
      (amap_get funsym_eq_dec (fst o1) cs)
      (amap_get funsym_eq_dec (fst o2) cs)) 
  (populate_all constrs P1)
  (populate_all constrs P2).
Proof.
  unfold populate_all.
  pose proof (get_heads_shape _ _ Hlen Hshape) as Hheads.
  destruct (get_heads P1) as [heads1|] eqn : Hhead1; simpl in Hheads.
  2: { destruct (get_heads P2); [contradiction| auto]. }
  destruct (get_heads P2) as [heads2|] eqn : Hhead2; [|contradiction].
  assert (Hsimpl2: simplified P2) by 
    (apply (simplified_shape _ _ Hlen Hshape Hsimpl)).
  rewrite <- simplified_rev in Hsimpl.
  rewrite <- simplified_rev in Hsimpl2.
  assert (Hget1: get_heads (rev P1) = Some (rev heads1)) by
    (rewrite get_heads_rev, Hhead1; reflexivity).
  assert (Hget2: get_heads (rev P2) = Some (rev heads2)) by
    (rewrite get_heads_rev, Hhead2; reflexivity).
  destruct Hheads as [Hlenh Hallhds].
  assert (Hall: all2 shape_p (rev heads1) (rev heads2)) by
    (rewrite <- all2_rev; auto). 
  rewrite !fold_left_right_opt.
  assert (Hlen2: length (rev heads1) = length (rev heads2)) by solve_len.
  rewrite <- lens_mx_rev in Hlen.
  clear -Hsimpl Hsimpl2 Hget1 Hget2 Hall Hlen2 Hlen.
  generalize dependent (rev heads1).
  generalize dependent (rev heads2).
  generalize dependent (rev P2).
  generalize dependent (rev P1).
  clear P1 P2.
  intros P1; induction P1 as [| [ps1 a1] t1 IH].
  - intros _. intros [| [ps2 a2] t2]; try discriminate. simpl; auto.
    intros _ _ l1 Hsome1 l2 Hsome2 Hall Hlen.
    inversion Hsome1; inversion Hsome2; subst; simpl. auto.
  - intros Hsimp1 [| [ps2 a2] t2] Hlens; [discriminate|].
    rewrite lens_mx_cons in Hlens.
    intros Hsimp2 hds1 Hhds1 hds2 Hhds2 Hshapes Hlenheads.
    simpl in Hhds1, Hhds2.
    destruct ps1 as [|phd1 ptl1]; [discriminate|].
    destruct ps2 as [|phd2 ptl2]; [discriminate|].
    destruct (get_heads t1) as [hd1|] eqn : Hhd1; [|discriminate].
    destruct (get_heads t2) as [hd2|] eqn : Hhd2; [|discriminate].
    simpl in Hhds1, Hhds2. revert Hhds1 Hhds2. inv Hsome. inv Hsome.
    simpl.
    (*Now we use IH*)
    simpl in *.
    rewrite all2_cons in Hshapes.
    apply andb_true_iff in Hsimp1, Hsimp2, Hlens, Hshapes.
    destruct Hsimp1 as [Hsimphd1 Hsimpt1].
    destruct Hsimp2 as [Hsimphd2 Hsimpt2].
    destruct Hlens as [Hlenpt Hlens].
    destruct Hshapes as [Hshapep Hshapeh].
    specialize (IH Hsimpt1 _ Hlens Hsimpt2 _ Hhd2 _ eq_refl Hshapeh
      (ltac:(lia))).
    destruct (fold_right_opt _ hd1 _) as [o1|]; simpl in IH |- *.
    2: { destruct (fold_right_opt _ hd2 _) as [o2|]; [contradiction|auto]. }
    destruct (fold_right_opt _ hd2 _) as [o2|]; [simpl in IH|contradiction].
    simpl.
    destruct IH as [Hmap [IHall IH]].
    (*Now we need to reason about [populate] - simplified helps here*)
    destruct phd1 as [| f1 tys1 ps1 | | |]; destruct phd2 as [| f2 tys2 ps2 | | |]; try discriminate;
    simpl; auto.
    (*constr case*)
    destruct o1 as [css1 csl1].
    destruct o2 as [css2 csl2].
    simpl in *.
    (*shape gives f1 = f2*)
    destruct (funsym_eq_dec f1 f2); [|discriminate]; subst.
    destruct (constrs f2); simpl; auto.
    (*Now, will need to use fact that mem are equivalent from IH*)
    rewrite !amap_mem_spec.
    assert (IH':=IH).
    specialize (IH f2).
    destruct (amap_get funsym_eq_dec css1 f2) as [y1|] eqn : Hget1;
    destruct (amap_get funsym_eq_dec css2 f2) as [y2|] eqn : Hget2;
    simpl in IH; try contradiction; try (simpl; split; auto); auto;
    [f_equal; auto|].
    split.
    {
      rewrite all2_cons; simpl.
      bool_hyps. unfold is_true. rewrite !andb_true_iff; split_all; auto.
    }
    (*Both some*) simpl. intros cs.
    destruct (funsym_eq_dec cs f2).
    * subst. rewrite !amap_set_get_same; simpl.
      bool_hyps; split; auto. apply Nat.eqb_eq; auto.
    * rewrite !amap_set_get_diff; auto.
Qed.


Definition all_wilds {A: Type} (P:list (list pattern * A)) :=
forallb (fun x =>
        match (fst x) with
        | Pwild :: _ => true
        | _ => false
        end) P.


Lemma populate_all_false {A: Type} {f} {o}
  {P: list (list pattern * A)}
  (Hpop: populate_all f P = Some o)
  (Hsimpl: simplified P)
  (Hf: forall x, f x = false)
  :
  all_wilds P.
Proof.
  unfold all_wilds.
  unfold populate_all in Hpop.
  destruct (get_heads P) as [heads|] eqn : Hheads; [|discriminate].
  rewrite fold_left_right_opt in Hpop.
  assert (Hhead1: get_heads (rev P) = Some (rev heads)). {
    rewrite get_heads_rev, Hheads. reflexivity.
  }
  rewrite <- forallb_rev.
  rewrite <- simplified_rev in Hsimpl.
  clear Hheads.
  generalize dependent (rev heads). revert o.
  induction (rev P) as [| [ps a] t IH ]; clear P heads; simpl; auto.
  intros o heads Hheads.
  destruct ps as [| phd ptl]; [discriminate|].
  simpl. destruct (get_heads t); simpl; [|discriminate].
  inv Hsome.
  simpl in Hsimpl.
  apply andb_true_iff in Hsimpl.
  destruct Hsimpl as [Hsimp Hsimpl].
  simpl in Hheads.
  apply option_bind_some in Hheads.
  destruct Hheads as [z [Hz Hpop]].
  specialize (IH Hsimpl _ _ Hz eq_refl).
  destruct phd; auto. simpl.
  simpl in Hpop. destruct z as [css csl].
  rewrite Hf in Hpop. discriminate.
Qed.

Lemma populate_all_wilds {A: Type} {f} (P: list (list pattern * A))
  (Hsimpl: simplified P)
  (Hwilds: all_wilds P):
  isSome (populate_all f P).
Proof.
  destruct (populate_all f P) as [o|] eqn : Hpop; auto.
  unfold populate_all in Hpop.
  destruct (get_heads P) as [heads|] eqn : Hheads.
  - rewrite fold_left_right_opt in Hpop.
    assert (Hhead1: get_heads (rev P) = Some (rev heads)). {
      rewrite get_heads_rev, Hheads. reflexivity.
    }
    unfold all_wilds in Hwilds.
    rewrite <- forallb_rev in Hwilds.
    rewrite <- simplified_rev in Hsimpl.
    clear Hheads.
    generalize dependent (rev heads).
    induction (rev P) as [| [ps a] t IH ]; clear P heads; simpl; auto.
    + intros heads Hheads. intros Hsome. inversion Hsome; subst; auto.
      simpl in Hheads. discriminate.
    + intros heads Hheads.
      destruct ps as [| phd ptl]; [discriminate|].
      simpl in *.
      destruct (get_heads t); simpl in *; [|discriminate].
      inv Hsome. simpl in Hheads. bool_hyps.
      destruct (fold_right_opt _ l _) eqn : Hfold; simpl in *; auto.
      * (*contradicts populate*)
        destruct phd; simpl in *; auto. discriminate.
      * eapply IH; eauto.
  - clear -Hwilds Hheads.
    unfold get_heads in Hheads.
    unfold all_wilds in Hwilds.
    induction P as [| [ps a] t IH]; simpl in *; try discriminate; bool_hyps; eauto.
    destruct ps as [| phd ptl]; simpl in *; auto.
    destruct (fold_right _ _); simpl in *; auto. discriminate.
Qed.


(*And show [all_wilds] preserved by shape_mx*)
Lemma all_wilds_shape {A B: Type} 
  (P1: list (list pattern * A)) (P2: list (list pattern * B)):
  lens_mx P1 P2 ->
  shape_mx P1 P2 ->
  all_wilds P1 ->
  all_wilds P2.
Proof.
  unfold lens_mx, shape_mx, all_wilds.
  unfold is_true; rewrite !andb_true_iff.
  intros [Hlens Halllens].
  apply Nat.eqb_eq in Hlens.
  generalize dependent P2.
  induction P1 as [| [ps1 a1] t IH]; intros [| [ps2 a2] t2]; auto; try discriminate; simpl.
  rewrite !all2_cons.
  rewrite !andb_true_iff.
  intros Hlent [Hlenh Halllen] [Hshapeh Hallshape].
  simpl in *.
  specialize (IH t2 (ltac:(lia)) Halllen Hallshape).
  destruct ps1 as [| phd1 ptl1]; destruct ps2 as [|phd2 ptl2]; simpl in *; auto; try discriminate.
  - intros [Hft  Hall]. discriminate.
  -  intros [Hhd Htl]; split; auto.
    destruct phd1; destruct phd2; try discriminate; auto.
Qed.

Lemma all_wilds_no_constr {A: Type} {P: list (list pattern * A)} {x y}:
  all_wilds P ->
  existsb (constr_args_at_head x y) P = false.
Proof.
  unfold all_wilds. unfold is_true. rewrite forallb_forall.
  intros Hall.
  rewrite existsb_false.
  rewrite Forall_forall.
  intros r Hinr.
  specialize (Hall _ Hinr).
  unfold constr_args_at_head.
  destruct r as [ [|phd ptl] a]; simpl in *; auto.
  destruct phd; auto; discriminate.
Qed.

Lemma len_mx_null_equiv {A B: Type} 
  (P1: list (list pattern * A))
  (P2: list (list pattern * B)):
  lens_mx P1 P2 ->
  existsb (fun x : list pattern * A => null (fst x)) P1 =
  existsb (fun x : list pattern * B => null (fst x)) P2.
Proof.
  unfold lens_mx.
  intros Hlens.
  apply existsb_eq'. rewrite all2_Forall2 in Hlens.
  revert Hlens.
  apply Forall2_impl. intros l1 l2 Hlen.
  apply Nat.eqb_eq in Hlen.
  destruct (fst l1); destruct (fst l2); auto; discriminate.
Qed. 

Lemma default_shape {A B: Type} 
  (P1: list (list pattern * A)) 
  (P2: list (list pattern * B)):
  shape_mx P1 P2 ->
  lens_mx P1 P2 ->
  shape_mx (Pattern.default P1) (Pattern.default P2) &&
  lens_mx (Pattern.default P1) (Pattern.default P2).
Proof.
  unfold shape_mx, lens_mx.
  unfold is_true. rewrite !andb_true_iff.
  intros Hshape [Hlenp12 Hlens].
  apply Nat.eqb_eq in Hlenp12.
  generalize dependent P2.
  induction P1 as [| h1 t1 IH]; intros [| h2 t2]; try discriminate; simpl; auto.
  rewrite !all2_cons.
  rewrite !andb_true_iff.
  intros [Hshapeh Hshapet] Hlent [Hlenh Hlenst].
  destruct h1 as [ps1 a1]; destruct h2 as [ps2 a2]; simpl fst in *.
  destruct ps1 as [| phd1 ptl1]; destruct ps2 as [| phd2 ptl2]; try discriminate; auto.
  destruct phd1; destruct phd2; try discriminate; auto.
  simpl. rewrite !all2_cons; simpl.
  rewrite all2_cons in Hshapeh. simpl in Hshapeh, Hlenh.
  rewrite Hshapeh, Hlenh; simpl; auto.
Qed. 

Lemma constr_at_head_ex_shape {A B} {P1 : list (list pattern * A)} 
  {P2: list (list pattern * B)} cs:
  shape_mx P1 P2 ->
  lens_mx P1 P2 ->
  constr_at_head_ex cs P1 = constr_at_head_ex cs P2.
Proof.
  unfold shape_mx, lens_mx.
  unfold is_true. rewrite !andb_true_iff.
  intros Hshape [Hlenp12 Hlens].
  apply Nat.eqb_eq in Hlenp12.
  generalize dependent P2.
  induction P1 as [| h1 t1 IH]; intros [| h2 t2]; try discriminate; simpl; auto.
  rewrite !all2_cons.
  rewrite !andb_true_iff.
  intros [Hshapeh Hshapet] Hlent [Hlenh Hlenst].
  unfold constr_at_head.
  destruct h1 as [ps1 a1]; destruct h2 as [ps2 a2]; simpl fst in *.
  destruct ps1 as [| phd1 ptl1]; destruct ps2 as [| phd2 ptl2]; try discriminate;
  [simpl; auto|].
  destruct phd1; destruct phd2; try discriminate; simpl; auto.
  rewrite all2_cons in Hshapeh.
  simpl in Hshapeh.
  destruct (funsym_eq_dec f f0); subst; [|discriminate].
  f_equal; auto.
Qed.

Lemma wild_at_head_ex_shape {A B} {P1: list (list pattern * A)} 
  {P2: list (list pattern * B)}:
  shape_mx P1 P2 ->
  lens_mx P1 P2 ->
  wild_at_head_ex P1 = wild_at_head_ex P2.
Proof.
  unfold shape_mx, lens_mx.
  unfold is_true. rewrite !andb_true_iff.
  intros Hshape [Hlenp12 Hlens].
  apply Nat.eqb_eq in Hlenp12.
  generalize dependent P2.
  induction P1 as [| h1 t1 IH]; intros [| h2 t2]; try discriminate; simpl; auto.
  rewrite !all2_cons.
  rewrite !andb_true_iff.
  intros [Hshapeh Hshapet] Hlent [Hlenh Hlenst].
  unfold pat_at_head.
  destruct h1 as [ps1 a1]; destruct h2 as [ps2 a2]; simpl fst in *.
  destruct ps1 as [| phd1 ptl1]; destruct ps2 as [| phd2 ptl2]; try discriminate;
  [simpl; auto|].
  destruct phd1; destruct phd2; try discriminate; simpl; auto.
Qed.

Variable (rel_refl: forall ty, rel ty ty).

Lemma all_rel_refl l:
  all2 rel l l.
Proof.
  induction l as [| h t IH]; simpl; auto; 
  rewrite all2_cons, rel_refl; auto.
Qed.

Lemma shape_p_refl p:
  shape_p p p.
Proof.
  induction p; simpl; auto.
  - destruct (funsym_eq_dec _ _); [|contradiction].
    destruct (Nat.eqb_spec (length ps) (length ps)); [| contradiction].
    destruct (Nat.eqb_spec (length vs) (length vs)); [|contradiction].
    rewrite all_rel_refl. simpl.
    induction ps as [| h t IH]; simpl; auto.
    inversion H; subst. rewrite all2_cons, H2; auto.
  - rewrite IHp1, IHp2; auto.
Qed.

Lemma all_shape_p_refl l:
  all2 shape_p l l.
Proof.
  induction l as [| h t]; simpl; auto.
  rewrite all2_cons, shape_p_refl, IHt.
  reflexivity.
Qed.


(*Not quite spec because not necessarily well-typed, so statement is
  awkward*)
Lemma spec_shape {A B: Type} cs n 
  (P1: list (list pattern * A)) 
  (P2: list (list pattern * B)):
  shape_mx P1 P2 ->
  lens_mx P1 P2 ->
  shape_mx (omap
    (fun x =>
    match fst x with
    | Pconstr fs _ pats :: ps => if funsym_eqb fs cs then Some (rev pats ++ ps, snd x)
    else None
    | Pwild :: ps => Some (repeat Pwild n ++ ps, snd x)
    | _ => None
    end) P1)
    (omap
    (fun x  =>
    match fst x with
    | Pconstr fs _ pats :: ps => if funsym_eqb fs cs then Some (rev pats ++ ps, snd x)
    else None
    | Pwild :: ps => Some (repeat Pwild n ++ ps, snd x)
    | _ => None
    end) P2) /\
  lens_mx (omap
    (fun x =>
    match fst x with
    | Pconstr fs _ pats :: ps => if funsym_eqb fs cs then Some (rev pats ++ ps, snd x)
    else None
    | Pwild :: ps => Some (repeat Pwild n ++ ps, snd x)
    | _ => None
    end) P1)
    (omap
    (fun x =>
    match fst x with
    | Pconstr fs _ pats :: ps => if funsym_eqb fs cs then Some (rev pats ++ ps, snd x)
    else None
    | Pwild :: ps => Some (repeat Pwild n ++ ps, snd x)
    | _ => None
    end) P2).
Proof.
  unfold shape_mx, lens_mx.
  unfold is_true. rewrite !andb_true_iff.
  intros Hshape [Hlenp12 Hlens].
  apply Nat.eqb_eq in Hlenp12.
  generalize dependent P2.
  induction P1 as [| h1 t1 IH]; intros [| h2 t2]; try discriminate; simpl; auto.
  rewrite !all2_cons.
  rewrite !andb_true_iff.
  intros [Hshapeh Hshapet] Hlent [Hlenh Hlenst].
  destruct h1 as [ps1 a1]; destruct h2 as [ps2 a2]; simpl fst in *.
  destruct ps1 as [| phd1 ptl1]; destruct ps2 as [| phd2 ptl2]; try discriminate; auto.
  destruct phd1 as [| f1 tys1 ps1 | | |]; 
  destruct phd2 as [| f2 tys2 ps2 | | |]; try discriminate; auto.
  - (*Pconstr*)
    simpl.
    rewrite all2_cons in Hshapeh; simpl in Hshapeh.
    destruct (funsym_eq_dec f1 f2); [|discriminate]; subst.
    destruct (funsym_eqb_spec f2 cs); auto; subst.
    rewrite !all2_cons; simpl.
    simpl in Hshapeh.
    rewrite !andb_true_iff in Hshapeh.
    destruct Hshapeh as [ [[[Hlentys Hallrel] Hlenps] Hallps] Hshapetl].
    simpl in *. apply Nat.eqb_eq in Hlenps, Hlentys.
    specialize (IH t2 Hshapet (ltac:(lia)) Hlenst).
    destruct IH as [IH1 IH2].
    rewrite !andb_true_iff. split_all; auto.
    + unfold all2. rewrite !map2_app, forallb_app by solve_len.
      rewrite map2_rev; auto. rewrite forallb_rev. 
      rewrite andb_true_iff; auto.
    + simpl_len. apply Nat.eqb_eq in Hlenh.
      rewrite Hlenps, Hlenh. apply Nat.eqb_refl.
  - (*Pwild*)
    simpl.
    rewrite all2_cons in Hshapeh; simpl in Hshapeh.
    rewrite !all2_cons. simpl. apply Nat.eqb_eq in Hlenh.
    specialize (IH t2 Hshapet (ltac:(lia)) Hlenst).
    destruct IH as [IH1 IH2].
    rewrite !andb_true_iff. split_all; auto.
    + unfold all2. rewrite !map2_app, forallb_app by solve_len.
      unfold all2 in Hshapeh; rewrite Hshapeh, andb_true_r.
      apply all_shape_p_refl.
    + simpl_len. simpl in Hlenh. apply Nat.eqb_eq. lia.
Qed.

Lemma ty_rel_subst tys1 tys2 params ty:
  length tys1 = length tys2 ->
  all2 ty_rel tys1 tys2 ->
  ty_rel (ty_subst params tys1 ty) ((ty_subst params tys2 ty)).
Proof.
  intros Hall2.
  destruct ty; simpl; auto.
  unfold ty_subst; simpl.
  generalize dependent tys2.
  revert params.
  induction tys1 as [| h1 t1 IH]; intros params [|h2 t2]; auto; try discriminate; simpl.
  - intros _ _. destruct params; auto.
  - intros Hlen.
    rewrite all2_cons.
    unfold is_true at 1.
    rewrite andb_true_iff; intros [Hrelh Hrelt].
    destruct params as [| p1 ptl]; simpl; auto.
    destruct (typevar_eq_dec t p1); subst; simpl; auto.
Qed.

Lemma ty_rel_subst_list tys1 tys2 params args:
  length tys1 = length tys2 ->
  all2 ty_rel tys1 tys2 ->
  all2 ty_rel (map (ty_subst params tys1) args)
    (map (ty_subst params tys2) args).
Proof.
  clear.
  intros Hlen Hall2.
  induction args as [| a1 atl IH]; simpl; auto.
  rewrite all2_cons, IH, andb_true_r.
  apply ty_rel_subst; auto.
Qed.

Fixpoint t_fun_equiv (t1 t2: term) :=
  match t1, t2 with
  | Tfun f1 ty1 tm1, Tfun f2 ty2 tm2 =>
    (funsym_eq_dec f1 f2) &&
    (length tm1 =? length tm2) && 
    (length ty1 =? length ty2) &&
    (all2 rel ty1 ty2) &&
    (all2 (fun t1 t2 => t_fun_equiv t1 t2)) tm1 tm2
  | Tvar _, Tvar _ => true
  | Tconst _, Tconst _ => true
  | Tlet _ _ _, Tlet _ _ _ => true
  | Tif _ _ _, Tif _ _ _ => true
  | Tmatch _ _ _, Tmatch _ _ _ => true
  | Teps _ _, Teps _ _ => true
  | _, _ => false
  end.

End ShapeP.

(*Instantiate with [ty_rel] here*)
Lemma ty_rel_refl ty:
  ty_rel ty ty.
Proof.
  destruct ty; auto.
Qed.

(*A bit of a hack: for the [simpl_constr] version, the relation
  is equality, since we require the terms to be the same, and for IH purposes, the types also
  must be the same. But in general, we want [ty_rel*)
Definition change_rel (simpl_constr: bool) := if simpl_constr then vty_eqb else ty_rel.

(*We do have to know that change_rel implies ty_rel (for ADT case)*)
Lemma change_rel_ty_rel simpl_constr ty1 ty2:
  change_rel simpl_constr ty1 ty2 -> ty_rel ty1 ty2.
Proof.
  destruct simpl_constr; auto.
  simpl. intros Heq. apply vty_eqb_eq in Heq.
  subst. apply ty_rel_refl.
Qed.

Lemma change_rel_refl simpl_constr: forall t,
  change_rel simpl_constr t t.
Proof. 
  destruct simpl_constr; [|apply ty_rel_refl].
  simpl. intros t. apply vty_eq_eqb. reflexivity.
Qed. 

Lemma all2_vty_eqb l1 l2:
  length l1 = length l2 ->
  all2 vty_eqb l1 l2 ->
  l1 = l2.
Proof.
  revert l2. induction l1 as [| h1 t1 IH]; simpl; intros [| h2 t2]; simpl; try discriminate; auto.
  intros Hlen. rewrite all2_cons. unfold is_true. rewrite andb_true_iff.
  intros [Heq Htl]. apply vty_eqb_eq in Heq. subst. f_equal; auto.
Qed.

(*We need that [change_rel] is preserved by substitution*)
Lemma change_rel_subst_list simpl_constr tys1 tys2 params args:
  length tys1 = length tys2 ->
  all2 (change_rel simpl_constr) tys1 tys2 ->
  all2 (change_rel simpl_constr) (map (ty_subst params tys1) args) (map (ty_subst params tys2) args).
Proof.
  destruct simpl_constr; simpl; [|apply ty_rel_subst_list].
  intros Htys1 Htys2.
  apply all2_vty_eqb in Htys2; auto. subst.
  apply all_rel_refl. intros ty. apply vty_eq_eqb. reflexivity.
Qed.

Lemma all2_app {A B: Type} (f: A -> B -> bool) (l1 l2: list A) (l3 l4: list B):
  length l1 = length l3 ->
  all2 f (l1 ++ l2) (l3 ++ l4) = all2 f l1 l3 && all2 f l2 l4.
Proof.
  intros Hlen. unfold all2. rewrite map2_app by auto. rewrite forallb_app; reflexivity.
Qed.

Lemma all2_firstn {A B: Type} (p: A -> B -> bool) (l1: list A) (l2: list B) (n: nat):
  all2 p l1 l2 ->
  all2 p (firstn n l1) (firstn n l2).
Proof.
  revert l2 n. induction l1 as [| h1 t1 IH]; intros [| h2 t2] [| n']; simpl; auto.
  rewrite all2_cons. unfold is_true at 1. rewrite andb_true_iff; intros [Hp Htl].
  rewrite all2_cons. rewrite Hp. simpl. auto.
Qed.

Lemma all2_t_fun_equiv_var (rel: vty -> vty -> bool) (l1 l2: list vsymbol):
  all2 (t_fun_equiv rel) (map Tvar l1) (map Tvar l2).
Proof.
  revert l2. induction l1 as [| h1 t1 IH]; intros [| h2 t2]; auto; simpl.
  rewrite all2_cons. simpl. auto.
Qed.


(*MUST be false for simpl_constr - does NOT hold of other version*)
Opaque dispatch1_opt.
Opaque dispatch1.
Lemma compile_change_tm_ps {A B: Type} {constrs match1 match2
  let1 let2 vars1 vars2 tms1 tms2} (simpl_constr: bool)
  {P1: list (list pattern * A)} {P2: list (list pattern * B)}
  (Hlet1: forall (v : vsymbol) (tm : term) (a : A) (x : vsymbol),
    In x (vars1 (let1 v tm a)) <-> v = x \/ In x (tm_bnd tm) \/ In x (tm_fv tm) \/ In x
    (vars1 a))
  (Hlet2: forall (v : vsymbol) (tm : term) (a : B) (x : vsymbol),
    In x (vars2 (let2 v tm a)) <-> v = x \/ In x (tm_bnd tm) \/ In x (tm_fv tm) \/ In x
    (vars2 a))
  (Hlens: lens_mx P1 P2)
  (Hshape: shape_mx ty_rel P1 P2)
  (Htyslen: length tms1 = length tms2)
  (Htys: all2 ty_rel (map snd tms1) (map snd tms2))
  (Htms: if simpl_constr then all2 (t_fun_equiv ty_rel) (map fst tms1) (map fst tms2) else true):
  (*NOTE: not proving equality anymore -
    but in some cases, can still get equality*)
  isSome (compile constrs match1 let1 vars1 true simpl_constr tms1 P1) ->
  isSome (compile constrs match2 let2 vars2 true simpl_constr tms2 P2).
Proof.
  revert tms2 P2 Hlens Hshape Htyslen Htys Htms.
  apply (compile_ind constrs match1 let1 vars1 Hlet1
    true simpl_constr (fun tms1 P1 o =>
      forall (tms2 : list (term * vty)) (P2 : list (list pattern * B)) 
      (Hlens: lens_mx P1 P2)
      (Hshape: shape_mx ty_rel P1 P2)
      (Htyslen: length tms1 = length tms2)
      (Htys: all2 ty_rel (map snd tms1) (map snd tms2))
      (Htms: if simpl_constr then all2 (t_fun_equiv ty_rel) (map fst tms1) (map fst tms2) else true),
      isSome o -> 
      isSome (compile constrs match2 let2 vars2 true simpl_constr tms2 P2)));
  clear tms1 P1; auto.
  - intros t ty tms1 P1 Hsimp tms2 P2 Hlens Hshape Htyslen Htys Htms.
    destruct tms2 as [| [t2 ty2] tms2]; [discriminate|].
    specialize (Hsimp ((t2, ty2) :: tms2) (simplify let2 t2 P2)).
    rewrite <- !compile_simplify in Hsimp by (apply Hlet1).
    rewrite <- !compile_simplify in Hsimp by (apply Hlet2).
    pose proof (@shape_mx_simplify _ A B let1 let2 t t2 _ _ Hlens Hshape) as Hsimpl.
    apply andb_true_iff in Hsimpl.
    destruct Hsimpl as [Hshape2 Hlens2].
    apply Hsimp; auto.
  - (*Some case*) intros ps1 a1 P1 [| t1 t2] [| [ps2 a2] P2]; try discriminate. auto.
  - (*Interesting case*)
    intros t ty tms1 P1 rhd rtl is_bare_css is_bare css is_constr Hsimpl
      Hrl types_cslist Hpop types cslist casewild Hdisp1 cases wilds [IHwilds IHconstrs]
      tms2 P2 Hlens Hshape Htyslen Htys Htms.
    destruct P2 as [| rhd2 rtl2]; [rewrite Hrl in Hlens; discriminate|].
    destruct tms2 as [| [t2 ty2] tms2]; [discriminate|].
    simpl in Htys. rewrite all2_cons in Htys.
    apply andb_true_iff in Htys. destruct Htys as [Htyrel Htys2]. 
    simp compile.
    set (P2:=rhd2 :: rtl2) in *.
    set (is_bare_css1:= match ty2 with
    | vty_cons _ _ => (true, [])
    | _ => (false, [])
    end) in *.
    assert (Hsimp2: simplified P2) by (eapply simplified_shape; eauto).
    assert (Hbare: (is_bare = false) \/ is_bare_css = is_bare_css1).
    {
      unfold is_bare_css, is_bare_css1. destruct ty; destruct ty2;
      try discriminate; auto.
    }
    Opaque dispatch1_opt.
    destruct Hbare as [Hbare | Hbare].
    {
      (*First case: is_bare is false, so no constructors, so
        everything is a wild and we can use IH*)
      (*Steps:
      1. Prove everything is Pwild
      2. So [populate_all] succeeds
      3. And so [types]*)
      (*How to phrase this?*)
      assert (Hwilds1: all_wilds P1). {
        apply (populate_all_false Hpop); auto. intros x.
        unfold is_constr. rewrite Hbare. simpl.
        unfold css, is_bare_css. destruct ty; simpl; rewrite andb_false_r; auto.
      }
      assert (Hwilds2: all_wilds P2). {
        apply (all_wilds_shape ty_rel P1); auto.
      }
      (*Now prove that [populate_all] is Some*)
      simpl.
      pose proof (@populate_all_wilds _
        (fun fs : funsym =>
          f_is_constr fs && (fst is_bare_css1 || in_bool funsym_eq_dec fs
          (snd is_bare_css1))) P2 Hsimp2 Hwilds2).
      destruct (populate_all _ P2) as [types_cslist2 |] eqn : Hpop2;
      [|discriminate].
      (*Now need to simplify [dispatch1_opt]*)
      apply dispatch1_opt_some in Hdisp1.
      destruct Hdisp1 as [Hnotnull Hcasewild]; subst casewild.
      destruct (dispatch1_opt let2 t2 (fst types_cslist2) P2) as [casewild2|] eqn : Hdisp2.
      2: {
        apply dispatch1_opt_none in Hdisp2. erewrite <- len_mx_null_equiv with (P1:=P1) in Hdisp2.
        rewrite existsb_forallb_negb, Hnotnull in Hdisp2. discriminate.
        auto.
      }
      (*Now prove that both maps are empty*)
      assert (Hemp1: amap_is_empty types).
      {
        unfold types.
        rewrite (amap_is_empty_get funsym_eq_dec).
        intros x.
        destruct (amap_get funsym_eq_dec (fst types_cslist) x) as [y|] eqn : Hget; auto.
        apply (populate_all_in_strong _ _ _ _ _ Hsimpl Hpop) in Hget.
        rewrite (all_wilds_no_constr Hwilds1) in Hget. discriminate.
      }
      rewrite Hemp1.
      assert (Hemp2: amap_is_empty (fst types_cslist2)).
      {
        rewrite (amap_is_empty_get funsym_eq_dec).
        intros x.
        destruct (amap_get funsym_eq_dec (fst types_cslist2) x) as [y|] eqn : Hget; auto.
        apply (populate_all_in_strong _ _ _ _ _ Hsimp2 Hpop2) in Hget.
        rewrite (all_wilds_no_constr Hwilds2) in Hget. discriminate.
      }
      rewrite Hemp2.
      apply dispatch1_opt_some in Hdisp2.
      destruct Hdisp2 as [Hall Hcasewild]; subst casewild2.
      pose proof (default_shape ty_rel P1 P2 Hshape Hlens) as Hdefault.
      apply andb_true_iff in Hdefault. destruct Hdefault as [Hshaped Hlensd].
      specialize (IHwilds tms2 (snd (dispatch1 let2 t2 (fst types_cslist2) P2))).
      forward IHwilds.
      { unfold wilds. rewrite !dispatch1_equiv_default by auto; auto. }
      forward IHwilds.
      { unfold wilds. rewrite !dispatch1_equiv_default by auto; auto. }
      clear Hshaped Hlensd. simpl in Htyslen.
      apply IHwilds; auto.
      destruct simpl_constr; auto. simpl in Htms.
      rewrite all2_cons in Htms. apply andb_true_iff in Htms.
      apply Htms. 
    } 
    (*Main case*)
    generalize dependent is_bare_css1. intros is_bare_css1 Hbarecs; subst is_bare_css1.
    (*Deal with [populate_all]*)
    simpl.
    pose proof (@populate_all_shape ty_rel is_constr _ _ _ _ Hsimpl Hlens Hshape) as Hpops.
    rewrite Hpop in Hpops. simpl in Hpops.
    destruct (populate_all _ P2) as [types_cslist2 |] eqn : Hpop2; [|contradiction].
    (*And [dispatch1_opt]*)
    apply dispatch1_opt_some in Hdisp1.
    destruct Hdisp1 as [Hnotnull Hcasewild]; subst casewild.
    destruct (dispatch1_opt let2 t2 (fst types_cslist2) P2) as [casewild2|] eqn : Hdisp2.
    2: {
      apply dispatch1_opt_none in Hdisp2. erewrite <- len_mx_null_equiv with (P1:=P1) in Hdisp2.
      rewrite existsb_forallb_negb, Hnotnull in Hdisp2. discriminate.
      auto.
    }
    apply dispatch1_opt_some in Hdisp2.
    destruct Hdisp2 as [Hnotnull2 Hcasewild2]; subst casewild2.
    (*Now prove that emptiness of types_cslist and types_cslist2 is equal*)
    unfold types.
    assert (Hsize: amap_size (fst types_cslist) = amap_size (fst types_cslist2)).
    {
      apply same_elts_size with (eq_dec:=funsym_eq_dec).
      intros f.
      rewrite !amap_mem_spec.
      destruct Hpops as [Hmap [Hcslist Hpops]].
      specialize (Hpops f).
      destruct (amap_get funsym_eq_dec (fst types_cslist) f);
      destruct (amap_get funsym_eq_dec (fst types_cslist2) f);
      auto; contradiction.
    }
    assert (Hemp: amap_is_empty (fst types_cslist) = amap_is_empty (fst types_cslist2)).
    { apply is_true_eq. rewrite !amap_size_emp, Hsize. reflexivity. }
    (*Specialize IHwilds for multiple cases*)
    pose proof (default_shape ty_rel P1 P2 Hshape Hlens) as Hdefault.
    apply andb_true_iff in Hdefault. destruct Hdefault as [Hshaped Hlensd].
    specialize (IHwilds tms2 (snd (dispatch1 let2 t2 (fst types_cslist2) P2))).
    forward IHwilds.
    { unfold wilds. rewrite !dispatch1_equiv_default by auto; auto. }
    forward IHwilds.
    { unfold wilds. rewrite !dispatch1_equiv_default by auto; auto. }
    clear Hshaped Hlensd. simpl in Htyslen.
    specialize (IHwilds (ltac:(lia)) Htys2).
    forward IHwilds.
    { destruct simpl_constr; auto. simpl in Htms; rewrite all2_cons in Htms;
      apply andb_true_iff in Htms; apply Htms. } 
    (*case 1: types is empty - from IH*)
    rewrite Hemp.
    destruct (amap_is_empty (fst types_cslist2)) eqn : Hisemp; [auto|].
    (*Otherwise, prove [comp_full] the same*)
    (*First, show that [is_wilds] is the same*)
    (*Simplify*)
    subst is_bare_css is_bare css is_constr.
    set (is_bare_css := match ty with
      | vty_cons _ _ => (true, [])
      | _ => (false, [])
      end) in *.
    set (is_bare := fst is_bare_css) in *.
    set (css := snd is_bare_css) in *.
    set (is_constr := fun fs : funsym => f_is_constr fs && (is_bare || in_bool funsym_eq_dec fs css)) in *.
    (*Prove [comp_full]*)
    match goal with
    |- is_true (isSome (if _ then _ else ?x)) ->
      is_true (isSome (if _ then _ else ?y)) =>
    assert (Hcompfull: isSome x -> isSome y)
    end.
    {
      unfold comp_full.
      destruct Hpops as [Hcslisteq [Hcslist Hpops]].
      (*Prove [is_wilds] the same*)
      match goal with
      | |-  is_true (isSome (option_bind (option_bind ?o ?f1) ?f2)) ->
        is_true (isSome (option_bind(option_bind ?o1 ?f3) ?f4)) =>
        assert (Hsomeq: o1 = o); [| rewrite Hsomeq; clear Hsomeq;
          set (no_wilds := o) in *]
      end.
      {
        destruct is_bare.
        - match goal with
          |- option_bind (option_map ?f1 ?o1) ?f2 =
            option_bind (option_map ?f3 ?o2) ?f4 =>
            assert (Heq: option_map f1 o1 = option_map f3 o2); [| rewrite Heq]
          end.
          {
            unfold cslist.
            destruct (snd types_cslist) as [| [[cs1 tys1] ps1] tl1]; 
            destruct (snd types_cslist2) as [| [[cs2 tys2] ps2] tl2]; auto;
            try discriminate; auto; simpl in Hcslisteq; inversion Hcslisteq; subst; auto.
          }
          apply option_bind_ext. intros x.
          rewrite Hsize. reflexivity.
        - f_equal.
          apply forallb_ext.
          intros cs.
          rewrite !amap_mem_spec.
          specialize (Hpops cs).
          destruct (amap_get funsym_eq_dec (fst types_cslist) cs);
          destruct (amap_get funsym_eq_dec (fst types_cslist2) cs);
          auto; contradiction.
      }
      
      (*Now these are the same, so we can proceed by cases*)
      (*Prove that the base is equivalent now, using wilds IH*)
      match goal with
      |- is_true (isSome (option_bind ?o1 ?f1)) -> 
        is_true (isSome (option_bind ?o2 ?f2)) =>
        assert (Hopteq: isSome o1 -> isSome o2); 
        [|destruct o1; destruct o2; try discriminate; auto]
      end.
      {
        destruct no_wilds as [b1|] eqn : hwilds; simpl; auto.
        destruct b1. simpl; auto.
        (*from wilds*)
        destruct (compile constrs match1 let1 vars1 true simpl_constr tms1 wilds);
        simpl in IHwilds |- *;
        destruct (compile _ _ _ _ _ _ _ _); simpl; auto.
      }
      simpl.
      (*Can we convert to [comp_cases]*)
      unfold cases, cslist, types in *.
      (*Don't need generalization anymore*)

      (*Generalize*)
      assert (Hsomenone: forall t1 t2 tms1 P1 tms2 P2 
        (types_cslist1 types_cslist2 : amap funsym (list pattern) * list (funsym * list vty * list pattern)) 
        l l1 l2
        (Hlens: lens_mx P1 P2)
        (Hshape: shape_mx ty_rel P1 P2)
        (Htyslen: length tms1 = length tms2)
        (Htys2: all2 ty_rel (map snd tms1) (map snd tms2))
        (Htms: if simpl_constr then all2 (t_fun_equiv ty_rel) (map fst tms1) (map fst tms2) else true)
        (* (Htys2: map snd tms1 = map snd tms2) *)
        (Hsimpl : simplified P1)
        (Hsimp2: simplified P2)
        (Hpop: populate_all is_constr P1 = Some types_cslist1)
        (Hpop2: populate_all is_constr P2 = Some types_cslist2)
        (Hclisteq: map (fun x => fst (fst x)) (snd types_cslist1) = 
          map (fun x => fst (fst x)) (snd types_cslist2))
        (Hcslist: all2
          (fun x y : funsym * list vty * list pattern =>
          (Datatypes.length (snd (fst x)) =? Datatypes.length (snd (fst y))) &&
          all2 ty_rel (snd (fst x)) (snd (fst y)) &&
          (Datatypes.length (snd x) =? Datatypes.length (snd y)) &&
          all2 (shape_p ty_rel) (snd x) (snd y)) (snd types_cslist1) (snd types_cslist2))
        (Hpops: forall cs, opt_related (fun ps1 ps2 =>
          length ps1 = length ps2 /\ all2 (shape_p ty_rel) ps1 ps2)
          (amap_get funsym_eq_dec (fst types_cslist1) cs)
          (amap_get funsym_eq_dec (fst types_cslist2) cs))
        (*NOTE: *)
        (IHconstrs : forall (cs : funsym) (al1 al2 : list (term * vty))
          l1 l2,
          amap_get funsym_eq_dec (fst (dispatch1 let1 t1 (fst types_cslist1) P1)) cs =
          Some l1 ->
          amap_get funsym_eq_dec (fst (dispatch1 let2 t2 (fst types_cslist2) P2)) cs =
          Some l2 ->
          lens_mx l1 l2 ->
          shape_mx ty_rel l1 l2 ->
          length (rev al1 ++ tms1) = length (rev al2 ++ tms2) ->
          all2 ty_rel (map snd (rev al1 ++ tms1)) (map snd (rev al2 ++ tms2)) ->
          (if simpl_constr then all2 (t_fun_equiv ty_rel) (map fst (rev al1 ++ tms1)) (map fst (rev al2 ++ tms2)) else true) ->
          (* map snd (rev al1 ++ tms1) = map snd (rev al2 ++ tms2) -> *)
          isSome (compile constrs match1 let1 vars1 true simpl_constr (rev al1 ++ tms1)
          l1) -> isSome (compile constrs match2 let2 vars2 true simpl_constr
          (rev al2 ++ tms2) l2)),
        (fold_left_opt
          (add vars1
          (fun (cs : funsym) (al : list (term * vty)) =>
          comp_cases (compile constrs match1 let1 vars1 true simpl_constr)
          (fst (dispatch1 let1 t1 (fst types_cslist1) P1)) tms1 cs al) t1 ty P1 tms1)
          (snd types_cslist1) l) = Some l2 ->
        (fold_left_opt
          (add vars2
          (fun (cs : funsym) (al : list (term * vty)) =>
          comp_cases (compile constrs match2 let2 vars2 true simpl_constr)
          (fst (dispatch1 let2 t2 (fst types_cslist2) P2)) tms2 cs al) t2 ty P2 tms2)
          (snd types_cslist2) l1) <> None
      ).
      {
        clear.
        intros t1 t2 tms1 P1 tms2 P2 types_cslist1 types_cslist2 l l1 l2 Hlens Hshapes
          Htyslen Htys2 Htms Hsimpl Hsimp2 Hpop1 Hpop2 Hcslists Hcslist Hpops IHconstrs Hopt1 Hopt2. 
        apply fold_right_opt_add_map in Hopt1.
        apply fold_left_opt_none in Hopt2.
        destruct Hopt2 as [l3 [x [l5 [ps1 [Hcslist2 [Hopt2 Hadd]]]]]].
        (*Now we prove that [add] is None, contradicting the Some case*)
        assert (Hinx: In x (snd types_cslist2)). {
          rewrite Hcslist2, in_app_iff; simpl; auto.
        }
        (*Now we need to get the term in [snd types_cslist1] corresponding
          to this constructor*)
        (*First get in terms of [fst types_clistX]*)
        destruct x as [[cs2 tys2] ps2].
        assert (Hex: exists tys3 ps3, 
          In (cs2, tys3, ps3) (snd types_cslist1) /\
          length tys2 = length tys3 /\
          all2 ty_rel tys3 tys2 /\
          length ps3 = length ps2 /\ all2 (shape_p ty_rel) ps3 ps2).
        {
          clear -Hcslist Hcslists Hinx.
          generalize dependent (snd types_cslist1).
          induction (snd types_cslist2) as [| h1 t1 IH];
          intros [| h2 t2]; simpl; auto; try contradiction;
          try discriminate.
          intros Hmap; injection Hmap; intros Hmapt Hheq.
          simpl in Hinx.
          destruct h1 as [[cs1 tys1] ps1];
          destruct h2 as [[cs4 tys4] ps4]; simpl in *; subst.
          rewrite all2_cons; simpl.
          unfold is_true; rewrite !andb_true_iff; 
          intros [[[[Hlenty Hallrel] Hlenps] Hallp] Hallt].
          apply Nat.eqb_eq in Hlenty, Hlenps.
          destruct Hinx as [Heq | Hinx]; [inversion Heq; subst|]; auto.
          - exists tys4. exists ps4. split_all; auto.
          - specialize (IH Hinx _ Hmapt Hallt).
            destruct IH as [tys5 [ps5 [Hin [Hlen1 [Hall1 [Hlen2 Hall2]]]]]].
            exists tys5. exists ps5. split_all; auto.
        }
        destruct Hex as [tys3 [ps3 [Hinx2 [Hlentys [Hreltys [Hlenps Hshapeps]]]]]].
        assert (Hget2: amap_get funsym_eq_dec (fst types_cslist2) cs2 = Some ps2).
        {
          rewrite (proj2 (populate_all_fst_snd_full _ _ _ Hsimp2 Hpop2)).
          exists tys2; auto.
        }
        assert (Hget3: amap_get funsym_eq_dec (fst types_cslist1) cs2 = Some ps3).
        {
          rewrite (proj2 (populate_all_fst_snd_full _ _ _ Hsimpl Hpop1)).
          exists tys3; auto.
        }
        assert (Hinx3: In (add_map vars1
          (fun (cs : funsym) (al : list (term * vty)) =>
          comp_cases (compile constrs match1 let1 vars1 true simpl_constr)
          (fst (dispatch1 let1 t1 (fst types_cslist1) P1)) tms1 cs al) t1 ty
          tms1 P1 (cs2, tys3, ps3)) (map (fun x => (fst x, Some (snd x))) l2)).
        {
          rewrite <- Hopt1.
          setoid_rewrite in_app_iff. left.  
          rewrite <- In_rev, in_map_iff.
          exists (cs2, tys3, ps3); split; auto.
        }
        (*Now we will use our contradiction from Hadd*)
        rewrite in_map_iff in Hinx3.
        destruct Hinx3 as [[p1 a1] [Hadd1 Hinpa]].
        simpl in Hadd1. inversion Hadd1; subst; clear Hadd1.
        simpl in Hadd.
        unfold comp_cases in H1, Hadd.
        (*Simplify [amap_get (fst dispatch1)], which is spec (but
        we don't have typing, so we can't quite use that)*)
        rewrite (spec_noty Hsimpl Hpop1 Hinx2) in H1.
        rewrite (spec_noty Hsimp2 Hpop2 Hinx) in Hadd.
        destruct (compile _ _ _ _ _ _ _  (omap _ P2)) as [a2|] eqn : Hcomp;
        [discriminate|].
        (*Now we use the IHconstrs*)
        symmetry in H1.
        (*So we don't have to manually specialize in IH*)
        assert (Hsolve: forall {A B: Type} (o1 : option A) 
          (o2: option B) a1,
          o1 = Some a1 ->
          o2 = None ->
          (isSome o1 -> isSome o2) ->
          False).
        { intros; subst. auto. }
        apply (Hsolve _ _ _ _ _ H1 Hcomp).
        apply IHconstrs with (cs:=cs2); auto. (*Prove IH premises*)
        - apply (spec_noty Hsimpl Hpop1 Hinx2). 
        - apply (spec_noty Hsimp2 Hpop2 Hinx).
        - rewrite Hlenps.
          apply (spec_shape ty_rel); auto. apply ty_rel_refl.
        - rewrite Hlenps.
          apply spec_shape; auto. apply ty_rel_refl.
        - unfold rev_map. solve_len.
        - unfold rev_map. rewrite <- !map_rev, !rev_involutive.
          rewrite !map_app, !map_rev.
          unfold all2.
          unfold vsymbol in *.
          rewrite map2_app by solve_len.
          rewrite forallb_app.
          unfold all2 in Htys2; rewrite Htys2, andb_true_r.
          rewrite map2_rev by solve_len.
          rewrite Hlenps.
          rewrite forallb_rev.
          apply all2_map_snd_combine; [| solve_len].
          apply all2_map_snd_combine; auto; [| solve_len].
          (*Need that [change_rel] preserved by substitutions*)
          apply ty_rel_subst_list; auto. 
        - (*Now prove equivalence of terms for simpl_constr - why we need equality relation*)
          destruct simpl_constr; [|auto].
          unfold rev_map; rewrite !map_rev, !rev_involutive.
          rewrite !map_app, all2_app by solve_len.
          rewrite Htms,andb_true_r.
          rewrite !map_rev, <-all2_rev by solve_len.
          (*We don't know that lengths are equal, use firstn lemma*)
          rewrite! map_fst_combine_eq; simpl_len. rewrite !Nat.min_id.
          rewrite Hlenps.
          apply all2_firstn.
          (*This is easy: they are both variables*)
          apply all2_t_fun_equiv_var.
      }
      (*Now prove other version of IH*)
      assert (IH': forall (cs : funsym) (al1 al2 : list (term * vty)) l2 l3,
        amap_get funsym_eq_dec (fst (dispatch1 let1 t (fst types_cslist) P1)) cs = Some l2 ->
        amap_get funsym_eq_dec (fst (dispatch1 let2 t2 (fst types_cslist2) P2)) cs = Some l3 ->
        lens_mx l2 l3 ->
        shape_mx ty_rel l2 l3 ->
        length (rev al1 ++ tms1) = length (rev al2 ++ tms2) ->
        all2 ty_rel (map snd (rev al1 ++ tms1)) (map snd (rev al2 ++ tms2)) ->
        (if simpl_constr
             then all2 (t_fun_equiv ty_rel) (map fst (rev al1 ++ tms1)) (map fst (rev al2 ++ tms2))
             else true) ->
        isSome (compile constrs match1 let1 vars1 true simpl_constr (rev al1 ++ tms1) l2) ->
        isSome (compile constrs match2 let2 vars2 true simpl_constr (rev al2 ++ tms2) l3)).
      {
        intros cs al1 al2 l2 l3 Hget1 Hget2 Hlens1 Hshape1 Hleneq Hall2 Htms1.
        apply IHconstrs with (cs:=cs); auto.
      }
      (*Now case on [fold_left_opt]*)
      destruct (fold_left_opt _ _ _) as [l1|] eqn : Hopt1; simpl;
      destruct (fold_left_opt _ (snd types_cslist2) _) as [l2|] eqn : Hopt2; simpl; auto.
      specialize (Hsomenone t t2 tms1 P1 tms2 P2 types_cslist types_cslist2 l l0 l1).
      eapply Hsomenone in Hopt1; auto.
      destruct simpl_constr; auto; simpl in Htms; rewrite all2_cons in Htms; apply andb_true_iff in Htms;
      apply Htms.
    }
    (*Now finally we return to case analysis*)
    destruct simpl_constr; [| apply Hcompfull].
    (*Use [t_fun_equiv] to argue that [is_fun t] and [is_fun t2] are related*)
    simpl in Htms. rewrite all2_cons in Htms. apply andb_true_iff in Htms.
    destruct Htms as [Hshapet Htms].
    destruct (is_fun t) as [[ [ [cs params] tms] Ht]| [_ Hnotfun1]];
    destruct (is_fun t2) as [[ [ [cs2 params2] tms2'] Ht2]| [_ Hnotfun]]; subst; simpl in Hshapet.
    2: { destruct t2; try discriminate. exfalso; eapply Hnotfun; reflexivity. }
    2: { destruct t; try discriminate. exfalso; eapply Hnotfun1; reflexivity. }
    2: { apply Hcompfull. }
    (*The only interesting case*)
    simpl. unfold is_constr.
    destruct (funsym_eq_dec cs cs2); [subst|discriminate].
    destruct (f_is_constr cs2 && (is_bare || in_bool funsym_eq_dec cs2 css)) eqn : Hconstr; [| apply Hcompfull].
    (*elements of both [types_cslist] are same*)
    assert (Hmemeq: amap_mem funsym_eq_dec cs2 (fst types_cslist) = amap_mem funsym_eq_dec cs2 (fst types_cslist2)).
    {
      rewrite !amap_mem_spec. destruct Hpops as [_ [_ Hoptrel]].
      specialize (Hoptrel cs2). destruct (amap_get funsym_eq_dec (fst types_cslist) cs2);
      destruct (amap_get funsym_eq_dec (fst types_cslist2) cs2); auto; contradiction.
    }
    rewrite <- Hmemeq.
    destruct (amap_mem funsym_eq_dec cs2 (fst types_cslist)) eqn : Hmem; [| apply IHwilds].
    unfold comp_cases.
    (*Now need to prove that [amap_get] is true in other case*)
    unfold cases. simpl.
    (*Simplify [amap_get (fst dispatch1)], which is spec (but
        we don't have typing, so we can't quite use that)*)
    set (t1:=Tfun cs2 params tms) in *.
    set (P1:=rhd :: rtl) in *.
    (*Get [pats] and [pats2], simplify dispatch*)
    destruct Hpops as [Hmap [Hcslist Hpops]].
    assert (Hpopscs := Hpops cs2).
    rewrite !amap_mem_spec in Hmem, Hmemeq.
    destruct (amap_get funsym_eq_dec (fst types_cslist) cs2) as [pats|] eqn : Hget3; [|discriminate].
    destruct (amap_get funsym_eq_dec (fst types_cslist2) cs2) as [pats2|] eqn : Hget2; [|discriminate]; clear Hmem Hmemeq.
    simpl in Hpopscs. destruct Hpopscs as [Hlenps Hshapeps].
    assert (Hin1: exists tys1, In (cs2, tys1, pats) (snd types_cslist)).
    { apply (populate_all_fst_snd_full _ _ _ Hsimpl Hpop); assumption. }
    assert (Hin2: exists tys2, In (cs2, tys2, pats2) (snd types_cslist2)).
    { apply (populate_all_fst_snd_full _ _ _ Hsimp2 Hpop2); assumption. }
    destruct Hin1 as [tys1 Hincs1]; destruct Hin2 as [tys2 Hincs2].
    (*Now we can rewrite to [spec]*)
    rewrite (spec_noty Hsimpl Hpop Hincs1), (spec_noty Hsimp2 Hpop2 Hincs2). 
    destruct (Nat.eqb_spec (length tms) (length tms2')) as [Hlentms|]; [|discriminate].
    destruct (Nat.eqb_spec (length params) (length params2)); [|discriminate];
    simpl in Hshapet; apply andb_true_iff in Hshapet; destruct Hshapet as [Hallparams Halltms].
    (*For some reason, inner function not simplified*)
    intros Htemp.
    Opaque omap.
    simpl. Transparent omap. revert Htemp.
    (*Now we use the IHconstrs*)
    apply IHconstrs with (cs:=cs2); auto.
    (*Prove IH premises*)
    + apply (spec_noty Hsimpl Hpop Hincs1). 
    + rewrite Hlenps. apply (spec_shape ty_rel); auto. apply ty_rel_refl.
    + rewrite Hlenps.
      apply spec_shape; auto. apply ty_rel_refl.
    + unfold rev_map. solve_len.
    + (*prove ty_rel*) 
      rewrite !map_app, !map_rev,all2_app by solve_len.
      apply andb_true_iff; split; auto.
      rewrite <- all2_rev by solve_len.
      apply all2_map_snd_combine; auto.
      apply ty_rel_subst_list; auto.
    + (*prove tms goal*)
      rewrite !map_app, !map_rev, all2_app by solve_len.
      apply andb_true_iff; split; auto.
      rewrite <- all2_rev by solve_len.
       (*We don't know that lengths are equal, use firstn lemma*)
      rewrite! map_fst_combine_eq,Hlentms. simpl_len.
      apply all2_firstn. auto.
Qed.

(*Corollaries*)

Definition gterm_d b: gen_term b :=
  match b return gen_term b with
  | true => tm_d
  | false => Ftrue
  end.

Lemma compile_bare_single_ext {b1 b2} t1 t2 ty1 ty2 ps1 ps2
  (Hlenps: length ps1 = length ps2)
  (Htys: ty_rel ty1 ty2)
  (Hshapeps: all2 (shape_p ty_rel) (map fst ps1) (map fst ps2)):
  isSome (compile_bare_single b1 false t1 ty1 ps1) ->
  isSome (compile_bare_single b2 false t2 ty2 ps2).
Proof.
  apply compile_change_tm_ps; simpl; auto; try apply gen_getvars_let.
  - (*prove lens_mx*)
    unfold lens_mx; simpl_len. rewrite Hlenps, Nat.eqb_refl. simpl.
    unfold all2.
    rewrite map2_map. simpl.
    apply forallb_forall.
    intros x. rewrite in_map2_iff with (d1:=(Pwild, gterm_d b1))(d2:=(Pwild, gterm_d b2)); auto.
    intros; destruct_all; auto.
  - (*Prove shape_x*) unfold shape_mx, all2.
    rewrite map2_map. simpl.
    apply forallb_forall. intros x. 
    rewrite in_map2_iff with (d1:=(Pwild, gterm_d b1))(d2:=(Pwild, gterm_d b2)); auto.
    intros [i [Hi Hx]].
    unfold all2 in Hshapeps.
    rewrite map2_map in Hshapeps.
    fold (all2 (fun x y => shape_p ty_rel (fst x) (fst y)) ps1 ps2) in Hshapeps.
    rewrite andb_true_r in Hx. subst.
    rewrite all2_forall in Hshapeps; [| auto].
    apply Hshapeps; auto.
  - rewrite !all2_cons, Htys; auto.
Qed.


(*And an even simpler corollary*)
Lemma compile_bare_single_ext_simpl {b1 b2} t1 t2 ty ps1 ps2
  (Hps: map fst ps1 = map fst ps2):
  isSome (compile_bare_single b1 false t1 ty ps1) ->
  isSome (compile_bare_single b2 false t2 ty ps2).
Proof.
  apply compile_bare_single_ext; auto.
  - rewrite <-(map_length fst), Hps,map_length; reflexivity.
  - apply ty_rel_refl.
  - rewrite Hps. clear. induction (map fst ps2); simpl; auto.
    rewrite all2_cons, IHl, shape_p_refl; auto.
    apply ty_rel_refl.
Qed.

(*And a corollary for the simpl_constr case: if the terms are the same,
  we can change the patter matrix under these assumptions*)
(*NOTE: we could just require map fst tms1 = map fst tms2. See if we need*)

Lemma t_fun_equiv_refl (rel: vty -> vty -> bool) (rel_refl: forall v, rel v v) t:
  (t_fun_equiv rel t t).
Proof.
  apply (term_formula_ind (fun t => t_fun_equiv rel t t) (fun f => True)); simpl; auto. 2: apply Ftrue.
  intros f1 tys1 tms1 IH. destruct (funsym_eq_dec _ _); auto; simpl.
  rewrite !Nat.eqb_refl. simpl. apply andb_true_iff. split; [apply all_rel_refl; auto|].
  induction tms1 as [| h tl IH1]; simpl in *; auto.
  rewrite all2_cons. inversion IH; subst.
  apply andb_true_iff; split; auto.
Qed.

Lemma compile_simpl_constr_change_ps {A B: Type} {constrs match1 match2
  let1 let2 vars1 vars2 tms} 
  {P1: list (list pattern * A)} {P2: list (list pattern * B)}
  (Hlet1: forall (v : vsymbol) (tm : term) (a : A) (x : vsymbol),
    In x (vars1 (let1 v tm a)) <-> v = x \/ In x (tm_bnd tm) \/ In x (tm_fv tm) \/ In x
    (vars1 a))
  (Hlet2: forall (v : vsymbol) (tm : term) (a : B) (x : vsymbol),
    In x (vars2 (let2 v tm a)) <-> v = x \/ In x (tm_bnd tm) \/ In x (tm_fv tm) \/ In x
    (vars2 a))
  (Hlens: lens_mx P1 P2)
  (Hshape: shape_mx ty_rel P1 P2):
  (*NOTE: not proving equality anymore -
    but in some cases, can still get equality*)
  isSome (compile constrs match1 let1 vars1 true true tms P1) ->
  isSome (compile constrs match2 let2 vars2 true true tms P2).
Proof.
  apply compile_change_tm_ps; auto.
  - apply all_rel_refl. apply ty_rel_refl.
  - clear. induction (map fst tms) as [| h t IH]; auto. rewrite all2_cons. rewrite t_fun_equiv_refl; auto.
    apply ty_rel_refl.
Qed.


(*Now we give a context-insensitive version of pattern matching
  compilation ([compile_bare]). In real Why3, there are 2 differences:
  1. [compile_bare] does not compute the missing patterns. We ignore
    this entirely, so this is not a change
  2. When checking exhaustiveness, Why3 uses a trivial 
    mk_let and mk_match that return unit. Because we need to deal
    with free variables, we cannot quite do the same. So we
    construct the necessary terms, which is still cheap*)

(*Note that we proved above that the same spec holds
  with or without [bare]. What remains is to show that
  if [bare] is true, we can completely ignore [get_constructors]
  and thus we can pass in a trivial, context-free function*)

(*Provable by [reflexivity] because bare and get_constructors
  defined outside of the Fixpoint*)
Lemma compile_bare_equiv {A: Type} constr1 constr2 
  (gen_match: term -> vty -> list (pattern * A) -> A)
  gen_let gen_getvars simpl_constr tms P:
  compile constr1 gen_match gen_let gen_getvars true simpl_constr tms P =
  compile constr2 gen_match gen_let gen_getvars true simpl_constr tms P.
Proof.
  reflexivity.
Qed.

Corollary compile_bare_spec {gamma: context} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
  (pf: pi_funpred gamma_valid pd pdf) (vt: val_typevar) (v: val_vars pd vt)
  (b: bool) (ret_ty: gen_type b) tms P
  (Htys: Forall2 (term_has_type gamma) (map fst tms) (map snd tms))
  (Hp: pat_matrix_typed b ret_ty (map snd tms) P)
  (Hdisj: pat_matrix_var_names_disj b (map fst tms) P) t
  (Hty: gen_typed gamma b t ret_ty)
  (simpl_constr: bool):
  compile_bare b simpl_constr tms P = Some t ->
  matches_matrix_tms gamma_valid b ret_ty pd pdf pf vt v (map fst tms) (map snd tms) P Htys Hp = 
  Some (gen_rep gamma_valid pd pdf pf vt v ret_ty t Hty).
Proof.
  unfold compile_bare. erewrite compile_bare_equiv.
  apply compile_rep. auto.
Qed.

Corollary compile_bare_typed {gamma: context} (gamma_valid: valid_context gamma)
  (b: bool) (ret_ty: gen_type b) tms P
  (Htys: Forall2 (term_has_type gamma) (map fst tms) (map snd tms))
  (Hp: @pat_matrix_typed gamma b ret_ty (map snd tms) P) t
  (simpl_constr: bool):
  compile_bare b simpl_constr tms P = Some t ->
  gen_typed gamma b t ret_ty.
Proof.
  unfold compile_bare. erewrite compile_bare_equiv. 
  eapply compile_typed; eauto.
Qed.

(*And the single versions*)

(*Option version of [match_rep]*)
Definition match_rep_opt {gamma} (gamma_valid: valid_context gamma) 
  (b: bool) pd pdf pf vt v (ty: gen_type b) ty1 dom_t :=
  fix match_rep (ps: list (pattern * (gen_term b)))
    (Hps: Forall (fun x => pattern_has_type gamma (fst x) ty1) ps)
    (Hall: Forall (fun x => gen_typed gamma b (snd x) ty) ps) :
      option (gen_ret pd vt b ty) :=
    match ps as l' return
      Forall (fun x => pattern_has_type gamma (fst x) ty1) l' ->
      Forall (fun x => gen_typed gamma b (snd x) ty) l' ->
      option (gen_ret pd vt b ty) with
    | (p , dat) :: ptl => fun Hpats Hall =>
      match (match_val_single gamma_valid pd pdf vt ty1 p (Forall_inv Hpats) dom_t) with
      | Some l => 
          Some (gen_rep gamma_valid pd pdf pf vt (extend_val_with_list pd vt v l) ty dat (Forall_inv Hall))
      | None => match_rep ptl (Forall_inv_tail Hpats) (Forall_inv_tail Hall)
      end
    | _ => fun _ _ => None
    end Hps Hall .

Lemma match_rep_opt_some {gamma} (gamma_valid: valid_context gamma) b
  pd pdf pf vt v ty ty1 dom_t ps Hps1 Hps2 a:
  match_rep_opt gamma_valid b pd pdf pf vt v ty ty1 dom_t ps Hps1 Hps2 = Some a ->
  a = match_rep gamma_valid pd pdf vt v 
    (term_rep gamma_valid pd pdf vt pf) (formula_rep gamma_valid pd pdf vt pf) b ty ty1 dom_t ps Hps1 Hps2.
Proof.
  induction ps as [| [p d] tl IH]; simpl; auto; [discriminate|].
  destruct_match_single l Hmatch; auto.
  inv Hsome. destruct b; simpl; auto.
Qed.

Lemma match_rep_opt_equiv {gamma} (gamma_valid: valid_context gamma) b ret_ty
  pd pdf pf vt v t ty Hty ps Hps1 Hps2 Htys Hp:
  matches_matrix_tms gamma_valid b ret_ty pd pdf pf vt v [t] [ty]
    (map (fun x => ([fst x], snd x)) ps) Htys Hp =
  match_rep_opt gamma_valid b pd pdf pf vt v ret_ty ty
    (term_rep gamma_valid pd pdf vt pf v t ty Hty) ps Hps1 Hps2.
Proof.
  unfold matches_matrix_tms.
  induction ps as [|[p d] tl IH]; simpl; simp terms_to_hlist; simp matches_matrix; auto.
  simp matches_row. simpl. simp matches_row.
  simpl hlist_hd.
  rewrite match_val_single_irrel with (Hval2:=(Forall_inv Hps1)).
  rewrite term_rep_irrel with (Hty2:=Hty). simpl.
  destruct_match_single l Hmatch; auto.
  - rewrite app_nil_r. f_equal. apply gen_rep_irrel.
  - simp matches_matrix. erewrite <- IH.
    f_equal. simp terms_to_hlist. simpl.
    erewrite term_rep_irrel. reflexivity.
Qed.

Corollary compile_bare_single_spec1 {gamma: context} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
  (pf: pi_funpred gamma_valid pd pdf) (vt: val_typevar) (v: val_vars pd vt)
  (b: bool) (ret_ty: gen_type b) (t: term) (ty: vty)
  (ps: list (pattern * gen_term b))
  (Hty: term_has_type gamma t ty)
  (Htyps1: Forall (fun p => pattern_has_type gamma (fst p) ty) ps)
  (Htyps2: Forall (fun t => gen_typed gamma b (snd t) ret_ty) ps)
  (Hdisj: disj (map fst (tm_fv t)) (map fst (big_union vsymbol_eq_dec pat_fv (map fst ps)))) 
  tm
  (Htym: gen_typed gamma b tm ret_ty)
  (simpl_constr: bool):
  compile_bare_single b simpl_constr t ty ps = Some tm ->
  match_rep_opt gamma_valid b pd pdf pf vt v ret_ty ty 
      (term_rep gamma_valid pd pdf vt pf v t ty Hty) ps Htyps1 Htyps2 =
  Some (gen_rep gamma_valid pd pdf pf vt v ret_ty tm Htym).
Proof.
  unfold compile_bare_single.
  intros Hcomp.
  assert (Hall1: Forall2 (term_has_type gamma) (map fst [(t, ty)]) (map snd [(t, ty)])).
  { constructor; auto. }
  assert (Hmx: @pat_matrix_typed gamma b ret_ty (map snd [(t, ty)])
    (map (fun x : pattern * gen_term b => ([fst x], snd x)) ps)).
  { apply compile_bare_single_pat_typed; rewrite Forall_map; auto. }
  
  eapply compile_bare_spec with (gamma_valid:=gamma_valid)
    (pd:=pd)(pdf:=pdf)(pf:=pf)(vt:=vt)(v:=v)(ret_ty:=ret_ty)(Htys:=Hall1)
    (Hp:=Hmx)(Hty:=Htym) in Hcomp.
  - simpl in Hcomp. rewrite (match_rep_opt_equiv) with (Hty:=Hty)
      (Hps1:=Htyps1)(Hps2:=Htyps2) in Hcomp.
    assumption.
  - simpl. clear -Hdisj.
    (*Prove disjoint*)
    intros x [Hinx1 Hinx2].
    rewrite in_map_iff in Hinx1, Hinx2.
    destruct Hinx1 as [[n1 ty1] [Hx Hinx1]]; subst.
    destruct Hinx2 as [[n2 ty2] [Hx Hinx2]]; simpl in Hx; subst.
    unfold pat_mx_fv in Hinx2. simpl_set.
    destruct Hinx1 as [Hinx1 | []].
    destruct Hinx2 as [y [Hiny Hinx2]].
    rewrite in_map_iff in Hiny.
    destruct Hiny as [[p gt] [Hy Hinpg]]; simpl in Hy; subst.
    unfold row_fv in Hinx2.
    simpl_set. destruct Hinx2 as [p2 [Hinp2 Hinx2]].
    destruct Hinp2 as [Hp | []]; subst.
    apply (Hdisj n1). rewrite !in_map_iff.
    split.
    + eexists; split; [|apply Hinx1]; reflexivity.
    + exists (n1, ty2). split; auto. simpl_set.
      exists p2. split; auto. rewrite in_map_iff. 
      eexists; split; [| apply Hinpg]; reflexivity.
Qed.

(*And the version that relates to [match_rep] directly*)
Corollary compile_bare_single_spec2 {gamma: context} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
  (pf: pi_funpred gamma_valid pd pdf) (vt: val_typevar) (v: val_vars pd vt)
  (b: bool) (ret_ty: gen_type b) (t: term) (ty: vty)
  (ps: list (pattern * gen_term b))
  (Hty: term_has_type gamma t ty)
  (Htyps1: Forall (fun p => pattern_has_type gamma (fst p) ty) ps)
  (Htyps2: Forall (fun t => gen_typed gamma b (snd t) ret_ty) ps)
  (Hdisj: disj (map fst (tm_fv t)) (map fst (big_union vsymbol_eq_dec pat_fv (map fst ps)))) 
  tm
  (Htym: gen_typed gamma b tm ret_ty)
  (simpl_constr: bool):
  compile_bare_single b simpl_constr t ty ps = Some tm ->
  match_rep gamma_valid pd pdf vt v (term_rep gamma_valid pd pdf vt pf)
    (formula_rep gamma_valid pd pdf vt pf) b ret_ty ty 
      (term_rep gamma_valid pd pdf vt pf v t ty Hty) ps Htyps1 Htyps2 =
  gen_rep gamma_valid pd pdf pf vt v ret_ty tm Htym.
Proof.
  intros Hcomp.
  eapply compile_bare_single_spec1 in Hcomp; eauto.
  eapply match_rep_opt_some in Hcomp.
  symmetry. apply Hcomp.
Qed. 

(*Typing*)
Corollary compile_bare_single_typed {gamma: context} (gamma_valid: valid_context gamma)
  (b: bool) (ret_ty: gen_type b) (t: term) (ty: vty)
  (ps: list (pattern * gen_term b))
  (Hty: term_has_type gamma t ty)
  (Htyps1: Forall (fun p => pattern_has_type gamma (fst p) ty) ps)
  (Htyps2: Forall (fun t => gen_typed gamma b (snd t) ret_ty) ps)
  tm (simpl_constr: bool) 
  (Hcomp: compile_bare_single b simpl_constr t ty ps = Some tm):
  gen_typed gamma b tm ret_ty.
Proof.
  unfold compile_bare_single in Hcomp.
  eapply compile_bare_typed in Hcomp; eauto.
  - constructor; auto.
  - apply compile_bare_single_pat_typed; rewrite Forall_map; auto.
Qed.

(*Reason about type variables*)

Definition pat_mx_type_vars {b} (P: list (list pattern * gen_term b)) : list typevar :=
  big_union typevar_eq_dec (fun x => union typevar_eq_dec
    (big_union typevar_eq_dec pat_type_vars (fst x))
    (gen_type_vars (snd x))) P.

Definition tm_list_type_vars (tm: list (term * vty)) : list typevar :=
  big_union typevar_eq_dec (fun x => union typevar_eq_dec (tm_type_vars (fst x)) (type_vars (snd x))) tm.

Lemma pat_mx_type_vars_simp b t (P: list (list pattern * gen_term b)):
  forall x, In x (pat_mx_type_vars (simplify gen_let t P)) -> In x (pat_mx_type_vars P) \/ In x (tm_type_vars t).
Proof.
  intros x. unfold simplify. induction P as [| rhd rtl IH]; simpl; auto.
  unfold pat_mx_type_vars in IH |- *. rewrite big_union_app. simpl_set_small.
  intros [Hin | Hin]; auto.
  2: { apply IH in Hin. destruct Hin as [Hin | Hin]; auto. }
  clear IH.
  assert (Hhd: (In x (big_union typevar_eq_dec pat_type_vars (fst rhd)) \/ 
    In x (gen_type_vars (snd rhd)) \/ In x (tm_type_vars t)));
  [|destruct_all; auto].
  unfold simplify_single in Hin.
  destruct rhd as [ps a]. simpl in *. destruct ps as [| phd ptl]; simpl in *.
  { simpl_set. destruct Hin as [Hin | []]. auto. }
  simpl_set_small. generalize dependent a.
  induction phd; simpl in *; intros; auto; simpl_set_small; try (destruct Hin as [Hin | []]);
  try solve[repeat (simpl_set_small; auto; progress(destruct_all); auto)]; simpl.
  - simpl_set_small. rewrite gen_type_vars_let in Hin.
    repeat (destruct_all; simpl_set_small; auto).
  - (*Por inductive*)
    rewrite map_app, big_union_app in Hin.
    simpl_set_small.
    destruct Hin as [Hin1 | Hin2].
    + apply IHphd1 in Hin1.
      destruct_all; auto.
    + apply IHphd2 in Hin2; destruct_all; auto.
  - simpl_set_small. apply IHphd in Hin.
    rewrite gen_type_vars_let in Hin. 
    repeat (destruct_all; simpl_set_small; auto).
Qed. 

Lemma pat_mx_type_vars_default {b} (P: list (list pattern * gen_term b)):
  sublist (pat_mx_type_vars (default P)) (pat_mx_type_vars P).
Proof.
  induction P as [| [ps a] rtl]; simpl; [apply sublist_refl|].
  destruct ps as [| phd ptl]; simpl.
  - eapply sublist_trans. apply IHrtl. apply union_sublist_r.
  - destruct phd; try solve[eapply sublist_trans; [apply IHrtl | apply union_sublist_r]].
    simpl. apply sublist_union; auto.
    apply sublist_refl.
Qed.

Lemma pat_mx_type_vars_spec {b} n cs rl:
  sublist (pat_mx_type_vars
    (omap
      (fun x : list pattern * gen_term b =>
      match fst x with
      | Pconstr fs _ pats :: ps =>
      if funsym_eqb fs cs then Some (rev pats ++ ps, snd x) else None
      | Pwild :: ps => Some (repeat Pwild n ++ ps, snd x)
      | _ => None
      end) rl)) (pat_mx_type_vars rl).
Proof.
  induction rl as [| [ps a] rtl IH]; simpl; [apply sublist_refl|].
  destruct ps as [| phd ptl]; simpl; auto.
  - eapply sublist_trans. apply IH. apply union_sublist_r.
  - destruct phd as [| f1 tys1 ps1 | | |]; try solve[eapply sublist_trans; [apply IH | apply union_sublist_r]].
    + (*funsym case*)
      destruct (funsym_eqb_spec f1 cs); [| solve[eapply sublist_trans; [apply IH | apply union_sublist_r]]].
      subst. simpl.
      intros x Hinx. unfold sublist in IH. simpl_set_small.
      destruct Hinx as [Hinx | Hinx]; auto.
      simpl_set_small. destruct Hinx as [Hinx | Hinx]; auto.
      rewrite big_union_app in Hinx. simpl_set_small.
      destruct Hinx as [Hinx | Hinx]; auto.
      rewrite big_union_rev in Hinx. auto.
    + (*wild case*)
      simpl. intros x Hinx. unfold sublist in IH. simpl_set_small.
      destruct Hinx as [Hinx | Hinx]; auto.
      simpl_set_small. destruct Hinx as [Hinx | Hinx]; auto.
      rewrite big_union_app in Hinx. simpl_set_small.
      destruct Hinx as [Hinx | Hinx]; auto.
      (*Pwild has no vars*)
      apply big_union_repeat in Hinx. contradiction.
Qed.


Opaque dispatch1_opt.
Opaque dispatch1.
Lemma compile_bare_type_vars (b: bool) (simpl_constr: bool) (tms: list (term * vty))
  (P: list (list pattern * gen_term b)) t:
  compile_bare b simpl_constr tms P = Some t ->
  sublist (gen_type_vars t) (union typevar_eq_dec (tm_list_type_vars tms) (pat_mx_type_vars P)).
Proof.
  intros Hcomp. assert (Ht: True) by auto; revert t Ht Hcomp. unfold compile_bare.
  apply (compile_prove_some _ gen_match gen_let gen_getvars gen_getvars_let
    true simpl_constr (fun tms P => True)
    (fun tms P t =>  sublist (gen_type_vars t) (union typevar_eq_dec (tm_list_type_vars tms) (pat_mx_type_vars P)))); 
  clear tms P.
  - (*simplify*)
    intros. specialize (Hsimpl _ (ltac:(auto)) Hcomp).
    intros x Hinx.
    specialize (Hsimpl _ Hinx).
    simpl_set_small.
    destruct Hsimpl as [Hin | Hin]; auto.
    apply pat_mx_type_vars_simp in Hin.
    destruct Hin as [Hin | Hin]; auto.
    simpl. simpl_set_small; auto.
  - (*nil case*)
    intros ps a l _. simpl.
    eapply sublist_trans.
    2: apply union_sublist_l.
    apply union_sublist_r.
  - (*default*)
    intros. apply IHwilds in Hmt1; auto.
    eapply sublist_trans; [apply Hmt1|].
    apply sublist_union.
    + apply union_sublist_r.
    + eapply sublist_trans; [ apply pat_mx_type_vars_default| apply sublist_refl].
  - (*full*)
    intros.
    eapply sublist_iff_l.
    { intros x. symmetry. apply gen_type_vars_match. }
    (*Now proceed by cases*)
    intros x Hinx.
    (*An easier formulation*)
    assert (Hinx': In x (union typevar_eq_dec (union typevar_eq_dec (tm_type_vars t) (type_vars ty))
      (union typevar_eq_dec (big_union typevar_eq_dec pat_type_vars (map fst ps))
        (big_union typevar_eq_dec gen_type_vars (map snd ps))))).
    { simpl_set_small. destruct Hinx; simpl_set_small; destruct_all; auto. }
    clear Hinx.
    simpl_set_small. simpl.
    destruct Hinx' as [Hinx | Hinx]; simpl_set_small; auto.
    assert (Hinx': In x (big_union typevar_eq_dec (fun x => union typevar_eq_dec (pat_type_vars (fst x)) (gen_type_vars (snd x))) ps)).
    {
      simpl_set. destruct Hinx as [Hinx | Hinx]; simpl_set; destruct Hinx as [y [Hiny Hinx]];
      rewrite in_map_iff in Hiny; destruct Hiny as [z [Hz Hinz]]; subst; exists z; split; auto;
      simpl_set_small; auto.
    }
    clear Hinx.
    (*Now get element of ps we are interested in*)
    rewrite <- big_union_elts in Hinx'.
    destruct Hinx' as [yt [Hinyt Hinx]].
    (*Get element, relate it to ps1 and cslist*)
    destruct (In_nth _ _ (Pwild, gen_d _) Hinyt) as [n [Hn Hyt]].
    pose proof (f_equal (fun x => nth n x (Pwild, Some (gen_d b))) Hopt)
      as Hntheq.
    simpl in Hntheq.
    revert Hntheq.
    (*Simplify this*)
    rewrite map_nth_inbound with (d2:=(Pwild, gen_d b)) by auto.
    rewrite Hyt.
    assert (Hn1: n < length cslist \/ n >= length cslist) by lia.
    assert (Hlen: length ps = length ps1 + length cslist).
    { apply (f_equal (@length _)) in Hopt. revert Hopt. solve_len. }
    destruct Hn1 as [Hn1 | Hn1].
    2: { (*Second case (wilds) is easier*)
      rewrite app_nth2; simpl_len; [|lia].
      destruct Hps1' as [[Hps1eq Hiswilds] | [Hiswilds [t2 [Hcompw Hps1eq]]]]; subst ps1; simpl in *; try lia.
      assert (Hn': n = length cslist) by lia.
      rewrite Hn' at 1. rewrite Nat.sub_diag. simpl.
      destruct yt as [y1 t1]. simpl. intros Heq; inversion Heq; subst y1 t1; clear Heq.
      (*Use wilds result*)
      apply IHwilds in Hcompw; auto.
      simpl in Hinx. apply Hcompw in Hinx.
      simpl_set_small. destruct Hinx as [Hinx | Hinx]; auto.
      apply pat_mx_type_vars_default in Hinx. auto.
    }
    (*Constr case is harder*)
    rewrite app_nth1 by solve_len.
    rewrite rev_nth; simpl_len; [| lia].
    erewrite map_nth_inbound with (d2:=(id_fs, nil, nil)); try lia.
    destruct ( nth (Datatypes.length cslist - S n) cslist (id_fs, [], []))
      as [[cs tys] pats] eqn : Hnth.
    simpl.
    unfold rev_map. rewrite !map_rev, !rev_involutive.
    destruct yt as [y1 t1]. simpl in Hinx |- *.
    intros Heq. injection Heq. intros Hcompcase Hconstr. clear Heq.
    unfold comp_cases in Hcompcase.
    assert (Hincs: In (cs, tys, pats) cslist). {
      rewrite <- Hnth.
      apply nth_In. lia.
    }
    (*Rewrite to [spec]*)
    revert Hcompcase. unfold cases. rewrite Hcasewild.
    rewrite (spec_noty Hsimpl Hpop Hincs). intros.
    apply IHconstrs with(cs:=cs) in Hcompcase; auto; [| unfold cases; rewrite Hcasewild; apply (spec_noty Hsimpl Hpop Hincs)].
    (*Need to know that if in tys, we are OK*)
    (*If in tys, in pat matrix because (cs, tys, ps) is in matrix*)
    assert (Htys: forall x, In x (big_union typevar_eq_dec type_vars tys) ->
      In x (pat_mx_type_vars rl)).
    {
      intros x' Hinx'.
      unfold cslist in Hincs.
      apply (populate_all_snd_strong _ _ _ _ _ _ Hsimpl Hpop) in Hincs.
      assert (In x' (pat_mx_type_vars rl)); [|auto].
      unfold pat_mx_type_vars.
      apply existsb_exists in Hincs.
      destruct Hincs as [row [Hinrow Hconstrargs]].
      rewrite <- big_union_elts. exists row. split; auto.
      unfold constr_args_at_head_strong in Hconstrargs.
      destruct row as [r1 r2]; simpl in Hconstrargs |- *.
      destruct r1 as [| phd ptl]; [discriminate|].
      destruct phd as [| f1 tys1 pats1 | | |]; try solve[discriminate].
      simpl. simpl_set_small.
      destruct (funsym_eqb_spec f1 cs); [|discriminate].
      destruct (list_eqb_spec _ vty_eq_spec tys tys1); [|discriminate].
      subst.
      auto.
    }
    assert (Hsubst: forall x (v: vsymbol),
        In (snd v) (map (ty_subst (s_params cs) tys) (s_args cs)) ->
        In x (type_vars (snd v)) ->
        In x (pat_mx_type_vars rl)).
    {
      intros x' v' Hinv' Hinx'.
      rewrite in_map_iff in Hinv'.
      destruct Hinv' as [ty1 [Hsndv Hinty1]].
      rewrite <- Hsndv in Hinx'.
      apply ty_subst_type_vars in Hinx'.
      (*From previous result*)
      auto.
    }
    (*Now case on where x is*)
    simpl_set_small. destruct Hinx as [Hinx | Hinx].
    + (*Case 1: x in resulting pattern*)
      rewrite <- Hconstr in Hinx. simpl in Hinx.
      simpl_set.
      (*First case already did, otherwise in pat vars*)
      destruct Hinx as [Hinx | Hinx]; auto.
      simpl_set.
      destruct Hinx as [p [Hinp Hinx]].
      rewrite in_map_iff in Hinp.
      destruct Hinp as [v [Hp Hinv]]; subst p.
      simpl in Hinx.
      apply in_combine_snd in Hinv.
      (*Use subst case we proved*)
      specialize (Hsubst _ _ Hinv Hinx). auto.
    + (*Case 2: In vars of t1 - use IH*)
      apply Hcompcase in Hinx.
      simpl_set_small. destruct Hinx as [Hinx | Hinx].
      * (*Case 1: in new terms - either old terms or new variables*)
        unfold tm_list_type_vars in Hinx.
        simpl_set.
        destruct Hinx as [[t2 ty2] [Hintty2 Hinx]].
        rewrite in_app_iff in Hintty2.
        destruct Hintty2 as [Hintty2 | Hintty2].
        2: {
          (*Easier: in tl (not newly added)*)
          left. right. unfold tm_list_type_vars.
          simpl_set. exists (t2, ty2). split; auto.
          simpl_set; auto.
        }
        rewrite <- In_rev in Hintty2.
        simpl in Hinx.
        assert (Hint2:=Hintty2).
        assert (Hinty2 := Hintty2).
        apply in_combine_r in Hinty2.
        apply in_combine_l in Hint2.
        (*Now case*)
        simpl_set_small; destruct Hinx as [Hinx | Hinx].
        -- (*Case 1: in term type vars*)
          rewrite in_map_iff in Hint2.
          destruct Hint2 as [v [Hv Hinv]].
          subst t2. simpl in Hinx.
          apply in_combine_snd in Hinv.
          (*Again, subst lemma*)
          specialize (Hsubst _ _ Hinv Hinx). auto.
        -- (*Case 2: in type vars*)
          rewrite in_map_iff in Hinty2.
          destruct Hinty2 as [v [Hty2 Hinv]]; subst ty2.
          simpl in Hinx. apply in_combine_snd in Hinv.
          (*Also subst case*)
          specialize (Hsubst _ _ Hinv Hinx). auto.
      * (*In spec type vars*)
        apply pat_mx_type_vars_spec in Hinx. auto.
  - (*Tfun case*)
    intros. revert Hcomp.
    unfold comp_cases.
    (*First, rewrite with spec*)
    rewrite amap_mem_spec in Hmem.
    destruct (amap_get funsym_eq_dec types cs) as [pats|] eqn : Htypes; [|discriminate].
    assert (Hin: exists tys, In (cs, tys, pats) cslist).
    { unfold cslist. apply (proj2 (populate_all_fst_snd_full _ _ _ Hsimpl Hpop)); assumption. }
    destruct Hin as [tys Hincs].
    unfold cases. rewrite Hcasewild.
    rewrite (spec_noty Hsimpl Hpop Hincs). intros Hcomp.
    apply (IHconstrs cs) in Hcomp; auto; [| unfold cases; rewrite Hcasewild; apply (spec_noty Hsimpl Hpop Hincs)].
    (*And now sublist goals*)
    eapply sublist_trans; [apply Hcomp|]; clear Hcomp.
    intros x Hinx. simpl_set_small.
    unfold tm_list_type_vars in Hinx.
    rewrite big_union_app in Hinx.
    destruct Hinx as [Hinx | Hinx]; [| apply pat_mx_type_vars_spec in Hinx; auto]. (*spec result*)
    simpl_set_small.
    rewrite big_union_rev in Hinx.
     assert (Htys: forall x, In x (big_union typevar_eq_dec type_vars params) ->
      In x (tm_type_vars t)).
    {
      subst. simpl. intros x1 Hinx1. simpl_set_small; auto.
    }
    assert (Hsubst: forall x (ty: vty),
        In ty (map (ty_subst (s_params cs) params) (s_args cs)) ->
        In x (type_vars ty) ->
        In x (tm_type_vars t)).
    {
      intros x' v' Hinv' Hinx'.
      rewrite in_map_iff in Hinv'.
      destruct Hinv' as [ty1 [Hsndv Hinty1]].
      rewrite <- Hsndv in Hinx'.
      apply ty_subst_type_vars in Hinx'.
      (*From previous result*)
      auto.
    }
    simpl. unfold tm_list_type_vars. simpl_set_small.
    (*First case already did, otherwise in pat vars*)
    destruct Hinx as [Hinx | Hinx]; auto.
    simpl_set.
    (*Case in new terms - either old terms or new variables*)
    unfold tm_list_type_vars in Hinx.
    simpl_set.
    destruct Hinx as [[t2 ty2] [Hintty2 Hinx]].
    simpl in Hinx.
    assert (Hint2:=Hintty2).
    assert (Hinty2 := Hintty2).
    apply in_combine_r in Hinty2.
    apply in_combine_l in Hint2.
    (*Now case*)
    left. left. left.
    simpl_set_small; destruct Hinx as [Hinx | Hinx].
    -- (*Case 1: in term type vars*)
      subst. simpl. simpl_set_small. right.
      simpl_set. exists t2; auto.
    -- (*Case 2: in type vars*) eauto.
Qed.

(*Free variables*)

(*Reason about free variables - all free variables in the result
  are in the original term matrix actions, but NOT in the pattern
  matrix*)
(*Don't think we need full generality here*)

(*Term vars of a pat matrix*)
Definition pat_mx_tm_fv b (P: list (list pattern * gen_term b)): list vsymbol :=
  (big_union vsymbol_eq_dec
    (fun x => remove_all vsymbol_eq_dec (row_fv x) (gen_fv (snd x))) P).

(*for this to be to true, need well-typed patterns.
  In Por case: if p1 and p2 do not have the same vars, can have free in 1 but not other
  Example: (Por x y) and we have term x. x is not free in whole term
  But when we split x -> x and y -> x, x free in 2nd 
*)
(*Maybe don't need whole thing, just need well-type wrt SOME type*)
Lemma pat_mx_tm_fv_simp gamma b ret_ty t tys P
  (Hp: @pat_matrix_typed gamma b ret_ty tys P):
  forall x, In x (pat_mx_tm_fv b (simplify gen_let t P)) -> In x (pat_mx_tm_fv b P) \/ In x (tm_fv t).
Proof.
  intros x. unfold simplify. induction P as [| rhd rtl IH]; simpl; auto.
  unfold pat_mx_tm_fv in IH |- *. rewrite big_union_app. simpl_set_small.
  specialize (IH (pat_matrix_typed_tail _ _ Hp)).
  intros [Hin | Hin]; auto.
  2: { apply IH in Hin. destruct Hin as [Hin | Hin]; auto. }
  clear IH.
  assert (Hhd: (In x (gen_fv (snd rhd)) /\ ~ In x (row_fv rhd)) \/ In x (tm_fv t)); [| destruct_all; auto].
  unfold simplify_single in Hin.
  destruct rhd as [ps a]. simpl in *. destruct ps as [| phd ptl]; simpl in *.
  { simpl_set. destruct Hin as [Hin | []]. auto. }
  unfold row_fv in *. simpl. simpl_set_small.
  pose proof (pat_matrix_typed_head _ _ Hp) as [Hty _]. clear Hp.
  simpl in Hty. (*All we need is that phd has pattern type*)
  inversion Hty as [|? ty1 ? ? Hty1 Hty2]; subst. clear Hty2 Hty.
  generalize dependent ty1.
  generalize dependent a.
  induction phd; simpl in *; auto; intros; simpl_set_small.
  - (*Pvar a bit complicated*) destruct Hin as [Hin | []].
    simpl_set_small. rewrite gen_let_fv in Hin.
    destruct Hin as [Hin1 Hin2].
    simpl_set_small.
    destruct Hin1 as [Hin1 | Hin1]; auto.
    simpl_set_small. destruct Hin1 as [Hin1 Hxv]; left; auto. split; auto.
    intros [Heq | Hbig]; subst; contradiction.
  - (*Constr is easy*) destruct Hin as [Hin | []].
    simpl_set_small.
    destruct Hin as [Hina Hinx].
    simpl_set_small. auto.
  - (*Pwild*) destruct Hin as [Hin | []]; simpl_set_small; auto.
    destruct Hin as [Hina Hnotin].
    left; split; auto.
    intros [[] | Hinx]; contradiction.
  - (*Por inductive case*)
    rewrite map_app in Hin.
    rewrite big_union_app in Hin. simpl_set_small.
    inversion Hty1; subst; auto.
    destruct Hin as [Hin1 | Hin2].
    + (*NOTE: this is where we need the typing assumption - need 
        that freevars are the same*)  
      apply IHphd1 with (ty1:=ty1) in Hin1; auto.
      rewrite <- H5. rewrite or_idem. destruct_all; auto.
    + apply IHphd2 with (ty1:=ty1) in Hin2; auto.
      rewrite H5, or_idem. destruct_all; auto.
  - inversion Hty1; subst. apply IHphd with (ty1:=(snd v)) in Hin ; auto.
    rewrite gen_let_fv in Hin.
    destruct Hin as [Hin | Hin]; auto.
    destruct Hin as [Hin1 Hin2]; auto.
    simpl_set_small.
    destruct Hin1 as [Hin1 | Hin1]; auto.
    simpl_set_small.
    left. destruct Hin1 as [Hin1 Hxv]. split; auto.
    intro C; destruct_all; subst; try contradiction; apply Hin2; auto.
Qed.

Lemma pat_mx_tv_fv_default b rl:
  sublist (pat_mx_tm_fv b (default rl)) (pat_mx_tm_fv b rl).
Proof.
  induction rl as [| [ps a] rtl IH]; simpl; [apply sublist_refl|].
  destruct ps as [| phd ptl]; simpl;
  [eapply sublist_trans; [apply IH | apply union_sublist_r]|].
  destruct phd; try solve[eapply sublist_trans; [apply IH | apply union_sublist_r]].
  simpl. intros x Hinx. simpl_set_small.
  destruct Hinx as [Hinx | ?]; auto.
  simpl_set_small.
  unfold row_fv in *. simpl in *. auto.
Qed.

Lemma pat_mx_tv_fv_spec b rl cs:
  sublist (pat_mx_tm_fv b (spec b rl cs)) (pat_mx_tm_fv b rl).
Proof.
  induction rl as [|[ps a] rtl IH]; simpl; [apply sublist_refl|].
  destruct ps as [| phd ptl]; [apply (sublist_trans _ _ _ IH),
    union_sublist_r|].
  destruct phd as [| f1 tys1 ps1 | | |]; try solve[apply (sublist_trans _ _ _ IH), union_sublist_r].
  - (*constr case*)
    destruct (funsym_eqb_spec f1 cs); [| apply (sublist_trans _ _ _ IH), union_sublist_r].
    simpl. unfold row_fv; simpl. 
    intros x Hinx. simpl_set_small.
    destruct Hinx as [Hinx | Hinx]; auto.
    simpl_set_small. rewrite big_union_app in Hinx.
    destruct Hinx as [Hina Hnotinx].
    simpl_set_small.
    rewrite big_union_rev in Hnotinx.
    auto.
  - (*wild case*)
    simpl. unfold row_fv; simpl.
    intros x Hinx.
    simpl_set_small.
    destruct Hinx as [Hinx | Hinx]; auto.
    simpl_set_small.
    destruct Hinx as [Hina Hnotinx].
    rewrite big_union_app in Hnotinx.
    simpl_set_small.
    left. split; auto.
Qed.

Lemma compile_bare_fv {gamma} (gamma_valid: valid_context gamma) 
  (b: bool) (ret_ty: gen_type b) (tms: list (term * vty))
  (P: list (list pattern * gen_term b)) t
  (Htys: Forall2 (term_has_type gamma) (map fst tms) (map snd tms))
  (Hp: @pat_matrix_typed gamma b ret_ty (map snd tms) P)
  (simpl_constr: bool):
  compile_bare b simpl_constr tms P = Some t ->
  (*Idea: in each row, take free vars in term, remove those in pattern*)
  (*I think they are actually equal (as sets), but we don't prove*)
  sublist (gen_fv t) (union vsymbol_eq_dec (big_union vsymbol_eq_dec tm_fv (map fst tms))
    (pat_mx_tm_fv b P)).
Proof.
  revert Htys Hp. assert (Ht: True) by auto; revert t Ht. unfold compile_bare.
  apply (compile_prove_some_typed gamma_valid b ret_ty true simpl_constr (fun _ _ => True)
    (fun tms P t _ _ => sublist (gen_fv t) (union vsymbol_eq_dec (big_union vsymbol_eq_dec tm_fv (map fst tms))
    (pat_mx_tm_fv b P)))); auto.
  - intros. (*simplify*)
    specialize (Hsimpl (ltac:(auto))).
    intros x Hinx.
    specialize (Hsimpl _ Hinx).
    simpl_set_small.
    destruct Hsimpl as [Hin | Hin]; auto.
    eapply pat_mx_tm_fv_simp in Hin; eauto.
    simpl. simpl_set_small. destruct Hin; auto.
  - (*nil case*)
    intros a l _ Hty. simpl. apply union_sublist_l.
  - (*wilds*)
    intros.
    specialize (IHwilds _ (ltac:(auto)) Hcomp).
    eapply sublist_trans; [ apply IHwilds|]. simpl.
    apply sublist_union; [apply union_sublist_r| apply pat_mx_tv_fv_default].
  - (*full case*) intros.
    rewrite gen_match_fv.
    (*Proceed by cases*)
    intros x Hinx. simpl. simpl_set_small.
    destruct Hinx as [Hinx | Hinx]; auto.
    rewrite <- big_union_elts in Hinx.
    destruct Hinx as [pt [Hinpt Hinx]].
    simpl_set_small.
    destruct Hinx as [Hinx Hnotinx].
    (*I think it should be in [pat_mx_tm_fv]*)
    (*Get element, relate it to ps1 and cslist*)
    destruct (In_nth _ _ (Pwild, gen_d _) Hinpt) as [n [Hn Hyt]].
    pose proof (f_equal (fun x => nth n x (Pwild, Some (gen_d b))) Hopt)
      as Hntheq.
    simpl in Hntheq.
    revert Hntheq.
    (*Simplify this*)
    rewrite map_nth_inbound with (d2:=(Pwild, gen_d b)) by auto.
    rewrite Hyt.
    assert (Hn1: n < length cslist \/ n >= length cslist) by lia.
    assert (Hlen: length ps = length ps1 + length cslist).
    { apply (f_equal (@length _)) in Hopt. revert Hopt. solve_len. }
    destruct Hn1 as [Hn1 | Hn1].
    2: { (*Second case (wilds) is easier*)
      rewrite app_nth2; simpl_len; [|lia].
      destruct Hps1' as [[Hps1eq Hnowilds1] | [Hnowilds1 [t2 [Hcompw Hps1eq]]]]; subst ps1; simpl in *; try lia.
      assert (Hn': n = length cslist) by lia.
      rewrite Hn' at 1. rewrite Nat.sub_diag. simpl.
      destruct pt as [y1 t1]. simpl. intros Heq; inversion Heq; subst y1 t1; clear Heq.
      (*Use wilds result*)
      apply IHwilds in Hcompw; auto.
      apply Hcompw in Hinx.
      simpl_set_small. destruct Hinx as [Hinx | Hinx]; auto.
      apply pat_mx_tv_fv_default in Hinx; auto.
    }
    (*Constr case is harder*)
    rewrite app_nth1 by solve_len. 
    rewrite rev_nth; simpl_len; [| lia].
    erewrite map_nth_inbound with (d2:=(id_fs, nil, nil)); try lia.
    destruct ( nth (Datatypes.length cslist - S n) cslist (id_fs, [], []))
      as [[cs tys] pats] eqn : Hnth.
    simpl.
    unfold rev_map. rewrite !map_rev, !rev_involutive.
    destruct pt as [y1 t1]. simpl in Hinx |- *.
    intros Heq. injection Heq. intros Hcompcase Hconstr. clear Heq.
    unfold comp_cases in Hcompcase.
    (*For typing info, let's get info about ty, cs, etc*)
    assert (Hincslist: In (cs, tys, pats) cslist). {
      rewrite <- Hnth. apply nth_In. lia.
    }
    assert (Hget: amap_get funsym_eq_dec (fst types_cslist) cs = Some pats). {
      apply (populate_all_fst_snd_full _ _ _ Hsimpl Hpop). exists tys; auto. }
    assert (Hmem: amap_mem funsym_eq_dec cs (fst types_cslist)).
    { rewrite amap_mem_spec, Hget; auto. }
    revert Hcompcase. unfold cases. rewrite Hcasewild.
    pose proof (in_cslist_typed _ _ Hp Hpop Hsimpl Hincslist) as Hcsty.
    assert (Hlenpats: Datatypes.length pats = Datatypes.length (s_args cs)).
    { inversion Hcsty; solve_len. } 
    erewrite (dispatch1_equiv_spec _ ret_ty _ _  _ Hsimpl Hpop Hp Hmem).
    rewrite map_snd_combine; [|solve_len].
    intros.
    (*Now we use the IH*)
    apply IHconstrs with(cs:=cs) in Hcompcase; auto.
    (*Now no more typing conditions, just need to prove sublist inclusion*)
    assert (Hinxt1:=Hinx).
    apply Hcompcase in Hinx; clear Hcompcase.
    simpl_set_small.
    destruct Hinx as [Hinx | Hinx].
    + (*Case 1: x in newly added variables*)
      revert Hinx. rewrite map_app. unfold vsymbol in *.
      rewrite rev_combine by solve_len.
      rewrite map_fst_combine by solve_len.
      rewrite big_union_app. simpl_set_small.
      rewrite big_union_rev. intros Hinx.
      destruct Hinx as [Hinx | Hinx]; auto.
      (*Idea: contradiction: known not in pat_fv of y1, but we add
        all the vars we create to the bound list in pattern
        Very important: we have intermediate free vars, but nothing
        by the end!*)
      simpl_set.
      destruct Hinx as [tm [Hintm Hinx]].
      rewrite in_map_iff in Hintm.
      destruct Hintm as [v [Htm Hinv]].
      subst tm.
      simpl in Hinx. destruct Hinx as [Hvx | []]; subst v.
      (*The contradiction*)
      simpl in Hnotinx. exfalso; apply Hnotinx.
      rewrite <- Hconstr. simpl.
      simpl_set. exists (Pvar x). simpl; split; auto.
      rewrite in_map_iff. exists x; auto.
    + (*Case 2: x in [spec] matrix*)
      apply pat_mx_tv_fv_spec in Hinx; auto.
  - (*Tfun wild case*)
    intros. simpl.
    apply IHwilds in Hcomp; auto.
    eapply sublist_trans;[apply Hcomp|]; clear Hcomp.
    intros x Hinx. simpl_set_small.
    destruct Hinx as [Hinx | Hinx]; auto.
    right. apply pat_mx_tv_fv_default; auto.
  - (*Tfun*) intros. revert Hcomp.
    unfold comp_cases.
    (*Again, relate to [spec]*)
    unfold cases; rewrite Hcasewild.
    rewrite (dispatch1_equiv_spec _ ret_ty _ _  _ Hsimpl Hpop Hp Hmem).
    intros Hcomp.
    subst params.
    specialize (IHfun _ (ltac:(auto)) Hcomp).
    eapply sublist_trans;[apply IHfun|]; clear IHfun.
    intros x Hinx. simpl. simpl_set_small.
    destruct Hinx as [Hinx | Hinx].
    + (*Case 1: x in newly added variables*)
      revert Hinx.
      rewrite rev_combine by solve_len.
      rewrite map_app, map_fst_combine by solve_len.
      rewrite big_union_app. simpl_set_small. 
      rewrite big_union_rev. intros [Hinx | Hinx]; auto.
      (*If in tms, in t*)
      left. left. subst. simpl. auto.
    +(*Case 2: x in [spec] matrix*)
      apply pat_mx_tv_fv_spec in Hinx; auto.
Qed.

(*single versions of these lemmas*)
Lemma compile_bare_single_fv {gamma: context} (gamma_valid: valid_context gamma)
  (b: bool) (ret_ty: gen_type b) (t: term) (ty: vty)
  (ps: list (pattern * gen_term b))
  (Hty: term_has_type gamma t ty)
  (Htyps1: Forall (fun p => pattern_has_type gamma (fst p) ty) ps)
  (Htyps2: Forall (fun t => gen_typed gamma b (snd t) ret_ty) ps) tm
  (simpl_constr: bool):
  compile_bare_single b simpl_constr t ty ps = Some tm ->
  sublist (gen_fv tm) (gen_fv (gen_match t ty ps)).
Proof.
  unfold compile_bare_single.
  intros Hcomp.
  apply (compile_bare_fv gamma_valid) with (ret_ty:=ret_ty) in Hcomp; auto.
  - (*Prove sublist*)
    apply (sublist_trans _ _ _ Hcomp).
    rewrite gen_match_fv.
    unfold pat_mx_tm_fv. simpl. intros x Hinx.
    simpl_set_small. 
    destruct Hinx as [Hinx | Hinx]; simpl_set_small.
    { destruct_all; auto. contradiction. }
    right. simpl_set.
    destruct Hinx as [y [Hiny Hinx]]. simpl_set_small.
    rewrite in_map_iff in Hiny. destruct Hiny as [y2 [Hy Hiny2]]; subst.
    simpl in Hinx. exists y2. split; auto.
    destruct Hinx as [Hinx Hnotinx].
    unfold row_fv in Hnotinx. simpl in Hnotinx.
    simpl_set_small; split; auto.
  - constructor; auto.
  - apply compile_bare_single_pat_typed; rewrite Forall_map; auto.
Qed.

Lemma compile_bare_single_type_vars
  (b: bool) (t: term) (ty: vty)
  (ps: list (pattern * gen_term b)) tm
  (simpl_constr: bool):
  compile_bare_single b simpl_constr t ty ps = Some tm ->
  sublist (gen_type_vars tm) (gen_type_vars (gen_match t ty ps)).
Proof.
  unfold compile_bare_single; intros Hcomp.
  apply compile_bare_type_vars in Hcomp.
  apply (sublist_trans _ _ _ Hcomp).
  intros x Hinx. rewrite gen_type_vars_match.
  unfold tm_list_type_vars, pat_mx_type_vars in Hinx. simpl in Hinx.
  simpl_set_small.
  destruct Hinx as [Hinx | Hinx].
  - simpl_set_small. destruct Hinx as [Hinx | []]; simpl_set_small.
    destruct Hinx; auto.
  - simpl_set. destruct Hinx as [y [Hiny Hinx]].
    rewrite in_map_iff in Hiny. destruct Hiny as [y2 [Hy Hiny2]]; subst.
    simpl in Hinx.
    simpl_set_small.
    destruct Hinx as [Hinx | Hinx].
    + simpl_set_small. destruct Hinx as [Hinx | []].
      left. right. exists (fst y2); split; auto.
      rewrite in_map_iff; eauto.
    + right. left. exists (snd y2). split; auto. 
      rewrite in_map_iff; eauto.
Qed. 

(*Need to prove that fun//predsysm in terms dont change
  This is needed for recursion purposes*)

Definition gensym_in_pat_mx {b1 b2: bool} (f: gen_sym b1)
  (P: list (list pattern * gen_term b2)) : bool :=
  existsb (gensym_in_gen_term f) (map snd P).

Definition gensym_in_tms {b1: bool} (f: gen_sym b1)
  (tms: list (term * vty)) : bool :=
  existsb (gensym_in_term f) (map fst tms).

Lemma gensym_in_simplify {b1 b2: bool} (f: gen_sym b1) t (rl: list (list pattern * gen_term b2)):
  gensym_in_pat_mx f (simplify gen_let t rl) ->
  gensym_in_pat_mx f rl \/ gensym_in_term f t.
Proof.
  unfold simplify.
  unfold gensym_in_pat_mx.
  induction rl as [| rhd rtl IH]; simpl; auto.
  rewrite map_app, existsb_app.
  unfold is_true. rewrite !orb_true_iff; intros [Hex | Hex]; auto.
  2: { apply IH in Hex. destruct Hex; auto. }
  clear IH.
  assert (Hin: gensym_in_gen_term f (snd rhd) \/ gensym_in_term f t); 
    [|destruct Hin; auto].
  unfold simplify_single in Hex.
  destruct rhd as [ps a]; destruct ps as [| phd ptl].
  1: { simpl in *. rewrite orb_true_iff in Hex; destruct Hex as [Hex | Hex]; auto. }
  rewrite map_map in Hex. simpl in Hex.
  simpl. generalize dependent a.
  induction phd; simpl; intros a; try rewrite !orb_true_iff;
  try solve[intros; destruct_all; auto].
  - rewrite gensym_in_gen_let. rewrite orb_true_iff.
    intros; destruct_all; auto.
  - rewrite map_app, existsb_app.
    rewrite orb_true_iff. intros [Hex | Hex]; eauto.
  - intros Hex. apply IHphd in Hex.
    rewrite gensym_in_gen_let in Hex.
    destruct Hex as [Hex | ?]; auto. 
    apply orb_true_iff in Hex.
    destruct Hex; auto.
Qed.

Lemma gensym_in_default {b1 b2: bool} (f: gen_sym b1) (rl: list (list pattern * gen_term b2)):
  gensym_in_pat_mx f (default rl) ->
  gensym_in_pat_mx f rl.
Proof.
  unfold gensym_in_pat_mx.
  induction rl as [| [ps a] rtl IH]; simpl; auto.
  destruct ps as [| phd ptl]; simpl;
  [intros; rewrite IH; auto; apply orb_true_r|].
  destruct phd; try solve[intros; rewrite IH; auto; apply orb_true_r].
  simpl.
  unfold is_true; rewrite !orb_true_iff; intros; destruct_all; auto.
  rewrite IH; auto.
Qed. 

Lemma gensym_in_spec n cs {b1 b2: bool} (f: gen_sym b1) (rl: list (list pattern * gen_term b2)):
   gensym_in_pat_mx f
    (omap
    (fun x : list pattern * gen_term b2 =>
    match fst x with
    | Pconstr fs _ pats :: ps =>
    if funsym_eqb fs cs then Some (rev pats ++ ps, snd x) else None
    | Pwild :: ps => Some (repeat Pwild n ++ ps, snd x)
    | _ => None
    end) rl) -> gensym_in_pat_mx f rl.
Proof.
  unfold gensym_in_pat_mx.
  induction rl as [|[ps a] rtl IH]; simpl; auto.
  destruct ps as [| phd ptl]; [intros; rewrite IH; auto; apply orb_true_r|].
  destruct phd as [| f1 tys1 ps1 | | |]; try solve[intros; rewrite IH; auto; apply orb_true_r].
  - (*constr*)
    destruct (funsym_eqb_spec f1 cs); [|intros; rewrite IH; auto; apply orb_true_r].
    simpl. unfold is_true; rewrite !orb_true_iff; intros; destruct_all; auto;
    rewrite IH; auto.
  - (*wild*)
    simpl. unfold is_true; rewrite !orb_true_iff; intros; destruct_all; auto;
    rewrite IH; auto.
Qed.


Lemma gensym_in_match {b1 b2: bool} (f: gen_sym b1) (t: term)
  (ty: vty) (ps: list (pattern * gen_term b2)):
  gensym_in_gen_term f (gen_match t ty ps) =
  gensym_in_term f t || existsb (fun x => gensym_in_gen_term f (snd x)) ps.
Proof. destruct b1; destruct b2; reflexivity. Qed.

Lemma compile_bare_gensyms (b1 b2: bool) (tms: list (term * vty))
  (P: list (list pattern * gen_term b2)) t (simpl_constr: bool):
  compile_bare b2 simpl_constr tms P = Some t ->
  (forall (f: gen_sym b1), gensym_in_gen_term f t ->
    gensym_in_pat_mx f P \/ gensym_in_tms f tms).
Proof.
  intros Hcomp. assert (Ht: True) by auto; revert t Ht Hcomp. unfold compile_bare.
  apply (compile_prove_some _ gen_match gen_let gen_getvars gen_getvars_let
    true simpl_constr (fun tms P => True)
    (fun tms P t => forall f (Hinf: gensym_in_gen_term f t), gensym_in_pat_mx f P \/ gensym_in_tms f tms)); clear tms P.
  - intros. (*simplify*)
    specialize (Hsimpl _ (ltac:(auto)) Hcomp f Hinf). simpl.
    destruct Hsimpl as [Hin | Hin]; auto.
    apply gensym_in_simplify in Hin.
    destruct Hin as [Hin | Hin]; auto.
    right. unfold gensym_in_tms; simpl. rewrite Hin; auto.
  - (*nil case*)
    intros ps a l _ f Hinf.
    unfold gensym_in_pat_mx. simpl. rewrite Hinf; auto.
  - (*wilds*)
    intros. specialize (IHwilds _ (ltac:(auto)) Hmt1 f Hinf). 
    unfold gensym_in_tms; simpl.
    destruct IHwilds as [Hin | Hin]; auto.
    + apply gensym_in_default in Hin; auto.
    + right. apply orb_true_iff; auto.
  - (*full*)
    intros. 
    rewrite gensym_in_match in Hinf.
    apply orb_true_iff in Hinf.
    destruct Hinf as [Hinf | Hinf].
    1: { unfold gensym_in_tms; simpl. rewrite Hinf; auto. }
    apply existsb_exists in Hinf.
    destruct Hinf as [yt [Hinyt Hinx]].
    (*Get element, relate it to ps1 and cslist*)
    destruct (In_nth _ _ (Pwild, gen_d _) Hinyt) as [n [Hn Hyt]].
    pose proof (f_equal (fun x => nth n x (Pwild, Some (gen_d b2))) Hopt)
      as Hntheq.
    simpl in Hntheq.
    revert Hntheq.
    (*Simplify this*)
    rewrite map_nth_inbound with (d2:=(Pwild, gen_d b2)) by auto.
    rewrite Hyt.
    assert (Hn1: n < length cslist \/ n >= length cslist) by lia.
    assert (Hlen: length ps = length ps1 + length cslist).
    { apply (f_equal (@length _)) in Hopt. revert Hopt; solve_len. }
    destruct Hn1 as [Hn1 | Hn1].
    2: { (*Second case (wilds) is easier*)
      rewrite app_nth2; simpl_len; [|lia].
      destruct Hps1' as [[Hps1eq Hiswilds1] | [Hiswilds1 [t2 [Hcompw Hps1eq]]]]; subst ps1; simpl in *; try lia.
      assert (Hn': n = length cslist) by lia.
      rewrite Hn' at 1. rewrite Nat.sub_diag. simpl.
      destruct yt as [y1 t1]. simpl. intros Heq; inversion Heq; subst y1 t1; clear Heq.
      (*Use wilds result*)
      specialize (IHwilds _ (ltac:(auto)) Hcompw f Hinx).
      destruct IHwilds as [Hin | Hin]; auto.
      + apply gensym_in_default in Hin; auto.
      + right. apply orb_true_iff; auto.
    }
    (*Constr case is harder*)
    rewrite app_nth1 by solve_len.
    rewrite rev_nth by solve_len. simpl_len.
    rewrite map_nth_inbound with (d2:=(id_fs, nil, nil)) by solve_len.
    destruct ( nth (Datatypes.length cslist - S n) cslist (id_fs, [], []))
      as [[cs tys] pats] eqn : Hnth.
    simpl.
    unfold rev_map. rewrite !map_rev, !rev_involutive.
    destruct yt as [y1 t1]. simpl in Hinx |- *.
    intros Heq. injection Heq. intros Hcompcase Hconstr. clear Heq.
    unfold comp_cases in Hcompcase.
    assert (Hincs: In (cs, tys, pats) cslist). {
      rewrite <- Hnth.
      apply nth_In. lia.
    }
    revert Hcompcase. unfold cases; rewrite Hcasewild.
    rewrite (spec_noty Hsimpl Hpop Hincs).
    intros.
    apply IHconstrs with(cs:=cs)(f:=f) in Hcompcase; auto; 
    [| unfold cases; rewrite Hcasewild; apply (spec_noty Hsimpl Hpop Hincs)].
    destruct Hcompcase as [Hinf | Hinf]; [apply gensym_in_spec in Hinf; solve[auto]|]. (*solve spec case*)
    (*Case 2: in newly added - no funsyms!*)
    unfold gensym_in_tms in Hinf.
    rewrite map_app, existsb_app in Hinf.
    apply orb_true_iff in Hinf. unfold gensym_in_tms. simpl.
    destruct Hinf as [Hinf | Hinf]; auto; [| right; apply orb_true_iff; auto].
    rewrite map_rev, existsb_rev in Hinf.
    apply existsb_map_fst_combine in Hinf.
    apply existsb_exists in Hinf.
    destruct Hinf as [tm [Hintm Hinf]].
    rewrite in_map_iff in Hintm.
    destruct Hintm as [v [Htm Hintm]]; subst tm.
    (*Cannot have sym in var*)
    destruct b1; discriminate.
  - (*Tfun*) intros. unfold comp_cases in Hcomp.
    (*First, rewrite with spec*)
    rewrite amap_mem_spec in Hmem.
    destruct (amap_get funsym_eq_dec types cs) as [pats|] eqn : Htypes; [|discriminate].
    assert (Hin: exists tys, In (cs, tys, pats) cslist).
    { unfold cslist. apply (proj2 (populate_all_fst_snd_full _ _ _ Hsimpl Hpop)); assumption. }
    destruct Hin as [tys Hincs]. revert Hcomp.
    unfold cases. rewrite Hcasewild.
    rewrite (spec_noty Hsimpl Hpop Hincs). intros Hcomp.
    apply (IHconstrs cs) with (f:=f) in Hcomp; auto; [| unfold cases; rewrite Hcasewild; apply (spec_noty Hsimpl Hpop Hincs)].
    destruct Hcomp as [Hinf1 | Hinf1]; [ apply gensym_in_spec in Hinf1; solve[auto] |].
    (*Case 2: in newly added*)
    unfold gensym_in_tms in Hinf1.
    rewrite map_app, existsb_app in Hinf1.
    apply orb_true_iff in Hinf1.
    destruct Hinf1 as [Hinf1 | Hinf1]; auto; [| right; apply orb_true_iff; auto].
    rewrite map_rev, existsb_rev in Hinf1.
    apply existsb_map_fst_combine in Hinf1. subst. right.
    unfold gensym_in_tms; simpl.
    apply orb_true_iff; left.
    destruct b1; auto. simpl. apply orb_true_iff; auto.
Qed.

(*And the single version*)
Lemma compile_bare_single_syms
  (b1 b2: bool) (t: term) (ty: vty)
  (ps: list (pattern * gen_term b2)) tm (simpl_constr: bool):
  compile_bare_single b2 simpl_constr t ty ps = Some tm ->
    (forall (f: gen_sym b1), gensym_in_gen_term f tm ->
      gensym_in_gen_term f (gen_match t ty ps)).
Proof.
  unfold compile_bare_single. intros Hcomp f Hinf.
  apply compile_bare_gensyms with (b1:=b1)(f:=f) in Hcomp; auto.
  rewrite gensym_in_match.
  unfold gensym_in_pat_mx, gensym_in_tms in Hcomp.
  simpl in Hcomp.
  rewrite orb_false_r in Hcomp.
  destruct Hcomp as [Hex | Hinf1]; [|rewrite Hinf1; auto].
  rewrite map_map in Hex. simpl in Hex.
  apply orb_true_iff. right.
  revert Hex. induction ps; simpl; auto.
  unfold is_true; rewrite !orb_true_iff; intros; destruct_all; auto.
Qed.

(*Now we need to relate the [simpl_constr] and non-[simpl_constr]
versions. We have the following relation:
if (simpl_constr = false) gives Some (i.e. exhaustive), then
so does (simpl_constr = true). Thus, in the typing, we use the more
exhaustive check, and so the (optimized) compilation succeeds*)

Lemma lens_mx_refl {A: Type} (l1 : list (list pattern * A)):
  lens_mx l1 l1.
Proof.
  unfold lens_mx.
  rewrite Nat.eqb_refl; simpl.
  induction l1 as [| h t IH]; auto; rewrite all2_cons, Nat.eqb_refl; auto.
Qed.

(*Could prove for any reflexive relation*)
Lemma shape_mx_refl {A: Type} (l1 : list (list pattern * A)):
  shape_mx ty_rel l1 l1.
Proof.
  unfold shape_mx.
  induction l1 as [| h t IH]; auto. rewrite all2_cons, all_shape_p_refl; auto.
  apply ty_rel_refl. 
Qed.

(*A weaker but unconditional version of the change lemma:
  For any version of compiling, if the terms are equal and the
  patterns have the same shape, [compile] gives Some equally*)

Lemma isSome_some {A: Type} (o: option A):
  isSome o ->
  exists y, o = Some y.
Proof.
  destruct o; simpl; eauto. discriminate.
Qed.

Lemma option_bind_none {A B: Type} (o: option A) (f: A -> option B):
  option_bind o f = None ->
  o = None \/ exists y, o = Some y /\ f y = None.
Proof.
  destruct o; simpl; eauto.
Qed.

Lemma option_map_none {A B: Type} (o: option A) (f: A -> B):
  option_map f o = None -> o = None.
Proof.
  destruct o; simpl; auto; discriminate.
Qed.

Lemma none_isSome_false {A: Type} (o: option A):
  o = None ->
  ~ isSome o.
Proof.
  destruct o; auto. discriminate.
Qed.



(*We need a stronger [shape_p] - generalize by relation*)


(*Note for induction, we CANNOT have terms be the same*)
(*Here, we use [compile_ind] directly - dealing with two different typing results
  makes things quite tricky and the proof follows a different structure*)
Lemma compile_bare_simpl_constr {gamma} (gamma_valid: valid_context gamma)
  (b: bool)
  (P: pat_matrix b) tms1 tms2  ret_ty
  (* (P: list (list pattern * A)) *)
  (Htys: map snd tms1 = map snd tms2)
  (Htys1: Forall2 (term_has_type gamma) (map fst tms1) (map snd tms1))
  (Htys2: Forall2 (term_has_type gamma) (map fst tms2) (map snd tms2))
  (Hp: @pat_matrix_typed gamma b ret_ty (map snd tms1) P):
  isSome (compile_bare b false tms1 P) ->
  isSome (compile_bare b true tms2 P).
Proof.
  revert Htys1 Hp tms2 Htys Htys2. unfold compile_bare.
  apply (compile_ind _ gen_match gen_let gen_getvars (@gen_getvars_let b)
    true false
    (fun tms1 P o =>
      forall 
      (Htys1: Forall2 (term_has_type gamma) (map fst tms1) (map snd tms1))
      (Hp: @pat_matrix_typed gamma b ret_ty (map snd tms1) P)
      tms2 (Htys: map snd tms1 = map snd tms2)
      (Htys2: Forall2 (term_has_type gamma) (map fst tms2) (map snd tms2)),
      isSome o -> isSome 
        (compile (fun _ : typesym => []) gen_match gen_let gen_getvars true true tms2 P)));
  auto; clear tms1 P.
  - (*simplify*)
    intros t1 ty1 tms1 rl Hsimp Htys1 Hp tms2 Htys12 Htys2.
    destruct tms2 as [| [t2 ty2] tms2]; [discriminate|].
    simpl in *.
    specialize (Hsimp Htys1 (simplify_typed _ ret_ty (Forall2_inv_head Htys1) Hp)
      ((t2, ty2) :: tms2) Htys12 Htys2).
    (*Here, need to change to other [simplify] - why we needed "change" lemma to involve simpl_constr*)
    intros Hsome. rewrite <- !compile_simplify in Hsimp by apply gen_getvars_let.
    apply Hsimp in Hsome.
    pose proof (@shape_mx_simplify ty_rel _ _ gen_let gen_let t1 t2 rl rl (lens_mx_refl _) (shape_mx_refl _)) as Hshapes.
    apply andb_true_iff in Hshapes. destruct Hshapes.
    eapply @compile_simpl_constr_change_ps with (P2:=simplify gen_let t2 rl) in Hsome; eauto;
    try apply gen_getvars_let.
    rewrite <- !compile_simplify in Hsome by apply gen_getvars_let; auto. apply Hsome.
  - (*Return*)
    intros ps a l _ Hty tms Htms. destruct tms as [| tm2 tms2]; [|discriminate].
    intros _ _. reflexivity.
  - (*Interesting case*)
    intros t1 ty tms1 rl rhd rtl is_bare_css is_bare css is_constr Hsimpl Hrl types_cslist
      Hpop types cslist casewild Hdisp1 cases wilds [IHwilds IHconstrs] Htytms1 Htyrl [| [tm2 ty2] tms2]; [discriminate|].
    simpl. intros Heq; injection Heq. intros Htms12 Hty; clear Heq; subst ty2. intros Htytms2.
    subst rl. Opaque dispatch1_opt. simp compile. set (rl:=rhd :: rtl) in *.
    subst is_bare_css.
    set (is_bare_css:= match ty with
    | vty_cons _ _ => (true, [])
    | _ => (false, [])
    end) in *.
    subst is_bare; subst css; simpl; set (is_bare := fst is_bare_css) in *; set (css := snd is_bare_css) in *.
    subst is_constr; set (is_constr:= fun fs : funsym => f_is_constr fs && (is_bare || in_bool funsym_eq_dec fs css)) in *.
    rewrite Hpop.
    (*Deal with [[dispatch1_opt]*)
    apply dispatch1_opt_some in Hdisp1.
    destruct Hdisp1 as [Hnotnull Hcasewild]; subst casewild.
    destruct (dispatch1_opt gen_let tm2 (fst types_cslist) rl) as [casewild2|] eqn : Hdisp2.
    2: {
      apply dispatch1_opt_none in Hdisp2. 
      rewrite existsb_forallb_negb, Hnotnull in Hdisp2. discriminate.
    }
    apply dispatch1_opt_some in Hdisp2.
    destruct Hdisp2 as [Hnotnull2 Hcasewild2]; subst casewild2.
    (*Before destructing, prove IHwilds hyps*)
    assert (Hwilds: wilds = default rl). {
      unfold wilds. apply dispatch1_equiv_default; auto.
    } 
    forward IHwilds.
    { inversion Htytms1; auto. }
    forward IHwilds.
    { rewrite Hwilds. eapply default_typed; eauto. }
    specialize (IHwilds _ Htms12).
    forward IHwilds.
    { inversion Htytms2; auto. }
    (*Now case analysis*)
    unfold types.
    destruct (amap_is_empty (fst types_cslist)) eqn : Hemp.
    { rewrite dispatch1_equiv_default; auto. rewrite <- Hwilds. apply IHwilds. }
    (*Now we know that [comp_full] isSome
      idea: should prove that this means that 
      1) all constrs compile are Some (for false, and by IH, by true)
      2) if is_wilds is true, then wilds are Some
      3) and therefore, comp_full is Some
      use (3) for comp_full, use (1) for constr case
    *)
    unfold comp_full.
    rewrite <- option_map_bind.
    intros Hopt.
    apply isSome_some in Hopt.
    destruct Hopt as [tm1 Hopt].
    apply option_map_some in Hopt.
    destruct Hopt as [ps [Hps Ht1]]; subst tm1.
    apply option_bind_some in Hps.
    destruct Hps as [ps1 [Hps1 Hopt]].
    (*This way we can deal with [fold_left_opt] before destructing 'forallb'*)
    apply fold_right_opt_add_map in Hopt. unfold cslist in Hps1.
    set (is_wilds := (if is_bare
          then
           option_bind
             (option_map
                (fun x : funsym * list vty * list pattern => let (y, _) := x in let (cs, _) := y in cs)
                (hd_error (snd types_cslist)))
             (fun x : funsym => Some (amap_size (fst types_cslist) =? f_num_constrs x))
          else Some (forallb (fun f : funsym => amap_mem funsym_eq_dec f (fst types_cslist)) css))) in *.
    (*Much more useful than destructing and simplifying each time*)
    assert (Hps1': (ps1 = nil /\ is_wilds = Some true) \/ (is_wilds = Some false /\
      exists t2, compile (fun _ => nil) gen_match gen_let gen_getvars true false tms1 wilds = Some t2 /\
        ps1 = [(Pwild, t2)])).
    {
      apply option_bind_some in Hps1.
      destruct Hps1 as [z [Hsome Hifz]].
      destruct z; [inversion Hifz; auto|].
      apply option_map_some in Hifz. destruct Hifz as [t1' [Hwilds' Hps1]]; subst. right.
      split; auto.
      exists t1'. auto.
    }
    clear Hps1.
    (*First, prove that compiling all constructors (with any well-typed terms) gives Some*)
    assert (Hallconstrs: forall (cs: funsym) tys pats, (*(l: list (list pattern * gen_term b)),
      amap_get funsym_eq_dec cases cs = Some l ->*)
      (*amap_mem funsym_eq_dec cs types ->*)
      In (cs, tys, pats) cslist ->
      (*Will prove typing*)
      forall tms2,
      (rev (map (ty_subst (s_params cs) tys) (s_args cs)) ++ map snd tms1) = map snd tms2 ->
      Forall2 (term_has_type gamma) (map fst tms2) (map snd tms2) ->
      isSome (compile (fun _ : typesym => []) gen_match gen_let gen_getvars true true tms2 (spec _ rl cs))).
    {
      intros cs tys pats Hincslist tms3 Htms3 Htytms3.
      (*Idea: since cs is in types, we find element of [Hopt]*)
      assert (Hinmap: In ((add_map gen_getvars
               (fun (cs : funsym) (al : list (term * vty)) =>
                comp_cases (compile (fun _ : typesym => []) gen_match gen_let gen_getvars true false)
                  cases tms1 cs al) t1 ty tms1 rl) (cs, tys, pats)) 
      (map (fun x : pattern * gen_term b => (fst x, Some (snd x))) ps)).
      {
        rewrite <- Hopt. rewrite in_app_iff. left. rewrite <- In_rev.
        rewrite in_map_iff. eexists; eauto.
      }
      clear Hopt.
      simpl in Hinmap.
      rewrite in_map_iff in Hinmap.
      destruct Hinmap as [[p gt] [Heq Hinx]].
      simpl in Heq. injection Heq; clear Heq; intros Hcomp Hp.
      subst p. symmetry in Hcomp.
      unfold comp_cases in Hcomp.
      (*use [spec] results*)
      assert (Hmem: amap_mem funsym_eq_dec cs (fst types_cslist)). {
        rewrite amap_mem_spec.
        assert (Hget: amap_get funsym_eq_dec (fst types_cslist) cs = Some pats) by
        (apply (proj2 (populate_all_fst_snd_full _ _ _ Hsimpl Hpop)); eauto).
        rewrite Hget; auto.
      }
      unfold cases,types in Hcomp.
      rewrite @dispatch1_equiv_spec with(gamma:=gamma)(is_constr:=is_constr)(ret_ty:=ret_ty)(tys:=ty :: map snd tms1) 
        in Hcomp by auto.
      (*Now simplify and use IHconstrs*)
      revert Hcomp.
      unfold rev_map. rewrite !map_rev, !rev_involutive.
      intros Hcomp.
      pose proof (in_cslist_typed _ _ Htyrl Hpop Hsimpl Hincslist) as Htycs.
      assert (Hlen: length pats = length (s_args cs)) by (inversion Htycs; auto).
      eapply IHconstrs with (cs:=cs). 6: rewrite Hcomp; auto. all: eauto.
      - unfold cases, types. apply @dispatch1_equiv_spec with(gamma:=gamma)(is_constr:=is_constr)(ret_ty:=ret_ty)(tys:=ty :: map snd tms1); auto.
      - (*Term types*)
        rewrite !map_app. apply Forall2_app; [| inversion Htytms1; auto].
        rewrite !map_rev, map_fst_combine, map_snd_combine by solve_len.
        apply Forall2_rev.
        rewrite map_snd_combine by solve_len.
        rewrite Forall2_nth. simpl_len. rewrite Hlen, Nat.min_id.
        split; auto. intros i d1 d2 Hi.
        rewrite map_nth_inbound with (d2:=(""%string, vty_int)) by solve_len.
        rewrite combine_nth by solve_len.
        apply T_Var'; [| simpl; apply nth_indep; solve_len].
        pose proof (in_cslist_val _ _ Htyrl Hpop Hsimpl Hincslist) as Hallval.
        rewrite Forall_nth in Hallval.
        apply Hallval; rewrite map_length; lia.
      - (*pat matrix typed*)
        rewrite map_app, !map_rev.
        rewrite !map_snd_combine by solve_len.
        (*Get ty as ADT*)
        inversion Htycs; subst.
        destruct  H11 as [m [a [m_in [a_in c_in]]]].
        unfold sigma in H9. simpl in H9.
        rewrite (adt_constr_subst_ret gamma_valid m_in a_in c_in) in H9; auto.
        subst ty.
        eapply spec_typed; subst; eauto.
        rewrite Forall_forall. apply (constr_ret_valid gamma_valid m_in a_in); auto.
      - (*And the equality*)
        rewrite map_app, <- Htms3. f_equal; auto.
        rewrite !map_rev. rewrite !map_snd_combine by solve_len.
        reflexivity.
    }
    (*2: prove [comp_full]*)
    assert (Hcompfullsome: isSome
      (option_bind
         (option_bind is_wilds
            (fun b0 : bool =>
             if b0
             then Some []
             else
              option_map (fun x : gen_term b => [(Pwild, x)])
                (compile (fun _ : typesym => []) gen_match gen_let gen_getvars true true tms2
                   (snd (dispatch1 gen_let tm2 (fst types_cslist) rl)))))
         (fun b0 : list (pattern * gen_term b) =>
          option_map (fun b1 : list (pattern * gen_term b) => gen_match tm2 ty b1)
            (fold_left_opt
               (add gen_getvars
                  (fun (cs : funsym) (al : list (term * vty)) =>
                   match
                     amap_get funsym_eq_dec (fst (dispatch1 gen_let tm2 (fst types_cslist) rl)) cs as o
                     return
                       (amap_get funsym_eq_dec (fst (dispatch1 gen_let tm2 (fst types_cslist) rl)) cs = o ->
                        option (gen_term b))
                   with
                   | Some l =>
                       fun
                         _ : amap_get funsym_eq_dec (fst (dispatch1 gen_let tm2 (fst types_cslist) rl)) cs =
                             Some l =>
                       compile (fun _ : typesym => []) gen_match gen_let gen_getvars true true
                         (rev al ++ tms2) l
                   | None =>
                       fun
                         _ : amap_get funsym_eq_dec (fst (dispatch1 gen_let tm2 (fst types_cslist) rl)) cs =
                             None => None
                   end eq_refl) tm2 ty rl tms2) (snd types_cslist) b0)))).
    {
      assert (Hnone: forall {A: Type} (o: option A), (o = None -> False) -> isSome o) by (intros; destruct o; auto).
      apply Hnone; clear Hnone; intros Hcomp.
      apply option_bind_none in Hcomp.
      destruct Hcomp as [Hwildsn | [w [Hwildsy Hcomp]]].
      { apply option_bind_none in Hwildsn.
        (*contradiction from above*)
        destruct Hwildsn as [Hiswildsn | [y [Hiswilds Hy]]].
        - destruct Hps1' as [ [_ Hiswilds] | [Hiswilds _] ]; rewrite Hiswildsn in Hiswilds; discriminate.
        - destruct y; simpl in Hy; try discriminate.
          (*Use wilds IH*)
          destruct Hps1' as [[_ Hiswilds1] | [_ [tmw [Hcomp Hps1]]]]; [rewrite Hiswilds1 in Hiswilds; discriminate|].
          apply option_map_none in Hy.
          rewrite Hcomp in IHwilds. simpl in IHwilds. forward IHwilds; [reflexivity|].
          rewrite dispatch1_equiv_default in Hy by auto.
          rewrite <- Hwilds in Hy.
          rewrite Hy in IHwilds. discriminate.
      }
      (*Wilds case done, now get contradiction from None in rest*)
      apply option_map_none in Hcomp.
      apply fold_left_opt_none in Hcomp.
      destruct Hcomp as [l1 [x [l2 [y [Hcslist [Hfold Hadd]]]]]]. (*do we need Hfold?*)
      unfold add in Hadd.
      destruct x as [[cs params] pats].
      (*Use fact that it is [spec]*)
      assert (Hget1: amap_get funsym_eq_dec (fst types_cslist) cs = Some pats).
      { apply (proj2 (populate_all_fst_snd_full _ _ _ Hsimpl Hpop)). rewrite Hcslist.
        exists params. rewrite in_app_iff; simpl; auto.
      }
      assert (Hmem: amap_mem funsym_eq_dec cs types). {
        unfold types; rewrite amap_mem_spec, Hget1. reflexivity.
      }
      rewrite @dispatch1_equiv_spec with(gamma:=gamma)(is_constr:=is_constr)(ret_ty:=ret_ty)(tys:=ty :: map snd tms1) 
        in Hadd by auto.
      (*Now we use the constr lemma we proved*)
      revert Hadd.
      match goal with
      |- ((match ?x with | Some v => ?a | None => ?b end) = None -> False) =>
        destruct x eqn : Hcomp; [discriminate|]
      end.
      (*simplify list*)
      revert Hcomp.
      unfold rev_map; rewrite!map_rev,!rev_involutive,map_snd_combine_eq; simpl_len. (*TODO: do we need exact length from typing?*)
      intros Hcomp. 
      apply none_isSome_false in Hcomp. exfalso; apply Hcomp.
      assert (Hin: In (cs, params, pats) (snd types_cslist)) by (rewrite Hcslist, in_app_iff; simpl; auto).
      (*Need typing*)
      pose proof (in_cslist_typed _ _ Htyrl Hpop Hsimpl Hin) as Htypat.
      assert (Hlenpats: length pats = length (s_args cs)) by (inversion Htypat; auto).
      rewrite Hlenpats, Nat.min_id, firstn_all2 by solve_len. 
      eapply (Hallconstrs cs params pats); auto.
      - symmetry. rewrite map_app, !map_rev. f_equal; auto.
        rewrite map_snd_combine by solve_len.
        reflexivity.
      - (*prove typing*)
        rewrite !map_app. apply Forall2_app; [|inversion Htytms2; auto].
        rewrite !map_rev, map_fst_combine, map_snd_combine by solve_len.
        apply Forall2_rev.
        rewrite Forall2_nth. simpl_len; split; [lia|].
        intros i di d2 Hi.
        (*TODO: should really prove an induction principle for typing to avoid all this repetition*)
        rewrite map_nth_inbound with (d2:=("x"%string, vty_int)) by solve_len.
        rewrite combine_nth by solve_len. 
        apply T_Var'; [|simpl; apply nth_indep; solve_len].
        (* show these types are valid*)
        pose proof (in_cslist_val _ _ Htyrl Hpop Hsimpl Hin) as Hallval.
        rewrite Forall_nth in Hallval.
        apply Hallval; solve_len.
    }
    (*Now back to case analysis*)
    destruct (is_fun tm2) as [s|] ; [|solve[auto]].
    destruct s as [[[cs tys] tms] Ht].
    simpl in Ht |- *.
    destruct (f_is_constr cs && (is_bare || in_bool funsym_eq_dec cs css)) eqn : Hconstr; [|solve[auto]].
    (*Get ADT info*)
    assert (Htytm2: term_has_type gamma tm2 ty).
    { subst. inversion Htytms2; auto. }
    rewrite Ht in Htytm2.
    assert (Hisconstr: f_is_constr cs) by (bool_hyps; auto).
    rewrite is_constr_iff in Hisconstr; [| apply gamma_valid | inversion Htytm2; auto].
    destruct Hisconstr as [m [a [m_in [a_in c_in]]]].
    assert (Hty: ty = vty_cons (adt_name a) tys).
    {
      inversion Htytm2; subst.
      apply (adt_constr_subst_ret gamma_valid m_in a_in c_in); auto.
    }
    destruct (amap_mem funsym_eq_dec cs (fst types_cslist)) eqn : Hmem.
    2: {
      (*wilds case - first need to prove that is_wilds is true because we have constr notin*)
      assert (Hiswilds: is_wilds = Some (forallb (fun f : funsym => amap_mem funsym_eq_dec f (fst types_cslist)) (adt_constr_list a))).
      {
        unfold is_wilds.
        subst ty. subst is_bare_css; subst is_bare; subst css. simpl. 
        (* unfold is_bare, bare_css. rewrite Hty.
        destruct bare; simpl; auto; [| unfold css', css, bare_css; rewrite Hty; auto]. *)
        (*Idea: if bare is true:
        1. amap_choose is Some
        2. result is well-typed so equal to [get_constructors]*)
        unfold cslist.
        destruct (hd_error (snd types_cslist)) as [[[cs2 tys2] ps2]|] eqn : Hchoose.
        2: {
          apply (populate_all_snd_hd_none Hsimpl Hpop) in Hchoose.
          unfold types in Hemp.
          rewrite Hemp in Hchoose; discriminate.
        }
        simpl. apply (populate_all_snd_hd_some Hsimpl Hpop) in Hchoose.
        f_equal.
        unfold types.
        
        (*Now continue*)
        assert (c2_in: constr_in_adt cs2 a). {
          unfold types in Hchoose.
          apply (populate_all_in_adt gamma_valid  _ _ m_in a_in Hsimpl Htyrl Hpop Hchoose).
        }
        erewrite (size_check_equal gamma_valid _ _ m_in a_in c2_in Hsimpl Htyrl); [| | eauto].
        2: {
          erewrite populate_all_ext. apply Hpop. 
          unfold is_constr. simpl.
          intros. rewrite andb_true_r; reflexivity.
        }
        reflexivity.
      }
      (*And now we prove that [is_wilds] is true*)
      assert (Hwildt: is_wilds = Some false).
      {
        rewrite Hiswilds. f_equal. apply forallb_false.
        exists cs. rewrite Hmem. simpl. split; auto.
        apply constr_in_adt_eq; auto.
      }
      destruct Hps1' as [ [Hps1 Hiswilds1] | [_ [ tm3 [Hwilds1 Hps1] ]]];
      [rewrite Hiswilds1 in Hwildt; discriminate |].
      rewrite Hwilds1 in IHwilds.
      forward IHwilds; [reflexivity|].
      rewrite dispatch1_equiv_default by auto.
      rewrite <- Hwilds. auto.
    }
    (*Constr case*)
    (*Know that [amap_get] must be [spec]*)
    rewrite (dispatch1_equiv_spec _ _ _  _ _ Hsimpl Hpop Htyrl Hmem).
    (*Need to get constructor in cslist*)
    rewrite amap_mem_spec in Hmem. 
    destruct (amap_get funsym_eq_dec (fst types_cslist) cs) as [pats|] eqn : Hget; [|discriminate].
    assert (Hincs: exists tys2, In (cs, tys2, pats) (snd types_cslist)). {
      apply (proj2 (populate_all_fst_snd_full _ _ _ Hsimpl Hpop)); assumption.
    }
    destruct Hincs as [tys2 Hincs]. subst ty.
    (*Now need that tys = tys2, from typing*)
    pose proof (in_cslist_args gamma_valid _ _ m_in a_in Htyrl Hpop Hsimpl Hincs) as [_ Htys].
    subst tys2.
    (*Now we can use constrs assumption*)
    inversion Htytms2; auto.
    eapply (Hallconstrs cs tys pats); auto.
    + rewrite map_app; f_equal; auto. rewrite !map_rev. f_equal.
      rewrite map_snd_combine; auto. simpl_len. inversion Htytm2; auto.
    + (*And prove typing*)
      rewrite !map_app. apply Forall2_app; auto. 
      rewrite !map_rev. apply Forall2_rev.
      assert (Hlentms: Datatypes.length tms = Datatypes.length (s_args cs)) by
        (inversion Htytm2; auto).
      rewrite map_fst_combine, map_snd_combine by solve_len.
      (*From typing*)
      inversion Htytm2; subst.
      rewrite Forall2_combine; split; auto. solve_len.
Qed.

(*And the corollary*)
Lemma compile_bare_single_simpl_constr {gamma} (gamma_valid: valid_context gamma)
  (b: bool) ret_ty (t1 t2: term) (ty: vty) (ps : list (pattern * gen_term b))
  (Hty1: term_has_type gamma t1 ty)
  (Hty2: term_has_type gamma t2 ty)
  (Htyps1: Forall (fun p => pattern_has_type gamma (fst p) ty) ps)
  (Htyps2: Forall (fun t => gen_typed gamma b (snd t) ret_ty) ps):
  isSome (compile_bare_single b false t1 ty ps) ->
  isSome (compile_bare_single b true t2 ty ps).
Proof.
  apply (@compile_bare_simpl_constr gamma gamma_valid) with (ret_ty:=ret_ty); auto;
  try solve[constructor; auto].
  apply compile_bare_single_pat_typed; rewrite Forall_map; auto.
Qed.
 