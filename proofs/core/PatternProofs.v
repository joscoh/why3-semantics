Require Import Pattern.
Require Import Denotational.
Require Import Coq.Sorting.Permutation.
From Equations Require Import Equations. 
Set Bullet Behavior "Strict Subproofs".

(*General results we need*)
Lemma Forall2_inv_head {A B: Type} {R: A -> B -> Prop} {a: A} {la: list A}
  {b1: B} {lb: list B} (Hall: Forall2 R (a :: la) (b1 :: lb)) : R a b1.
Proof.
  inversion Hall; auto.
Qed.

Lemma Forall2_inv_tail {A B: Type} {R: A -> B -> Prop} {a: A} {la: list A}
  {b1: B} {lb: list B} (Hall: Forall2 R (a :: la) (b1 :: lb)) : Forall2 R la lb.
Proof.
  inversion Hall; auto.
Qed.

Lemma Forall2_rev {A B: Type} {R: A -> B -> Prop} {l1 : list A} {l2: list B}:
  Forall2 R l1 l2 ->
  Forall2 R (rev l1) (rev l2).
Proof.
  intros Hall. induction Hall; simpl; auto.
  apply Forall2_app; auto.
Qed.

Lemma Forall2_rev_inv {A B: Type} {R: A -> B -> Prop} {l1 : list A} {l2: list B}:
  Forall2 R (rev l1) (rev l2) ->
  Forall2 R l1 l2.
Proof.
  intros Hall.
  rewrite <- (rev_involutive l1), <- (rev_involutive l2).
  apply Forall2_rev; auto.
Qed.

Lemma Forall2_app_inv {A B: Type} {P: A -> B -> Prop} {l1 l2 l3 l4}:
  Forall2 P (l1 ++ l2) (l3 ++ l4) ->
  length l1 = length l3 ->
  Forall2 P l1 l3 /\ Forall2 P l2 l4.
Proof.
  generalize dependent l3. induction l1 as [| h1 t1 IH]; intros [| h3 t3]; simpl;
  intros Hall Hlen; try discriminate; auto.
  inversion Hall as [|? ? ? ? Hp Hallt]; subst.
  specialize (IH t3 Hallt ltac:(lia)).
  destruct_all; split; auto.
Qed.

Lemma rev_inj {A: Type} (l1 l2: list A):
  rev l1 = rev l2 ->
  l1 = l2.
Proof.
  intros Hrev.
  rewrite <- (rev_involutive l1), <- (rev_involutive l2). rewrite Hrev; auto.
Qed.

(*TODO: move*)
(*Prevent expansion under simpl*)
Lemma big_union_cons {A B: Type} (eq_dec: forall x y: A, {x = y} + {x <> y})
  (f: B -> list A) (y: B) (l: list B):
  big_union eq_dec f (y :: l) = union eq_dec (f y) (big_union eq_dec f l).
Proof. reflexivity. Qed.


(*TODO: move to hlist and do stuff with equations*)
Equations hlist_app {A: Type} (f: A -> Type) (l1 l2: list A) (h1: hlist f l1) (h2: hlist f l2):
  hlist f (l1 ++ l2) :=
  hlist_app f nil l2 h1 h2 := h2;
  hlist_app f (x :: l1) l2 (HL_cons _ a1 htl) h2 := HL_cons _ _ _ a1 (hlist_app f l1 l2 htl h2).

Equations hlist_rev {A: Type} (f: A -> Type) (l: list A) (h: hlist f l) : hlist f (rev l) :=
  hlist_rev f nil h := h;
  hlist_rev f (x :: t) (HL_cons _ a1 htl) := hlist_app f (rev t) [x] (hlist_rev f t htl) 
    (HL_cons _ _ _ a1 (HL_nil _)).


Lemma hlist_hd_app1 {A: Type} {f: A -> Type} hd l1 l2 h1 h2:
  hlist_hd (hlist_app f (hd :: l1) l2 h1 h2) =
  hlist_hd h1.
Proof.
  rewrite (hlist_inv h1). simp hlist_app. reflexivity.
Qed. 

Lemma hlist_tl_app1 {A: Type} {f: A -> Type} hd l1 l2 h1 h2:
  hlist_tl (hlist_app f (hd :: l1) l2 h1 h2) =
  (hlist_app f l1 l2 (hlist_tl h1) h2).
Proof.
  rewrite (hlist_inv h1). simp hlist_app. reflexivity.
Qed. 

Lemma hlist_app_cast1 {f: sort -> Set} (l1 l2 l3: list sort) (h: arg_list f l1) h2 (Heq: l1 = l2):
  hlist_app f l2 l3 (cast_arg_list Heq h) h2 =
  cast_arg_list (f_equal (fun x => x ++ l3) Heq) (hlist_app f l1 l3 h h2).
Proof.
  subst. simpl. unfold cast_arg_list; simpl. reflexivity.
Qed.

Lemma hlist_rev_cast {f: sort -> Set} (l1 l2: list sort) (Heq: l1 = l2) (h1: arg_list f l1):
  hlist_rev f l2 (cast_arg_list Heq h1) =
  cast_arg_list (f_equal (fun x => rev x) Heq) (hlist_rev f l1 h1).
Proof.
  subst. reflexivity.
Qed.

Ltac destruct_match_single l Hmatch :=
  match goal with |- context [match_val_single ?v ?pd ?vt ?ty ?phd ?H1 ?h1] =>
      destruct (match_val_single v pd vt ty phd H1 h1) as [l|] eqn : Hmatch; simpl
    end.

Section PatProofs.

Context {gamma: context} (gamma_valid: valid_context gamma).
Context (pd: pi_dom) (pf: pi_funpred gamma_valid pd) (vt: val_typevar).
Variable (v: val_vars pd vt).
Variable (b: bool). (*Generic over terms and formulas*)
Variable (ret_ty : gen_type b). (*The return type of the values*)

(*More "gen" results (TODO: should move somewhere)*)
Section Gen.
(*Generalized term/formula rep*)
Definition gen_rep (v: val_vars pd vt) (ty: gen_type b) (d: gen_term b) (Hty: gen_typed b d ty) : gen_ret pd vt b ty :=
  match b return forall (ty: gen_type b) (dat: gen_term b), 
    gen_typed b dat ty -> gen_ret pd vt b ty with
  | true => fun ty dat Hty => term_rep gamma_valid pd vt pf v dat ty Hty
  | false => fun ty dat Hty => formula_rep gamma_valid pd vt pf v dat Hty
  end ty d Hty.

Definition gen_fv (t: gen_term b) : list vsymbol :=
  match b return gen_term b -> list vsymbol with
  | true => tm_fv
  | false => fmla_fv
  end t.

Lemma gen_rep_change_vv v1 v2 ty t Hty:
  (forall x, In x (gen_fv t) -> v1 x = v2 x) ->
  gen_rep v1 ty t Hty = gen_rep v2 ty t Hty.
Proof.
  generalize dependent t.
  generalize dependent ty.
  unfold gen_term, gen_type, gen_typed, gen_fv, gen_rep.
  destruct b; simpl in *; intros; [apply tm_change_vv | apply fmla_change_vv]; auto.
Qed.

Lemma gen_rep_irrel v1 ty d Hty1 Hty2:
  gen_rep v1 ty d Hty1 = gen_rep v1 ty d Hty2.
Proof.
  generalize dependent d.
  revert ty. unfold gen_rep. destruct b; simpl; intros;
  [apply term_rep_irrel | apply fmla_rep_irrel].
Qed.

End Gen.

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
  Forall (fun row => @gen_typed gamma b (snd row) ret_ty) p.

Lemma pat_matrix_typed_tail {tys p ps}:
  pat_matrix_typed tys (p :: ps) ->
  pat_matrix_typed tys ps.
Proof.
  intros Hp. destruct Hp as [Hp1  Hp2]; inversion Hp1; inversion Hp2; subst; split; auto.
Qed.

Lemma pat_matrix_typed_head {tys p ps}:
  pat_matrix_typed tys (p :: ps) ->
  row_typed tys (fst p) /\ @gen_typed gamma b (snd p) ret_ty.
Proof.
  intros Hp. destruct Hp as [Hp1  Hp2]; inversion Hp1; inversion Hp2; subst; split; auto.
Qed.

Lemma pat_matrix_typed_app_inv {tys p1 p2}:
  pat_matrix_typed tys (p1 ++ p2) ->
  pat_matrix_typed tys p1 /\ pat_matrix_typed tys p2.
Proof.
  unfold pat_matrix_typed.
  rewrite !Forall_app. intros; destruct_all; split_all; auto.
Qed.

End PatMatrixTyping.

(*Semantics of multiple pattern matching*)
Section MultipleMatchSemantics.


(*Much, much easier with Equations*)
Equations matches_row (tys: list vty) 
  (al: arg_list (domain (dom_aux pd)) (map (v_subst vt) tys))
  (p: list pattern) 
  (Htys: row_typed tys p) :
  option ((list (vsymbol * {s: sort & domain (dom_aux pd) s }))) :=
matches_row nil al nil Htys := Some [];
matches_row (t1 :: tys1) al (p :: ps) Htys :=
  option_bind ((match_val_single gamma_valid pd vt _ p (Forall2_inv_head Htys) (hlist_hd al)))
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

(*TODO (later): prove these equivalent to semantics in Denotational.v*)

(*One more version, when we start with terms*)
Equations terms_to_hlist (ts: list term) (tys: list vty)
  (Hty: Forall2 (fun t ty => term_has_type gamma t ty) ts tys) :
  arg_list (domain (dom_aux pd)) (map (v_subst vt) tys) :=
terms_to_hlist nil nil Hty := HL_nil _;
terms_to_hlist (t :: ts) (ty :: tys) Hty :=
  HL_cons _ _ _ (term_rep gamma_valid pd vt pf v t ty (Forall2_inv_head Hty)) 
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
  iter_arg_list gamma_valid pd tys a ps Htys =
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
  - destruct (match_val_single _ _ _ _ phd _) as [m1|] eqn : Hmatch1; simpl in Hmatch; try discriminate.
    destruct (matches_row _ _ ptl _) as [m2|] eqn : Hmatch2; try discriminate. simpl in Hmatch.
    inversion Hmatch; subst. simpl.
    rewrite map_app, in_app_iff, union_elts,
      (match_val_single_free_var _ _ _ _ _ _ _ _ _ Hmatch1), (IH _ _ _ _ Hmatch2).
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

(*Prove the key intermediate results for the S and D matrices.
  First, we give nicer definitions*)

Definition spec(P: pat_matrix) (c: funsym) : pat_matrix :=
  Pattern.filter_map (fun x =>
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

Definition default(P: pat_matrix) : pat_matrix :=
  Pattern.filter_map (fun x =>
    match (fst x) with
    | Pwild :: ps => Some (ps, snd x)
    | _ => None
    end ) P.

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
  term_rep gamma_valid pd vt pf v t _ Hty = dom_cast (dom_aux pd) (*Need 2 casts*)
    (eq_sym (v_subst_cons (adt_name a) args)) 
  (scast 
    (eq_sym (adts pd m (map (v_subst vt) args) a a_in))
  (* [[c]](al)*)
  (constr_rep gamma_valid m m_in 
    (map (v_subst vt) args) (eq_trans (map_length _ _) args_len) (dom_aux pd) a a_in 
      c c_in (adts pd m (map (v_subst vt) args)) 
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
  assert (srts_len: length (map (v_subst vt) args) = length (m_params m)) by (rewrite map_length; auto).
  assert (Hunif: uniform m) by (apply (gamma_all_unif gamma_valid); auto). 
  (*Of course, use [find_constr_rep]*)
  destruct (find_constr_rep gamma_valid _ m_in (map (v_subst vt) args) srts_len (dom_aux pd) a a_in
    (adts pd m (map (v_subst vt) args)) Hunif
    (scast (adts pd m (map (v_subst vt) args) a a_in) (dom_cast (dom_aux pd) (v_subst_cons (adt_name a) args) 
      (term_rep gamma_valid pd vt pf v t
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

(*Technically works for anything associative, can change*)
Lemma option_bind_appcomp {A: Type} (o1 o2: option (list A)) (m: list A):
  option_bind (option_bind o1 (fun x => option_bind o2 (fun y => Some (x ++ y)))) (fun x => Some (m ++ x)) =
  option_bind (option_bind o1 (fun x => Some (m ++ x))) (fun y => option_bind o2 (fun x => Some (y ++ x))).
Proof.
  destruct o1; destruct o2; simpl; auto.
  rewrite app_assoc. reflexivity.
Qed.

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
    destruct_match_single m1 Hmatch1.
    + (*fails: rewrite Hmatch1*) (*Can't even refer to other one*)
      match goal with |- context [match_val_single ?v ?pd ?vt ?ty ?phd ?H1 ?h1] =>
        replace (match_val_single v pd vt ty phd H1 h1) with (Some m1)
      end.
      erewrite IH with (h1:=hlist_tl h1) (Hr2:=(Forall2_inv_tail Hr2)) (Hr3:=Hr3); simpl.
      * (*Same problem again - this time, we prove a lemma*)
        apply option_bind_appcomp.
      * lia.
      * rewrite hlist_tl_cast.
        rewrite (hlist_tl_app1 (v_subst vt ty)). reflexivity.
    + match goal with |- context [match_val_single ?v ?pd ?vt ?ty ?phd ?H1 ?h1] =>
        replace (match_val_single v pd vt ty phd H1 h1) with (@None (list (vsymbol * {s : sort & domain (dom_aux pd) s})))
      end.
      reflexivity.
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
  match_val_single gamma_valid pd vt (vty_cons (adt_name a) args) (Pconstr c params tms) Hp 
    (term_rep gamma_valid pd vt pf v t (vty_cons (adt_name a) args) Hty1) =
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
  match_val_single gamma_valid pd vt (vty_cons (adt_name a) args) (Pconstr c2 params tms) Hp 
    (term_rep gamma_valid pd vt pf v t (vty_cons (adt_name a) args) Hty1) =
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

Definition opt_related {A B: Type} (P: A -> B -> Prop) (o1: option A) (o2: option B) : Prop :=
  match o1, o2 with
  | Some x, Some y => P x y
  | None, None => True
  | _, _ => False
  end.

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
  apply Forall2_app_inv in Hty2'; [| rewrite !rev_length; auto].
  destruct Hty2' as [Hrowrev Hrowhd].
  (*Need correct typecast*)
  set (h2:=(HL_cons (domain (dom_aux pd)) (v_subst vt ty1) (map (v_subst vt) nil) 
    (hlist_hd al) (HL_nil _)) : arg_list (domain (dom_aux pd)) (map (v_subst vt) [ty1])).

  rewrite matches_row_app with (h1:=cast_arg_list (eq_sym (map_rev _ _)) 
    (hlist_rev _ (map (v_subst vt) tys) (hlist_tl al)))(h2:=h2)(Hr2:=Hrowrev)(Hr3:=Hrowhd); auto.
  3: rewrite !rev_length; auto.
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
    destruct (match_val_single gamma_valid pd vt ty1 p1
      (Forall2_inv_head Hrowhd) (hlist_hd al)); auto.
    rewrite app_nil_r. eapply Permutation_trans. apply Permutation_app_comm.
    apply Permutation_app_tail; assumption.
  - destruct (matches_row (rev tys)
      (cast_arg_list (eq_sym (map_rev (v_subst vt) tys))
      (hlist_rev (domain (dom_aux pd)) (map (v_subst vt) tys)
      (hlist_tl al)))
      (rev ps) Hrowrev) as [m2|] eqn : Hmatch2; [contradiction|].
    destruct (match_val_single gamma_valid pd vt ty1 p1
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

(*Finally, a few small results about [extend_val_with_list] - TODO move these*)

Lemma get_assoc_list_app {A B: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y}) (l1 l2: list (A * B)) (x: A):
  get_assoc_list eq_dec (l1 ++ l2) x =
  match (get_assoc_list eq_dec l1 x) with
  | Some y => Some y
  | _ => get_assoc_list eq_dec l2 x
  end.
Proof.
  induction l1 as [| [x1 y1] t1]; simpl; auto.
  destruct (eq_dec x x1); subst; auto.
Qed.

Lemma extend_val_app l1 l2 x:
  extend_val_with_list pd vt v (l1 ++ l2) x =
  if in_dec vsymbol_eq_dec x (map fst l1) then
    extend_val_with_list pd vt v l1 x
  else extend_val_with_list pd vt v l2 x.
Proof.
  unfold extend_val_with_list.
  rewrite get_assoc_list_app.
  destruct (get_assoc_list vsymbol_eq_dec l1 x) eqn : Hsome; simpl;
  destruct (in_dec vsymbol_eq_dec x (map fst l1)); auto.
  - apply get_assoc_list_some in Hsome.
    exfalso; apply n; rewrite in_map_iff; exists (x, s); auto.
  - apply get_assoc_list_none in Hsome. contradiction.
Qed.

Lemma extend_val_perm l1 l2 x:
  NoDup (map fst l1) ->
  Permutation l1 l2 ->
  extend_val_with_list pd vt v l1 x = extend_val_with_list pd vt v l2 x.
Proof.
  intros Hn Hp.
  destruct (in_dec vsymbol_eq_dec x (map fst l1)) as [Hin | Hnotin].
  - rewrite in_map_iff in Hin. destruct Hin as [[x1 d1] [Hx Hinx1]]; simpl in *; subst.
    rewrite !extend_val_lookup with (t:=d1); auto.
    + eapply Permutation_NoDup. apply Permutation_map. apply Hp. auto.
    + eapply Permutation_in. apply Hp. auto.
  - rewrite !extend_val_notin; auto.
    erewrite perm_in_iff. apply Hnotin. apply Permutation_sym, Permutation_map; auto.
Qed.

(*The exact one we need*)
Lemma extend_val_app_perm m1 m2 m3 x:
NoDup (map fst m1) ->
Permutation m1 m2 ->
extend_val_with_list pd vt v (m1 ++ m3) x =
extend_val_with_list pd vt v (m2 ++ m3) x.
Proof.
  intros Hn Hperm.
  rewrite !extend_val_app.
  assert (Hiff: In x (map fst m1) <-> In x (map fst m2)). {
    apply perm_in_iff, Permutation_map; auto.
  }
  destruct (in_dec vsymbol_eq_dec x (map fst m1)) as [Hin1 | Hnotin1];
  destruct (in_dec vsymbol_eq_dec x (map fst m2)) as [Hin2 | Hnotin2]; auto.
  - apply extend_val_perm; auto.
  - apply Hiff in Hin1; contradiction.
  - apply Hiff in Hin2; contradiction.
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

  matches_matrix_tms (t :: ts) (vty_cons (adt_name a) args :: tys) P
    Htsty Htyp =

  matches_matrix 
  (*Type list more complicated: args of c + rest*)
  (rev (ty_subst_list (s_params c) args (s_args c)) ++ tys)
    (cast_arg_list (spec_prop_cast c args _ params_len)
   (hlist_app _ _ _ (hlist_rev _ _ al1) (terms_to_hlist ts tys (Forall2_inv_tail Htsty))))
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
    apply rev_inj in e. auto.
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
        2: {  unfold sorts_to_tys, ty_subst_list.
          rewrite !rev_length, !map_length. auto. }
        destruct Hr1 as [Hrow1 Hrow2].
        (*Now we can split the [app]*)
        rewrite matches_row_app with(h1:=cast_arg_list Heq1 (hlist_rev _ _ al1))(h2:=terms_to_hlist ts tys f)
          (Hr2:=Hrow1)(Hr3:=Hrow2).
        (*We prove the easy goals first*)
        2: rewrite hlist_app_cast1, cast_arg_list_compose; apply cast_arg_list_eq.
        2: unfold ty_subst_list; rewrite !rev_length, map_length; auto.
        2: symmetry; apply (Forall2_length (Forall2_inv_tail Htyr)).

        (*Now we need to transform the [matches_row] into the corresponding
          [match_val_single] and the rest of the row; we then prove that
          [match_val_single] for a constructor is equivalent to [matches_row] 
          on the arg_list*)
        simp matches_row. simp terms_to_hlist. simpl hlist_hd.
        (*Coq is just awful at unifying things; this is really annoying*)
        match goal with
        | |- context [match_val_single ?v ?pd ?vt ?ty ?p ?Hp (term_rep _ _ _ _ _ _ _ ?Hty)] =>
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
          destruct (matches_row tys (terms_to_hlist ts tys f) ptl Hrow2) as [m3|] eqn : Hmatch3; simpl.
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
      2: {
        rewrite repeat_length, rev_length.
        unfold ty_subst_list.
        rewrite !map_length. reflexivity.
      }
      destruct Hrowty as [Hr1 Hr2].
      (*Again decompose the row via append*)
      simpl.
      rewrite matches_row_app  with (h1:=cast_arg_list Heq1 (hlist_rev (domain (dom_aux pd))
          (sym_sigma_args c (map (v_subst vt) args)) al1) )
        (h2:=(terms_to_hlist ts tys f))(Hr2:=Hr1)(Hr3:=Hr2).
      (*First, prove the side conditions*)
      2: {
        rewrite (hlist_app_cast1) with (Heq:=Heq1).
        rewrite !cast_arg_list_compose.
        apply cast_arg_list_eq.
      }
      2: {
        rewrite repeat_length.
        unfold ty_subst_list. rewrite rev_length, map_length; reflexivity. 
      }
      2: apply Forall2_length in Hr2; auto.
      (*Then simplify first because all wilds*)
      rewrite matches_row_all_wilds with (ps:=(repeat Pwild (Datatypes.length (s_args c)))); [| apply repeat_spec].
      simpl.
      (*A bit of simplification to get things together*)
      rewrite terms_to_hlist_tl.
      rewrite terms_to_hlist_irrel with (H2:=f).
      rewrite matches_row_irrel with (Hr2:=Hr2).
      destruct (matches_row tys (terms_to_hlist ts tys f) ptl Hr2) as [m1|] eqn : Hmatch1; simpl; auto.
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

  matches_matrix_tms (t :: ts) (vty_cons (adt_name a) args :: tys) P
    Htsty Htyp =

  matches_matrix tys (terms_to_hlist ts tys (Forall2_inv_tail Htsty)) (default P) Htyp'.
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
      * (*TODO: why do we need to do this?*)
        match goal with |- context [matches_row ?tys ?hl ?ptl ?H] =>
          replace (matches_row tys hl ptl H) with (Some m1) by (apply Hmatch1); auto
        end.
        f_equal. apply gen_rep_irrel.
      * match goal with |- context [matches_row ?tys ?hl ?ptl ?H] =>
          replace (matches_row tys hl ptl H) with (@None (list (vsymbol * {s: sort & domain (dom_aux pd) s }))) by (apply Hmatch1); auto
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
   matches_matrix_tms (t :: ts) (ty :: tys) P
    Htsty Htyp =

  matches_matrix tys (terms_to_hlist ts tys (Forall2_inv_tail Htsty)) (default P) Htyp'.
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
      * (*TODO: why do we need to do this?*)
        match goal with |- context [matches_row ?tys ?hl ?ptl ?H] =>
          replace (matches_row tys hl ptl H) with (Some m1) by (apply Hmatch1); auto
        end.
        f_equal. apply gen_rep_irrel.
      * match goal with |- context [matches_row ?tys ?hl ?ptl ?H] =>
          replace (matches_row tys hl ptl H) with (@None (list (vsymbol * {s: sort & domain (dom_aux pd) s }))) by (apply Hmatch1); auto
        end.
Qed.

(*The last big result we need before the main proof: simplifying the pattern matrix
  does not change the semantics*)

(*First, we need a generalized notion of "let"*)

Definition gen_let (v: vsymbol) (t: term) (g: gen_term b) : gen_term b :=
  match b return gen_term b -> gen_term b with
  | true => fun t2 => Tlet t v t2
  | false => fun f => Flet t v f
  end g.

Lemma gen_rep_let vv (ty2: gen_type b) (x: vsymbol) (t: term) (a: gen_term b) Hty1 Hty2 Hty3:
  gen_rep vv ty2 (gen_let x t a) Hty2 =
  gen_rep (substi pd vt vv x (term_rep gamma_valid pd vt pf vv t (snd x) Hty1)) ty2 a Hty3.
Proof.
  clear ret_ty.
  revert ty2 a Hty2 Hty3.
  unfold gen_let, gen_rep.
  destruct b; simpl; intros; simpl_rep; simpl;
  rewrite term_rep_irrel with (Hty2:=Hty1);
  [apply term_rep_irrel | apply fmla_rep_irrel].
Qed.

Lemma gen_let_typed_inv {t x d ty}:
  @gen_typed gamma b (gen_let x t d) ty ->
  term_has_type gamma t (snd x) /\ @gen_typed gamma b d ty.
Proof.
  unfold gen_let. destruct b; simpl in *; intros Hty; inversion Hty; subst; auto.
Qed.

Lemma gen_let_ty x t a ty:
  @gen_typed gamma b a ty ->
  term_has_type gamma t (snd x) ->
  @gen_typed gamma b (gen_let x t a) ty.
Proof.
  unfold gen_let.
  destruct b; simpl; intros; constructor; auto.
Qed.

(*We need the condition that no variable free in the list of terms we match on
  also appears free in a pattern. To see why, consider:
   match Tvar y, Tvar z with
  | Pvar x, Pvar y -> f (x, y)
  end
  should be: f(y, z)
  But if we match by iterating over each term and binding in a "let", we get:
  let x = y in (let y = z in f(x, y))
  let (y = z in f(y, y)) -> f(z, z)*)

Definition pat_row_vars_disj (ts: list term) (ps: list pattern) : Prop :=
  disj (big_union vsymbol_eq_dec tm_fv ts) (big_union vsymbol_eq_dec pat_fv ps).

Definition pat_matrix_vars_disj (ts: list term) (P: pat_matrix) : Prop :=
  Forall (fun row => pat_row_vars_disj ts (fst row)) P.

(*The interesting part: expanding with [simplify_single] is the same as matching the
  row, then substituting*)
Lemma simplify_single_match_eq t ts ty1 tys Htmty (row : list pattern * gen_term b) Hp1 Hp2
  (Htyrow: gen_typed b (snd row) ret_ty)
  (Htty: term_has_type gamma t ty1)
  (Hvars: pat_row_vars_disj (t :: ts) (fst row)):
  opt_related (fun d l => d = gen_rep (extend_val_with_list pd vt v l) ret_ty (snd row) Htyrow) 
  (matches_matrix (ty1 :: tys) (terms_to_hlist (t :: ts) (ty1 :: tys) Htmty)
    (simplify_single gen_let t row) Hp1)
  (matches_row (ty1 :: tys) (terms_to_hlist (t :: ts) (ty1 :: tys) Htmty) (fst row) Hp2).
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
      erewrite gen_rep_let with (Hty1:=proj1 (gen_let_typed_inv Hletty))
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
        apply (Hvars v1).
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
      assert (Hdisj1: pat_row_vars_disj (t :: ts) (rhd1 :: rtl)). {
        clear -Hvars.
        unfold pat_row_vars_disj in *.
        simpl in *. unfold disj in *.
        intros x [Hinx1 Hinx2].
        apply (Hvars x).
        simpl_set_small. destruct_all; split; auto.
      } 
      specialize (IHrhd1 Hp2' Hdisj1 a Hr1 Htyrow).
      destruct (matches_matrix _ _ _ Hr1) as [m1 |] eqn : Hmatch1.
      * (*First pattern matches*) simpl.
        simpl in IHrhd1.
        (*Make everything in goal match IH, need to destruct, all other cases contradictions*)
        rewrite match_val_single_irrel with (Hval2:=Forall2_inv_head Hp2').
        destruct (match_val_single _ _ _ _ _ (Forall2_inv_head Hp2') _) as [m2 |] eqn : Hmatch2;
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
        assert (Hdisj2: pat_row_vars_disj (t :: ts) (rhd2 :: rtl)). {
          clear -Hvars.
          unfold pat_row_vars_disj in *.
          simpl in *. unfold disj in *.
          intros x [Hinx1 Hinx2].
          apply (Hvars x).
          simpl_set_small. destruct_all; split; auto.
        }
        specialize (IHrhd2 Hp2'' Hdisj2 a Hr2 Htyrow).
        simpl hlist_tl in *.
        destruct (matches_matrix _ _ _ Hr2) as [m2|] eqn : Hmatch2.
        --(*Second pattern matches*)
          simpl in *.
          (*Still need info from first IH - cannot match*)
          rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hp2')).
          destruct (match_val_single _ _ _ _ rhd1 (Forall2_inv_head Hp2') _) as [m3|] eqn : Hmatch3; simpl in *.
          ++ (*Get contradiction from first IH*)
            rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hp2')).
            destruct (matches_row _ _ rtl _) as [m4|] eqn : Hmatch4; simpl in *; [contradiction|].
            (*Now use second IH*)
            destruct (match_val_single _ _ _ _ rhd2 _ _) as [m5|] eqn : Hmatch5;
            simpl in IHrhd2; [|contradiction].
            erewrite matches_row_irrel in Hmatch4; rewrite Hmatch4 in IHrhd2.
            contradiction.
          ++ (*Otherwise rhd does not match - no more info from IH1. rest of case is like first*)
            rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hp2'')).
            destruct (match_val_single _ _ _ _ rhd2 _ _) as [m4|] eqn : Hmatch4; simpl in *;
            [|contradiction]. 
            rewrite matches_row_irrel with (Hr2:=Forall2_inv_tail Hp2'').
            destruct (matches_row _ _ rtl _) as [m5|] eqn : Hmatch5; [|contradiction].
            simpl in *. apply IHrhd2.
        -- (*Neither matches*)
          simpl in *.
          (*Use info from both IHs*)
          rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hp2')).
          destruct (match_val_single _ _ _ _ rhd1 _ _) as [m3|] eqn : Hmatch3; simpl in *.
          ++ (*If rhd1 matches, by IH1, rtl cannot*)
            rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hp2')).
            destruct (matches_row _ _ rtl _) as [m4|] eqn : Hmatch4; [contradiction| auto].
          ++ (*see if rh2 matches*) 
            rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hp2'')).
            destruct (match_val_single _ _ _ _ rhd2 _ _) as [m4|] eqn : Hmatch4; simpl in *; auto.
            (*If rh2 matches, rtl cannot by IH2*)
            rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hp2'')).
            destruct (matches_row _ _ rtl) as [m5|] eqn : Hmatch5; [contradiction| auto].
    + (*Pbind case - recursive + Pvar case*)
      simpl simplify_aux.
      assert (Hr2: row_typed (ty1 :: tys) (rhd :: rtl)). {
        inversion Hp2; subst; constructor; auto.
        inversion H2; subst; auto.
      }
      assert (Hdisj: pat_row_vars_disj (t :: ts) (rhd :: rtl)).
      {
        clear -Hvars.
        unfold pat_row_vars_disj in *.
        simpl in *. unfold disj in *.
        intros x [Hinx1 Hinx2].
        apply (Hvars x).
        simpl_set_small. destruct_all; split; auto.
      } 
      assert (Htty': term_has_type gamma t (snd v0)). {
        inversion Hp2; subst.
        inversion H2; subst. auto.
      }
      assert (Hletty: @gen_typed gamma b (gen_let v0 t a) ret_ty).
      {
        apply gen_let_ty; auto.
      }
      specialize (IHrhd Hr2 Hdisj (gen_let v0 t a) Hp1 Hletty).
      (*Now destruct LHS and use IH*)
      (*Coq has trouble again*)
      match goal with 
      | |- context [matches_matrix ?a ?b ?c ?d] => destruct (matches_matrix a b c d) as [m1|]
        eqn : Hmatch1; simpl in *
      end.
      * (*Case 1: LHS matches, by IH we know that RHS matches also*)
        rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hr2)).
        destruct (match_val_single _ _ _ _ rhd _ _) as [m2|] eqn : Hmatch2; simpl in *;[|contradiction].
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
          rewrite <- (match_val_single_free_var _ _ _ _ _ _ _ _ _ Hmatch2).
          unfold pat_row_vars_disj in Hdisj.
          intros Hinv1'.
          apply (Hdisj v1).
          rewrite !big_union_cons.
          rewrite !union_elts. auto.
        -- unfold extend_val_with_list at 2. simpl.
          destruct (vsymbol_eq_dec x v0); subst; try contradiction.
          unfold extend_val_with_list. reflexivity.
      * (*Case 2: LHS doesnt match. Show same for RHS*)
        rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hr2)).
        destruct (match_val_single _ _ _ _ rhd _ _) as [m2|] eqn : Hmatch2; simpl in *; [| auto].
        (*If rhd matches, know rtl does not*)
        rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hr2)).
        destruct (matches_row _ _ rtl _) as [m3|] eqn : Hmatch3; simpl in *; [contradiction| auto].
Qed.

(*And the full result*)
Theorem simplify_match_eq (t: term) (ts: list term) (tys: list vty) (P: pat_matrix)
  Htmty Hty1 Hty2
  (Hdisj: pat_matrix_vars_disj (t :: ts) P):
  matches_matrix_tms (t :: ts) tys (simplify gen_let t P) Htmty Hty1 =
  matches_matrix_tms (t :: ts) tys P Htmty Hty2.
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
    assert (Hdisj1: pat_row_vars_disj (t :: ts) (fst rhd) ). {
      inversion Hdisj; auto.
    }
    (*Bulk is [simplify_single_match_eq] can't rewrite bc not rewritable relation*)
    pose proof (simplify_single_match_eq t ts ty1 tys Htmty rhd Hp1 (Forall_inv (proj1 Hty2))
      (Forall_inv (proj2 Hty2)) (Forall2_inv_head Htmty) Hdisj1) as Hrelated.
    destruct (matches_matrix _ _ _ Hp1) as [m1 |] eqn : Hmatch1; simpl in *.
    + (*If LHS matches, easy from lemma*)
      destruct (matches_row _ _ (fst rhd) _) as [m2|] eqn : Hmatch2; [|contradiction].
      subst. reflexivity.
    + (*If LHS doesn't match, use lemma to show RHS doesn't, then use IH*)
      destruct (matches_row _ _ (fst rhd) _) as [m2|] eqn : Hmatch2;[contradiction|].
      apply IH.
      inversion Hdisj; auto.
Qed.

End SpecDefaultLemmas.

Definition gen_match (t: term) (ty: vty) (l: list (pattern * gen_term b)) : gen_term b :=
  match b return list (pattern * gen_term b) -> gen_term b with
  | true => fun pats => Tmatch t ty pats
  | false => fun pats => Fmatch t ty pats
  end l.

Definition get_constructors (ts: typesym) : list funsym :=
  match (find_ts_in_ctx gamma ts) with
  | Some (m, a) => adt_constr_list a
  | None => nil
  end.

(*[populate] is some iff all constructors (nested) in the pattern satisfy [is_constr]*)
Check populate.

(*TODO: unify with thing in Pattern.v*)
Fixpoint constrs_in_pat (p: pattern) : list funsym :=
  match p with
  | Pconstr c tys ps => c :: concat (map constrs_in_pat ps)
  | Por p1 p2 => (constrs_in_pat p1) ++ (constrs_in_pat p2)
  | Pbind p _ => constrs_in_pat p
  | _ => nil
  end.
Print simplified_aux.
(*Only if simplified already or something*)
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
(*  - intros acc. destruct (populate is_constr acc p1) as [o1|] eqn : Hpop1; simpl.
    + intros Hpop2. apply IHp2 in Hpop2.
      destruct Hpop2 as [c [tys [ps [Hp2 Hc]]]]; subst. exists c. exists tys. exists ps. 
      
      [Hinc Hc]]. exists c. rewrite in_app_iff. split; auto.
    + intros _. apply IHp1 in Hpop1.
      destruct Hpop1 as [c [Hinc Hc]].
      exists c. rewrite in_app_iff. split; auto.
  - intros acc Hpop. eapply IHp. apply Hpop. 
Qed. *)

Lemma fold_left_opt_none {B C: Type} (f: B -> C -> option B) (l: list C) (base: B) :
  fold_left_opt f l base = None <->
  exists l1 x l2 y, l = l1 ++ x :: l2 /\ (fold_left_opt f l1 base)= Some y /\ f y x  = None.
Proof.
  revert base. induction l as [| h t IH]; simpl; intros; auto.
  - split; try discriminate.
    intros [l1 [x [l2 [y [Hl _]]]]]. destruct l1; inversion Hl.
  - destruct (f base h) eqn : Hf.
    + rewrite IH. split; intros [l1 [x [l2 [y [Hl [Hfold Hf']]]]]]; subst.
      * exists (h :: l1). exists x. exists l2. exists y. split_all; auto.
        simpl. rewrite Hf. auto.
      * destruct l1 as [| h1 t1].
        -- simpl in *. inversion Hfold; subst.
          inversion Hl; subst. rewrite Hf' in Hf. discriminate.
        -- inversion Hl; subst.
          simpl in Hfold. rewrite Hf in Hfold. 
          exists t1. exists x. exists l2. exists y. split_all; auto.
    + split; auto. intros _. exists nil. exists h. exists t.
      exists base. split_all; auto.
Qed.

(*pattern in matrix*)
Definition pat_in_mx (p: pattern) (P: pat_matrix) : Prop :=
  exists row, In row P /\ In p (fst row).

Lemma pat_in_mx_head p row P:
  In p (fst row) ->
  pat_in_mx p (row :: P).
Proof.
  intros Hin. unfold pat_in_mx. exists row. simpl; auto.
Qed.

Lemma pat_in_mx_tail p row P:
  pat_in_mx p P ->
  pat_in_mx p (row :: P).
Proof.
  unfold pat_in_mx.
  intros [row1 [Hinr Hinp]].
  exists row1. simpl; auto.
Qed.

Lemma pat_in_mx_nil p:
  ~ (pat_in_mx p nil).
Proof.
  intro C. destruct C; destruct_all; contradiction.
Qed.

Lemma pat_in_mx_cons_inv p row P:
  pat_in_mx p (row :: P) ->
  In p (fst row) \/ pat_in_mx p P.
Proof.
  unfold pat_in_mx. simpl.
  intros [row1 [[Hrow | Hinr] Hinp]]; subst; eauto.
Qed.

(*TODO: move to common*)
Ltac inv H :=
  try(intros H); inversion H; subst; clear H.


(*Everything in [get_heads] is in the original matrix*)
Lemma in_get_heads (P: pat_matrix) l:
  get_heads P = Some l ->
  forall p, In p l -> pat_in_mx p P.
Proof.
  revert l.
  induction P as [|[ps a] P' IH]; simpl; auto; intros l.
  - inv Hsome. contradiction.
  - destruct ps as [| phd ptl]; [discriminate|].
    destruct (get_heads P') as [l'|]; simpl; [|discriminate].
    inv Hsome. simpl. intros p [Hp | Hinp]; subst.
    + apply pat_in_mx_head. simpl; auto.
    + apply pat_in_mx_tail. eapply IH. reflexivity. auto.
Qed.

(*No, that isn't what we want: want: if p is in [get_heads] and matrix is typed,
  then p has the first type n the list*)
Lemma in_get_heads_tys (ty: vty) (tys: list vty) (P: pat_matrix) (p: pattern) l
  (Hp: pat_matrix_typed (ty :: tys) P)
  (Hheads: get_heads P = Some l)
  (Hinp: In p l):
  pattern_has_type gamma p ty.
Proof.
  generalize dependent l.
  (* remember (ty :: tys) as tys2. *)
  (* generalize dependent tys. generalize dependent tys2. revert ty.  *)
  induction P as [| [ps a] P' IH]; simpl; intros l. (*intros ty tys2 Hp tys Htys2 l; subst.*)
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

(*TODO: prob don't need these below: *)
Lemma pat_in_row_typed (p: pattern) (ps: list pattern) (tys: list vty)
  (Hrow: row_typed tys ps)
  (Hinp: In p ps):
  exists ty, pattern_has_type gamma p ty.
Proof.
  induction Hrow; [contradiction|].
  simpl in Hinp. destruct Hinp as [Hp | Hinp]; subst; eauto.
Qed.

(*Any pattern in a well-typed pattern matrix is well-typed*)
Lemma pat_in_mx_typed (p: pattern) (P: pat_matrix) (tys: list vty)
  (HP: pat_matrix_typed tys P)
  (Hinp: pat_in_mx p P):
  exists ty, pattern_has_type gamma p ty.
Proof.
  induction P as [| row P' IH]; simpl in *.
  - exfalso. apply (pat_in_mx_nil _ Hinp).
  - apply pat_in_mx_cons_inv in Hinp.
    pose proof (pat_matrix_typed_tail HP) as Htail.
    pose proof (pat_matrix_typed_head HP) as Hhead.
    destruct Hinp as [Hinp | Hinp]; auto.
    apply (pat_in_row_typed _ (fst row) tys); auto. apply Hhead.
Qed.

(*Any constructor pattern in a well-typed pattern matrix is indeed a constructor*)
(* 
Check simplify.
Section DispatchEq.

(*Simplifying twice does nothing*)

Lemma simplified_simplify_aux {B: Type}  (mk_let : vsymbol -> term -> B -> B) 
  t a p:
  simplified_aux p ->
  simplify_aux mk_let t a p = [(p, a)].
Proof.
  induction p; simpl; try discriminate; auto.
Qed.

Lemma simplified_simplify {B: Type}  (mk_let : vsymbol -> term -> B -> B) 
  (t : term) (rl : list (list pattern * B)):
  simplified rl ->
  simplify mk_let t rl = rl.
Proof.
  induction rl as [| [ps a] rtl IH]; simpl.
  - intros _. reflexivity.
  - destruct ps as [| phd ptl]; simpl; auto.
    + intros Htl. unfold simplify in *. simpl. f_equal. auto.
    + intros Hsimp. apply andb_prop in Hsimp.
      destruct Hsimp as [Hhd Htl].
      unfold simplify in *. simpl. rewrite IH; auto.
      rewrite simplified_simplify_aux; auto.
Qed.

Lemma simplify_twice  {B: Type}  (mk_let : vsymbol -> term -> B -> B) 
  (t : term) (rl : list (list pattern * B)):
  simplify mk_let t (simplify mk_let t rl) = simplify mk_let t rl.
Proof.
  apply simplified_simplify, simplify_simplified.
Qed.

Lemma dispatch1_simplify {B: Type} (mk_let: vsymbol -> term -> B -> B) t types P:
  dispatch1 mk_let t types (simplify mk_let t P) = dispatch1 mk_let t types P.
Proof.
  rewrite !dispatch_equiv.
  unfold dispatch2.
  rewrite simplify_twice.
  reflexivity.
Qed.

(*TODO: move*)
Lemma existsb_forallb_negb {B: Type} (p: B -> bool) (l: list B):
  existsb p l = negb (forallb (fun x => negb (p x)) l).
Proof.
  induction l as [| h t IH]; simpl; auto.
  destruct (p h); simpl; auto.
Qed.

(*TODO: move to Pattern?*)
Lemma dispatch1_opt_simplify {B: Type} t types P (mk_let: vsymbol -> term -> B -> B) : 
  dispatch1_opt mk_let t types (simplify mk_let t P) = dispatch1_opt mk_let t types P.
Proof.
  destruct (dispatch1_opt _ _ _ P) as [l1|] eqn : Hd1.
  - apply dispatch1_opt_some in Hd1.
    destruct Hd1 as [Hall Hl1].
    apply dispatch1_opt_some.
    split.
    + rewrite <- simplify_all_null. auto.
    + rewrite dispatch1_simplify; assumption.
  - apply dispatch1_opt_none in Hd1.
    apply dispatch1_opt_none.
    rewrite existsb_forallb_negb in Hd1 |- *.
    rewrite <- simplify_all_null. auto.
Qed.

(*Can we try to prove: compile ... = compile ... (simplify ...)
  then assume simplified - will make things easier I think*)
Lemma compile_simplify (tms: list (term * vty)) (P: pat_matrix)  t ty
  (*(Htys: Forall2 (term_has_type gamma) tms tys)*)
  (*(Hp: pat_matrix_typed tys P)*):
  compile get_constructors gen_match gen_let ((t, ty) :: tms) P =
  compile get_constructors gen_match gen_let ((t, ty) :: tms) (simplify gen_let t P).
Proof.
  destruct P as [| row P']; simp compile; auto.
  destruct ((simplify gen_let t (row :: P'))) as [| s1 stl] eqn : Hsimp.
  {
    exfalso. revert Hsimp. rewrite <- null_nil, null_simplify. simpl. auto.
  }
  simp compile.
  set (css := match ty with
    | vty_cons ts _ => get_constructors ts
    | _ => []
    end ) in *.
  set (P := row :: P') in *.
  rewrite <- Hsimp.
  Opaque dispatch1_opt.
  simpl.
  set (is_constr := fun fs => in_bool funsym_eq_dec fs css) in *.
  rewrite <- populate_all_simplify.
  destruct (populate_all is_constr P) as [types_cslist|] eqn : Hpop; [| reflexivity].
  rewrite dispatch1_opt_simplify.
  destruct (dispatch1_opt gen_let t (fst types_cslist) P) as [casewild|] eqn : Hdispatch; reflexivity.
Qed. *)

(*And therefore, it suffices to assume that the pattern matrix is simplified*)
(*Don't do this, just use for cons case*)
(*Do want to assume simplified this makes this easier for sure - problem
  is null, P :: ps case - get different a if we simplify or not (could assume ts not nil)*)
(*Lemma compile_simplified_suff
  (P1: option (gen_term b) -> Prop):
  (forall tms P, simplified P -> P1 (compile get_constructors gen_match gen_let tms P)) ->
  (forall tms P, P1 (compile get_constructors gen_match gen_let tms P)).
Proof.
  intros Hall.
  intros.
  destruct P as [| [ps a] P'].
  - simp compile. specialize (Hall tms nil). apply Hall. reflexivity.
  - destruct tms as [| thd ttl].
    + simp compile.
      specialize (Hall nil (simplify gen_let tm_d ((ps, a) :: P'))).
      prove_hyp Hall.
      { apply simplify_simplified. }
      destruct (simplify gen_let tm_d ((ps, a) :: P')) 


      simpl in Hall.
    
     rewrite compile_equation_2. simp compile.
   simpl in Hall.
  Check compile_equation_1.
  destruct tms as [| thd ttl]. simp compile.

  (tms: list (term * vty)) (P: pat_matrix)

  
   [|reflexivity].
  reflexivity.


  Search populate_all simplify.

    Search null nil.

    null_simplify:
  forall {A : Type} (mk_let : vsymbol -> term -> A -> A) 
    (t : term) (rl : list (list pattern * A)),
  null (simplify mk_let t rl) = null rl
     unfold simplify in Hsimp.
    apply concat_nil_Forall in Hsimp.
    rewrite Forall_map in Hsimp.
    inversion Hsimp; subst.
    unfold simplify_single in H1.
    Search simplify null.
    destruct ps

    Search concat nil.
  }*)

(*TODO: replace*)
(* Lemma pat_matrix_typed_cons tys p ps:
  row_typed tys (fst p) ->
  @gen_typed gamma b (snd p) ret_ty ->
  pat_matrix_typed tys ps ->
  pat_matrix_typed tys (p :: ps).
Proof.
  unfold pat_matrix_typed. intros; destruct_all; split; constructor; auto.
Qed.

Lemma simplify_single_typed_inv1 tms mk_let t row:
  pat_matrix_typed tms (simplify_single mk_let t row) ->
  row_typed tms (fst row).
Proof.
  unfold simplify_single. destruct row as [[| rhd rtl] a]; simpl; auto.
  - intros Hpat. apply pat_matrix_typed_head in Hpat.
    simpl in Hpat. apply Hpat.
  - intros Htyped. 
    induction rhd; simpl in *.
    + pose proof (pat_matrix_typed_head Htyped) as Hpat.
      simpl in *. destruct Hpat as [Hrow Hgen].
      inversion Hrow; subst.
      constructor; auto.
      Search pattern_has_type Pvar.
      constructor.
    
     apply pat_matrix_typed_head.head in Htyped. 

  
   unfold pat_matrix_typed in Hpat. simpl in Hpat.
  Print simplify_single.


Lemma simplify_typed_inv tms mk_let t rl:
  pat_matrix_typed tms (simplify mk_let t rl) ->
  pat_matrix_typed tms rl.
Proof.
  induction rl as [| rhd rtl IH].
  - unfold simplify; simpl. auto.
  - unfold simplify in *. simpl.
    intros Hpattyped.
    apply pat_matrix_typed_app_inv in Hpattyped.
    destruct Hpattyped as [Htyhd Htytl].
    apply pat_matrix_typed_cons; auto.
    + 
    Search pat_matrix_typed cons.
    Search pat_matrix_typed.
  Print pat_matrix_typed.

  pat_matrix_typed_app_inv:
  forall {tys : list vty}
  {p1 p2 : list (list pattern * gen_term b)},
pat_matrix_typed tys (p1 ++ p2) ->
pat_matrix_typed tys p1 /\ pat_matrix_typed tys p2

 pat_matrix_typed (ty :: map snd tms)
  (simplify gen_let t rl)
(2 / 2)
pat_matrix_typed (ty :: map snd tms) rl *) 

(*NOT iff: if regular, then simplify*)

Fixpoint pat_in_strong (p1 p2: pattern) : bool :=
  pattern_eqb p1 p2 ||
  match p2 with
  | Por pa pb => pat_in_strong p1 pa || pat_in_strong p1 pb
  | Pbind p _ => pat_in_strong p1 p
  | Pconstr c tys ps => existsb (fun x => x) (map (pat_in_strong p1) ps)
  | _ => false
  end.

Lemma pat_in_strong_rewrite p1 p2: pat_in_strong p1 p2 =
  pattern_eqb p1 p2 ||
  match p2 with
  | Por pa pb => pat_in_strong p1 pa || pat_in_strong p1 pb
  | Pbind p _ => pat_in_strong p1 p
  | Pconstr c tys ps => existsb (fun x => x) (map (pat_in_strong p1) ps)
  | _ => false
  end.
Proof.
  destruct p2; reflexivity.
Qed.

Lemma pat_in_strong_refl p: pat_in_strong p p.
Proof.
  rewrite pat_in_strong_rewrite. destruct (pattern_eqb_spec p p); auto; contradiction.
Qed.

(*All free vars in inner pattern are in outer pattern*)
Lemma pat_in_strong_fv p1 p2:
  pat_in_strong p1 p2 ->
  (forall x, In x (pat_fv p1) -> In x (pat_fv p2)).
Proof.
  intros Hstrong x Hinx.
  induction p2 as [v1 | f tys ps IH | |pa pb | p2 v1]; rewrite pat_in_strong_rewrite in Hstrong.
  - destruct (pattern_eqb_spec p1 (Pvar v1)); try discriminate. subst.
    simpl in Hinx. auto.
  - destruct (pattern_eqb_spec p1 (Pconstr f tys ps)); subst; auto. simpl in *.
    simpl_set. apply existsb_exists in Hstrong.
    destruct Hstrong as [b1 [Hinb1 Hb1]]; subst.
    rewrite in_map_iff in Hinb1.
    destruct Hinb1 as [p2 [Hstrong Hinp2]].
    exists p2. split; auto. rewrite Forall_forall in IH; apply IH; auto.
  - destruct (pattern_eqb_spec p1 Pwild); [|discriminate]; subst; auto.
  - destruct (pattern_eqb_spec p1 (Por pa pb)); subst; auto. simpl. simpl_set.
    destruct (pat_in_strong p1 pa); auto.
  - destruct (pattern_eqb_spec p1 (Pbind p2 v1)); subst; auto. simpl. simpl_set.
    destruct (pat_in_strong p1 p2); auto.
Qed.

Definition pat_in_mx_strong (p: pattern) (P: pat_matrix) : Prop :=
  exists row p1, In row P /\ In p1 (fst row) /\ pat_in_strong p p1.

(*TODO: prob dont use strong, just look at fv*)
Definition row_fv {B: Type} (row: list pattern * B) : list vsymbol :=
  big_union vsymbol_eq_dec pat_fv (fst row).
Definition pat_mx_fv (P: pat_matrix) : list vsymbol :=
  big_union vsymbol_eq_dec row_fv P.

Definition pat_matrix_vars_disj1 (tms: list term) (P: pat_matrix) : Prop :=
  disj (big_union vsymbol_eq_dec tm_fv tms) (pat_mx_fv P).

Lemma pat_matrix_vars_disj_equiv tms P:
  (pat_matrix_vars_disj tms P) <-> (pat_matrix_vars_disj1 tms P).
Proof.
  unfold pat_matrix_vars_disj, pat_matrix_vars_disj1. split.
  - intros Hall. intros x [Hinx1 Hinx2].
    unfold pat_mx_fv in Hinx2.
    revert Hinx2. rewrite <- big_union_elts.
    intros [row [Hinrow Hinx2]].
    rewrite Forall_forall in Hall.
    apply Hall in Hinrow.
    apply (Hinrow x). auto.
  - unfold pat_mx_fv. intros Hdisj.
    rewrite Forall_forall. intros row Hinrow x [Hxin1 Hinx2].
    revert Hinx2. rewrite <- big_union_elts. intros [p [Hinp Hinx2]].
    apply (Hdisj x); split; auto. simpl_set. exists row. split; auto.
    unfold row_fv. simpl_set. exists p; auto.
Qed.

(*Move?*) (*P1 = regular, P2 = simplify*)
Lemma pat_matrix_vars_subset tms P1 P2:
  (forall x, In x (pat_mx_fv P2) -> In x (pat_mx_fv P1)) ->
  (* (forall p, pat_in_mx_strong p P2 -> pat_in_mx_strong p P1) -> *)
  pat_matrix_vars_disj tms P1 -> 
  pat_matrix_vars_disj tms P2.
Proof.
  intros Hall.
  rewrite !pat_matrix_vars_disj_equiv. (*TODO: only have 1*) 
  unfold pat_matrix_vars_disj1.
  intros Hdisj x [Hx1 Hx2].
  apply Hall in Hx2.
  apply (Hdisj x); auto.
Qed.
(* 
  rewrite !Forall_forall.
  intros Hallin row Hinrow.
  unfold pat_row_vars_disj.
  unfold disj. intros x [Hinx1 Hinx2].
  rewrite <- big_union_elts in Hinx2.
  destruct Hinx2 as [p [Hinp Hinx2]].
  specialize (Hall p).
  assert (Hinmx: pat_in_mx_strong p P1). {
    apply Hall. unfold pat_in_mx. exists row. exists p. split_all; auto.
    apply pat_in_strong_refl.
  }
  unfold pat_in_mx in Hinmx.
  destruct Hinmx as [row2 [p_in [Hinrow2 [Hinp2 Hinstr]]]].
  specialize (Hallin row2 Hinrow2).
  apply (Hallin x).
  split; auto. simpl_set. exists p_in. split; auto.
  eapply pat_in_strong_fv. apply Hinstr. auto.
Qed. *)
(* 
Lemma pat_matrix_vars_subset tms P1 P2:
  (forall p, pat_in_mx p P2 -> pat_in_mx p P1) ->
  pat_matrix_vars_disj tms P1 -> 
  pat_matrix_vars_disj tms P2.
Proof.
  intros Hall.
  unfold pat_matrix_vars_disj.
  rewrite !Forall_forall.
  intros Hallin row Hinrow.
  unfold pat_row_vars_disj.
  unfold disj. intros x [Hinx1 Hinx2].
  rewrite <- big_union_elts in Hinx2.
  destruct Hinx2 as [p [Hinp Hinx2]].
  specialize (Hall p).
  assert (Hinmx: pat_in_mx p P1). {
    apply Hall. unfold pat_in_mx. exists row; auto.
  }
  unfold pat_in_mx in Hinmx.
  destruct Hinmx as [row2 [Hinrow2 Hinp2]].
  specialize (Hallin row2 Hinrow2).
  apply (Hallin x).
  split; auto. simpl_set. exists p. auto.
Qed. *)
(*TODO: delete this stuff*)
Lemma pat_in_mx_strong_app_iff p P1 P2:
  pat_in_mx_strong p (P1 ++ P2) <-> pat_in_mx_strong p P1 \/ pat_in_mx_strong p P2.
Proof.
  unfold pat_in_mx_strong. setoid_rewrite in_app_iff.
  split; intros Hin; destruct_all; eauto 6.
Qed.

Lemma pat_in_mx_strong_tail p row P:
  pat_in_mx_strong p P ->
  pat_in_mx_strong p (row :: P).
Proof.
  unfold pat_in_mx_strong. simpl.
  intros; destruct_all; eauto 6.
Qed.

Lemma pat_in_mx_strong_head p1 p2 row P:
  In p2 (fst row) ->
  pat_in_strong p1 p2 ->
  pat_in_mx_strong p1 (row :: P).
Proof.
  intros Hin Hstr. unfold pat_in_mx_strong. exists row. exists p2. simpl; auto.
Qed.

Lemma pat_in_mx_strong_nil p:
  ~ (pat_in_mx_strong p nil).
Proof.
  intro C. destruct C; destruct_all; contradiction.
Qed.

Lemma pat_in_mx_strong_cons_inv p row P:
  pat_in_mx_strong p (row :: P) ->
  (exists p2, In p2 (fst row) /\ pat_in_strong p p2) \/ pat_in_mx_strong p P.
Proof.
  unfold pat_in_mx_strong. simpl.
  intros [row1 [p1 [[Hrow | Hinr] [Hinp1 Hstrong]]]]; subst; eauto 6.
Qed.

Lemma big_union_app {B C: Type} (eq_dec: forall (x y: C), {x = y} + {x <> y})
  (f: B -> list C) (l1 l2: list B):
  forall x, In x (big_union eq_dec f (l1 ++ l2)) <-> In x (union eq_dec (big_union eq_dec f l1) (big_union eq_dec f l2)).
Proof. 
  intros x. simpl_set. setoid_rewrite in_app_iff.
  split; intros; destruct_all; eauto.
Qed.

(*This is NOT true - ex: (Por p1 p2) in original, p1 in simplify, not in original
  Need stronger, nested notion*)
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

(*And so we get the disjointness result we want*)
Lemma simplify_disj mk_let tms t rl:
  pat_matrix_vars_disj tms rl ->
  pat_matrix_vars_disj tms (simplify mk_let t rl).
Proof.
  apply pat_matrix_vars_subset.
  apply simplify_subset.
Qed.

Lemma pat_matrix_typed_app {tys: list vty} {p1 p2}:
  pat_matrix_typed tys p1 ->
  pat_matrix_typed tys p2 ->
  pat_matrix_typed tys (p1 ++ p2).
Proof.
  unfold pat_matrix_typed; rewrite !Forall_app; intros; destruct_all; auto.
Qed.

Lemma prove_pat_matrix_typed_cons {tys p ps}:
  row_typed tys (fst p) ->
  @gen_typed gamma b (snd p) ret_ty ->
  pat_matrix_typed tys ps ->
  pat_matrix_typed tys (p :: ps).
Proof.
  intros. unfold pat_matrix_typed in *.
  destruct_all; split; constructor; auto.
Qed.

Lemma pat_matches_typed_nil l:
  pat_matrix_typed l nil.
Proof.
  split; auto.
Qed.

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
      try(solve[constructor; auto]); try solve[apply pat_matches_typed_nil];
      try solve[apply gen_let_ty; auto].
      * repeat(constructor; auto).
      * rewrite map_app. apply pat_matrix_typed_app; auto.
      * apply IHphd; auto. apply gen_let_ty; auto.
Qed.
Print simplified.
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

(*Need a bunch of typing results for default and specialize*)
Search dispatch1_opt Some.
(*First, prove equivalent to dispatch*)
Lemma dispatch1_equiv_default mk_let t types rl:
  simplified rl -> (*Makes things easier*)
  snd (dispatch1 mk_let t types rl) = default rl.
Proof.
  intros Hsimp.
  rewrite dispatch_equiv.
  unfold dispatch2.
  rewrite simplified_simplify; auto.
  induction rl as [| [[| phd ptl] a] rtl IH]; auto; simpl;
  destruct (dispatch2_gen types rtl) as [cases wilds]; simpl in *; auto.
  destruct phd; auto. simpl. rewrite IH; auto.
Qed.

(*The other one will be harder, do later*)

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
  simplified rl ->
  pat_matrix_vars_disj (t :: ts) rl ->
  pat_matrix_vars_disj ts (default rl).
Proof.
  intros Hsimp.
  rewrite !pat_matrix_vars_disj_equiv.
  unfold pat_matrix_vars_disj1.
  intros Hdisj.
  eapply disj_sublist_lr.
  - apply Hdisj.
  - rewrite big_union_cons. apply union_sublist_r.
  - apply default_vars_subset.
Qed.

Lemma default_typed {t ts rl}:
  pat_matrix_typed (t :: ts) rl ->
  pat_matrix_typed ts (default rl).
Proof.
  induction rl as [| [ps a] rtl IH]; intros Hpat.
  - apply pat_matches_typed_nil.
  - simpl.
    pose proof (pat_matrix_typed_tail Hpat) as Htl.
    pose proof (pat_matrix_typed_head Hpat) as Hhd; simpl in Hhd;
    destruct Hhd as [Hrow Hty].
    destruct ps as [| phd ptl]; auto.
    inversion Hrow; subst.
    destruct phd; auto.
    apply prove_pat_matrix_typed_cons; auto.
Qed.

  
(*Our main correctness theorem: [compile is_constr gen_let gen_case tms tys P] =
  Some t iff [matches_matrix_tms tms tys P] = Some d and
  d = term_rep v t*)
Theorem compile_correct (tms: list term) (tys: list vty) (P: pat_matrix) 
  (Htys: Forall2 (term_has_type gamma) tms tys)
  (Hp: pat_matrix_typed tys P)
  (Hdisj: pat_matrix_vars_disj tms P):
  opt_related (fun t d => forall Hty, d = gen_rep v ret_ty t Hty)
    (compile get_constructors gen_match gen_let (combine tms tys) P)
    (matches_matrix_tms tms tys P Htys Hp).
Proof.
  assert (Htms: tms = map fst (combine tms tys)).
  {
    rewrite map_fst_combine; auto. apply Forall2_length in Htys; auto.
  }
  assert (Htyseq: tys = map snd (combine tms tys)).
  {
    rewrite map_snd_combine; auto. apply Forall2_length in Htys; auto.
  }
  assert (Htys2: Forall2 (term_has_type gamma) (map fst (combine tms tys))
    (map snd (combine tms tys))).
  {
    rewrite <- Htms, <- Htyseq; auto.
  }
  assert (Hp2: pat_matrix_typed (map snd (combine tms tys)) P).
  {
    rewrite <- Htyseq; auto.
  }
  replace (matches_matrix_tms tms tys P Htys Hp) with
  (matches_matrix_tms (map fst (combine tms tys)) (map snd (combine tms tys)) P Htys2 Hp2).
  2: {
    revert Htys2 Hp2.
    rewrite <- Htms, <- Htyseq.
    intros. unfold matches_matrix_tms.
    erewrite terms_to_hlist_irrel. apply matches_matrix_irrel.
  }
  rewrite Htms in Hdisj.
  clear Htms Htyseq Htys Hp.
  generalize dependent (combine tms tys). clear tms tys.
  intros tms Hdisj Htys Hp.
  apply (compile_ind get_constructors gen_match gen_let
    (fun ts P o => forall (Hdisj: pat_matrix_vars_disj (map fst ts) P) Htys Hp, 
      opt_related (fun t d => forall Hty, d = gen_rep v ret_ty t Hty)
      o (matches_matrix_tms (map fst ts) (map snd ts) P Htys Hp))); clear.
  - (*extensionality*)
    intros t ty tms rl Hopt Hdisj Htys Hp. simpl in *.
    unfold opt_related in *.
    (*Proved hyps for Hopt*)
    specialize (Hopt (simplify_disj _ _ _ _ Hdisj) Htys (simplify_typed (Forall2_inv_head Htys) Hp)).
    rewrite <- compile_simplify in Hopt.
    destruct (compile _ _ _ _ rl); erewrite simplify_match_eq  with (Hty2:=Hp) in Hopt; assumption.
  - (*P is nil*) intros. reflexivity.
  - (*P not nil, ts is nil*) intros ps a P' Hdisj Htys Hp.
    simpl in *. unfold matches_matrix_tms. simp terms_to_hlist. simp matches_matrix. simpl.
    destruct ps as [| phd ptl].
    + simp matches_row. intros. unfold extend_val_with_list. simpl. apply gen_rep_irrel.
    + (*Cannot have non-null row in this case*)
      exfalso.
      apply pat_matrix_typed_head in Hp.
      destruct Hp as [Hrow _]; inversion Hrow.
  - (*Ill-typed (populate_all or dispatch don't give Some)*)
    intros t ty tl rl css is_constr Hsimp [Hpop | Hdisj] Hdisj1.
    + unfold populate_all in Hpop.
      destruct (get_heads rl) as [l|] eqn : Hget.
      * (*Case 1: [get_heads] is Some, [fold_left_opt] is None*)
        simpl. intros Htyps Hp.
        apply fold_left_opt_none in Hpop.
        destruct Hpop as [ps1 [p [ps2 [acc1 [Hl [Hfold Hpop]]]]]].
        subst. apply populate_none_simpl in Hpop.
        2: {
          apply (get_heads_simplified rl (ps1 ++ p :: ps2)); auto.
          rewrite in_app_iff; simpl; auto.
        }
        (*Idea: contradiction, by None we found a constructor in 1st column that is
          not [is_constr]. But by tying, it has to be*)
        destruct Hpop as [c [tys [ps [Hpeq Hnotconstr]]]]; subst.

        assert (Htyp: pattern_has_type gamma (Pconstr c tys ps) ty). {
          eapply in_get_heads_tys. apply Hp. apply Hget.
          rewrite !in_app_iff; simpl; auto.
        }
        (*The contradiction*)
        assert (Hconstr: is_constr c). {
          unfold is_constr. unfold css.
          inversion Htyp; subst.
          unfold sigma.
          destruct H11 as [m [a [m_in [a_in c_in]]]].
          rewrite (adt_constr_ret gamma_valid m_in a_in c_in).
          rewrite ty_subst_cons.
          unfold get_constructors.
          assert (Hts: find_ts_in_ctx gamma (adt_name a) = Some (m, a)). {
            apply find_ts_in_ctx_iff; auto.
          }
          rewrite Hts.
          apply In_in_bool.
          apply constr_in_adt_eq. exact c_in.
        }
        rewrite Hnotconstr in Hconstr; discriminate.
      * (*Second typing contradiction: if get_heads is None*)
        (*By typing, cannot have an empty pattern list in a row*)
        apply get_heads_none_iff in Hget. intros Htys Hp.
        rewrite (pat_matrix_typed_not_null Hp) in Hget.
        discriminate.
    + (*Final typing contradiction - dispatch1_opt is None, same as previous.*)
      intros Htyps Hp. simpl in *.
      destruct Hdisj as [types_cslist [Hpop Hdisp]].
      apply dispatch1_opt_none in Hdisp.
      rewrite (pat_matrix_typed_not_null Hp) in Hdisp.
      discriminate.
  - (*The interesting case*)
    intros t ty tl rl css is_constr Hsimp types_cslist Hpop types cslist casewild
      Hdisp cases wilds IH Hdisj Htmtys Hp. simpl in Htmtys.
    set (comp_wilds := fun (_: unit) => compile get_constructors gen_match gen_let tl
      wilds) in *.
    set (comp_cases := fun cs (al : list (term * vty)) =>
          match (amap_get funsym_eq_dec cases cs ) as o return amap_get funsym_eq_dec cases cs = o -> _ with
            | None => fun _ => None (*impossible*)
            | Some l => fun Hget => compile get_constructors gen_match gen_let (rev al ++ tl) l
            end eq_refl).
    (*A bit more simplified, start with this - try to simplify add or comp_full*)
    set (no_wilds := forallb (fun f => amap_mem funsym_eq_dec f types) css) in *. simpl.
    set (base := if no_wilds then Some [] else
      match comp_wilds tt with
      | Some x => Some [(Pwild, x)]
      | None => None
      end) in *.
    set (add := fun acc (x: funsym * list vty * list pattern) =>
          let '(cs, params, ql) := x in
          (*create variables*)
          let pat_tys :=  (map (ty_subst (s_params cs) params) (s_args cs)) in
          let new_var_names := GenElts.gen_vars (length ql) (tm_fv t ++ tm_bnd t) in
          let typed_vars := map (fun '(x, y) => (fst x, y)) (combine new_var_names pat_tys) in
          let vl := rev typed_vars in 
          let pl := rev_map Pvar vl in
          let al := rev_map Tvar vl in
          match (comp_cases cs (combine al (map snd vl))) with
          | None => None
          | Some v => Some ((Pconstr cs params pl, v) :: acc)
          end) in *.
    set (comp_full:=
        match base with
        | Some b =>
          match (fold_left_opt add cslist b) with
          | Some b1 => Some (gen_match t ty b1)
          | None => None
          end
        | None => None
        end) in *.
    destruct IH as [IHwilds IHconstrs].
    assert (Hwilds: wilds = default rl). {
      unfold wilds.
      apply dispatch1_opt_some in Hdisp.
      destruct Hdisp as [Hnotnull Hcasewild]; subst.
      rewrite dispatch1_equiv_default; auto.
    }
    (*Might as well prove hypotheses for IH now*)
    prove_hyp IHwilds.
    {
      rewrite Hwilds.
      eapply disj_default; eauto.
    }
    assert (Htywild: pat_matrix_typed (map snd tl) wilds). {
      rewrite Hwilds. eapply default_typed; eauto.
    }
    specialize (IHwilds (Forall2_inv_tail Htmtys) Htywild).
    (*Case 1: types is empty*)
    destruct (amap_is_empty types) eqn : Htypesemp.
    {
      (*We know:
        1. All elements are Pwild in first column
        2. No matter what type ty is, it cannot be a constructor that is in the first column.
        3. Thus, we can use either of our default lemmas*)
      destruct (is_vty_adt gamma ty) as [[[m a] args]|] eqn : Hisadt.
      - (*case 1: ADT. Know constructor not in first column*)
        assert (args_len: length args = length (m_params m)). {
          apply adt_vty_length_eq in Hisadt; auto.
          clear -Htmtys.
          apply Forall2_inv_head in Htmtys.
          apply has_type_valid in Htmtys; auto.
        }
        apply is_vty_adt_some in Hisadt.
        destruct Hisadt as [Hty [a_in m_in]]; subst.
        destruct (find_semantic_constr t m_in a_in args_len (Forall2_inv_head Htmtys))
        as [f [[c_in al] Hrep]].
        simpl in Hrep.
        assert (Hnotin: constr_at_head_ex f rl = false).
        {
          destruct (constr_at_head_ex f rl) eqn : Hconstr; auto.
          apply (populate_all_in _ _ _ _ Hsimp Hpop) in Hconstr.
          unfold types in Htypesemp.
          assert (Hconstrf: amap_mem funsym_eq_dec f (fst types_cslist) = false).
            apply amap_is_empty_mem; auto.
          rewrite Hconstrf in Hconstr; discriminate.
        }
        (*Now we apply default lemma 1*)
        unfold comp_wilds. simpl in Hdisj.
        assert (constrs_len: length (s_params f) = length args).
        {
          rewrite args_len. f_equal. apply (adt_constr_params gamma_valid m_in a_in c_in).
        }
        rewrite (default_match_eq _ m_in a_in c_in args_len constrs_len (Forall2_inv_head Htmtys) al Hrep _ 
          _ Htmtys rl Hsimp Hnotin Hp (default_typed Hp)).
        (*And use IH about wilds*)
        revert IHwilds.
        unfold matches_matrix_tms.
        generalize dependent Htywild.
        rewrite Hwilds.
        intros Htywild.
        rewrite matches_matrix_irrel with (Hty2:=(default_typed Hp)).
        auto.
      - (*Case 2: not ADT at all. Similar but use second default lemma*)
        rewrite (default_match_eq_nonadt _ _ (Forall2_inv_head Htmtys) Hisadt _ _ Htmtys
          rl Hsimp Hp (default_typed Hp)).
        revert IHwilds.
        unfold comp_wilds.
        unfold matches_matrix_tms.
        generalize dependent Htywild.
        rewrite Hwilds.
        intros Htywild.
        rewrite matches_matrix_irrel with (Hty2:=(default_typed Hp)).
        auto.
    }
    (*Now that we know that [types] is non-empty, we know that there is at least
      one constructor in the first column. By typing, ty is an ADT*)
         

(*TODO: either prove separately that [compile] is well-typed (maybe easier) or 
  have "exists" in theorem*)



End PatProofs.