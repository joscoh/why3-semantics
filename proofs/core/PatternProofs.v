Require Import Pattern.
Require Import Denotational.
Require Import Coq.Sorting.Permutation.
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
  rewrite (hlist_inv h1), hlist_app_equation_2. reflexivity.
Qed. 

Lemma hlist_tl_app1 {A: Type} {f: A -> Type} hd l1 l2 h1 h2:
  hlist_tl (hlist_app f (hd :: l1) l2 h1 h2) =
  (hlist_app f l1 l2 (hlist_tl h1) h2).
Proof.
  rewrite (hlist_inv h1), hlist_app_equation_2. reflexivity.
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
  rewrite terms_to_hlist_equation_4. reflexivity.
Qed.

Lemma terms_to_hlist_irrel ts tys H1 H2:
  terms_to_hlist ts tys H1 = terms_to_hlist ts tys H2.
Proof.
  revert tys H1 H2. induction ts as [| tm ts IH]; simpl; intros [| ty1 tys];
  intros Hall1 Hall2; auto; try solve[inversion Hall1].
  rewrite !terms_to_hlist_equation_4. 
  rewrite term_rep_irrel with (Hty2:=(Forall2_inv_head Hall2)).
  f_equal. apply IH.
Qed.

Lemma matches_row_irrel tys h ps Hr1 Hr2:
  matches_row tys h ps Hr1 = matches_row tys h ps Hr2.
Proof.
  revert Hr1 Hr2.
  revert ps.
  induction tys as [| ty tys IH]; intros.
  - assert (Hlen:=row_typed_length Hr1). destruct ps; try discriminate.
    rewrite !matches_row_equation_1; reflexivity.
  - assert (Hlen:=row_typed_length Hr1). destruct ps as [| phd ptl]; try discriminate.
    rewrite !matches_row_equation_4, match_val_single_irrel with (Hval2:=(Forall2_inv_head Hr2)).
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
  rewrite matches_row_equation_4. simpl.
  rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hrow)).
  destruct_match_single m1 Hmatch1; auto.
  rewrite IH with (Hrow:=(Forall2_inv_tail Hrow)).
  reflexivity.
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

(*(TODO: prove simplify later)*)

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
    intros. subst. rewrite matches_row_equation_1. simpl.
    rewrite hlist_app_equation_1, option_bind_id.
    assert (e = eq_refl) by (apply UIP_dec, list_eq_dec, sort_eq_dec).
    subst. unfold cast_arg_list; simpl.
    apply matches_row_irrel.
  - intros [| phd ps1] Hlen1; try discriminate. intros. subst. simpl.
    rewrite !matches_row_equation_4.
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
  try solve[inversion Hty1].
  - unfold opt_related. rewrite !matches_row_equation_1. apply Permutation_refl.
  - unfold opt_related.
    rewrite matches_row_equation_4.
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
      rewrite hlist_rev_equation_2. simpl.
      apply cast_arg_list_eq.
    }
    rewrite matches_row_equation_4. rewrite matches_row_equation_1. simpl.
    (*Using the IH is a bit complicated*)
    unfold option_bind.
    specialize (IH (hlist_tl al) ps (Forall2_inv_tail Hty1) Hrowrev (eq_sym (map_rev (v_subst vt) tys))).
    unfold opt_related in IH.
    (*Now lots of destructing*)
    destruct (matches_row tys (hlist_tl al) ps
      (Forall2_inv_tail Hty1)) as [m1|] eqn : Hmatch1.
    + destruct (matches_row (rev tys)
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
    + destruct (matches_row (rev tys)
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
  rewrite matches_row_equation_4. simpl in Hall.
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
  induction P as [| rhd rtl].
  - intros. simpl. rewrite !matches_matrix_equation_1. reflexivity.
  - intros. simpl. rewrite !matches_matrix_equation_2.
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
    + assert (Htyph:=Htyp). apply pat_matrix_typed_head in Htyph.
      simpl in Htyph. destruct Htyph as [Hrow _]; inversion Hrow. 
    + destruct phd as [| f' params tms | | |]; try discriminate.
      * (*Interesting case: Pconstr*) 
        revert Htyp'. simpl.

        (*Info from typing*)
        assert (Htyt:=pat_matrix_typed_head Htyp).
        destruct Htyt as [Htyr Htyt]; simpl in Htyr.
        assert (Htyconstr:=Forall2_inv_head Htyr).
        assert (Hlentms: length (s_args f') = length tms) by (inversion Htyconstr; auto).

        destruct (funsym_eqb_spec f' c); subst; simpl; intros.
        -- rewrite matches_matrix_equation_2. simpl.
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
          rewrite matches_row_equation_4. 
          rewrite terms_to_hlist_equation_4. simpl hlist_hd. 
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
              rewrite terms_to_hlist_equation_4.
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
            rewrite terms_to_hlist_equation_4.
            erewrite terms_to_hlist_irrel; reflexivity. Unshelve. auto.
        -- (*funsym doesn't match - here, we do not have a match with the [match_val_single]*)
          rewrite matches_row_equation_4.
          (*Use nomatch result*)
          rewrite terms_to_hlist_equation_4. simpl hlist_hd. 
          rewrite match_val_single_constr_nomatch with (m_in := m_in) (a_in:=a_in)(c1_in:=c_in)
            (args_len:=args_len)(al1:=al1)(Hty:=Hty); auto.
          simpl.
          (*Thus, IH case*)
          erewrite <- IHrtl with (Htyp:=(pat_matrix_typed_tail Htyp))(Htsty:=Htsty); [| apply 
                (simplified_tl _ _ Hpsimp)].
          rewrite terms_to_hlist_equation_4.
          erewrite terms_to_hlist_irrel; reflexivity. Unshelve. auto.
      * (*Pwild case*) 
        (*Idea: we add n terms and n wilds, that is the same (always matches) as 1 term and 1 wild*)
        rewrite matches_row_equation_4. simpl.
        rewrite matches_matrix_equation_2.
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
  induction P as [| rhd rtl].
  - intros. simpl. rewrite !matches_matrix_equation_1. reflexivity.
  - intros. simpl. rewrite !matches_matrix_equation_2.
    destruct rhd as [ps a1]; simpl.
    (*Case on patterns*)
    destruct ps as [| phd ptl].
    + assert (Htyph:=Htyp). apply pat_matrix_typed_head in Htyph.
      simpl in Htyph. destruct Htyph as [Hrow _]; inversion Hrow. 
    + destruct phd as [| f' params tms | | |]; try discriminate.
      * (*Pconstr*)
        simpl in c_notin. apply orb_false_iff in c_notin.
        unfold constr_at_head in c_notin.
        simpl in c_notin.
        destruct c_notin as [c_eq c_notin].
        destruct (funsym_eqb_spec f' c); try discriminate.
        rewrite matches_row_equation_4.
        (*Use fact that different constructor gives None*)
        rewrite terms_to_hlist_equation_4 at 1. simpl hlist_hd.
        rewrite match_val_single_constr_nomatch with (m_in:=m_in)(a_in:=a_in)(c1_in:=c_in)
          (args_len:=args_len)(Hty:=Hty)(al1:=al1); auto.
        simpl. apply IHrtl; auto.
      * (*Pwild*)
        rewrite matches_row_equation_4. simpl.
        rewrite terms_to_hlist_tl.
        rewrite matches_matrix_equation_2. simpl.
        rewrite terms_to_hlist_irrel with (H2:=f).
        rewrite matches_row_irrel with (Hr2:=(Forall_inv (proj1 Htyp'))). simpl.
        simpl in *.
        unfold option_bind.
        match goal with |- context [matches_row ?tys ?hl ?ptl ?H] =>
          destruct (matches_row tys hl ptl H) as [m1|] eqn : Hmatch1
        end.
        -- (*TODO: why do we need to do this?*)
          match goal with |- context [matches_row ?tys ?hl ?ptl ?H] =>
            replace (matches_row tys hl ptl H) with (Some m1) by (apply Hmatch1); auto
          end.
          f_equal. apply gen_rep_irrel.
        -- match goal with |- context [matches_row ?tys ?hl ?ptl ?H] =>
            replace (matches_row tys hl ptl H) with (@None (list (vsymbol * {s: sort & domain (dom_aux pd) s }))) by (apply Hmatch1); auto
          end.
Qed.

End SpecDefaultLemmas.
End PatProofs.