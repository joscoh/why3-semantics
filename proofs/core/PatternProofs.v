Require Import Pattern.
Require Import Denotational.

Section PatProofs.

Context {gamma: context} (gamma_valid: valid_context gamma).
Context (pd: pi_dom) (pf: pi_funpred gamma_valid pd) (vt: val_typevar).
Variable (v: val_vars pd vt).
Variable (b: bool). (*Generic over terms and formulas*)
Variable (ret_ty : gen_type b). (*The return type of the values*)

(*First, we define the semantics of multiple pattern matching*)
Section MultipleMatchSemantics.

(*Generalized term/formula rep*)
Definition gen_rep (v: val_vars pd vt) (ty: gen_type b) (d: gen_term b) (Hty: gen_typed b d ty) : gen_ret pd vt b ty :=
  match b return forall (ty: gen_type b) (dat: gen_term b), 
    gen_typed b dat ty -> gen_ret pd vt b ty with
  | true => fun ty dat Hty => term_rep gamma_valid pd vt pf v dat ty Hty
  | false => fun ty dat Hty => formula_rep gamma_valid pd vt pf v dat Hty
  end ty d Hty.

Definition pat_matrix := list (list pattern * gen_term b).


(*Typing for row*)
Definition row_typed (tys: list vty) (p: list pattern) : Prop :=
  Forall2 (fun p t => pattern_has_type gamma p t) p tys.

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

End MultipleMatchSemantics.

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

(*TODO: move*)
Equations hlist_app {A: Type} (f: A -> Type) (l1 l2: list A) (h1: hlist f l1) (h2: hlist f l2):
  hlist f (l1 ++ l2) :=
  hlist_app f nil l2 h1 h2 := h2;
  hlist_app f (x :: l1) l2 (HL_cons _ a1 htl) h2 := HL_cons _ _ _ a1 (hlist_app f l1 l2 htl h2).

Equations hlist_rev {A: Type} (f: A -> Type) (l: list A) (h: hlist f l) : hlist f (rev l) :=
  hlist_rev f nil h := h;
  hlist_rev f (x :: t) (HL_cons _ a1 htl) := hlist_app f (rev t) [x] (hlist_rev f t htl) 
    (HL_cons _ _ _ a1 (HL_nil _)).

(*Is there a better way to do this without all the casting, etc*)

(*An easy cast, just a bunch of maps, revs, and apps together*)
Lemma spec_prop_cast params sargs args tys : (map (v_subst vt)
  (rev
  (sorts_to_tys
  (ty_subst_list_s params (map (v_subst vt) args)
  sargs)) ++
tys)) = (rev (ty_subst_list_s params  (map (v_subst vt) args) sargs)) ++
map (v_subst vt) tys.
Proof.
  unfold sorts_to_tys, ty_subst_list_s. rewrite !map_map, !map_app, !map_rev, !map_map.
  f_equal. f_equal. apply map_ext. intros. rewrite <- subst_sort_eq; reflexivity.
Qed. 

Set Bullet Behavior "Strict Subproofs".

Lemma row_typed_length {tys ps}:
  row_typed tys ps ->
  length tys = length ps.
Proof.
  unfold row_typed. intros Hall2.
  apply Forall2_length in Hall2; auto.
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

Ltac destruct_match_single l Hmatch :=
  match goal with |- context [match_val_single ?v ?pd ?vt ?ty ?phd ?H1 ?h1] =>
      destruct (match_val_single v pd vt ty phd H1 h1) as [l|] eqn : Hmatch; simpl
    end.

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

Lemma hlist_app_cast1 {f: sort -> Set} (l1 l2 l3: list sort) (h: arg_list f l1) h2 (Heq: l1 = l2):
  hlist_app f l2 l3 (cast_arg_list Heq h) h2 =
  cast_arg_list (f_equal (fun x => x ++ l3) Heq) (hlist_app f l1 l3 h h2).
Proof.
  subst. simpl. unfold cast_arg_list; simpl. reflexivity.
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

Lemma row_typed_rev tys ps:
  row_typed tys ps ->
  row_typed (rev tys) (rev ps).
Proof.
  apply Forall2_rev.
Qed.

Lemma Forall2_combine {A B: Type} (P: A -> B -> Prop) (l1 : list A) (l2: list B):
  Forall2 P l1 l2 <-> length l1 = length l2 /\ Forall (fun x => P (fst x) (snd x)) (combine l1 l2).
Proof.
  split.
  - intros Hall. induction Hall; simpl; auto.
    destruct IHHall as [Hlen IHall].
    split; auto.
  - revert l2. induction l1 as [| h1 t1 IH]; intros [| h2 t2]; simpl; intros [Hlen Hall]; try discriminate; auto.
    inversion Hall; subst.
    constructor; auto.
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

(*Lemma constr_typed_row c params tms ts args:
  pattern_has_type gamma (Pconstr c params tms) (vty_cons ts args) ->
  row_typed (sorts_to_tys (ty_subst_list_s (s_params c) (map (v_subst vt) args) (s_args c))) tms.
Proof.
  intros Hty. inversion Hty; subst.
  apply Forall2_combine. split.
  - unfold sorts_to_tys, ty_subst_list_s. rewrite !map_map, map_length. auto.
  - rewrite Forall_forall. intros x Hinx. apply H9.
    replace (map (ty_subst (s_params c) params) (s_args c)) with
      (sorts_to_tys (ty_subst_list_s (s_params c) (map (v_subst vt) args) (s_args c))); auto.
    unfold ty_subst_list_s, sorts_to_tys. rewrite !map_map.
    revert Hinx.
  Search Forall2 combine.*)

Lemma terms_to_hlist_hd t ts ty tys Hty:
  hlist_hd (terms_to_hlist (t :: ts) (ty :: tys) Hty) =
  term_rep gamma_valid pd vt pf v t ty (Forall2_inv_head Hty).
Proof.
  rewrite terms_to_hlist_equation_4. reflexivity.
Qed.

(*One more lemma we need: if we have a constructor which matches,
  then [match_val_single] is the same as [matches_row] on the argument list*)
(* Lemma match_val_single_constr_row *)
Lemma match_val_single_constr_row 
  (t: term) {m: mut_adt} (m_in : mut_in_ctx m gamma)
  {a: alg_datatype} (a_in: adt_in_mut a m) {c: funsym} (c_in: constr_in_adt c a) 
  {args: list vty} (args_len: length args = length (m_params m))
  (Hty: term_has_type gamma t (vty_cons (adt_name a) args))
  (al1: arg_list (domain (dom_aux pd)) (sym_sigma_args c (map (v_subst vt) args)))
  (Ht: tm_semantic_constr t m_in a_in c_in args_len Hty al1)
  params tms 
  (Hp :  pattern_has_type gamma (Pconstr c params tms) (vty_cons (adt_name a) args)) 
  (Hty1 : term_has_type gamma t (vty_cons (adt_name a) args)) 
  (Heq : sym_sigma_args c (map (v_subst vt) args) = map (v_subst vt)
    (sorts_to_tys (ty_subst_list_s (s_params c) (map (v_subst vt) args) (s_args c)))) 
  (Hrow: row_typed (sorts_to_tys (ty_subst_list_s (s_params c) (map (v_subst vt) args)
    (s_args c))) tms):
  match_val_single gamma_valid pd vt (vty_cons (adt_name a) args) (Pconstr c params tms) Hp 
    (term_rep gamma_valid pd vt pf v t (vty_cons (adt_name a) args) Hty1) =
  matches_row (sorts_to_tys 
    (ty_subst_list_s (s_params c) (map (v_subst vt) args) (s_args c)))
    (cast_arg_list Heq al1) tms Hrow.
Admitted.

Definition opt_related {A B: Type} (P: A -> B -> Prop) (o1: option A) (o2: option B) : Prop :=
  match o1, o2 with
  | Some x, Some y => P x y
  | None, None => True
  | _, _ => False
  end.

  Require Import Coq.Sorting.Permutation.

(*The relationship is annoying: they are permutations*)
Lemma matches_row_rev tys al ps Hty1 Hty2:
  opt_related (@Permutation _) 
    (matches_row tys al ps Hty1)
    (matches_row (rev tys) 
    (cast_arg_list (eq_sym (map_rev _ _)) (hlist_rev _ _ al)) (rev ps) Hty2).
Proof.
  (*TODO: generalize e?*)
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
    (*Damn it, do we have to reason more concretely about reversal - e.g. list is reversed
      or whatever?*)
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

Lemma spec_prop 
  (*Info about first term*)
  (t: term) {m: mut_adt} (m_in : mut_in_ctx m gamma)
  {a: alg_datatype} (a_in: adt_in_mut a m) {c: funsym} (c_in: constr_in_adt c a) 
  {args: list vty} (args_len: length args = length (m_params m))
  (Hty: term_has_type gamma t (vty_cons (adt_name a) args))
  (al1: arg_list (domain (dom_aux pd)) (sym_sigma_args c (map (v_subst vt) args)))
  (Ht: tm_semantic_constr t m_in a_in c_in args_len Hty al1)
  (*Info about rest of terms*)
  (ts: list term) (tys: list vty) (al2: arg_list (domain (dom_aux pd)) (map (v_subst vt) tys))
  (Htsty: Forall2 (term_has_type gamma) (t :: ts) (vty_cons (adt_name a) args :: tys)) (*duplicate proof for irrelevance*)
  (*Info about pattern matrix*)
  (P: pat_matrix) (Hpsimp: simplified P) (*(Hc: constr_at_head_ex c P)*) (*TODO: don't think we need - SEEE*)
  (Htyp: pat_matrix_typed (vty_cons (adt_name a) args :: tys) P)
  (Htyp': pat_matrix_typed (rev (sorts_to_tys (ty_subst_list_s (s_params c) (map (v_subst vt) args) (s_args c))) ++ tys)
    (spec P c)):

  matches_matrix_tms (t :: ts) (vty_cons (adt_name a) args :: tys) P
    Htsty Htyp =

  matches_matrix 
  (*Type list more complicated: args of c + rest*)
  (rev (sorts_to_tys (ty_subst_list_s (s_params c) (map (v_subst vt) args) (s_args c))) ++ tys)
    (cast_arg_list (eq_sym (spec_prop_cast (s_params c) (s_args c) args tys))
   (hlist_app _ _ _ (hlist_rev _ _ al1) (terms_to_hlist ts tys (Forall2_inv_tail Htsty))))
    (spec P c) Htyp'.
Proof.
  unfold matches_matrix_tms.
  generalize dependent (eq_sym (spec_prop_cast (s_params c) (s_args c) args tys)).
  generalize dependent (Forall2_inv_tail Htsty).
  revert Htsty Htyp Htyp'.
  unfold matches_matrix_tms. (*TODO: get [matches_matrix_elim] to work?*)
  induction P as [| rhd rtl].
  - intros. simpl. rewrite !matches_matrix_equation_1. reflexivity.
  - intros. simpl. rewrite !matches_matrix_equation_2.
    destruct rhd as [ps a1]; simpl.
    (*Case on patterns*)
    destruct ps as [| phd ptl].
    + (*TODO: prove that we cannot have nil row in matrix if well-typed*) admit.
    + destruct phd as [| f' params tms | | |]; try discriminate.
      * (*Interesting case: Pconstr*)
        revert Htyp'. simpl.
        destruct (funsym_eqb_spec f' c); subst; simpl; intros.
        (*TODO: need to decompose [matches_matrix] for app (matches_matrix (tys1 ++ tys2) (hlist_app h1 h2)
          = matches_matrix tys1 h1 && matches_matrix tys2 h2 (assuming lengths are correct and && = option bind)
          then prove that the first one is equal to this [matches_row]
          )*)
        -- rewrite matches_matrix_equation_2. simpl.
        (*Above is wrong - need to just decompose [matches_row] in way described above
          and then prove that [match_val_single] in constr case (assuming we know constr matches)
          is equal to [matches_row] for that given arg list - result follows from this*)
          assert (Heq1: rev (sym_sigma_args c (map (v_subst vt) args)) =
            map (v_subst vt) (rev (sorts_to_tys (ty_subst_list_s (s_params c)
              (map (v_subst vt) args) (s_args c))))).
          {
            unfold sym_sigma_args, ty_subst_list_s, sorts_to_tys.
            rewrite !map_map. rewrite map_rev, !map_map. f_equal.
            apply map_ext. intros. rewrite <- subst_sort_eq; reflexivity.
          }
          (*TODO: better ways to do this*)
          assert (Htyt:=pat_matrix_typed_head Htyp).
          destruct Htyt as [Htyr Htyt]; simpl in Htyr.
          assert (Htyconstr:=Forall2_inv_head Htyr).
          assert (Hlentms: length (s_args c) = length tms) by (inversion Htyconstr; auto).

          (*Get [row_typed] info*)
          assert (Hr1:=pat_matrix_typed_head Htyp'). simpl in Hr1.
          destruct Hr1 as [Hr1 _].
          apply Forall2_app_inv in Hr1.
          2: {  unfold sorts_to_tys, ty_subst_list_s.
            rewrite !rev_length, !map_length. auto. }
          destruct Hr1 as [Hrow1 Hrow2].
          (*Now finally, we can split the [app]*)
          rewrite matches_row_app with(h1:=cast_arg_list Heq1 (hlist_rev _ _ al1))(h2:=terms_to_hlist ts tys f)
            (Hr2:=Hrow1)(Hr3:=Hrow2).
          (*We prove the easy goals first*)
          2: rewrite hlist_app_cast1, cast_arg_list_compose; apply cast_arg_list_eq.
          2: unfold sorts_to_tys, ty_subst_list_s; rewrite !map_map, !rev_length, map_length; auto.
          2: symmetry; apply (Forall2_length (Forall2_inv_tail Htyr)).

          (*Now we need to transform the [matches_row] into the corresponding
            [match_val_single] and the rest of the row; we then prove that
            [match_val_single] for a constructor is equivalent to [matches_row] 
            on the arg_list*)
          rewrite matches_row_equation_4. 
          rewrite terms_to_hlist_equation_4. simpl hlist_hd. 
          assert (Heq2: sym_sigma_args c (map (v_subst vt) args) =
            map (v_subst vt)
              (sorts_to_tys
              (ty_subst_list_s (s_params c) (map (v_subst vt) args)
              (s_args c)))).
          {
            unfold sym_sigma_args, sorts_to_tys, ty_subst_list_s.
            rewrite !map_map. apply map_ext.
            intros. rewrite <- subst_sort_eq; auto.
          }
          rewrite match_val_single_constr_row with (m_in:=m_in) (a_in:=a_in) (c_in:=c_in)
            (args_len:=args_len)(al1:=al1) (Hrow:= Forall2_rev_inv Hrow1)(Hty:=Hty)(Heq:=Heq2); auto.
          (*Need to prove that matches_row tys al ps Hty = 
              matches_row (rev tys) (hlist_rev al) (rev ps) (Forall2_rev Hty)*)
          Unshelve.


          
        (*TODO: prove that match_val_single, in constr_case (if equal) is equal to
          matches_row*)


      * try discriminate. (*Pvar case*) rewrite matches_row_equation_4.

    (*Really, what we want to prove:
      Suppose that (t :: ts) matches row r*)


    rewrite terms_to_hlist_equation_4.
    destruct ps as [| phd ptl].
    + (*TODO: prove that we cannot have nil row in matrix if well-typed*) admit.
    + rewrite matches_row_equation_4.
      (*Think we need a different lemma*)
      destruct phd.
      * simpl.
      unfold match_val_single at 1.
      (*Core of the proof: *)
    
    
   rewrite (matches_row_equation_4 (vty_cons (adt_name a) args) tys
      (HL_cons (domain (dom_aux pd))
  (v_subst vt (vty_cons (adt_name a) args))
  (map (v_subst vt) tys)
  (term_rep gamma_valid pd vt pf v t
  (vty_cons (adt_name a) args) (Forall2_inv_head Htsty))
  (terms_to_hlist ts tys (Forall2_inv_tail Htsty)))).
    (*Probably need: if matches_row *)

    Check matches_row_equation_4.
    rewrite matches_row_equation_4.

    simpl in Hc. unfold constr_at_head in Hc.


  
   unfold matches_matrix_tms.
    Search matches_matrix.
    simpl.
    Print matches_matrix.



  generalize dependent Hty. Htysty.



has type
"hlist (domain (dom_aux pd))
  (rev (sym_sigma_args c (map (v_subst vt) args)) ++
map (v_subst vt) tys)"
while it is expected to have type
"arg_list (domain (dom_aux pd))
  (map (v_subst vt)
  (sorts_to_tys
  (ty_subst_list_s (s_params c) (map (v_subst vt) args)
  (s_args c)) ++
tys))".




Definition matches_matrix_tms (tms: list term) (tys: list vty) (P: pat_matrix)
  (Hty: Forall2 (term_has_type gamma) tms tys)
  (Hp: pat_matrix_typed tys P) : option (gen_ret pd vt b ret_ty) :=
  matches_matrix tys (terms_to_hlist tms tys Hty) P Hp.




(tl: list term) (c: funsym) (ty1: vty) (tys1: list vty) 
  (al: arg_list (domain (dom_aux pd)) (map (v_subst vt) tys1))
  (P: pat_matrix)
  (Hsimp: simplified P)
  (Hc: constr_at_head_ex c P) Hty1 Htyp:
  
  matches_matrix (terms_to_hlist (t :: tl) (ty1 :: tys1) Hty1) P Htyp =
  matches_matrix (hlist_app (hlist_rev al) 


Lemma default_prop




(tys: list vty) 
  (al: arg_list (domain (dom_aux pd)) (map (v_subst vt) tys))
  (p: pat_matrix)
  (Hty: pat_matrix_typed tys p)