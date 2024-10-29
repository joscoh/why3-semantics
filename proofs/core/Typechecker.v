(*Separate file to use ssreflect*)
(* Require Export Typing. *)
Require Import CommonSSR.
Require Import TerminationChecker.

From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

(* General ssreflect helpful lemmas *)

Lemma eq_mem_In {A: eqType} (s1 s2: seq A):
  (forall x, In x s1 <-> In x s2) <-> s1 =i s2.
Proof.
  split.
  - move=> Hin x. case: (x \in s1) /inP => Hin1.
    symmetry. apply /inP. by apply Hin.
    case: (x \in s2) /inP =>//= Hin2.
    by apply Hin in Hin2.
  - move=> Heq x. 
    by split => /inP Hin; apply /inP; rewrite ?Heq // -Heq.
Qed.

(*Use this because we cannot assume eqType, so need In, not \in*)
Lemma all_forallb: forall {A: Type} (p: A -> bool) (l: seq A),
  all p l = forallb p l.
Proof.
  by [].
Qed.

Lemma all_Forall {A: eqType} (P: A -> Prop) (p: pred A) (s: seq A):
  (forall x, x \in s -> reflect (P x ) (p x)) ->
  reflect (Forall P s) (all p s).
Proof.
  move=> Hall. rewrite all_forallb.
  apply forallb_ForallP => x /inP. by apply Hall.
Qed.

Lemma forallP' {T: finType} (P: T -> Prop) (p: pred T):
  (forall x, reflect (P x) (p x)) ->
  reflect (forall x, P x) [forall x, p x].
Proof.
  move=> Hallrefl.
  have Halleq: (forall x, P x) <-> (forall x, p x). {
    split=> Hall x. by apply: (introT (Hallrefl x)) (Hall x).
    by apply: (elimT (Hallrefl x) (Hall x)).
  }
  case Hall: [forall x, p x].
  - apply: ReflectT. rewrite Halleq. by apply /forallP.
  - apply: ReflectF=>C. rewrite Halleq in C.
    have: [forall x, p x] by apply /forallP.
    by rewrite Hall.
Qed.

Definition sublistb {A: eqType} (l1 l2: seq A) : bool :=
  (all (fun x => x \in l2) l1).

Lemma sublistbP {A: eqType} (l1 l2: seq A):
  reflect (sublist l1 l2) (sublistb l1 l2).
Proof.
  rewrite /sublist/sublistb.
  eapply equivP.
  2: apply Forall_forall.
  apply all_Forall. move=> x Hinx.
  apply inP.
Qed.

(*maybe use instead of nodupb*)
Lemma uniqP {A: eqType} (l: list A):
  reflect (NoDup l) (uniq l).
Proof.
  elim: l => [//= | h t /= IH].
  - reflT.
  - eapply equivP. 2: symmetry; apply NoDup_cons_iff.
    apply andPP=>//.
    apply negPP. apply inP.
Qed.


(* A Verified Typechecker *)
(*TODO: replace nested fixes*)
Section Typechecker.

Fixpoint typecheck_type (gamma:context) (v: vty) : bool :=
  match v with
  | vty_int => true
  | vty_real => true
  | vty_var tv => true
  | vty_cons ts vs => 
      (ts \in (sig_t gamma)) &&
      (length vs == length (ts_args ts)) &&
      all (typecheck_type gamma) vs
  end.

(*"=i" is decidable. This would be much worse without
  ssreflect*)
Definition eq_memb {A: eqType} (s1 s2: seq A) : bool :=
  all (fun x => x \in s1) s2 &&
  all (fun x => x \in s2) s1.

Lemma eq_memb_spec {A: eqType} (s1 s2: seq A):
  reflect (s1 =i s2) (eq_memb s1 s2).
Proof.
  case Heq: (eq_memb s1 s2); move: Heq; rewrite /eq_memb.
  - move=> /andP[/allP Hins2 /allP Hins1].
    apply ReflectT => x.
    case Hinx1: (x \in s1).
    + symmetry. by apply Hins1.
    + case Hinx2: (x \in s2) =>//.
      move: Hinx1. by rewrite Hins2.
  - move=> Hall; apply negbT in Hall; constructor; move: Hall.
    rewrite negb_and => /orP[/allPn [x Hinx Hnotinx] C | 
      /allPn [x Hinx Hnotinx] C].
    + have: x \in s1 by rewrite C. by rewrite (negbTE Hnotinx).
    + have: x \in s2 by rewrite -C. by rewrite (negbTE Hnotinx).
Qed. 

(*Patterns can have many types, so we ask: can this pattern
  have this type? (ex: Pwild)*)

(*Decidable list intersection, may have duplicates*)
Definition seqI {A: eqType} (s1 s2: seq A) :=
  filter (fun x => x \in s2) s1.

Definition all_in_range (bound: nat) (p: nat -> bool) : bool :=
  forallb p (iota 0 bound).

Lemma iota_plus_1: forall x y,
  iota x (y.+1) = iota x y ++ [ :: (x + y)%N].
Proof.
  move => x y. by rewrite -addn1 iotaD /=.
Qed.

Lemma all_in_range_spec bound p P:
  (forall n, n < bound -> reflect (P n) (p n)) ->
  reflect (forall n, n < bound -> P n) (all_in_range bound p).
Proof.
  rewrite /all_in_range.
  elim: bound => [/=| n' IHn] => [Hrefl | Hrefl].
  - by apply ReflectT.
  - rewrite iota_plus_1 forallb_app/= andbT add0n.
    prove_hyp IHn.
    { move=> n Hn. apply Hrefl.
      by apply (ltn_trans Hn).
    }
    case: IHn=>//= Hall.
    + have Hr: reflect (P n') (p n') by apply Hrefl.
      case: Hr => Hn'/=.
      * apply ReflectT. move=> n. rewrite ltnS.
        rewrite leq_eqVlt => /orP[/eqP -> | Hlt]//=.
        by apply Hall.
      * apply ReflectF=> C.
        apply Hn'. by apply C.
    + apply ReflectF. move=> C.
      apply Hall. move=> x Hn. apply C.
      by apply (leq_trans Hn).
Qed.

Fixpoint typecheck_pattern (gamma: context) (p: pattern) (v: vty) : bool :=
  match p with
  | Pvar x => (v == (snd x)) && typecheck_type gamma (snd x)
  | Pwild => typecheck_type gamma v
  | Por p1 p2 => 
    typecheck_pattern gamma p1 v &&
    typecheck_pattern gamma p2 v &&
    (eq_memb (pat_fv p2) (pat_fv p1))
  | Pbind p x =>
    (v == (snd x)) &&
    (x \notin (pat_fv p)) &&
    (typecheck_pattern gamma p v)
  | Pconstr f params ps => 
    (v == ty_subst (s_params f) params (f_ret f)) &&
    (f \in (sig_f gamma)) &&
    all (fun x => typecheck_type gamma x) params &&
    (typecheck_type gamma (f_ret f)) &&
    (length ps == length (s_args f)) &&
    (length params == length (s_params f)) &&
    (*TODO: remove nested induction*)
    ((fix check_list (l1: list pattern) (l2: list vty) : bool :=
      match l1, l2 with
      | nil, nil => true
      | h1 :: t1, h2 :: t2 => typecheck_pattern gamma h1 h2 &&
        check_list t1 t2
      |  _, _ => false
       end) ps (map (ty_subst (s_params f) params) (s_args f))) &&
    (*Kind of an awkward encoding*)
    (all_in_range (length ps) (fun x =>
      all_in_range (length ps) (fun y =>
      (x != y) ==>
      null (seqI (pat_fv (nth Pwild ps x)) (pat_fv (nth Pwild ps y)))))) &&
    (is_funsym_constr gamma f)
  end.

(*Proofs of correctness*)

Local Lemma all_ForallT_reflect {A: Type} {P: A -> Prop} {b: A -> bool}
  (l: list A) (Hall: ForallT (fun x => reflect (P x) (b x)) l):
  reflect (forall x, In x l -> P x) (all b l).
Proof.
  intros. induction l; simpl.
  - apply ReflectT. intros; contradiction.
  - destruct (ForallT_hd _ _ _ Hall).
    2: { apply ReflectF; intro Con. specialize (Con a). auto. }
    simpl. destruct (IHl (ForallT_tl _ _ _ Hall)); simpl;
    [apply ReflectT | apply ReflectF]; auto.
    intros; destruct_all; subst; auto.
Qed.

Ltac refl_destruct_extra := idtac.

Ltac refl_destruct :=
  match goal with
    | |- context [?x \in ?l] => case: (inP x l); intros
    | |- context [?x == ?l] => case: (@eqP _ x l); intros
    | H: reflect ?P ?b |- context [?b] => destruct H; intros
    | H: forall (x: ?A), reflect (?P x) (?b x) |- context [ ?b ?y] =>
        destruct (H y); intros
    | H: ForallT (fun (x : ?A) => reflect (?P x) (?b x)) ?l |-
      reflect _ (all ?b ?l) => 
      destruct (all_ForallT_reflect l H); intros
  end + refl_destruct_extra.

Ltac reflect_step :=
  refl_destruct; simpl; try solve[reflF; contradiction].

Ltac simpl_reflect :=
  repeat (progress (reflect_step; simpl; subst)).

Ltac solve_reflect :=
  repeat progress(reflect_step; simpl; subst); reflT; auto.


Lemma typecheck_type_correct: forall (gamma: context) (v: vty),
  reflect (valid_type gamma v) (typecheck_type gamma v).
Proof.
  move=> gamma. apply vty_rect=>//=; try by intros; reflT.
  move=> ts vs Hty.
  solve_reflect.
Qed.

Ltac refl_destruct_extra1 := idtac.
Ltac refl_destruct_extra ::= 
  match goal with
  | |- reflect ?P (typecheck_type ?x ?y) =>
    destruct (typecheck_type_correct x y); intros; subst
  | |- reflect ?P (eq_memb ?x1 ?x2) =>  let H := fresh in 
    destruct (eq_memb_spec x1 x2) as [H|H]; [rewrite <- eq_mem_In in H|]
  end + refl_destruct_extra1.

Lemma typecheck_pattern_correct: forall (s: context) (p: pattern) (v: vty),
  reflect (pattern_has_type s p v) (typecheck_pattern s p v).
Proof.
  move=> s. apply 
    (pattern_rect (fun (p: pattern) => forall v, 
      reflect (pattern_has_type s p v) (typecheck_pattern s p v)))=>//=;
  try solve[intros; solve_reflect].
  - (*The hard case*)
    move=> f vs ps Hall v.
    case: (v == ty_subst (s_params f) vs (f_ret f)) /eqP => Hv/=; 
      subst; last by reflF.
    case: (f \in sig_f s) /inP => Hinf/=; last by reflF.
    case: (all [eta typecheck_type s] vs) 
      /(all_Forall _ _ _ (fun x _ => typecheck_type_correct s x)) => Hforall/=;
      last by reflF.
    case: (typecheck_type s (f_ret f)) /typecheck_type_correct => Hvalret; last by reflF.
    case: (length ps == length (s_args f)) /eqP => Hlenps/=; last by reflF.
    case: (length vs == length (s_params f)) /eqP => Hlenvs/=; last by reflF.
    (*Prove each of the last two conditions separately*)
    have Hfvs: reflect ((forall (i j : nat) (d : pattern) (x : vsymbol),
      (i < Datatypes.length ps)%coq_nat ->
      (j < Datatypes.length ps)%coq_nat ->
      i <> j ->
      ~
      (In x (pat_fv (List.nth i ps d)) /\
      In x (pat_fv (List.nth j ps d)))))
    (all_in_range (Datatypes.length ps)
    (fun x : nat =>
     all_in_range (Datatypes.length ps)
       (fun y : nat =>
        (x != y) ==> null (seqI (pat_fv (nth Pwild ps x)) (pat_fv (nth Pwild ps y)))))). {
        (*Have to prove manually*)
        case: (all_in_range_spec (length ps) _
          (fun i => forall j, (j < length ps) ->
            i <> j -> forall d x, ~ (In x (pat_fv (List.nth i ps d)) /\ In x (pat_fv (List.nth j ps d))))).
        - move=> n Hn.
          apply all_in_range_spec.
          move=> m Hm.
          apply implyPP. apply negPP. apply eqP.
          case: (nullP (seqI (pat_fv (nth Pwild ps n)) (pat_fv (nth Pwild ps m)))).
          + move=> /eqP. rewrite /seqI -(negbK (_ == _)) -has_filter => Hnone.
            apply ReflectT => d x [Hinx1 Hinx2].
            apply /negP. apply Hnone.
            apply /hasP. 
            by exists x; apply /inP; rewrite -nth_eq (nth_indep _ _ d) //;
            apply /ltP.
          + move /eqP. rewrite /seqI -has_filter => /hasP Hhas.
            apply ReflectF => C.
            case: Hhas => [x /inP Hinx1 /inP Hinx2].
            apply (C Pwild x);
            by rewrite !nth_eq.
        - move=> Hall1.
          apply ReflectT.
          move=> i j d x /ltP Hi /ltP Hj Hij. by apply Hall1.
        - move=> Hnotall.
          apply ReflectF => C.
          by apply Hnotall => x /ltP Hn j /ltP Hj Hneq d y;
          apply C.
    }        
    case: Hfvs => Hfreevars;[rewrite andbT | rewrite andbF]; last by
    reflF.
    rewrite andbC.
    case: (is_funsym_constr s f) /is_funsym_constr_correct => Hisadt/=;
    last by reflF.
    (*Now we just have the nested induction left*)
    apply iff_reflect. split.
    + move=> Hty. inversion Hty; subst. clear -H8 H5 Hall.
      move: H5 H8.
      move: Hall (s_params f) (s_args f) vs.
      elim: ps =>[//= Hall params [|] vs //| phd ptl /= IH Hall params 
        [// | ahd atl/=] vs [Hlen] Hforall].
      case: (typecheck_pattern s phd (ty_subst params vs ahd))
        /(ForallT_hd _ _ _  Hall) => Hhasty/=; last by
        exfalso; apply Hhasty; 
        apply (Hforall (phd, ty_subst params vs ahd));
        left.
      apply IH=>//. apply (ForallT_tl _ _ _ Hall).
      by move=> x Hinx; apply Hforall; right.
    + move => Hcheck. constructor=>//.
      clear -Hcheck Hall Hlenps.
      move: (s_params f) (s_args f) vs Hlenps Hall Hcheck.
      elim: ps => [//= | phd ptl /= IH params [// | ahd atl /=] vs [Hlen] Hall].
      case: (typecheck_pattern s phd (ty_subst params vs ahd))
      /(ForallT_hd _ _ _  Hall) => Hhasty//= Hcheck.
      move=> x [Hx/= | Hinx]; subst=>//=.
      by apply (IH _ _ _ Hlen (ForallT_tl _ _ _ Hall) Hcheck).
  - intros; simpl_reflect; [reflT | reflF]; auto; simpl in *.
    + intros; symmetry; auto.
    + apply H1. rewrite <- eq_mem_In; simpl; intros; symmetry; auto. 
Qed.

(*Terms and formulas*)
Fixpoint typecheck_term (s: context) (t: term) : option vty :=
  match t with
  | Tconst (ConstInt z) => Some vty_int
  | Tconst (ConstReal r) => Some vty_real
  | Tvar x => if typecheck_type s (snd x) then Some (snd x) else None
  | Tlet tm1 x tm2 => 
    if (typecheck_term s tm1) == Some (snd x) then
    typecheck_term s tm2 else None
  | Tif f tm1 tm2 =>
    if typecheck_formula s f then
    match (typecheck_term s tm1) with
    | Some ty1 => if typecheck_term s tm2 == Some ty1 then Some ty1 else None
    | None => None
    end else None
  | Tmatch tm ty1 ps =>
    if (typecheck_term s tm == Some ty1) &&
      all (fun x => typecheck_pattern s (fst x) ty1) ps &&
      isSome (Pattern.compile_bare_single true false tm ty1 ps)
    then 
      match ps with
      | nil => None
      | (pat, tm) :: tl =>
        match (typecheck_term s tm) with
        | Some ty2 =>
          (*Now we have ty2, so we can check that all terms have this*)
          if ((fix check_list (l: list (pattern * term)) : bool :=
           match l with
          | (pat, tm) :: tl => (typecheck_term s tm == Some ty2) && 
            check_list tl
          | nil => true
          end) ps) then Some ty2 else None
        | None => None
        end
      end
    else None
  | Tfun f params tms =>
    if (f \in (sig_f s)) &&
      all (typecheck_type s) params &&
      typecheck_type s (f_ret f) &&
      (length tms == length (s_args f)) &&
      (length params == length (s_params f)) &&
      ((fix typecheck_args (l1: list term) (l2: list vty) : bool :=
      match l1, l2 with
      | tm1 :: tl1, ty1 :: tl2 => 
        (typecheck_term s tm1 == Some ty1)
        && typecheck_args tl1 tl2
      | nil, nil => true
      | _, _ => false
      end) tms (List.map (ty_subst (s_params f) params) (s_args f)))
    then Some (ty_subst (s_params f) params (f_ret f))
    else None
  (*Function case*)

  | Teps f x => if typecheck_formula s f && typecheck_type s (snd x)
    then Some (snd x) else None
  end 
with typecheck_formula (s: context) (f: formula) : bool :=
  match f with
  | Ftrue => true
  | Ffalse => true
  | Fbinop b f1 f2 =>
    typecheck_formula s f1 && typecheck_formula s f2
  | Fnot f1 => typecheck_formula s f1
  | Fquant q x f1 =>
    typecheck_type s (snd x) &&
    typecheck_formula s f1
  | Fpred p params tms =>
      (p \in (sig_p s)) &&
      all (typecheck_type s) params &&
      (length tms == length (s_args p)) &&
      (length params == length (s_params p)) &&
      ((fix typecheck_args (l1: list term) (l2: list vty) : bool :=
      match l1, l2 with
      | tm1 :: tl1, ty1 :: tl2 => 
        (typecheck_term s tm1 == Some ty1)
        && typecheck_args tl1 tl2
      | nil, nil => true
      | _, _ => false
      end) tms (List.map (ty_subst (s_params p) params) (s_args p)))
  | Flet t x f1 =>
    (typecheck_term s t == Some (snd x)) &&
    typecheck_formula s f1
  | Fif f1 f2 f3 =>
    typecheck_formula s f1 &&
    typecheck_formula s f2 &&
    typecheck_formula s f3
  | Feq ty t1 t2 =>
    (typecheck_term s t1 == Some ty) &&
    (typecheck_term s t2 == Some ty)
  | Fmatch tm ty ps =>
    (*is_vty_adt s ty &&*)
    (typecheck_term s tm == Some ty) &&
    all (fun x => typecheck_pattern s (fst x) ty) ps &&
    isSome (Pattern.compile_bare_single false false tm ty ps) &&
    (* (~~ (null ps)) && *)
    ((fix check_list (l: list (pattern * formula)) : bool :=
      match l with
      | (pat, fm) :: tl => typecheck_formula s fm && 
        check_list tl
      | nil => true
      end) ps)
  end.

(*Now we prove the correctness of this*)
Lemma typecheck_term_fmla_spec (s: context): 
  forall (tm: term) (f: formula),
  (forall v, 
    reflect (term_has_type s tm v) (typecheck_term s tm == Some v)) *
  reflect (formula_typed s f) (typecheck_formula s f).
Proof.
  apply (term_formula_rect) with(P1:=fun tm => forall v,
    reflect (term_has_type s tm v) (typecheck_term s tm == Some v))
  (P2:= fun f => reflect (formula_typed s f) (typecheck_formula s f))=>/=.
  - move=> c v. case: c => [z | r].
    + by case: (Some vty_int == Some v) /eqP=> [[Hv] | Hneq]; 
      subst; [reflT | reflF].
    + by case: (Some vty_real == Some v) /eqP=> [[Hv] | Hneq]; 
      subst; [reflT | reflF].
  - move=> v ty2. 
    case: (typecheck_type s (snd v)) /typecheck_type_correct => Hval; 
    last by reflF.
    by case: (Some (snd v) == Some ty2) /eqP => [[Hv12] | Hneq]; subst;
    [reflT | reflF].
  - move=> f tys tms Hall1 v.
    case: (f \in sig_f s) /inP => Hinf/=; last by reflF.
    have Halltyps: forall x, x \in tys -> 
      reflect (valid_type s x) (typecheck_type s x) by move=> x _;
      apply typecheck_type_correct.
    case: (all (typecheck_type s) tys) /(all_Forall _ _ _ Halltyps) =>Halltys/=;
    last by reflF.
    rewrite {Halltyps}.
    case: (typecheck_type s (f_ret f)) /typecheck_type_correct => Hvalret/=;
    last by reflF.
    case: (length tms == length (s_args f)) /eqP => Hlentms/=; last by reflF.
    case: (length tys == length (s_params f)) /eqP => Hlentys/=; 
    last by reflF.
    have Hargs:
      Forall (fun x : term * vty => term_has_type s x.1 x.2)
      (combine tms (List.map (ty_subst (s_params f) tys) (s_args f))) <->
      (fix typecheck_args (l1 : seq term) (l2 : seq vty) {struct l1} : bool :=
      match l1 with
      | [::] => match l2 with
                | [::] => true
                | _ :: _ => false
                end
      | tm1 :: tl1 =>
          match l2 with
          | [::] => false
          | ty1 :: tl2 =>
              (typecheck_term s tm1 == Some ty1) && typecheck_args tl1 tl2
          end
      end) tms (List.map (ty_subst (s_params f) tys) (s_args f)). {
      clear -Hall1 Hlentms. 
      move: (s_args f) Hlentms Hall1. move: (ty_subst (s_params f) tys).
      elim: tms => [// sigma [|]//= | h t /= IH sigma [//| arg1 argtl/=] [Hlens] HallT].
      split.
      - move=> Hall.
        case: (typecheck_term s h == Some (sigma arg1)) 
          /(ForallT_hd _ _ _ HallT) => Hty/=; last by inversion Hall.
        apply IH=>//. by inversion HallT. by inversion Hall.
      - move => /andP[/(ForallT_hd _ _ _ HallT) Htyp Hargs ].
        constructor=>//. apply IH=>//.
        by inversion HallT.
    }
    apply iff_reflect. split.
    + move=> Hty. inversion Hty; subst. rewrite Hargs in H9.
      rewrite H9. by apply /eqP.
    + move: Hargs.
      case: ((fix typecheck_args (l1 : seq term) (l2 : seq vty) {struct l1} : bool :=
      match l1 with
      | [::] => match l2 with
                | [::] => true
                | _ :: _ => false
                end
      | tm1 :: tl1 =>
          match l2 with
          | [::] => false
          | ty1 :: tl2 =>
              (typecheck_term s tm1 == Some ty1) && typecheck_args tl1 tl2
          end
      end) tms (List.map (ty_subst (s_params f) tys) (s_args f))) => 
      Hargs /eqP // [Hv]; subst.
      constructor=>//. by rewrite Hargs.
  - move=> tm1 v tm2 IHtm1 IHtm2 ty'.
    case: (typecheck_term s tm1 == Some (snd v)) /(IHtm1 (snd v))=> Hty1/=; 
    last by reflF.
    case: (typecheck_term s tm2 == Some ty') /(IHtm2 ty') => Hty2/=;
    last by reflF.
    by reflT.
  - move=> f t1 t2 IHf IHt1 IHt2 v.
    case: (typecheck_formula s f) /IHf => Hf/=; last by reflF.
    (*Useful in multiple cases*)
    have Hunique: forall t ty1 ty2,
      (forall v, reflect (term_has_type s t v) 
        (typecheck_term s t == Some v)) ->
      term_has_type s t ty1 ->
      term_has_type s t ty2 ->
      ty1 = ty2. {
      move=> t ty1 ty2 Hr /(Hr ty1) /eqP Hty1 /(Hr ty2).
      by rewrite Hty1 => /eqP [].
    }
    case Ht1': (typecheck_term s t1) =>[ty |].
    + move: Ht1' => /eqP /(IHt1 ty) Ht1.
      case: (typecheck_term s t2 == Some ty) /(IHt2 ty) => Ht2.
      * case: (Some ty == Some v) /eqP => [[Hv] | Hneq]; subst.
        by reflT. reflF.
        have Heq: ty = v by apply (Hunique t1). by subst. 
      * case: (None == Some v) /eqP=>//= _. reflF.
        have Heq: ty = v by apply (Hunique t1). by subst.
    + case: (None == Some v) /eqP=>//= _. reflF.
      move: H5 => /(IHt1 v). by rewrite Ht1'.
  - move=> tm ty ps IHtm HallT v.
    (*case Hisadt: (is_vty_adt s ty) => [t |]/=; last first.
      reflF. rewrite <- is_vty_adt_none_iff in Hisadt.
      case: H2 => [a [m [args [m_in [a_in Hty]]]]].
      apply (Hisadt a m args m_in a_in Hty).*)
    case: (typecheck_term s tm == Some ty) /(IHtm ty)=> Htm/=; last by reflF.
    (*Here things get trickier because terms and patterns are not
      eqTypes*)
    have Hallt: (forall x, In x ps -> reflect (pattern_has_type s x.1 ty)
      (typecheck_pattern s x.1 ty)) by move=> x _; apply typecheck_pattern_correct.
    case: (all (fun x : pattern * term => typecheck_pattern s x.1 ty) ps)
      /(forallb_ForallP _ _ _ Hallt) => Hallps; last first.
      case: (None == Some v) /eqP =>// _; reflF.
      apply Hallps. by rewrite Forall_forall.
    case Hcomp: (Pattern.compile_bare_single true false tm ty ps) => [tm2 |]; last first.
      reflF. by rewrite Hcomp in H7.
    have Hallpat: forall x, In x ps -> pattern_has_type s x.1 ty by
      rewrite -Forall_forall.
    rewrite {Hallps Hallt}.
    move: HallT Hallpat Hcomp.
    case Hnull: (null ps); move: Hnull; case: ps => [_ HallT Hallpat Hcomp|/= 
      [p1 tm1] ptl Hnull HallT Hallpat Hcomp]//.
    case Htm1': (typecheck_term s tm1) => [ty2 |]; last first.
      case: (None == Some v) /eqP=>// _. reflF.
      have: typecheck_term s tm1 == Some v. 
      apply /(ForallT_hd _ _ _ HallT). apply H6. by left.
      by rewrite Htm1'.
    rewrite eq_refl/=.
    have Htm1: term_has_type s tm1 ty2 by
      apply /(ForallT_hd _ _ _ HallT); apply /eqP.
    (*Handle the nested function*)
    have: reflect (forall x, In x ptl -> term_has_type s x.2 ty2)
    ((fix check_list (l : seq (pattern * term)) : bool :=
    match l with
    | [::] => true
    | p :: tl =>
        let (_, tm0) := p in
        (typecheck_term s tm0 == Some ty2) && check_list tl
    end) ptl). {
      clear -IHtm HallT. inversion HallT; subst. clear - IHtm H2.
      move: H2. elim: ptl => [//= HallT | [h1 h2] t /= IH HallT].
      - by apply ReflectT.
      - case: (typecheck_term s h2 == Some ty2) /(ForallT_hd _ _ _ HallT) 
          =>//= Hhty; last first.
          apply ReflectF => C. apply Hhty. apply (C (h1, h2)). by left.
        move: IH => /(_ (ForallT_tl _ _ _ HallT)).
        case: ((fix check_list (l : seq (pattern * term)) : bool :=
        match l with
        | [::] => true
        | p :: tl =>
            let (_, tm0) := p in
            (typecheck_term s tm0 == Some ty2) && check_list tl
        end) t) =>//= IH.
        + apply elimT in IH=>//. apply ReflectT. 
          move=> x [<- // | Hinx].
          by apply IH.
        + apply elimF in IH=>//. apply ReflectF => C.
          apply IH. move=> x Hinx. apply C. by right.
    }
    case: ((fix check_list (l : seq (pattern * term)) : bool :=
    match l with
    | [::] => true
    | p :: tl =>
        let (_, tm0) := p in
        (typecheck_term s tm0 == Some ty2) && check_list tl
    end) ptl) =>//=.
    * move=> /elimT /(_ isT) Hptl.
      case: (Some ty2 == Some v) /eqP => [[] <-| Hneq].
      -- reflT=>//.
        ++ move=> x [<-// | Hinx]. by apply Hptl.
        ++ by rewrite Hcomp.
      -- reflF. have /eqP : typecheck_term s tm1 == Some v by 
          apply /(ForallT_hd _ _ _ HallT); apply H6; left.
        by rewrite Htm1'.
    * move=> /elimF /(_ erefl) Hnotall.
      case: (None == Some v) /eqP=>// _. reflF.
      apply Hnotall. move=> x Hinx.
      have->:ty2 = v. {
        have /eqP: typecheck_term s tm1 == Some v by
          apply /(ForallT_hd _ _ _ HallT); apply H6; left.
        by rewrite Htm1' =>/= [[]].
      }
      by apply H6; right.
  - move=> f v IHf ty2.
    case: (typecheck_formula s f) /IHf => Hval; last by reflF.
    case: (typecheck_type s (snd v)) /typecheck_type_correct => /=Hty1;
    last by reflF.
    case: (Some (snd v) == Some ty2) /eqP => [[] Heq| Hneq].
    + subst. by reflT.
    + by reflF.
  - (*Now for formulas*)
    move=> p tys tms HallT.
    case: (p \in (sig_p s)) /inP => Hinp/=; last by reflF.
    have Halltyps: forall x, x \in tys -> 
      reflect (valid_type s x) (typecheck_type s x) by move=> x _;
      apply typecheck_type_correct.
    case: (all (typecheck_type s) tys) /(all_Forall _ _ _ Halltyps) =>Halltys/=;
    last by reflF.
    rewrite {Halltyps}.
    case: (length tms == length (s_args p)) /eqP => Hlentms/=; last by reflF.
    case: (length tys == length (s_params p)) /eqP => Hlentys/=; 
    last by reflF.
    apply iff_reflect. split.
    + move=> Hvalp. inversion Hvalp; subst.
      clear -H7 HallT Hlentms.
      move: (s_args p) (ty_subst (s_params p) tys) Hlentms HallT H7 .
      elim: tms => [// [|]// | tmh tmtl /= IH [//|ah atl] sigma [Hlen]
        HallT /= Hall].
      apply /andP; split.
      * apply /(ForallT_hd _ _ _ HallT). apply (Forall_inv Hall).
      * apply IH=>//. by inversion HallT. by inversion Hall.
    + move=> Hargs. constructor=>//.
      move: (s_args p) (ty_subst (s_params p) tys) Hlentms HallT Hargs. clear.
      elim: tms => [[|]// | tmh tmtl /= IH [//| ah atl] sigma [Hlen]
        HallT /= /andP[/(ForallT_hd _ _ _ HallT) Hh Hargs]].
      constructor=>//. apply IH=>//. by inversion HallT.
  - move=> q v f IHf.
    case: (typecheck_type s (snd v)) /typecheck_type_correct => Hty/=; 
      last by reflF.
    by case: (typecheck_formula s f) /IHf => Hf; [reflT | reflF].
  - move=> ty t1 t2 Ht1 Ht2.
    case: (typecheck_term s t1 == Some ty) /Ht1 => Ht1/=;
    last by reflF.
    by case: (typecheck_term s t2 == Some ty) /Ht2 => Ht2/=; 
    [reflT | reflF].
  - move=> b f1 f2 Hf1 Hf2.
    case: (typecheck_formula s f1) /Hf1 => Hf1/=; last by reflF.
    by case: (typecheck_formula s f2) /Hf2 => Hf2/=; [reflT | reflF].
  - move=> f Hf.
    by case: (typecheck_formula s f) /Hf => Hf/=; [reflT | reflF].
  - by reflT.
  - by reflT.
  - move=> tm v f Htm Hf.
    case: (typecheck_term s tm == Some (snd v)) /Htm => Htm/=; last by reflF.
    by case: (typecheck_formula s f) /Hf => Hf/=; [reflT | reflF].
  - move=> f1 f2 f3 Hf1 Hf2 Hf3.
    case: (typecheck_formula s f1) /Hf1 => Hf1/=; last by reflF.
    case: (typecheck_formula s f2) /Hf2 => Hf2/=; last by reflF.
    by case: (typecheck_formula s f3) /Hf3 => Hf3/=; [reflT | reflF].
  - (*The difficult case: patterns (easier than terms because
      we don't need to determine the type of the inner patterns)*)
    move=> tm ty ps Htm HallT.
    (*case Hisadt: (is_vty_adt s ty) => [t |]/=; last first.
      reflF. rewrite <- is_vty_adt_none_iff in Hisadt.
      case: H2 => [a [m [args [m_in [a_in Hty]]]]].
      apply (Hisadt a m args m_in a_in Hty).*)
    case: (typecheck_term s tm == Some ty) /Htm => Htm /=; last by reflF.
    have Hallt: (forall x, In x ps -> reflect (pattern_has_type s x.1 ty)
      (typecheck_pattern s x.1 ty)) by move=> x _; apply typecheck_pattern_correct.
    case: (all (fun x : pattern * formula => typecheck_pattern s x.1 ty) ps)
      /(forallb_ForallP _ _ _ Hallt) => Hallps/=; last by
      (reflF; rewrite Forall_forall in Hallps).
    case Hcomp: (Pattern.compile_bare_single false false tm ty ps) => [tm2 |]; last first.
      reflF. by rewrite Hcomp in H6.
    apply iff_reflect. split.
    + move=> Hmatch. inversion Hmatch; subst.
      move: HallT H5. clear. elim: ps => [// | [p1 f1] pt /= IH HallT Hall].
      apply /andP; split.
      * apply /(ForallT_hd _ _ _ HallT). by apply (Hall (p1, f1)); left. 
      * apply IH=>//. by inversion HallT. move=> x Hinx.
        by apply Hall; right.
    + move=> Hcheck. rewrite Forall_forall in Hallps. 
      constructor=>//; last by rewrite Hcomp.
      move: HallT Hcheck. clear. 
      elim: ps => [// | [p1 f1] ptl /= IH HallT /andP[Hf1 Hcheck]].
      inversion HallT; subst.
      move=> x [Hx | Hinx]; subst=>//.
      by apply /H1. by apply IH.
Qed.

(*Now a few easy corollaries*)
Definition typecheck_term_correct (gamma: context) (tm: term) (v: vty):
  reflect (term_has_type gamma tm v) (typecheck_term gamma tm == Some v) :=
  fst (typecheck_term_fmla_spec gamma tm Ftrue) v.

Definition typecheck_formula_correct (gamma: context) (f: formula):
  reflect (formula_typed gamma f) (typecheck_formula gamma f) :=
  snd (typecheck_term_fmla_spec gamma tm_d f).

Lemma term_has_type_unique: forall s t x y,
  term_has_type s t x ->
  term_has_type s t y ->
  x = y.
Proof.
  move=>s t x y /(typecheck_term_correct s t) /eqP Hx
    /(typecheck_term_correct s t) /eqP.
  by rewrite Hx => [[]].
Qed.

Section ContextCheck.

Variable gamma: context.

(*Part 1: wf_funsym and wf_predsym*)

Definition check_wf_funsym (f: funsym) : bool :=
  all (fun t => typecheck_type gamma t &&
    all (fun x => x \in (s_params f)) (type_vars t))
  (f_ret f :: s_args f).

Lemma check_wf_funsym_spec (f: funsym):
  reflect (wf_funsym gamma f) (check_wf_funsym f).
Proof.
  rewrite /check_wf_funsym/wf_funsym.
  apply all_Forall=> x Hinx.
  apply andPP; first by apply typecheck_type_correct.
  apply all_Forall=> v Hinv.
  apply /inP.
Qed.

Definition check_wf_predsym (p: predsym) : bool :=
  all (fun t => typecheck_type gamma t &&
    all (fun x => x \in (s_params p)) (type_vars t))
  (s_args p).

Lemma check_wf_predsym_spec (p: predsym):
  reflect (wf_predsym gamma p) (check_wf_predsym p).
Proof.
  rewrite /check_wf_predsym/wf_predsym.
  apply all_Forall => x Hinx.
  apply andPP; first by apply typecheck_type_correct.
  apply all_Forall => v Hinv.
  apply /inP.
Qed.

(*Part 2: definition check*)

(*Checks for datatypes*)

Section Datatype.

Definition adt_valid_type_check (a: alg_datatype) : bool :=
  match a with
  | alg_def ts constrs =>
    all (fun (c: funsym) => ((s_params c) == (ts_args ts)) &&
      ((f_ret c) == vty_cons ts (map vty_var (ts_args ts))))
      (ne_list_to_list constrs)
  end.

Lemma adt_valid_type_check_spec (a: alg_datatype) :
  reflect (adt_valid_type a) (adt_valid_type_check a).
Proof.
  rewrite /adt_valid_type /adt_valid_type_check.
  case: a => [ts constrs].
  apply all_Forall => x Hinx.
  by apply andPP; apply eqP.
Qed.

Definition valid_mut_rec_check (m: mut_adt) : bool :=
  all (fun a => ((m_params m) == (ts_args (adt_name a))) &&
    all (fun (f: funsym) => m_params m == s_params f)
      (adt_constr_list a))
  (typs m).

Lemma valid_mut_rec_check_spec m :
  reflect (valid_mut_rec m) (valid_mut_rec_check m).
Proof.
  rewrite /valid_mut_rec /valid_mut_rec_check.
  apply forallb_ForallP => x Hinx.
  apply andPP; first by apply eqP.
  apply all_Forall => y Hiny.
  by apply eqP.
Qed.

(*The whole check is easy, since the most difficult check
  (inhab) is a boolean already*)
Definition mut_valid_check (m: mut_adt) : bool :=
  all (adt_valid_type_check) (typs m) &&
  all (adt_inhab gamma) (typs m) &&
  valid_mut_rec_check m &&
  uniform m.

Lemma mut_valid_check_spec (m: mut_adt) :
  reflect (mut_valid gamma m) (mut_valid_check m).
Proof.
  rewrite /mut_valid/mut_valid_check.
  rewrite - !andbA.
  repeat (apply andPP).
  - apply forallb_ForallP => x Hinx. 
    by apply adt_valid_type_check_spec.
  - apply forallb_ForallP=> y Hiny.
    by apply idP.
  - by apply valid_mut_rec_check_spec.
  - by apply idP.
Qed.

End Datatype.

(*Recursive functions *)

Section RecFun.

(*This is much harder, since we need to find the decreasing arguments
  (and prove that the decreasing check itself is decidable).
  We also need this typechecking to define the full recursive
  function implementation in RecFun2.v.
  We did this in [TerminationChecker.v]*)

HB.instance Definition _ := hasDecEq.Build pattern pattern_eqb_spec.
HB.instance Definition _ := hasDecEq.Build term term_eqb_spec.
HB.instance Definition _ := hasDecEq.Build formula formula_eqb_spec.

Definition check_funpred_def_valid_type (fd: funpred_def) : bool :=
  match fd with
  | fun_def f vars t =>
    (typecheck_term gamma t == Some (f_ret f)) &&
    sublistb (tm_fv t) vars &&
    sublistb (tm_type_vars t) (s_params f) &&
    uniq (map fst vars) &&
    (map snd vars == s_args f)
  | pred_def p vars f =>
    (typecheck_formula gamma f) &&
    sublistb (fmla_fv f) vars &&
    sublistb (fmla_type_vars f) (s_params p) &&
    uniq (map fst vars) &&
    (map snd vars == s_args p)
  end.

Lemma check_funpred_def_valid_type_spec (fd: funpred_def):
  reflect (funpred_def_valid_type gamma fd) 
    (check_funpred_def_valid_type fd).
Proof.
  rewrite /funpred_def_valid_type/check_funpred_def_valid_type.
  case: fd => [f vars t | p vars f].
  - rewrite -andbA -andbA -andbA.
    repeat (apply andPP; [| apply andPP]). 
    + apply typecheck_term_correct.
    + apply sublistbP.
    + apply sublistbP.
    + apply uniqP.
    + apply eqP.
  - rewrite -andbA -andbA -andbA.
     repeat (apply andPP; [|apply andPP]).
    + apply typecheck_formula_correct.
    + apply sublistbP.
    + apply sublistbP.
    + apply uniqP.
    + apply eqP.
Qed.

Section WFCtx.
Variable gamma_wf: wf_context gamma.

(*For our purposes, we need something a bit more specific,
  we need to know that a function creates these (so that they
  are unique)*)
Lemma termination_check_decide (l: list funpred_def):
  In l (mutfuns_of_context gamma) ->
  Forall (funpred_def_valid_type gamma) l ->
  funpred_def_term_exists gamma l ->
  match (@check_termination gamma l) with
  | Some (m, params, vs, il) =>
    funpred_def_term gamma l m params vs il
  | None => False
  end.
Proof.
  move=>Hin Hall Hex.
  case Hfind: (check_termination l) => [[[[m params] vs] il] |].
  - by apply check_termination_some.
  - case: Hex => [m [params [vs [il Hterm]]]].
    by apply (check_termination_none gamma_wf l Hin Hall Hfind _ _ _ _ Hterm).
Qed.

End WFCtx.

(*The other half: funpred_def_valid_type*)

Definition funpred_def_valid_type_check (fd: funpred_def): bool :=
  match fd with
  | fun_def f vars t =>
    (typecheck_term gamma t == Some (f_ret f)) &&
    (sublistb (tm_fv t) vars) &&
    (sublistb (tm_type_vars t) (s_params f)) &&
    (uniq (map fst vars)) &&
    (map snd vars == (s_args f))
  | pred_def p vars f =>
    (typecheck_formula gamma f) &&
    (sublistb (fmla_fv f) vars) &&
    (sublistb (fmla_type_vars f) (s_params p)) &&
    (uniq (map fst vars)) &&
    ((map snd vars) == (s_args p))
  end.

Lemma funpred_def_valid_type_check_spec (fd: funpred_def) :
  reflect (funpred_def_valid_type gamma fd) 
    (funpred_def_valid_type_check fd).
Proof.
  rewrite /funpred_def_valid_type/funpred_def_valid_type_check.
  case: fd => [f vars t | p vars f];
  rewrite -!andbA; repeat (apply andPP);
  try (apply sublistbP);
  try (apply uniqP);
  try (apply eqP).
  - apply typecheck_term_correct.
  - apply typecheck_formula_correct.
Qed.

(*And now the full check for functions*)
Definition funpred_valid_check (l: list funpred_def) : bool :=
  all (funpred_def_valid_type_check) l &&
  (isSome (@check_termination gamma l)).

HB.instance Definition _ := hasDecEq.Build fpsym fpsym_eqb_spec.
HB.instance Definition _ := hasDecEq.Build funpred_def funpred_def_eqb_spec.

Lemma funpred_valid_check_spec (l: list funpred_def) :
  wf_context gamma ->
  In l (mutfuns_of_context gamma) ->
  reflect (funpred_valid gamma l) (funpred_valid_check l).
Proof.
  move=> Hwf l_in.
  rewrite /funpred_valid/funpred_valid_check.
  case: (all_Forall (funpred_def_valid_type gamma) funpred_def_valid_type_check
    l)=>/=.
  - move=> x Hinx. apply funpred_def_valid_type_check_spec.
  - move=> Hall.
    rewrite /funpred_def_term_exists.
    case Hfind: (check_termination l) => [[[[m params] vs] il] |]/=.
    + apply ReflectT. split=>//.
      exists m. exists params. exists vs. exists il.
      by apply check_termination_some.
    + apply ReflectF.
      move=> [Hall' [m [params [vs [il Hdef]]]]].
      by apply (check_termination_none Hwf l l_in Hall Hfind m params vs il).
  - move=> Hnotall. reflF; contradiction.
Qed.

End RecFun.

(*Inductive predicates*)

(*[valid_ind_form]*)
Fixpoint valid_ind_form_check (p: predsym) (f: formula) : bool :=
  match f with
  | Fpred p' tys tms =>
    (p == p') && (tys == map vty_var (s_params p)) &&
    (length (s_args p) == length tms)
  | Fbinop Timplies f1 f2 =>
    valid_ind_form_check p f2
  | Fquant Tforall x f =>
    valid_ind_form_check p f
  | Flet t x f =>
    valid_ind_form_check p f
  | _ => false
  end.

Lemma valid_ind_form_check_spec (p: predsym) (f: formula):
  reflect (valid_ind_form p f) (valid_ind_form_check p f).
Proof.
  move: f.
  apply (formula_rect (fun _ => True) (fun f => 
  reflect (valid_ind_form p f) (valid_ind_form_check p f) ))=>//=;
  intros; try by reflF.
  - case: (p == p0) /eqP=>/= Hpp0; last by reflF.
    rewrite -Hpp0.
    case: (tys == [seq vty_var i | i <- s_params p]) /eqP => /= Htys;
    last by reflF.
    case: (length (s_args p) == length tms) /eqP => /= Hlens;
    last by reflF.
    by reflT.
  - case: q; last by reflF. 
    case: H => Hval; last by reflF. by reflT.
  - case: b; try by reflF.
    case: H0 => Hval; last by reflF. by reflT.
  - case: H0 => Hval; last by reflF. by reflT.
Qed.

Definition indprop_valid_type_check (i: indpred_def) : bool :=
  match i with
  | ind_def p lf =>
    all (fun (f: formula) =>
      typecheck_formula gamma f &&
      closed_formula f &&
      valid_ind_form_check p f &&
      sublistb (fmla_type_vars f) (s_params p)
      ) (map snd lf)
  end.

Lemma indprop_valid_type_check_spec (i: indpred_def) :
  reflect (indprop_valid_type gamma i) (indprop_valid_type_check i).
Proof.
  rewrite /indprop_valid_type/indprop_valid_type_check.
  case: i => [p lf].
  apply all_Forall=> x Hinx.
  rewrite - !andbA. repeat (apply andPP).
  - apply typecheck_formula_correct.
  - apply idP.
  - apply valid_ind_form_check_spec.
  - apply sublistbP.
Qed.

(*Now [indpred_positive]*)

Fixpoint ind_strictly_positive_check (ps: seq predsym) (f: formula)
  {struct f} : bool :=
  (all (fun p => ~~ predsym_in_fmla p f) ps) ||
  match f with
  | Fpred p vs ts =>
    (p \in ps) &&
    all (fun t => all (fun x => ~~ predsym_in_tm x t) ps ) ts
  | Fbinop Timplies f1 f2 =>
    ind_strictly_positive_check ps f2 &&
    all (fun p => ~~ predsym_in_fmla p f1) ps
  | Fquant q x f =>
    ind_strictly_positive_check ps f
  | Fbinop Tand f1 f2 =>
    ind_strictly_positive_check ps f1 &&
    ind_strictly_positive_check ps f2
  | Fbinop Tor f1 f2 =>
    ind_strictly_positive_check ps f1 &&
    ind_strictly_positive_check ps f2
  | Flet t x f =>
    all (fun p => ~~ predsym_in_tm p t) ps &&
    ind_strictly_positive_check ps f
  | Fif f1 f2 f3 =>
    all (fun p => ~~ predsym_in_fmla p f1) ps &&
    ind_strictly_positive_check ps f2 &&
    ind_strictly_positive_check ps f3
  | Fmatch t ty pats =>
    all (fun p => ~~ predsym_in_tm p t) ps &&
    (*to satisfy positivity checker*)
    all id (map (fun x => ind_strictly_positive_check ps (snd x)) pats)
  | _ => false
  end.

(*Want to handle notin case at beginning*)
Ltac not_in_pos_case ps f :=
  let Hallin := fresh "Hallin" in
  case: (all (fun p => ~~ predsym_in_fmla p f) ps) 
    /(all_Forall _ _ _ (fun x Hin => idP))=>/= Hallin;
    rewrite -> Forall_forall in Hallin; first by
      apply ReflectT; constructor.

Lemma all_id_map {A: Type} {p: pred A} {s: seq A}:
  all id (map p s) = all p s.
Proof.
  by elim: s => [// | h t /= ->].
Qed.
  

Lemma ind_strictly_positive_check_spec (ps: seq predsym) (f: formula) :
  reflect (ind_strictly_positive ps f) (ind_strictly_positive_check ps f).
Proof.
  move: f.
  apply (formula_rect (fun _ => true) (fun f => 
  reflect (ind_strictly_positive ps f) (ind_strictly_positive_check ps f)))=>//=;
  intros.
  - not_in_pos_case ps (Fpred p tys tms).
    case:(p \in ps) /inP => Hinp/=; last by reflF.
    case: (all (fun t : term => all (fun x : predsym => ~~ predsym_in_tm x t) ps) tms)
      /(all_Forall (fun t => Forall (fun x => ~~ predsym_in_tm x t) ps)).
    + move=>x Hinx. apply all_Forall=> y Hiny. apply idP.
    + move=> Hall2. apply ReflectT. apply ISP_pred=>//.
      move=> x t Hint Hinx.
      move: Hall2.
      rewrite -> Forall_forall => /(_ _ Hint).
      by rewrite -> Forall_forall => /(_ _ Hinx).
    + move=> Hnotall. apply ReflectF. move=> C; inversion C; subst=>//.
      apply Hnotall.
      rewrite Forall_forall => t Hint.
      rewrite Forall_forall=> x. by apply H4.
  - not_in_pos_case ps (Fquant q v f).
    case: H => Hpos. by reflT. by reflF.
  - not_in_pos_case ps (Feq v t1 t2).
    by reflF.
  - not_in_pos_case ps (Fbinop b f1 f2).
    case: b; try by reflF.
    + case: H => Hpos1; last by reflF.
      case: H0 => Hpos2; last by reflF.
      by reflT.
    + case: H => Hpos1; last by reflF.
      case: H0 => Hpos2; last by reflF.
      by reflT.
    + case: H0 => Hpos; last by reflF.
      case: (all (fun p : predsym => ~~ predsym_in_fmla p f1) ps) 
        /(all_Forall _ _ _ (fun _ _ => idP)) => Hall;
      rewrite -> Forall_forall in Hall;
      last by reflF.
      by reflT.
  - not_in_pos_case ps (Fnot f). by reflF.
  - not_in_pos_case ps Ftrue. by reflF.
  - not_in_pos_case ps Ffalse. by reflF.
  - not_in_pos_case ps (Flet tm v f).
    case: (all (fun p : predsym => ~~ predsym_in_tm p tm) ps)
    /(all_Forall _ _ _ (fun _ _ => idP)) => Hall;
    rewrite -> Forall_forall in Hall;
    last by reflF.
    case: H0 => Hpos; last by reflF.
    by reflT.
  - not_in_pos_case ps (Fif f1 f2 f3).
    case: (all (fun p : predsym => ~~ predsym_in_fmla p f1) ps) 
    /(all_Forall _ _ _ (fun _ _ => idP)) => Hall;
    rewrite -> Forall_forall in Hall;
    last by reflF.
    case: H0=> Hpos1; last by reflF.
    case: H1=> Hpos2; last by reflF.
    by reflT.
  - not_in_pos_case ps (Fmatch tm v ps0).
    case: (all (fun p : predsym => ~~ predsym_in_tm p tm) ps)
    /(all_Forall _ _ _ (fun _ _ => idP)) => Hall;
    rewrite -> Forall_forall in Hall;
    last by reflF.
    have Hrefl: reflect (forall f : formula,
    In f (List.map snd ps0) -> ind_strictly_positive ps f)
    (all id [seq ind_strictly_positive_check ps x.2 | x <- ps0]). {
      eapply equivP. 2: apply Forall_forall.
      rewrite all_id_map.
      eapply equivP. 2: symmetry; apply Forall_map.
      apply all_Forall.
      move=> x /inP Hinx.
      apply (ForallT_In _ formula_eq_dec _ H0).
      rewrite in_map_iff. by exists x.
    }
    case: Hrefl => Hallpos; last by reflF.
    by reflT.
Qed.

Fixpoint ind_positive_check (ps: seq predsym) (f: formula) : bool :=
  match f with
  | Fpred p vs ts =>
    (p \in ps) &&
    all (fun t => all (fun x => ~~ predsym_in_tm x t) ps ) ts
  | Fquant Tforall x f =>
    ind_positive_check ps f
  | Flet t x f =>
    all (fun p => ~~ predsym_in_tm p t) ps &&
    ind_positive_check ps f
  | Fbinop Timplies f1 f2 =>
    ind_strictly_positive_check ps f1 &&
    ind_positive_check ps f2
  | _ => false
  end.

(*Some duplication with previous proof*)
Lemma ind_positive_check_spec (ps: seq predsym) (f: formula) : 
  reflect (ind_positive ps f) (ind_positive_check ps f).
Proof.
  apply (formula_rect (fun _ => True) (fun f =>
  reflect (ind_positive ps f) (ind_positive_check ps f)))=>//=;
  intros; try by reflF.
  - case:(p \in ps) /inP => Hinp/=; last by reflF.
    case: (all (fun t : term => all (fun x : predsym => ~~ predsym_in_tm x t) ps) tms)
      /(all_Forall (fun t => Forall (fun x => ~~ predsym_in_tm x t) ps)).
    + move=>x Hinx. apply all_Forall=> y Hiny. apply idP.
    + move=> Hall2. apply ReflectT. apply IP_pred=>//.
      move=> x t Hint Hinx.
      move: Hall2.
      rewrite -> Forall_forall => /(_ _ Hint).
      by rewrite -> Forall_forall => /(_ _ Hinx).
    + move=> Hnotall. apply ReflectF. move=> C; inversion C; subst=>//.
      apply Hnotall.
      rewrite Forall_forall => t Hint.
      rewrite Forall_forall=> x. by apply H4.
  - case: q; last by reflF.
    case: H=> Hpos; last by reflF.
    by reflT.
  - case: b; try by reflF.
    case: (ind_strictly_positive_check_spec ps f1) => Hpos1;
    last by reflF.
    case: H0 => Hpos2; last by reflF.
    by reflT.
  - case: (all (fun p : predsym => ~~ predsym_in_tm p tm) ps)
    /(all_Forall _ _ _ (fun _ _ => idP)) => Hall;
    rewrite -> Forall_forall in Hall;
    last by reflF.
    case: H0 => Hpos; last by reflF.
    by reflT.
Qed.

Definition indpred_positive_check (l: seq indpred_def) : bool :=
  let ps :=
    map (fun i => match i with | ind_def p _ => p end) l in
  let fs :=
    concat (map (fun i => match i with | ind_def _ fs => map snd fs end) l)
  in
  all (ind_positive_check ps) fs.

Lemma indpred_positive_check_spec (l: seq indpred_def) :
  reflect (indpred_positive l) (indpred_positive_check l).
Proof.
  rewrite /indpred_positive/indpred_positive_check.
  apply all_Forall.
  move=> x Hinx.
  apply ind_positive_check_spec.
Qed.

(*[indpred_params_same]*)

(*A faster check than using "all" at each iteration (from the
  definition)*)

Definition all_eq {A: Type} {B: eqType} (f: A -> B) (l: seq A) : bool :=
  match l with
  | nil => true
  | h :: t => all (fun x => f x == f h) t
  end.

Lemma all_eq_spec {A: Type} {B: eqType}(f: A -> B) (l: seq A)  :
  reflect (forall x y, In x l -> In y l -> f x = f y)
    (all_eq f l).
Proof.
  rewrite /all_eq.
  case: l=>[| h t]; first by apply ReflectT.
  eapply equivP.
  apply (forallb_ForallP (fun y => f y = f h));
  first by move=> x Hinx; apply eqP.
  rewrite -> Forall_forall. split=> Hallin x.
  - move=> y [Hxh | Hxt] [Hyh | Hyt]; subst=>//;
    try (by apply Hallin);
    try (symmetry; by apply Hallin).
    rewrite Hallin //. symmetry.
    by rewrite Hallin.
  - move=> Hinx. by apply Hallin=>/=; auto.
Qed.

Lemma all_eq_Forall_eq {A: Type} {B: eqType} (f: A -> B) (l: seq A):
  reflect (Forall_eq f l) (all_eq f l).
Proof.
  apply iff_reflect.
  rewrite -(reflect_iff _ _ (all_eq_spec f l)).
  by apply Forall_eq_iff.
Qed.

Definition indpred_params_same_check (l: seq indpred_def) : bool :=
  all_eq (fun i => match i with | ind_def p _ => s_params p end) l.

Lemma indpred_params_same_check_spec (l: seq indpred_def) :
  reflect (indpred_params_same l) (indpred_params_same_check l).
Proof.
  rewrite /indpred_params_same/indpred_params_same_check.
  apply all_eq_Forall_eq.
Qed.

(*Now, full indprop def*)
Definition indprop_valid_check (il: seq indpred_def) : bool :=
  all indprop_valid_type_check il &&
  indpred_positive_check il &&
  indpred_params_same_check il &&
  indpreds_uniform il.

Lemma indprop_valid_check_spec (il: seq indpred_def) :
  reflect (indprop_valid gamma il) (indprop_valid_check il).
Proof.
  rewrite /indprop_valid/indprop_valid_check.
  rewrite -!andbA.
  repeat (apply andPP).
  - apply forallb_ForallP. move=> x Hinx.
    apply indprop_valid_type_check_spec.
  - apply indpred_positive_check_spec.
  - apply indpred_params_same_check_spec.
  - apply idP.
Qed.

(*And now, we can check an entire definition*)
Definition valid_def_check (d: def) : bool :=
  match d with
  | datatype_def m => mut_valid_check m
  | recursive_def fs => funpred_valid_check fs
  | inductive_def l => indprop_valid_check l
  | nonrec_def f => funpred_def_valid_type_check f &&
      nonrec_def_nonrec f
  | _ => true
  end.

Lemma valid_def_check_spec (d: def) :
  wf_context gamma ->
  In d gamma ->
  reflect (valid_def gamma d) (valid_def_check d).
Proof.
  move=> Hwf.
  rewrite /valid_def/valid_def_check.
  case: d; try by (move=> _ _; apply ReflectT).
  - move=> m _. apply mut_valid_check_spec.
  - move=> l l_in. apply funpred_valid_check_spec=>//.
    by apply in_mutfuns.
  - move=> l _. apply indprop_valid_check_spec.
  - move=> f _. apply andPP.
    apply funpred_def_valid_type_check_spec.
    apply idP.
Qed.

End ContextCheck.

(*Now we show that we can incrementally check the context,
  since we don't want to have to check it each time*)

Definition check_context_cons (d: def) (gamma: context) : bool :=
  let funs := funsyms_of_def d in
  let preds := predsyms_of_def d in
  let tys := typesyms_of_def d in
  all (check_wf_funsym (d :: gamma)) funs &&
  all (check_wf_predsym (d :: gamma)) preds &&
  all (fun f => f \notin (sig_f gamma)) funs &&
  all (fun p => p \notin (sig_p gamma)) preds &&
  all (fun t => t \notin (sig_t gamma)) tys &&
  uniq funs &&
  uniq preds &&
  uniq tys &&
  nonempty_def d &&
  valid_constrs_def d &&
  valid_def_check (d :: gamma) d.

(*If we start with a valid context, this check means that
  our additional context is still valid*)
Theorem check_context_cons_correct (d: def) (gamma: context) :
  valid_context gamma ->
  reflect (valid_context (d :: gamma)) (check_context_cons d gamma).
Proof.
  move=> Hval.
  rewrite /check_context_cons.
  (*First, wf_funsym and predsym*)
  case: (all (check_wf_funsym (d :: gamma)) (funsyms_of_def d))
    /(all_Forall (fun f => wf_funsym (d :: gamma) f)); 
  last by move=> Hall; reflF.
    by move=> x Hinx; apply check_wf_funsym_spec.
  move=> Hfunswf.

  case: (all (check_wf_predsym (d :: gamma)) (predsyms_of_def d))
    /(all_Forall (fun p => wf_predsym (d :: gamma) p));
  last by move=> Hall; reflF.
    by move=> x Hinx; apply check_wf_predsym_spec.
  move=> Hpredswf.

  (*Now, sig_t checks*)
  case: (all (fun f => f \notin sig_f gamma) (funsyms_of_def d))
    /(all_Forall (fun f => ~ In f (sig_f gamma)));
  last by move=> Hall; reflF.
    by move=> x Hinx; apply negPP, inP.
  move=> Hsigf.

  case: (all (fun p => p \notin sig_p gamma) (predsyms_of_def d))
    /(all_Forall (fun p => ~ In p (sig_p gamma)));
  last by move=> Hall; reflF.
    by move=> x Hinx; apply negPP, inP.
  move=> Hsigp.

  case: (all (fun t => t \notin sig_t gamma) (typesyms_of_def d))
    /(all_Forall (fun t => ~ In t (sig_t gamma)));
  last by move=> Hall; reflF.
    by move=> x Hinx; apply negPP, inP.
  move=> Hsigt.

  (*Now NoDups checks for new definitions*)
  case: (uniq (funsyms_of_def d)) /uniqP => Hnodupf; last by reflF.
  case: (uniq (predsyms_of_def d)) /uniqP => Hnodupp; last by reflF.
  case: (uniq (typesyms_of_def d)) /uniqP => Hnodupt; last by reflF.
  case Hemp: (nonempty_def d); last 
    by (apply ReflectF => C; inversion C; subst; rewrite Hemp in H10).
  case Hconstrs: (valid_constrs_def d); last by
    (apply ReflectF => C; inversion C; subst; rewrite Hconstrs in H11).
  (*At this point, wf_context holds, so we can use the
    def check lemma (the recfun case needs a wf_context)*)
  have Hwf: wf_context (d :: gamma). {
    apply valid_context_wf in Hval. by constructor.
  }
  case: (valid_def_check_spec (d :: gamma) d Hwf ltac:(simpl; auto))
  => Hvald; last by reflF.
  by reflT.
Qed.

(*A corollary: we can typecheck an entire context*)
Fixpoint check_context (gamma: context) : bool :=
  match gamma with
  | nil => true
  | d :: g => check_context g && check_context_cons d g
  end.

Theorem check_context_correct (gamma: context) :
  reflect (valid_context gamma) (check_context gamma).
Proof.
  elim: gamma => [| d g /= IH].
  - by reflT.
  - case: IH => g_val; last by reflF.
    case: (check_context_cons_correct d g g_val) => Hval;
      last by apply ReflectF.
    by apply ReflectT.
Qed.

End Typechecker.