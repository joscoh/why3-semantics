(*Separate file to use ssreflect*)
Require Export Typing.

From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

(*Tactics*)
Ltac reflT := apply ReflectT; constructor.

Ltac reflF := let C := fresh "C" in apply ReflectF => C; inversion C; subst.

(* General ssreflect helpful lemmas *)
Lemma inP: forall {A: eqType} (x: A) (l: seq A),
  reflect (In x l) (x \in l).
Proof.
  move=> A x l. elim: l => [//= | h t /= IH].
  - by apply ReflectF.
  - rewrite in_cons. apply orPP => //.
    rewrite eq_sym. apply eqP.
Qed.

(*A similar result for In*)
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

Lemma forallb_ForallP {A: Type} (P: A -> Prop) (p: pred A) (s: seq A):
  (forall x, In x s -> reflect (P x ) (p x)) ->
  reflect (Forall P s) (all p s).
Proof.
  elim: s =>[//= Hall | h t /= IH Hall].
  - apply ReflectT. constructor.
  - case: (p h) /(Hall h (or_introl _)) => //= Hh; last by reflF.
    have IHt: (forall x : A, In x t -> reflect (P x) (p x)) by
      move=> x Hinx; apply Hall; right.
    move: IH => /(_ IHt) IH.
    case: (all p t) /IH => Ht/=; last by reflF.
    apply ReflectT. by constructor.
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

Lemma nullP {A: Type} (s: seq A):
  reflect (s = nil) (null s).
Proof.
  case: s=>/= [| h t].
  apply ReflectT=>//.
  by apply ReflectF.
Qed.

Lemma nth_eq {A: Type} (n: nat) (s: seq A) (d: A):
  List.nth n s d = nth d s n.
Proof.
  move: n. elim:s=>[// [|]// | h t /= IH [// | n' /=]].
  by apply IH.
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


(* Let's try to build a typechecker *)
Section Typechecker.

Fixpoint typecheck_type (gamma:context) (v: vty) : bool :=
  match v with
  | vty_int => true
  | vty_real => true
  | vty_var tv => true
  | vty_cons ts vs => 
      (ts \in (sig_t gamma)) &&
      (length vs == length (ts_args ts)) &&
      (fix check_list (l: list vty) : bool :=
      match l with
      | nil => true
      | x :: t => typecheck_type gamma x && check_list t
      end) vs
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

HB.instance Definition _ := hasDecEq.Build funsym funsym_eqb_spec.
HB.instance Definition _ := hasDecEq.Build predsym predsym_eqb_spec.

(*Decidable list intersection, may have duplicates*)
Definition seqI {A: eqType} (s1 s2: seq A) :=
  filter (fun x => x \in s2) s1.

Definition is_funsym_constr (gamma: context) (f: funsym) : bool :=
  List.existsb (fun (m: mut_adt) =>
    List.existsb (fun (a: alg_datatype) => constr_in_adt f a)
     (typs m)) (mut_of_context gamma).

Lemma has_existsP {A: Type} (b: A -> bool) (P: A -> Prop) {l: list A}:
  (forall x, In x l -> reflect (P x) (b x)) ->
  reflect (exists x, In x l /\ P x) (List.existsb b l).
Proof.
  elim: l => //=[_ |h t /= IH Hrefl].
  { reflF. by case: H. }
  case: (Hrefl h (ltac:(auto))) => Hph/=.
  { apply ReflectT. exists h. by auto. }
  prove_hyp IH.
  { move=> x Hinx. by apply Hrefl; auto. }
  case: IH => Hex.
  - apply ReflectT. case: Hex => [y [Hiny Hy]].
    by exists y; auto.
  - reflF.
    case: H => [[Hxh | Hinx]] Hpx; subst=>//.
    apply Hex. by exists x.
Qed.

(*Not very ssreflect-like but much easier to prove this way*)
Lemma is_funsym_constr_correct gamma f:
  reflect (exists m a, mut_in_ctx m gamma /\ adt_in_mut a m /\
    constr_in_adt f a) (is_funsym_constr gamma f).
Proof.
  apply iff_reflect.
  rewrite /is_funsym_constr.
  rewrite existsb_exists.
  setoid_rewrite existsb_exists.
  split; intros; destruct_all.
  - exists x. split; first by apply mut_in_ctx_eq.
    exists x0. split=>//; by apply in_bool_In in H0.
  - exists x. exists x0. split_all=>//; [by apply mut_in_ctx_eq |
    by apply In_in_bool].
Qed.

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
(*Check forallP.
(*What about this?*)
Lemma all_in_range_equiv bound p:
  all_in_range bound p =
  [forall x in 'I_bound, p x].
Proof.
  case: [forall x0 in 'I_bound, p x0] /forallP => Hall.
  - apply /(all_in_range_spec _ p p).
    + move=> x Hx. apply idP.
    + move=> n Hn.
      by move: Hall => /(_ (Ordinal Hn))/=.
  - apply /(all_in_range_spec _ p p).
    + move=> x Hx. apply idP.
    + move=> C. apply Hall => x/=.
      by apply C.
Qed.*)

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



(*We would like to prove this correct*)
Lemma typecheck_type_correct: forall (gamma: context) (v: vty),
  reflect (valid_type gamma v) (typecheck_type gamma v).
Proof.
  move=> gamma. apply vty_rect=>//=.
  - apply ReflectT. constructor.
  - apply ReflectT. constructor.
  - move=> v. apply ReflectT. constructor.
  - move=> ts vs Hty. case Hts: (ts \in sig_t gamma)=>/=; last first.
      apply ReflectF => C. inversion C; subst.
      move: H1 => /inP. by rewrite Hts.
    (*Annoyingly, we can't do a single induction because of the
      length requirement*)
    apply iff_reflect. split.
    + move => Hty'. inversion Hty'; subst. rewrite {H1} (introT eqP H3)/=.
      move: Hty H4. clear. elim: vs => [// | v vs /= IH Hall Hval].
      have->/=: typecheck_type gamma v by apply /(ForallT_hd _ _ _ Hall);
        apply Hval; left.
      apply IH. by apply (ForallT_tl _ _ _ Hall).
      move=> x Hinx. by apply Hval; right.
    + move => /andP[/eqP Hlen Hvs].
      constructor=>//. by apply /inP.
      move: Hvs Hty. clear. elim: vs => 
        [// | v vs /= IH /andP[Hv Hvs] Hall x [Hvx | Hinx]]; subst.
      by apply /(ForallT_hd _ _ _ Hall).
      apply IH=>//. by apply (ForallT_tl _ _ _ Hall).
Qed.

Lemma typecheck_pattern_correct: forall (s: context) (p: pattern) (v: vty),
  reflect (pattern_has_type s p v) (typecheck_pattern s p v).
Proof.
  move=> s. apply 
    (pattern_rect (fun (p: pattern) => forall v, 
      reflect (pattern_has_type s p v) (typecheck_pattern s p v)))=>//=.
  - move=> vs ty2. 
    case: (ty2 == (snd vs)) /eqP => //= Hty12; subst; last by reflF.
    case: (typecheck_type s (snd vs)) /typecheck_type_correct => Hty1; 
    last by reflF.
    apply ReflectT. by constructor.
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
  - move=> v.
    case: (typecheck_type s v) /typecheck_type_correct => Hv; last by reflF.
    apply ReflectT. by constructor.
  - move=> p1 p2 IH1 IH2 v.
    case: (typecheck_pattern s p1 v) /(IH1 v) => Hp1/=; last by reflF.
    case: (typecheck_pattern s p2 v) /(IH2 v)=> Hp2/=; last by reflF.
    case: (eq_memb (pat_fv p2) (pat_fv p1)) /eq_memb_spec => Heq/=.
    + apply ReflectT. constructor=>//. by rewrite eq_mem_In.
    + apply ReflectF => C. inversion C; subst.
      rewrite eq_mem_In in H5. apply Heq=> x. by rewrite H5.
  - move=> p v IH v'.
    case: (v' == (snd v)) /eqP => Hv'/=; subst; last by reflF.
    case: (v \in pat_fv p) /inP => Hinv/=; first by reflF.
    case: (typecheck_pattern s p (snd v)) /(IH (snd v)) => Hty; last by reflF.
    apply ReflectT. by constructor.
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
    if is_vty_adt s ty1 && (typecheck_term s tm == Some ty1) &&
      all (fun x => typecheck_pattern s (fst x) ty1) ps
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
    is_vty_adt s ty &&
    (typecheck_term s tm == Some ty) &&
    all (fun x => typecheck_pattern s (fst x) ty) ps &&
    (~~ (null ps)) &&
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
    case Hisadt: (is_vty_adt s ty) => [t |]/=; last first.
      reflF. rewrite <- is_vty_adt_none_iff in Hisadt.
      case: H2 => [a [m [args [m_in [a_in Hty]]]]].
      apply (Hisadt a m args m_in a_in Hty).
    case: (typecheck_term s tm == Some ty) /(IHtm ty)=> Htm/=; last by reflF.
    (*Here things get trickier because terms and patterns are not
      eqTypes*)
    have Hallt: (forall x, In x ps -> reflect (pattern_has_type s x.1 ty)
      (typecheck_pattern s x.1 ty)) by move=> x _; apply typecheck_pattern_correct.
    case: (all (fun x : pattern * term => typecheck_pattern s x.1 ty) ps)
      /(forallb_ForallP _ _ _ Hallt) => Hallps; last first.
      case: (None == Some v) /eqP =>// _; reflF.
      apply Hallps. by rewrite Forall_forall.
    have Hallpat: forall x, In x ps -> pattern_has_type s x.1 ty by
      rewrite -Forall_forall.
    rewrite {Hallps Hallt}.
    move: HallT Hallpat.
    case Hnull: (null ps); move: Hnull; case: ps => [_ HallT Hallpat|/= 
      [p1 tm1] ptl Hnull HallT Hallpat]//.
    + case: (None == Some v) /eqP=>// _. by reflF.
    + case Htm1': (typecheck_term s tm1) => [ty2 |]; last first.
        case: (None == Some v) /eqP=>// _. reflF.
        have: typecheck_term s tm1 == Some v. 
        apply /(ForallT_hd _ _ _ HallT). apply H7. by left.
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
          ++ move: Hisadt. case: t => [[m a] vs] Hisadt.
            apply is_vty_adt_some in Hisadt.
            case: Hisadt => [Hty [a_in m_in]].
            exists a. exists m. by exists vs. 
          ++ move=> x [<-// | Hinx]. by apply Hptl.
        -- reflF. have /eqP : typecheck_term s tm1 == Some v by 
            apply /(ForallT_hd _ _ _ HallT); apply H7; left.
          by rewrite Htm1'.
      * move=> /elimF /(_ erefl) Hnotall.
        case: (None == Some v) /eqP=>// _. reflF.
        apply Hnotall. move=> x Hinx.
        have->:ty2 = v. {
          have /eqP: typecheck_term s tm1 == Some v by
            apply /(ForallT_hd _ _ _ HallT); apply H7; left.
          by rewrite Htm1' =>/= [[]].
        }
        by apply H7; right.
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
    case Hisadt: (is_vty_adt s ty) => [t |]/=; last first.
      reflF. rewrite <- is_vty_adt_none_iff in Hisadt.
      case: H2 => [a [m [args [m_in [a_in Hty]]]]].
      apply (Hisadt a m args m_in a_in Hty).
    case: (typecheck_term s tm == Some ty) /Htm => Htm /=; last by reflF.
    have Hallt: (forall x, In x ps -> reflect (pattern_has_type s x.1 ty)
      (typecheck_pattern s x.1 ty)) by move=> x _; apply typecheck_pattern_correct.
    case: (all (fun x : pattern * formula => typecheck_pattern s x.1 ty) ps)
      /(forallb_ForallP _ _ _ Hallt) => Hallps/=; last by
      (reflF; rewrite Forall_forall in Hallps).
    case Hnull: (null ps) =>/=. reflF. by rewrite Hnull in H7.
    apply iff_reflect. split.
    + move=> Hmatch. inversion Hmatch; subst.
      move: HallT H6. clear. elim: ps => [// | [p1 f1] pt /= IH HallT Hall].
      apply /andP; split.
      * apply /(ForallT_hd _ _ _ HallT). by apply (Hall (p1, f1)); left. 
      * apply IH=>//. by inversion HallT. move=> x Hinx.
        by apply Hall; right.
    + move=> Hcheck. rewrite Forall_forall in Hallps. 
      constructor=>//; last by rewrite Hnull.
      * move: Hisadt. case: t => [[m a] vs] Hisadt.
        apply is_vty_adt_some in Hisadt.
        case: Hisadt => [Hty [a_in m_in]].
        exists a. exists m. by exists vs.
      *  move: HallT Hcheck. clear. 
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
  function implementation in RecFun2.v*)

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

(*Now, we come to the core of this: finding the list of
  indices such that the function is structurally 
  decreasing on these indices*)

(*Default values for fn, sn*)


Definition fn_d : fn :=
  (mk_fn id_fs sn_d tm_d).

Definition pn_d : pn :=
  (mk_pn (Build_predsym id_sym) sn_d Ftrue).


(*First, we need a decidable version of
  [decrease_fun] and [decrease_pred], assuming we already
  have fs and ps*)
Fixpoint check_decrease_fun (fs: list fn) (ps: list pn)
  (small: list vsymbol) (hd: option vsymbol) (m: mut_adt)
  (vs: list vty) (t: term) : bool :=
  (*Don't use any recursive instance*)
  (all (fun f => negb (funsym_in_tm (fn_sym f) t)) fs &&
  all (fun p => negb (predsym_in_tm (pn_sym p) t)) ps) ||
  match t with
  | Tfun f l ts =>
    (*Hard case:*)
    let idx := find (fun f' => fn_sym f' == f) fs in
    if (idx < length fs) then
      let f_decl := nth fn_d fs idx in
      
      match nth tm_d ts (sn_idx f_decl) with
      | Tvar x => 
        (x \in small) &&
        (l == map vty_var (s_params f)) &&
        all (check_decrease_fun fs ps small hd m vs) ts
        (* all (fun t => all (fun f => negb (funsym_in_tm (fn_sym f) t)) fs) ts &&
        all (fun t => all (fun p => negb (predsym_in_tm (pn_sym p) t)) ps) ts  *)
      | _ => false
      end 
    else 
      (*Not recursive*)
      all (fun t => check_decrease_fun fs ps small hd m vs t) ts
  (*Other hard cases - pattern matches*)
  | Tmatch (Tvar mvar) v pats =>
    if ((hd == Some mvar) || (mvar \in small)) then 
      match vty_m_adt m vs (snd mvar) with
      | Some _ =>
          all (fun x =>
          check_decrease_fun fs ps
          (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x))) 
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
          small)) (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)
          ) pats
      | None => false
      end
    (*Non-smaller cases*)
    else 
      all (fun x =>
        check_decrease_fun fs ps 
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats
  | Tmatch tm v pats =>
    check_decrease_fun fs ps small hd m vs tm &&
    all (fun x =>
      check_decrease_fun fs ps 
      (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats
  | Tlet t1 v t2 =>
    check_decrease_fun fs ps small hd m vs t1 &&
    check_decrease_fun fs ps (remove vsymbol_eq_dec v small) (upd_option hd v) m vs t2
  | Tif f1 t1 t2 =>
    check_decrease_pred fs ps small hd m vs f1 &&
    check_decrease_fun fs ps small hd m vs t1 &&
    check_decrease_fun fs ps small hd m vs t2
  | Teps f v =>
    check_decrease_pred fs ps (remove vsymbol_eq_dec v small) (upd_option hd v) m vs f
  | _ => true
  end

with check_decrease_pred (fs: list fn) (ps: list pn)
  (small: list vsymbol) (hd: option vsymbol) (m: mut_adt)
  (vs: list vty) (f: formula) : bool :=
  (*Don't use any recursive instance*)
  (all (fun f' => negb (funsym_in_fmla (fn_sym f') f)) fs &&
  all (fun p => negb (predsym_in_fmla (pn_sym p) f)) ps) ||
  match f with
  | Fpred p l ts =>
    (*Hard case:*)
    let idx := find (fun p' => pn_sym p' == p) ps in
    if (idx < length ps) then
      let p_decl := nth pn_d ps idx in
      
      match nth tm_d ts (sn_idx p_decl) with
      | Tvar x => 
        (x \in small) &&
        (l == map vty_var (s_params p)) &&
        all (check_decrease_fun fs ps small hd m vs) ts
        (* all (fun t => all (fun f => negb (funsym_in_tm (fn_sym f) t)) fs) ts &&
        all (fun t => all (fun p => negb (predsym_in_tm (pn_sym p) t)) ps) ts  *)
      | _ => false
      end 
    else 
      (*Not recursive*)
      all (fun t => check_decrease_fun fs ps small hd m vs t) ts
   (*Other hard cases - pattern matches*)
   | Fmatch (Tvar mvar) v pats =>
    if ((hd == Some mvar) || (mvar \in small)) then 
      match vty_m_adt m vs (snd mvar) with
      | Some _ =>
          all (fun x =>
          check_decrease_pred fs ps
          (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x))) 
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
          small)) (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)
          ) pats
      | None => false
      end
    (*Non-smaller cases*)
    else 
      all (fun x =>
        check_decrease_pred fs ps 
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats
  | Fmatch tm v pats =>
    check_decrease_fun fs ps small hd m vs tm &&
    all (fun x =>
      check_decrease_pred fs ps 
      (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats
  | Fnot f =>
    check_decrease_pred fs ps small hd m vs f 
  | Fquant q v f =>
    check_decrease_pred fs ps (remove vsymbol_eq_dec v small) (upd_option hd v) m vs f
  | Feq ty t1 t2 =>
    check_decrease_fun fs ps small hd m vs t1 &&
    check_decrease_fun fs ps small hd m vs t2
  | Fbinop b f1 f2 =>
    check_decrease_pred fs ps small hd m vs f1 &&
    check_decrease_pred fs ps small hd m vs f2
  | Flet t1 v f =>
    check_decrease_fun fs ps small hd m vs t1 &&
    check_decrease_pred fs ps (remove vsymbol_eq_dec v small) (upd_option hd v) m vs f
  | Fif f1 f2 f3 =>
    check_decrease_pred fs ps small hd m vs f1 &&
    check_decrease_pred fs ps small hd m vs f2 &&
    check_decrease_pred fs ps small hd m vs f3
  | _ => true
  end.

Lemma funsym_in_tmP: forall fs (t: term),
  reflect (forall (f: fn), In f fs -> negb (funsym_in_tm (fn_sym f) t))
    (all (fun f => negb (funsym_in_tm (fn_sym f) t)) fs).
Proof.
  move=> fs t.
  eapply equivP.
  2: apply Forall_forall.
  apply forallb_ForallP.
  move=> x Hinx.
  apply idP.
Qed.

Lemma predsym_in_tmP: forall ps (t: term),
  reflect (forall p, In p ps -> negb (predsym_in_tm (pn_sym p) t))
    (all (fun p => negb (predsym_in_tm (pn_sym p) t)) ps).
Proof.
  move=> ps t.
  eapply equivP.
  2: apply Forall_forall.
  apply forallb_ForallP.
  move=> x Hinx.
  apply idP.
Qed.

Lemma funsym_in_fmlaP: forall fs (fm: formula),
  reflect (forall (f: fn), In f fs -> negb (funsym_in_fmla (fn_sym f) fm))
    (all (fun f => negb (funsym_in_fmla (fn_sym f) fm)) fs).
Proof.
  move=> fs t.
  eapply equivP.
  2: apply Forall_forall.
  apply forallb_ForallP.
  move=> x Hinx.
  apply idP.
Qed.

Lemma predsym_in_fmlaP: forall ps (fm: formula),
  reflect (forall p, In p ps -> negb (predsym_in_fmla (pn_sym p) fm))
    (all (fun p => negb (predsym_in_fmla (pn_sym p) fm)) ps).
Proof.
  move=> ps t.
  eapply equivP.
  2: apply Forall_forall.
  apply forallb_ForallP.
  move=> x Hinx.
  apply idP.
Qed.

HB.instance Definition _ := hasDecEq.Build fn fn_eqb_spec.
HB.instance Definition _ := hasDecEq.Build pn pn_eqb_spec.

(*Handle case at beginning of most*)
Ltac not_in_tm_case fs ps t :=
  case: (all (fun (f: fn) => ~~ (funsym_in_tm (fn_sym f) t)) fs &&
    all (fun (p: pn) => ~~ (predsym_in_tm (pn_sym p) t)) ps)
    /(andPP (funsym_in_tmP fs t) (predsym_in_tmP ps t))=>/=;
  [move=> [Hnotf Hnotp]; apply ReflectT; by apply Dec_notin_t |].

Ltac not_in_fmla_case fs ps fm :=
  case: (all (fun (f: fn) => ~~ (funsym_in_fmla (fn_sym f) fm)) fs &&
    all (fun (p: pn) => ~~ (predsym_in_fmla (pn_sym p) fm)) ps)
    /(andPP (funsym_in_fmlaP fs fm) (predsym_in_fmlaP ps fm))=>/=;
  [move=> [Hnotf Hnotp]; apply ReflectT; by apply Dec_notin_f |].

(*Handle trivial cases for false*)
Ltac false_triv_case Hnot :=
  let C := fresh "C" in 
  apply ReflectF; intro C; inversion C; subst; try by apply Hnot.

(*It is not easy to prove this correct*)
Lemma check_decrease_spec fs ps m vs (t: term) (f: formula):
  NoDup (map fn_sym fs) ->
  NoDup (map pn_sym ps) ->
  (forall small hd,
    reflect (decrease_fun fs ps small hd m vs t)
      (check_decrease_fun fs ps small hd m vs t)) *
    (forall small hd,
      reflect (decrease_pred fs ps small hd m vs f)
        (check_decrease_pred fs ps small hd m vs f)).
Proof.
  move=> Hnodupf Hnodup.
  move: t f; apply term_formula_rect =>//=;
  try rewrite orbT.
  - move=> c small hh.
    apply ReflectT. apply Dec_const.
  - move=> v small hd.
    apply ReflectT. apply Dec_var.
  - (*Function case - hard one*)
    move=> f1 tys tms IHall small hd.
    (*First, handle case where fun/predsyms do not occur*)
    not_in_tm_case fs ps (Tfun f1 tys tms).
    (*Now, the main case*)
    move=> Hnotfp. (*Don't need fun/predsym info anymore*)
    rewrite -has_find.
    case: (has (fun f' : fn => fn_sym f' == f1) fs) /hasP => Hhas; last first.
    {
      (*First, do non-recursive (in constructed function) case*)
      have Hnotin: ~ In f1 (List.map fn_sym fs). {
        rewrite in_map_iff => [[x [Hf1 Hinx]]]; subst.
        apply Hhas. exists x. by apply/inP. by [].
      }
      have Hall: (forall x, x \in tms ->
        reflect (decrease_fun fs ps small hd m vs x)
          (check_decrease_fun fs ps small hd m vs x)).
      { 
        move {Hnotfp}.
        move: IHall.
        elim: tms =>[//= | h t /= IH Hall x].
        rewrite in_cons.
        case: (x == h) /eqP => [Hxh _ | Hneq/= Hint]; subst.
        - apply (ForallT_hd _ _ _ Hall).
        - apply IH=>//. apply (ForallT_tl _ _ _ Hall).
      }
      case: (all [eta check_decrease_fun fs ps small hd m vs] tms)
        /(all_Forall _ _ _ Hall) => Hall2.
      - apply ReflectT. apply Dec_fun_notin=>//.
        by rewrite -Forall_forall.
      - false_triv_case Hnotfp.
        apply Hall2. by apply Forall_forall.
    }
    (*Now we handle the recursive case*)
    move: Hhas => /hasP Hhas.
    have /eqP Hnth :=nth_find fn_d Hhas.
    (*Here, need NoDup, so that f_decl actually equals
      find ...*)
    have Hntheq: forall f_decl, In f_decl fs ->
      f1 = fn_sym f_decl ->
      f_decl = (nth fn_d fs
      (find (fun f' : fn => fn_sym f' == fn_sym f_decl) fs)).
    {
      move=> f_decl Hin Hf1.
      apply (NoDup_map_in Hnodupf)=>//.
      + apply /inP. apply mem_nth. rewrite -has_find. apply /hasP.
        exists f_decl=>//. by apply /inP.
      + subst. by rewrite Hnth.
     }
    have Hinmap: In f1 (List.map fn_sym fs). {
      rewrite in_map_iff. eexists. split; [apply Hnth |].
      apply /inP. apply mem_nth. by rewrite -has_find. 
    }
    (*We have to case on the term, only 1 case is interesting;
      there are a lot of trivial ones*)
    case Hntht: (nth tm_d tms
    (sn_idx (nth fn_d fs (find (fun f' : fn => fn_sym f' == f1) fs))))
    => [| v | | | | |];
    try (apply ReflectF; intros C; inversion C; subst;
    try (by apply Hnotfp);
    try (rewrite -(Hntheq f_decl ltac:(assumption) erefl) in
      Hntht;
      match goal with
      | H1: List.nth ?i ?tms ?tm_d = ?x, H2: nth ?tm_d ?tms ?i = ?y |- _ =>
        rewrite nth_eq in H1; rewrite H1 in H2; try discriminate end);
    try contradiction
    ).
    case: (v \in small) /inP => Hinv/=; last first.
    {
      false_triv_case Hnotfp.
      rewrite nth_eq in H9. 
      rewrite -(Hntheq f_decl H2 erefl) in Hntht.
      rewrite H9 in Hntht. by injection Hntht => Hxy; subst.
    }
    case: (tys == map vty_var (s_params f1)) /eqP => Htys/=; last
    by false_triv_case Hnotfp.
    case: ((all (check_decrease_fun fs ps small hd m vs) tms)) 
    /allP => Halldec.
    + (*The case where we actually say true*)
      apply ReflectT.
      apply Dec_fun_in with(x:=v)(f_decl:=(nth fn_d fs (find (fun x => fn_sym x == f1) fs))) =>//.
      * apply /inP. apply mem_nth. by rewrite -has_find.
      * by rewrite nth_eq.
      * rewrite Forall_forall. move=> x /inP Hinx.
        move: Halldec => /(_ _ Hinx).
        apply ForallT_In with (x:=x) in IHall; 
        [| by apply term_eq_dec | by apply /inP ].
        by move: IHall => /(_ small hd) [].
    + (*One final contradiction case*)
      false_triv_case Hnotfp.
      apply Halldec. 
      move => y /inP Hiny.
      move: H11; rewrite Forall_forall; move => /(_ y Hiny).
      apply ForallT_In with (x:=y) in IHall => //; last
        by apply term_eq_dec.
      by move: IHall => /(_ small hd) [].
  - move=> tm1 v tm2 IH1 IH2 small hd.
    not_in_tm_case fs ps (Tlet tm1 v tm2).
    move => Hnotin.
    case: (IH1 small hd)=> Hdec1/=; last by false_triv_case Hnotin.
    case: (IH2 (remove vsymbol_eq_dec v small) (upd_option hd v))=> 
      Hdec2/=; last by false_triv_case Hnotin.
    apply ReflectT. by apply Dec_tlet.
  - (*should automate these cases more*)
    move=> f t1 t2 IH1 IH2 IH3 small hd.
    not_in_tm_case fs ps (Tif f t1 t2).
    move=> Hnotin.
    case: (IH1 small hd)=> Hdec1/=; last by false_triv_case Hnotin.
    case: (IH2 small hd)=> Hdec2/=; last by false_triv_case Hnotin.
    case: (IH3 small hd)=> Hdec3/=; last by false_triv_case Hnotin.
    apply ReflectT. by apply Dec_tif.
  - (*Match case - other hard one*) 
    move=> tm v pats IH1 IHall small hd.
    not_in_tm_case fs ps (Tmatch tm v pats).
    move=> Hnotin.
    move: IH1 Hnotin.
    (*Most of the cases are the same. First, prove a lemma*)
    have Hall: forall small hd,
      reflect (forall x, In x pats ->
        decrease_fun fs ps (small x) (hd x) m vs (snd x))
        (all (fun x => check_decrease_fun fs ps (small x) (hd x) m vs (snd x)) pats).
    {
      move=> s h. eapply equivP. 2: apply Forall_forall.
      apply forallb_ForallP.
      move=> x /inP.
      move: IHall. elim: pats => [// | h' t' /= IH Hall].
      rewrite in_cons. case: (x == h') /eqP => Hxh /= => [_ | Hint]; subst.
      - apply (ForallT_hd _ _ _ Hall).
      - apply IH=>//. apply (ForallT_tl _ _ _ Hall).
    }
    case: tm;
    (*all cases but 1 are identical*)
    try (intros; case: (IH1 small hd) => Hdec1/=;
      [| by false_triv_case Hnotin];
      case: (Hall (fun x =>(remove_all vsymbol_eq_dec (pat_fv x.1) small) )
        (fun x => (upd_option_iter hd (pat_fv x.1)))) => Hall1;
      [| by false_triv_case Hnotin];
      apply ReflectT; apply Dec_tmatch_rec=>//;
      move=> [var [Hvar _]]; discriminate).
    (*Now we come to the variable case*)
    move=> mvar IH1 Hnotin.
    case: (@orP ((hd == Some mvar)) ((mvar \in small))) => Hmvar; last first.
    {
      case: (Hall (fun x =>(remove_all vsymbol_eq_dec (pat_fv x.1) small) )
        (fun x => (upd_option_iter hd (pat_fv x.1)))) => Hall1;
        last first.
        {
          false_triv_case Hnotin.
          apply Hmvar. by case: H2 => Hcon; [left; apply /eqP | right; apply /inP].
        }
      apply ReflectT. apply Dec_tmatch_rec=>//.
      - move=> [var [[Heq] Hvar]]; subst.
        apply Hmvar. by case: Hvar => Hcon; [left; apply /eqP | right; apply /inP].
      - by apply Dec_notin_t.
    }
    case Hadt: (vty_m_adt m vs (snd mvar)) => [a |]/=; last first.
    {
      false_triv_case Hnotin. eapply vty_m_adt_none in Hadt.
      apply Hadt. apply H8. by [].
      apply H6. exists mvar. split=>//. 
      by case: Hmvar => Hcon; [left; apply /eqP | right; apply /inP].
    }
    case: (Hall (fun x =>  (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs x.1))
    (remove_all vsymbol_eq_dec (pat_fv x.1) small)))
    (fun x => (upd_option_iter hd (pat_fv x.1))))=> Hallin;
    last first.
    {
      false_triv_case Hnotin. apply H6.
      exists mvar. split=>//. 
      by case: Hmvar => Hcon; [left; apply /eqP | right; apply /inP].
    }
    apply ReflectT.
    apply vty_m_adt_some in Hadt. case: Hadt => [a_in mvar_eq].
    apply Dec_tmatch with(a:=a)=>//.
    by case: Hmvar => Hcon; [left; apply /eqP | right; apply /inP].
  - move=> f v IH small hd.
    not_in_tm_case fs ps (Teps f v).
    move => Hnotin.
    case: (IH (remove vsymbol_eq_dec v small) (upd_option hd v))=> 
      Hdec2/=; last by false_triv_case Hnotin.
    apply ReflectT. by apply Dec_eps.
  - (*Now, formula proof*)
    (*copy Tfun for now*)
    move=> p1 tys tms IHall small hd.
    (*First, handle case where fun/predsyms do not occur*)
    not_in_fmla_case fs ps (Fpred p1 tys tms).
    (*Now, the main case*)
    move=> Hnotfp. (*Don't need fun/predsym info anymore*)
    rewrite -has_find.
    case: (has (fun p' : pn => pn_sym p' == p1) ps) /hasP => Hhas; last first.
    {
      (*First, do non-recursive (in constructed function) case*)
      have Hnotin: ~ In p1 (List.map pn_sym ps). {
        rewrite in_map_iff => [[x [Hf1 Hinx]]]; subst.
        apply Hhas. exists x. by apply/inP. by [].
      }
      have Hall: (forall x, x \in tms ->
        reflect (decrease_fun fs ps small hd m vs x)
          (check_decrease_fun fs ps small hd m vs x)).
      { 
        move {Hnotfp}.
        move: IHall.
        elim: tms =>[//= | h t /= IH Hall x].
        rewrite in_cons.
        case: (x == h) /eqP => [Hxh _ | Hneq/= Hint]; subst.
        - apply (ForallT_hd _ _ _ Hall).
        - apply IH=>//. apply (ForallT_tl _ _ _ Hall).
      }
      case: (all [eta check_decrease_fun fs ps small hd m vs] tms)
        /(all_Forall _ _ _ Hall) => Hall2.
      - apply ReflectT. apply Dec_pred_notin=>//.
        by rewrite -Forall_forall.
      - false_triv_case Hnotfp.
        apply Hall2. by apply Forall_forall.   
    }
    (*Now we handle the recursive case*)
    move: Hhas => /hasP Hhas.
    have /eqP Hnth :=nth_find pn_d Hhas.
    (*Here, need NoDup, so that f_decl actually equals
      find ...*)
    have Hntheq: forall p_decl, In p_decl ps ->
      p1 = pn_sym p_decl ->
      p_decl = (nth pn_d ps
      (find (fun p' : pn => pn_sym p' == pn_sym p_decl) ps)).
    {
      move=> p_decl Hin Hf1.
      apply (NoDup_map_in Hnodup)=>//.
      + apply /inP. apply mem_nth. rewrite -has_find. apply /hasP.
        exists p_decl=>//. by apply /inP.
      + subst. by rewrite Hnth.
     }
    have Hinmap: In p1 (List.map pn_sym ps). {
      rewrite in_map_iff. eexists. split; [apply Hnth |].
      apply /inP. apply mem_nth. by rewrite -has_find. 
    }
    (*We have to case on the term, only 1 case is interesting;
      there are a lot of trivial ones*)
    case Hntht: (nth tm_d tms
    (sn_idx (nth pn_d ps (find (fun p' : pn => pn_sym p' == p1) ps))))
    => [| v | | | | |];
    try (apply ReflectF; intros C; inversion C; subst;
    try (by apply Hnotfp);
    try (rewrite -(Hntheq p_decl ltac:(assumption) erefl) in
      Hntht;
      match goal with
      | H1: List.nth ?i ?tms ?tm_d = ?x, H2: nth ?tm_d ?tms ?i = ?y |- _ =>
        rewrite nth_eq in H1; rewrite H1 in H2; try discriminate end);
    try contradiction
    ).
    case: (v \in small) /inP => Hinv/=; last first.
    {
      false_triv_case Hnotfp.
      rewrite nth_eq in H9. 
      rewrite -(Hntheq p_decl H2 erefl) in Hntht.
      rewrite H9 in Hntht. by injection Hntht => Hxy; subst.
    }
    case: (tys == map vty_var (s_params p1)) /eqP => Htys/=; last
    by false_triv_case Hnotfp.
    case: ((all (check_decrease_fun fs ps small hd m vs) tms)) 
    /allP => Halldec.
    + (*The case where we actually say true*)
      apply ReflectT.
      apply Dec_pred_in with(x:=v)(p_decl:=(nth pn_d ps (find (fun x => pn_sym x == p1) ps))) =>//.
      * apply /inP. apply mem_nth. by rewrite -has_find.
      * by rewrite nth_eq.
      * rewrite Forall_forall. move=> x /inP Hinx.
        move: Halldec => /(_ _ Hinx).
        apply ForallT_In with (x:=x) in IHall; 
        [| by apply term_eq_dec | by apply /inP ].
        by move: IHall => /(_ small hd) [].
    + (*One final contradiction case*)
      false_triv_case Hnotfp.
      apply Halldec. 
      move => y /inP Hiny.
      move: H11; rewrite Forall_forall; move => /(_ y Hiny).
      apply ForallT_In with (x:=y) in IHall => //; last
        by apply term_eq_dec.
      by move: IHall => /(_ small hd) [].
  - move=> q v f IH small hd.
    not_in_fmla_case fs ps (Fquant q v f) => Hnotin.
    case: (IH (remove vsymbol_eq_dec v small) (upd_option hd v)) =>Hdec;
    last by false_triv_case Hnotin.
    apply ReflectT. by apply Dec_quant.
  - move=> v t1 t2 IH1 IH2 small hd.
    not_in_fmla_case fs ps (Feq v t1 t2)=> Hnotin.
    case: (IH1 small hd)=> Hdec1; last by false_triv_case Hnotin.
    case: (IH2 small hd)=>Hdec2; last by false_triv_case Hnotin.
    apply ReflectT. by apply Dec_eq.
  - move=> b f1 f2 IH1 IH2 small hd.
    not_in_fmla_case fs ps (Fbinop b f1 f2)=> Hnotin.
    case: (IH1 small hd)=> Hdec1; last by false_triv_case Hnotin.
    case: (IH2 small hd)=> Hdec2; last by false_triv_case Hnotin.
    apply ReflectT. by apply Dec_binop.
  - move=> f IH small hd.
    not_in_fmla_case fs ps (Fnot f)=> Hnotin.
    case: (IH small hd)=> Hdec; last by false_triv_case Hnotin.
    apply ReflectT. by apply Dec_not.
  - move=> small hd. apply ReflectT. apply Dec_true.
  - move=> small hd. apply ReflectT. apply Dec_false.
  - move=> tm v f IH1 IH2 small hd.
    not_in_fmla_case fs ps (Flet tm v f)=> Hnotin.
    case: (IH1 small hd)=>Hdec1; last by false_triv_case Hnotin.
    case: (IH2 (remove vsymbol_eq_dec v small) (upd_option hd v))=> Hdec2;
      last by false_triv_case Hnotin.
    apply ReflectT. by apply Dec_flet.
  - move=> f1 f2 f3 IH1 IH2 IH3 small hd.
    not_in_fmla_case fs ps (Fif f1 f2 f3) => Hnotin.
    case: (IH1 small hd)=> Hdec1; last by false_triv_case Hnotin.
    case: (IH2 small hd)=> Hdec2; last by false_triv_case Hnotin.
    case: (IH3 small hd)=> Hdec3; last by false_triv_case Hnotin.
    apply ReflectT. by apply Dec_fif.
  -  (*Match case - other hard one*) 
    move=> tm v pats IH1 IHall small hd.
    not_in_fmla_case fs ps (Fmatch tm v pats).
    move=> Hnotin.
    move: IH1 Hnotin.
    (*Most of the cases are the same. First, prove a lemma*)
    have Hall: forall small hd,
      reflect (forall x, In x pats ->
        decrease_pred fs ps (small x) (hd x) m vs (snd x))
        (all (fun x => check_decrease_pred fs ps (small x) (hd x) m vs (snd x)) pats).
    {
      move=> s h. eapply equivP. 2: apply Forall_forall.
      apply forallb_ForallP.
      move=> x /inP.
      move: IHall. elim: pats => [// | h' t' /= IH Hall].
      rewrite in_cons. case: (x == h') /eqP => Hxh /= => [_ | Hint]; subst.
      - apply (ForallT_hd _ _ _ Hall).
      - apply IH=>//. apply (ForallT_tl _ _ _ Hall).
    }
    case: tm;
    (*all cases but 1 are identical*)
    try (intros; case: (IH1 small hd) => Hdec1/=;
      [| by false_triv_case Hnotin];
      case: (Hall (fun x =>(remove_all vsymbol_eq_dec (pat_fv x.1) small) )
        (fun x => (upd_option_iter hd (pat_fv x.1)))) => Hall1;
      [| by false_triv_case Hnotin];
      apply ReflectT; apply Dec_fmatch_rec=>//;
      move=> [var [Hvar _]]; discriminate).
    (*Now we come to the variable case*)
    move=> mvar IH1 Hnotin.
    case: (@orP ((hd == Some mvar)) ((mvar \in small))) => Hmvar; last first.
    {
      case: (Hall (fun x =>(remove_all vsymbol_eq_dec (pat_fv x.1) small) )
        (fun x => (upd_option_iter hd (pat_fv x.1)))) => Hall1;
        last first.
        {
          false_triv_case Hnotin.
          apply Hmvar. by case: H2 => Hcon; [left; apply /eqP | right; apply /inP].
        }
      apply ReflectT. apply Dec_fmatch_rec=>//.
      - move=> [var [[Heq] Hvar]]; subst.
        apply Hmvar. by case: Hvar => Hcon; [left; apply /eqP | right; apply /inP].
      - by apply Dec_notin_t.
    }
    case Hadt: (vty_m_adt m vs (snd mvar)) => [a |]/=; last first.
    {
      false_triv_case Hnotin. eapply vty_m_adt_none in Hadt.
      apply Hadt. apply H8. by [].
      apply H6. exists mvar. split=>//. 
      by case: Hmvar => Hcon; [left; apply /eqP | right; apply /inP].
    }
    case: (Hall (fun x =>  (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs x.1))
    (remove_all vsymbol_eq_dec (pat_fv x.1) small)))
    (fun x => (upd_option_iter hd (pat_fv x.1))))=> Hallin;
    last first.
    {
      false_triv_case Hnotin. apply H6.
      exists mvar. split=>//. 
      by case: Hmvar => Hcon; [left; apply /eqP | right; apply /inP].
    }
    apply ReflectT.
    apply vty_m_adt_some in Hadt. case: Hadt => [a_in mvar_eq].
    apply Dec_fmatch with(a:=a)=>//.
    by case: Hmvar => Hcon; [left; apply /eqP | right; apply /inP].
Qed.

Definition check_decrease_fun_spec fs ps m vs (t: term) small hd
  (Hn1: NoDup (map fn_sym fs))
  (Hn2: NoDup (map pn_sym ps)):=
  (fst (check_decrease_spec fs ps m vs t Ftrue Hn1 Hn2)) small hd.

Definition check_decrease_pred_spec fs ps m vs (f: formula) small hd
  (Hn1: NoDup (map fn_sym fs))
  (Hn2: NoDup (map pn_sym ps)):=
  (snd (check_decrease_spec fs ps m vs tm_d f Hn1 Hn2)) small hd.


(*Now we need to find the list of is, m, and vs
  such that the conditions we need hold. The following method
  is not efficient (ideally this should be done lazily)
  but it is relatively simple: we generate all possible lists
  and check each one. For small-ish mutually recursive functions,
  this is not too bad*)

(*First, generate the lists*)
(*Generate all lists of length n with element i bounded between
0 and f(i)*)
Fixpoint get_lists_bound (f: nat -> nat) (n: nat) : list (list nat) :=
  match n with
  | O => [nil]
  | S n' =>
    let l_n' := get_lists_bound f n' in
    (*Idea: take all lists of length n-1, make f(n) copies of each,
      each one with 1 element from 0 to f(n)
      *)
    (*NOTE: should really reverse at end instead of concat (or something)
    but oh well*)
    concat (map (fun l => (map (fun i => rcons l i) (iota 0 (f(n'))))) l_n')
  end.

Lemma concatP {A: eqType} (l: list (list A)) (x: A):
  reflect (exists2 y, y \in l & x \in y) (x \in (concat l)).
Proof.
  apply iff_reflect. rewrite -(reflect_iff _ _ (inP _ _)).
  rewrite in_concat. split; intros [y Hy]; destruct_all; 
  exists y; try split; 
  try apply /inP; auto.
Qed.

Lemma length_size {A: Type} (l: list A):
  length l = size l.
Proof.
  by [].
Qed. 

Lemma nil_or_rcons {A: Type} (l: list A):
  l = nil \/ exists t h, l = rcons t h.
Proof.
  elim: l => [//= | h1 t1 /= IH]; first by left.
  right. case: IH => [-> | [t2 [h2 Ht1]]].
  - exists nil. by exists h1.
  - subst. exists (h1 :: t2). exists h2.
    by rewrite rcons_cons.
Qed. 

Lemma get_lists_bound_spec (f: nat -> nat) (n: nat) (l: list nat):
  reflect (length l = n /\ (forall i, i < length l ->
    nth 0 l i < f (i))) (l \in (get_lists_bound f n)).
Proof.
  move: l.
  elim: n => [l | n' IH l]/=.
  - rewrite in_cons orbF.
    case: (l == nil) /eqP => Hnil; [apply ReflectT | apply ReflectF].
    + rewrite -length_zero_iff_nil in Hnil. 
      by rewrite Hnil.
    + move=> [Hlen _]. by rewrite length_zero_iff_nil in Hlen.
  - case: (l
  \in concat
        [seq [seq rcons l0 i | i <- iota 0 (f n')] | l0 <- get_lists_bound f n'])
    /concatP=> Hex; [apply ReflectT | apply ReflectF].
  (*Note: need to get Prop before destructing exists*)
  + move: Hex => [l' /mapP [l'' Hinl'' Hl'] Hinl]; subst.
    move: Hinl => /mapP [i Hini Hl]; subst.
    move: Hinl''.
    case: (IH l'') => // [[Hlenl'' Hl'']] _.
    rewrite length_size in Hlenl'' Hl''.
    rewrite length_size size_rcons Hlenl''.
    split=>//.
    move=> [_/=| j'].
    * rewrite nth_rcons.
      move: Hlenl'' Hl''. case: l''=>/= [Hn' _ | h l' Hlenl' Hl']; subst.
      -- by rewrite mem_iota in Hini.
      -- by apply Hl'.
    * rewrite ltnS=> Hj.
      rewrite nth_rcons. subst.
      move: Hj. rewrite leq_eqVlt => /orP[Hj1 | Hj1];
      rewrite Hj1.
      -- move: Hj1 => /eqP Hj1. rewrite Hj1 ltnn.
        by rewrite mem_iota in Hini.
      -- by apply Hl''.
  + (*Now, the reverse direction*)
    move=> [Hlenl Hl].
    (*We show that there must be a list with the properties*)
    case (nil_or_rcons l) => [Hleq | [t [h Hleq]]]; subst=>//.
    rewrite length_size size_rcons in Hl Hlenl.
    case: Hlenl => Hn; subst.
    apply Hex.
    exists [seq rcons t i | i <- iota 0 (f (size t))].
    * apply /mapP. exists t=>//.
      (*Now, we prove that t is in [get_lists_bound]*)
      case: (IH t)=>//.
      move=> C. exfalso. apply C. rewrite {C}.
      split=>//.
      move=> i. rewrite length_size.
      move=> Hi.
      move: Hl => /( _ i (ltn_trans Hi (ltnSn _))).
      by rewrite nth_rcons Hi.
    * apply /mapP. exists h=>//. rewrite mem_iota/= add0n.
      move: Hl => /( _ (size t) (ltnSn _)).
      by rewrite nth_rcons ltnn eq_refl.
Qed.

(*Now, we define the test for finding the mutual adt and args,
  as well as checking termination, given a list of potential
  indices*)

Definition find_mut_args (fs: list fn) (ps: list pn) (il: list nat) :
  option (mut_adt * list vty) :=

  (*First, get candidates*)
  let sns := map fn_sn fs ++ map pn_sn ps in
  match sns with
  | nil => None
  | hd :: tl => 
    let i := nth 0 il 0 in
    match (is_vty_adt gamma (snd (nth vs_d (sn_args hd) i))) with
    | Some (m, _, vs) => 
      (*Check if size vs = size (m_params m)*)
      (*NOTE: may be implied by typing, but we check it anyway*)
      if (size vs =? size (m_params m))%nat &&
       (*Check using is list*)
       all (fun x =>
       let i := fst x in
       let s := snd x in
       vty_in_m m vs (snd (nth vs_d (sn_args s) i))) 
       (combine il sns) &&
      (*And check termination*)
      all (fun x =>
        let i := fst x in
        let f : fn := snd x in
        check_decrease_fun fs ps nil
        (Some (nth vs_d (sn_args f) i )) m vs (fn_body f))
        (combine (take (size fs) il) fs) &&
      all (fun x =>
        let i := fst x in
        let p : pn := snd x in
        check_decrease_pred fs ps nil
        (Some (nth vs_d (sn_args p) i)) m vs (pn_body p))
        (combine (drop (size fs) il) ps)
      then Some (m, vs)
      else None
    | None => None
    end
  end.

Definition mut_adt_eqb (m1 m2: mut_adt) : bool :=
  mut_adt_dec m1 m2.

Lemma mut_adt_eqb_spec (m1 m2: mut_adt) :
  reflect (m1 = m2) (mut_adt_eqb m1 m2).
Proof.
  unfold mut_adt_eqb. destruct (mut_adt_dec m1 m2); subst; simpl;
  [apply ReflectT | apply ReflectF]; auto.
Qed.

HB.instance Definition _ := hasDecEq.Build mut_adt mut_adt_eqb_spec.
HB.instance Definition _ := hasDecEq.Build sn sn_eqb_spec.

Lemma list_map_map {A B: Type} (f: A -> B) (l: list A):
  List.map f l = map f l.
Proof.
by [].
Qed.

Lemma app_cat {A: Type} (l1 l2: list A):
  (l1 ++ l2)%list = l1 ++ l2.
Proof. by []. Qed.

Lemma combineP {A B: eqType} (l1: list A) (l2: list B) x:
  size l1 = size l2 ->
  reflect (exists i, i < size l1 /\
    forall d1 d2,
    x = (nth d1 l1 i, nth d2 l2 i))
  (x \in (combine l1 l2)).
Proof.
  move=> Hsz. apply iff_reflect.
  rewrite -(reflect_iff _ _ (inP x (combine l1 l2))).
  rewrite in_combine_iff; last by rewrite !length_size.
  rewrite length_size.
  by split => [[i [Hi Hx]] | [i [Hi Hx]]]; exists i; split; (try by apply /ltP);
  move=> d1 d2; rewrite (Hx d1 d2) !nth_eq.
Qed.

(*And the spec*)
(*Do with all ssreflect functions, fix later*)
Lemma find_mut_args_spec (fs: list fn) (ps: list pn) (il: list nat) m vs:
  size il = (size fs + size ps) ->
  (*il agrees with sn_idx*)
  (forall i, i < size il -> 
    sn_idx (nth sn_d (map fn_sn fs ++ map pn_sn ps) i) =
    nth 0 il i) ->
  (*At least one list should not be nil*)
  ((size fs + size ps) != 0) ->
  (*Cannot have duplicate ADTs - this is implied by
    wf_context (see [mut_adts_inj]), so there are no
    circular dependencies*)
  (forall (m1 m2: mut_adt) {a1 a2: alg_datatype},
    mut_in_ctx m1 gamma ->
    mut_in_ctx m2 gamma ->
    adt_in_mut a1 m1 ->
    adt_in_mut a2 m2 ->
    adt_name a1 = adt_name a2 ->
    m1 = m2) ->
  (*From spec for decrease_fun and pred*)
  NoDup (map fn_sym fs) ->
  NoDup (map pn_sym ps) ->
  reflect (size vs = size (m_params m) /\
    mut_in_ctx m gamma /\
    (forall f, f \in fs ->
      vty_in_m m vs (snd (nth vs_d (sn_args f) (sn_idx f)))) /\
    (forall p, p \in ps ->
      vty_in_m m vs (snd (nth vs_d (sn_args p) (sn_idx p) ))) /\
    (forall f, f \in fs ->
       decrease_fun fs ps nil 
      (Some (nth vs_d (sn_args f) (sn_idx f))) m vs (fn_body f)) /\
    (forall p, p \in ps ->
      decrease_pred fs ps nil 
      (Some (nth vs_d (sn_args p) (sn_idx p))) m vs (pn_body p)))
    (find_mut_args fs ps il == Some (m, vs)).
Proof.
  rewrite /find_mut_args. move=>Hlen Hileq Hnotemp Hadtsuniq Hn1 Hn2.
  case Happ: ([seq fn_sn i | i <- fs] ++ [seq pn_sn i | i <- ps]) => [| shd stl].
  {
    (*Nil case is not very intersting - contradicts assumption*)
    apply ReflectF. exfalso.
    case: (negP Hnotemp). apply /eqP.
    by rewrite -(size_map fn_sn) -(size_map pn_sn) -size_cat Happ.
  }
  (*Some cleanup*)
  rewrite {Hnotemp}.
  have Hlen': size il = size ([seq fn_sn i | i <- fs] ++ [seq pn_sn i | i <- ps])
    by rewrite size_cat !size_map.
  rewrite {Hlen}. move: Hlen' => Hlen.
  (*First, we make a simplification: we don't want to consider
    fs and ps separately for vty_in_m*)
  have Hvtymeq: ((forall f,
    f \in fs -> vty_in_m m vs (nth vs_d (sn_args f) (sn_idx f)).2) /\
  (forall p ,
    p \in ps -> vty_in_m m vs (nth vs_d (sn_args p) (sn_idx p)).2) <->
  (forall s, s \in [seq fn_sn i | i <- fs] ++ [seq pn_sn i | i <- ps] ->
    vty_in_m m vs (nth vs_d (sn_args s) (sn_idx s)).2)). {
    split.
    - move=> [Hf Hp] s. rewrite mem_cat => /orP [/mapP [x Hinx Hsx]|
      /mapP [x Hinx Hsx]]; subst.
      by rewrite Hf. by rewrite Hp.
    - move=> Hs. by split=> s Hins; apply Hs; rewrite mem_cat; apply /orP;
      [left | right]; apply /mapP; exists s.
  }
  (*Now we see if the first element has an ADT in the correct place*)
  case Hisadt: (is_vty_adt gamma (nth vs_d (sn_args shd) (nth 0 il 0)).2) => [ [[m' a] vs']| ];
  last first.
  {
    (*If not, we must prove a contradiction - it is not hard,
      but there are a lot of parts*)
    apply ReflectF => [[Hlen' [m_in [Hfsm [Hpsm _]]]]].
    (*With the lemma we just proved, we consider the fs and ps cases
      together*)
    rewrite Happ in Hvtymeq.
    case: Hvtymeq => [/(_ (conj Hfsm Hpsm) _ (mem_head _ _)) 
      /vty_in_m_spec [a [a_in Hnth]]  _].
    move: Hisadt. rewrite -Hileq/=; last by rewrite Hlen Happ.
    rewrite Happ/= -is_vty_adt_none_iff => Hadt.
    by apply (Hadt a m vs).
  }
  apply is_vty_adt_some in Hisadt.
  case: Hisadt => [Hnth [a_in m_in]].
  (*Now we prove that this "candidate" is sufficient:
    if the fs and ps all have a mutual type m vs,
    it must be this m' and vs'*)
  have Hsuffices: ( forall m,
    mut_in_ctx m gamma ->
    (forall s,
           s \in [seq fn_sn i | i <- fs] ++ [seq pn_sn i | i <- ps] ->
           vty_in_m m vs (nth vs_d (sn_args s) (sn_idx s)).2) ->
    m = m' /\ vs = vs').
  {
    move=> m1 m1_in.
    rewrite Happ => /(_ _ (mem_head _ _)) /vty_in_m_spec 
    [a' [a_in' Hnth']].
    move: Hnth. rewrite -Hileq/=; last by rewrite Hlen Happ.
    rewrite Happ/= Hnth' => [[Hname Hvs]]; subst.
    split=>//. by apply (Hadtsuniq m1 m' a' a).
  }
  (*Now, we continue*)
  case: (size vs' =? size (m_params m'))%nat /eqP=>/= Hszvs; last first.
  {
    apply ReflectF => [[Hlenvs [m_in' [Hfsm [Hpsm _]]]]].
    (*Now from our previous results, m=m' and vs=vs'*)
    have [Hm Hvs]: m = m' /\ vs = vs' by apply Hsuffices=>//; apply Hvtymeq.
    subst.
    by apply Hszvs.
  }
  (*Check for mut args*)
  case: (all (fun x : nat * sn => vty_in_m m' vs' (nth vs_d (sn_args x.2) x.1).2)
  (combine il (shd :: stl))) /allP => Hallvty/=; last first.
  {
    apply ReflectF => [[Hlenvs [m_in' [Hfsm [Hpsm _]]]]].
    have [Hm Hvs]: m = m' /\ vs = vs' by apply Hsuffices=>//; apply Hvtymeq.
    subst.
    apply Hallvty=> x /combineP.
    rewrite -{1}Happ {1}Hlen => /(_ erefl ) [i [Hi /(_ 0 sn_d) Hx]]; subst.
    rewrite /=. rewrite -Hileq// Happ.
    apply Hvtymeq=>//. by rewrite Happ mem_nth // -Happ -Hlen.
  }
  have Hsztake: size (take (size fs) il) = size fs. {
    rewrite size_take Hlen size_cat !size_map.
    have: (size fs <= size fs + size ps) by rewrite leq_addr.
    rewrite leq_eqVlt => /orP[/eqP Hsz | Hlt].
    - have: (size ps = 0). {
        rewrite addnC in Hsz.
        apply (f_equal (fun x => x - size fs)) in Hsz.
        by rewrite -addnBA // subnn addn0 in Hsz.
      }
      move->. by rewrite addn0 ltnn.
    - by rewrite Hlt.
  }
  have Hsz': size fs <= size il by
          rewrite Hlen size_cat !size_map leq_addr.
  have Hsz'': forall i, i < size ps -> size fs + i < size il by
    move=> i Hi; rewrite Hlen size_cat !size_map ltn_add2l.
  have Hszps: size il - size fs = size ps by
    rewrite Hlen size_cat !size_map addnC -addnBA // subnn addn0.
  (*Finally, check for termination*)
  case: (all
    (fun x : nat * fn =>
    check_decrease_fun fs ps [::] (Some (nth vs_d (sn_args x.2) x.1)) m' vs'
      (fn_body x.2)) (combine (take (size fs) il) fs) &&
  all
    (fun x : nat * pn =>
    check_decrease_pred fs ps [::] (Some (nth vs_d (sn_args x.2) x.1)) m' vs'
      (pn_body x.2)) (combine (drop (size fs) il) ps)) 
  /(andPP allP allP) => Hdec; last first.
  {
    apply ReflectF => [[Hlenvs [m_in' [Hfsm [Hpsm [Hdecf Hdecp]]]]]].
    have [Hm Hvs]: m = m' /\ vs = vs' by apply Hsuffices=>//; apply Hvtymeq.
    subst.
    apply Hdec. split; move=> x /combineP. (*Cases are similar*)
    - rewrite Hsztake => /(_ erefl) [i [Hi /(_ 0 fn_d)]].
      rewrite nth_take // => Hx; subst=>/=.
      rewrite -Hileq; last by rewrite (leq_trans Hi Hsz').
      rewrite nth_cat size_map Hi (nth_map fn_d) //.
      apply /check_decrease_fun_spec =>//.
      apply Hdecf. by rewrite mem_nth.
    - (*Similar, but drop instead of take - lemma is easier*)
      rewrite size_drop Hszps.
      move=> /(_ erefl) [i [Hi /(_ 0 pn_d)]].
      rewrite nth_drop // => Hx; subst=>/=.
      rewrite -Hileq //; last by apply Hsz''. 
      rewrite nth_cat size_map ltnNge leq_addr/=
        addnC -addnBA // subnn addn0 (nth_map pn_d) //.
      apply /check_decrease_pred_spec =>//.
      apply Hdecp. by rewrite mem_nth.
  }
  (*Finally, the last case*)
  case : (Some (m', vs') == Some (m, vs)) /eqP => [[Hm Hvs] | Hneq];
  last first.
  {
    (*Easy contradiction*)
    apply ReflectF => [[Hlenvs [m_in' [Hfsm [Hpsm [Hdecf Hdecp]]]]]].
    have [Hm Hvs]: m = m' /\ vs = vs' by apply Hsuffices=>//; apply Hvtymeq.
    subst. by apply Hneq.
  }
  
  (*The true case*)
  apply ReflectT.
  subst.
  (*We prove both vy_in_m's together*)
  have Hallvtys: (forall s ,
    s \in [seq fn_sn i | i <- fs] ++ [seq pn_sn i | i <- ps] ->
    vty_in_m m vs (nth vs_d (sn_args s) (sn_idx s)).2).
  {
    move=> s Hins.
    move: Hallvty. rewrite -Happ => Hallvty.
    have/nthP:=Hins.
    move=> /(_ sn_d) [i Hi Hf]; subst.
    rewrite -Hlen in Hi.
    have Hcomb: (nth 0 il i, 
      nth sn_d ([seq fn_sn i | i <- fs] ++ [seq pn_sn i | i <- ps]) i) 
      \in  combine il ([seq fn_sn i | i <- fs] ++ [seq pn_sn i | i <- ps]). {
      apply /combineP. 
      by rewrite Hlen Happ.
      exists i. split=>//.
      move=> d1 d2.
      by rewrite (set_nth_default d1) // 
        (set_nth_default d2) // -Hlen.
    }
    move: Hallvty => /( _ _ Hcomb).
    by rewrite -(Hileq). 
  }
  split_all=>//; try by apply Hvtymeq.
  - (*Only need decrease fun and pred cases - annoying part is combine*)
    move=> f Hinf. have/nthP: f \in fs by [].
    move=> /(_ fn_d) [i Hi Hf]; subst.
    have Hcomb: (nth 0 il i, nth fn_d fs i) \in combine (take (size fs) il) fs. {
        apply /combineP; rewrite Hsztake //.
        exists i. split=>//. move=> d1 d2. rewrite nth_take //.
        rewrite (set_nth_default d1); last by apply (leq_trans Hi Hsz').
        by rewrite (set_nth_default d2).
      }
      move: H => /(_ _ Hcomb)/=.
      rewrite -(Hileq) //; last by apply (leq_trans Hi Hsz').
      rewrite nth_cat size_map Hi (nth_map fn_d) //.
      move=> Hcheck. by apply /check_decrease_fun_spec.
  - move=> p Hinp. have/nthP: p \in ps by [].
    move=> /(_ pn_d) [i Hi Hp]; subst.
    have Hcomb: (nth 0 il (size fs + i), nth pn_d ps i) \in 
      (combine (drop (size fs) il) ps). {
        apply /combineP; rewrite size_drop Hszps //.
        exists i. split=>//. move=> d1 d2. rewrite nth_drop.
        rewrite (set_nth_default d1); last by apply Hsz''.
        by rewrite (set_nth_default d2).
    }
    move: H0 => /(_ _ Hcomb)/=.
    rewrite -(Hileq) //; last by apply Hsz''.
    rewrite nth_cat size_map ltnNge leq_addr /= addnC -addnBA // subnn addn0
    (nth_map pn_d) //.
    move=> Hcheck. by apply /check_decrease_pred_spec.
Qed.

(*Now, a version of [find] that returns the element: given
  a function that evaluates to Some x (success) or None (failure),
  return the first success*)
Definition find_elt {A B: Type} (f: A -> option B) (l: list A) :
  option (A * B) :=
  fold_right (fun x acc => match f x with | None => acc | Some y => Some (x, y) end)
  None l.

Lemma find_elt_some {A B : eqType} (f: A -> option B) (l: list A) x y:
  find_elt f l = Some (x, y) ->
  x \in l /\ f x = Some y.
Proof.
  elim: l =>[//| h t /= Ih].
  case Hh: (f h)=>[a |].
  - move=> [Hax] hay; subst. by rewrite mem_head.
  - move=> Hfind. apply Ih in Hfind.
    case: Hfind => Hinxt Hfx.
    by rewrite in_cons Hinxt orbT.
Qed.

Lemma find_elt_none {A B : eqType} (f: A -> option B) (l: list A):
  reflect (forall y, y \in l -> f y = None)
    (find_elt f l == None).
Proof.
  elim: l => [//= | h t /= IH].
  - by apply ReflectT.
  - case Hh: (f h) => [a |].
    + apply ReflectF. move=> C. 
      rewrite C in Hh=>//. by rewrite mem_head.
    + eapply equivP. apply IH.
      split; move=> Hall y.
      * rewrite in_cons => /orP[/eqP Hhy | Hint]; subst=>//.
        by apply Hall.
      * move=> Hint. apply Hall. by rewrite in_cons Hint orbT.
Qed.


(*We also need to check the params. This is easy; we do it generically*)

(*Given a list of A's and a function A -> B, return Some x 
  iff f y = x for all y in l*)
Definition find_eq {A B: eqType} (f: A -> B) (l: list A) : option B :=
  match l with
  | nil => None
  | x :: tl => 
    (*x is our candidate*)
    if all (fun y => f y == f x) l then Some (f x) else None
    end.

Lemma find_eq_spec {A B: eqType} (f: A -> B) (l: list A) (b: B):
  reflect (l <> nil /\ forall x, x \in l -> f x = b)
  (find_eq f l == Some b).
Proof.
  rewrite /find_eq.
  case: l => [//= | h t /=].
  - by apply ReflectF => [] [].
  - rewrite eq_refl/=.
    case: (all (fun y : A => f y == f h) t) /allP => [ Hall| Hnotall].
    + case: (Some (f h) == Some b) /eqP => [[Hhb] | Hneq]; subst.
      * apply ReflectT.  split=>//. move=> x.
        rewrite in_cons => /orP[/eqP Hxh | Hint]; subst=>//.
        by apply /eqP; apply Hall.
      * apply ReflectF.
        move=> [_ Hall2].
        rewrite Hall2 in Hneq=>//.
        by rewrite mem_head.
    + apply ReflectF.
      move=> [_ Hall].
      apply Hnotall. move=> x Hinx. rewrite !Hall //.
      by rewrite mem_head.
      by rewrite in_cons Hinx orbT.
Qed. 

HB.instance Definition _ := hasDecEq.Build fpsym fpsym_eqb_spec.
HB.instance Definition _ := hasDecEq.Build funpred_def funpred_def_eqb_spec.


(*Now we can define the fill function*)
Definition find_funpred_def_term (l: list funpred_def) :
  option (mut_adt * list typevar * list vty * list nat) :=
  let t := split_funpred_defs l in
  let syms := map (fun x => f_sym (fst (fst x))) (fst t) ++
    map (fun x => p_sym (fst (fst x))) (snd t) in

  (*First, find params*)
  let o_params :=
    find_eq (fun x => s_params x) syms in
  match o_params with
  | None => None
  | Some params =>
      (*Now, we iterate over all possible il lists and find
        the first (m, vs) pair *)
        let m_data := 
        find_elt (
          fun il =>
            let fs :=  fst (funpred_defs_to_sns l il) in
            let ps := snd (funpred_defs_to_sns l il) in
            find_mut_args fs ps il
        ) (get_lists_bound (fun i =>
          (*Here, we use syms - needs to correspond to
          correct order*)
          size (s_args (nth id_sym syms i))) (size l)) in

        match m_data with
        | Some (il, (m, vs)) => Some (m, params, vs, il)
        | None => None
        end
  end.

Lemma firstn_take {A: Type} (n: nat) (l: list A) :
firstn n l = take n l.
Proof.
  move: n.
  elim:l=>//=[ [| n'] //| h t IH [| n'] //=].
  by rewrite IH.
Qed.

Lemma skipn_drop {A: Type} (n: nat) (l: list A) :
skipn n l = drop n l.
Proof.
  move: n.
  by elim:l=>//=[ [| n'] //| h t IH [| n'] //=].
Qed.

Lemma size_combine {A B: Type} (l1: list A) (l2: list B):
  size l1 = size l2 ->
  size (combine l1 l2) = size l1.
Proof.
  move: l2. elim: l1=> [[| h2 t2] // | h1 t1 /= IH [// | h2 t2/=[] Hsz] ].
  by rewrite IH.
Qed.

Lemma size_skipn {A: Type} (n: nat) (l: list A) :
  size (skipn n l) = size l - n.
Proof.
  by rewrite skipn_drop size_drop.
Qed.

  (*Need a bunch of size results*)
Lemma size_split_funpred_defs_fst l (il: list nat):
  size l = size il ->
  size (split_funpred_defs l).1 =
  size (firstn (Datatypes.length (split_funpred_defs l).1) il).
Proof.
  move=> Hsz.
  have Hlen: (size (split_funpred_defs l).1 + size (split_funpred_defs l).2) = size l
    by rewrite -!length_size -(split_funpred_defs_length l).
  rewrite firstn_take size_take length_size.
  have: size (split_funpred_defs l).1 <= size il by
    rewrite -Hsz -Hlen leq_addr.
  rewrite leq_eqVlt => /orP[/eqP Hsz1 | ->//].
  by rewrite Hsz1 ltnn.
Qed.

Lemma size_split_funpred_defs_snd l (il: list nat):
  size l = size il ->
  size (split_funpred_defs l).2 =
    size (skipn (Datatypes.length (split_funpred_defs l).1) il).
Proof.
  move=> Hsz.
  have Hlen: (size (split_funpred_defs l).1 + size (split_funpred_defs l).2) = size l
    by rewrite -!length_size -(split_funpred_defs_length l).
  by rewrite size_skipn -Hsz -Hlen  length_size addnC -addnBA // subnn addn0.
Qed.

Lemma size_split_funpred_defs_comb1 l (il: list nat):
  size l = size il ->
  size (combine (split_funpred_defs l).1
    (firstn (Datatypes.length (split_funpred_defs l).1) il)) =
  size (split_funpred_defs l).1.
Proof.
  move=> Hsz. 
  by rewrite size_combine // (size_split_funpred_defs_fst _ il).
Qed.

Lemma size_split_funpred_defs_comb2 l (il: list nat):
  size l = size il ->
  size (combine (split_funpred_defs l).2
    (skipn (Datatypes.length (split_funpred_defs l).1) il)) =
  size (split_funpred_defs l).2.
Proof.
  move=> Hsz.
  by rewrite size_combine // (size_split_funpred_defs_snd _ il).
Qed. 

(*NOTE: should be in typing, but in terms of ssreflect*)
Lemma funpred_defs_to_sns_idx l il:
  size l = size il ->
  forall i,
  i < size il ->
    sn_idx
      (nth sn_d
        ([seq fn_sn i | i <- (funpred_defs_to_sns l il).1] ++
          [seq pn_sn i | i <- (funpred_defs_to_sns l il).2]) i) = 
    nth 0 il i.
Proof.
  move=> Hsz i Hi.
  rewrite nth_cat size_map. have Hleneq: length l = length il by rewrite !length_size.
  have Hlen: (size (split_funpred_defs l).1 + size (split_funpred_defs l).2) = size l
    by rewrite -!length_size -(split_funpred_defs_length l).
  rewrite /funpred_defs_to_sns/= !size_map size_split_funpred_defs_comb1 //.
  case Hilt: (i < size (split_funpred_defs l).1).
  - rewrite (nth_map fn_d) //=; last by
      rewrite size_map size_split_funpred_defs_comb1.
    rewrite (nth_map (id_fs, @nil vsymbol, tm_d, 0)) /=;
      last by rewrite size_split_funpred_defs_comb1.
    rewrite -nth_eq combine_nth //=; last by
      rewrite !length_size -(size_split_funpred_defs_fst _ il).
    by rewrite firstn_take nth_eq nth_take.
  - have Hige: size (split_funpred_defs l).1 <= i. {
      move: Hilt; rewrite ltnNge => Hle. by apply negbFE in Hle.
    }
    have Hi': i - size (split_funpred_defs l).1 < size (split_funpred_defs l).2
      by rewrite ltn_subLR // Hlen Hsz.
    rewrite (nth_map pn_d) //=; last by rewrite size_map 
      size_split_funpred_defs_comb2.
    rewrite (nth_map (id_ps, nil, Ftrue, 0)) /=;
      last by rewrite size_split_funpred_defs_comb2.
    rewrite -nth_eq combine_nth //=; last by
      rewrite !length_size -size_split_funpred_defs_snd.
    by rewrite skipn_drop nth_eq nth_drop length_size subnKC.
Qed.

Lemma plus_coq_nat n1 n2:
  (n1 + n2)%coq_nat = n1 + n2.
by [].
Qed.

Lemma size_funpred_defs_to_sns l il:
  size l = size il ->
  size (funpred_defs_to_sns l il).1 =
  size (split_funpred_defs l).1 /\
  size (funpred_defs_to_sns l il).2 =
  size (split_funpred_defs l).2.
Proof.
  move=> Hsz.
  rewrite /funpred_defs_to_sns !size_map !size_combine //.
  - by rewrite -size_split_funpred_defs_snd.
  - by rewrite -size_split_funpred_defs_fst.
Qed.

Section WFCtx.
Variable gamma_wf: wf_context gamma.


(*We need 2 specs: if it is Some (m, p, vs, il), then these
  satisfy the conditions of *)

(*The converse is not true because in principle many lists could
  satsify the conditions*)
Theorem find_funpred_def_term_some (l: list funpred_def) m params vs il:
  l \in (mutfuns_of_context gamma) ->
  find_funpred_def_term l = Some (m, params, vs, il) ->
  funpred_def_term gamma l m params vs il.
Proof.
  move=> Hinl.
  rewrite /find_funpred_def_term /funpred_def_term.
  case Hfind: (find_eq s_params ([seq f_sym x.1.1 | x <- (split_funpred_defs l).1] ++
  [seq p_sym x.1.1 | x <- (split_funpred_defs l).2])) => [p | //].
  move: Hfind => /eqP /find_eq_spec => [[Hnotnil Hparams]].
  case Hfind: (find_elt
  (fun il0 : seq nat =>
   find_mut_args (funpred_defs_to_sns l il0).1 (funpred_defs_to_sns l il0).2 il0)
  (get_lists_bound
     (fun i : nat =>
      size
        (s_args
           (nth id_sym
              ([seq f_sym x.1.1 | x <- (split_funpred_defs l).1] ++
               [seq p_sym x.1.1 | x <- (split_funpred_defs l).2]) i))) 
     (size l))) => [[il' [m' vs']] | //].
  move => [Hm] Hp Hvs Hil; subst.
  apply find_elt_some in Hfind.
  case: Hfind => [/get_lists_bound_spec [Hlenil Hil] /eqP /find_mut_args_spec Hfind].
  (*We have to prove the hypotheses*)
  have Hsz1: size il =
  size (funpred_defs_to_sns l il).1 + size (funpred_defs_to_sns l il).2 by
    rewrite -!length_size Hlenil -length_size -(funpred_defs_to_sns_length _ il).
  rewrite length_size in Hlenil.
  move: Hfind => /(_ Hsz1 (funpred_defs_to_sns_idx l il (esym Hlenil))) => Hfind.
  rewrite {Hsz1}.
  have Hsz2: size (funpred_defs_to_sns l il).1 + size (funpred_defs_to_sns l il).2 != 0. {
    have []:=(size_funpred_defs_to_sns l il (esym Hlenil))=>->->.
    rewrite -(size_map(fun x => f_sym x.1.1)) -(size_map (fun x => p_sym x.1.1)).
    rewrite -size_cat size_eq0. by apply /eqP.
  }
  have Hleneq: length l = length il by rewrite !length_size.
  move: Hfind => /( _ Hsz2 (@mut_adts_inj _ gamma_wf)
    (proj1 (funpred_defs_to_sns_NoDup gamma_wf l il (elimT (inP _ _) Hinl) Hleneq))
    (proj2 (funpred_defs_to_sns_NoDup gamma_wf l il (elimT (inP _ _) Hinl) Hleneq)))
  [ Hszvs [m_in [Hallvtyf [Hallvtyp [Hdecf Hdecp]]]]].
  split_all =>//.
  - move=> Hl; subst. by apply Hnotnil.
  - move=> i /ltP Hi. apply /ltP. rewrite !nth_eq length_size app_cat.
    by apply Hil.
  - move=> f /inP. rewrite nth_eq. apply Hallvtyf.
  - move=> p /inP. rewrite nth_eq. apply Hallvtyp.
  - move=> f /inP.
    rewrite /funpred_defs_to_sns/==> /mapP [x Hx Hf]; subst=>/=.
    move: Hx => /combineP.
    rewrite -size_split_funpred_defs_fst // => /(_ erefl) [i [Hi /(_ (id_fs, nil, tm_d) 0)]]
    ->/=. apply Hparams.
    rewrite mem_cat. apply /orP; left.
    apply /mapP. exists ((nth (id_fs, [::], tm_d) (split_funpred_defs l).1 i))=>//.
    by rewrite mem_nth.
  - move=> p /inP.
    rewrite /funpred_defs_to_sns/==> /mapP [x Hx Hp]; subst=>/=.
    move: Hx => /combineP.
    rewrite -size_split_funpred_defs_snd // => /(_ erefl) [i [Hi /(_ (id_ps, nil, Ftrue) 0)]]
    ->/=. apply Hparams.
    rewrite mem_cat. apply /orP; right.
    apply /mapP. exists ((nth (id_ps, [::], Ftrue) (split_funpred_defs l).2 i))=>//.
    by rewrite mem_nth.
  - rewrite Forall_forall => x /inP. rewrite nth_eq. by apply Hdecf.
  - rewrite Forall_forall => x /inP. rewrite nth_eq. by apply Hdecp.
Qed.

(*For the converse, we show that if this function gives None,
  [funpred_def_term gamma l m params vs il] is always false*)
Theorem find_funpred_def_term_none (l: list funpred_def):
  l \in (mutfuns_of_context gamma) ->
  find_funpred_def_term l = None ->
  forall m params vs il,
    ~ funpred_def_term gamma l m params vs il.
Proof.
  move=> Hinl Hfind m params vs il.
  rewrite /funpred_def_term => [[Hlnil [Hlenvs [m_in [Hlenil 
    [Hargsnth [Hfvty [Hpty [Hfparams [Hpparams [Hfdec Hpdec]]]]]]]]]]].
  move: Hfind.
  rewrite /find_funpred_def_term.
  (*First, show that [find_eq] must be (Some params). This is annoying*)
  have->: (find_eq s_params ([seq f_sym x.1.1 | x <- (split_funpred_defs l).1] ++
  [seq p_sym x.1.1 | x <- (split_funpred_defs l).2])) = Some params. {
    apply /eqP. apply /find_eq_spec.
    split.
    - have:=(split_funpred_defs_length l).
      rewrite !length_size plus_coq_nat => Hszl.
      move=> Hnil; apply (f_equal (@size _)) in Hnil;
      move: Hnil; rewrite !size_cat !size_map Hszl/= => /eqP.
      by rewrite size_eq0  => /eqP Hl; subst.
    - move=> x. rewrite mem_cat => /orP[/mapP [x' Hinx' Hx'] | /mapP [x' Hinx' Hx']];
      subst.
      + have:=(nth_index (id_fs, nil, tm_d) Hinx') => Hx'; subst.
        rewrite -Hx'/=.
        move: Hfparams => /(_ (fundef_to_fn x'.1.1 x'.1.2 x'.2 (nth 0 il (index x' (split_funpred_defs l).1)))).
        have Hin: In (fundef_to_fn x'.1.1 x'.1.2 x'.2 (nth 0 il (index x' (split_funpred_defs l).1)))
        (funpred_defs_to_sns l il).1. {
          apply /inP. rewrite /funpred_defs_to_sns/=. apply /mapP.
          exists (x', nth 0 (firstn (Datatypes.length (split_funpred_defs l).1) il) (index x' (split_funpred_defs l).1))=>//.
          apply /combineP; first by rewrite -size_split_funpred_defs_fst.
          exists (index x' (split_funpred_defs l).1).
          split.
          - by rewrite index_mem.
          - move=> d1 d2. rewrite -{1}Hx'/=.
            rewrite (set_nth_default d1); last by rewrite index_mem. 
            by rewrite (set_nth_default d2) // -size_split_funpred_defs_fst //
            index_mem.
          - by rewrite firstn_take nth_take // length_size index_mem.
        }
        move=> /(_ Hin)/=. by rewrite -{1}Hx'.
      + (*In the 2nd part, very similar*)
        have:=(nth_index (id_ps, nil, Ftrue) Hinx') => Hx'; subst.
        rewrite -Hx'/=.
        move: Hpparams => /(_ (preddef_to_pn x'.1.1 x'.1.2 x'.2 (nth 0 il (size (split_funpred_defs l).1 + (index x' (split_funpred_defs l).2))))).
        have Hin: In
        (preddef_to_pn x'.1.1 x'.1.2 x'.2
           (nth 0 il (size (split_funpred_defs l).1 + index x' (split_funpred_defs l).2)))
        (funpred_defs_to_sns l il).2. {
          apply /inP. rewrite /funpred_defs_to_sns/=. apply /mapP.
          exists (x', nth 0 (skipn (Datatypes.length (split_funpred_defs l).1) il) 
            (index x' (split_funpred_defs l).2))=>//; last by
            rewrite /= skipn_drop nth_drop length_size.
          apply /combineP; first by rewrite -size_split_funpred_defs_snd.
          exists (index x' (split_funpred_defs l).2).
          split.
          - by rewrite index_mem.
          - move=> d1 d2. rewrite -{1}Hx'/=.
            rewrite (set_nth_default d1); last by rewrite index_mem. 
            by rewrite (set_nth_default d2) // -size_split_funpred_defs_snd //
            index_mem.
        }
        move=> /(_ Hin)/=. by rewrite -{1}Hx'.
  }
  case Hfind: (find_elt
  (fun il0 : seq nat =>
   find_mut_args (funpred_defs_to_sns l il0).1 (funpred_defs_to_sns l il0).2 il0)
  (get_lists_bound
     (fun i : nat =>
      size
        (s_args
           (nth id_sym
              ([seq f_sym x.1.1 | x <- (split_funpred_defs l).1] ++
               [seq p_sym x.1.1 | x <- (split_funpred_defs l).2]) i))) 
     (size l))) => [[il' [m' vs']]// |].
  move: Hfind => /eqP /find_elt_none.
  (*We give a contradiction by showing that il satisfies the conditions*)
  move=> /(_ il).
  have Hil: (il
  \in get_lists_bound
        (fun i : nat =>
         size
           (s_args
              (nth id_sym
                 ([seq f_sym x.1.1 | x <- (split_funpred_defs l).1] ++
                  [seq p_sym x.1.1 | x <- (split_funpred_defs l).2]) i))) 
        (size l)).
  {
    apply /get_lists_bound_spec. split; rewrite length_size //.
    move=> i Hi.
    move: Hargsnth. rewrite !length_size => /(_ i (elimT ltP Hi)).
    by rewrite !nth_eq length_size => /ltP.
  }
  move=> /(_ Hil).
  (*Now we show a contradiction from [find_mut_args]. Again we
    need to prove the hypotheses first*)
  have->//:
  find_mut_args (funpred_defs_to_sns l il).1 (funpred_defs_to_sns l il).2 il =
  Some (m, vs).
  apply /eqP.
  rewrite !length_size in Hlenil.
  apply /find_mut_args_spec.
  - have:=(funpred_defs_to_sns_length l il). 
    rewrite !length_size plus_coq_nat => /(_ (esym Hlenil)).
    by rewrite Hlenil.
  - apply (funpred_defs_to_sns_idx l il (esym Hlenil)).
  - have:=(funpred_defs_to_sns_length l il).
    rewrite !length_size plus_coq_nat => /(_ (esym Hlenil)) ->.
    rewrite size_eq0. by apply /eqP.
  - apply (@mut_adts_inj _ gamma_wf).
  - have Hleneq: length l = length il by rewrite !length_size.
    apply (funpred_defs_to_sns_NoDup gamma_wf l il (elimT (inP _ _) Hinl) Hleneq).
  - have Hleneq: length l = length il by rewrite !length_size.
    apply (funpred_defs_to_sns_NoDup gamma_wf l il (elimT (inP _ _) Hinl) Hleneq).
  - (*Now we prove each of the conditions*)
    split_all=>//.
    + move=> f /inP. by rewrite -nth_eq; apply Hfvty.
    + move=> p /inP. by rewrite -nth_eq; apply Hpty.
    + move=> f /inP Hinf. move: Hfdec.
      rewrite Forall_forall => /(_ _ Hinf).
      by rewrite nth_eq.
    + move=> p /inP Hinp. move: Hpdec.
      rewrite Forall_forall => /(_ _ Hinp).
      by rewrite nth_eq.
Qed.

(*For our purposes, we need something a bit more specific,
  we need to know that a function creates these (so that they
  are unique)*)
Lemma funpred_def_term_decide (l: list funpred_def):
  In l (mutfuns_of_context gamma) ->
  funpred_def_term_exists gamma l ->
  match (find_funpred_def_term l) with
  | Some (m, params, vs, il) =>
    funpred_def_term gamma l m params vs il
  | None => False
  end.
Proof.
  move=>Hin Hex.
  case Hfind: (find_funpred_def_term l) => [[[[m params] vs] il] |].
  - apply find_funpred_def_term_some =>//.
    by apply /inP.
  - case: Hex => [m [params [vs [il Hterm]]]].
    move: Hin => /inP Hin.
    by apply (find_funpred_def_term_none l Hin Hfind m params vs il).
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
  (isSome (find_funpred_def_term l)).

Lemma funpred_valid_check_spec (l: list funpred_def) :
  wf_context gamma ->
  l \in mutfuns_of_context gamma ->
  reflect (funpred_valid gamma l) (funpred_valid_check l).
Proof.
  move=> Hwf l_in.
  rewrite /funpred_valid/funpred_valid_check.
  apply andPP.
  - apply all_Forall=> x Hinx.
    apply funpred_def_valid_type_check_spec.
  - (*This one is a bit tougher*)
    rewrite /funpred_def_term_exists.
    case Hfind: (find_funpred_def_term l) => [[[[m params] vs] il] |]/=.
    + apply ReflectT.
      exists m. exists params. exists vs. exists il.
      by apply find_funpred_def_term_some.
    + apply ReflectF.
      move=> [m [params [vs [il Hdef]]]].
      by apply (find_funpred_def_term_none Hwf l l_in Hfind m params vs il).
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
    apply /inP.
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