(*Separate file to use ssreflect*)
Require Import Syntax.
Require Import Types.
Require Import Typing.

From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

(* Let's try to build a typechecker *)
Section Typechecker.

Fixpoint typecheck_type (s:sig) (v: vty) : bool :=
  match v with
  | vty_int => true
  | vty_real => true
  | vty_var tv => false
  | vty_cons ts vs => 
      (ts \in (sig_t s)) &&
      (length vs == length (ts_args ts)) &&
      (fix check_list (l: list vty) : bool :=
      match l with
      | nil => true
      | x :: t => typecheck_type s x && check_list t
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

(*TODO: move*)
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

(*Patterns can have many types, so we ask: can this pattern
  have this type? (ex: Pwild)*)

Definition funsym_eqMixin := EqMixin funsym_eqb_spec.
Canonical funsym_eqType := EqType funsym funsym_eqMixin.
Definition predsym_eqMixin := EqMixin predsym_eqb_spec.
Canonical predsym_eqType := EqType predsym predsym_eqMixin.

(*Decidable list intersection, may have duplicates*)
Definition seqI {A: eqType} (s1 s2: seq A) :=
  filter (fun x => x \in s2) s1.

Fixpoint typecheck_pattern (s: sig) (p: pattern) (v: vty) : bool :=
  match p with
  | Pvar x => (v == (snd x)) && typecheck_type s (snd x)
  | Pwild => typecheck_type s v
  | Por p1 p2 => 
    typecheck_pattern s p1 v &&
    typecheck_pattern s p2 v &&
    (eq_memb (pat_fv p2) (pat_fv p1))
  | Pbind p x =>
    (v == (snd x)) &&
    (x \notin (pat_fv p)) &&
    (typecheck_pattern s p v)
  | Pconstr f params ps => 
    (v == ty_subst (s_params f) params (f_ret f)) &&
    (f \in (sig_f s)) &&
    all (fun x => typecheck_type s x) params &&
    (typecheck_type s (f_ret f)) &&
    (length ps == length (s_args f)) &&
    (length params == length (s_params f)) &&
    ((fix check_list (l1: list pattern) (l2: list vty) : bool :=
      match l1, l2 with
      | nil, nil => true
      | h1 :: t1, h2 :: t2 => typecheck_pattern s h1 h2 &&
        check_list t1 t2
      |  _, _ => false
       end) ps (map (ty_subst (s_params f) params) (s_args f))) &&
    (*Kind of an awkward encoding*)
    [forall x in 'I_(length ps), forall y in 'I_(length ps),
      (x != y) ==>  
      null (seqI (pat_fv (nth Pwild ps x)) (pat_fv (nth Pwild ps y)))]
  end.

(*Proofs of correctness*)



(*We would like to prove this correct*)
Lemma typecheck_type_correct: forall (s: sig) (v: vty),
  reflect (valid_type s v) (typecheck_type s v).
Proof.
  move=> s. apply vty_rect=>//=.
  - apply ReflectT. constructor.
  - apply ReflectT. constructor.
  - move=> v. apply ReflectF => C. inversion C.
  - move=> ts vs Hty. case Hts: (ts \in sig_t s)=>/=; last first.
      apply ReflectF => C. inversion C; subst.
      move: H1 => /inP. by rewrite Hts.
    (*Annoyingly, we can't do a single induction because of the
      length requirement*)
    apply iff_reflect. split.
    + move => Hty'. inversion Hty'; subst. rewrite {H1} (introT eqP H3)/=.
      move: Hty H4. clear. elim: vs => [// | v vs /= IH Hall Hval].
      have->/=: typecheck_type s v by apply /(ForallT_hd _ _ _ Hall);
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

Ltac reflF := let C := fresh "C" in apply ReflectF => C; inversion C; subst.

(*TODO: move*)
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

(*Let's start this*)
Lemma typecheck_pattern_correct: forall (s: sig) (p: pattern) (v: vty),
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
    ([forall x in 'I_(Datatypes.length ps),
      forall y in 'I_(Datatypes.length ps),
      (x != y) ==>
      null (seqI (pat_fv (nth Pwild ps x)) (pat_fv (nth Pwild ps y)))]). {
        (*Have to prove manually*)
        case: [forall x in 'I_(Datatypes.length ps),
        forall y in 'I_(Datatypes.length ps),
        (x != y) ==>
        null (seqI (pat_fv (nth Pwild ps x)) (pat_fv (nth Pwild ps y)))] 
        /forallP => Hforallx/=; last first.
        - apply ReflectF => C. apply Hforallx. move=> x.
          apply /implyP => _. apply /forallP => y.
          apply /implyP=>_. apply /implyP => Hneq.
          apply /nullP. apply /eqP. 
          rewrite /seqI -(negbK (_ == _)) -has_filter. 
          apply /negP => /hasP [z] /inP Hzin1 /inP Hzin2.
          apply (C x y Pwild z).
          + by apply /ltP.
          + by apply /ltP.
          + by apply /eqP.
          + by rewrite !nth_eq.
        - apply ReflectT. move => i j d x /ltP Hi /ltP Hj /eqP Hij [].
          rewrite !nth_eq => Hinxi Hinxj.
          move: Hforallx => /(_ (Ordinal Hi))/= /forallP 
            /(_ (Ordinal Hj))/= /implyP.
          have Hneq: (Ordinal (n:=Datatypes.length ps) (m:=i) Hi
            != Ordinal (n:=Datatypes.length ps) (m:=j) Hj).
          apply /eqP=> C. inversion C; subst. by rewrite eq_refl in Hij.
          move=>/(_ Hneq) /nullP /eqP. 
          rewrite /seqI -(negbK (_ == _)) -has_filter => /hasP.
          apply. by exists x; rewrite (set_nth_default d)//; apply /inP.
    }
    case: Hfvs => Hfreevars;[rewrite andbT | rewrite andbF]; last by
    reflF.
    (*Now we just have the nested induction left*)
    apply iff_reflect. split.
    + move=> Hty. inversion Hty; subst. clear -H8 H5 Hall.
      move: H5 H8. subst sigma.
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
Fixpoint typecheck_term (s: sig) (t: term) : option vty :=
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
with typecheck_formula (s: sig) (f: formula) : bool :=
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

Ltac reflT := apply ReflectT; constructor.

(*Now we prove the correctness of this*)
Lemma typecheck_term_fmla_spec (s: sig): 
  forall (tm: term) (f: formula),
  (forall v, 
    reflect (term_has_type s tm v) (typecheck_term s tm == Some v)) *
  reflect (valid_formula s f) (typecheck_formula s f).
Proof.
  apply (term_formula_rect) with(P1:=fun tm => forall v,
    reflect (term_has_type s tm v) (typecheck_term s tm == Some v))
  (P2:= fun f => reflect (valid_formula s f) (typecheck_formula s f))=>/=.
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
        -- reflT=>//. move=> x [<-// | Hinx]. by apply Hptl.
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
      clear -H7 HallT Hlentms. subst sigma.
      move: (s_args p) (ty_subst (s_params p) tys) Hlentms HallT H7 .
      elim: tms => [// [|]// | tmh tmtl /= IH [//|ah atl] sigma [Hlen]
        HallT /= Hall].
      apply /andP; split.
      * apply /(ForallT_hd _ _ _ HallT). apply (Forall_inv Hall).
      * apply IH=>//. by inversion HallT. by inversion Hall.
    + move=> Hargs. constructor=>//.
      move: (s_args p) (ty_subst (s_params p) tys) Hlentms HallT Hargs. clear.
      elim: tms => [[|]// | tmh tmtl /= IH [//| ah atl] sigma [Hlen]
        HallT /= /andP[/(ForallT_hd _ _ _ HallT) Hh Hargs]]; 
        first by constructor.
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
    case: (typecheck_term s tm == Some ty) /Htm => Htm /=; last by reflF.
    have Hallt: (forall x, In x ps -> reflect (pattern_has_type s x.1 ty)
      (typecheck_pattern s x.1 ty)) by move=> x _; apply typecheck_pattern_correct.
    case: (all (fun x => typecheck_pattern s x.1 ty) ps)
      /(forallb_ForallP _ _ _ Hallt) => Hallps/=; last by reflF.
    case Hnull: (null ps) =>/=. reflF. by rewrite Hnull in H6.
    apply iff_reflect. split.
    + move=> Hmatch. inversion Hmatch; subst.
      move: HallT H5. clear. elim: ps => [// | [p1 f1] pt /= IH HallT Hall].
      inversion Hall; subst.
      case: (typecheck_formula s f1) /(ForallT_hd _ _ _ HallT)=>//=Hf1.
      apply IH=>//. by inversion HallT.
    + move=> Hcheck. constructor=>//; last by rewrite Hnull.
      move: HallT Hcheck. clear. 
      elim: ps => [// | [p1 f1] ptl /= IH HallT /andP[Hf1 Hcheck]].
      inversion HallT; subst.
      constructor. by apply /H1.
      by apply IH.
Qed.

(*Now a few easy corollaries*)
Definition typecheck_term_correct (s: sig) (tm: term) (v: vty):
  reflect (term_has_type s tm v) (typecheck_term s tm == Some v) :=
  fst (typecheck_term_fmla_spec s tm Ftrue) v.

Definition typecheck_formula_correct (s: sig) (f: formula):
  reflect (valid_formula s f) (typecheck_formula s f) :=
  snd (typecheck_term_fmla_spec s tm_d f).

(*TODO: separate module or something so we don't have imports?*)
(*TODO: better name*)
Lemma typecheck_dec: forall s t,
(exists x, term_has_type s t x) ->
{ x | term_has_type s t x}.
Proof.
  move=> s t Hex.
  case Hcheck: (typecheck_term s t) => [ty |].
  - apply (exist _ ty). apply /typecheck_term_correct. by apply /eqP.
  - exfalso. case: Hex => [ty /typecheck_term_correct].
    by rewrite Hcheck.
Qed.

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

(*Here, we show that the context checks (some of them for now)
  are decidable.
  We need this for some proofs; namely for recursive functions, 
  we need to be able to find the fs and ps to build our function*)

Fixpoint check_valid_matches_tm (t: term) : bool :=
  match t with
  | Tfun f vs tms =>
    all check_valid_matches_tm tms
  | Tlet tm1 v tm2 =>
    check_valid_matches_tm tm1 &&
    check_valid_matches_tm tm2
  | Tif f1 t1 t2 =>
    check_valid_matches_fmla f1 &&
    check_valid_matches_tm t1 &&
    check_valid_matches_tm t2
  | Tmatch t1 v ps =>
    check_valid_matches_tm t1 &&
    is_vty_adt gamma v &&
    all (fun x => check_valid_matches_tm (snd x)) ps
  | Teps f v =>
    check_valid_matches_fmla f
  | _ => true
  end
with check_valid_matches_fmla (f: formula) : bool :=
  match f with
  | Fpred p vs tms => all check_valid_matches_tm tms
  | Fquant q v f => check_valid_matches_fmla f
  | Feq v t1 t2 => check_valid_matches_tm t1 &&
    check_valid_matches_tm t2
  | Fbinop b f1 f2 => check_valid_matches_fmla f1 &&
    check_valid_matches_fmla f2
  | Fnot f => check_valid_matches_fmla f
  | Flet t v f => check_valid_matches_tm t &&
    check_valid_matches_fmla f
  | Fif f1 f2 f3 =>
    check_valid_matches_fmla f1 &&
    check_valid_matches_fmla f2 &&
    check_valid_matches_fmla f3
  | Fmatch t v ps =>
    check_valid_matches_tm t &&
    is_vty_adt gamma v &&
    all (fun x => check_valid_matches_fmla (snd x)) ps
  | _ => true
  end.

(*We could assume stuff, but let's just plow through
  this I guess*)
Definition pattern_eqMixin := EqMixin pattern_eqb_spec.
Canonical pattern_eqType := EqType pattern pattern_eqMixin.
Definition term_eqMixin := EqMixin term_eqb_spec.
Canonical term_eqType := EqType term term_eqMixin.
Definition formula_eqMixin := EqMixin formula_eqb_spec.
Canonical formula_eqType := EqType formula formula_eqMixin.

Lemma iter_and_Forall {A: Type} {P: A -> Prop} {l: list A}:
  Forall P l <-> iter_and (List.map P l).
Proof.
  elim: l=>//= h t IH/=.
  split =>[Hall | [Hh Ht]].
  - split.
    + exact (Forall_inv Hall).
    + rewrite -IH. exact (Forall_inv_tail Hall).
  - constructor=>//. by apply IH.
Qed.

Lemma check_valid_matches_spec (t: term) (f: formula):
  reflect (valid_matches_tm gamma t) (check_valid_matches_tm t) *
  reflect (valid_matches_fmla gamma f) (check_valid_matches_fmla f).
Proof.
  revert t f; apply term_formula_rect =>//=;
  (try by (intros; apply ReflectT));
  try by (intros; apply andPP).
  (*Only 3 nontrivial cases for each: fun/pred, if (basically trivial),
  and match*)
  - move=> f1 tys tms Hall.
    eapply equivP. 2: apply iter_and_Forall.
    apply all_Forall. 
    move: Hall; elim: tms => [//=| thd ttl IH /= Hall x].
    rewrite in_cons. (*Can't destruct on or*)
    case: (x == thd) /eqP => [Hxh _ | Hneq]/=; subst.
    + exact (ForallT_hd _ _ _ Hall).
    + apply IH. exact (ForallT_tl _ _ _ Hall).
  - move=> f t1 t2 IH1 IH2 IH3.
    rewrite -andbA.
    repeat apply andPP=>//.
  - move=> tm v ps IH1 Hall. cbn.
    rewrite -andbA.
    repeat apply andPP=>//.
    + apply is_vty_adt_weak.
    + eapply equivP. 2: apply iter_and_Forall.
      apply all_Forall.
      move: Hall.
      elim: ps => //= [[p1 t1]] tl IH Hall x.
      rewrite in_cons.
      case: (x == (p1, t1)) /eqP => /=[Hxp1 _ | Hneq ]; subst=>/=.
      * exact (ForallT_hd _ _ _ Hall).
      * apply IH. exact (ForallT_tl _ _ _ Hall).
  - move=> p tys tms Hall.
    eapply equivP. 2: apply iter_and_Forall.
    apply all_Forall. 
    move: Hall; elim: tms => [//=| thd ttl IH /= Hall x].
    rewrite in_cons. (*Can't destruct on or*)
    case: (x == thd) /eqP => [Hxh _ | Hneq]/=; subst.
    + exact (ForallT_hd _ _ _ Hall).
    + apply IH. exact (ForallT_tl _ _ _ Hall).
  - move=> f1 f2 f3 IH1 IH2 IH3.
    rewrite -andbA.
    repeat apply andPP=>//.
  - move=> tm v ps IH1 Hall. cbn.
    rewrite -andbA.
    repeat apply andPP=>//.
    + apply is_vty_adt_weak.
    + eapply equivP. 2: apply iter_and_Forall.
      apply all_Forall.
      move: Hall.
      elim: ps => //= [[p1 t1]] tl IH Hall x.
      rewrite in_cons.
      case: (x == (p1, t1)) /eqP => /=[Hxp1 _ | Hneq ]; subst=>/=.
      * exact (ForallT_hd _ _ _ Hall).
      * apply IH. exact (ForallT_tl _ _ _ Hall).
Qed.

Definition check_valid_matches_tm_spec t := 
  fst (check_valid_matches_spec t Ftrue).
Definition check_valid_matches_fmla_spec f := 
  snd (check_valid_matches_spec tm_d f).

End ContextCheck.

End Typechecker.