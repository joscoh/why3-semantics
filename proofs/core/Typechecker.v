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

(*TODO*)
Definition funsym_eqMixin := EqMixin funsym_eqb_spec.
Canonical funsym_eqType := EqType funsym funsym_eqMixin.

(*Decidable list intersection, may have duplicates*)
Definition seqI {A: eqType} (s1 s2: seq A) :=
  filter (fun x => x \in s2) s1.

Fixpoint typecheck_pattern (s: sig) (p: pattern) (v: vty) : bool :=
  match p with
  | Pvar x ty => (v == ty) && typecheck_type s ty
  | Pwild => typecheck_type s v
  | Por p1 p2 => 
    typecheck_pattern s p1 v &&
    typecheck_pattern s p2 v &&
    (eq_memb (pat_fv p2) (pat_fv p1))
  | Pbind p x ty =>
    (v == ty) &&
    (x \notin (pat_fv p)) &&
    (typecheck_pattern s p v)
  | Pconstr f params ps => 
    (v == ty_subst (s_params f) params (s_ret f)) &&
    (f \in (sig_f s)) &&
    all (fun x => typecheck_type s x) params &&
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
Lemma all_Forall {A: eqType} (P: A -> Prop) (p: pred A) (s: seq A):
  (forall x, x \in s -> reflect (P x ) (p x)) ->
  reflect (Forall P s) (all p s).
Proof.
  elim: s =>[//= Hall | h t /= IH Hall].
  - apply ReflectT. constructor.
  - case: (p h) /(Hall h (mem_head _ _)) => Hh/=; last by reflF.
    have IHt: (forall x : A, x \in t -> reflect (P x) (p x)) by
      move=> x Hinx; apply Hall; rewrite in_cons Hinx orbT.
    move: IH => /(_ IHt) IH.
    case: (all p t) /IH => Ht/=; last by reflF.
    apply ReflectT. by constructor.
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
  - move=> vs ty1 ty2. 
    case: (ty2 == ty1) /eqP => //= Hty12; subst; last by reflF.
    case: (typecheck_type s ty1) /typecheck_type_correct => Hty1; 
    last by reflF.
    apply ReflectT. by constructor.
  - (*The hard case*)
    move=> f vs ps Hall v.
    case: (v == ty_subst (s_params f) vs (s_ret f)) /eqP => Hv/=; 
      subst; last by reflF.
    case: (f \in sig_f s) /inP => Hinf/=; last by reflF.
    case: (all [eta typecheck_type s] vs) 
      /(all_Forall _ _ _ (fun x _ => typecheck_type_correct s x)) => Hforall/=;
      last by reflF.
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
    + move=> Hty. inversion Hty; subst. clear -H7 H4 Hall.
      move: H4 H7. subst sigma.
      move: Hall (s_params f) (s_args f) vs.
      elim: ps =>[//= Hall params [|] vs //| phd ptl /= IH Hall params 
        [// | ahd atl/=] vs [Hlen] Hforall].
      case: (typecheck_pattern s phd (ty_subst params vs ahd))
        /(ForallT_hd _ _ _  Hall) => Hhasty/=; last by
        exfalso; apply Hhasty; apply (Forall_inv Hforall).
      apply IH=>//. apply (ForallT_tl _ _ _ Hall).
      apply (Forall_inv_tail Hforall).
    + move => Hcheck. constructor=>//.
      clear -Hcheck Hall Hlenps.
      move: (s_params f) (s_args f) vs Hlenps Hall Hcheck.
      elim: ps => [//= | phd ptl /= IH params [// | ahd atl /=] vs [Hlen] Hall].
      case: (typecheck_pattern s phd (ty_subst params vs ahd))
      /(ForallT_hd _ _ _  Hall) => Hhasty//= Hcheck.
      constructor=>//. apply IH=>//.
      apply (ForallT_tl _ _ _ Hall).
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
  - move=> p v ty IH v'.
    case: (v' == ty) /eqP => Hv'/=; subst; last by reflF.
    case: (v \in pat_fv p) /inP => Hinv/=; first by reflF.
    case: (typecheck_pattern s p ty) /(IH ty) => Hty; last by reflF.
    apply ReflectT. by constructor.
Qed.
