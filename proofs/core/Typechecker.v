(*Separate file to use ssreflect*)
Require Export Typing.
Set Bullet Behavior "Strict Subproofs".

(*Ordering on types*)
(*Require Import Coq.Structures.OrdersEx.
Require Import Coq.Structures.Orders.

(*Does this exist?*)
Print StrictOrder.
(*Require this to be decidable equality also*)
Definition comparison_eq {A: Type} (comp: A -> A -> comparison) : Prop :=
  forall x y, comp x y = Eq <-> x = y.
Definition comparison_lt_gt {A: Type} (comp: A -> A -> comparison) : Prop :=
  forall x y, comp x y = Lt <-> comp y x = Gt.
Definition comparison_lt_trans  {A: Type} (comp: A -> A -> comparison) : Prop :=
  forall x y z, comp x y = Lt -> comp y z = Lt -> comp x z = Lt.

Class StrictComp {A: Type} (comp: A -> A -> comparison) : Prop :=
  mk_strictcomp { strict_eq: comparison_eq comp; strict_lt_gt : comparison_lt_gt comp;
    strict_lt_trans : comparison_lt_trans comp }.

Lemma StrictComp_StrictOrder {A: Type} (comp: A -> A -> comparison) (Hcomp: StrictComp comp) :
  StrictOrder (fun x y => comp x y = Lt).
Proof.
  destruct Hcomp as [Heq Hlt Htrans].
  constructor.
  - intros x; unfold complement.
    assert (Hex': comp x x = Eq) by (apply Heq; auto).
    rewrite Hex'; discriminate.
  - apply Htrans.
Qed.

(*Definition comparison_eqb (c1 c2: comparison) : bool :=
  match c1, c2 with
  | Eq, Eq => true
  | Lt, Lt => true
  | Gt, Gt => true
  | _, _ => false
  end.

Lemma comparison_eqb_spec c1 c2:
  reflect (c1 = c2) (comparison_eqb c1 c2).
Proof.
  destruct c1; destruct c2; simpl;
  try solve[apply ReflectT; reflexivity];
  apply ReflectF; intro C; discriminate.
Qed.*)

Instance StrictComp_n: StrictComp N_as_OT.compare.
Proof.
  constructor.
  - split; apply N_as_OT.compare_eq_iff.
  - intros x y.
    rewrite N_as_OT.compare_antisym.
    unfold CompOpp.
    destruct (N_as_OT.compare y x); split; auto; intros; discriminate.
  - intros x y z. rewrite !N_as_OT.compare_lt_iff. apply N_as_OT.lt_trans.
Qed.

Lemma StrictComp_alpha {A B: Type} (comp: B -> B -> comparison) (f: A -> B)
  (Hstrict: StrictComp comp)
  (Hinj: forall x y, f x = f y -> x = y):
  StrictComp (fun x y => comp (f x) (f y)).
Proof.
  destruct Hstrict as [strict_eq strict_lt_gt strict_trans].
  constructor.
  - intros x y. split.
    + intros Hcomp. apply strict_eq in Hcomp. auto.
    + intros; subst. apply strict_eq. reflexivity.
  - intros x y. apply strict_lt_gt.
  - intros x y z. apply strict_trans.
Qed.

Instance StrictComp_ascii: StrictComp Ascii_as_OT.compare.
Proof.
  unfold Ascii_as_OT.compare. apply StrictComp_alpha.
  apply StrictComp_n.
  intros x y Heq.
  apply (f_equal Ascii.ascii_of_N) in Heq.
  rewrite !Ascii.ascii_N_embedding in Heq. exact Heq.
Qed.


(*Lexicographic comparison of tuples*)
Definition lex_comp (c1 c2: comparison) : comparison :=
  match c1 with
  | Eq => c2
  | x => x
  end.

Definition tuple_compare {A B: Type} (comp1: A -> A -> comparison) (comp2: B -> B -> comparison)
  (x1 : A * B) (x2: A * B) : comparison :=
  lex_comp (comp1 (fst x1) (fst x2)) (comp2 (snd x1) (snd x2)).

Definition list_compare {A: Type} (comp: A -> A -> comparison) :=
  fix list_compare (l1 l2: list A) : comparison :=
  match l1, l2 with
  | nil, nil => Eq
  | nil, _ => Lt
  | _, nil => Gt
  | x1 :: t1, x2 :: t2 =>
    tuple_compare comp list_compare (x1, t1) (x2, t2)
    (* lex_comp (comp x1 x2) (list_compare t1 t2) *)
  end.*

(*OK, going to use ssreflect because they have lists and prods already*)
(*From mathcomp.ssreflect Require Import order.
From HB Require Import structures.
Check prod.
Print seqprod_with.
HB.about (list nat).

(*TODO: maybe use ssreflect orderType?*)
Definition compare_destruct {A: Type} (comp: A -> A -> comparison) :=
  forall x y, CompSpec eq (fun x y => comp x y = Lt) x y (comp x y).

Lemma tuple_compare_spec {A B: Type} (comp1: A -> A -> comparison) (comp2: B -> B -> comparison):
  compare_destruct comp1 ->
  compare_destruct comp2 ->
  compare_destruct (tuple_compare comp1 comp2).

Definition StrictComp_tuple {A B: Type} {comp1: A -> A -> comparison} {comp2: B -> B -> comparison}
  (Hcomp1: StrictComp comp1) (Hcomp2: StrictComp comp2) : StrictComp (tuple_compare comp1 comp2).
Proof.
  destruct Hcomp1 as [Heq1 Hlt1 Htrans1]; destruct Hcomp2 as [Heq2 Hlt2 Htrans2].
  (*The equality case is useful in multiple places*)


comparison_eq
  (fun x1 x2 : A * B =>
   match comp1 (fst x1) (fst x2) with
   | Eq => comp2 (snd x1) (snd x2)
   | _ => comp1 (fst x1) (fst x2)
   end)

  unfold tuple_compare, lex_comp.
  constructor.
  - intros [x1 x2] [y1 y2]; simpl.
    destruct (comp1 x1 y1) eqn : Hcomp1.
    + apply Heq1 in Hcomp1; subst.
      split.
      * intros Hcomp2. apply Heq2 in Hcomp2; subst; auto.
      * intros Heq; inversion Heq; subst; apply Heq2; reflexivity.
    + split; try discriminate. intros Heq; inversion Heq; subst.
      rewrite <- Hcomp1. apply Heq1; reflexivity.
    + split; try discriminate. intros Heq; inversion Heq; subst.
      rewrite <- Hcomp1. apply Heq1; reflexivity.
  - intros [x1 x2] [y1 y2]; simpl.
    destruct (comp1 x1 y1) eqn : Hcomp1.
    + 

 destruct
      rewrite Heq2. apply Heq2.


(*Define new string function*)

list_ascii_of_string


Search list_ascii_of_string.
  



Ascii_as_OT.compare =
fun a b : Ascii.ascii => N_as_OT.compare (Ascii.N_of_ascii a) (Ascii.N_of_ascii b)
     : Ascii.ascii -> Ascii.ascii -> comparison

Instance StrictComp_string : StrictComp String_as_OT.compare.
Proof.
  unfold String_as_OT.compare.
  Print Ascii_as_OT.compare.


  constructor.


Definition typevar_compare (t1 t2: typevar) : comparison := String_as_OT.compare t1 t2.


Definition typesym_compare (t1 t2: typesym) : comparison := 
  tuple_compare String_as_OT.compare (list_compare typevar_compare)
    (ts_name t1) (ts_args t1) (ts_name t2) (ts_args t2).

Fixpoint vty_compare (v1 v2: vty) : comparison :=
  match v1, v2 with
  | vty_int, vty_int => Eq
  | vty_int, _ => Lt
  | _, vty_int => Gt
  | vty_real, vty_real => Eq
  | vty_real, _ => Lt
  | _, vty_real => Gt
  | vty_var v1, vty_var v2 => typevar_compare v1 v2
  | vty_var _, _ => Lt
  | _, vty_var _ => Gt
  | vty_cons t1 vs1, vty_cons t2 vs2 =>
    tuple_compare typesym_compare (list_compare vty_compare)
      t1 vs1 t2 vs2
  end.

Print mut_adt.
Print alg_datatype.
Print funsym.
Print fpsym.

Definition fpsym_compare (f1 f2: fpsym) : comparison :=
  lex_comp (String_as_OT.compare (s_name f1) (s_name f2))
    (tuple_compare (list_compare typevar_compare) (list_compare vty_compare)
      (s_params f1) (s_args f1) (s_params f2) (s_args f2)).

Definition funsym_compare (f1 f2: funsym) : comparison :=
  tuple_compare fpsym_compare vty_compare (f_sym f1) (f_ret f1) (f_sym f2) (f_ret f2).

Definition alg_datatype_compare (a1 a2: alg_datatype) : comparison :=
  tuple_compare typesym_compare (list_compare funsym_compare) (adt_name a1) (adt_constr_list a1)
    (adt_name a2) (adt_constr_list a2).

Definition mut_adt_compare (m1 m2: mut_adt) : comparison :=
  tuple_compare (list_compare alg_datatype_compare) (list_compare typevar_compare) (typs m1) (m_params m1)
    (typs m2) (m_params m2).


(*Nope, let's go back to existing map*)

Require Import Coq.FSets.FMapAVL.

Module TyOrderedType <: OrderedType.
Definition t := vty.
Definition eq (t1 t2: t) : Prop := (t1 = t2).
Definition eq_equiv : Equivalence eq.
Proof.
  apply eq_equivalence.
Defined.
Definition lt v1 v2 := vty_compare v1 v2 = Lt. 
Instance lt_strorder : StrictOrder lt.
Print StrictOrder.
End TyOrderedType.

Module MutOrderedType <: OrderedType.
End MutOrderedType.

Print OrderedType.*)*)


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
    if (*is_vty_adt s ty1 &&*) (typecheck_term s tm == Some ty1) &&
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
    (*is_vty_adt s ty &&*)
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
        -- reflT=>//.
          move=> x [<-// | Hinx]. by apply Hptl.
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
    case Hnull: (null ps) =>/=. reflF. by rewrite Hnull in H6.
    apply iff_reflect. split.
    + move=> Hmatch. inversion Hmatch; subst.
      move: HallT H5. clear. elim: ps => [// | [p1 f1] pt /= IH HallT Hall].
      apply /andP; split.
      * apply /(ForallT_hd _ _ _ HallT). by apply (Hall (p1, f1)); left. 
      * apply IH=>//. by inversion HallT. move=> x Hinx.
        by apply Hall; right.
    + move=> Hcheck. rewrite Forall_forall in Hallps. 
      constructor=>//; last by rewrite Hnull.
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

(*We will typecheck [decrease_fun] and [decrease_pred]
  differently: the naive way takes exponential time.
  Instead, we will find the index for each fun/predsym at a time*)

(* Print fn.
Print sn.*)

(*Do all occurrences of fpsymbol f appear with index i smaller?*)
Fixpoint check_decrease_fun_aux (f: fpsym) (idx: nat)
  (small: list vsymbol) (hd: option vsymbol) (m: mut_adt)
  (vs: list vty) (t: term) : bool :=
  match t with
  | Tfun f1 tys tms =>
    if fpsym_eqb f f1 then
      match (nth tm_d tms idx) with
      | Tvar x =>
          (x \in small) &&
          (tys == map vty_var (s_params f)) &&
          all (check_decrease_fun_aux f idx small hd m vs) tms
      | _ => false
      end
    else 
      (*Not recursive*)
      all (fun t => check_decrease_fun_aux f idx small hd m vs t) tms
  | Tmatch t ty pats =>
    check_decrease_fun_aux f idx small hd m vs t &&
    match t with
    | Tvar x =>
      if (check_var_case hd small x) then
         all (fun x =>
          check_decrease_fun_aux f idx
          (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x))) 
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
          small)) (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)
          ) pats
      else
        all (fun x =>
        check_decrease_fun_aux f idx
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats
    | Tfun f1 tys tms =>
      all (fun x =>
          check_decrease_fun_aux f idx
          (union vsymbol_eq_dec (vsyms_in_m m vs 
            (get_constr_smaller small hd m vs f1 tys tms (fst x)))
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
          small)) (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)
          ) pats
    | _ =>
      all (fun x =>
        check_decrease_fun_aux f idx 
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats
    end
  | Tlet t1 v t2 =>
    check_decrease_fun_aux f idx small hd m vs t1 &&
    check_decrease_fun_aux f idx (remove vsymbol_eq_dec v small) (upd_option hd v) m vs t2
  | Tif f1 t1 t2 =>
    check_decrease_pred_aux f idx small hd m vs f1 &&
    check_decrease_fun_aux f idx small hd m vs t1 &&
    check_decrease_fun_aux f idx small hd m vs t2
  | Teps f1 v =>
    check_decrease_pred_aux f idx (remove vsymbol_eq_dec v small) (upd_option hd v) m vs f1
  | _ => true
  end
with check_decrease_pred_aux (f: fpsym) (idx: nat)
  (small: list vsymbol) (hd: option vsymbol) (m: mut_adt)
  (vs: list vty) (fmla: formula) : bool :=
  match fmla with
  | Fpred f1 tys tms =>
    if fpsym_eqb f f1 then
      match (nth tm_d tms idx) with
      | Tvar x =>
          (x \in small) &&
          (tys == map vty_var (s_params f)) &&
          all (check_decrease_fun_aux f idx small hd m vs) tms
      | _ => false
      end
    else 
      (*Not recursive*)
      all (fun t => check_decrease_fun_aux f idx small hd m vs t) tms
  | Fmatch t ty pats =>
    check_decrease_fun_aux f idx small hd m vs t &&
    match t with
    | Tvar x =>
      if (check_var_case hd small x) then
         all (fun x =>
          check_decrease_pred_aux f idx
          (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x))) 
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
          small)) (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)
          ) pats
      else
        all (fun x =>
        check_decrease_pred_aux f idx
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats
    | Tfun f1 tys tms =>
      all (fun x =>
          check_decrease_pred_aux f idx
          (union vsymbol_eq_dec (vsyms_in_m m vs 
            (get_constr_smaller small hd m vs f1 tys tms (fst x)))
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
          small)) (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)
          ) pats
    | _ =>
      all (fun x =>
        check_decrease_pred_aux f idx 
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
        (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) pats
    end
  | Fnot f1 =>
    check_decrease_pred_aux f idx small hd m vs f1
  | Fquant q v f1 =>
    check_decrease_pred_aux f idx (remove vsymbol_eq_dec v small) (upd_option hd v) m vs f1
  | Feq ty t1 t2 =>
    check_decrease_fun_aux f idx small hd m vs t1 &&
    check_decrease_fun_aux f idx small hd m vs t2
  | Fbinop b f1 f2 =>
    check_decrease_pred_aux f idx small hd m vs f1 &&
    check_decrease_pred_aux f idx small hd m vs f2
  | Flet t1 v f1 =>
    check_decrease_fun_aux f idx small hd m vs t1 &&
    check_decrease_pred_aux f idx (remove vsymbol_eq_dec v small) (upd_option hd v) m vs f1
  | Fif f1 f2 f3 =>
    check_decrease_pred_aux f idx small hd m vs f1 &&
    check_decrease_pred_aux f idx small hd m vs f2 &&
    check_decrease_pred_aux f idx small hd m vs f3
  | _ => true
  end.

(*Check termination for all terms/formulas for a given
  index for a fun or predsym*)
Definition check_decrease_idx {A: Type}
  (check_aux: fpsym -> nat -> list vsymbol -> option vsymbol ->
    mut_adt -> list vty -> A -> bool)
  (l: list (list vsymbol * A))
  (m: mut_adt) (args: list vty)
  (i: nat) (f: fpsym) : bool :=
  forallb (fun x => (*Check given term's termination*)
    let '(vs, t) := x in
    match nth_error vs i with
    | Some v =>
        check_aux f i nil (Some v) m args t
    | None => false
    end
  ) l.

(*Group indices by mutual adt*)
(*Should really be map, not assoc list*)
(*Hmm, should we use pmap or something?*)
(*want map (mut_adt * list vty) (map fsym (list nat))*)
(*Require Import Coq.FSets.FMapAVL.*)

(*We really do want a BST instead of binary trie.
  With tuples/lists, ordering is much easier than *)



(*Countable instance for mutual ADT*)



(*TODO: if this gets awful, use stdpp*)
(* Definition set_assoc_list  {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (y: B) : list (A * B) :=
 fold_right (fun t acc => if eq_dec x (fst t) then (x, y) :: acc 
  else t :: acc) nil l. *)


(*A very lazy, inefficient implementation of association lists*)
(*Replace if element there, do nothing if not*)
Definition replace_assoc_list_aux {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B) : list (A * B) := 
  fold_right (fun h acc => (if eq_dec x (fst h) then (x, f x (snd h)) else h) :: acc) nil l.

(*We define "get" on this*)
(* Lemma replace_aux_get1 {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B): *)
  

Lemma replace_assoc_list_aux_elt {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B) :
  forall z1 z2, In (z1, z2) (replace_assoc_list_aux eq_dec l x f) <->
     (In (z1, z2) l /\ z1 <> x) \/ (z1 = x /\ exists y1, In (x, y1) l /\ z2 = f x y1).
Proof.
  intros z1 z2. induction l as [| [x1 y1] tl IH]; simpl.
  - split; intros; destruct_all; contradiction.
  - split; intros Hin.
    + destruct Hin as [Heq|Hin].
      * destruct (eq_dec x x1); simpl in Heq; inversion Heq; subst.
        -- right. split; auto. exists y1. auto.
        -- left. auto.
      * apply IH in Hin.
        destruct Hin as [[Hin Hneq]|[Heq [y2 [Hiny2 Heqy2]]]].
        -- left. auto.
        -- subst. right. split; auto. exists y2. auto.
    + destruct Hin as [[[Heq | Hin] Hneq] | [Heq [y2 [[Heq1 | Hin] Heqy2]]]].
      * inversion Heq; subst. destruct (eq_dec x z1); subst; auto; contradiction.
      * right. apply IH; auto.
      * inversion Heq1; subst. destruct (eq_dec x x); auto; contradiction.
      * subst. right. apply IH. right. split; auto.
        exists y2. auto.
Qed.

Lemma replace_assoc_list_map_fst {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B):
  map fst (replace_assoc_list_aux eq_dec l x f) = map fst l.
Proof.
  induction l as [| [x1 y1] tl IH]; simpl; auto.
  destruct (eq_dec x x1); simpl; subst; rewrite IH; reflexivity.
Qed.


Definition replace_assoc_list {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B) (y: B) : list (A * B) :=
  match (get_assoc_list eq_dec l x) with
  | Some _ => replace_assoc_list_aux eq_dec l x f
  | None => (x, y) :: l
  end.

Lemma replace_assoc_list_keys {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B) (y: B):
  forall z1 z2, In (z1, z2) (replace_assoc_list eq_dec l x f y) <->
    ((In (z1, z2) l /\ z1 <> x) \/ (z1 = x /\ exists y1, In (x, y1) l /\ z2 = f x y1)) \/
    (z1 = x /\ z2 = y /\ ~ In x (map fst l)).
Proof.
  intros z1 z2.
  unfold replace_assoc_list.
  destruct (get_assoc_list eq_dec l x) eqn : Hget.
  - rewrite replace_assoc_list_aux_elt.
    split; intros Hin.
    + left. auto.
    + destruct Hin as [? | [Hx [Hy Hinx]]]; auto; subst.
      assert (Hget': get_assoc_list eq_dec l x = None) by (apply get_assoc_list_none; auto).
      rewrite Hget' in Hget. discriminate.
  - simpl. apply get_assoc_list_none in Hget.
    split; intros Hin.
    + destruct Hin as [ Heq | Hin]; [inversion Heq |]; subst; auto.
      left. left. split; auto. intro C; subst.
      apply Hget. rewrite in_map_iff. exists (x, z2); auto.
    + destruct Hin as [[[Hin Hneq] | [Heq [y1 [Hiny1 Heqy1]]]] | [Hx [Hy _]]]; subst; auto.
      exfalso. apply Hget. rewrite in_map_iff. exists (x, y1); auto.
Qed.
 

(*Replace an element if it is present, add (x, y) otherwise*)
(* Fixpoint replace_assoc_list {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B) (y: B) : list (A * B) :=
  match l with
  | nil => [(x, y)]
  | h :: tl => if eq_dec x (fst h) then (x, f x (snd h)) :: tl else 
    h :: replace_assoc_list eq_dec tl x f y
  end. *)
(* 
Definition map_elt_aux {A B: Set} (eq_dec: forall (x y: A), {x = y} + {x <> y})
  (l: list (A * B)) (x: A) : option B := get_assoc_list eq_dec l x.


Lemma replace_assoc_list_keys {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B) (y: B):
  forall z1 z2, In (z1, z2) (replace_assoc_list eq_dec l x f y) <->
    (In (z1, z2) l /\ z1 <> x) \/ (z1 = x /\ exists y1, In (x, y1) l /\ z2 = f x y1) \/
    (z1 = x /\ z2 = y /\ ~ In x (map fst l)).
Proof.
  intros z1 z2.
  induction l as [| h t IH]; simpl.
  - split; intros Hin.
    + destruct Hin as [Heq | []]; inversion Heq; subst; auto.
      right. right. auto.
    + destruct Hin as [[[] _]|[[_ [_ [[] _]]]|[Heq1 [Heq2 _]]]]; subst; auto.
  - destruct h as [x1 y1]; simpl in *. destruct (eq_dec x x1); simpl; subst.
    + split; intros Hin.
      * destruct Hin as [Heq | Hin]; [inversion Heq; subst |].
        -- right. left. split; auto. exists y1. auto.
        -- destruct (eq_dec z1 x1); subst.
          ++  

 split; intros; destruct_all; auto; try contradiction. 
  left.


 intros.

  forall z, In z (map fst l) *)

Lemma replace_assoc_list_nodup {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B) (y: B) :
  NoDup (map fst l) ->
  NoDup (map fst (replace_assoc_list eq_dec l x f y)).
Proof.
  unfold replace_assoc_list.
  destruct (get_assoc_list eq_dec l x) eqn : Hget.
  - rewrite replace_assoc_list_map_fst. auto.
  - intros Hnodup. simpl. constructor; auto.
    apply get_assoc_list_none in Hget. auto.
Qed.
    
Definition set_assoc_list  {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (y: B) : list (A * B) :=
 replace_assoc_list eq_dec l x (fun _ _ => y) y.

Definition map_aux (A B: Set) := list (A * B).
Definition map_get_aux {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: map_aux A B) (x: A) : option B := get_assoc_list eq_dec m x.
Definition map_set_aux {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: map_aux A B) (x: A) (y: B) : map_aux A B := set_assoc_list eq_dec m x y.
Definition map_replace_aux {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: map_aux A B) (x: A) (f: A -> B -> B) y: map_aux A B := replace_assoc_list eq_dec m x f y.
Definition map_bindings_aux {A B: Set} (m: map_aux A B) : list (A * B) := m.
Definition map_singleton_aux {A B: Set} (x: A) (y: B) : map_aux A B := [(x, y)].
Definition map_empty_aux {A B: Set} : map_aux A B := nil.

Definition map_wf {A B: Set} (m: map_aux A B) : Prop :=
  NoDup (map fst m).
Definition map (A B: Set) := {m: map_aux A B | map_wf m}.
Definition map_get {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: map A B) (x: A) : option B := map_get_aux eq_dec (proj1_sig m) x.
Definition map_set_proof {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: map A B) (x: A) (y: B) : map_wf (map_set_aux eq_dec (proj1_sig m) x y).
Proof.
  unfold map_wf, map_set_aux, set_assoc_list.
  apply replace_assoc_list_nodup.
  destruct m as [m m_wf].
  apply m_wf.
Qed.
Definition map_replace_proof {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: map A B) (x: A) (f: A -> B -> B) (y: B) : map_wf (map_replace_aux eq_dec (proj1_sig m) x f y).
Proof.
  unfold map_wf, map_replace_aux. apply replace_assoc_list_nodup.
  destruct m as [m m_wf].
  apply m_wf.
Qed.
Definition map_singleton_proof {A B: Set} (x: A) (y: B) : map_wf (map_singleton_aux x y).
Proof.
  constructor; auto. constructor.
Qed.
Definition map_empty_proof {A B: Set} : map_wf (@map_empty_aux A B).
Proof. constructor. Qed.
Definition map_set {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: map A B) (x: A) (y: B) : map A B := exist _ _ (map_set_proof eq_dec m x y).
Definition map_replace {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: map A B) (x: A) (f: A -> B -> B) (y: B) : map A B := exist _ _ (map_replace_proof eq_dec m x f y).
Definition map_bindings {A B: Set} (m: map A B) : list (A * B) := map_bindings_aux (proj1_sig m).
Definition map_singleton {A B: Set} x y : map A B := exist _ _ (map_singleton_proof x y).
Definition map_empty {A B: Set} : map A B := exist _ _ (@map_empty_proof A B).

(*And now the proofs*)
Section MapProofs.
Context  {A B: Set} (eq_dec: forall (x y: A), {x = y} + { x <> y}).

Local Lemma map_get_some_iff (m: map A B) (x: A) (y: B):
  map_get eq_dec m x = Some y <-> In (x, y) (proj1_sig m).
Proof.
  unfold map_get, map_get_aux. split; intros Hin.
  - apply get_assoc_list_some in Hin; auto.
  - apply get_assoc_list_nodup; auto. destruct m; auto.
Qed.

Local Lemma map_get_none_iff (m: map A B) (x: A):
  map_get eq_dec m x = None <-> ~ In x (List.map fst (proj1_sig m)).
Proof.
  apply get_assoc_list_none.
Qed.

Local Lemma map_get_eq_iff (m1 m2: map A B) (x: A):
  map_get eq_dec m1 x = map_get eq_dec m2 x <-> 
  (forall y, In (x, y) (proj1_sig m1) <-> In (x, y) (proj1_sig m2)).
Proof.
  destruct (map_get eq_dec m2 x) as [y2 |] eqn : Hget2.
  - rewrite !map_get_some_iff in Hget2 |- *.
    split.
    + intros Hget1 y.
      split; intros Hin.
      -- assert (y = y2) by (apply (nodup_fst_inj (proj2_sig m1) Hin); auto);
          subst; auto.
      -- assert (y = y2) by (apply (nodup_fst_inj (proj2_sig m2) Hin); auto);
          subst; auto.
    + intros Hiff. apply Hiff; auto.
  - rewrite !map_get_none_iff in Hget2 |- *.
    split.
    + intros Hget1 y. split; intros Hin; exfalso; [apply Hget1 | apply Hget2];
      rewrite in_map_iff; exists (x, y); auto.
    + intros Hiff Hinfst. apply Hget2.
      rewrite !in_map_iff in Hinfst |- *.
      destruct Hinfst as [[x1 y1] [Hx Hinx]]; subst.
      exists (x1, y1); split; auto. apply Hiff; auto.
Qed.


Lemma map_set_get_same (m: map A B) (x: A) (y: B):
  map_get eq_dec (map_set eq_dec m x y) x = Some y.
Proof.
  rewrite map_get_some_iff. simpl.
  unfold map_set_aux.
  apply replace_assoc_list_keys.
  destruct (in_dec eq_dec x (List.map fst (sval m))) as [Hin | Hnotin].
  + left. right. split; auto. rewrite in_map_iff in Hin.
    destruct Hin as [[x1 y1] [Hxx1 Hin1]]; subst; exists y1; auto.
  + right. auto.
Qed.

Lemma map_set_get_diff (m: map A B) (x: A) (y: B) (z: A):
  x <> z ->
  map_get eq_dec (map_set eq_dec m x y) z = map_get eq_dec m z.
Proof.
  intros Hneq.
  apply map_get_eq_iff.
  intros z2. simpl.
  unfold map_set_aux. rewrite replace_assoc_list_keys.
  split; intros; destruct_all; subst; try contradiction; auto.
Qed.

Lemma map_singleton_get1 (x : A) (y: B) :
  map_get eq_dec (map_singleton x y) x = Some y.
Proof.
  apply map_get_some_iff. simpl. auto.
Qed.

Lemma map_singleton_get2 (x : A) (y: B) z:
  x <> z ->
  map_get eq_dec (map_singleton x y) z = None.
Proof.
  intros Hneq.
  apply map_get_none_iff. simpl. intros [Heq | []]; auto.
Qed.

Lemma map_empty_get z: @map_get A B eq_dec map_empty z = None.
Proof.
  apply map_get_none_iff. simpl. auto.
Qed.

(*Replace lemmas*)
Lemma map_replace_get_same1 (m: map A B) (x: A) (f: A -> B -> B) (y: B) (y1: B)
  (Hget: map_get eq_dec m x = Some y1):
  map_get eq_dec (map_replace eq_dec m x f y) x = Some (f x y1).
Proof.
  apply map_get_some_iff. simpl. apply replace_assoc_list_keys.
  apply get_assoc_list_some in Hget.
  left. right. split; auto. exists y1; auto.
Qed.

Lemma map_replace_get_same2 (m: map A B) (x: A) (f: A -> B -> B) (y: B)
  (Hget: map_get eq_dec m x = None):
  map_get eq_dec (map_replace eq_dec m x f y) x = Some y.
Proof.
  apply map_get_some_iff.
  apply map_get_none_iff in Hget.
  apply replace_assoc_list_keys. right. auto.
Qed.

Lemma map_replace_get_diff (m: map A B) (x: A) (f: A -> B -> B) (y: B) (z: A):
  x <> z ->
  map_get eq_dec (map_replace eq_dec m x f y) z = map_get eq_dec m z.
Proof.
  intros Hneq.
  apply map_get_eq_iff. intros y1; simpl.
  rewrite replace_assoc_list_keys. 
  split; intros; destruct_all; subst; auto; contradiction.
Qed.

Lemma map_bindings_iff (m: map A B) (x: A) (y: B) :
  In (x, y) (map_bindings m) <-> map_get eq_dec m x = Some y.
Proof.
  rewrite map_get_some_iff. reflexivity.
Qed.

End MapProofs.

Definition group_indices_adt 
  (l: list (fpsym * list vsymbol)):
  map (mut_adt * list vty)  (map fpsym (list nat)) :=
  fold_right (fun x acc =>
    let '(f, vs) := x in

    fold_right (fun vi m =>
      let '(v, idx) := vi in
      match (is_vty_adt gamma (snd v)) with
      | Some (m1, a, args) => 
        map_replace 
          (tuple_eq_dec mut_adt_dec (list_eq_dec vty_eq_dec))
          m (m1, args) (fun t mp =>
          map_replace fpsym_eq_dec mp f (fun _ l => idx :: l) [idx])
          map_empty

      | None => m
      end
      ) acc (combine vs (iota 0 (length vs)))
  ) map_empty l.

(*A more powerful version of "find" that allows a predicate to return an option
  which we return*)
(*Oops, forgot I was using ssreflect. Redo?*)
Definition list_find {A B: Type} (p: A -> option B) (l: list A) : option (A * B) :=
  fold_right (fun x acc => match (p x) with | Some y => Some (x, y) | None => acc end) None l.

Lemma list_find_none_iff {A B: Type} (p: A -> option B) (l: list A):
  list_find p l = None <-> forall x, In x l -> p x = None.
Proof.
  induction l; simpl; split; intros; auto; try contradiction; destruct_all; subst; auto.
  - destruct (p x); auto; discriminate.
  - destruct (p a) eqn : Ha; try discriminate.
    apply IHl; auto.
  - destruct (p a) eqn : Ha.
    + exfalso. assert (Hnone: p a = None) by auto.
      rewrite Hnone in Ha; discriminate.
    + apply IHl; auto.
Qed.

Lemma list_find_some {A B: Type} (p: A -> option B) (l: list A)  x y:
  list_find p l = Some (x, y) ->
  In x l /\ p x = Some y.
Proof.
  induction l as [| h t IH]; simpl; try discriminate.
  destruct (p h) eqn : Hph; intros Hsome.
  - inversion Hsome; subst. auto.
  - apply IH in Hsome. destruct_all; auto.
Qed.


(*Option version of "forall"*)
(*TODO: define in terms of "pmap"?*)
Definition list_collect {A B: Type} (p: A -> option B) (l: list A) : option (list B) :=
  fold_right (fun x acc =>
    Option.bind (fun y =>
                Option.bind (fun z => Some (z :: y)) (p x)) acc
  ) (Some nil) l.

Lemma list_collect_some_iff {A B: Type} (p: A -> option B) (l: list A) (l1: list B):
  list_collect p l = Some l1 <->  (List.map Some l1 = List.map p l) /\ (forall x, In x l -> isSome (p x)).
Proof.
  revert l1.
  induction l as [| h t IH]; simpl; intros [| h1 t1]; simpl; split; intros Hl; auto.
  - inversion Hl.
  - destruct Hl; discriminate.
  - destruct (list_collect p t); try discriminate.
    destruct (p h); discriminate.
  - destruct Hl; discriminate.
  - destruct (list_collect p t) eqn : Ht; try discriminate.
    destruct (p h) eqn : Hph; try discriminate.
    simpl in Hl; inversion Hl; subst.
    destruct (IH t1) as [IH' _]; clear IH; specialize (IH' Logic.eq_refl); destruct IH' as 
    [Hsome Hall].
    rewrite Hsome. split; auto. intros; destruct_all; subst; auto. rewrite Hph; reflexivity.
  - destruct Hl as [Hht Hall]. inversion Hht as [[Hh Ht]] .
    specialize (IH t1); destruct IH as [_ IH]. rewrite IH; auto.
Qed.

Lemma list_collect_none_iff {A B: Type} (p: A -> option B) (l: list A):
  list_collect p l = None <-> (exists x, In x l /\ p x = None).
Proof.
  induction l as [| h t IH]; simpl; split.
  - discriminate.
  - intros; destruct_all; contradiction.
  - intros Hnone.
    destruct (list_collect p t) eqn : Ht; simpl in Hnone; try discriminate.
    + destruct (p h) eqn : Hh; simpl in Hnone; try discriminate.
      exists h. auto.
    + apply IH in Hnone. destruct_all. eauto.
  - intros [x [[Hhx | Hinx] Hpx]]; subst; auto.
    + rewrite Hpx. simpl. destruct (list_collect p t); reflexivity.
    + destruct (list_collect p t); simpl; auto.
      assert (Some l = None); [| discriminate].
      apply IH. exists x; auto.
Qed.

(*Get all ADTs present in types*)

(*TODO: do s_args instead?*)
Definition get_adts_present (l: list (list vsymbol)) : list (mut_adt * list vty) :=
  fold_right (fun v acc => match (is_vty_adt gamma (snd v)) with
                            | Some (m, a, vs) => union (tuple_eq_dec mut_adt_dec (list_eq_dec vty_eq_dec))
                                [(m, vs)] acc
                            | None => acc
                            end) nil (concat l).

(*Get all index lists for each type in list*)

Definition check_decrease_fun 
  (mutfun: list (funsym * list vsymbol * term))
  (mutpred: list (predsym * list vsymbol * formula)) : option (mut_adt * list vty * list nat) :=
  (*First, build mut map*)
  let syms_args := (List.map (fun x => (f_sym (fst (fst x)), snd (fst x))) mutfun ++
     List.map (fun x => (p_sym (fst (fst x)), snd (fst x))) mutpred) in
  let all_vars := List.map snd syms_args in
  let all_muts := get_adts_present all_vars in
  (* let mut_map := group_indices_adt syms_args in *)
  let syms := List.map fst syms_args in 
  
  let tmlist := List.map (fun x => (snd (fst x), (snd x))) mutfun in
  let fmlalist := List.map (fun x => (snd (fst x), (snd x))) mutpred in
  (*For each m(vs), we have map funsym -> list indices*)
  (* let mut_mapl := map_bindings mut_map in  *)
  (* Option.map (fun x => (fst (fst x), snd x)) *)
  list_find (fun t => 
    (* let '(mvs, mp) := t in *)
    let '(m, vs) := t in
    (*For every fun/predsym in the list, 
      1. see if the sym appears in mp (if not, return false, there
      is no possible index)
      2. If so, get indices, and find one that works, if any*)
    (list_collect (fun (f : fpsym) => 
        List.find (fun i =>
          check_decrease_idx check_decrease_fun_aux tmlist m vs i f &&
          check_decrease_idx check_decrease_pred_aux fmlalist m vs i f
        ) (filter (fun i => vty_in_m m vs  (List.nth i (s_args f) vty_int)) (iota 0 (length (s_args f))))
    ) syms)
  ) all_muts.
(* 

Definition check_decrease_fun 
  (mutfun: list (funsym * list vsymbol * term))
  (mutpred: list (predsym * list vsymbol * formula)) : bool :=
  (*First, build mut map*)
  let syms_args := (List.map (fun x => (f_sym (fst (fst x)), snd (fst x))) mutfun ++
     List.map (fun x => (p_sym (fst (fst x)), snd (fst x))) mutpred) in
  let mut_map := group_indices_adt syms_args in
  let syms := List.map fst syms_args in 
  
  let tmlist := List.map (fun x => (snd (fst x), (snd x))) mutfun in
  let fmlalist := List.map (fun x => (snd (fst x), (snd x))) mutpred in
  (*For each m(vs), we have map funsym -> list indices*)
  let mut_mapl := map_bindings mut_map in
  List.existsb (fun t => 
    let '(mvs, mp) := t in
    let '(m, vs) := mvs in
    (*For every fun/predsym in the list, 
      1. see if the sym appears in mp (if not, return false, there
      is no possible index)
      2. If so, get indices, and find one that works, if any*)
    forallb (fun (f : fpsym) => 
      match (map_get fpsym_eq_dec mp f) with
      | None => false
      | Some l =>
        List.existsb (fun i =>
          check_decrease_idx check_decrease_fun_aux tmlist m vs i f &&
          check_decrease_idx check_decrease_pred_aux fmlalist m vs i f
        ) l
      end
    ) syms
  ) mut_mapl. *)

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

(*TODO: move*)
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
Definition mut_adt_eqb (m1 m2: mut_adt) : bool :=
  mut_adt_dec m1 m2.

Lemma mut_adt_eqb_spec (m1 m2: mut_adt) :
  reflect (m1 = m2) (mut_adt_eqb m1 m2).
Proof.
  unfold mut_adt_eqb. destruct (mut_adt_dec m1 m2); subst; simpl;
  [apply ReflectT | apply ReflectF]; auto.
Qed.

HB.instance Definition _ := hasDecEq.Build mut_adt mut_adt_eqb_spec.


(*TODO: do we need all info? Or just bool?*)
Definition check_termination (l: list funpred_def) : option (mut_adt * list typevar * list vty * list nat) :=
  if null l then None else
  let t := (split_funpred_defs l) in
  let syms := List.map (fun x => f_sym (fst (fst x))) (fst t) ++
    List.map (fun x => p_sym (fst (fst x))) (snd t) in
  match find_eq (fun (x : fpsym) => s_params x) syms with
  | Some params =>
    match (check_decrease_fun (fst t) (snd t)) with
    | Some (m, vs, idxs) =>
      (*Some of these might be implied by typing but we check them anyway for proofs*)
      if ((length vs =? length (m_params m))%nat &&
        mut_in_ctx m gamma) then
        Some (m, params, vs, idxs) else None
    | None => None
    end
    (* omap (fun x => (fst (fst x), params, snd (fst x), snd x)) (check_decrease_fun (fst t) (snd t)) *)
  | None => None
  end.

(*We need assumption that map snd vars = s_args f*)








  (*Check each funsym and each predsym*)
  (* forallb (fun (f: fpsym) => (*For given funsym*)
    let argslen := length (s_args f) in
    (*If no indices, true (constant symbols)*)
    (argslen =? 0)%nat || List.existsb (fun i => (*Check all terms using index i*)
      check_decrease_idx check_decrease_fun_aux tmlist i f &&
      check_decrease_idx check_decrease_pred_aux fmlalist i f
      ) (iota 0 argslen)
  ) (map f_sym funsyms ++ map p_sym predsyms). *)

(*Now to prove correct*)

(*This is substantially different than the Typing definition
  (because the naive implementation of that "algorithm" takes
    exponential time. This one is polynomial.)
  To prove this correct, we prove it equivalent to a Prop-typed
  version, and prove that equivalent to the Typing version.
  First, we define the Prop-typed version*)
Section TypecheckFuncProp.

(*(f: fpsym) (idx: nat)
  (small: list vsymbol) (hd: option vsymbol) (m: mut_adt)
  (vs: list vty) (t: term)*)



(*START - I think - without adding info to context, doesn't work
  Need separate funsym and predsym version for each (see if can redo somehow)
  Because otherwise have - funsym foo (not in fs), predsym foo (in ps)
  here - call recursive for Tfun foo when that is a problem*)
Unset Elimination Schemes.
Inductive decrease_fun_prop_triv
  (ind1: list vsymbol -> option vsymbol -> mut_adt -> list vty -> term -> Prop)
  (ind2: list vsymbol -> option vsymbol -> mut_adt -> list vty -> formula -> Prop):
  list vsymbol -> option vsymbol -> mut_adt -> list vty -> term -> Prop :=
  | Decp_tmatch: forall (small: list vsymbol) (hd: option vsymbol) 
    (m: mut_adt)
    (vs: list vty) 
    (mvar: vsymbol) (v: vty) (pats: list (pattern * term)),
    var_case hd small mvar ->
    (forall (x: pattern * term), In x pats ->
      ind1 (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x))) 
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
        small)) (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) ->
    decrease_fun_prop_triv ind1 ind2 small hd m vs (Tmatch (Tvar mvar) v pats).

Inductive decrease_pred_prop_triv
  (ind1: list vsymbol -> option vsymbol -> mut_adt -> list vty -> term -> Prop)
  (ind2: list vsymbol -> option vsymbol -> mut_adt -> list vty -> formula -> Prop):
  list vsymbol -> option vsymbol -> mut_adt -> list vty -> formula -> Prop :=
  | Decp_fmatch: forall (small: list vsymbol) (hd: option vsymbol) 
    (m: mut_adt)
    (vs: list vty) 
    (mvar: vsymbol) (v: vty) (pats: list (pattern * formula)),
    var_case hd small mvar ->
    (forall (x: pattern * formula), In x pats ->
      ind2 (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x))) 
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
        small)) (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) ->
    decrease_pred_prop_triv ind1 ind2 small hd m vs (Fmatch (Tvar mvar) v pats).

Section Dec.
Variable (f: funsym) (idx: nat).

Inductive decrease_fun_prop  : 
  list vsymbol -> option vsymbol -> mut_adt -> list vty -> term -> Prop :=
  | Decp_ttriv: forall small hd m vs t,
    decrease_fun_prop_triv decrease_fun_prop decrease_pred_prop small hd m vs t ->
    decrease_fun_prop small hd m vs t
with decrease_pred_prop :
  list vsymbol -> option vsymbol -> mut_adt -> list vty -> formula -> Prop :=
  | Decp_ftriv: forall small hd m vs f,
    decrease_pred_prop_triv decrease_fun_prop decrease_pred_prop small hd m vs f ->
    decrease_pred_prop small hd m vs f.

End Dec.
(*This will work but induction will be horrible - maybe just do 4 even though that is horrible*)
  
  | Decp_fun_in: forall (f1: funsym) (small: list vsymbol) (hd: option vsymbol) (m: mut_adt)
    (vs: list vty) (l: list vty) (ts: list term) (x: vsymbol),
    f = f_sym f1 ->
    nth tm_d ts idx = Tvar x ->
    In x small ->
    l = List.map vty_var (s_params f) ->
    Forall (decrease_fun_prop f idx small hd m vs) ts ->
    decrease_fun_prop f idx small hd m vs (Tfun f1 l ts)
  | Decp_fun_notin: forall (small: list vsymbol) (hd: option vsymbol)
    (m: mut_adt) (vs: list vty) 
    (f1: funsym) (l: list vty) (ts: list term),
    f <> f_sym f1 ->
    (forall t, In t ts -> decrease_fun_prop f idx small hd m vs t) ->
    decrease_fun_prop f idx small hd m vs (Tfun f1 l ts)



Unset Elimination Schemes.
Inductive decrease_fun_prop (f: fpsym) (idx: nat) : 
  list vsymbol -> option vsymbol -> mut_adt -> list vty -> term -> Prop :=
  | Decp_fun_in: forall (f1: funsym) (small: list vsymbol) (hd: option vsymbol) (m: mut_adt)
    (vs: list vty) (l: list vty) (ts: list term) (x: vsymbol),
    f = f_sym f1 ->
    nth tm_d ts idx = Tvar x ->
    In x small ->
    l = List.map vty_var (s_params f) ->
    Forall (decrease_fun_prop f idx small hd m vs) ts ->
    decrease_fun_prop f idx small hd m vs (Tfun f1 l ts)
  | Decp_fun_notin: forall (small: list vsymbol) (hd: option vsymbol)
    (m: mut_adt) (vs: list vty) 
    (f1: funsym) (l: list vty) (ts: list term),
    f <> f_sym f1 ->
    (forall t, In t ts -> decrease_fun_prop f idx small hd m vs t) ->
    decrease_fun_prop f idx small hd m vs (Tfun f1 l ts)
  | Decp_tmatch: forall (small: list vsymbol) (hd: option vsymbol) 
    (m: mut_adt)
    (vs: list vty) 
    (mvar: vsymbol) (v: vty) (pats: list (pattern * term)),
    var_case hd small mvar ->
    (forall (x: pattern * term), In x pats ->
      decrease_fun_prop f idx
      (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x))) 
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
        small)) (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) ->
    decrease_fun_prop f idx small hd m vs (Tmatch (Tvar mvar) v pats) 
  | Decp_tmatch_constr: forall (small: list vsymbol) (hd: option vsymbol) 
    (m: mut_adt) (vs: list vty) (v: vty) (pats: list (pattern * term))
    (c: funsym) (l: list vty) (tms: list term),
    decrease_fun_prop f idx small hd m vs (Tfun c l tms) ->
    (forall (x: pattern * term), In x pats ->
      decrease_fun_prop f idx
      (union vsymbol_eq_dec 
        (vsyms_in_m m vs 
          (get_constr_smaller small hd m vs c l tms (fst x)))
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
        small)) (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) ->
    decrease_fun_prop f idx small hd m vs 
      (Tmatch (Tfun c l tms) v pats) 
  | Decp_tmatch_rec: forall (small: list vsymbol) (hd: option vsymbol)
    m vs
    (tm: term) (v: vty) (pats: list (pattern * term)),
      (match tm with
        | Tvar var => ~ var_case hd small var
        | Tfun f l tms => false
        | _ => True
      end) ->
   decrease_fun_prop f idx small hd m vs tm ->
    (forall x, In x pats ->
      decrease_fun_prop f idx
      (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) ->
    decrease_fun_prop f idx small hd m vs (Tmatch tm v pats)
  | Decp_var: forall (small : list vsymbol) (hd: option vsymbol) m vs (v: vsymbol),
    decrease_fun_prop f idx small hd m vs (Tvar v)
  | Decp_const: forall (small : list vsymbol) (hd: option vsymbol) m vs (c: Syntax.constant),
    decrease_fun_prop f idx small hd m vs (Tconst c)
  | Decp_tlet: forall (small: list vsymbol) (hd: option vsymbol) m vs (t1: term)
    (v: vsymbol) (t2: term),
    decrease_fun_prop f idx small hd m vs t1 ->
    decrease_fun_prop f idx (remove vsymbol_eq_dec v small) (upd_option hd v) m vs t2 ->
    decrease_fun_prop f idx small hd m vs (Tlet t1 v t2)
  | Decp_tif: forall (small: list vsymbol) (hd: option vsymbol) m vs (f1: formula)
    (t1 t2: term),
    decrease_pred_prop f idx small hd m vs f1 ->
    decrease_fun_prop f idx small hd m vs t1 ->
    decrease_fun_prop f idx small hd m vs t2 ->
    decrease_fun_prop f idx small hd m vs (Tif f1 t1 t2)
  | Decp_eps: forall (small: list vsymbol) (hd: option vsymbol) m vs (f1: formula)
    (v: vsymbol),
    decrease_pred_prop f idx (remove vsymbol_eq_dec v small) (upd_option hd v) m vs f1 ->
    decrease_fun_prop f idx small hd m vs (Teps f1 v)
with decrease_pred_prop (f: fpsym) (idx: nat) : 
  list vsymbol -> option vsymbol -> mut_adt -> list vty -> formula -> Prop :=
  | Decp_pred_in: forall (small: list vsymbol) (hd: option vsymbol) m vs
    (p: predsym) (l: list vty) (ts: list term) x,
    f = p_sym p ->
    nth tm_d ts idx = Tvar x ->
    In x small ->
    l = List.map vty_var (s_params p) ->
    Forall (decrease_fun_prop f idx small hd m vs) ts ->
    decrease_pred_prop f idx small hd m vs (Fpred p l ts)
  | Decp_pred_notin: forall (small: list vsymbol) (hd: option vsymbol) m vs
    (p: predsym) (l: list vty) (ts: list term),
    f <> p_sym p ->
    (forall t, In t ts -> decrease_fun_prop f idx small hd m vs t) ->
    decrease_pred_prop f idx small hd m vs (Fpred p l ts)
  | Decp_fmatch: forall (small: list vsymbol) (hd: option vsymbol) m vs
    (mvar: vsymbol) (v: vty) (pats: list (pattern * formula)),
    var_case hd small mvar ->
    (forall x, In x pats -> decrease_pred_prop f idx
      (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x))) 
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
        small)) (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) ->
    decrease_pred_prop f idx small hd m vs (Fmatch (Tvar mvar) v pats)
  | Decp_fmatch_constr: forall (small: list vsymbol) (hd: option vsymbol) 
    (m: mut_adt)
    (vs: list vty)(v: vty) (pats: list (pattern * formula))
    (c: funsym) (l: list vty) (tms: list term),
    decrease_fun_prop f idx small hd m vs (Tfun c l tms) ->
    (forall (x: pattern * formula), In x pats ->
      decrease_pred_prop f idx
      (union vsymbol_eq_dec 
        (vsyms_in_m m vs 
          (get_constr_smaller small hd m vs c l tms (fst x)))
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
        small)) (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) ->
    decrease_pred_prop f idx small hd m vs 
      (Fmatch (Tfun c l tms) v pats) 
  | Decp_fmatch_rec: forall (small: list vsymbol) (hd: option vsymbol) m vs
    (tm: term) (v: vty) (pats: list (pattern * formula)),
     (match tm with
        | Tvar var => ~ var_case hd small var
        | Tfun f l tms => false
        | _ => True
      end) ->
    decrease_fun_prop f idx small hd m vs tm ->
    (forall x, In x pats ->
      decrease_pred_prop f idx
      (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
      (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) ->
    decrease_pred_prop f idx small hd m vs (Fmatch tm v pats)
  | Decp_true: forall (small: list vsymbol) (hd: option vsymbol) m vs,
    decrease_pred_prop f idx small hd m vs Ftrue
  | Decp_false: forall (small: list vsymbol) (hd: option vsymbol) m vs,
    decrease_pred_prop f idx small hd m vs Ffalse
  | Decp_not: forall small hd m vs f1,
    decrease_pred_prop f idx small hd m vs f1 ->
    decrease_pred_prop f idx small hd m vs (Fnot f1)
  | Decp_quant: forall (small: list vsymbol) (hd: option vsymbol) m vs
    (q: quant) (v: vsymbol) (f1: formula),
    decrease_pred_prop f idx (remove vsymbol_eq_dec v small) (upd_option hd v) m vs f1 ->
    decrease_pred_prop f idx small hd m vs (Fquant q v f1)
  | Decp_eq: forall (small: list vsymbol) (hd: option vsymbol) m vs
    (ty: vty) (t1 t2: term),
    decrease_fun_prop f idx small hd m vs t1 ->
    decrease_fun_prop f idx small hd m vs t2 ->
    decrease_pred_prop f idx small hd m vs (Feq ty t1 t2)
  | Decp_binop: forall (small: list vsymbol) (hd: option vsymbol) m vs
    (b: binop) (f1 f2: formula),
    decrease_pred_prop f idx small hd m vs f1 ->
    decrease_pred_prop f idx small hd m vs f2 ->
    decrease_pred_prop f idx small hd m vs (Fbinop b f1 f2)
  | Decp_flet: forall (small: list vsymbol) (hd: option vsymbol) m vs (t1: term)
    (v: vsymbol) (f1: formula),
    decrease_fun_prop f idx small hd m vs t1 ->
    decrease_pred_prop f idx (remove vsymbol_eq_dec v small) (upd_option hd v) m vs f1 ->
    decrease_pred_prop f idx small hd m vs (Flet t1 v f1)
  | Decp_fif: forall (small: list vsymbol) (hd: option vsymbol) m vs
    (f1 f2 f3: formula),
    decrease_pred_prop f idx small hd m vs f1 ->
    decrease_pred_prop f idx small hd m vs f2 ->
    decrease_pred_prop f idx small hd m vs f3 ->
    decrease_pred_prop f idx small hd m vs (Fif f1 f2 f3)
    .
Set Elimination Schemes.
Scheme decrease_fun_prop_ind := Minimality for decrease_fun_prop Sort Prop
with decrease_pred_prop_ind := Minimality for decrease_pred_prop Sort Prop.

(*Prove reflection*)

Ltac fun_caseF t := 
  let x := fresh in
  let H1 := fresh in
  let H2 := fresh in
intros; reflF; try contradiction; generalize dependent t;
  intros x H1 H2; rewrite H1 in H2; inversion H2; subst; auto. 

Ltac match_case small hd Halliff constr :=
  let Hall2 := fresh in
  case: (Halliff (fun x => remove_all vsymbol_eq_dec (pat_fv x.1) small) 
        (fun x => upd_option_iter hd (pat_fv x.1))) => Hall2;
          [ apply ReflectT, constr | reflF].

Lemma check_decrease_fun_spec f1 i m vs t f:
  (forall small hd, 
    reflect (decrease_fun_prop f1 i small hd m vs t) (check_decrease_fun_aux f1 i small hd m vs t)) *
  (forall small hd,
    reflect (decrease_pred_prop f1 i small hd m vs f) (check_decrease_pred_aux f1 i small hd m vs f) ).
Proof.
  apply term_formula_rect with (P1:= fun tm => forall small hd,
    reflect (decrease_fun_prop f1 i small hd m vs tm) (check_decrease_fun_aux f1 i small hd m vs tm))
    (P2:= fun f => forall small hd,
      reflect (decrease_pred_prop f1 i small hd m vs f) (check_decrease_pred_aux f1 i small hd m vs f) );
   try solve[intros; simpl; apply ReflectT; by constructor].
  - move=>fs tys tms Hall small hd/=.
    have Halliff: reflect (forall x, In x tms -> (decrease_fun_prop f1 i small hd m vs x)) 
      (all [eta check_decrease_fun_aux f1 i small hd m vs] tms).
    {
      eapply equivP. apply forallb_ForallP. 2: by apply Forall_forall.
      move=> x Hinx. by apply (ForallT_In _ term_eq_dec _ Hall).
    }
    case: (fpsym_eqb_spec f1 fs) => Hf1fs; last first.
    { case: Halliff => Hallin.
      - by apply ReflectT,Decp_fun_notin.
      - by reflF; contradiction.
    } 
    subst.
    case Hnth: (nth tm_d tms i) => [| v|||||]; try solve[fun_caseF (nth tm_d tms i)].
    case: (v \in small) /inP => Hinv; last by fun_caseF (nth tm_d tms i).
    case: (tys == [seq vty_var i | i <- s_params fs]) /eqP => Htys; last by
      reflF; contradiction.
    case: Halliff => Halliff.
    + apply ReflectT, Decp_fun_in with (x:=v) =>//.
      by rewrite Forall_forall.
    + reflF; last by contradiction. 
      by apply Halliff, Forall_forall.
  - move=> tm1 v tm2 Ht1 Ht2 small hd/=.
    case: (Ht1 small hd) => Hdec1; last by reflF.
    case: (Ht2 (remove vsymbol_eq_dec v small) (upd_option hd v)) => Hdec2; last by reflF.
    by reflT.
  - move=> fmla t1 t2 Hfmla Ht1 Ht2 small hd/=.
    case: (Hfmla small hd) => Hdec1; last by reflF.
    case: (Ht1 small hd) => Hdec2; last by reflF.
    case: (Ht2 small hd) => Hdec3; last by reflF.
    by reflT.
  - move=> tm v ps Htm Hps small hd/=.
    (*Need "all" case for all of them*)
    have Halliff: (forall small hd,
      reflect (forall x, In x ps -> (decrease_fun_prop f1 i (small x) (hd x) m vs (snd x))) 
      (all (fun x => check_decrease_fun_aux f1 i (small x) (hd x) m vs (snd x)) ps)).
    {
      move=> s h.
      eapply equivP. apply forallb_ForallP. 2: by apply Forall_forall.
      move=> x Hinx. apply (ForallT_In _ term_eq_dec _ Hps).
      rewrite in_map_iff. by exists x.
    }
    case: Htm => Htm; last first.
    { reflF; try contradiction. apply Htm. constructor. }
    move: Htm. (*2 non-trivial cases*) case: tm;
      try solve[intros; simpl; by match_case small hd Halliff Decp_tmatch_rec].
    + (*Var case*)
      move=> v' Hdecv/=.
      case: (check_var_case_spec hd small v') => Hvar; last
        by match_case small hd Halliff Decp_tmatch_rec.
      by case: (Halliff (fun x => (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs x.1))
           (remove_all vsymbol_eq_dec (pat_fv x.1) small)))
        (fun x => (upd_option_iter hd (pat_fv x.1)))) => Hall2;
      [apply ReflectT, Decp_tmatch | reflF].
    + (*Constr case*)
      move=> fs tys tms Hfs. 
      by case: (Halliff (fun x => (union vsymbol_eq_dec (vsyms_in_m m vs (get_constr_smaller small hd m vs fs tys tms x.1))
           (remove_all vsymbol_eq_dec (pat_fv x.1) small)))
        (fun x => (upd_option_iter hd (pat_fv x.1)))) => Hall2;
      [apply ReflectT, Decp_tmatch_constr | reflF].
  - (*Teps*) move=> fmla v Hfmla small hd /=.
    by case: (Hfmla (remove vsymbol_eq_dec v small) (upd_option hd v)) => Hdec1; [reflT | reflF].
  - (*Fpred*) move=>ps tys tms Hall small hd/=.
    have Halliff: reflect (forall x, In x tms -> (decrease_fun_prop f1 i small hd m vs x)) 
      (all [eta check_decrease_fun_aux f1 i small hd m vs] tms).
    {
      eapply equivP. apply forallb_ForallP. 2: by apply Forall_forall.
      move=> x Hinx. by apply (ForallT_In _ term_eq_dec _ Hall).
    }
    case: (fpsym_eqb_spec f1 ps) => Hf1fs; last first.
    { case: Halliff => Hallin; last by reflF.
      by apply ReflectT,Decp_pred_notin.
    } 
    subst.
    case Hnth: (nth tm_d tms i) => [| v|||||]; try solve[fun_caseF (nth tm_d tms i)].
    case: (v \in small) /inP => Hinv; last by fun_caseF (nth tm_d tms i).
    case: (tys == [seq vty_var i | i <- s_params ps]) /eqP => Htys; last by
      reflF; contradiction.
    case: Halliff => Halliff.
    + apply ReflectT, Decp_pred_in with (x:=v) =>//.
      by rewrite Forall_forall.
    + reflF; last by contradiction. 
      by apply Halliff, Forall_forall.
  - (*Fquant*) move=>q v fmla Hfmla small hd/=.
    by case: (Hfmla (remove vsymbol_eq_dec v small) (upd_option hd v)) => Hdec1; [reflT |reflF].
  - (*Feq*) move=> v t1 t2 Ht1 Ht2 small hd/=.
    case: (Ht1 small hd) => Hdec1; last by reflF.
    case: (Ht2 small hd) => Hdec2; last by reflF.
    by reflT.
  - (*Fbinop*) move=>b fm1 fm2 Hfm1 Hfm2 small hd /=.
    case: (Hfm1 small hd) => Hdec1; last by reflF.
    case: (Hfm2 small hd) => Hdec2; last by reflF.
    by reflT.
  - (*Fnot*) move=>fm1 Hfm1 small hd/=.
    case: (Hfm1 small hd) => Hdec; last by reflF.
    by reflT.
  - (*Flet*) move=> tm v fm Htm Hfm small hd/=.
    case: (Htm small hd) => Hdec1; last by reflF.
    case: (Hfm (remove vsymbol_eq_dec v small) (upd_option hd v)) => Hdec2; last by reflF.
    by reflT.
  - (*Fif*) move=> fm1 fm2 fm3 Hfm1 Hfm2 Hfm3 small hd/=.
    case: (Hfm1 small hd) => Hdec1; last by reflF.
    case: (Hfm2 small hd) => Hdec2; last by reflF.
    case: (Hfm3 small hd) => Hdec3; last by reflF.
    by reflT.
  - (*Fmatch*) move=> tm v ps Htm Hps small hd/=.
    (*Need "all" case for all of them*)
    have Halliff: (forall small hd,
      reflect (forall x, In x ps -> (decrease_pred_prop f1 i (small x) (hd x) m vs (snd x))) 
      (all (fun x => check_decrease_pred_aux f1 i (small x) (hd x) m vs (snd x)) ps)).
    {
      move=> s h.
      eapply equivP. apply forallb_ForallP. 2: by apply Forall_forall.
      move=> x Hinx. apply (ForallT_In _ formula_eq_dec _ Hps).
      rewrite in_map_iff. by exists x.
    }
    case: Htm => Htm; last first.
    { reflF; try contradiction. apply Htm. constructor. }
    move: Htm. (*2 non-trivial cases*) case: tm;
      try solve[intros; simpl; by match_case small hd Halliff Decp_fmatch_rec].
    + (*Var case*)
      move=> v' Hdecv/=.
      case: (check_var_case_spec hd small v') => Hvar; last
        by match_case small hd Halliff Decp_fmatch_rec.
      by case: (Halliff (fun x => (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs x.1))
           (remove_all vsymbol_eq_dec (pat_fv x.1) small)))
        (fun x => (upd_option_iter hd (pat_fv x.1)))) => Hall2;
      [apply ReflectT, Decp_fmatch | reflF].
    + (*Constr case*)
      move=> fs tys tms Hfs. 
      by case: (Halliff (fun x => (union vsymbol_eq_dec (vsyms_in_m m vs (get_constr_smaller small hd m vs fs tys tms x.1))
           (remove_all vsymbol_eq_dec (pat_fv x.1) small)))
        (fun x => (upd_option_iter hd (pat_fv x.1)))) => Hall2;
      [apply ReflectT, Decp_fmatch_constr | reflF].
Qed.


(*TODO: move*)

Lemma omap_some_iff {A B: Type} (f: A -> B) (o: option A) (x: B):
  omap f o = Some x ->
  exists y, o = Some y /\ f y = x.
Proof.
  rewrite /omap. case: o => [z/= [] <- |//].
  by exists z.
Qed.

(* Lemma group_indices_adt_spec m vs mp syms
  (* (Hin: In (m, vs, mp) (map_bindings (group_indices_adt syms))): *)
  (Hin: map_get (tuple_eq_dec mut_adt_dec (list_eq_dec vty_eq_dec)) 
      (group_indices_adt syms) (m, vs) = Some mp) :
  forall f vars,
    In (f, vars) syms ->
    map_get fpsym_eq_dec mp f = Some (filter (fun i => vty_in_m m vs (snd (List.nth i vars vs_d))) (iota 0 (length vars))).
Proof.
  intros f vars Hinf.
  induction syms as [|[fhd vshd] stl IH]; simpl in *; [contradiction |].
  destruct Hinf as [Heq | Hinf]; [inversion Heq; subst|]; auto.
Admitted. *)
  (*Prove 2 things: for all m1, vs1, f1 <> f, fold is same as base
    and for f, we get property we want AND f does not occur in base,
    so we are fine (we do need something about nodups I think*)
(*   - 

    exists (idxs: list nat),
      map_get fpsym_eq_dec mp f = Some idxs /\
      forall (i : nat), 0 <= i < length vars -> In i idxs <-> vty_in_m m vs (snd (List.nth i vars vs_d)).
Proof.
  intros f vars Hinf.
  induction syms as [|[fhd vshd] stl IH]; simpl in *; [contradiction |].
  destruct Hinf as [Heq | Hinf]; [inversion Heq; subst|].
  -  *)
    (*Prove something like:
      the fold_right updates all things for THIS funsym correctly (no matter base map), otherwise
      if this funsym is not


  (*Better - do a concat and add_alll - is there a better way to update?
  (*For inner, we want lemma with something like:
    maybe prove: for all base maps, 
      we have the property for funsyms 


      2 cases:
      either (m, vs) not in recursive one or it is, and it is mp1

    1. In this case, argue that everyt

    map_get ... (m, vs) =
      map_

(*Maybe compute differently: 
  just concat all lists, and zip together, have add procedure that looks up
  and adds - add set abstraction.
  Then have add_all function
  problem is there is some aggregation - can't go unit-by-unit
  what should we prove?


  
  Search map_get Some.


  Print group_indices_adt.*)*)*)*)
Print sn.
Search sn.
Set Bullet Behavior "Strict Subproofs".

(*TODO: move*)
Lemma Forall_impl_in  {A: Type} {P Q: A -> Prop} {l}:
(forall x, In x l -> P x -> Q x) ->
Forall P l ->
Forall Q l.
Proof.
  rewrite !Forall_forall; intros; auto.
Qed.


Lemma NoDup_map_typerror {A B C: Type} (f1: A -> C) (f2: B -> C) (l1: list A) (l2: list B)
          (x1: A) (x2: B) (Hnodup: NoDup (List.map f1 l1 ++ List.map f2 l2)):
          In x1 l1 -> In x2 l2 -> f1 x1 = f2 x2 -> False.
Proof.
  induction l1; simpl; auto.
  simpl in Hnodup. inversion Hnodup; subst.
  intros [Heq | Hin]; subst; auto.
  intros Hin2 Heq. apply H1. rewrite in_app_iff. right. rewrite in_map_iff.
  exists x2. auto.
Qed.
(* 
Lemma NoDup_map_typerror' {A B C D: Type} (f1: A -> C) (f2: B -> C) (f3: C -> D) (l1: list A) (l2: list B)
          (x1: A) (x2: B) (Hnodup: NoDup (List.map f3 (List.map f1 l1 ++ List.map f2 l2))):
          In x1 l1 -> In x2 l2 -> f1 x1 = f2 x2 -> False.
Proof.
  induction l1; simpl; auto.
  simpl in Hnodup. inversion Hnodup; subst.
  intros [Heq | Hin]; subst; auto.
  intros Hin2 Heq. apply H1. rewrite in_app_iff. right. rewrite in_map_iff.
  exists x2. auto.
Qed. *)

Lemma all_dec_iff (fs: list fn) (ps: list pn) (idxs: list nat)
      (Hlen: length idxs = length fs + length ps) m vs t f
      (Hwf1: Forall fn_wf fs) (Hwf2: Forall pn_wf ps)
      (Hn: NoDup (List.map sn_sym (List.map fn_sn fs ++ List.map pn_sn ps))):
      (forall small hd,
        decrease_fun fs ps small hd m vs t <->
        (forall (i: nat) (Hi: (i < (length fs + length ps)%coq_nat)%coq_nat),
          let s := (List.nth i (List.map fn_sn fs ++ List.map pn_sn ps) sn_d) in
          decrease_fun_prop (sn_sym s) (sn_idx s) small hd m vs t)) /\
      (forall small hd,
        decrease_pred fs ps small hd m vs f <->
        (forall (i: nat) (Hi: (i < (length fs + length ps)%coq_nat)%coq_nat),
          let s := (List.nth i (List.map fn_sn fs ++ List.map pn_sn ps) sn_d) in
          decrease_pred_prop (sn_sym s) (sn_idx s)
          small hd m vs f)).
Proof.
  revert t f.
  apply term_formula_ind; try solve[intros; split; intros; constructor].
  - (*Tfun - interesting case*)
    intros f1 l l1 Hall small hd. split.
    + intros Hdec i Hi. inversion Hdec; subst.
      * (*Recursive case - only if s = fs *)
        destruct (@In_nth _  fs f_decl fn_d ltac:(assumption)) as [j [Hj Hfdecl]].
        assert (Hsymeq: f_sym (fn_sym (List.nth j fs fn_d)) = (sn_sym (List.nth j fs fn_d))).
        { subst. rewrite Forall_forall in Hwf1. apply Hwf1. assumption. }
        set (s:=List.nth i (List.map fn_sn fs ++ List.map pn_sn ps) sn_d). simpl.
        destruct (sn_eqb_spec s (fn_sn f_decl)) as [Hseq | Hsneq]; subst.
       (*  destruct (fpsym_eqb_spec (sn_sym s) (f_sym (fn_sym (List.nth j fs fn_d)))) as [Hseq | Hsneq]. *)
       (*  destruct (Nat.eqb_spec i j) as [Hij | Hij]; subst. *)
        -- simpl. apply Decp_fun_in with (x:=x); auto; try solve[
           subst s; rewrite <- ?nth_eq, Hseq, ?Hsymeq; auto].
           (*TODO: avoid repeat*)
           revert Hall H11. rewrite !Forall_forall. intros. apply Hall; auto.
        -- (*Other case, just non-recursive*) apply Decp_fun_notin.
          ++ intro C. rewrite Hsymeq in C.
            (*Need to reason about uniqueness*)
            apply Hsneq. eapply NoDup_map_in. apply Hn. all: auto.
            ** subst s. apply nth_In; rewrite -> app_length, !map_length; auto.
            ** apply in_app_iff. left. rewrite in_map_iff. exists (List.nth j fs fn_d). auto.
          ++ intros tm Hintm. revert H11 Hall. rewrite !Forall_forall; intros; apply Hall; auto.
      * (*f1 not in list*)
        simpl. apply Decp_fun_notin.
        -- intro C. assert (Hilt: (i < length fs)%coq_nat). {
            (*Has to be in 1st portion because no funsym and predsym can agree*)
            destruct (Nat.lt_ge_cases i (length fs)) as [Hilt | Higt]; auto.
            rewrite app_nth2 in C; [| rewrite map_length; lia].
            rewrite map_length in C.
            
            eapply NoDup_map_typerror in C; [contradiction | | | ].
            Search NoDup List.map.
            assert (NoDup_map_typerror {A B C: Type} (f1: A -> C) (f2: B -> C) (l1: list A) (l2: list B)
              (x1: A) (x2: B) (Hnodup: NoDup (List.map f1 l1 ++ List.map f2 l2)) ->
              In x1 l1 -> In x2 l2 -> f1 x1 = f2 x2 -> False).

 
            assert (Hicase: (i < length fs)%coq_nat \/ (length fs <= i < (length fs + length ps)%coq_nat)%coq_nat).
              Search (?x < ?y)%coq_nat "\/".
            

Nat.lt_ge_cases: forall n m : nat, (n < m)%coq_nat \/ (m <= n)%coq_nat
          


 rewrite app_nth1 in C.
          2: { 


 intro C. apply H5. rewrite in_map_iff. exists (List.nth i fs fn_d).
          split; [|apply nth_In
            


 exists (List.nth i (List.map fn_sn fs ++ List.map pn_sn ps) sn_d).  exists (f_sym f1).



 rewrite <- C in H5. subst f1.

 apply nth_In.
            Search NoDup List.map.
            
            (*Ugh, anyway need to reason about uniqueness*)
            

 inversion C.

 [rewrite -> Hsneq; auto|].
          apply Hall.


 apply Forall_impl_in. intros tm Hintm Hall. apply Hall; auto.
            rewrite Forall_forall in H11. auto.
            


            subst s. rewrite -> Hseq, Hsymeq. auto.
            subst s. rewrite <- nth_eq. rewrite -> Hseq. auto.
            subst s. rewrite -> Hseq, Hsymeq. auto. 


 symmetry. apply Hsymeq.


 (*All but 1 are trivial*)
          try solve[ subst s;
          rewrite app_nth1; [|rewrite map_length; auto];
          rewrite -> map_nth_inbound with (d2:=fn_d); auto;
          try rewrite <- nth_eq;
          try rewrite Hsymeq; auto]. subst s.
          revert Hall. apply Forall_impl_in. intros tm Hintm Hall. apply Hall; auto.
          rewrite Forall_forall in H11. auto.
        -- (*Other case, just non-recursive*) apply Decp_fun_notin.
          apply Hall.



          rewrite app_nth1; [|rewrite map_length; auto];
          rewrite -> map_nth_inbound with (d2:=fn_d); auto. auto.
          ++ rewrite app_nth1; [|rewrite map_length; auto].
            rewrite -> map_nth_inbound with (d2:=fn_d); auto.
            rewrite Forall_forall in Hwf1.
            symmetry. apply Hwf1. assumption.
          ++ rewrite app_nth1; [| rewrite map_length; auto].
            rewrite <- nth_eq, map_nth_inbound with (d2:=fn_d); auto.
          ++ rewrite app_nth1; [| rewrite map_length; auto].
            rewrite -> map_nth_inbound with (d2:=fn_d); auto.
            


  assumption.
            Search List.nth nth.
            specialize (Hwf1 (List.nth j fs fn_d) ltac:(assumption)).
            unfold fn_wf in Hwf1.

            Search fn_sym sn_sym.

 reflexivity.
          rewrite nth_app1.
        simpl. apply Decp_fun_in with (x:=x); auto.
        -- 



 Print decrease_fun_prop.
      intros i Hi. simpl. 

split.
    

  - intros; split; intros; constructor.
  - intros; split; intros; constructor. 
    + intros i Hi. constructor.
    + constructor.


 inversion Hdec. inversion Hdec; subst.

(*Don't bother with rest, only one we need induction for*)
(*The theorem we want to prove*)
(*Not iff because many lists could satisfy the condition, but this
  function only returns one*)

Lemma nat_min_id' n m: n = m -> Nat.min n m = n.
Proof. intros; subst; apply Nat.min_id. Qed.

Theorem check_termination_some (l: list funpred_def) m params vs idxs
  (Hallval: Forall (funpred_def_valid_type gamma) l): (*Overkill, only need that map snd vars = s_args f*)
  (*TODO: something about nodups*)
  check_termination l = Some (m, params, vs, idxs) ->
  funpred_def_term gamma l m params vs idxs.
Proof.
  (*TODO: ssreflect?*)
  rewrite /check_termination /funpred_def_term.
  case: (nullP l) => [//| Hnull].
  set (t := (split_funpred_defs l)).
  set (funsyms := List.map (fun x : funsym * seq vsymbol * term => f_sym (x.1.1)) t.1).
  set (predsyms := List.map (fun x : predsym * seq vsymbol * formula =>p_sym (x.1.1)) t.2).
  case Hfind: (find_eq  (fun (x : fpsym) => s_params x) (funsyms ++ predsyms)) => [params1 | //].
  move: Hfind => /eqP /find_eq_spec [Hnull' Hparams].
  case Hdec: (check_decrease_fun t.1 t.2) => [[[m1 vs1] idxs1] | //].
  case: (Nat.eqb_spec (length vs1) (length (m_params m1))) => [Hlenvs |//].
  case m_in: (mut_in_ctx m1 gamma) => //. move=> [] Hm Hparams1 Hvs Hidxs; subst.
  (*Simplify the [check_decrease_fun] to prove our coals*)
  rewrite /check_decrease_fun in Hdec.
  (* apply omap_some_iff in Hdec.
  case: Hdec => [[[[m2 vs2] mp2] idxs2] [Hfind]] [] Hm Hvs Hidx; subst. *)
  apply list_find_some in Hdec.
  case: Hdec => [Hinbind Hall].
  apply list_collect_some_iff in Hall.
  setoid_rewrite map_app in Hall.
  setoid_rewrite map_map in Hall.
  rewrite /= in Hall.
  subst funsyms predsyms.
  set (funsyms := List.map (fun x : funsym * seq vsymbol * term => f_sym (x.1.1)) t.1) in *.
  set (predsyms := List.map (fun x : predsym * seq vsymbol * formula =>p_sym (x.1.1)) t.2) in *.
  case : Hall => [Hmap Hall].
  have Hl : length idxs = length l.
  {
    rewrite <- map_length with (f:=Some). rewrite Hmap !map_length app_length.
    rewrite /funsyms/predsyms !map_length /t.
    by apply split_funpred_defs_length.
  }
  (*For this direction, doesn't actually matter that [get_adts_present] as present ADTs*)
  




(* 
In (m, vs, mp2)
            (map_bindings
               (group_indices_adt
                  (List.map (fun x : funsym * seq vsymbol * term => (x.1.1, x.1.2)) t.1 ++
                   List.map (fun x : predsym * seq vsymbol * formula => (x.1.1, x.1.2)) t.2)))


  rewrite -> map_bindings_iff with (eq_dec := tuple_eq_dec mut_adt_dec (list_eq_dec vty_eq_dec)) in Hinbind.
  Search map_get Some.

  Search map_bindings. *)

  assert (fd_d: funpred_def). {
    destruct l as [| hd tl]; [contradiction | exact hd].
  } 
  pose proof (split_funpred_defs_length l) as Hlenadd.
  assert (Hargsvars: forall i (Hi: (i < length l)%coq_nat),
      s_args (List.nth i (funsyms ++ predsyms) id_fs) = (List.map snd (List.nth i
         (List.map (fun x => x.1.2) t.1 ++ List.map (fun x => x.1.2) t.2) nil))).
  {
    intros i Hi.
    unfold funsyms, predsyms, t. 
    destruct (Nat.lt_ge_cases i (length (split_funpred_defs l).1)) as [Hi1 | Hi2].
    - rewrite !app_nth1; try rewrite !map_length; auto.
      rewrite -> !map_nth_inbound with (d2:=(id_fs, nil, tm_d)); auto.
      revert Hallval. rewrite Forall_forall; intros.
      set (x:= (List.nth i (split_funpred_defs l).1 (id_fs, [::], tm_d))).
      unfold funpred_def_valid_type in Hallval.
      specialize (Hallval (fun_def x.1.1 x.1.2 x.2)). symmetry. apply Hallval.
      apply split_funpred_defs_in_l. unfold x.
      apply nth_In. auto.
    - rewrite !app_nth2; try rewrite !map_length; auto.
      rewrite -> !map_nth_inbound with (d2:=(id_ps, nil, Ftrue)); try lia.
      revert Hallval. rewrite Forall_forall; intros.
      set (x:= (List.nth (i - Datatypes.length (split_funpred_defs l).1)%coq_nat (split_funpred_defs l).2
        (id_ps, [::], Ftrue))).
      unfold funpred_def_valid_type in Hallval.
      specialize (Hallval (pred_def x.1.1 x.1.2 x.2)). symmetry. apply Hallval.
      apply split_funpred_defs_in_l. unfold x.
      apply nth_In. lia.
    }

    assert (Hith: forall i, (i < length l)%coq_nat ->
      check_decrease_idx check_decrease_fun_aux (List.map (fun x => (snd (fst x), (snd x))) (fst t))
        m vs (List.nth i idxs 0) (List.nth i (funsyms ++ predsyms) id_sym) /\
      check_decrease_idx check_decrease_pred_aux (List.map (fun x => (snd (fst x), (snd x))) (snd t))
        m vs (List.nth i idxs 0) (List.nth i (funsyms ++ predsyms) id_sym) /\
      vty_in_m m vs
        (List.nth (List.nth i idxs 0) (s_args (List.nth i (funsyms ++ predsyms) id_sym)) vty_int) /\
      (List.nth i idxs 0 < Datatypes.length (s_args (List.nth i (funsyms ++ predsyms)%list id_fs)))%coq_nat).
    {
      intros i Hi.
      apply (f_equal (fun x => List.nth i x None)) in Hmap.
      revert Hmap. rewrite -> !map_nth_inbound with (d2:=0); [| lia].
      rewrite -> !map_nth_inbound with (d2:=id_sym).
      2 : { unfold funsyms, predsyms, t; rewrite -> !app_length, !map_length. lia. }
      intros Hsome; symmetry in Hsome.
      apply find_some in Hsome.
      destruct Hsome as [Hinidxf Hdectrue].
      rewrite in_filter in Hinidxf.
      destruct Hinidxf as [Hty Hiota].
      bool_hyps. split_all=>//.
      revert Hiota => /inP. (*ugh - only ssreflect*)
      rewrite mem_iota.
      intros. apply /ltP. auto.
    }

    (*Corollaries of [Hargsvars]*)
    assert (Hargsvars1: forall i, (i < length (split_funpred_defs l).1)%coq_nat ->
      s_args (List.nth i funsyms id_fs) =
         List.map snd (snd (fst (List.nth i (split_funpred_defs l).1 (id_fs, nil, tm_d))))).
    {
      intros i Hi. specialize (Hargsvars i ltac:(lia)).
      rewrite !app_nth1 in Hargsvars; [| rewrite map_length; unfold t | unfold funsyms, t;
        rewrite map_length]; try lia.
      rewrite Hargsvars. rewrite -> map_nth_inbound with (d2:=(id_fs, [::], tm_d)); auto.
    }
    assert (Hargsvars2: forall i, (i < length (split_funpred_defs l).2)%coq_nat ->
      s_args (List.nth i predsyms id_ps) =
         List.map snd (snd (fst (List.nth i (split_funpred_defs l).2 (id_ps, nil, Ftrue))))).
    {
      intros i Hi. specialize (Hargsvars (length (split_funpred_defs l).1 + i)%coq_nat ltac:(lia)).
      rewrite !app_nth2 in Hargsvars; [| rewrite map_length; unfold t | unfold funsyms, t;
        rewrite map_length]; try lia.
      unfold funsyms, predsyms, t in Hargsvars.
      rewrite !map_length in Hargsvars.
      (*TODO: separate lemma*)
      assert (Hnmn: forall n m, ((n+m)%coq_nat -n)%coq_nat = m) by (intros; lia).
      rewrite !Hnmn in Hargsvars.
      rewrite -> !map_nth_inbound with (d2:= (id_ps, [::], Ftrue)) in Hargsvars; auto.
      rewrite <- Hargsvars.
      unfold predsyms, t.
      rewrite -> map_nth_inbound with (d2:= (id_ps, [::], Ftrue)); auto.
    }

    
  split_all =>//.
  - intros i Hi. rewrite Hl in Hi.
    apply Hith. assumption.
  - intros f. rewrite -> funpred_defs_to_sns_in_fst by auto.
    intros [i [Hi Hf]]. rewrite Hf. simpl.
    assert (Hi': (i < Datatypes.length l)%coq_nat) by lia.
    specialize (Hith i Hi').
    destruct Hith as [_ [_ [Hith Hibound]]].
    rewrite app_nth1 in Hith, Hibound; [| unfold funsyms, t; rewrite map_length; assumption].
    rewrite Hargsvars1 in Hith, Hibound; [| auto].
    rewrite -> map_nth_inbound with (d2:=vs_d) in Hith; [| rewrite map_length in Hibound];
    assumption.
  - (*Similar to previous*)
    intros p. rewrite -> funpred_defs_to_sns_in_snd by auto.
    intros [i [Hi Hp]]. rewrite Hp. simpl.
    rewrite -> map_length, combine_length, nat_min_id' by (rewrite firstn_length; lia).
    set (i':=(length (split_funpred_defs l).1 + i)%coq_nat).
    assert (Hi': (i' < Datatypes.length l)%coq_nat) by lia.
    specialize (Hith i' Hi').
    destruct Hith as [_ [_ [Hith Hibound]]].
    rewrite app_nth2 in Hith, Hibound; [|unfold funsyms, t; rewrite map_length; lia].
    unfold i' at 2, funsyms, t in Hibound.
    unfold i' at 2, funsyms, t in Hith.
    rewrite -> map_length in Hibound, Hith.
    (*TODO: separate lemma*)
    assert (Hnmn: forall n m, ((n+m)%coq_nat -n)%coq_nat = m) by (intros; lia).
    rewrite Hnmn in Hibound, Hith.
    rewrite Hargsvars2 in Hith, Hibound; auto.
    erewrite -> map_nth_inbound in Hith; [apply Hith|].
    rewrite map_length in Hibound; auto.
  - (*Prove params are the same*)
    intros f. rewrite funpred_defs_to_sns_in_fst; simpl; auto.
    intros [i [Hi Hf]]; rewrite Hf; simpl.
    apply Hparams. apply /inP. rewrite in_app_iff; left.
    unfold funsyms; rewrite in_map_iff.
    exists (List.nth i (split_funpred_defs l).1 (id_fs, [::], tm_d)).
    split; auto. unfold t. apply nth_In; auto.
  - intros p. rewrite funpred_defs_to_sns_in_snd; simpl; auto.
    intros [i [Hi Hf]]; rewrite Hf; simpl.
    apply Hparams. apply /inP. rewrite in_app_iff; right.
    unfold funsyms; rewrite in_map_iff.
    exists (List.nth i (split_funpred_defs l).2 (id_ps, [::], Ftrue)).
    split; auto. unfold t. apply nth_In; auto.
  - rewrite Forall_forall.
    intros f1. rewrite funpred_defs_to_sns_in_fst; [| auto].
    intros [i [Hi Hf1]].

    simpl in Hf1; subst; simpl. Check decrease_pred_prop.


     /\

    (*So what is the idea: 
      decrease_fun takes in list of fn, pn, checks to see if, in given term,
      all f in fn and all p in pn decrease on their corresponding index

      decrease_fun_prop takes in single fpsym and sees if all ocurrences of this
      fpsym in given term decrease on given index

      2 directions: 
      1. If for all f in fs and p in ps, we have decrease_fun/pred_prop f (idx f) t,
      then we have decrease_fun fs ps t
      2. The converse - need to go term by term

      so theorem is:
      for all fs ps f, In f fs ->
      decrease_fun fs ps 
    

 Search funpred_defs_to_sns.



 Print check_decrease_idx.


    Lemma (f: fpsym) (l: list (list vsymbol * term)) (is: list nat)

     check_decrease_fun_aux f





(*Now, only need to prove [decrease_fun] goal*) Check decrease_fun.


    (*Know: forall i, i < length l ->
      check_decrease_idx funs ... (all terms in t.1) m vs (List.nth i idxs) (List.nth i (funsyms++ predsyms))
      and likewise for preds

      want to prove: for all fn in t.1, decresae_fun (all fs) (all ps) (sn_idx f) m vs (fn_body f)

- move => f. rewrite funpred_defs_to_sns_in_fst =>//=.
    move => [i [Hi Hf]]; rewrite Hf /=.
    apply Hparams. apply /inP. rewrite in_app_iff; left.
    rewrite /funsyms in_map_iff.
    exists (List.nth i (split_funpred_defs l).1 (id_fs, [::], tm_d)).
    split=>//. rewrite /t. by apply nth_In.



 lia.
    unfold  in Hibound.
    rewr
    
    
    rewrite Hargsvars1 in Hith, Hibound; [| auto].
    rewrite -> map_nth_inbound with (d2:=vs_d) in Hith; [| rewrite map_length in Hibound];
    assumption.



    rewrite app_nth1 in Hibound; [| unfold funsyms, t; rewrite map_length; assumption].
    assumption.
    rewrite -> map_nth_inbound  with(d2:=(id_fs, nil, tm_d)) in Hith; solve[auto].

    rewrite Hargsvars.
    
    Unshelve.
    (*TODO: lenght*)
    
    


    Search List.nth app. 
    



    apply Hith.
    

 Search funpred_defs_to_sns.

 (*TODO: maybe dont need Hargsvars?*)
    (* rewrite (Hargsvars i Hi). rewrite !map_length. *)
    (*Use Hmap to get info about idxs*)
    apply (f_equal (fun x => List.nth i x None)) in Hmap.
    revert Hmap. rewrite -> !map_nth_inbound with (d2:=0); [| lia].
    rewrite -> !map_nth_inbound with (d2:=id_sym).
    2 : { unfold funsyms, predsyms, t; rewrite -> !app_length, !map_length. lia. }
    (* destruct (map_get fpsym_eq_dec mp2 (List.nth i (funsyms ++ predsyms)%list id_sym)) as [idxf|] eqn : Hgetf;
    [| discriminate]. *)
    intros Hsome; symmetry in Hsome.
    apply find_some in Hsome.
    destruct Hsome as [Hinidxf Hdectrue].
    (*Everything up to here should be separate lemma*)
    (*Only "in" predicate is important right now - but other is important later -
      can use this proof to show that for all i, have decrease_fun for all i from 0 to length idxs*)
    (*TODO START: use spec assumed*)
    rewrite in_filter in Hinidxf.
    destruct Hinidxf as [Hty Hiota].
    
    
    (*Separate lemma here maybe*)
    revert Hiota => /inP. (*ugh - only ssreflect*)
    rewrite mem_iota.
    intros. apply /ltP. auto.
  - (*Yes,let's do separate lemma above?*)
    Search funpred_defs_to_sns.


    (*Yes, let's keep everything in terms of s_args*)


 simpl.



 Search in_mem In.
    Search iota.


mem_iota:
  forall (m n : nat) (i : Datatypes_nat__canonical__eqtype_Equality),
  (i \in iota m n) = (m <= i < m + n)


    apply group_indices_adt_spec in Hinbind.
    Search group_indices_adt.
   
    Search List.find.


find_some:
  forall [A : Type] (f : A -> bool) (l : seq A) [x : A], List.find f l = Some x -> In x l /\ f x = true
    


 2: rewrite app_length. Unshelve. with (d2:=None); [| lia].
    rerwite -> map_nth_inbound
    rewrite -> !map_nth_inbound with (d2:=nil) in Hmap.


 intros i Hi.
    revert Hallval. rewrite Forall_nth. rewrite Hl in Hi.
    intros Hallval. specialize (Hallval i fd_d Hi).
    unfold funpred_def_valid_type in Hallval.
    



 Print group_indices_adt.
    



 (*Some things we could prove that may be useful (see):
      1. It is the case that for i < length syms,
          check_decrease_idx ... m vs (nth i idxs) (nth i syms)
            for all terms and formulas in l
        (Note: can get from hmap, is hall useful?)
      2. Need to know mp2
         Spec should be:
          for every (funsym, list nat) in mp2,
            suppose (f, vs) is in syms.
            then for every 0 <= i < length (vs), i in idx <-> nth i vs has type m(vs)
      I think these 2 facts should be enough to prove what we need, but see*)

(*TODO: prove - need to know about idxs and where they come from*) admit.
  - (*prove about m*) admit.
  - (*same as before*) admit.
  - move => f. rewrite funpred_defs_to_sns_in_fst =>//=.
    move => [i [Hi Hf]]; rewrite Hf /=.
    apply Hparams. apply /inP. rewrite in_app_iff; left.
    rewrite /funsyms in_map_iff.
    exists (List.nth i (split_funpred_defs l).1 (id_fs, [::], tm_d)).
    split=>//. rewrite /t. by apply nth_In.
  - move => p. rewrite funpred_defs_to_sns_in_snd =>//= => [[i [Hi Hf]]].
    rewrite Hf /=.
    apply Hparams. apply /inP. rewrite in_app_iff; right.
    rewrite /predsyms in_map_iff.
    exists (List.nth i (split_funpred_defs l).2 (id_ps, [::], Ftrue)).
    split=>//. rewrite /t. by apply nth_In.
  - (*These are the big ones*)
    
    (*So the "Hall" part will be useful for that*)
    
    


Theorem check_term_equiv :  
  check_termination l = Some (m, params, vs, is) ->
  funpred_def_term l m params vs is.






 m params vs is


  reflect (check_termination l == Some (
  check_termination l ->
  funpred_def_term_exists gamma l
  .
Proof.
  unfold funpred_def_term_exists, check_termination_prop.
  (*TODO: maybe better way than split - only prove direction we need first*)
  intros [Hnotnil [[params Hparams] Hdecrease]].
  unfold decrease_prop in Hdecrease.
  destruct Hdecrease as [[[m vs] mp] [Hin Hall]].
  exists m. exists params. exists vs.
  (*Now we need to get list of nat*)
  (*Maybe it is better to produce this?*)




(*TODO: instead of bool, maybe should return 
  option (list nat * mut_adt * list vty)
  then fold through, ensure we are matching on single mut*)
Definition decrease_idx_prop {A: Type}
  (check_aux: fpsym -> nat -> list vsymbol -> option vsymbol ->
    mut_adt -> list vty -> A -> Prop)
  (l: list (list vsymbol * A))
  (m: mut_adt) (args: list vty)
  (i: nat) (f: fpsym) : Prop :=
  Forall (fun x => 
    let '(vs, t) := x in
    exists v,
      nth_error vs i = Some v /\
      check_aux f i nil (Some v) m args t
  ) l.

Definition decrease_prop
  (mutfun: list (funsym * list vsymbol * term))
  (mutpred: list (predsym * list vsymbol * formula)) : Prop :=
  let syms_args := (List.map (fun x => (f_sym (fst (fst x)), snd (fst x))) mutfun ++
     List.map (fun x => (p_sym (fst (fst x)), snd (fst x))) mutpred) in
  let mut_map := group_indices_adt syms_args in
  let syms := List.map fst syms_args in 
  
  let tmlist := List.map (fun x => (snd (fst x), (snd x))) mutfun in
  let fmlalist := List.map (fun x => (snd (fst x), (snd x))) mutpred in
  (*For each m(vs), we have map funsym -> list indices*)
  let mut_mapl := map_bindings mut_map in
  exists t, In t mut_mapl /\ 
    let '(mvs, mp) := t in
    let '(m, vs) := mvs in
    (*For every fun/predsym in the list, 
      1. see if the sym appears in mp (if not, return false, there
      is no possible index)
      2. If so, get indices, and find one that works, if any*)
    Forall (fun (f : fpsym) => 
      match (map_get fpsym_eq_dec mp f) with
      | None => false
      | Some l =>
        exists i, In i l /\
          decrease_idx_prop check_decrease_fun_aux tmlist m vs i f /\
          decrease_idx_prop check_decrease_pred_aux fmlalist m vs i f
      end
    ) syms.

Definition check_termination_prop (l: list funpred_def) : Prop :=
  l <> nil /\
  let t := (split_funpred_defs l) in
  let syms := List.map (fun x => f_sym (fst (fst x))) (fst t) ++
    List.map (fun x => p_sym (fst (fst x))) (snd t) in
  (exists params,
    forall x, In x syms -> s_params x = params) /\
  decrease_prop (fst t) (snd t).

(*The theorem we want to prove*)
Theorem check_term_equiv (l: list funpred_def) :
  check_termination_prop l ->
  funpred_def_term_exists gamma l
  .
Proof.
  unfold funpred_def_term_exists, check_termination_prop.
  (*TODO: maybe better way than split - only prove direction we need first*)
  intros [Hnotnil [[params Hparams] Hdecrease]].
  unfold decrease_prop in Hdecrease.
  destruct Hdecrease as [[[m vs] mp] [Hin Hall]].
  exists m. exists params. exists vs.
  (*Now we need to get list of nat*)
  (*Maybe it is better to produce this?*)
  
  


  intros [Hnotnil [[[m vs] mp] [Hin Hall]]].
  exists m. Print funpred_def_term.
  (*TODO: add check for params*)


  



  let fs := fst (funpred_defs_to_sns l is) in
    let ps := snd (funpred_defs_to_sns l is) in



Definition funpred_valid (l: list funpred_def) :=
    ((Forall funpred_def_valid_type l) /\
    funpred_def_term_exists l).



Definition check_decrease_fun 
  (mutfun: list (funsym * (list vsymbol * term)))
  (mutpred: list (predsym * (list vsymbol * formula))) : bool :=
  (*First, build mut map*)
  let syms_args := (List.map (fun x => (f_sym (fst x), fst (snd x))) mutfun ++
     List.map (fun x => (p_sym (fst x), fst (snd x))) mutpred) in
  let mut_map := group_indices_adt syms_args in
  let syms := List.map fst syms_args in 
  
  let tmlist := List.map snd mutfun in
  let fmlalist := List.map snd mutpred in
  (*For each m(vs), we have map funsym -> list indices*)
  let mut_mapl := map_bindings mut_map in
  forallb (fun t => 
    let '(mvs, mp) := t in
    let '(m, vs) := mvs in
    (*For every fun/predsym in the list, 
      1. see if the sym appears in mp (if not, return false, there
      is no possible index)
      2. If so, get indices, and find one that works, if any*)
    forallb (fun (f : fpsym) => 
      match (map_get fpsym_eq_dec mp f) with
      | None => false
      | Some l =>
        List.existsb (fun i =>
          check_decrease_idx check_decrease_fun_aux tmlist m vs i f &&
          check_decrease_idx check_decrease_pred_aux fmlalist m vs i f
        ) l
      end
    ) syms
  ) mut_mapl.

   

(*Check termination for all terms/formulas for a given
  index for a fun or predsym*)
Definition check_decrease_idx {A: Type}
  (check_aux: fpsym -> nat -> list vsymbol -> option vsymbol ->
    mut_adt -> list vty -> A -> bool)
  (l: list (list vsymbol * A))
  (i: nat) (f: fpsym) : bool :=
  forallb (fun x => (*Check given term's termination*)
    let '(vs, t) := x in
    match nth_error vs i with
    | Some v =>
      match (is_vty_adt gamma (snd v)) with
      | Some (m, a, args) =>
          check_aux f i nil (Some v) m args t
      | None => false
      end
    | None => false
    end
  ) l.

Definition check_decrease_fun 
  (mutfun: list (funsym * (list vsymbol * term)))
  (mutpred: list (predsym * (list vsymbol * formula))) : bool :=
  let funsyms := map fst mutfun in
  let predsyms := map fst mutpred in
  let tmlist := map snd mutfun in
  let fmlalist := map snd mutpred in
  (*Check each funsym and each predsym*)
  forallb (fun (f: fpsym) => (*For given funsym*)
    let argslen := length (s_args f) in
    (*If no indices, true (constant symbols)*)
    (argslen =? 0)%nat || List.existsb (fun i => (*Check all terms using index i*)
      check_decrease_idx check_decrease_fun_aux tmlist i f &&
      check_decrease_idx check_decrease_pred_aux fmlalist i f
      ) (iota 0 argslen)
  ) (map f_sym funsyms ++ map p_sym predsyms).




let check_decrease_fun (mut: (lsymbol * ((vsymbol list) * term)) list) : bool =
  (*For each lsymbol in the list, test all terms using each possible index, so that
    we can construct a list which works*)
  (*TODO: do we need decreasing indicies for something? If so, modify*)
  let syms = List.map fst mut in
  let tmlist = List.map snd mut in
  List.for_all (fun (l: lsymbol) ->
      print_endline ("CHECKING: " ^ l.ls_name.id_string); (*For given lsymbol, test all indicies*)
      (*If no indices, true (constant symbols)*)
      let argslen = (IntFuncs.int_length l.ls_args) in
      BigInt.is_zero argslen || 
      List.exists (fun i -> (*Check all terms with index i*)
        print_endline ("AT INDEX: " ^ BigInt.to_string i);
        let b = (List.for_all (fun (vs, t) -> (*Check given term's termination here*)
        print_endline ("CHECK_TERM: " ^ (term_to_string t));
        print_endline ("WITH VARS:" ^ vars_to_string vs);
          assert (List.length (l.ls_args) = List.length vs);
          begin match big_nth vs i with
          | Some v -> print_endline ("WITH HEAD = " ^ v.vs_name.id_string); 
            check_decrease_fun_aux syms (l, i) Svs.empty (Some v) t
          | None -> print_endline ("REACHED A BAD PLACE! with " ^ vars_to_string vs ^ " and idx " ^ BigInt.to_string i); (*impossible through well-formed assumptions*) false
          end) tmlist) in
          print_endline ("RESULT: " ^ Bool.to_string b); b) (IntFuncs.iota_z argslen)) syms


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
      (*match vty_m_adt m vs (snd mvar) with
      | Some _ =>*)
          all (fun x =>
          check_decrease_fun fs ps
          (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x))) 
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
          small)) (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)
          ) pats
      (*| None => false
      end*)
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
      (*match vty_m_adt m vs (snd mvar) with
      | Some _ =>*)
          all (fun x =>
          check_decrease_pred fs ps
          (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x))) 
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
          small)) (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)
          ) pats
      (*| None => false
      end*)
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
(* Ltac not_in_tm_case fs ps t :=
  case: (all (fun (f: fn) => ~~ (funsym_in_tm (fn_sym f) t)) fs &&
    all (fun (p: pn) => ~~ (predsym_in_tm (pn_sym p) t)) ps)
    /(andPP (funsym_in_tmP fs t) (predsym_in_tmP ps t))=>/=;
  [move=> [Hnotf Hnotp]; apply ReflectT; by apply Dec_notin_t |].

Ltac not_in_fmla_case fs ps fm :=
  case: (all (fun (f: fn) => ~~ (funsym_in_fmla (fn_sym f) fm)) fs &&
    all (fun (p: pn) => ~~ (predsym_in_fmla (pn_sym p) fm)) ps)
    /(andPP (funsym_in_fmlaP fs fm) (predsym_in_fmlaP ps fm))=>/=;
  [move=> [Hnotf Hnotp]; apply ReflectT; by apply Dec_notin_f |]. *)

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
Admitted.
(* Proof.
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
          apply Hmvar. by case: H5 => Hcon; [left; apply /eqP | right; apply /inP].
        }
      apply ReflectT. apply Dec_tmatch_rec=>//.
      - move=> [var [[Heq] Hvar]]; subst.
        apply Hmvar. by case: Hvar => Hcon; [left; apply /eqP | right; apply /inP].
      - by apply Dec_notin_t.
    }
    (*case Hadt: (vty_m_adt m vs (snd mvar)) => [a |]/=; last first.
    {
      false_triv_case Hnotin. eapply vty_m_adt_none in Hadt.
      apply Hadt. apply H8. by [].
      apply H6. exists mvar. split=>//. 
      by case: Hmvar => Hcon; [left; apply /eqP | right; apply /inP].
    }*)
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
    (*apply vty_m_adt_some in Hadt. case: Hadt => [a_in mvar_eq].*)
    apply Dec_tmatch => //.
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
          apply Hmvar. by case: H5 => Hcon; [left; apply /eqP | right; apply /inP].
        }
      apply ReflectT. apply Dec_fmatch_rec=>//.
      - move=> [var [[Heq] Hvar]]; subst.
        apply Hmvar. by case: Hvar => Hcon; [left; apply /eqP | right; apply /inP].
      - by apply Dec_notin_t.
    }
    (*case Hadt: (vty_m_adt m vs (snd mvar)) => [a |]/=; last first.
    {
      false_triv_case Hnotin. eapply vty_m_adt_none in Hadt.
      apply Hadt. apply H8. by [].
      apply H6. exists mvar. split=>//. 
      by case: Hmvar => Hcon; [left; apply /eqP | right; apply /inP].
    }*)
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
    (*apply vty_m_adt_some in Hadt. case: Hadt => [a_in mvar_eq].*)
    apply Dec_fmatch =>//.
    by case: Hmvar => Hcon; [left; apply /eqP | right; apply /inP].
Qed. *)

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