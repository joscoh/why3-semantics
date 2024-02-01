Require Import ADT.

Lemma unit_eq (x y: unit) : x = y.
Proof.
destruct x; destruct y; reflexivity.
Defined.

Definition unit_dec (x y: unit) : {x = y} + {x <> y} :=
  left (unit_eq x y).

Definition a: string := "a"%string.


Module ListTest.

(*1. Polymorphic lists*)

Definition list_ts : typesym string :=
  Build_typesym _ "list" [a].
Definition nil_constr : constr string unit unit := 
    Build_constr _ _ _ "nil" nil tt.
Definition cons_constr : constr string unit unit :=
    Build_constr _ _ _ "cons" [ty_var a; ty_app list_ts [ty_var a]] tt.

(*TODO: change adt to take in typesym then easier probably
  but still compare by name*)
Definition list_adt : adt string unit unit unit :=
  Build_adt _ _ _ _ "list"%string [a] [nil_constr; cons_constr] tt.
  
Definition list_mut : mut string unit unit unit unit :=
  Build_mut _ _ _ _ _  [list_adt] tt.

Definition bases: unit -> Set := fun u => unit.

(*Can give trivial typesym map because none*)
(*Poly map maps a -> A*)
Definition list_enc (A: Set) : Set :=
  mk_adts string string_dec unit tt unit_dec bases unit unit_dec unit unit_dec 
  unit (fun _ _ => unit) list_mut (fun v => if string_dec v a then A else unit)
  (exist _ list_adt eq_refl).

(*TODO: bool pred*)
Lemma nodup_list: NoDup
(map (a_name string unit unit unit)
   (m_adts string unit unit unit unit list_mut)).
Proof.
simpl. constructor; auto. constructor.
Qed.

Definition nil_enc (A: Set) : list_enc A :=
  constr_rep string string_dec unit tt unit_dec bases tt unit unit_dec unit unit_dec 
  unit (fun _ _ => unit) list_mut nodup_list _ (exist _ list_adt eq_refl)
  nil_constr eq_refl (HL_nil _).


Definition cons_hlist (A: Set) (x: A) (tl: list_enc A):
hlist
     (domain string string_dec unit tt unit_dec bases unit
        unit_dec unit unit_dec unit
        (fun _ _ => unit) list_mut
        (fun v : string =>
         if string_dec v a then A else unit))
     (c_args string unit unit cons_constr).
Proof.
  simpl.
  apply HL_cons.
  - exact x.
  - apply HL_cons.
    + exact tl.
    + apply HL_nil.
Defined.

(*Coq's type inference is not good enough to just give the hlist without
  annotating types*)
Definition cons_enc (A: Set) (x: A) (tl: list_enc A) : list_enc A :=
  constr_rep string string_dec unit tt unit_dec bases tt unit unit_dec unit unit_dec 
  unit (fun _ _ => unit) list_mut nodup_list _ (exist _ list_adt eq_refl)
  cons_constr eq_refl (cons_hlist A x tl).


(*Now we prove the 4 properties of this encoding*)
Lemma cons_inj (A: Set) (x1 x2: A) (t1 t2: list_enc A):
  cons_enc A x1 t1 = cons_enc A x2 t2 ->
  x1 = x2 /\ t1 = t2.
Proof.
  intros Heq.
  apply constr_rep_inj in Heq.
  apply hlist_cons_inj in Heq.
  destruct Heq; subst; split; auto.
  apply hlist_cons_inj in H0. apply H0.
Qed.

Lemma cons_not_nil (A: Set) (x: A) (t: list_enc A):
  nil_enc A <> cons_enc A x t.
Proof.
  (*This one can actually be solved by "discriminate"*)
  apply constr_rep_disjoint.
  intros Heq. discriminate.
Qed.

(*The 2 interesting ones*)
Lemma list_find_constr (A: Set) (x: list_enc A) :
  (exists hd tl, x = cons_enc A hd tl) \/ (x = nil_enc A).
Proof.
  destruct (find_constr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x) 
  as [c [[[c_in b] rec] Hxeq]].
  subst.
  simpl in *.
  assert (Hinc:=c_in).
  rewrite orb_false_r in Hinc.
  apply orb_true_iff in Hinc.
  destruct Hinc.
  - (*nil case*)
    right.
    assert (c = nil_constr). {
      destruct constr_eq_dec; subst; auto. discriminate.
    }
    subst.
    unfold nil_enc, constr_rep. simpl. f_equal.
    + apply bool_irrelevance.
    + apply unit_eq.
    + (*Use funext*)
      repeat(apply functional_extensionality_dep; intros).
      destruct x0. simpl in i. apply (is_false i).
  - (*Cons case*)
    left. assert (c = cons_constr). {
      clear -H.
      destruct constr_eq_dec; auto; discriminate.
    }
    subst.
    unfold build_constr_base, build_constr_base_aux in b; simpl in b.
    exists (fst b).
    exists (rec (exist _ list_adt eq_refl) (exist _ 1 eq_refl)).
    simpl.
    unfold cons_enc, constr_rep. simpl. f_equal.
    + apply bool_irrelevance.
    + unfold args_to_constr_base, args_to_constr_base_aux. simpl.
      destruct b; simpl. destruct p; simpl. destruct u; destruct u0. 
      reflexivity.
    + repeat(apply functional_extensionality_dep; intros).
      unfold args_to_ind_base, args_to_ind_base_aux. simpl.
      destruct x0 as [i Hi]; simpl.
      destruct x as [a a_in].
      simpl in a_in.
      assert (a = list_adt). {
        clear -a_in. destruct (adt_eq_dec); auto.
        apply (is_false a_in).
      }
      subst.
      simpl in Hi.
      destruct i; simpl in *.
      * apply (is_false Hi).
      * destruct i.
        -- assert (Hi = eq_refl). apply bool_irrelevance.
          assert (a_in = eq_refl). apply bool_irrelevance.
          subst.
          symmetry. apply scast_refl_uip.
        -- simpl in Hi. exfalso. apply (is_false Hi).
Qed.

(*Induction principle*)
Lemma list_enc_ind (A: Set) (P: list_enc A -> Prop)
  (Hnil: P (nil_enc A))
  (Hcons: forall (x: A) (tl: list_enc A), P tl -> P (cons_enc A x tl)):
  forall (l: list_enc A), P l.
Proof.
  apply (adt_rep_ind_single) with (P:=P)(bases_inhab:=tt)(adt_names_uniq:=nodup_list);
  [reflexivity|].
  simpl.
  intros.
  subst.
  (*reason by cases: nil or cons*)
  assert (c = nil_constr \/ c = cons_constr). {
    clear -c_in. do 2 (destruct constr_eq_dec; subst; auto).
    discriminate.
  }
  destruct H0; subst c.
  - (*Case 1: c is nil - show huge constr_rep is actuall nil_enc*)
    clear -Hnil.
    assert (c_in = eq_refl) by apply bool_irrelevance. subst.
    apply Hnil.
  - (*Case 2: c is cons. There is only 1 inductive case to consider*)
    assert (c_in = eq_refl) by apply bool_irrelevance. subst.
    apply Hcons.
    specialize (H 1 eq_refl ltac:(simpl; auto)).
    rewrite scast_refl_uip in H.
    exact H.
Qed.

End ListTest.