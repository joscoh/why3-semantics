(*Test for induction - we define natural numbers and prove that
  addition is commutative*)

From Proofs.proofsystem Require Import Tactics.
From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

Module InductionTest.

Local Open Scope string_scope.

(*First, define nat type*)
Definition nat_ts : typesym := mk_ts "nat" nil.
Definition wnat : vty := vty_cons nat_ts nil.
Definition O_fs : funsym := constr_noty "O" nil wnat 2.
Definition S_fs: funsym := constr_noty "S" [wnat] wnat 2.
Definition wnat_adt : alg_datatype := alg_def nat_ts
  (list_to_ne_list [O_fs; S_fs] erefl).
Definition wnat_mut : mut_adt := mk_mut [wnat_adt] nil erefl.

Definition O : term := Tfun O_fs nil nil.
Definition S (t: term) : term := Tfun S_fs nil [t].

(*Function definition*)
Definition n : vsymbol := ("n", wnat).
Definition m: vsymbol := ("m", wnat).
Definition n': vsymbol := ("n'", wnat).
Definition add_fs : funsym := funsym_noconstr_noty "add" [wnat; wnat] wnat.
Definition add (t1 t2: term) := Tfun add_fs nil [t1; t2].
Definition add_def : funpred_def :=
  fun_def add_fs [n; m] 
  (Tmatch (Tvar n) wnat
    [(Pconstr O_fs nil nil, Tvar m); (*O -> m*)
     (Pconstr S_fs nil [Pvar n'], S (add (Tvar n') (Tvar m))) (*S n' -> S (add n' m)*)
    ]).

Definition induction_theory : theory :=
  rev [
    tdef (datatype_def wnat_mut);
    tdef (recursive_def [add_def]);
    (*We need two lemmas*)
    tprop Plemma "add_0_r" (fforalls [n]
      (Feq wnat (add (Tvar n) O) (Tvar n)));
    tprop Plemma "plus_n_Sm" (fforalls [n; m]
      (Feq wnat (S (add (Tvar n) (Tvar m)))
        (add (Tvar n) (S (Tvar m)))));
    tprop Pgoal "add_comm" (fforalls [n; m]
      (Feq wnat (add (Tvar n) (Tvar m))
        (add (Tvar m) (Tvar n))))
  ].

Lemma S_eq: forall t,
Tfun S_fs nil [t] = S t.
Proof.
  reflexivity.
Qed.

Lemma add_eq: forall t1 t2,
  Tfun add_fs nil [t1; t2] = add t1 t2.
Proof.
  reflexivity.
Qed.

Definition n_ : term := (t_constsym "n" wnat).
Definition m_ : term := (t_constsym "m" wnat).

Lemma n_eq_: Tfun (const_noconstr "n" wnat) nil nil = n_.
Proof.
  reflexivity.
Qed.

Lemma m_eq_ : Tfun (const_noconstr "m" wnat) nil nil = m_.
reflexivity. Qed.

Ltac extra_simpl ::= fold wnat; fold n_; fold m_; 
  try rewrite n_eq_; try rewrite m_eq_; 
  try fold O; try rewrite !S_eq; try rewrite !add_eq.

Lemma induction_theory_typed : typed_theory induction_theory.
Proof.
  check_theory.
Qed.
(* 
Lemma induction_theory_valid : valid_theory induction_theory.
Proof.
  simpl. split_all; auto.
  - (*Prove "add_0_r"*)
    wstart.
    winduction.
    + wunfold add_fs. wsimpl_match. wreflexivity.
    + wintros "n" "IH".
      wunfold add_fs.
      wsimpl_match.
      wrewrite "IH".
      wreflexivity.
  - (*Prove "plus_n_Sm"*)
    wstart.
    winduction.
    + wintros "m".
      wunfold add_fs.
      wsimpl_match.
      wreflexivity.
    + wintros "n" "IH" "m".
      wunfold add_fs.
      wsimpl_match.
      wrewrite["IH" m_].
      wreflexivity.
  - (*And the main theorem*)
    wstart.
    winduction.
    + wintros "m". wrewrite["add_0_r" m_]. 
      wunfold add_fs. wsimpl_match.
      wreflexivity.
    + wintros "n" "IH" "m".
      wunfold_at add_fs 0%N; wsimpl_match.
      wrewrite["IH" m_].
      wrewrite["plus_n_Sm" m_ n_].
      wreflexivity.
Qed. *)

End InductionTest.

(* 
(*Test for induction - we define natural numbers and prove that
  addition is commutative*)



From Proofs.proofsystem Require Import Tactics.
From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".


Module InductionTest.

Local Open Scope string_scope.

(*First, define nat type*)
Definition nat_ts : typesym := mk_ts "nat" nil.
Definition wnat : vty := vty_cons nat_ts nil.
Definition O_fs : funsym := mk_constr "0" nil nil wnat 2 erefl erefl erefl.
Definition S_fs: funsym := mk_constr "S" nil [wnat] wnat 2 erefl erefl erefl.
Definition wnat_adt : alg_datatype := alg_def nat_ts
  (list_to_ne_list [O_fs; S_fs] erefl).
Definition wnat_mut : mut_adt := mk_mut [wnat_adt] nil erefl.

Definition O : term := Tfun O_fs nil nil.
Definition S (t: term) : term := Tfun S_fs nil [t].

(*Function definition*)
Definition n : vsymbol := ("n", wnat).
Definition m: vsymbol := ("m", wnat).
Definition n': vsymbol := ("n'", wnat).
Definition add_fs : funsym := mk_noconstr "add" nil [wnat; wnat] wnat erefl erefl erefl.
Definition add (t1 t2: term) := Tfun add_fs nil [t1; t2].
Definition add_def : funpred_def :=
  fun_def add_fs [n; m] 
  (Tmatch (Tvar n) wnat
    [(Pconstr O_fs nil nil, Tvar m); (*O -> m*)
     (Pconstr S_fs nil [Pvar n'], S (add (Tvar n') (Tvar m))) (*S n' -> S (add n' m)*)
    ]).

Definition induction_theory : theory :=
  rev [
    tdef (datatype_def wnat_mut);
    tdef (recursive_def [add_def]);
    (*We need two lemmas*)
    tprop Plemma "add_0_r" (fforalls [n]
      (Feq wnat (add (Tvar n) O) (Tvar n)));
    tprop Plemma "plus_n_Sm" (fforalls [n; m]
      (Feq wnat (S (add (Tvar n) (Tvar m)))
        (add (Tvar n) (S (Tvar m)))));
    tprop Pgoal "add_comm" (fforalls [n; m]
      (Feq wnat (add (Tvar n) (Tvar m))
        (add (Tvar m) (Tvar n))))
  ].

Lemma S_eq: forall t,
Tfun S_fs nil [t] = S t.
Proof.
  reflexivity.
Qed.

Lemma add_eq: forall t1 t2,
  Tfun add_fs nil [t1; t2] = add t1 t2.
Proof.
  reflexivity.
Qed.

Definition n_ : term := (t_constsym "n" wnat).
Definition m_ : term := (t_constsym "m" wnat).

Lemma n_eq_: Tfun (const_noconstr "n" wnat) nil nil = n_.
Proof.
  reflexivity.
Qed.

Lemma m_eq_ : Tfun (const_noconstr "m" wnat) nil nil = m_.
reflexivity. Qed.



Ltac extra_simpl ::= fold wnat; fold n_; fold m_; 
  try rewrite n_eq_; try rewrite m_eq_; 
  try fold O; try rewrite !S_eq; try rewrite !add_eq; simpl_gen_strs. (*TODO: bad*)

From Equations Require Import Equations.

Lemma induction_theory_typed : typed_theory induction_theory.
Proof.
  apply /check_typed_theory_correct.
  reflexivity.
Qed.
(* 
Lemma fpsym_eq_dec' (f1 f2: fpsym) : {f1 = f2} + {f1 <> f2}.
Print fpsym.

destruct f1 as [s1 p1 a1 w1 n1]; destruct f2 as [s2 p2 a2 w2 n2].
destruct (string_dec s1 s2); [|right; intro C; injection C; contradiction].
destruct (list_eq_dec typevar_eq_dec p1 p2); [|right; intro C; injection C; contradiction].
destruct (list_eq_dec vty_eq_dec a1 a2);  [|right; intro C; injection C; contradiction].
left. apply fpsym_eq; auto.
Defined.

Lemma funsym_eq_dec' (f1 f2: funsym) : {f1 = f2} + {f1 <> f2}.
Print funsym.

destruct f1 as [s1 r1 c1 n1 w1]; destruct f2 as [s2 r2 c2 n2 w2].
destruct (fpsym_eq_dec' s1 s2); [| right; intro C; injection C; contradiction].
destruct (vty_eq_dec r1 r2); [| right; intro C; injection C; contradiction].
Search bool "dec".
destruct (Bool.bool_dec c1 c2); [| right; intro C; injection C; contradiction].
destruct (Nat.eq_dec n1 n2); [| right; intro C; injection C; contradiction].
left. apply funsym_eq; auto.
Defined.
Print add_fs.

Print funsym.
Print fpsym.
Definition add_fs' : funsym := Build_funsym (Build_fpsym "add" nil [wnat; wnat] Logic.eq_refl Logic.eq_refl) wnat false 0 Logic.eq_refl.
Eval cbn in (funsym_eq_dec add_fs' add_fs').

Lemma add_fs_eq: add_fs' = add_fs. Proof.
  apply funsym_eq; try reflexivity.
  apply fpsym_eq; reflexivity.
Qed.

Definition O_fs': funsym := Build_funsym (Build_fpsym "O" nil nil Logic.eq_refl Logic.eq_refl) wnat true 2 erefl. *)
 (*  -
 vm_compute.
  erewrite bool_irrelevance.

 simpl. f_equal. f_equal. f_equal. f_equal. reflexivity.

Eval cbn in (funsym_eqb add_fs add_fs).
Eval vm_compute in (funsym_eq_dec' add_fs add_fs).
Locate find_args.

Eval cbn in (type_vars vty_int).
Eval vm_compute in (type_vars (vty_cons ts_d [vty_var "a"%string])).
Print find_args.



Definition find_args (l: list vty) : list typevar :=
  aset_to_list (aset_big_union type_vars l). *)

(* Definition list_to_aset' {A: Type} `{countable.Countable A} (l: list A) : aset A :=
  fold_right (fun x acc => aset_union (aset_singleton x) acc) aset_empty l.

Definition aset_singleton' {A: Type} `{countable.Countable A} (x: A) : aset A.
  unfold aset. unfold gmap.gset. constructor.
  destruct (@aset_empty A _ _)  as [y].
  exact (gmap_partial_alter (fun _ => Some tt) x y).
Defined. *)
Require Import Induction.
Ltac winduction :=
  match goal with
  | |- derives (?g, ?d, Fquant Tforall ?x ?f) =>
    eapply D_induction;
    [reflexivity | reflexivity | reflexivity | prove_closed | ];
    simpl; split_all; auto;
    unfold constr_case; simpl_gen_strs; unfold safe_sub_f;  (*Must do before simpl*) simpl;
    try extra_simpl
  | |- _ => fail "Induction requires generalization:
    goal must be in form (Forall (x: a(vs)), f
    where a is a non-mutual ADT"
  end.

Ltac simpl_aset_mem_dec :=
  repeat match goal with
  | |- context [aset_mem_dec ?x ?s] =>
    let z := fresh in
    set (z := aset_mem_dec x s) in *;
    cbv in z;
    unfold z
  end.

Ltac simpl_aset_to_list :=
  repeat match goal with
  |- context [aset_to_list ?s] => let z := fresh in
      set (z := aset_to_list s) in *;
      cbv in z;
      subst z
    end.

(* Definition aset_empty'  {A: Type} `{countable.Countable A} : aset A.
unfold aset. constructor. constructor. apply gmap.GEmpty.
Defined.

Definition aset_union' {A: Type} `{countable.Countable A} (s1 s2: aset A) : aset A.
unfold aset in *.
unfold gmap.gset in *.
destruct s1 as [s1]. destruct s2 as [s2].
constructor. exact (gmap.gmap_merge _ _  _ (stdpp.base.union_with (fun x _ => Some x)) s1 s2).
Defined.

Definition aset_big_union' {A B: Type} `{countable.Countable A} (f: B -> aset A) (l: list B): aset A :=
  fold_right (fun x acc => aset_union' (f x) acc) aset_empty' l.

Lemma aset_big_union_eq {A B: Type} `{countable.Countable A} (f: B -> aset A) (l: list B):
  aset_big_union f l = aset_big_union' f l.
Proof. Admitted. *)


Lemma induction_theory_valid : valid_theory induction_theory.
Proof.
  simpl. split_all; auto.
  - (*Prove "add_0_r"*)
    wstart. eapply D_induction;
    [reflexivity | reflexivity | reflexivity | prove_closed | ];
    simpl; split_all; auto;
    unfold constr_case; simpl_gen_strs; unfold safe_sub_f; simpl_aset_mem_dec.
    + simpl List.filter. simpl combine. unfold List.map. simpl_aset_to_list. simpl.
      Print Ltac wunfold.
      (*TODO: come back and fix this later, not worth doing right now*)
      wunfold add_fs.
    2: {
    repeat match goal with
    | |- 
    simpl List.filter. cbv beta. unfold List.map.
    repeat match goal with
    | |- context [aset_to_list ?s] => let z := fresh in
      set (z := aset_to_list s) in *;
      cbv in z;
      subst z
    end.
    simpl.
    


 cbv beta. cbv iota. simpl List.map.
    match goal with
    | |- context [tm_fv ?s] => let z := fresh in
      set (z := tm_fv s) in *;
      simpl in z;
      subst z
    end.
    simpl a_convert_f.
    simpl.
    simpl in H1. exfalso.
    rewrite aset_big_union_eq in H1. simpl in H1. vm_compute in H1. simpl in H1.
    

 cbv in H1.
    unfold tm_fv in H1. cbn beta.
    set (l:= (List.map Tvar (combine [:: "x0"] (ty_subst_list' (s_params S_fs) [::] (s_args S_fs))))) in *.
    cbv in l. subst l. exfalso.
    rewrite aset_big_union_eq in H1. cbv in H1. simpl in H1.
    Print tm_fv.
    cbn in H1.
    cbv in H1.
    

 simpl.

 set (y:= (aset_to_list
                  (tm_fv
                     (Tfun S_fs [::]
                        (List.map Tvar
                           (combine [:: "x0"] (ty_subst_list' (s_params S_fs) [::] (s_args S_fs)))))))) in *.
    cbv in y. unfold y. 
    set (z:= 

simpl.
    +
 simpl. wunfold add_fs. wreflexivity.
    set (x:= aset_mem_dec n (fmla_fv (Feq wnat (add (Tvar n) O) (Tvar n)))).
    cbv in x. unfold x; simpl.
    match goal with
  |

    simpl aset_mem_dec.



 simpl.
    + unfold constr_case. simpl_gen_strs. simpl. try extra_simpl.
    Print Ltac winduction.
 
      match goal with
      |- context [GenElts.gen_strs ?x ?y] => set (z := GenElts.gen_strs x y) in *
      end.
      cbv in z. unfold z; simpl.
      


 simpl GenElts.gen_strs.
      match goal with
  
      
      set (x:= {|
                         mapset.mapset_car :=
                           base.union
                             (base.union (base.singletonM n tt)
                                (base.union
                                   (base.union (base.singletonM n tt) (base.union base.empty base.empty))
                                   (base.singletonM n tt))) base.empty
                       |}).
    vm_compute in x.
    set (y := aset_to_list x).
    vm_compute in y.
    set (z := map fst y).
    vm_compute in z.
    set (z1 := list_to_aset' z).
    unfold list_to_aset' in z1.
    set (z2 := aset_singleton "n").
    vm_compute in z2.
    set (z2 := aset_union (aset_singleton "n") aset_empty
    vm_compute in z1.
    set (y:= aset_map fst x).
    vm_compute in y.
    simpl in y.
Check strings.String.countable_obligation_1 .
  cbv in y.
    set (y:= (GenElts.gen_strs 0 x)).
    Print GenElts.gen_strs.
    Eval cbn in (aset_map fst x).


 cbn in y.


 unfold x. simpl GenElts.gen_strs at 1.
     vm_compute in x.
  

 simpl GenElts.gen_strs. simpl map. simpl combine.


 simpl safe_sub_f.


 simpl aset_size. simpl.  cbn. simpl. vm_compute aset_size. unfold safe_sub_f. cbn.
      vm_compute aset_mem_dec. simpl.
    set (x:=aset_mem_dec n
            {|
              mapset.mapset_car :=
                {|
                  gmap.gmap_car :=
                    gmap.gmap_dep_merge (base.union_with (fun x : unit => fun=> Some x))
                      (gmap.gmap_dep_ne_omap [eta Some]
                         (gmap.gmap_dep_ne_singleton (countable.encode ("n", wnat))
                            (gmap.gmap_key_encode ("n", wnat)) tt))
                      (gmap.GNodes
                         (gmap.gmap_dep_ne_singleton (countable.encode ("n", wnat))
                            (gmap.gmap_key_encode ("n", wnat)) tt))
                |}
            |}) in *.
    exfalso.
    vm_compute in x.


 unfold aset_mem_dec, gmap.gset_elem_of_dec. cbn.
      About mapset.mapset_elem_of_dec. Print mapset.mapset_elem_of_dec. About base.decide.

simpl mapset.mapset_elem_of_dec.
      unfold mapset.mapset_elem_of_dec. cbn. About base.decide. simpl.

 simpl.
    
    simpl; split_all; auto;
    unfold constr_case; unfold safe_sub_f; simpl;
    try extra_simpl.

 winduction.
    wintros "n". 
    + wunfold add_fs. wsimpl_match. wreflexivity.
    + wintros "n". wintros "IH".
      wunfold add_fs. wsimpl_match. wrewrite "IH". wreflexivity.
  (*Prove "plus_n_Sm"*)
  - wstart.
    winduction.
    + wintros "m".
      wunfold add_fs.
      wsimpl_match.
      wreflexivity.
    + wintros "n" "IH" "m".
      wunfold add_fs.
      (* wrewrite["IH" m_]. *) (*extremely slow*)
      wsimpl_match. wcopy "IH" "IH2". 
      wspecialize_tac2 "IH2" [m_].
      wrewrite "IH2".
      wreflexivity.
  - (*And the main theorem*)
    wstart.
    winduction.
    + wintros "m". wrewrite["add_0_r" m_]. 
      wunfold add_fs. wsimpl_match.
      wreflexivity.
    + wintros "n" "IH" "m".
      wunfold_at add_fs 0%N; wsimpl_match.
      (*Which part is so slow? see*)
      (* wrewrite["IH" m_]. *)
      wcopy "IH" "IH2". 
      wspecialize_tac2 "IH2" [m_].
      wrewrite "IH2".
      (* wrewrite["plus_n_Sm" m_ n_]. TODO: dont use gen_strs maybe?*)
      wcopy "plus_n_Sm" "plus_n_Sm_1".
      wspecialize_tac2 "plus_n_Sm_1" [m_; n_].
      wrewrite "plus_n_Sm_1".
      wreflexivity.
Qed.
(* 
      
 wsimpl_match. wreflexivity.
    + wintros "n" "IH".
      wunfold add_fs.
      wsimpl_match.
      wrewrite "IH".
      wreflexivity.
  - (*Prove "plus_n_Sm"*)
    wstart.
    winduction.
    + wintros "m".
      wunfold add_fs.
      wsimpl_match.
      wreflexivity.
    + wintros "n" "IH" "m".
      wunfold add_fs.
      wsimpl_match.
      wrewrite["IH" m_].
      wreflexivity.
  - (*And the main theorem*)
    wstart.
    winduction.
    + wintros "m". wrewrite["add_0_r" m_]. 
      wunfold add_fs. wsimpl_match.
      wreflexivity.
    + wintros "n" "IH" "m".
      wunfold_at add_fs 0%N; wsimpl_match.
      wrewrite["IH" m_].
      wrewrite["plus_n_Sm" m_ n_].
      wreflexivity.
Qed. *)

End InductionTest.
 *)
