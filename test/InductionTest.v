(*Test for induction - we define natural numbers and prove that
  addition is commutative*)

Require Import Tactics.
From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

Module InductionTest.

Local Open Scope string_scope.

(*First, define nat type*)
Definition nat_ts : typesym := mk_ts "nat" nil.
Definition wnat : vty := vty_cons nat_ts nil.
Definition O_fs : funsym := funsym_noty "O" nil wnat.
Definition S_fs: funsym := funsym_noty "S" [wnat] wnat.
Definition wnat_adt : alg_datatype := alg_def nat_ts
  (list_to_ne_list [O_fs; S_fs] erefl).
Definition wnat_mut : mut_adt := mk_mut [wnat_adt] nil erefl.

Definition O : term := Tfun O_fs nil nil.
Definition S (t: term) : term := Tfun S_fs nil [t].

(*Function definition*)
Definition n : vsymbol := ("n", wnat).
Definition m: vsymbol := ("m", wnat).
Definition n': vsymbol := ("n'", wnat).
Definition add_fs : funsym := funsym_noty "add" [wnat; wnat] wnat.
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

Lemma n_eq_: Tfun (constsym "n" wnat) nil nil = n_.
Proof.
  reflexivity.
Qed.

Lemma m_eq_ : Tfun (constsym "m" wnat) nil nil = m_.
reflexivity. Qed.

Ltac extra_simpl ::= fold wnat; fold n_; fold m_; 
  try rewrite n_eq_; try rewrite m_eq_; 
  try fold O; try rewrite !S_eq; try rewrite !add_eq.

Lemma induction_theory_typed : typed_theory induction_theory.
Proof.
  check_theory.
Qed.

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
Qed.

End InductionTest.

