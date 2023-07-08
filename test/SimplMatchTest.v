(*Here we have a small test for simplifying
  pattern matches.
  In particular, we define an option type and have the function
  foo (l: option 'a) : int =
  match l with
  | None -> 0
  | Some _ -> 1
  end
  
  and we prove that
  1. foo None = 0
  2. foo (Some x) = 1 for any x

  (we don't do with prop because we didn't implement predicate
    unfolding yet, though we could easily)
  *)
Require Import Tactics.
From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

Module SimplMatchTest.

Local Open Scope string_scope.

Definition zero : term := Tconst (ConstInt 0).
Definition one : term := Tconst (ConstInt 1).

(*First, define option type (we will do for real later)*)
(*TODO: make this nicer*)
Definition avar : typevar := "a".
Definition a : vty := vty_var avar.
Definition option_ts : typesym := mk_ts "option" [avar].
Definition option_ty : vty := vty_cons option_ts [a].
Definition none_fs : funsym := funsym_noty "None" nil option_ty.
Definition some_fs : funsym := funsym_noty "Some" [a] option_ty.
Definition option_adt : alg_datatype := alg_def option_ts 
  (list_to_ne_list [none_fs; some_fs] Logic.eq_refl).
Definition option_mut: mut_adt := mk_mut [option_adt] [avar] erefl.

(*Our function definition*)
Definition isSome : funsym := funsym_noty "isSome" [option_ty] vty_int.
Definition o: vsymbol := ("o", option_ty).
Definition isSome_def : funpred_def :=
  fun_def isSome [o] 
  (Tmatch (Tvar o) option_ty
    [(Pconstr none_fs [a] nil, zero) (*None -> 0*);
     (Pconstr some_fs [a] [Pwild], one) (*Some _ -> 1*)]).

Definition none : term := Tfun none_fs [a] nil.
Definition some y : term := Tfun some_fs [a] [y].

(*Define a variable x of type a*)
Definition x : vsymbol := ("x", a).

Definition simpl_match_theory : theory :=
  rev [
    tdef (datatype_def option_mut);
    tdef (recursive_def [isSome_def]);
    tprop Pgoal "isSome_None" (Feq vty_int
      (Tfun isSome [a] [none]) zero);
    tprop Pgoal "isSome_some" (Fquant Tforall x
      (Feq vty_int (Tfun isSome [a] [some (Tvar x)])
        one))
  ].

Lemma simpl_match_theory_typed : typed_theory simpl_match_theory.
Proof.
  check_theory.
Qed.

Lemma simpl_match_theory_valid: valid_theory simpl_match_theory.
Proof.
  simpl. split_all; auto.
  - exists ["a"].
    wstart.
    wunfold isSome.
    wsimpl_match.
    wreflexivity.
  - exists ["a"].
    wstart.
    wintros "x".
    wunfold isSome.
    wsimpl_match.
    wreflexivity.
Qed.

End SimplMatchTest.