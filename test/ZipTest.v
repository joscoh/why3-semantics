(*Here we define the function "zip", which is a test that our constructor
  termination check (which allows multiple pattern matches) works*)
From Proofs.proofsystem Require Import Tactics.
From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

Module ZipTest.

Local Open Scope string_scope.

Definition a : vty := vty_var "'a".
Definition b : vty := vty_var "'b".

(*First, define tuple*)
Section Tuple.

Definition prod_ts : typesym := mk_ts "pair" ["'a"; "'b"].
Definition wprod (a b: vty) : vty := vty_cons prod_ts  [a; b].
Definition Pair : funsym :=  funsym_noty "Pair" [a; b] (wprod a b).
Definition wprod_adt : alg_datatype := alg_def prod_ts
  (list_to_ne_list [Pair] erefl).
Definition wprod_mut : mut_adt := mk_mut [wprod_adt] ["'a"; "'b"] erefl.
Definition mk_pair (a b: vty) (t1 t2: term) : term :=
  Tfun Pair [a; b] [t1; t2].
End Tuple.

(*Then, define list -has to be truly polymorphic also*)
Section List.
Definition list_ts : typesym := mk_ts "list" ["'a"].
Definition wlist (a: vty) : vty := vty_cons list_ts [a].
Definition Nil : funsym := funsym_noty "nil" nil (wlist a).
Definition Cons : funsym := funsym_noty "Cons" [a; (wlist a)] (wlist a).
Definition wlist_adt: alg_datatype := alg_def list_ts
  (list_to_ne_list [Nil; Cons] erefl).
Definition wlist_mut: mut_adt := mk_mut [wlist_adt] ["'a"] erefl.
Definition mk_cons (v: vty) (t1 t2: term) : term :=
  Tfun (Cons) [v] [t1; t2]. (*Idea: substitute in v for type variable 'a*)
End List.

(*Now, the zip function*)
(*First, we use variables c and d rather than a and b to make
  it a bit clearer*)
Section ZipFn.

Definition c : vty := vty_var "c".
Definition d : vty := vty_var "d".

Definition tuplist (v1 v2: vty) := wlist (wprod v1 v2).
Definition l1 : vsymbol := ("l1",(wlist c)).
Definition l2 : vsymbol := ("l2",(wlist d)).
Definition zip_fs : funsym := funsym_noty "zip" [(wlist c); (wlist d)]
  (tuplist c d).

(*Define the patterns separately*)
(*Pattern 1: (x :: xs, y :: ys)*)
Definition x : vsymbol := ("x", c).
Definition xs : vsymbol := ("xs", wlist c).
Definition y : vsymbol := ("y", d).
Definition ys : vsymbol := ("ys", wlist d).
Definition patconscons : list pattern :=
  [Pconstr Cons [c] [Pvar x; Pvar xs]; 
  Pconstr Cons [d] [Pvar y; Pvar ys]]. (*TODO: repetition?*)

Definition zip_body : term :=
  (*match (l1, l2) with*)
  Tmatch (Tfun Pair [wlist c; wlist d] (*TODO*)
    [Tvar l1; Tvar l2]) (wprod (wlist c) (wlist d))
    [
      (*| (x :: xs, y :: ys) -> (x, y) :: zip xs ys*)
      (Pconstr Pair [wlist c; wlist d] patconscons,
        mk_cons (wprod c d) (mk_pair c d (Tvar x) (Tvar y)) 
          (Tfun zip_fs [c; d] [Tvar xs; Tvar ys])); (*TODO: nil?*) 
      (*| (_, _ -> nil)*)
      (Pconstr Pair [wlist c; wlist d] [Pwild; Pwild],
        Tfun Nil [wprod c d] nil)
    ].

Definition zip_def : funpred_def :=
  fun_def zip_fs [l1; l2] zip_body.

Definition zip_theory : theory :=
  rev [
    tdef (datatype_def (wprod_mut));
    tdef (datatype_def (wlist_mut));
    tdef (recursive_def [zip_def])
  ].

Lemma zip_theory_typed : typed_theory zip_theory.
Proof. check_theory. Qed.

End ZipFn.
End ZipTest.