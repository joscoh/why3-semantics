Require Import StdLib.

Module Relations.
Local Open Scope why3_scope.

(*Generic definitions*)
Definition t_ts : typesym := mk_ts "t" nil.
Definition t : vty := vty_cons t_ts nil.

Definition x : vsymbol := ("x", t).
Definition y : vsymbol := ("y", t).
Definition z : vsymbol := ("z", t).

Definition rel : predsym := binpred "rel" t.

Definition EndoRelation : theory :=
  rev [
    tdef (abs_type t_ts);
    tdef (abs_pred rel)
  ].

Definition Reflexive : theory :=
  rev [
    tclone EndoRelation None nil nil nil;
    tprop Paxiom "Refl" <f forall x, rel({x}, {x}) f>
  ].

Definition Irreflexive : theory :=
  rev [
    tclone EndoRelation None nil nil nil;
    tprop Paxiom "Strict" <f forall x, not (rel({x}, {x})) f>
  ].

Definition Transitive : theory :=
  rev [
    tclone EndoRelation None nil nil nil;
    tprop Paxiom "Trans" <f forall x, forall y, forall z, 
      rel ({x}, {y}) -> rel ({y}, {z}) -> rel({x}, {z}) f>
  ].

Definition Symmetric : theory :=
  rev [
    tclone EndoRelation None nil nil nil;
    tprop Paxiom "Symm" <f forall x, forall y,
      rel({x}, {y}) -> rel({y}, {x}) f>
  ].

Definition Asymmetric : theory :=
  rev [
    tclone EndoRelation None nil nil nil;
    tprop Paxiom "Asymm" <f forall x, forall y,
      rel({x}, {y}) -> not (rel({y}, {x})) f>
  ].

Definition Antisymmetric: theory :=
  rev [
    tclone EndoRelation None nil nil nil;
    tprop Paxiom "Antisymm" <f forall x, forall y,
      rel({x}, {y}) -> rel({y}, {x}) -> [t] {x} = {y} f>
  ].

Definition Total : theory :=
  rev [
    tclone EndoRelation None nil nil nil;
    tprop Paxiom "Total" <f forall x, forall y,
      rel({x}, {y}) \/ rel({y}, {x}) f>
  ].

Definition PreOrder : theory :=
  rev [
    tclone Reflexive None nil nil nil;
    tclone Transitive None [(t_ts, t_ts)] nil [(rel, rel)]
  ].

Definition Equivalence : theory :=
  rev [
    tclone PreOrder None nil nil nil;
    tclone Symmetric None [(t_ts, t_ts)] nil [(rel, rel)]
  ].

Definition TotalPreOrder : theory :=
  rev [
    tclone PreOrder None nil nil nil;
    tclone Total None [(t_ts, t_ts)] nil [(rel, rel)]
  ].

Definition PartialOrder : theory :=
  rev [
    tclone PreOrder None nil nil nil;
    tclone Antisymmetric None [(t_ts, t_ts)] nil [(rel, rel)]
  ].

Definition TotalOrder : theory :=
  rev [
    tclone PartialOrder None nil nil nil;
    tclone Total None [(t_ts, t_ts)] nil [(rel, rel)]
  ].

Definition PartialStrictOrder : theory :=
  rev [
    tclone Transitive None nil nil nil;
    tclone Asymmetric None [(t_ts, t_ts)] nil [(rel, rel)]
  ].

Definition TotalStrictOrder : theory :=
  rev [
    tclone PartialStrictOrder None nil nil nil;
    tprop Paxiom "Trichotomy" <f forall x, forall y,
      rel({x}, {y}) \/ rel({y}, {x}) \/ [t] {x} = {y} f>
  ].

(*TODO: need non-ADT defs for predicates for inverse*)
(*Maybe just add other def, interpret as term/formula, easy to show*)
(*Definition Inverse : theory :=
  rev [
    tclone EndoRelation None nil nil;
    tdef ()
  ]*)

(*Inductive relT {A: Type} (R: A -> A -> Prop) : A -> A -> Prop :=
| BaseTrans: forall x y, R x y -> relT R x y
| StepTrans: forall x y z, relT R x y -> R y z -> relT R x z.

Lemma relT_trans: forall {A: Type} (R: A -> A -> Prop) x y z, 
  relT R x y -> relT R y z -> relT R x z.
Proof.
  intros.
  induction H0.
  - eapply StepTrans. apply H. auto.
  eapply StepTrans. apply IHrelT. auto. auto.
Qed.*)

(*Closures*)

Definition relR : predsym := binpred "relR" t.
Definition relT : predsym := binpred "relT" t.
Definition relTR : predsym := binpred "relTR" t.

Definition ReflClosure : theory :=
  rev [
    tclone EndoRelation None nil nil nil;
    tdef <{ 
      inductive relR =
      | "BaseRefl" : forall x, relR({x}, {x})
      | "StepRefl" : forall x, forall y, rel({x}, {y}) -> relR({x}, {y})
      end }>
  ].

Definition TransClosure : theory :=
  rev [
    tclone EndoRelation None nil nil nil;
    tdef <{
      inductive relT =
      | "BaseTrans" : forall x, forall y, rel({x}, {y}) -> relT({x}, {y})
      | "StepTrans" : forall x, forall y, forall z,
        relT({x}, {y}) -> rel({y}, {z}) -> relT({x}, {z})
      end
    }>;
    tprop Plemma "relT_transitive" <f forall x, forall y, forall z,
      relT({x}, {y}) -> relT({y}, {z}) -> relT({x}, {z}) f>
  ].

Definition ReflTransClosure : theory :=
  rev [
    tclone EndoRelation None nil nil nil;
    tdef <{
      inductive relTR =
      | "BaseTransRefl" : forall x, relTR({x}, {x})
      | "StepTransRefl" : forall x, forall y, forall z,
        relTR({x}, {y}) -> rel({y}, {z}) -> relTR({x}, {z})
      end
    }>;
    tprop Plemma "relTR_transitive" <f forall x, forall y, forall z,
      relTR({x}, {y}) -> relTR({y}, {z}) -> relTR({x}, {z}) f>
  ].

(*Lexicographic Ordering*)
(*We define our own tuple type, since we don't include Why3's
  tuples, which are generated on-the-fly*)
Definition t1_ts : typesym := mk_ts "t1" nil.
Definition t2_ts : typesym := mk_ts "t2" nil.
Definition t1 : vty := vty_cons t1_ts nil.
Definition t2 : vty := vty_cons t2_ts nil.
Definition tup_ts : typesym := mk_ts "Tup" nil.
Definition tup : vty := vty_cons tup_ts nil.
Definition pair : funsym := funsym_noty "Pair" [t1; t2] tup.
Definition tup_adt : alg_datatype :=
  alg_def tup_ts (list_to_ne_list [pair] erefl).
Definition tup_mut : mut_adt := mut_from_adt tup_adt.
Definition rel1 : predsym := binpred "rel1" t1.
Definition rel2 : predsym := binpred "rel2" t2.
Definition lex : predsym := binpred "lex" tup.

Definition x1 : vsymbol := ("x1", t1).
Definition x2 : vsymbol := ("x2", t1).
Definition y1 : vsymbol := ("y1", t2).
Definition y2 : vsymbol := ("y2", t2).

Definition Lex : theory :=
  rev [
    tdef (abs_type t1_ts);
    tdef (abs_type t2_ts);
    tdef (abs_pred rel1);
    tdef (abs_pred rel2);
    (*Simulating the "on-the-fly" tuple creation in Why3*)
    tdef (datatype_def tup_mut);
    tdef <{
      inductive lex =
      | "Lex_1": forall x1, forall x2, forall y1, forall y2,
        rel1({x1}, {x2}) -> lex(pair({x1}, {y1}), pair({x2}, {y2}))
      | "Lex_2": forall x1, forall y1, forall y2,
        rel2({y1}, {y2}) -> lex(pair({x1}, {y1}), pair({x1}, {y2}))
      end
    }>
  ].

(*TODO: min and max most likely (good demo) after non-recursive funs*)

End Relations.