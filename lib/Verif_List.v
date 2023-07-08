Require Import StdLib.
Require Import Verif_Int.
Require Import Lib_List.
Set Bullet Behavior "Strict Subproofs".

(*First, just do typechecking*)
Lemma list_typed : typed_theory List.List.
Proof.
  check_theory.
Qed.

Lemma length_typed : typed_theory List.Length.
Proof.
  check_theory.
Qed.

Lemma mem_typed : typed_theory List.Mem.
Proof. 
  check_theory.
Qed.

Lemma app_typed: typed_theory List.Append.
Proof.
  check_theory.
Qed.

Lemma reverse_typed: typed_theory List.Reverse.
Proof.
  check_theory.
Qed.

(*Contexts*)
Module ListCtx.

Import Lib_Relations.Relations.
Import Lib_Algebra.Algebra.
Import Lib_Int.Int.
Import Lib_List.List.

Lemma list_ctx : theory_ctx_ext List = 
[:: nonrec_pred is_nil [:: l] is_nil_body; datatype_def list_mut].
Proof.
  reflexivity.
Qed.

Lemma length_ctx : theory_ctx_ext Length = [:: rec_fun length [:: l] length_body].
Proof.
  reflexivity.
Qed.

Lemma mem_ctx: theory_ctx_ext Mem = [:: rec_pred mem [:: x; l] mem_body].
Proof.
  reflexivity.
Qed.

Lemma app_ctx: theory_ctx_ext Append = [:: rec_fun app [:: l1; l2] app_body].
Proof.
  reflexivity.
Qed.

Lemma reverse_ctx: theory_ctx_ext Reverse = [:: rec_fun reverse [:: l] reverse_body].
Proof.
  reflexivity.
Qed.

End ListCtx.

Module ListAxioms.

Import Lib_Relations.Relations.
Import Lib_Algebra.Algebra.
Import Lib_Int.Int.
Import Lib_List.List.

Lemma list_axioms : theory_axioms_ext List = 
[:: ("is_nil_spec", <f forall l,
      is_nil<a>({l}) <-> [list] {l} = Nil<a>() f>)].
Proof.
  reflexivity.
Qed.

Lemma length_axioms : theory_axioms_ext Length =
[("Length_nil", <f forall l,
    [vty_int] length<a>({l}) = zero() <-> [list] {l} = Nil<a>()
    f>);
  ("Length_nonnegative", <f forall l,
    ge(length<a>({l}), zero()) f>)].
Proof.
  reflexivity.
Qed.

Lemma mem_axioms: theory_axioms_ext Mem = nil.
Proof. 
  reflexivity.
Qed.

Lemma app_axioms: theory_axioms_ext Append =
[
  ("mem_decomp",
  <f forall x, forall l1,
    mem<a>({x}, {l1}) ->
    exists l2, exists l3, 
      [list] {l1} = app<a>({l2}, Cons<a>({x}, {l3})) f>);
  ("mem_append", 
  <f forall x, forall l1, forall l2,
    mem<a>({x}, app<a>({l1}, {l2})) <->
    mem<a>({x}, {l1}) \/ mem<a>({x}, {l2}) f>);
  ("Append_length", 
  <f forall l1, forall l2,
    [vty_int] length<a>(app<a>({l1}, {l2})) =
      plus(length<a>({l1}), length<a>({l2})) f>);
  ("Append_l_nil", <f forall l1,
    [list] app<a>({l1}, Nil<a>()) = {l1} f>);
  ("Append_assoc", <f forall l1, forall l2, forall l3,
    [list] app<a>({l1}, app<a>({l2}, {l3})) =
          app<a>(app<a>({l1}, {l2}), {l3})
    f>)
].
Proof.
  reflexivity.
Qed.

(*TODO: reverse axioms*)
End ListAxioms.

(*Helpful for lemmas*)
Module OtherCtx.

Import Lib_Relations.Relations.
Import Lib_Algebra.Algebra.
Import Lib_Int.Int.
Import Lib_List.List.

End OtherCtx.

(*Prove lemmas*)

Module ListProofs.

Import Lib_Relations.Relations.
Import Lib_Algebra.Algebra.
Import Lib_Int.Int.
Import Lib_List.List.

Definition a_ : vty := tyconst "a".
Definition x_ : vsymbol := ("x", a_).
Definition y_ : vsymbol := ("y", a_).
Definition list_a : vty := vty_cons list_ts [a_].
Definition r_: vsymbol := ("r", list_a).
Definition l1_ : vsymbol := ("l1", list_a).
Definition l2_ : vsymbol := ("l2", list_a).
Definition l3_ : vsymbol := ("l3", list_a).

Definition l1__ : term := Tfun (constsym "l1" list_a) nil nil.
Definition l2__ : term := Tfun (constsym "l2" list_a) nil nil.
Definition l3__ : term := Tfun (constsym "l3" list_a) nil nil.
Definition l__ : term := Tfun (constsym "l" list_a) nil nil.
Definition x__ : term := Tfun (constsym "x" a_) nil nil.
Definition y__ : term := Tfun (constsym "y" a_) nil nil.

Ltac extra_simpl ::= fold a_; fold x_; fold y_; 
  fold list_a;
  fold l1_; fold l2_; fold l3_; fold r_;
  unfold t_constsym;
  fold l1__; fold l2__; fold l3__; fold l__;
  fold x__; fold y__;
  repeat (tryif progress(unfold ty_subst; try unfold ty_subst_var)
    then simpl else idtac).


(*The interesting ones are Append and Reverse*)
Lemma app_valid: valid_theory Append.
Proof.
  simpl valid_theory.
  split_all; auto; exists ["a"];
  apply soundness; simpl_task;
  rewrite ListCtx.list_ctx ListAxioms.list_axioms; simpl.
  - (*[app] is associative*)
    (*In all, we expand the context by rewriting,
      not manually unfolding, which takes a long time*)
    simpl_mono.
    winduction.
    + (*Nil case: simplify both sides*)
      wintros "l2". wintros "l3".
      wunfold_at app 0%N; wsimpl_match.
      wunfold_at app 2%N; wsimpl_match.
      wreflexivity.
    + wintros "x" "l" "IH" "l2" "l3".
      wunfold_at app 0%N; wsimpl_match.
      wunfold_at app 3%N; wsimpl_match.
      wunfold_at app 2%N; wsimpl_match.
      (*Now we can rewrite with the IH*)
      wspecialize "IH" l2__ l3__.
      wrewrite "IH".
      wreflexivity.
  - (*l ++ nil = l*)
    (*This proof is much easier, it is almost the same
      as in Coq*)
    simpl_mono.
    winduction.
    + wunfold_at app 0%N; wsimpl_match.
      wreflexivity.
    + wintros "x" "l" "IH".
      wunfold_at app 0%N; wsimpl_match.
      wrewrite "IH".
      wreflexivity.
  - (*length (l1 ++ l2) = length l1 + length l2*)
    (*Here, we cannot unfold even if we wanted to*)
    rewrite ListCtx.length_ctx 
    Verif_Int.IntCtx.int_ctx
    ListAxioms.length_axioms
    Verif_Int.IntCtx.int_axioms; simpl.
    simpl_mono.
    winduction.
    + wintros "l2". 
      wunfold_at app 0%N; wsimpl_match.
      wunfold_at length 1%N; wsimpl_match.
      (*Use fact that x + 0 = x*)
      wspecialize "Unit_def_l" <t length<a_>(l2__) t>.
      wrewrite "Unit_def_l".
      wreflexivity.
    + (*Inductive case*)
      wintros "x" "l" "IH" "l2".
      wunfold_at app 0%N; wsimpl_match.
      wunfold_at length 0%N; wsimpl_match.
      wunfold_at length 1%N; wsimpl_match.
      (*Use IH+add assoc*)
      wspecialize "IH" l2__.
      wrewrite "IH".
      wspecialize "Assoc" <t one() t> <t length<a_>(l__) t>
        <t length<a_>(l2__) t>.
      wrewrite "Assoc".
      wreflexivity.
  (*We do not (yet) do the mem goals*)
  (*TODO: do predicate unfolding then this*)
  - admit.
  - admit.
Admitted.

(*Reverse*)
Lemma rev_valid: valid_theory Reverse.
Proof.
  simpl valid_theory.
  split_all; auto; exists ["a"];
  apply soundness; simpl_task;
  rewrite ListCtx.list_ctx ListAxioms.list_axioms
  ListCtx.app_ctx ListAxioms.app_axioms
  ListCtx.mem_ctx ListAxioms.mem_axioms
  ListCtx.length_ctx ListAxioms.length_axioms
  Verif_Int.IntCtx.int_ctx Verif_Int.IntCtx.int_axioms ; simpl.
  - simpl_mono.
    (*Don't need induction here*)
    wintros "l1" "l2" "x".
    wunfold_at reverse 0%N; wsimpl_match.
    (*Use app_assoc*)
    (*Need to specialize type*)
    wspecialize_ty "Append_assoc" [("a", a_)].
    wspecialize "Append_assoc" <t reverse <a_>(l1__) t>
      <t Cons<a_>(x__, Nil<a_>()) t>
      l2__.
    wrewrite<- "Append_assoc".
    wunfold_at app 1%N; wsimpl_match.
    wunfold_at app 1%N; wsimpl_match.
    wreflexivity.
  - (*reverse_cons is even easier*)
    simpl_mono.
    wintros "l" "x".
    wunfold_at reverse 0%N; wsimpl_match.
    wreflexivity.
  - (*cons_reverse now needs induction*)
    simpl_mono.
    winduction.
    + wintros "x".
      wunfold_at reverse 0%N; wsimpl_match.
      wunfold app; wsimpl_match.
      wunfold reverse; wsimpl_match.
      wunfold reverse; wsimpl_match.
      wunfold app; wsimpl_match.
      wreflexivity.
    + wintros "x" "l" "IH" "y".
      wunfold app; wsimpl_match.
      wunfold_at reverse 1%N; wsimpl_match.
      wspecialize "IH" y__.
      wrewrite<- "IH".
      wunfold app; wsimpl_match.
      (*Now use [reverse_cons]*)
      wspecialize_ty "reverse_cons" [("a", a_)].
      wspecialize "reverse_cons" l__ x__.
      wrewrite "reverse_cons".
      wreflexivity.
  - (*reverse_reverse follows from these*)
    simpl_mono.
    winduction.
    + wunfold_at reverse 1%N; wsimpl_match.
      wunfold reverse; wsimpl_match.
      wreflexivity.
    + wintros "x" "l" "IH".
      wunfold_at reverse 1%N; wsimpl_match.
      (*Use cons_reverse here*)
      wspecialize_ty "cons_reverse" [("a", a_)].
      wspecialize "cons_reverse" <t reverse<a_>(l__) t> x__.
      wrewrite<- "cons_reverse".
      wrewrite "IH".
      wreflexivity.
  - (*TODO: mem*) admit.
  - (*length of reverse - from length_app*)
    simpl_mono.
    winduction.
    + wunfold reverse; wsimpl_match.
      wreflexivity.
    + wintros "x" "l" "IH".
      wunfold reverse; wsimpl_match.
      (*Use Append_length*)
      wspecialize_ty "Append_length" [("a", a_)].
      wspecialize "Append_length" <t reverse<a_>(l__) t>
        <t Cons<a_>(x__, Nil<a_>()) t>.
      wrewrite "Append_length".
      wrewrite "IH".
      do 3 (wunfold_at length 1%N ; wsimpl_match).
      (*Now, just some int arithemtic*)
      wassert "Honezero" <f [int] plus(one(), zero()) = one() f>.
      {
        wspecialize "Comm" <t one() t> <t zero() t>.
        wrewrite "Comm".
        wspecialize "Unit_def_l" <t one() t>.
        wassumption.
      }
      wrewrite "Honezero".
      wspecialize "Comm"  <t length<a_>(l__) t>
        <t one() t>.
      wassumption.
Admitted.

End ListProofs.