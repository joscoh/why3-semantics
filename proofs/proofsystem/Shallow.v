(*A (very incomplete) shallowly embedded proof system, in which
  we can represent goals as corresponding goals in Coq.
  This is incomplete (in part) because of quantifiers: 
  it is NOT true that [I |= forall x, f] iff forall closed t,
    [I |= f [t/x]], because there may not be enough closed terms
  and domain elements may be unmatched. Quantifiers require the
  context and interpretation to be modified, which we do
  in our deeply embedded natural deduction proof system.*)
(*Some of these lemmas are useful for later proofs in NatDed.v*)
Require Export Logic.


(*I |= f1 /\ f2 iff I |= f1 and I |= f2. If only all connectives
  were so nice*)
Lemma satisfies_and {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (pf_full: full_interp gamma_valid pd pf)
  (A B: formula) (A_ty: formula_typed gamma A) 
  (B_ty: formula_typed gamma B):
  satisfies gamma_valid pd pf pf_full (Fbinop Tand A B) 
    (F_Binop _ _ _ _ A_ty B_ty)
  <-> 
  satisfies gamma_valid pd pf pf_full A A_ty /\
  satisfies gamma_valid pd pf pf_full B B_ty.
Proof.
  unfold satisfies. split; intros.
  - split; intros vt vv; specialize (H vt vv); revert H;
    simpl_rep_full; bool_to_prop; intros [C1 C2]; 
    erewrite fmla_rep_irrel; [apply C1 | apply C2].
  - destruct H as [F1 F2]; specialize (F1 vt vv);
    specialize (F2 vt vv); simpl_rep_full;
    rewrite fmla_rep_irrel with(Hval2:=A_ty),
      fmla_rep_irrel with (Hval2:=B_ty), F1, F2; auto.
Qed.

(*TODO: prove OR, IMPL for closed formulas*)


