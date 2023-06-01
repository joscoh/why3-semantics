(*Here, we manually instantiate a few theories to test
  that (especially) the cloning/qualifying works*)
Require Import Task.
Require Import Theory.
Require Import Typechecker.
Require Import NatDed.
From mathcomp Require Import all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

(*Why3 has constants, which so far as I can tell are just
  function symbols that take no arguments. We give some
  utilities*)
Definition mk_constant (name: string) (ty: vty):=
  Build_funsym (Build_fpsym name nil nil erefl erefl) ty.


(*Here, we first use some examples from why3/stdlib/algebra*)

Module Alg.

Definition t : typesym := mk_ts "t" nil.
Definition t_ty : vty := vty_cons t nil.

Definition op: funsym := Build_funsym 
  (Build_fpsym "op" nil [t_ty; t_ty] erefl erefl)
  t_ty erefl.

Definition x : vsymbol := ("x"%string, t_ty).
Definition y : vsymbol := ("y"%string, t_ty).
Definition z : vsymbol := ("z"%string, t_ty).

Module Assoc.

Definition assoc : theory :=
  rev [
    (*type t*)
    tdef (abs_type t);
    (*function op t t : t*)
    tdef (abs_fun op);
    (*axiom Assoc : forall x y z : t. op (op x y) z = op x (op y z)*)
    tprop Paxiom "Assoc" (fforalls [x; y; z]
      (Feq t_ty (Tfun op nil [Tfun op nil [Tvar x; Tvar y]; Tvar z])
        (Tfun op nil [Tvar x; Tfun op nil [Tvar y; Tvar z]])))
  ].

Lemma assoc_typed : typed_theory assoc.
Proof.
  check_theory.
Qed.

Lemma assoc_valid: valid_theory assoc.
Proof.
  simpl. split; auto. prove_task_wf.
Qed.

End Assoc.

(*Commutativity*)
Module Comm.

Definition comm: theory :=
  rev [
    (*type t*)
    tdef (abs_type t);
    (*function op t t : t*)
    tdef (abs_fun op);
    (*axiom Comm : forall x y : t. op x y = op y x*)
    tprop Paxiom "Comm" (fforalls [x; y]
      (Feq t_ty (Tfun op nil [Tvar x; Tvar y]) 
        (Tfun op nil [Tvar y; Tvar x])))
  ].

Definition comm_typed : typed_theory comm.
Proof.
  check_theory. 
Qed.

Lemma comm_valid: valid_theory comm.
Proof.
  simpl. split; auto. prove_task_wf.
Qed.

End Comm.

(*Monoid*)
Module Monoid.

Definition unit : funsym := mk_constant "unit" t_ty erefl.

Definition monoid : theory :=
  rev [
    (*clone export Assoc*)
    tclone Assoc.assoc None nil nil nil;
    (*constant unit : t*)
    tdef (abs_fun unit);
    (*axiom Unit_def_l : forall x:t. op unit x = x*)
    tprop Paxiom "Unit_def_l" (Fquant Tforall x (Feq t_ty 
      (Tfun op nil [Tfun unit nil nil; Tvar x]) (Tvar x)));
    (*axiom Unit_def_r : forall x:t. op x unit = x*)
    tprop Paxiom "Unit_def_r" (Fquant Tforall x (Feq t_ty
      (Tfun op nil [Tvar x; Tfun unit nil nil]) (Tvar x)))
  ].

Lemma monoid_ctx : theory_ctx_int monoid =
  rev [abs_type t; abs_fun op; abs_fun unit].
Proof.
  reflexivity.
Qed.

Lemma monoid_valid: valid_theory monoid.
Proof.
  simpl; split_all; auto; prove_task_wf.
Qed.

Lemma monoid_typed: typed_theory monoid.
Proof. check_theory. Qed.

End Monoid.

(*Commutative Monoid*)

Module CommutativeMonoid.

Definition comm_monoid : theory :=
  rev [
    (*clone export Monoid*)
    tclone Monoid.monoid None nil nil nil;
    (*clone export Comm with type t = t, function op = op*)
    tclone Comm.comm None [(t, t)] [(op, op)] nil
  ].

(*Still same context*)
Lemma comm_monoid_ctx : theory_ctx_int comm_monoid =
rev [abs_type t; abs_fun op; abs_fun Monoid.unit].
Proof.
  reflexivity.
Qed.

Lemma comm_monoid_typed: typed_theory comm_monoid.
Proof. check_theory. Qed.

Lemma comm_monoid_valid: valid_theory comm_monoid.
Proof.
  simpl; split_all; auto; prove_task_wf.
Qed.

End CommutativeMonoid.

(*Group*)

Module Group.

Definition inv : funsym := Build_funsym 
  (Build_fpsym "inv" nil [t_ty] erefl erefl) t_ty erefl.

Definition group : theory :=
  rev [
    (*clone export Monoid*)
    tclone Monoid.monoid None nil nil nil;
    (*function inv t : t*)
    tdef (abs_fun inv);
    (*axiom Inv_def_l : forall x:t. op (inv x) x = unit*)
    tprop Paxiom "Inv_def_l" (Fquant Tforall x (Feq t_ty 
      (Tfun op nil [Tfun inv nil [Tvar x]; Tvar x]) (Tfun Monoid.unit nil nil)));
    (*axiom Inv_def_r : forall x:t. op x (inv x) = unit*)
    tprop Paxiom "Inv_def_r" (Fquant Tforall x (Feq t_ty
      (Tfun op nil [Tvar x; Tfun inv nil [Tvar x]]) (Tfun Monoid.unit nil nil)))
  ].

(*Now, we have inverse*)
Lemma group_ctx : theory_ctx_int group =
rev [abs_type t; abs_fun op; abs_fun Monoid.unit;
  abs_fun inv].
Proof.
  reflexivity.
Qed.

Lemma group_typed: typed_theory group.
Proof. check_theory. Qed.

Lemma group_valid: valid_theory group.
Proof.
  simpl; split_all; auto; prove_task_wf.
Qed.


End Group.

(*Commutative Groups*)
Module CommGroup.

Definition comm_group : theory :=
  rev [
    (*clone export Group*)
    tclone Group.group None nil nil nil;
    (*clone export Comm with type t = t, function op = op*)
    tclone Comm.comm None [(t, t)] [(op, op)] nil
  ].

Lemma comm_group_ctx : theory_ctx_int comm_group =
rev [abs_type t; abs_fun op; abs_fun Monoid.unit;
  abs_fun Group.inv].
Proof.
  reflexivity.
Qed.

Lemma comm_group_typed: typed_theory comm_group.
Proof. check_theory. Qed.

Lemma comm_group_valid: valid_theory comm_group.
Proof.
  simpl; split_all; auto; prove_task_wf.
Qed.

End CommGroup.

(*Rings*)

Module Ring.

(*Here, things get a bit interesting, since we have multiple
  clones and more than 1 set of functions interacting.
  We do not support the infix notation of why3*)

Definition zero : funsym := mk_constant "zero" t_ty erefl.
Definition plus : funsym := Build_funsym 
  (Build_fpsym "plus" nil [t_ty; t_ty] erefl erefl)
  t_ty erefl.
Definition mult : funsym := Build_funsym 
  (Build_fpsym "mult" nil [t_ty; t_ty] erefl erefl)
  t_ty erefl.
Definition neg : funsym := Build_funsym 
(Build_fpsym "neg" nil [t_ty] erefl erefl)
t_ty erefl.

(*Unlike regular why3, we require qualified names in "clone"*)
Definition MA_t : typesym := mk_ts "MulAssoc.t" nil.
Definition MA_t_ty : vty := vty_cons MA_t nil.
(*We have utilities to do this, but we are testing them, so we
  do it by hand*)
Definition MA_op: funsym := Build_funsym (Build_fpsym "MulAssoc.op" nil [MA_t_ty; MA_t_ty] erefl erefl)
  MA_t_ty erefl.

Definition ring : theory :=
  rev [
    (*type t*)
    tdef (abs_type t);
    (*constant zero : t*)
    tdef (abs_fun zero);
    (*function (+) t t : t*)
    tdef (abs_fun plus);
    (*function (-_) t : t*)
    tdef (abs_fun neg);
    (*function ( * ) t t: t*)
    tdef (abs_fun mult);
    (*clone export CommutativeGroup with type t = t,
                                constant unit = zero,
                                function op = (+),
                                function inv = (-_)*)
    tclone CommGroup.comm_group None [(t, t)] [(Monoid.unit, zero); 
      (op, plus); (Group.inv, neg)] nil;
    (*clone Assoc as MulAssoc with type t = t, function op = ( * )*)
    tclone Assoc.assoc (Some "MulAssoc"%string) [(MA_t, t)] [(MA_op, mult)] nil;
    (*axiom Mul_distr_l : forall x y z : t. x * (y + z) = x * y + x * z*)
    tprop Paxiom "Mul_distr_l" (fforalls [x; y; z] (Feq t_ty
      (Tfun mult nil [Tvar x; Tfun plus nil [Tvar y; Tvar z]])
      (Tfun plus nil [Tfun mult nil [Tvar x; Tvar y]; Tfun mult nil [Tvar x; Tvar z]])
    ));
    (*axiom Mul_distr_r : forall x y z : t. (y + z) * x = y * x + z * x*)
    tprop Paxiom "Mul_distr_r" (fforalls [x;y;z] (Feq t_ty
      (Tfun mult nil [Tfun plus nil [Tvar y; Tvar z]; Tvar x])
      (Tfun plus nil [Tfun mult nil [Tvar y; Tvar x]; Tfun mult nil [Tvar z; Tvar x]])
    ))
  ].

(*Note that all of our exports do not add to the context. This fails
  if we don't add the qualified names in the "with" part*)
Lemma ring_ctx : theory_ctx_int ring =
rev [abs_type t; abs_fun zero; abs_fun plus; abs_fun neg; abs_fun mult].
Proof.
  reflexivity.
Qed.

(*The context (with the qualified names and everything)
  is still well-typed (meaning so are all the lemmas)*)
Lemma ring_typed: typed_theory ring.
Proof. check_theory. Qed.

(*god Coq is annoying sometimes*)

Lemma all_cons {T: Type} (p: pred T) (h: T) (s: seq T):
  all p (h :: s) = p h && all p s.
Proof.
  reflexivity.
Qed.

(*Problem - we cannot typecheck the context: why
  we have (from assoc)
  - forall x y z, (x op y) op z = x op (y op z)
  (from other assoc)
  - 

*)
(*
Lemma ring_valid: valid_theory ring.
Proof.
  simpl; split_all; auto; try prove_task_wf.
  - (*OK, what is problem here?*)
    apply /check_task_wf_correct.
    unfold check_task_wf.
    apply /andP; split; auto.
    apply /andP; split; auto.
    apply /andP; split; auto.
    apply /andP; split; auto.
    apply /andP; split; auto.
    + simpl task_delta.
      rewrite all_cons. apply /andP. split; auto.
      unfold Assoc.assoc, rev, catrev.
      rewrite !get_exported_names_equation_3.
      rewrite !get_exported_names_equation_2.
      rewrite get_exported_names_equation_1.
      rewrite qualify_theory_equation_3.
      rewrite !qualify_theory_equation_2.
      rewrite qualify_theory_equation_1.
      simpl.
      rewrite theory_axioms_ext_equation_4.
      rewrite !theory_axioms_ext_equation_2.
      rewrite theory_axioms_ext_equation_1.
      unfold sub_props_map. simpl List.map.
      simpl map.
      rewrite all_cons.
      apply /andP; split; auto.
      (*Aha, so this one is the problem*)
      apply /typecheck_formula_correct.
      apply F_Quant; auto.
      {
        apply /typecheck_type_correct. reflexivity.
      }
      simpl. apply F_Quant; auto.
      {
        apply /typecheck_type_correct. reflexivity.
      }
      simpl. apply F_Quant; auto.
      {
        apply /typecheck_type_correct. reflexivity.
      }
      apply F_Eq.
      {
        (*A problem here - why is everything op?*)
        apply T_Fun; simpl; auto.
        - apply /inP. reflexivity.
        - apply /typecheck_type_correct. reflexivity.
        -
        
        
        repeat constructor; auto. apply /forallb_ForallP. reflexivity. unfold CommGroup.comm_group, Group.group, Comm.comm, Monoid.monoid, Assoc.assoc,
        rev, catrev. 
          simpl. rewrite !theory_ctx_ext_equation_3.
          rewrite !theory_ctx_ext_equation_2.
          rewrite theory_ctx_ext_equation_1.
          simpl.
          rewrite !theory_ctx_ext_equation_6.
          simpl.
          rewrite theory_ctx_ext_equation_1.
          simpl.
          rewrite !theory_ctx_ext_equation_3.
          rewrite !theory_ctx_ext_equation_2.
          rewrite !theory_ctx_ext_equation_6. simpl.
          rewrite !theory_ctx_ext_equation_3.
          rewrite !theory_ctx_ext_equation_2.
          rewrite !theory_ctx_ext_equation_6. simpl.
          rewrite !theory_ctx_ext_equation_3.
          rewrite !theory_ctx_ext_equation_2.
          rewrite !theory_ctx_ext_equation_1.
          rewrite !app_nil_r.

          simpl sig_f. unfold sig_f. simpl List.map.
          unfold sub_funs.
          unfold sub_from_map.
          simpl get_assoc_list. simpl. auto.
          (*WTF, this is true. What is going on?*)
          simpl sub_funs.
          unfold sub_funs. simpl.
          unfold sub_ctx_map. simpl.
          unfold Group.grou
          simpl.
          unfold sub_ctx_map.
          
          u

        apply /typecheck_term_correct. reflexivity.
      }
      simpl.
      simpl.
      unfold qual_fmla.
      unfold sub_in_f.
      simpl.
      simpl.
      reflexivity.


      rewrite all_cons.
      rewrite all_cons.
      simpl.
      
      simpl.

      unfold sub_props_map.
      simpl.
    
    simpl.
    
    
    reflexivity.
    
    
    simpl.
    
    simpl.


Qed.
*)
End Ring.

(*Now, we prove a few simple theories (manually)
  about rings. This is not part of the stdlib (names from
  mathcomp)*)
Module RingTheory.

Definition ring_theory : theory :=
  rev [
    (*use ring*)
    tuse Ring.ring false;
    (*lemma subr0_eq : forall x y : t. x + (- y) = 0 -> x = y*)
    tprop Plemma "subr0_eq" (fforalls [x; y] (Fbinop Timplies
      (Feq t_ty (Tfun Ring.plus nil [Tvar x; Tfun Ring.neg nil [Tvar y]]) (Tfun Ring.zero nil nil))
      (Feq t_ty (Tvar x) (Tvar y))  
    ));
    (*lemma add_cancel_l: forall x y z: t. x + y = x + z -> y = z*)
    tprop Plemma "add_cancel_l" (fforalls [x;y;z] (Fbinop Timplies
      (Feq t_ty (Tfun Ring.plus nil [Tvar x; Tvar y])
        (Tfun Ring.plus nil [Tvar x; Tvar z]))
      (Feq t_ty (Tvar y) (Tvar z))
    ));
    (*lemma mulr0: forall x: t. x * 0 = 0*)
    tprop Plemma "mulr0" (Fquant Tforall x (Feq t_ty
      (Tfun Ring.mult nil [Tvar x; Tfun Ring.zero nil nil])
      (Tfun Ring.zero nil nil)))
  ].

(*Internal context still has everything from ring*)
Lemma ring_theory_ctx : theory_ctx_int ring_theory =
rev [abs_type t; abs_fun Ring.zero; abs_fun Ring.plus; abs_fun Ring.neg; abs_fun Ring.mult].
Proof.
  reflexivity.
Qed.

(*External context is empty*)
Lemma ring_theory_ctx_ext: theory_ctx_ext ring_theory = nil.
Proof.
  reflexivity.
Qed.

(*Everything is well-typed*)
Lemma ring_theory_typed: typed_theory ring_theory.
Proof. check_theory. Qed.

Require Import Alpha.

Ltac prove_fmla_ty :=
  apply /typecheck_formula_correct; reflexivity.

Ltac prove_tm_ty :=
  apply /check_tm_ty_spec; reflexivity.

Definition check_formulas_typed (gamma: context) (l: list formula): bool :=
  all (typecheck_formula gamma) l.

Lemma check_formulas_typed_correct gamma l:
  reflect (Forall (formula_typed gamma) l) (check_formulas_typed gamma l).
Proof.
  unfold check_formulas_typed.
  apply forallb_ForallP. intros.
  apply typecheck_formula_correct.
Qed.

Ltac prove_fmlas_ty :=
  apply /check_formulas_typed_correct; reflexivity.

Ltac prove_valid_context :=
  apply /check_context_correct; reflexivity.

(*Now, we prove these lemmas (manually, from the semantics)
  *)
Notation "0r" :=(Tfun Ring.zero nil nil).
Notation "x '+r' y" := (Tfun Ring.plus nil [x; y])
  (at level 60).
Notation "'-r' x" := (Tfun Ring.neg nil x)
  (at level 70).
Notation "x '*r' y" := (Tfun Ring.mult nil [x;y])
  (at level 50).
Notation "x '==' y" := (Feq _ x y).
(*A complete hack*)
Notation xt := (t_constsym ("x"%string) t_ty).
(*TODO: get some real notations*)
Lemma ring_theory_valid: valid_theory ring_theory.
Proof.
  simpl. split_all; auto.
  - (*First lemma*)
    apply soundness.
    simpl_task.
    rewrite theory_axioms_ext_equation_1.
    rewrite !app_nil_r.
    (*1.intros*)
    apply D_forallI with(c:="x"%string).
    reflexivity.
    (*TODO: automate these*)
    prove_fmlas_ty.
    prove_closed.
    (*TODO: safe_sub_f does not evaluate*)
    unfold safe_sub_f; simpl.
    (*So now we have to prove for a specific x, that x * 0 = 0 *)
    (*2. assert (0 + 0 = 0)*)
    apply (D_assert _ _ (Feq t_ty (0r +r 0r) 0r)).
    {
      (*Prove the assertion*)
      (*We need a better way to do this*)
      apply (D_assert _ _ (Fquant Tforall x 
        (Feq t_ty (0r +r (Tvar x)) (Tvar x)))).
      {
        apply D_axiom.
        prove_task_wf.
        apply /inP. reflexivity.
      }
      (*Now we specialize*)
      (*TODO: this is awful*)
      apply (D_assert _ _ (safe_sub_f 0r x (Feq t_ty 
        (0r +r Tvar x) (Tvar x)))).
      {
        apply D_forallE. prove_tm_ty.
        (*TODO: decidable closed term*)
        constructor; reflexivity.
        apply D_axiom; [prove_task_wf | apply /inP; reflexivity].
      }
      unfold safe_sub_f; simpl. 
      apply D_axiom; [prove_task_wf | apply /inP; reflexivity].
    }
    (*3. From this and f_equal, we can prove that x * (0 + 0) = x * 0*)
    apply (D_assert _ _ (Feq t_ty (xt *r (0r +r 0r)) (xt *r 0r))).
    {
      apply D_f_equal; try reflexivity; try prove_tm_ty.
      simpl. (*Need better way to do this*) constructor.
      - apply D_eq_refl; auto.
        prove_valid_context.
        prove_fmlas_ty.
        constructor; reflexivity.
        prove_tm_ty.
      - constructor; [|constructor].
        apply D_axiom; [prove_task_wf | apply /inP; reflexivity].
    }
    (*4. we have that x * (0 + 0) = 0 + x * 0*)
    apply (D_assert _ _ (Feq t_ty (xt *r (0r +r 0r)) (0r +r (xt *r 0r)))).
    {
      apply D_rewrite with(t1:=0r +r (xt *r 0r))(t2:=xt *r 0r)(ty:=t_ty).
      prove_closed.
      - apply (D_assert _ _ (Fquant Tforall x 
          (Feq t_ty (0r +r (Tvar x)) (Tvar x)))).
        {
          apply D_axiom.
          prove_task_wf.
          apply /inP. reflexivity.
        }
        (*Now we specialize*)
        apply (D_assert _ _ (safe_sub_f (xt *r 0r) x (Feq t_ty 
          (0r +r Tvar x) (Tvar x)))).
        {
          apply D_forallE. prove_tm_ty.
          (*TODO: decidable closed term*)
          constructor; reflexivity.
          apply D_axiom; [prove_task_wf | apply /inP; reflexivity].
        }
        unfold safe_sub_f; simpl. apply D_axiom; [prove_task_wf | apply /inP; reflexivity].
      - unfold replace_tm_f; simpl. apply D_axiom; [prove_task_wf | apply /inP; reflexivity].
    }
    (*5. we can distribute and rewrite so that x * 0 + x * 0 = 0 + x * 0*)
    apply (D_assert _ _ (Feq t_ty ((xt *r 0r) +r (xt *r 0r)) 
      (0r +r (xt *r 0r)))).
    {
      (*need to rewrite, use symmetry, etc*)
      admit.
    }
    (*Now, use cancellation*)
    (*TODO: finish this (or make nicer with hypotheses)
    This really isn't usable
    what I should do 
    1. name the hypotheses
    2. make "derived derivations" - from core
      that allow us to modify the hypotheses
      (ex: specialize: 
        if we have H: forall x, f in delta, 
        then we can replace with H (f[t/x]))
    3. On top of this, write tactics that
      handle the reflexivity goals
    *)
    Check D_forallE.
    apply (D_assert _ _ (safe_sub_f ))

    (*4: we also have that x * 0 = 0 + x * 0*)
    apply 


        reflexivity.
    }

        admit.

        Search check_closed_tm.
        
        apply check_ty.
      }
      Check D_forallE.
      apply D_forallE.

      (Fquant Tforall x (Feq t_ty 
      (Tfun op nil [Tfun unit nil nil; Tvar x]) (Tvar x)))


      unfold Ring.ring. simpl.
      assert (D_assert _ _ ())
    }

    apply /all_forallP.
    2: prove_closed.



    2: check_closed.
    Search Logic.closed.
    (*We want to prove that x * 0 = 0*)
    (*First step: show that 0 + 0 = 0*)
    apply D_assert (Feq t_ty (Tfun Ring.plus nil 
      [Tfun Ring.zero nil nil; Tfun Ring.))
    Check D_assert.
    apply D_assert.



    simpl.
    unfold task_valid. simpl. split.
    + prove_task_wf.
    + intros.
      unfold log_conseq. intros. simpl in H.
      assert (L2 := H).
      assert (L1 := H).
      specialize (L1 _ (ltac:(left; reflexivity))).
      specialize (L2 _ (ltac:(right; left; reflexivity))).
      rewrite !tforall_rewrite. simpl.
      intros.
      (*TODO: how to avoid needing to unfold*) 
      unfold safe_sub_f; simpl.
      (*Let's see*)
      (*assert: (x * (0+0) = x * 0)*)
      assert (satisfies (task_gamma_valid w_wf) pd pf pf_full
        (Feq t_ty (Tfun Ring.mult nil [Tvar (y0, t_ty); 
          Tfun Ring.plus nil [Tfun Ring.zero nil nil; Tfun Ring.zero nil nil]])
          (Tfun Ring.mult nil [Tvar x; Tfun Ring.zero nil nil])) ltac:(prove_fmla_ty)).
      {
        admit.
      }
      


      }  Ring.zero nil nil])))
      
      simpl in *.

      
      simpl.
      
      simpl in L2.

      
      specialize (H0 _ ltac:(right; right)).
    
    
    apply /check_task_wf_correct.

      unfold check_task_wf.  
      assert (check_context (theory_ctx_ext Ring.ring ++ [::])%list).
        reflexivity.
      rewrite H.
      do 5 (try (apply /andP; split)); auto.
      unfold task_delta.
      rewrite all_cons.
      apply /andP. split; auto.
      rewrite all_cons. apply /andP. split; try reflexivity.
      (*This is the hard one - one that doesnt work*)
      rewrite theory_axioms_ext_equation_1.
      rewrite !app_nil_r.
      (*This should follow from above?*)
      unfold Ring.ring.
      unfold rev, catrev.
      rewrite theory_axioms_ext_equation_4.
      rewrite theory_axioms_ext_equation_4.
      rewrite theory_axioms_ext_equation_8.
      rewrite theory_axioms_ext_equation_8.
      rewrite theory_axioms_ext_equation_2.
      rewrite theory_axioms_ext_equation_2.
      rewrite theory_axioms_ext_equation_2.
      rewrite theory_axioms_ext_equation_2.
      rewrite theory_axioms_ext_equation_2.
      rewrite theory_axioms_ext_equation_1.
      reflexivity.
      unfold Assoc.assoc.
      rewrite app_nil_r.
      rewrite all_cons. unfold is_true. rewrite andb_true_iff. split; try reflexivity.

      * reflexivity.
      *
      
      apply /andP.
      idtac.
      reflexivity.
      


      rewrite !all_cons.
      unfold is_true.
      Search all cons.
      simpl all.
      cbn iota.
      rewrite andb_true_iff.
      apply /andP; split.
      * reflexivity.
      * unfold Ring.ring. unfold rev. unfold catrev.
        rewrite theory_axioms_ext_equation_4.
        cbn beta. unfold is_true. rewrite andb_true_iff.
        split; try reflexivity.
        unfold is_true.
        cbn.

        rewrite andb_true_iff. split; try reflexivity.

      
      
      simpl catrev. simpl rev.
      
      
      simpl. unfold theory_ctx_ext. apply /andP. split; try reflexivity.


        simpl.
        repeat (apply /andP; split; try reflexivity). idtac.
        unfold sub_tys. unfold sub_from_map. simpl.

        unfold get_exported_names.


        reflexivity.
        
        reflexivity.
      
      unfold Ring.ring. simpl. reflexivity. apply /andP. split; try reflexivity.
        simpl. rewrite -/all. simpl. rewrite -andbA. simpl. apply /andP. 


      simpl.
      simpl all.
      simpl.
      reflexivity.
      compute.
      simpl.


      apply /andP. split.
      rewrite <- !andbA.
      do 3 (try (apply /andP; split)).
      * auto.
      * reflexivity.
      * reflexivity.
      repeat (apply /andP; split).
      simpl.
    
    simpl.
    reflexivity.
    
    prove_task_wf. *)

(*Plan: prove cancellation, zero identity in ring*)

(*THEN, do unit ring*)

(*then prove 1 results about mult and -1*)

(*Now, as a quick test, we prove some theorems about rings*)


(*TODO: groups, comm groups, rings
  Then, prove some ring theorems*)

(*old, maybe get rid of after finishing ring theory*)
(*Here, a simple test for cloning with a name and
  substitution - fixed some bugs in Theory with this*)
  (*Much simpler test*)
  Module Test.

  Definition theory1 : theory :=
    rev [
      tdef (abs_type t);
      tdef (abs_fun op)
    ].
  (*Unlike why3, we require qualified names even in clone declaration*)
  Definition tt : typesym := mk_ts "T.t" nil.
  Definition tt_ty : vty := vty_cons tt nil.
  Definition top : funsym := Build_funsym (Build_fpsym "T.op" nil [tt_ty; tt_ty] erefl erefl)
    tt_ty erefl.
  
  Definition theory2 : theory :=
    rev [
      tdef (abs_type t);
      tdef (abs_fun op);
      tclone theory1 (Some "T"%string) [(tt, t)] [(top, op)] nil;
      tprop Paxiom "foo" (fforalls [x; y] (Feq t_ty
        (Tfun op nil [Tvar x; Tvar y])
        (Tfun op nil [Tvar y; Tvar x])
      ))
    ].
  
  Lemma theory2_ctx: theory_ctx_int theory2 =
    rev [abs_type t; abs_fun op].
  Proof. reflexivity. Qed.
  
  Lemma theory2_ctx_ext: theory_ctx_ext theory2 =
  rev [abs_type t; abs_fun op].
  Proof.
    reflexivity.
  Qed.
  
  (*Typed*)
  Lemma theory2_typed: typed_theory theory2.
  Proof.
    check_theory.
  Qed.
  
  (*Well-formed*)
  Lemma theory2_valid: valid_theory theory2.
  Proof.
    simpl. split; auto. prove_task_wf.
  Qed.


(*Test where we clone twice*)


(*TODO: start here*)
(*Want to see why we have issues in ring
  I think - has to do with same module being cloned twice
  Try: module with axiom, clone twice with different ops and names
  then try with 1 that is unqualified
  see if we find an issue
  *)

  Definition theory3 : theory :=
    rev [
      tdef (abs_type t);
      tdef (abs_fun op);
      tprop Paxiom "foo" (fforalls [x; y] (Feq t_ty
        (Tfun op nil [Tvar x; Tvar y])
        (Tfun op nil [Tvar y; Tvar x])
      ))
    ].

    Definition at' : typesym := mk_ts "A.t" nil.
    Definition at_ty' : vty := vty_cons at' nil.
    Definition aop : funsym := Build_funsym (Build_fpsym "A.op" nil [at_ty'; at_ty'] erefl erefl)
      at_ty' erefl.

  Definition theory4 : theory :=
    rev [
      tdef (abs_type t);
      tdef (abs_fun Ring.plus);
      tdef (abs_fun Ring.mult);
      tclone theory3 (Some "T"%string) [(tt, t)] [(top, Ring.plus)] nil;
      tclone theory3 (Some "A"%string) [(at', t)] [(aop, Ring.mult)] nil;
      tprop Paxiom "Mul_distr_l" (fforalls [x; y; z] (Feq t_ty
        (Tfun Ring.mult nil [Tvar x; Tfun Ring.plus nil [Tvar y; Tvar z]])
        (Tfun Ring.plus nil [Tfun Ring.mult nil [Tvar x; Tvar y]; Tfun Ring.mult nil [Tvar x; Tvar z]])
      ))
    ].

  Lemma theory4_ctx: theory_ctx_int theory4 =
    rev [abs_type t; abs_fun Ring.plus; abs_fun Ring.mult].
  Proof. reflexivity. Qed.
  
  (*Typed*)
  Lemma theory4_typed: typed_theory theory4.
  Proof.
    check_theory.
  Qed.
  
  (*Well-formed*)
  Lemma theory4_valid: valid_theory theory4.
  Proof.
    simpl. split; auto.
    apply /check_task_wf_correct.
    reflexivity.
  Qed.
    unfold check_task_wf.
    apply /andP; split; auto.
    apply /andP; split; auto.
    apply /andP; split; auto.
    apply /andP; split; auto.
    apply /andP; split; auto.
    2: {
      simpl.
      unfold theory3, rev, catrev.
      rewrite !get_exported_names_equation_3.
      rewrite !get_exported_names_equation_2.
      rewrite !get_exported_names_equation_1.
      rewrite !qualify_theory_equation_3.
      rewrite !qualify_theory_equation_2.
      rewrite !qualify_theory_equation_1.
      simpl.
      rewrite !theory_axioms_ext_equation_4.
      rewrite !theory_axioms_ext_equation_2.
      rewrite !theory_axioms_ext_equation_1.
      unfold sub_props_map. Print sub_in_f.

      simpl.
      simpl.


    } simpl.
    
    
    2: reflexivity.
    + simpl task_delta.
      rewrite all_cons. apply /andP. split; auto.
      unfold Assoc.assoc, rev, catrev.
      rewrite !get_exported_names_equation_3.
      rewrite !get_exported_names_equation_2.
      rewrite get_exported_names_equation_1.
      rewrite qualify_theory_equation_3.
      rewrite !qualify_theory_equation_2.
      rewrite qualify_theory_equation_1.
      simpl.
      rewrite theory_axioms_ext_equation_4.
      rewrite !theory_axioms_ext_equation_2.
      rewrite theory_axioms_ext_equation_1.
      unfold sub_props_map. simpl List.map.
      simpl map.
      rewrite all_cons.
      apply /andP; split; auto.
      (*Aha, so this one is the problem*)
      apply /typecheck_formula_correct.
      apply F_Quant; auto.
      {
        apply /typecheck_type_correct. reflexivity.
      }
      simpl. apply F_Quant; auto.
      {
        apply /typecheck_type_correct. reflexivity.
      }
      simpl. apply F_Quant; auto.
      {
        apply /typecheck_type_correct. reflexivity.
      }
      apply F_Eq.
      {
        (*A problem here - why is everything op?*)
        apply T_Fun; simpl; auto.
        - apply /inP. reflexivity.
        - apply /typecheck_type_correct. reflexivity.
        -
        
        
        repeat constructor; auto. apply /forallb_ForallP. reflexivity. unfold CommGroup.comm_group, Group.group, Comm.comm, Monoid.monoid, Assoc.assoc,
        rev, catrev. 
          simpl. rewrite !theory_ctx_ext_equation_3.
          rewrite !theory_ctx_ext_equation_2.
          rewrite theory_ctx_ext_equation_1.
          simpl.
          rewrite !theory_ctx_ext_equation_6.
          simpl.
          rewrite theory_ctx_ext_equation_1.
          simpl.
          rewrite !theory_ctx_ext_equation_3.
          rewrite !theory_ctx_ext_equation_2.
          rewrite !theory_ctx_ext_equation_6. simpl.
          rewrite !theory_ctx_ext_equation_3.
          rewrite !theory_ctx_ext_equation_2.
          rewrite !theory_ctx_ext_equation_6. simpl.
          rewrite !theory_ctx_ext_equation_3.
          rewrite !theory_ctx_ext_equation_2.
          rewrite !theory_ctx_ext_equation_1.
          rewrite !app_nil_r.

          simpl sig_f. unfold sig_f. simpl List.map.
          unfold sub_funs.
          unfold sub_from_map.
          simpl get_assoc_list. simpl. auto.
          (*WTF, this is true. What is going on?*)
          simpl sub_funs.
          unfold sub_funs. simpl.
          unfold sub_ctx_map. simpl.
          unfold Group.grou
          simpl.
          unfold sub_ctx_map.


    simpl.
    simpl.
    Print Ltac prove_task_wf.
    
    prove_task_wf.
  Qed.

  Definition theory5 : theory :=
    rev [
      tdef (abs_type t);
      tdef (abs_fun Ring.plus);
      tdef (abs_fun Ring.mult);
      tclone theory3 (Some "T"%string) [(tt, t)] [(top, Ring.plus)] nil;
      tclone theory3 None [(t, t)] [(op, Ring.mult)] nil;
      tprop Paxiom "Mul_distr_l" (fforalls [x; y; z] (Feq t_ty
        (Tfun Ring.mult nil [Tvar x; Tfun Ring.plus nil [Tvar y; Tvar z]])
        (Tfun Ring.plus nil [Tfun Ring.mult nil [Tvar x; Tvar y]; Tfun Ring.mult nil [Tvar x; Tvar z]])
      ))
    ].

  Lemma theory5_ctx: theory_ctx_int theory5 =
    rev [abs_type t; abs_fun Ring.plus; abs_fun Ring.mult].
  Proof. reflexivity. Qed.
  
  (*Typed*)
  Lemma theory4_typed: typed_theory theory4.
  Proof.
    check_theory.
  Qed.
  
  (*Well-formed*)
  Lemma theory4_valid: valid_theory theory2.
  Proof.
    simpl. split; auto. prove_task_wf.
  Qed.

      
      
    ].
  
  End Test.