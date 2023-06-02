(*Here, we manually instantiate a few theories to test
  that (especially) the cloning/qualifying works*)
Require Import Task.
Require Import Theory.
Require Import Typechecker.
Require Import Tactics.
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


(*Now, we prove these lemmas (manually, from the semantics)
  *)
Notation "0r" :=(Tfun Ring.zero nil nil).
Notation "x '+r' y" := (Tfun Ring.plus nil [x; y])
  (at level 60).
Notation "'-r' x" := (Tfun Ring.neg nil [x])
  (at level 70).
Notation "x '*r' y" := (Tfun Ring.mult nil [x;y])
  (at level 50).
Notation "x '==' y" := (Feq _ x y).
(*A complete hack*)
Definition xt := (t_constsym ("x"%string) t_ty).
Definition yt := (t_constsym ("y"%string) t_ty).
Definition zt := (t_constsym ("z"%string) t_ty).

Lemma xt_eq: Tfun (constsym "x" t_ty) nil nil = xt.
Proof. reflexivity. Qed.
Lemma yt_eq: Tfun (constsym "y" t_ty) nil nil = yt.
Proof. reflexivity. Qed.
Lemma zt_eq: Tfun (constsym "z" t_ty) nil nil = zt.
Proof. reflexivity. Qed.


Local Open Scope string_scope.

(*Here, our extra_simpl task folds up our defined constants*)
Ltac extra_simpl ::=
  fold t_ty; fold x; fold y; fold z;
  fold xt; fold yt; fold zt;
  try rewrite !xt_eq;
  try rewrite !yt_eq;
  try rewrite !zt_eq.

(*TODO: get some real notations*)
Lemma ring_theory_valid: valid_theory ring_theory.
Proof.
  simpl. split_all; auto.
  - (*First lemma*)
    wstart.  
    (*1.intros*)
    wintros "x".
    (*So now we have to prove for a specific x, that x * 0 = 0 *)
    (*2. assert (0 + 0 = 0)*)
    wassert "Hz" (Feq t_ty (0r +r 0r) 0r).
    {
      wrewrite["Unit_def_l" 0r].
      wreflexivity.
      (*Alternative (and faster)*)
      (*
      wspecialize "Unit_def_l" 0r.
      wassumption.*)
    }
    (*3. From this and f_equal, we can prove that x * (0 + 0) = x * 0*)
    wassert "Hz2" (Feq t_ty (xt *r (0r +r 0r)) (xt *r 0r)).
    {
      wf_equal.
      - wreflexivity.
      - wassumption.
    }
    (*4. we have that x * (0 + 0) = 0 + x * 0*)
    wassert "Hz3" (Feq t_ty (xt *r (0r +r 0r)) ((xt *r 0r) +r 0r)).
    {
      wrewrite "Hz2".
      wrewrite["Unit_def_r" (xt *r 0r)].
      wreflexivity.
      (*Alt (faster:)*)
      (*wspecialize "Unit_def_r" (xt *r 0r).
      wsymmetry.
      wassumption.*)
    }
    (*Alt:*)
    (* wrewrite["Mul_distr_l" xt 0r 0r]in "Hz3".*)
    wspecialize "Mul_distr_l" xt 0r 0r.
    wrewrite "Mul_distr_l" in "Hz3".
    (*Now we use cancellation*)
    wspecialize "add_cancel_l" (xt *r 0r) (xt *r 0r) 0r.
    wapply "add_cancel_l".
    wassumption.
    (*Yay!*)
  - (*Now we want to prove cancellation*)
    wstart.
    wintros "x" "y" "z" "Heq".
    wassert "Hsub" (Feq t_ty ((-r xt) +r (xt +r yt)) ((-r xt) +r (xt +r zt))).
    {
      wf_equal. wreflexivity. wassumption.
    }
    (*rewrite with associativity*)
    wrewrite<-["Assoc" (-r xt) xt yt]in "Hsub".
    wrewrite<-["Assoc" (-r xt) xt zt]in "Hsub".
    wrewrite["Inv_def_l" xt]in "Hsub".
    wrewrite["Unit_def_l" yt]in "Hsub".
    wrewrite["Unit_def_l" zt]in "Hsub".
    wassumption.
  - (*And an even easier goal*)
    wstart.
    wintros "x" "y" "Hxy".
    (*TODO: tactic for this (easy with f_equal)*)
    wassert "Heq" (Feq t_ty ((xt +r (-r yt)) +r yt) (0r +r yt)).
    {
      wf_equal. wassumption. wreflexivity.
    }
    wrewrite["Assoc" xt (-r yt) yt]in "Heq".
    wrewrite["Inv_def_l" yt]in "Heq".
    wrewrite["Unit_def_r" xt]in "Heq".
    wrewrite["Unit_def_l" yt]in "Heq".
    wassumption.
Qed.

End RingTheory.

End Alg.
