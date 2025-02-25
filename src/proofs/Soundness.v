(*Here we give the definition of soundness for transformations
  in the errState monad: if the initial state if wf, then if the resulting
  task(s) is/are valid, so is the initial one.*)
From Proofs Require Import Task.
Require Import Relations ErrStateHoare StateInvar RelationProofs.
Require Import TaskDefs TransDefs.
Set Bullet Behavior "Strict Subproofs".

(*Version for single tarns (not list)*)
(*NOTE: here, we do not require that the output is wf. We can prove that separately*)
Definition trans_errst_sound (trans: trans_errst task) : Prop :=
  forall (t: task),
  (*put typing in precondition, some may be ill-defined without typing (though should just
    be error which is OK because partial correctness)*)
  errst_spec (fun s => st_wf t s /\ typed_task t) (trans t)
    (fun (s1: full_st) (r: task) (s2: full_st) =>
      valid_task r ->
      valid_task t).

(*Version for lists*)
Definition trans_errst_list_sound (trans: trans_errst (list task)) : Prop :=
  forall (t: task),
  errst_spec (fun s => st_wf t s) (trans t)
    (fun (s1: full_st) (r: list task) (s2: full_st) =>
      Forall valid_task r ->
      valid_task t).

(*This definition is not terribly useful. Instead, we want to show
  that the transformation relates to a stateless one in the core language
  that is sound. We show that this condition implies soundness*)




(*Here, just prove that related inputs -> related outputs, purely syntactic reasoning*)
Theorem prove_trans_errst_decompose (trans: trans_errst task) (tr1: Task.task -> Task.task):
  sound_trans (single_trans tr1) ->
  (forall tsk1 tsk2,
    errst_spec (fun s => st_wf tsk1 s /\ task_related tsk1 tsk2) (trans tsk1)
      (fun _ r _ => task_related r (tr1 tsk2))) ->
  trans_errst_sound trans.
Proof.
  unfold sound_trans, TaskGen.sound_trans . intros Htrans Hrel.
  unfold trans_errst_sound.
  intros t.
  unfold typed_task.
  destruct (eval_task t) as [t1|] eqn : Htask.
  2: { apply (errst_spec_weaken_pre) with (P1:= fun _ => False).
    - intros; destruct_all; discriminate.
    - unfold errst_spec. contradiction.
  }
  assert (Htaskrel: task_related t t1). {
    unfold task_related. exists t1. split; auto. apply a_equiv_task_refl.
  }
  specialize (Hrel t t1).
  apply errst_spec_weaken_pre with (P1:=fun s => st_wf t s /\ task_typed t1).
  { intros i. intros; destruct_all; subst. inversion H0; subst; auto. }
  (*Now just unfold errst_spec - not great*)
  unfold errst_spec in *.
  intros i b [Hwf Hty] Hrun.
  specialize (Hrel i b (conj Hwf Htaskrel) Hrun).
  (*Now use soundness result*)
  specialize (Htrans _ Hty).
  unfold single_trans in Htrans. simpl in Htrans.
  intros Hvalb.
  forward Htrans.
  { intros tr [Htr | []]. subst. 
    pose proof (task_related_valid b (tr1 t1) Hrel) as Hvaliff.
    apply Hvaliff; auto.
  }
  pose proof (task_related_valid t t1 Htaskrel) as Hvaliff.
  apply Hvaliff; auto.
Qed.
  