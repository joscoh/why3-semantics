(*Here we give the definition of soundness for transformations
  in the errState monad: if the initial state if wf, then if the resulting
  task(s) is/are valid, so is the initial one.*)
From Proofs Require Import Task.
Require Import Relations ErrStateHoare StateInvar.
Require Import TaskDefs TransDefs.

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


(*TODO: maybe I don't actually need var alpha for funpred_def -
  my [open_ls_defn] is stateless, so we should never actually change
  If I change this, should be easy I believe*)


(*Here, just prove that related inputs -> related outputs, purely syntactic reasoning*)
Lemma prove_trans_errst_sound (trans: trans_errst task) (tr1: Task.task -> Task.task):
  sound_trans (single_trans tr1) ->
  (forall tsk1 tsk2,
    errst_spec (fun s => st_wf tsk1 s /\ task_related tsk1 tsk2) (trans tsk1)
      (fun _ r _ => task_related r (tr1 tsk2))) ->
  trans_errst_sound trans.
Proof.
  unfold sound_trans, TaskGen.sound_trans . intros Htrans Hrel.
  unfold trans_errst_sound.
  intros t.
  (*Idea: look at [eval_task] t, know in precondition it (t1) is well-typed,
    and know that [task_related t t1], so 
    then, have precondition of Hrel, then know task_related r (tr1 t1),
    use trans to know that t1 is valid, then use task_valid result to combine*)
Admitted.


  