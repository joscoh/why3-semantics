(*An example of how to prove soundness of stateful functions:

We use a version of [eliminate_let], as implemented in proofs/transform/eliminate_let.v.
Notably, this is NOT why3's version (which we proved sound), which has a nontrivial 
termination argument. Instead, we substitute only on subterms. Also, it only eliminates
let-bindings in goals, not elsewhere, this simplifies things a bit.
The primary proof goal is to relate stateless and stateful substitution (which is
really the primary difference between the two layers) so it does encompass the main
difficulties.
*)
Require Import TaskDefs.
Require Import TermTraverse.

(*First, define the stateful transformation*)

Import MonadNotations.

Local Open Scope errst_scope.

(*Simple: eliminate all*)
Check term_map.
Definition elim_let_rewrite (t: term_c) : errState (CoqBigInt.t * hashcons_full) term_c :=
  term_map hashcons_full
  (*let is only interesting one*)
  (fun t1 t2 t3 v r1 r2 =>
    t_subst_single1 v r1 r2)
  (tmap_if_default _)
  (tmap_app_default _)
  (tmap_match_default _)
  (tmap_eps_default _)
  (tmap_quant_default _)
  (tmap_binop_default _)
  (tmap_not_default _)
  t.

(*And the transformation*)


(*Change decl in task_hd*)

Definition change_tdecl_node (t: tdecl_c) (new: tdecl_node) : tdecl_c :=
  mk_tdecl_c new (td_tag_of t).

Definition change_tdecl_c (t: task_hd) (new: tdecl_c) : task_hd :=
  mk_task_head new (task_prev t) (task_known t) (task_clone t) (task_meta t) (task_tag t).

Definition change_decl_node (d: decl) (new: decl_node) : decl :=
  build_decl new (d_news d) (d_tag d).

(*NOTE: assuming goal is at the end (just like with eval)*)
Definition rewrite_goal {St} (f: prsymbol -> term_c -> errState St term_c)
  (t: task_hd) : errState St task_hd :=
  match (td_node_of (task_decl t)) with
  | Decl d =>
    match d_node d with
      | Dprop x =>
        let '(k, pr, f1) := of_tup3 x in
        match k with
        | Pgoal => 
          f2 <- f pr f1 ;;
          errst_ret (change_tdecl_c t (change_tdecl_node (task_decl t) (Decl (change_decl_node d (Dprop (k, pr, f2))))))
        | _ => (*dont do anything*) errst_ret t
        end
      | _ => errst_ret t
      end
  | _ => errst_ret t
  end.

Definition elim_let_aux (t: task_hd) : errState (CoqBigInt.t * hashcons_full) task_hd :=
  rewrite_goal (fun _ => elim_let_rewrite) t.

Require Import TransDefs.

Definition lift_trans (f: task_hd -> errState (CoqBigInt.t * hashcons_full) task_hd) :
  trans_errst task :=
  fun t => 
    match t with
    | None => errst_ret None
    | Some t => x <- f t;; errst_ret (Some x)
    end.

Definition elim_let : trans_errst task := lift_trans elim_let_aux.
Set Bullet Behavior "Strict Subproofs".
(*Soundness*)
Require Import Relations ErrStateHoare StateInvar Soundness.
Require Import eliminate_let.
Check trans_errst.

(*The main part: prove related*)
Theorem elim_let_related (tsk1 : task) (tsk2 : Task.task):
errst_spec
  (fun s : full_st => st_wf tsk1 s /\ task_related tsk1 tsk2)
  (elim_let tsk1)
  (fun (_ : full_st) (r : task) (_ : full_st) =>
   task_related r (single_goal (elim_let_f true true) tsk2)).
Proof.
  (*need to do induction on formula*)
  (*Next steps:
    1. prove we can move [task_related] out of condition (or maybe just change decomp?
    2. unfold tasks, get elim_let and elim_let_f just on goal,
      then need to get formulas, do induction on formulas
      will need to reason about eval, related, and results via induction
      do not want to unfold errst_spec if possible so we can prove intermediate results
  unfold task_related at 1.
  unfold errst_spec.




Theorem elim_let_sound: trans_errst_sound elim_let.
Proof.
  apply prove_trans_errst_decompose with (tr1:=single_goal (elim_let_f true true)).
  - (*already proved soundness*) apply elim_let_sound. 
  - (*Now prove related*)


