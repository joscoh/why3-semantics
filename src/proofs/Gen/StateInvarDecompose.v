Require Import TermDefs StateInvar TermTactics.
Set Bullet Behavior "Strict Subproofs".

(*Decompose state invariant into pieces of each term*)


(*TODO: move*)
Lemma idents_of_term_rewrite t :
  idents_of_term t = match t_node_of t with
  | Tvar v => [vs_name v]
  | Tapp _ ts => concat (map idents_of_term ts)
  | Tif t1 t2 t3 => idents_of_term t1 ++ idents_of_term t2 ++ idents_of_term t3
  | Tlet t1 (v, _, t2) => vs_name v :: idents_of_term t1 ++ idents_of_term t2
  | Tcase t1 ps =>
      idents_of_term t1 ++
      concat
        (map
           (fun x : pattern_c * bind_info * term_c =>
            idents_of_pattern (fst (fst x)) ++ idents_of_term (snd x)) ps)
  | Teps (v, _, t0) => vs_name v :: idents_of_term t0
  | Tquant _ (vs, _, _, t0) => map vs_name vs ++ idents_of_term t0
  | Tbinop _ t1 t2 => idents_of_term t1 ++ idents_of_term t2
  | Tnot t0 => idents_of_term t0
  | _ => []
  end
.
Proof.
destruct t;
reflexivity.
Qed.

(*Decompose wf*)
Lemma term_st_wf_if {t t1 t2 t3} (Ht: t_node_of t = TermDefs.Tif t1 t2 t3):
  forall s,
  term_st_wf t s <-> term_st_wf t1 s /\ term_st_wf t2 s /\ term_st_wf t3 s /\  ty_st_wf (t_ty_of t) s.
Proof.
  intros s.
  unfold term_st_wf, ty_st_wf.
  (*Easier to separate - can we generalize?*)
  assert (Hidents: idents_of_term_wf t (fst s) <-> idents_of_term_wf t1 (fst s) /\ idents_of_term_wf t2 (fst s) /\
    idents_of_term_wf t3 (fst s)).
  {
    unfold idents_of_term_wf. setoid_rewrite idents_of_term_rewrite at 1. rewrite Ht. 
    repeat (setoid_rewrite in_app_iff).
    split.
    - intros Hin. split_all; intros i Hini; apply Hin; auto.
    - intros [Hin1 [Hin2 Hin3]] i Hini. destruct_all; eauto.
  }
  assert (Hhash: term_hash_wf t (snd s) <-> term_hash_wf t1 (snd s) /\ term_hash_wf t2 (snd s) /\ 
    term_hash_wf t3 (snd s) /\ ty_hash_wf (t_ty_of t) (snd s)).
  {
    unfold term_hash_wf, ty_hash_wf, gen_hash_wf. destruct_term_node t; inversion Ht; subst; simpl.
    rewrite !map_app, !concat_app. unfold all_in_hashtable, all_idents_smaller.
    repeat (setoid_rewrite in_app_iff).
    split.
    - intros [Hi1 Hi2]. split_all; eauto.
    - intros; destruct_all; split; intros; destruct_all; eauto.
  }
  rewrite Hidents, Hhash.
  split; intros; destruct_all; split_all; auto.
Qed.

Lemma term_st_wf_let {t t1 tb} (Ht: t_node_of t = TermDefs.Tlet t1 tb):
  forall s,
  term_st_wf t s <-> term_st_wf t1 s /\ term_st_wf (snd tb) s /\ vsym_st_wf (fst (fst tb)) s /\ ty_hash_wf (t_ty_of t) (snd s).
Proof.
  intros s. destruct tb as [[v1 b1] t2]. simpl.
  unfold term_st_wf, vsym_st_wf.
  assert (Hidents: idents_of_term_wf t (fst s) <-> idents_of_term_wf t1 (fst s) /\ idents_of_term_wf t2 (fst s) /\
    vsym_ident_wf v1 (fst s)).
  {
    destruct_term_node t. inversion Ht; subst. unfold idents_of_term_wf, vsym_ident_wf; simpl.
    repeat (setoid_rewrite in_app_iff).
    split.
    - intros Hin. split_all; auto.
    - intros; destruct_all; eauto.
  }
  assert (Hhash: term_hash_wf t (snd s) <-> term_hash_wf t1 (snd s) /\ term_hash_wf t2 (snd s) /\ vsym_hash_wf v1 (snd s) 
      /\ ty_hash_wf (t_ty_of t) (snd s)).
  {
    unfold term_hash_wf, ty_hash_wf, vsym_hash_wf, gen_hash_wf. destruct_term_node t; inversion Ht; subst; simpl.
    rewrite !map_app, !concat_app. unfold all_in_hashtable, all_idents_smaller.
    repeat (setoid_rewrite in_app_iff).
    split.
    - intros [Hi1 Hi2]. split_all; eauto.
    - intros; destruct_all; split; intros; destruct_all; eauto.
  }
  rewrite Hidents, Hhash.
  split; intros; destruct_all; split_all; auto.
Qed.

Lemma term_st_wf_binop {t b t1 t2} (Ht: t_node_of t = TermDefs.Tbinop b t1 t2):
  forall s,
  term_st_wf t s <-> term_st_wf t1 s /\ term_st_wf t2 s /\ ty_st_wf (t_ty_of t) s.
Proof.
  intros s.
  unfold term_st_wf, ty_st_wf.
  assert (Hidents: idents_of_term_wf t (fst s) <-> idents_of_term_wf t1 (fst s) /\ idents_of_term_wf t2 (fst s)).
  {
    unfold idents_of_term_wf. setoid_rewrite idents_of_term_rewrite at 1. rewrite Ht. 
    repeat (setoid_rewrite in_app_iff).
    split.
    - intros Hin. split_all; intros i Hini; apply Hin; auto.
    - intros [Hin1 Hin2] i Hini. destruct_all; eauto.
  }
  assert (Hhash: term_hash_wf t (snd s) <-> term_hash_wf t1 (snd s) /\ term_hash_wf t2 (snd s) (*/\ 
    term_hash_wf t3 (snd s)*) /\ ty_hash_wf (t_ty_of t) (snd s)).
  {
    unfold term_hash_wf, ty_hash_wf, gen_hash_wf. destruct_term_node t; inversion Ht; subst; simpl.
    rewrite !map_app, !concat_app. unfold all_in_hashtable, all_idents_smaller.
    repeat (setoid_rewrite in_app_iff).
    split.
    - intros [Hi1 Hi2]. split_all; eauto.
    - intros; destruct_all; split; intros; destruct_all; eauto.
  }
  rewrite Hidents, Hhash.
  split; intros; destruct_all; split_all; auto.
Qed.


Lemma term_st_wf_not {t t1} (Ht: t_node_of t = TermDefs.Tnot t1):
  forall s,
  term_st_wf t s <-> term_st_wf t1 s /\ ty_st_wf (t_ty_of t) s.
Proof.
  intros s.
  unfold term_st_wf, ty_st_wf.
  assert (Hidents: idents_of_term_wf t (fst s) <-> idents_of_term_wf t1 (fst s)).
  {
    unfold idents_of_term_wf. setoid_rewrite idents_of_term_rewrite at 1; rewrite Ht. reflexivity.
  }
  assert (Hhash: term_hash_wf t (snd s) <-> term_hash_wf t1 (snd s) (*/\ 
    term_hash_wf t3 (snd s)*) /\ ty_hash_wf (t_ty_of t) (snd s)).
  {
    unfold term_hash_wf, ty_hash_wf, gen_hash_wf. destruct_term_node t; inversion Ht; subst; simpl.
    rewrite !map_app, !concat_app. unfold all_in_hashtable, all_idents_smaller.
    repeat (setoid_rewrite in_app_iff).
    split.
    - intros [Hi1 Hi2]. split_all; eauto.
    - intros; destruct_all; split; intros; destruct_all; eauto.
  }
  rewrite Hidents, Hhash.
  split; intros; destruct_all; split_all; auto.
Qed.




