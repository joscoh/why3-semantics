Require Import TermDefs StateInvar TermTactics.

(*Decompose state invariant into pieces of each term*)

(*Decompose wf*)
Lemma term_st_wf_if {t t1 t2 t3} (Ht: t_node_of t = TermDefs.Tif t1 t2 t3):
  forall s,
  term_st_wf t s <-> term_st_wf t1 s /\ term_st_wf t2 s /\ term_st_wf t3 s /\  ty_st_wf (t_ty_of t) s.
Proof.
  intros s.
  unfold term_st_wf, ty_st_wf.
  (*Easier to separate - can we generalize?*)
  assert (Hidents: idents_of_term_wf t s <-> idents_of_term_wf t1 s /\ idents_of_term_wf t2 s /\
    idents_of_term_wf t3 s).
  {
    destruct_term_node t. inversion Ht; subst. unfold idents_of_term_wf; simpl.
    repeat (setoid_rewrite in_app_iff).
    split.
    - intros Hin. split_all; intros i Hini; apply Hin; auto.
    - intros [Hin1 [Hin2 Hin3]] i Hini. destruct_all; eauto.
  }
  assert (Hhash: term_hash_wf t s <-> term_hash_wf t1 s /\ term_hash_wf t2 s /\ term_hash_wf t3 s /\ ty_hash_wf (t_ty_of t) s).
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
  term_st_wf t s <-> term_st_wf t1 s /\ term_st_wf (snd tb) s /\ vsym_st_wf (fst (fst tb)) s /\ ty_hash_wf (t_ty_of t) s.
Proof.
  intros s. destruct tb as [[v1 b1] t2]. simpl.
  unfold term_st_wf, vsym_st_wf.
  assert (Hidents: idents_of_term_wf t s <-> idents_of_term_wf t1 s /\ idents_of_term_wf t2 s /\
    vsym_ident_wf v1 s).
  {
    destruct_term_node t. inversion Ht; subst. unfold idents_of_term_wf, vsym_ident_wf; simpl.
    repeat (setoid_rewrite in_app_iff).
    split.
    - intros Hin. split_all; auto.
    - intros; destruct_all; eauto.
  }
  assert (Hhash: term_hash_wf t s <-> term_hash_wf t1 s /\ term_hash_wf t2 s /\ vsym_hash_wf v1 s /\ ty_hash_wf (t_ty_of t) s).
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