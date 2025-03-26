Require Import TermFuncs Relations TermTactics.
From Proofs Require Import Task.
(*The conditions we have (e.g. evaluation) do not lend themseleves to nice
  decomposition, so we prove the results here*)

(*TODO: move these*)

(*Inversion Lemmas for eval*)
Section EvalInv.

(*Const*)

Lemma eval_const_tm {f1 g1 c} 
  (Hn: t_node_of f1 = TermDefs.Tconst c)
  (Heval: eval_term f1 = Some g1):
  exists c1, g1 = Tconst c1 /\ eval_const c = Some c1.
Proof.
  destruct_term_node f1. apply option_map_some in Heval. inversion Hn; subst. 
  destruct Heval as [c1 [Heval Hg1]]; subst. eauto.
Qed.

Lemma eval_const_fmla {f1 g1 c} 
  (Hn: t_node_of f1 = TermDefs.Tconst c)
  (Heval: eval_fmla f1 = Some g1):
  False.
Proof.
  destruct_term_node f1.
Qed.

(*var*)
Lemma eval_var_tm {f1 g1 v} 
  (Hn: t_node_of f1 = TermDefs.Tvar v)
  (Heval: eval_term f1 = Some g1):
  g1 = Tvar (eval_vsymbol v).
Proof.
  destruct_term_node f1. inversion Heval; subst; auto. inversion Hn; subst; auto.
Qed.

Lemma eval_var_fmla {f1 g1 v} 
  (Hn: t_node_of f1 = TermDefs.Tvar v)
  (Heval: eval_fmla f1 = Some g1):
  False.
Proof.
  destruct_term_node f1.
Qed.

(*if*)

Lemma eval_if_tm {f1 g1 t1 t2 t3} 
  (Hn: t_node_of f1 = TermDefs.Tif t1 t2 t3)
  (Heval: eval_term f1 = Some g1):
  exists e1 e2 e3, g1 = Tif e1 e2 e3 /\ eval_fmla t1 = Some e1 /\ eval_term t2 = Some e2 /\
    eval_term t3 = Some e3.
Proof.
  destruct_term_node f1.
  inversion Hn; subst; clear Hn.
  apply option_bind_some in Heval. destruct Heval as [e1 [He1 Hbind]].
  apply option_bind_some in Hbind. destruct Hbind as [e2 [He2 Hbind]].
  apply option_bind_some in Hbind. destruct Hbind as [e3 [He3 Hbind]].
  inversion Hbind; subst. eauto 10.
Qed.

Lemma eval_if_fmla {f1 g1 t1 t2 t3} 
  (Hn: t_node_of f1 = TermDefs.Tif t1 t2 t3)
  (Heval: eval_fmla f1 = Some g1):
  exists e1 e2 e3, g1 = Fif e1 e2 e3 /\ eval_fmla t1 = Some e1 /\ eval_fmla t2 = Some e2 /\
    eval_fmla t3 = Some e3.
Proof.
  destruct_term_node f1.
  inversion Hn; subst; clear Hn.
  apply option_bind_some in Heval. destruct Heval as [e1 [He1 Hbind]].
  apply option_bind_some in Hbind. destruct Hbind as [e2 [He2 Hbind]].
  apply option_bind_some in Hbind. destruct Hbind as [e3 [He3 Hbind]].
  inversion Hbind; subst. eauto 10.
Qed.



(*app - trickier: can become Tfun, Fpred, or Feq*)

Lemma eval_app_tm {f1 g1 l ts}
  (Hn: t_node_of f1 = TermDefs.Tapp l ts)
  (Heval: eval_term f1 = Some g1):
  exists l1 tys' tys1 ts1,
    g1 = Tfun l1 tys1 ts1 /\ eval_funsym l = Some l1 /\
      fold_list_option (map term_type ts) = Some tys' /\
      funpred_ty_list l1 tys' = Some tys1 /\
      fold_list_option (map eval_term ts) = Some ts1.
Proof.
  destruct_term_node f1.
  inversion Hn; subst; clear Hn.
  apply option_bind_some in Heval. destruct Heval as [l1 [Hl1 Hbind]]. exists l1.
  apply option_bind_some in Hbind. destruct Hbind as [ts1 [Hts1 Hbind]].
  apply option_bind_some in Hbind. destruct Hbind as [tys' [Htsys' Hbind]].
  apply option_map_some in Hbind. destruct Hbind as [tys1 [Htys1 Hg1]]; subst; eauto 10.
Qed.

Lemma eval_app_fmla {f1 g1 l ts}
  (Hn: t_node_of f1 = TermDefs.Tapp l ts)
  (Heval: eval_fmla f1 = Some g1):
  (l = ps_equ /\ exists t1 t2 t3 t4 ty1, ts = [t1 ; t2] /\ g1 = Feq ty1 t3 t4 /\
    eval_term t1 = Some t3 /\ eval_term t2 = Some t4 /\ term_type t1 = Some ty1) \/
  l <> ps_equ /\
  exists l1 tys' tys1 ts1,
    g1 = Fpred l1 tys1 ts1 /\ eval_predsym l = Some l1 /\
      fold_list_option (map term_type ts) = Some tys' /\
      funpred_ty_list l1 tys' = Some tys1 /\
      fold_list_option (map eval_term ts) = Some ts1.
Proof.
  destruct_term_node f1.
  inversion Hn; subst; clear Hn.
  destruct (lsymbol_eqb l ps_equ) eqn : Heq.
  - assert (l = ps_equ). apply lsymbol_eqb_eq; auto. subst.
    left. destruct ts as [| t1 [| t2 [| ? ?]]]; try discriminate.
    split; auto. exists t1. exists t2. 
    apply option_bind_some in Heval. destruct Heval as [t3 [Ht3 Hbind]].
    apply option_bind_some in Hbind. destruct Hbind as [t4 [Ht4 Hbind]].
    apply option_bind_some in Hbind. destruct Hbind as [ty1 [Hty1 Hbind]].
    inversion Hbind; subst. eauto 10.
  - assert (l <> ps_equ).
    { intro C; subst. assert (Ht: lsymbol_eqb ps_equ ps_equ) by (apply lsymbol_eqb_eq; auto).
      rewrite Ht in Heq; discriminate.
    }
    right. split; auto.
    apply option_bind_some in Heval. destruct Heval as [l1 [Hl1 Hbind]]. exists l1.
    apply option_bind_some in Hbind. destruct Hbind as [ts1 [Hts1 Hbind]].
    apply option_bind_some in Hbind. destruct Hbind as [tys' [Htsys' Hbind]].
    apply option_map_some in Hbind. destruct Hbind as [tys1 [Htys1 Hg1]]; subst; eauto 10.
Qed.

(*let*)

Lemma eval_let_tm {f1 g1 t1 tb1} 
  (Hn: t_node_of f1 = TermDefs.Tlet t1 tb1)
  (Heval: eval_term f1 = Some g1):
  exists e1 e2, g1 = Tlet e1 (eval_vsymbol (fst (fst tb1))) e2 /\
    eval_term t1 = Some e1 /\ eval_term (snd tb1) = Some e2.
Proof.
  destruct_term_node f1.
  inversion Hn; subst; clear Hn.
  destruct tb1 as [[v1 b1] t2]; simpl.
  apply option_bind_some in Heval. destruct Heval as [e1 [He1 Hbind]].
  apply option_bind_some in Hbind. destruct Hbind as [e2 [He2 Hbind]].
  inversion Hbind; subst. eauto 10.
Qed.

Lemma eval_let_fmla {f1 g1 t1 tb1} 
  (Hn: t_node_of f1 = TermDefs.Tlet t1 tb1)
  (Heval: eval_fmla f1 = Some g1):
  exists e1 e2, g1 = Flet e1 (eval_vsymbol (fst (fst tb1))) e2 /\
    eval_term t1 = Some e1 /\ eval_fmla (snd tb1) = Some e2.
Proof.
  destruct_term_node f1.
  inversion Hn; subst; clear Hn.
  destruct tb1 as [[v1 b1] t2]; simpl.
  apply option_bind_some in Heval. destruct Heval as [e1 [He1 Hbind]].
  apply option_bind_some in Hbind. destruct Hbind as [e2 [He2 Hbind]].
  inversion Hbind; subst. eauto 10.
Qed.

End EvalInv.
