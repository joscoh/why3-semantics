Require Import TermFuncs Relations TermTactics.
From Proofs Require Import Task.
(*The conditions we have (e.g. evaluation) do not lend themseleves to nice
  decomposition, so we prove the results here*)

(*Patterns*)


Lemma eval_pat_tm {p e v} 
  (Hn: pat_node_of p = TermDefs.Pvar v)
  (Heval: eval_pat p = Some e):
  e = Pvar (eval_vsymbol v).
Proof.
  destruct_pat_node p. inversion Hn; subst. inversion Heval; subst; auto.
Qed.

Lemma eval_pat_app {p l ps e} (Hn: pat_node_of p = TermDefs.Papp l ps)
  (Heval: eval_pat p = Some e):
  exists l1 (*tys'*) tys1 ps1,
    e = Pconstr l1 tys1 ps1 /\ eval_funsym l = Some l1 /\
      (*fold_list_option (map pat_type ps) = Some tys' /\*)
      funpred_ty_list l1 (map pat_type ps) = Some tys1 /\
      fold_list_option (map eval_pat ps) = Some ps1.
Proof.
  destruct_pat_node p. inversion Hn; subst. apply option_bind_some in Heval.
  destruct Heval as [l1 [Heval Hbind]]. apply option_bind_some in Hbind.
  destruct Hbind as [ps1 [Hps Hbind]]. apply option_map_some in Hbind.
  destruct Hbind as [tys1 [Htys He]]; subst.
  exists l1. exists tys1. exists ps1. auto.
Qed.

Lemma eval_pat_or {p p1 p2 e} (Hn: pat_node_of p = TermDefs.Por p1 p2)
  (Heval: eval_pat p = Some e):
  exists e1 e2, e = Por e1 e2 /\ eval_pat p1 = Some e1 /\ eval_pat p2 = Some e2.
Proof.
  destruct_pat_node p. inversion Hn; subst. apply option_bind_some in Heval.
  destruct Heval as [e1 [Heval1 Hbind]]. apply option_bind_some in Hbind.
  destruct Hbind as [e2 [Heval2 Hbind]]. inversion Hbind; subst.
  eauto.
Qed.

Lemma eval_pat_as {p p1 v e} (Hn: pat_node_of p = TermDefs.Pas p1 v)
  (Heval: eval_pat p = Some e):
  exists p1', e = Pbind p1' (eval_vsymbol v) /\ eval_pat p1 = Some p1'.
Proof.
  destruct_pat_node p. inversion Hn; subst. apply option_bind_some in Heval. 
  destruct Heval as [p1' [Heval Hsome]]. inversion Hsome; subst.
  exists p1'; auto.
Qed.

Lemma eval_pat_wild {p e} (Hn: pat_node_of p = TermDefs.Pwild) (Heval: eval_pat p = Some e):
  e = Pwild.
Proof.
  destruct_pat_node p. inversion Heval; auto.
Qed.

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


(*TODO: should use option_map not bind but whatever*)
Lemma eval_match_tm {f1 t ps g1} (Hn: t_node_of f1 = Tcase t ps)
  (Heval: eval_term f1 = Some g1):
  exists t1 ty1 ps1, g1 = Tmatch t1 ty1 ps1 /\ eval_term t = Some t1 /\
    term_type t = Some ty1 /\ fold_list_option (map (fun x => option_bind (eval_pat (fst (fst x)))
      (fun p => option_bind (eval_term (snd x)) (fun t' => Some (p, t')))) ps) = Some ps1.
Proof.
  destruct_term_node f1. inversion Hn; subst; auto.
  apply option_bind_some in Heval. destruct Heval as [e1 [Heval1 Hbind]].
  apply option_bind_some in Hbind. destruct Hbind as [ty1 [Hty1 Hbind]].
  apply option_bind_some in Hbind. destruct Hbind as [ps1 [Hfold Hsome]].
  inversion Hsome; subst. eauto 10.
Qed.

Lemma eval_match_fmla {f1 t ps g1} (Hn: t_node_of f1 = Tcase t ps)
  (Heval: eval_fmla f1 = Some g1):
  exists t1 ty1 ps1, g1 = Fmatch t1 ty1 ps1 /\ eval_term t = Some t1 /\
    term_type t = Some ty1 /\ fold_list_option (map (fun x => option_bind (eval_pat (fst (fst x)))
      (fun p => option_bind (eval_fmla (snd x)) (fun t' => Some (p, t')))) ps) = Some ps1.
Proof.
  destruct_term_node f1. inversion Hn; subst; auto.
  apply option_bind_some in Heval. destruct Heval as [e1 [Heval1 Hbind]].
  apply option_bind_some in Hbind. destruct Hbind as [ty1 [Hty1 Hbind]].
  apply option_bind_some in Hbind. destruct Hbind as [ps1 [Hfold Hsome]].
  inversion Hsome; subst. eauto 10.
Qed.

Lemma eval_eps_tm {f1 tb g1} (Hn: t_node_of f1 = TermDefs.Teps tb)
  (Heval: eval_term f1 = Some g1):
  exists g2, g1 = Teps g2 (eval_vsymbol (fst (fst tb))) /\ eval_fmla (snd tb) = Some g2.
Proof.
  destruct_term_node f1. inversion Hn; subst. destruct tb as [[v1 b1] t1]; simpl in *.
  apply option_bind_some in Heval. destruct Heval as [g2 [Heval Hsome]]; inversion Hsome; subst.
  eauto.
Qed.

Lemma eval_eps_fmla {f1 tb g1} (Hn: t_node_of f1 = TermDefs.Teps tb)
  (Heval: eval_fmla f1 = Some g1):
  False.
Proof.
  destruct_term_node f1.
Qed.

Definition gen_quant (b: bool) : quant := if b then Tforall else Texists.

Definition gen_quants (b: bool) : list vsymbol -> formula -> formula :=
  if b then fforalls else fexists.

Definition is_forall q := match q with | TermDefs.Tforall => true | TermDefs.Texists => false end.

Lemma eval_quant_fmla {f1 q tq g1} (Hn: t_node_of f1 = Tquant q tq)
  (Heval: eval_fmla f1 = Some g1):
  exists g2, g1 = gen_quants (is_forall q)  
    (map eval_vsymbol (fst (fst (fst tq)))) g2 /\
    eval_fmla (snd tq) = Some g2.
Proof.
  destruct_term_node f1. inversion Hn; subst. destruct tq as [[[vs b] tr] f].
  simpl. apply option_bind_some in Heval. destruct Heval as [e1 [Heval1 Hsome]].
  inversion Hsome; subst. destruct q; eauto.
Qed.

Lemma eval_quant_tm {f1 q tq g1} (Hn: t_node_of f1 = Tquant q tq)
  (Heval: eval_term f1 = Some g1):
  False.
Proof.
  destruct_term_node f1.
Qed.

Lemma eval_binop_fmla {f1 b t1 t2 g1} (Hn: t_node_of f1 = TermDefs.Tbinop b t1 t2)
  (Heval: eval_fmla f1 = Some g1):
  exists e1 e2, g1 = Fbinop (eval_binop b) e1 e2 /\ eval_fmla t1 = Some e1 /\ eval_fmla t2 = Some e2.
Proof.
  destruct_term_node f1. inversion Hn; subst. apply option_bind_some in Heval.
  destruct Heval as [e1 [He1 Hbind]]. apply option_bind_some in Hbind. destruct Hbind as [e2 [He2 Hsome]].
  inversion Hsome; subst. eauto.
Qed.

Lemma eval_binop_tm {f1 b t1 t2 g1} (Hn: t_node_of f1 = TermDefs.Tbinop b t1 t2)
  (Heval: eval_term f1 = Some g1):
  False.
Proof. destruct_term_node f1. Qed.

Lemma eval_not_fmla {f1 f2 g1} (Hn: t_node_of f1 = TermDefs.Tnot f2) (Heval: eval_fmla f1 = Some g1):
  exists g2, g1 = Fnot g2 /\ eval_fmla f2 = Some g2.
Proof.
  destruct_term_node f1. inversion Hn; subst. apply option_bind_some in Heval.
  destruct Heval as [g2 [Heval1 Hsome]]; inversion Hsome; eauto.
Qed.

Lemma eval_not_tm {f1 f2 g1} (Hn: t_node_of f1 = TermDefs.Tnot f2) (Heval: eval_term f1 = Some g1):
  False.
Proof. destruct_term_node f1. Qed.

Lemma eval_true_fmla {f1 g1} (Hn: t_node_of f1 = TermDefs.Ttrue) (Heval: eval_fmla f1 = Some g1):
  g1 = Ftrue.
Proof.
  destruct_term_node f1. inversion Heval; auto.
Qed.

Lemma eval_false_fmla {f1 g1} (Hn: t_node_of f1 = TermDefs.Tfalse) (Heval: eval_fmla f1 = Some g1):
  g1 = Ffalse.
Proof.
  destruct_term_node f1. inversion Heval; auto.
Qed.

Lemma eval_true_tm {f1 g1} (Hn: t_node_of f1 = TermDefs.Ttrue) (Heval: eval_term f1 = Some g1):
  False.
Proof. destruct_term_node f1. Qed.

Lemma eval_false_tm {f1 g1} (Hn: t_node_of f1 = TermDefs.Tfalse) (Heval: eval_term f1 = Some g1):
  False.
Proof. destruct_term_node f1. Qed.

End EvalInv.
