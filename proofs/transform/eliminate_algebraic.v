
Require Import Task.
Require Import Pattern PatternProofs Alpha.
Set Bullet Behavior "Strict Subproofs".

(*TODO: does this work?*)
Section Map.
Variable (fn: term -> term) (pn: formula -> formula).

Definition t_map  (t: term) : term :=
  match t with
  | Tlet ta x tb => Tlet (fn ta) x (fn tb)
  | Tmatch t1 ty ps =>
    Tmatch (fn t1) ty (map (fun x => (fst x, fn (snd x))) ps)
  | Teps f x => Teps (pn f) x
  | Tif f t1 t2 => Tif (pn f) (fn t1) (fn t2)
  | Tfun f tys tms => Tfun f tys (map fn tms)
  | Tconst _ => t
  | Tvar _ => t
  end.
Definition f_map (f: formula) : formula :=  
  match f with
  | Flet t x f => Flet (fn t) x (pn f)
  | Fmatch t ty ps => Fmatch (fn t) ty (map (fun x => (fst x, pn (snd x))) ps)
  | Fif f1 f2 f3 => Fif (pn f1) (pn f2) (pn f3)
  | Fpred f tys tms => Fpred f tys (map fn tms)
  | Fnot f => Fnot (pn f)
  | Feq ty t1 t2 => Feq ty (fn t1) (fn t2)
  | Fbinop b f1 f2 => Fbinop b (pn f1) (pn f2)
  | Fquant q v f => Fquant q v (pn f)
  | Ftrue => Ftrue
  | Ffalse => Ffalse
  end.

End Map.


(** Compile match patterns *)

Fixpoint rewriteT (t: term) : term :=
  match t with
  | Tmatch tm ty ps =>
    let t1 := rewriteT tm in
    match (compile_bare_single true t1 ty 
      (map (fun x => (fst x, rewriteT (snd x))) ps)) with
    | Some t2 => t2
    | None => t
    end
  | _ => t_map rewriteT rewriteF t
  end
with rewriteF (f: formula) : formula :=
  match f with
  | Fmatch t ty ps =>
    let t1 := rewriteT t in
    match (compile_bare_single false t1 ty 
      (map (fun x => (fst x, rewriteF (snd x))) ps)) with
    | Some t2 => t2
    | None => f
    end
  | _ => f_map rewriteT rewriteF f
  end.

Definition rewriteT' t := rewriteT (a_convert_all_t t nil).
Definition rewriteF' f := rewriteF (a_convert_all_f f nil).

(*And the transformation*)
Definition compile_match : trans := trans_map rewriteT' rewriteF'.

(*Proofs*)
(* 
(*1. Typing*)
Lemma rewrite_typed gamma t f:
  (forall ty (Hty: term_has_type gamma t ty),
    term_has_type gamma (rewriteT t) ty) /\
  (forall (Hty: formula_typed gamma f),
    formula_typed gamma (rewriteF f)).
Proof.
  revert t f; apply term_formula_ind; simpl; auto;
  try solve[intros; inversion Hty; subst; constructor; auto].
  - (*Tfun*) intros f1 tys tms IH ty Hty.
    inversion Hty; subst.
    constructor; auto.
    + rewrite map_length; auto.
    + assert (Hlen: length tms = length (map (ty_subst (s_params f1) tys) (s_args f1))).
      { rewrite map_length; auto. }
      generalize dependent (map (ty_subst (s_params f1) tys) (s_args f1)).
      revert IH.
      clear.
      induction tms as [| thd ttl IH]; intros Hall [| tyh tyt]; auto;
      try discriminate; simpl.
      intros Hall2 Hlen.
      inversion Hall; subst. inversion Hall2; subst.
      constructor; auto.
  - (*Tmatch*)
    intros tm ty ps IHtm IHps ty1 Hty1.
    destruct (compile_bare_single _ _ _ _) as [o1|] eqn : Hcompile; auto.
    (*2nd case cannot occur by typing but we don't prove that yet*)
    unfold compile_bare_single in Hcompile.
    eapply compile_bare_typed in Hcompile; eauto.
    Search compile_bare.
  - intros; inversion Hty; subst; constructor; auto.


(*2: Semantics*)

(*3: Simple patterns*)


    
     t ty:
  term_has_type gamma t ty ->
  term_has_type gamma (rewriteT t) ty.
Proof.
  unfold rewriteT.

Lemma compile_match_sound: sound_trans compile_match.
Proof.
  unfold compile_match.
  apply trans_map_sound. *)


