(* Require Import Typing.

(*An alternate termination check*)
Print pat_constr_vars.
Print pat_constr_vars_inner.
(*Get all smaller vars in pattern match*)
Fixpoint pat_vars_inner (p: pattern) : list vsymbol :=
  match p with
  | Pconstr c tys ps => big_union vsymbol_eq_dec pat_vars_inner ps
  | Por p1 p2 => intersect vsymbol_eq_dec 
    (pat_vars_inner p1) (pat_vars_inner p2)
  | Pwild => nil
  | Pbind p' y => union vsymbol_eq_dec [y] (pat_vars_inner p')
  | Pvar v => [v]
  end.

(*TODO: is this right?*)
Fixpoint pat_vars_smaller (p: pattern) : list vsymbol :=
  match p with
  | Pconstr c tys ps => pat_fv p
  | Por p1 p2 => intersect vsymbol_eq_dec (pat_vars_smaller p1)
      (pat_vars_smaller p2)
  | Pwild => nil
  | Pbind p' _ => pat_vars_smaller p'
  | Pvar _ => nil
  end.
Unset Elimination Schemes.
Inductive decrease_fun' (fs: list fn) (ps: list pn) : 
  list vsymbol -> option vsymbol -> term -> Prop :=
  (*Before any of the constructor cases, if none of fs or ps appear
    in t, then t is trivially a decreasing function*)
  | Dec_notin_t: forall (small: list vsymbol) (hd: option vsymbol) (t: term),
    (forall (f: fn), In f fs -> negb (funsym_in_tm (fn_sym f) t)) ->
    (forall p, In p ps -> negb (predsym_in_tm (pn_sym p) t)) ->
    decrease_fun' fs ps small hd t
  (*First, the recursive function call case*)
  | Dec_fun_in: forall (small: list vsymbol) (hd: option vsymbol) 
    (f: funsym) (f_decl: fn) (l: list vty) (ts: list term) (x: vsymbol),
    In f_decl fs ->
    f = fn_sym f_decl ->
    (*The decreasing argument is a variable in our list of decreasing terms*)
    In x small ->
    nth (sn_idx f_decl) ts tm_d = Tvar x ->
    (*Uniformity: we must be applying the function uniformly*)
    l = map vty_var (s_params f) ->
    (*None of [fs] of [ps] appear in the terms*) 
    Forall (fun t => forall f,  In f fs -> negb (funsym_in_tm (fn_sym f) t)) ts ->
    Forall (fun t => forall p, In p ps -> negb (predsym_in_tm (pn_sym p) t)) ts ->
    (*Then this recursive call is valid*)
    decrease_fun' fs ps small hd (Tfun f l ts)
  (*Other function call*)
  | Dec_fun_notin: forall (small: list vsymbol) (hd: option vsymbol)
    (f: funsym) (l: list vty) (ts: list term),
    ~ In f (map fn_sym fs) ->
    (*In this case, just recursive*)
    (*Forall doesn't give ind principle*)
    (forall t, In t ts -> (decrease_fun' fs ps small hd t)) ->
    decrease_fun' fs ps small hd (Tfun f l ts)
  (*Pattern match on var - this is how we add new, smaller variables*)
  | Dec_tmatch: forall (small: list vsymbol) (hd: option vsymbol) 
    (* (m: mut_adt)
    (vs: list vty) (a: alg_datatype) *)
    (mvar: vsymbol) (v: vty) (pats: list (pattern * term)),
    (*We can only match on a variable?*)
    (hd = Some mvar) \/ In mvar small ->
    (* adt_in_mut a m ->
    snd mvar = vty_cons (adt_name a) vs -> *)
    (*Note: we allow repeated matches on the same variable*)
    (forall (x: pattern * term), In x pats ->
      decrease_fun' fs ps 
        (union vsymbol_eq_dec (pat_vars_smaller (fst x))
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
        (upd_option_iter hd (pat_fv (fst x))) (snd x)) ->
      (*remove pat_fv's (bound), add back constr vars (smaller)*)
      (* (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars m vs (fst x))) 
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
        small)) (upd_option_iter hd (pat_fv (fst x))) m vs (snd x)) -> *)
    decrease_fun' fs ps small hd (Tmatch (Tvar mvar) v pats) 
  (*Other pattern match is recursive case*)
  | Dec_tmatch_rec: forall (small: list vsymbol) (hd: option vsymbol)
    (tm: term) (v: vty) (pats: list (pattern * term)),
    ~(exists var, tm = Tvar var /\ (hd = Some var \/ In var small)) ->
    decrease_fun' fs ps small hd tm ->
    (forall x, In x pats ->
      decrease_fun' fs ps 
      (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
      (upd_option_iter hd (pat_fv (fst x))) (snd x)) ->
    decrease_fun' fs ps small hd (Tmatch tm v pats)
  (*Now the easy cases: Constants, Variables always decreasing*)
  | Dec_var: forall (small : list vsymbol) (hd: option vsymbol) (v: vsymbol),
    decrease_fun' fs ps small hd  (Tvar v)
  | Dec_const: forall (small : list vsymbol) (hd: option vsymbol) (c: constant),
    decrease_fun' fs ps small hd (Tconst c)
  (*Recursive cases: let, if, eps*)
  | Dec_tlet: forall (small: list vsymbol) (hd: option vsymbol) (t1: term)
    (v: vsymbol) (t2: term),
    decrease_fun' fs ps small hd t1 ->
    (*v is bound, so it is no longer smaller in t2 or equal in hd*)
    decrease_fun' fs ps (remove vsymbol_eq_dec v small) (upd_option hd v) t2 ->
    decrease_fun' fs ps small hd (Tlet t1 v t2)
  | Dec_tif: forall (small: list vsymbol) (hd: option vsymbol) (f1: formula)
    (t1 t2: term),
    decrease_pred' fs ps small hd f1 ->
    decrease_fun' fs ps small hd t1 ->
    decrease_fun' fs ps small hd t2 ->
    decrease_fun' fs ps small hd (Tif f1 t1 t2)
  | Dec_eps: forall (small: list vsymbol) (hd: option vsymbol) (f: formula)
    (v: vsymbol),
    decrease_pred' fs ps (remove vsymbol_eq_dec v small) (upd_option hd v) f ->
    decrease_fun' fs ps small hd (Teps f v)
(*This is very similar*)
with decrease_pred' (fs: list fn) (ps: list pn) : 
  list vsymbol -> option vsymbol -> formula -> Prop :=
  | Dec_notin_f: forall (small: list vsymbol) (hd: option vsymbol) (fmla: formula),
  (forall f, In f fs -> negb (funsym_in_fmla (fn_sym f) fmla)) ->
  (forall p, In p ps -> negb (predsym_in_fmla (pn_sym p) fmla)) ->
  decrease_pred' fs ps small hd fmla
  (*First, the recursive predicate call case*)
  | Dec_pred_in: forall (small: list vsymbol) (hd: option vsymbol)
    (p: predsym) (p_decl: pn) (l: list vty) (ts: list term) x,
    In p_decl ps ->
    p = pn_sym p_decl ->
    (*The decreasing argument must be in our list of decreasing terms*)
    In x small ->
    nth (sn_idx p_decl) ts tm_d = Tvar x ->
    (*Uniformity: we must be applying the function uniformly*)
    l = map vty_var (s_params p) ->
    (*None of [fs] or[ps] appear in the terms*) 
    Forall (fun t => forall f,  In f fs -> negb (funsym_in_tm (fn_sym f) t)) ts ->
    Forall (fun t => forall p, In p ps -> negb (predsym_in_tm (pn_sym p) t)) ts ->
    (*Then this recursive call is valid*)
    decrease_pred' fs ps small hd (Fpred p l ts)
  (*Other predicate call*)
  | Dec_pred_notin: forall (small: list vsymbol) (hd: option vsymbol)
    (p: predsym) (l: list vty) (ts: list term),
    ~ In p (map pn_sym ps) ->
    (*In this case, just recursive*)
    (forall t, In t ts -> decrease_fun' fs ps small hd t) ->
    decrease_pred' fs ps small hd (Fpred p l ts)
  (*Pattern match on var - this is how we add new, smaller variables*)
  | Dec_fmatch: forall (small: list vsymbol) (hd: option vsymbol) 
    (mvar: vsymbol) (v: vty) (pats: list (pattern * formula)),
    hd = Some mvar \/ In mvar small ->
    (* adt_in_mut a m ->
    snd mvar = vty_cons (adt_name a) vs -> *)
    (forall x, In x pats -> decrease_pred' fs ps 
      (*remove pat_fv's (bound), add back constr vars (smaller)*)
      (union vsymbol_eq_dec (pat_vars_smaller (fst x)) 
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
        small)) (upd_option_iter hd (pat_fv (fst x))) (snd x)) ->
    decrease_pred' fs ps small hd (Fmatch (Tvar mvar) v pats)
  (*Other pattern match is recursive case*)
  | Dec_fmatch_rec: forall (small: list vsymbol) (hd: option vsymbol)
    (tm: term) (v: vty) (pats: list (pattern * formula)),
    ~(exists var, tm = Tvar var /\ (hd = Some var \/ In var small)) ->
    decrease_fun' fs ps small hd tm ->
    (forall x, In x pats ->
      decrease_pred' fs ps 
      (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
      (upd_option_iter hd (pat_fv (fst x))) (snd x)) ->
    decrease_pred' fs ps small hd (Fmatch tm v pats)
  (*Easy cases: true, false*)
  | Dec_true: forall (small: list vsymbol) (hd: option vsymbol),
    decrease_pred' fs ps small hd Ftrue
  | Dec_false: forall (small: list vsymbol) (hd: option vsymbol),
    decrease_pred' fs ps small hd Ffalse
  (*Recursive cases: not, quantifier, eq, binop, let, if*)
  | Dec_not: forall small hd f,
    decrease_pred' fs ps small hd f ->
    decrease_pred' fs ps small hd (Fnot f)
  | Dec_quant: forall (small: list vsymbol) (hd: option vsymbol)
    (q: quant) (v: vsymbol) (f: formula),
    decrease_pred' fs ps (remove vsymbol_eq_dec v small) (upd_option hd v) f ->
    decrease_pred' fs ps small hd (Fquant q v f)
  | Dec_eq: forall (small: list vsymbol) (hd: option vsymbol)
    (ty: vty) (t1 t2: term),
    decrease_fun' fs ps small hd t1 ->
    decrease_fun' fs ps small hd t2 ->
    decrease_pred' fs ps small hd (Feq ty t1 t2)
  | Dec_binop: forall (small: list vsymbol) (hd: option vsymbol)
    (b: binop) (f1 f2: formula),
    decrease_pred' fs ps small hd f1 ->
    decrease_pred' fs ps small hd f2 ->
    decrease_pred' fs ps small hd (Fbinop b f1 f2)
  | Dec_flet: forall (small: list vsymbol) (hd: option vsymbol) (t1: term)
    (v: vsymbol) (f: formula),
    decrease_fun' fs ps small hd t1 ->
    decrease_pred' fs ps (remove vsymbol_eq_dec v small) (upd_option hd v) f ->
    decrease_pred' fs ps small hd (Flet t1 v f)
  | Dec_fif: forall (small: list vsymbol) (hd: option vsymbol)
    (f1 f2 f3: formula),
    decrease_pred' fs ps small hd f1 ->
    decrease_pred' fs ps small hd f2 ->
    decrease_pred' fs ps small hd f3 ->
    decrease_pred' fs ps small hd (Fif f1 f2 f3)
    .
Set Elimination Schemes.
Scheme decrease_fun'_ind := Minimality for decrease_fun' Sort Prop
with decrease_pred'_ind := Minimality for decrease_pred' Sort Prop.
Print uniform.
Print uniform_list.
(*Now we can try to test (and this will likely fail)*)
(*Need assumption about things appearing with no nesting
  Problem: even if we can support nesting, very very
  difficult to generate generalized induction principle*)
Definition non_nested_list (m: mut_adt) (l: list vty) : bool :=
  forallb (fun (v: vty) =>
    match v with
    | vty_cons ts vs => ts_in_mut_list ts (typs m)
    | _ => true
    end) l.
Definition non_nested (m: mut_adt) : bool :=
  forallb (fun (a: alg_datatype) => forallb
    (fun (f: funsym) => non_nested_list m (s_args f))
      (ne_list_to_list (adt_constrs a))) (typs m).

(*Little test*)
Fixpoint znth {A: Type} (l: list A) (n: Z) : option A :=
  if Z.ltb n 0%Z then None else
  match l with
  | nil => None
  | a :: l => if Z.eqb n 0%Z then Some a else znth l (Z.pred n)
  end.
Set Bullet Behavior "Strict Subproofs".
Lemma znth_spec {A: Type} (l: list A) (n: Z) :
  (0 <= n)%Z ->
  znth l n = nth_error l (Z.to_nat n).
Proof.
  intros.
  set (m:=Z.to_nat n).
  assert (n = Z.of_nat m) by lia.
  rewrite H0; clear H0.
  clear.
  generalize dependent l.
  generalize dependent m. induction m; intros l.
  - destruct l; simpl; auto.
  - rewrite Znat.Nat2Z.inj_succ.
    destruct l; simpl.
    + destruct (_ <? 0)%Z; reflexivity.
    + destruct (Z.ltb_spec0 (Z.succ (Z.of_nat m)) 0%Z); try lia.
      destruct (Z.eqb_spec (Z.succ (Z.of_nat m)) 0%Z); try lia.
      rewrite Z.pred_succ. apply IHm.
Qed.
      Search Z.pred Z.succ.
    
    
    
     Search Z.ltb. destruct (_ <? 0)%Z eqn : H. 
    
    
     destruct _.
  
   Search Z.of_nat S. 
  
  
  
   unfold znth.

   clear m.
  assert (n = Z.of_nat (Z.to_nat n)) by lia.
  replace (Z.to_nat n) with ()
  rewrite H0 at 1.



(*Need to prove something like:
  If small is not empty (and decreate_fun' holds),
  then ith type is mutual type
  and this is the type we are wrt to*)
Lemma decrease_fun_mut gamma 
  (Hval: valid_context gamma)
  (Hnest: forall m, mut_in_ctx m gamma -> non_nested m) t f:
  (forall ty small hd fs ps,
    term_has_type gamma t ty ->
    decrease_fun' fs ps small hd t ->
    exists m a vs,
      mut_in_ctx m gamma /\
      adt_in_mut a m /\
      (*Hard to prove: let's do 2 tests:
        either nonrecursive (no funsym or predsym appears)
        or recursive - if recursive, then ith must be ADT
        so separate out into 2 predicates, and total one
        is just OR TODO this*)
      (*What we want to show: if small is nonempty,
        then *)
      nth i (s_args )

    exists m vs,
      decrease_fun fs ps small hd m vs t) /\
  (forall small hd fs ps,
    formula_typed gamma f ->
    decrease_pred' fs ps small hd f ->
    exists m vs,
      decrease_pred fs ps small hd m vs f).

Set Bullet Behavior "Strict Subproofs".
Lemma decrease_fun_equiv gamma 
  (Hval: valid_context gamma)
  (Hnest: forall m, mut_in_ctx m gamma -> non_nested m)
  (m: mut_adt) (vs: list vty) t f:
  (forall ty small hd fs ps,
    term_has_type gamma t ty ->
    decrease_fun' fs ps small hd t ->
    exists m vs,
      decrease_fun fs ps small hd m vs t) /\
  (forall small hd fs ps,
    formula_typed gamma f ->
    decrease_pred' fs ps small hd f ->
    exists m vs,
      decrease_pred fs ps small hd m vs f).
Proof.
  revert t f.
  apply term_formula_ind.
  - intros.
    exists m. exists vs.
    apply Typing.Dec_const.
  - intros. exists m. exists vs.
    apply Typing.Dec_var.
  - intros. inversion H1; subst.
    + exists m. exists vs. constructor; auto.
    + 

    (*Maybe - check that index we are decre\asing on
      is an ADT?*)

    (*function foo (x: int) (y: list int) : int =
      match y with
      | Cons z tl -> 1 + foo z y
      | Nil -> 0
      end*)
    inversion H0; subst.
    + constructor; auto.
    + inversion H0. 




  Check term_formula_ind.
  apply term_formula_ind. *)