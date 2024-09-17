Require Import Task.
Require Import Alpha GenElts.
Require Import eliminate_inductive. (*TODO: not great, factor out common stuff*)
Require Import PatternProofs. (*TODO: factor out gen stuff*)
Require Import Denotational2.
Set Bullet Behavior "Strict Subproofs".

(*TODO: really make [gen] versions more extensive and organized*)

Section Gen.
Definition gen_sym (b: bool) : Set := if b then funsym else predsym.

Definition gen_sym_name {b: bool} (f: gen_sym b) : string :=
  match b return gen_sym b -> string with
  | true => fun f => s_name f
  | false => fun f => s_name f
  end f.

Definition gen_sym_params {b: bool} (f: gen_sym b) : list typevar :=
  match b return gen_sym b -> list typevar with
  | true => s_params
  | false => s_params
  end f.

Definition gen_sym_args {b: bool} (f: gen_sym b) : list vty :=
  match b return gen_sym b -> list vty with
  | true => s_args
  | false => s_args
  end f.

Definition gen_funpred_def (b: bool) (f: gen_sym b) (l: list vsymbol) (t: gen_term b) : funpred_def :=
  match b return gen_sym b -> gen_term b -> funpred_def with
  | true => fun ls t => fun_def ls l t
  | false => fun ls f => pred_def ls l f
  end f t.

Definition gen_funpred_def_match (x: funpred_def) : {b: bool & (gen_sym b * list vsymbol * gen_term b)%type} :=
  match x with
  | fun_def ls vs t => existT _ true (ls, vs, t)
  | pred_def ls vs f => existT _ false (ls, vs, f)
  end.

Lemma gen_funpred_def_match_eq (x: funpred_def) b ls vs tms:
  gen_funpred_def_match x = existT _ b (ls, vs, tms) <-> gen_funpred_def b ls vs tms = x.
Proof.
  unfold gen_funpred_def_match, gen_funpred_def. destruct x; simpl.
  - split; intros Hex; [|destruct b]; inversion Hex; subst; auto.
    apply inj_pair2_eq_dec in Hex; [inversion Hex; subst; auto | apply Bool.bool_dec].
  - split; intros Hex; [|destruct b]; inversion Hex; subst; auto.
    apply inj_pair2_eq_dec in Hex; [inversion Hex; subst; auto | apply Bool.bool_dec].
Qed.

(*Common features: let, match, app (fun or predsym), if*)
Definition gen_app (b: bool) (f: gen_sym b) (tys: list vty) (tms: list term) : gen_term b :=
  match b return gen_sym b -> gen_term b with
  | true => fun f => Tfun f tys tms
  | false => fun p => Fpred p tys tms
  end f.

Definition gen_if (b: bool) (f: formula) (t1 t2: gen_term b) : gen_term b :=
  match b return gen_term b -> gen_term b -> gen_term b with
  | true => fun t1 t2 => Tif f t1 t2
  | false => fun f1 f2 => Fif f f1 f2
  end t1 t2.

(*Generalized equality (Teq or Fiff)*)
Definition gen_eq (b: bool) (ty: gen_type b) (t1 t2: gen_term b) : formula :=
  match b return gen_type b -> gen_term b -> gen_term b -> formula with
  | true => fun ty t1 t2 => Feq ty t1 t2
  | false => fun _ f1 f2 => Fbinop Tiff f1 f2
  end ty t1 t2.

Definition gen_sym_ret {b: bool} (f: gen_sym b) : gen_type b :=
  match b return gen_sym b -> gen_type b with
  | true => f_ret
  | false => fun _ => tt
  end f.

Definition gen_abs {b: bool} (f: gen_sym b) : def :=
  match b return gen_sym b -> def with
  | true => abs_fun
  | false => abs_pred
  end f.

Definition a_convert_gen {b: bool} (t: gen_term b) (vs: list vsymbol) : gen_term b :=
  match b return gen_term b -> gen_term b with
  | true => fun t => a_convert_t t vs
  | false => fun f => a_convert_f f vs
  end t.


End Gen.

(*Easy: don't need to change b as wer recurse*)

(*Assume everything alpha converted already so no free var in hd in bound in t*)
Fixpoint t_insert (ty: vty) (hd t: term) : formula :=
  match t with
  | Tif f t2 t3 => Fif f (t_insert ty hd t2) (t_insert ty hd t3)
  | Tlet t1 v t2 => Flet t1 v (t_insert ty hd t2)
  | Tmatch tm ty1 pats => Fmatch tm ty1 (map (fun x => (fst x, (t_insert ty hd (snd x)))) pats)
  | _ => Feq ty hd t
  end.

Fixpoint f_insert (hd t: formula) : formula :=
  match t with
  | Fif f t2 t3 => Fif f (f_insert hd t2) (f_insert hd t3)
  | Flet t1 v t2 => Flet t1 v (f_insert hd t2)
  | Fmatch tm ty1 pats => Fmatch tm ty1 (map (fun x => (fst x, (f_insert hd (snd x)))) pats)
  | _ => Fbinop Tiff hd t
  end.

(*Need this to get around positivity checker*)
Definition t_insert_gen {b: bool} (ty: gen_type b) (hd t: gen_term b) : formula :=
  match b return gen_type b -> gen_term b -> gen_term b -> formula with
  | true => t_insert
  | false => fun _ => f_insert
  end ty hd t.




Definition add_ld (which: forall b, gen_sym b -> bool) (x: funpred_def) 
  (y: list def * list funpred_def * list (string * formula)) : 
  list def * list funpred_def * list (string * formula) :=
  let '(abst, defn, axl) := y in
  match (gen_funpred_def_match x) with
  | existT b (ls, vl, e) =>
    if which b ls then
      (*Create new name for axiom*)
      let pr := ((gen_sym_name ls) ++ "_'def")%string in
      (*produce e.g. the term fact(n) - note that these are always polymorphic so we can give vars*)
      let hd := gen_app b ls (map vty_var (gen_sym_params ls)) (map Tvar vl) in
      let ty := gen_sym_ret ls in
      (*Axiom: forall n, fact n = e*)
      (*First, alpha convert e so there are no freevars in common*)
      let e' := a_convert_gen e vl in
      let ax1 := fforalls vl (t_insert_gen ty hd e') in
      let ax2 := (pr, ax1) in
      (*abstract logical symbol*)
      let ld := gen_abs ls in
      (ld :: abst, defn, ax2 :: axl)
    else 
      (abst, x :: defn, axl)
  end.

(*Here, nonrec means that we are giving in non-recursive*)
Definition elim_decl (which: forall b, gen_sym b -> bool)(nonrec: bool) (l: list funpred_def) : list def * list (string * formula) :=
  let '(abst, defn, axl)  :=
    fold_right (add_ld which) (nil, nil, nil) l in
  let defn :=
    match defn with
    | nil => nil
    | [d] => if nonrec then [nonrec_def d] else [recursive_def [d]]
    | _ => [recursive_def defn]
    end in
  (abst ++ defn, axl). 

(*Slightly different; we also choose if we eliminate nonrecursive*)
Definition elim (which: forall b, gen_sym b -> bool) (nonrec: bool) (d: def) : list def * list (string * formula) :=
  match d with
  | recursive_def l => elim_decl which false l
  | nonrec_def l => if nonrec then elim_decl which true [l] else ([d], nil)
  | _ => ([d], nil)
  end.


(*Versions to handle only structural (we only allow structural) and mutual, which we don't
  include at the moment*)

Definition eliminate_definition_gen which nonrec : trans :=
  fun t => [trans_decl (elim which nonrec) t].
Definition eliminate_definition_func : trans :=
  eliminate_definition_gen (fun b _ => b) true.
Definition eliminate_definition_pred : trans :=
  eliminate_definition_gen (fun b _ => negb b) true.
Definition eliminate_definition : trans :=
  eliminate_definition_gen (fun _ _ => true) true.
Definition eliminate_recursion : trans :=
  eliminate_definition_gen (fun _ _ => true) false.

(*Proofs*)

Section Proofs.

(*Part 1: Rewrite lemmas*)

(*Just like [eliminate_inductive], easier to reason about gamma and delta
  separately*)

(*Helpful for us - get axiom for single logic def*)
Definition rec_axiom {b: bool} (ls: gen_sym b)
  (vl: list vsymbol) (e: gen_term b) : string * formula :=
  let pr := ((gen_sym_name ls) ++ "_'def")%string in
  let hd := gen_app b ls (map vty_var (gen_sym_params ls)) (map Tvar vl) in
  let ty := gen_sym_ret ls in
  let e' := a_convert_gen e vl in
  let ax1 := fforalls vl (t_insert_gen ty hd e') in
  (pr, ax1).

(*Decls for each recursive def: either single one or one abstract symbol per element*)

Definition axioms_of_def (which : forall b, gen_sym b -> bool) 
  (l: list funpred_def) : list (string * formula) :=
  concat (map (fun x =>
    match (gen_funpred_def_match x) with
    | existT b (ls, vl, e) => 
      if which _ ls then [rec_axiom ls vl e] else []
    end) l).

(*We do this in 2 parts: give both the axioms and the ones to go in the recursive
  decl, separately*)
Definition decls_of_def_aux (which: forall b, gen_sym b -> bool) (nonrec : bool)
  (l: list funpred_def) : list def * list funpred_def :=
  (*TODO: partition*)
  (Pattern.filter_map (fun x =>
  match (gen_funpred_def_match x) with
  | existT b (ls, vl, e) => if which _ ls then Some (gen_abs ls) else None
  end
  ) l,
  Pattern.filter_map (fun x =>
  match (gen_funpred_def_match x) with
  | existT b (ls, vl, e) => if which _ ls then None else Some x
  end) l).

Definition decls_of_def (which: forall b, gen_sym b -> bool) (nonrec : bool)
  (l: list funpred_def) : list def * option def :=
  let x := decls_of_def_aux which nonrec l in
  (fst x, match snd x with
    | nil => None
    | [d] => Some (if nonrec then nonrec_def d else recursive_def [d])
    | _ => Some (recursive_def (snd x))
  end).

Definition decl_list_of_def (which: forall b, gen_sym b -> bool) (nonrec : bool)
  (l: list funpred_def) : list def :=
  let x := decls_of_def which nonrec l in
  fst x ++ match (snd x) with | None => nil | Some d => [d] end.


(*We have two transformations: one that generates axioms, one that
  changes gamma*)

Definition gen_axioms which (nonrec : bool) (t: task) : task :=
  let new_d :=
  concat (map (fun x =>
    match x with
    | recursive_def l => rev (axioms_of_def which l)
    | nonrec_def l => if nonrec then rev (axioms_of_def which [l]) else nil
    | _ => []
    end) (task_gamma t)) in
  add_axioms t new_d.

Definition gen_new_ctx_gamma which (nonrec: bool) (gamma: context) : context :=
  concat (map (fun x =>
    match x with
    | recursive_def l => rev (decl_list_of_def which false l)
    | nonrec_def l => if nonrec then rev (decl_list_of_def which true [l]) else [x]
    | _ => [x]
    end) gamma).

Definition gen_new_ctx which (nonrec : bool) (t: task) : task :=
  mk_task (gen_new_ctx_gamma which nonrec (task_gamma t)) (task_delta t) (task_goal t).

Definition eliminate_definition_alt which nonrec : trans :=
  compose_single_trans (gen_axioms which nonrec) (gen_new_ctx which nonrec).

 (*Lemmas we need*)
Lemma decls_of_def_elim which nonrec (l: list funpred_def):
   (fst (elim_decl which nonrec l)) = decl_list_of_def which nonrec l.
Proof.
  unfold elim_decl, decl_list_of_def.
  (*Handle end first*)
  destruct (fold_right _ _ _) as [[abst defn] axl] eqn : Hfold.
  simpl fst at 1. f_equal.
  - (*First, prove abstract*)
    replace abst with (fst (fst (fold_right (add_ld which) (nil, nil, nil) l))) by (rewrite Hfold; reflexivity).
    clear Hfold. induction l as [| x t IH]; simpl; auto.
    unfold add_ld at 1.
    destruct (gen_funpred_def_match x) as [b [[ls vs] e]] eqn : Hgen; simpl in *.
    destruct (fold_right (add_ld which) ([], [], []) t ) as [[abst1 defn1] axl1]; simpl.
    destruct (which b ls) eqn : Hwhich; simpl; [f_equal|]; auto.
  - (*Now prove end*)
    assert (Habs: forall l,snd (fst (fold_right (add_ld which) (nil, nil, nil)l)) = 
      snd (decls_of_def_aux which nonrec l)).
    {
      clear. induction l as [| h t IH]; simpl; auto.
      unfold add_ld at 1.
      destruct (fold_right (add_ld which) ([], [], []) t ) as [[abst1 defn1] axl1]; simpl.
      simpl snd at 1 in IH.
      destruct (gen_funpred_def_match h) as [b [[ls vs] e]] eqn : Hgen.
      destruct (which b ls) eqn : Hwhich; auto.
      simpl. f_equal; auto.
    }
    (*The rest is just case analysis*)
    unfold decls_of_def at 1. Opaque decls_of_def_aux. simpl snd. Transparent decls_of_def_aux.
    destruct defn as [| def1 deft].
    { rewrite <- Habs, Hfold. reflexivity. }
    destruct deft as [|def2 deft].
    + destruct nonrec; rewrite <- Habs, Hfold; reflexivity.
    + rewrite <- Habs, Hfold; reflexivity.
Qed.

(*Much easier*)
Lemma axioms_of_def_elim which nonrec (l: list funpred_def):
   (snd (elim_decl which nonrec l)) = axioms_of_def which l.
Proof.
  unfold elim_decl, axioms_of_def.
  induction l as [| h t IH]; simpl; auto.
  unfold add_ld at 1.
  destruct (gen_funpred_def_match h) as [b [[ls vs] e]] eqn : Hgen; simpl in *.
  destruct (fold_right (add_ld which) ([], [], []) t ) as [[abst1 defn1] axl1]; simpl.
  destruct (which b ls) eqn : Hwhich; simpl; [f_equal|]; auto.
Qed.

(*And the proof of equivalence*)
Lemma eliminate_definition_split which nonrec: forall t,
  eliminate_definition_gen which nonrec t =
  eliminate_definition_alt which nonrec t.
Proof.
  intros t. unfold eliminate_definition_gen, eliminate_definition_alt, compose_single_trans, single_trans, trans_decl.
  f_equal. unfold gen_new_ctx, gen_axioms.
  destruct t as [[gamma delta] goal]; simpl_task.
  rewrite (surjective_pairing (fold_left _ gamma _)); simpl. f_equal. f_equal.
  - (*Prove gamma equivalent*)
    unfold gen_new_ctx_gamma.
    rewrite <- fold_left_rev_right. simpl_task.
    rewrite <- (rev_involutive gamma) at 2.
    (*TODO: bad*)
    induction (rev gamma); simpl; auto.
    rewrite (surjective_pairing (elim _ _ a)); simpl.
    rewrite rev_app_distr.
    rewrite map_app, concat_app. simpl. rewrite app_nil_r.
    rewrite IHl. f_equal.
    (*The interesting part*)
    destruct a; simpl; try reflexivity.
    + rewrite decls_of_def_elim. reflexivity.
    + destruct nonrec; simpl; [| reflexivity]. rewrite decls_of_def_elim. reflexivity.
  - (*Prove delta part*)
    f_equal. rewrite <- fold_left_rev_right.
    rewrite <- (rev_involutive gamma) at 2.
    rewrite map_rev.
    induction (rev gamma); simpl; auto.
    rewrite (surjective_pairing (elim _ _ a)); simpl.
    rewrite !rev_app_distr.
    rewrite concat_app. simpl. rewrite <- IHl, app_nil_r. f_equal.
    destruct a; simpl; auto.
    + rewrite axioms_of_def_elim. reflexivity.
    + destruct nonrec; [|reflexivity]. rewrite axioms_of_def_elim. reflexivity.
Qed.

(*Part 1: Everything is well-typed*)

Section Typing.

Lemma t_insert_gen_typed gamma {b: bool} (ty: gen_type b) (t1 t2: gen_term b):
  @gen_typed gamma b t1 ty ->
  @gen_typed gamma b t2 ty ->
  formula_typed gamma (t_insert_gen ty t1 t2).
Proof.
  (*Prove in 2 parts bc of induction*)
  unfold gen_typed, gen_type, gen_term in *. destruct b; simpl in *.
  - intros Hty1 Hty2.
    apply (term_ind (fun t2 => forall ty t1 (Hty1: term_has_type gamma t1 ty) (Hty2: term_has_type gamma t2 ty),
      formula_typed gamma (t_insert ty t1 t2)) (fun _ => True)); intros; simpl; auto; 
        try solve[apply F_Eq; assumption]; inversion Hty3; subst; constructor; auto;
    [| | rewrite null_map; assumption]; intros x; rewrite in_map_iff; intros [y [Hx Hiny]]; subst; simpl; auto.
    rewrite Forall_map, Forall_forall in H0. auto.
  - intros Hty1 Hty2.
    apply (formula_ind (fun _ => True) (fun f2 => forall f1 (Hty1: formula_typed gamma f1) 
      (Hty2: formula_typed gamma f2),
      formula_typed gamma (f_insert f1 f2))); intros; simpl; auto; 
        try solve[apply F_Eq; assumption]; inversion Hty3; subst; constructor; auto;
    [| | rewrite null_map; assumption]; intros x; rewrite in_map_iff; intros [y [Hx Hiny]]; subst; simpl; auto.
    rewrite Forall_map, Forall_forall in H0. auto.
Qed.

Definition gen_sig (b: bool) : context -> list (gen_sym b) :=
  match b return context -> list (gen_sym b) with
  | true => sig_f
  | false => sig_p
  end.

Definition gen_valid_type {b: bool} (gamma: context) (ty: gen_type b) : Prop :=
  match b return gen_type b -> Prop with
  | true => fun ty => valid_type gamma ty
  | false => fun _ => True
  end ty.

Definition gen_ty_subst {b: bool} (params: list typevar) (tys: list vty) (ty: gen_type b) : gen_type b :=
  match b return gen_type b -> gen_type b with
  | true => ty_subst params tys
  | false => fun _ => tt
  end ty.

Lemma gen_app_typed {b: bool} gamma (ls: gen_sym b) (tys: list vty) (tms: list term) (ty: gen_type b)
  (Inf: In ls (gen_sig b gamma))
  (Hval: Forall (valid_type gamma) tys)
  (Hvalret: gen_valid_type gamma (gen_sym_ret ls))
  (* (Hlentms: length tms = length (gen_sym_args ls)) *)
  (Hlentys: length tys = length (gen_sym_params ls))
  (Hinner: Forall2 (term_has_type gamma) tms (map (ty_subst (gen_sym_params ls) tys) (gen_sym_args ls)))
  (Hty: ty = gen_ty_subst (gen_sym_params ls) tys (gen_sym_ret ls))
  : @gen_typed gamma b (gen_app b ls tys tms) ty.
Proof.
  rewrite Forall2_combine in Hinner.
  destruct Hinner as [Htms Hinner]; rewrite map_length in Htms.
  destruct b; simpl in *; subst; constructor; auto.
Qed.

Definition gen_type_vars {b: bool} (t: gen_term b) : list typevar :=
  match b return gen_term b -> list typevar with
  | true => tm_type_vars
  | false => fmla_type_vars
  end t.

Definition gen_funpred_def_valid_type gamma {b: bool} (ls: gen_sym b) (vs: list vsymbol)
  (t: gen_term b):
  funpred_def_valid_type gamma (gen_funpred_def b ls vs t) <->
  @gen_typed gamma b t (gen_sym_ret ls) /\
  sublist (gen_fv b t) vs /\
  sublist (gen_type_vars t) (gen_sym_params ls) /\
  NoDup (map fst vs) /\
  map snd vs = gen_sym_args ls.
Proof.
  unfold gen_funpred_def. destruct b; simpl; reflexivity.
Qed.

Definition wf_gen_sym {b: bool} gamma (ls: gen_sym b) : Prop :=
  match b return gen_sym b -> Prop with
  | true => wf_funsym gamma
  | false => wf_predsym gamma
  end ls.

(*NOTE: don't care about type variables right now*)
Lemma wf_gen_sym_valid {b: bool} {gamma} {ls: gen_sym b}
  (Hwf: wf_gen_sym gamma ls):
  Forall (valid_type gamma) (gen_sym_args ls) /\
  gen_valid_type gamma (gen_sym_ret ls).
Proof.
  destruct b; simpl in *.
  - unfold wf_funsym in Hwf. inversion Hwf as [ | ? ? [Hret _] Hargs]; subst.
    split; auto. revert Hargs. apply Forall_impl. intros a Hval; apply Hval.
  - split; auto.  unfold wf_predsym in Hwf. revert Hwf. apply Forall_impl. 
    intros a Hval; apply Hval.
Qed.

(*TODO: move*)
Lemma recpred_in_predsyms {gamma} {f: predsym} {l: list funpred_def}
  (l_in: In l (mutfuns_of_context gamma))
  (f_in: predsym_in_mutfun f l):
  In f (predsyms_of_context gamma).
Proof.
  unfold predsyms_of_context. rewrite in_concat.
  exists (predsyms_of_def (recursive_def l)).
  split. rewrite in_map_iff. exists (recursive_def l).
  split; auto. apply in_mutfuns in l_in; auto.
  apply in_bool_In in f_in. auto.
Qed.

(*NOTE: only need that it is in fun/predsyms of context*)

Definition sym_in_context {b: bool} (ls: gen_sym b) gamma : Prop :=
  match b return gen_sym b -> Prop with
  | true => fun f => In f (funsyms_of_context gamma)
  | false => fun f => In f (predsyms_of_context gamma)
  end ls.

Lemma in_context_wf_gen_sym {b: bool} gamma{ls: gen_sym b}
  (gamma_wf: wf_context gamma)
  (Hin: sym_in_context ls gamma):
  wf_gen_sym gamma ls.
Proof.
  apply wf_context_alt in gamma_wf.
  destruct gamma_wf as [Hfun [Hpred _]].
  rewrite Forall_forall in Hfun, Hpred.
  destruct b; simpl in *; auto.
Qed.

Lemma recursive_def_in_gen_sig {b: bool} gamma  {ls: gen_sym b}
  (Hin: sym_in_context ls gamma):
  In ls (gen_sig b gamma).
Proof.
  pose proof (concrete_in_sig gamma) as [_ [Hfun Hpred]].
  rewrite Forall_forall in Hfun, Hpred.
  destruct b; simpl in *; auto.
Qed.

Lemma a_convert_gen_typed {b: bool} gamma (t: gen_term b) (vs: list vsymbol) (ty: gen_type b):
  @gen_typed gamma b t ty ->
  @gen_typed gamma b (a_convert_gen t vs) ty.
Proof.
  intros Hty. destruct b; simpl in *.
  - apply a_convert_t_ty; assumption.
  - apply a_convert_f_typed; assumption.
Qed.

Lemma recursive_in_context {b: bool} gamma {l: list funpred_def} {ls: gen_sym b}
  {vs: list vsymbol} {e: gen_term b} 
  (Hin1: In (recursive_def l) gamma)
  (Hin2: In (gen_funpred_def b ls vs e) l):
  sym_in_context ls gamma.
Proof.
  destruct b; simpl in *.
  - eapply recfun_in_funsyms.
    + apply in_mutfuns, Hin1.
    + eapply fun_in_mutfun. eauto.
  - eapply recpred_in_predsyms.
    + apply in_mutfuns, Hin1.
    + eapply pred_in_mutfun. eauto.
Qed.

Lemma nonrec_in_context {b: bool} gamma {ls: gen_sym b}
  {vs: list vsymbol} {e: gen_term b} 
  (Hin: In (nonrec_def (gen_funpred_def b ls vs e)) gamma):
  sym_in_context ls gamma.
Proof.
  destruct b; simpl in *.
  - eapply nonrec_in_funsyms; eauto.
  - eapply nonrec_in_predsyms; eauto.
Qed.

Lemma gen_typevars_in_params {x v b} (ls: gen_sym b)
  (Hinx: In x (gen_sym_args ls))
  (Hinv: In v (type_vars x)):
  In v (gen_sym_params ls).
Proof.
  destruct (In_nth _ _ vty_int Hinx) as [i [Hi Hx]]; subst.
  destruct b; simpl in *; apply (typevars_in_params _ _ Hi _ Hinv).
Qed.

(*Need intermediate pieces in multiple places*)
Lemma rec_axiom_app_typed {gamma b ls vs e}
  (gamma_valid: valid_context gamma)
  (Hallval: funpred_def_valid_type gamma (gen_funpred_def b ls vs e))
  (Hinctx: sym_in_context ls gamma):
@gen_typed gamma b
  (gen_app b ls (map vty_var (gen_sym_params ls))
  (map Tvar vs))
  (gen_sym_ret ls).
Proof.
  apply gen_funpred_def_valid_type in Hallval.
  destruct Hallval as [Hty [Hsubvs [Hsubparams [Hnodup Hvs]]]].
  assert (Hwf: wf_gen_sym gamma ls) (*NOTE: need this*)
    by apply (in_context_wf_gen_sym gamma (valid_context_wf _ gamma_valid) Hinctx).
  apply wf_gen_sym_valid in Hwf.
  destruct Hwf as [Hvalargs Hvalret].
   apply gen_app_typed; auto.
  + apply (recursive_def_in_gen_sig _ Hinctx).
  + rewrite Forall_map. rewrite Forall_forall. intros x Hinsym. constructor.
  + rewrite map_length; reflexivity.
  + (*The nontrivial part: prove that the arguments are correct*)
    rewrite map_id'.
    2: {
      rewrite Forall_forall. intros x Hinx.
      apply ty_subst_params_id.
      intros v Hinv.
      eapply gen_typevars_in_params. apply Hinx. auto.
    }
    replace vs with (combine (map fst vs) (gen_sym_args ls)).
    2: { rewrite <- Hvs, combine_eq. reflexivity. }
    rewrite Forall2_nth.
    assert (Hvslen: length vs = length (gen_sym_args ls)). {
      rewrite <- Hvs, map_length; reflexivity.
    }
    split; unfold vsymbol in *; rewrite map_length, combine_length, map_length, Hvslen, Nat.min_id; [reflexivity|].
    intros i d1 d2 Hi. rewrite map_nth_inbound with (d2:=(""%string, vty_int));
    [| rewrite combine_length, map_length; lia].
    apply T_Var'; auto.
    * rewrite Forall_nth in Hvalargs. auto.
    * rewrite combine_nth; [| rewrite map_length; lia]. simpl. apply nth_indep, Hi.
  + (*And return type*)
    (*Just case on b*)
    destruct b; simpl in *; auto.
    symmetry; apply ty_subst_params_id.
    intros v Hinv.
    assert (ls_wf: check_sublist (type_vars (f_ret ls)) (s_params ls)) by (destruct ls; auto).
    apply (reflect_iff _ _ (check_sublist_correct _ _) ) in ls_wf.
    apply ls_wf, Hinv.
Qed.


Lemma rec_axiom_typed {gamma b ls vs e}
  (gamma_valid: valid_context gamma)
  (Hallval: funpred_def_valid_type gamma (gen_funpred_def b ls vs e))
  (Hinctx: sym_in_context ls gamma):
  formula_typed gamma (snd (rec_axiom ls vs e)).
Proof.
  assert (Hval:=Hallval).
  apply gen_funpred_def_valid_type in Hallval.
  destruct Hallval as [Hty [Hsubvs [Hsubparams [Hnodup Hvs]]]].
  assert (Hwf: wf_gen_sym gamma ls) (*NOTE: need this*)
    by apply (in_context_wf_gen_sym gamma (valid_context_wf _ gamma_valid) Hinctx).
  apply wf_gen_sym_valid in Hwf.
  destruct Hwf as [Hvalargs Hvalret].
  (*Now we can prove each part*)
  apply fforalls_typed.
  2: { rewrite <- Forall_map. rewrite Hvs. apply Hvalargs. }
  apply t_insert_gen_typed.
  2: { apply a_convert_gen_typed, Hty. }
  eapply rec_axiom_app_typed; eauto.
Qed.

Lemma recursive_valid_type {gamma} (gamma_valid: valid_context gamma) {l fd}
  (Hin1: In (recursive_def l) gamma)
  (Hin2: In fd l):
  funpred_def_valid_type gamma fd.
Proof.
  apply valid_context_defs in gamma_valid.
  rewrite Forall_forall in gamma_valid.
  specialize (gamma_valid _ Hin1).
  simpl in gamma_valid.
  unfold funpred_valid in gamma_valid.
  destruct gamma_valid as [Hallval _].
  rewrite Forall_forall in Hallval.
  auto.
Qed.

Lemma nonrec_valid_type {gamma} (gamma_valid: valid_context gamma) {d}
  (Hin1: In (nonrec_def d) gamma):
  funpred_def_valid_type gamma d.
Proof.
  apply valid_context_defs in gamma_valid.
  rewrite Forall_forall in gamma_valid.
  specialize (gamma_valid _ Hin1).
  simpl in gamma_valid. apply gamma_valid.
Qed.

Lemma gen_axioms_typed which (nonrec : bool) (t: task) (t_wf: task_wf t):
forall fmla : formula,
In fmla (map snd (concat (map (fun x =>
    match x with
    | recursive_def l => rev (axioms_of_def which l)
    | nonrec_def l => if nonrec then rev (axioms_of_def which [l]) else nil
    | _ => []
    end) (task_gamma t)))) -> formula_typed (task_gamma t) fmla.
Proof.
  rewrite <- Forall_forall, Forall_map, Forall_concat, Forall_map.
  rewrite Forall_forall; intros d Hd.
  rewrite Forall_forall; intros ax.
  destruct d; try solve[intros []].
  - rewrite <- In_rev. (*LOTS of boilerplate should reduce*)
    unfold axioms_of_def. (*Nicer: concat instead of fold_right*) 
    rewrite in_concat.
    intros [axs [Hinaxs Hax]].
    rewrite in_map_iff in Hinaxs.
    destruct Hinaxs as [fd [Haxs Hinfd]]; subst.
    destruct (gen_funpred_def_match fd) as [b [[ls vs] e]] eqn : Hgen; simpl in *.
    destruct (which b ls) eqn : Hwhich; [| contradiction].
    destruct Hax as [Hax | []]. subst. 
    apply gen_funpred_def_match_eq in Hgen. subst.
    inversion t_wf.
    pose proof (recursive_valid_type task_gamma_valid Hd Hinfd) as Hallval.
    assert (Hinctx: sym_in_context ls (task_gamma t)) by
          apply (recursive_in_context _ Hd Hinfd).
    apply rec_axiom_typed; assumption.
  - destruct nonrec; [|contradiction].
    unfold axioms_of_def.
    rewrite <- In_rev, in_concat. 
    simpl. intros [axs [[Hinaxs | []] Hax]].
    destruct (gen_funpred_def_match f) as [b [[ls vs] e]] eqn : Hgen; simpl in *.
    destruct (which b ls) eqn : Hwhich; [| subst; contradiction]. subst.
    destruct Hax as [Hax | []]. subst. 
    unfold rec_axiom. simpl.
    apply gen_funpred_def_match_eq in Hgen. subst.
    inversion t_wf.
    pose proof (nonrec_valid_type task_gamma_valid Hd) as Hallval.
    assert (Hinctx: sym_in_context ls (task_gamma t)) by
          apply (nonrec_in_context _ Hd).
    apply rec_axiom_typed; assumption.
Qed.

End Typing.

(*Part 2: Axioms are sound*)


Ltac split_all_dec_eq :=
  match goal with
  | |- @eq bool (proj_sumbool _ _ (all_dec (?x = ?y)))  (proj_sumbool _ _ (all_dec (?a = ?b))) => 
    let H1 := fresh in let H2 := fresh in
    assert (H1: x = a); [| assert (H2: y = b); [| rewrite H1, H2]]
  end.
    
Lemma sublist_cons {A: Type} (l1 l2 : list A) x:
  sublist l1 l2 ->
  sublist l1 (x :: l2).
Proof.
  unfold sublist. simpl. intros. right; auto.
Qed.

(*A key result: t_insert_gen*)
(*It must be the case that the free vars of t1 do not intersect with the boundvars of t2*)
Lemma t_insert_rep {gamma} (gamma_valid: valid_context gamma) pd vt pf vv ty t1 t2 Hty Hty1 Hty2
  (Hdisj: disj (tm_fv t1) (tm_bnd t2)):
  formula_rep gamma_valid pd vt pf vv (t_insert ty t1 t2) Hty =
  all_dec (term_rep gamma_valid pd vt pf vv t1 ty Hty1 =
    term_rep gamma_valid pd vt pf vv t2 ty Hty2).
Proof.
  revert vv t1 Hdisj Hty Hty1 Hty2.
  apply (term_ind (fun t2 => forall vv t1,
    disj (tm_fv t1) (tm_bnd t2) ->
    forall Hty Hty1 Hty2,
    formula_rep gamma_valid pd vt pf vv
    (t_insert ty t1 t2) Hty =
  all_dec
    (term_rep gamma_valid pd vt pf vv t1 ty Hty1 =
  term_rep gamma_valid pd vt pf vv t2 ty Hty2)) (fun _ => True)); simpl; intros; simpl_rep_full; auto.
  - split_all_dec_eq; auto; apply term_rep_irrel.
  - split_all_dec_eq; auto; [apply term_rep_irrel | apply dom_cast_eq].
  - split_all_dec_eq; auto; [apply term_rep_irrel |].
    unfold fun_arg_list. erewrite get_arg_list_eq.
    unfold cast_dom_vty. rewrite !dom_cast_compose. apply dom_cast_eq.
    rewrite Forall_forall; intros; apply term_rep_irrel.
  - (*First interesting case: Tlet*)
    rewrite H0 with (Hty1:=Hty1) (Hty2:=(proj2' (ty_let_inv Hty2))).
    2: { eapply disj_sublist. apply H1. apply sublist_cons. apply sublist_app_r. }
    (*Use disj*)
    rewrite tm_change_vv with (v2:=vv); auto.
    + erewrite (term_rep_irrel _ _ _ _ _ tm1). reflexivity.
    + intros x Hinx. unfold substi. destruct (vsymbol_eq_dec x v); subst; auto.
      exfalso. apply (H1 v); split; simpl; auto.
  - (*Tif*)
    rewrite fmla_rep_irrel with (Hval2:= (proj2' (proj2' (ty_if_inv Hty2)))).
    destruct (formula_rep _ _ _ _ _ f _) eqn : Hrep.
    + erewrite H0; [reflexivity|].
      eapply disj_sublist. apply H2. eapply sublist_trans. apply sublist_app_l.
      apply sublist_app_r.
    + erewrite H1; [reflexivity|].
      eapply disj_sublist. apply H2. rewrite app_assoc. apply sublist_app_r.
  - (*Tmatch*)
    rewrite term_rep_irrel with (Hty2:=(proj1' (ty_match_inv Hty2))).
    generalize dependent (proj1' (proj2' (typed_match_inv Hty))).
    generalize dependent (proj2' (proj2' (typed_match_inv Hty))).
    generalize dependent (proj1' (proj2' (ty_match_inv Hty2))).
    generalize dependent (proj2' (proj2' (ty_match_inv Hty2))).
    generalize dependent (term_rep gamma_valid pd vt pf vv tm v
      (proj1' (ty_match_inv Hty2))).
    (*Get hypotheses we need*)
    clear -H0 H1. (*do we need Hty2/info about pattern typing?*)
    induction ps as [|phd ptl IH]; simpl.
    (*TODO: we actually need non-exhaustiveness here*)
    + admit.
    + intros d Hall1 Hall2 Hall3 Hall4.
      destruct phd as [phd tdh]; simpl in *.
      rewrite match_val_single_irrel with (Hval2:=(Forall_inv Hall2)).
      simpl.
      destruct (match_val_single gamma_valid pd vt v phd
        (Forall_inv Hall2) d) as [l1|] eqn : Hmatch.
      * (*use original IH*) rewrite Forall_forall in H0; rewrite H0 with (Hty1:=Hty1)(Hty2:=Forall_inv Hall1); simpl; auto.
        -- rewrite tm_change_vv with (t:=t1)(v2:=vv); [reflexivity|].
          intros x Hinx. rewrite extend_val_notin; auto.
          rewrite <- (match_val_single_free_var _ _ _ _ _ _ _ _ _ Hmatch).
          intros Hinx1.
          apply (H1 x); split; auto. rewrite !in_app_iff; auto.
        -- eapply disj_sublist. apply H1. eapply sublist_trans. apply sublist_app_r.
          eapply sublist_trans. apply sublist_app_l. apply sublist_app_r.
      * (*Use IH*) apply IH.
        -- inversion H0; subst; auto.
        -- eapply disj_sublist. apply H1. unfold sublist. intros x. rewrite !in_app_iff.
          intros; destruct_all; auto.
  - (*epsilon*)
    split_all_dec_eq; auto; [ apply term_rep_irrel|].
    f_equal. repeat (apply functional_extensionality_dep; intros).
    erewrite fmla_rep_irrel.
    erewrite fmla_change_vv. reflexivity.
    intros y Hiny. unfold substi. destruct (vsymbol_eq_dec y v); subst; auto.
    unfold eq_sym; simpl. apply dom_cast_eq.
Admitted.

(*And the same for formulas - can we prove easier?*)
Lemma f_insert_rep {gamma} (gamma_valid: valid_context gamma) pd vt pf vv f1 f2 Hty Hty1 Hty2
  (Hdisj: disj (fmla_fv f1) (fmla_bnd f2)):
  formula_rep gamma_valid pd vt pf vv (f_insert f1 f2) Hty =
  eqb (formula_rep gamma_valid pd vt pf vv f1 Hty1)
    (formula_rep gamma_valid pd vt pf vv f2 Hty2).
Proof.
  revert vv f1 Hdisj Hty Hty1 Hty2.
  apply (formula_ind (fun _ => True) (fun f2 => forall vv f1,
    disj (fmla_fv f1) (fmla_bnd f2) ->
    forall Hty Hty1 Hty2,
    formula_rep gamma_valid pd vt pf vv
    (f_insert f1 f2) Hty =
  eqb
    (formula_rep gamma_valid pd vt pf vv f1 Hty1)
  (formula_rep gamma_valid pd vt pf vv f2 Hty2))); simpl; intros; simpl_rep_full; auto;
  try solve[f_equal; try solve[apply fmla_rep_irrel]; auto; 
    solve[repeat(f_equal; auto; apply fmla_rep_irrel)]].
  - (*Fpred*)
    f_equal; [apply fmla_rep_irrel |f_equal]. apply get_arg_list_eq.
    rewrite Forall_forall; intros; apply term_rep_irrel.
  - (*Feq*) f_equal; [apply fmla_rep_irrel|].
    split_all_dec_eq; [| | reflexivity]; apply term_rep_irrel.
  - (*Flet*) 
    rewrite H0 with (Hty1:=Hty1)(Hty2:=(proj2' (typed_let_inv Hty2))).
    2: { eapply disj_sublist. apply H1. apply sublist_cons. apply sublist_app_r. }
    (*Use disj*)
    rewrite fmla_change_vv with (v2:=vv); auto.
    + erewrite (term_rep_irrel _ _ _ _ _ tm). reflexivity.
    + intros x Hinx. unfold substi. destruct (vsymbol_eq_dec x v); subst; auto.
      exfalso. apply (H1 v); split; simpl; auto.
  - (*Fif*)
    rewrite fmla_rep_irrel with (Hval2:= (proj1' (typed_if_inv Hty2))).
    destruct (formula_rep _ _ _ _ _ f1 _) eqn : Hrep.
    + erewrite H0; [reflexivity|].
      eapply disj_sublist. apply H2. eapply sublist_trans. apply sublist_app_l.
      apply sublist_app_r.
    + erewrite H1; [reflexivity|].
      eapply disj_sublist. apply H2. rewrite app_assoc. apply sublist_app_r.
  - (*Fmatch*)
    rewrite term_rep_irrel with (Hty2:=(proj1' (typed_match_inv Hty2))).
    generalize dependent (proj1' (proj2' (typed_match_inv Hty))).
    generalize dependent (proj2' (proj2' (typed_match_inv Hty))).
    generalize dependent (proj1' (proj2' (typed_match_inv Hty2))).
    generalize dependent (proj2' (proj2' (typed_match_inv Hty2))).
    generalize dependent (term_rep gamma_valid pd vt pf vv tm v
      (proj1' (typed_match_inv Hty2))).
    clear -H0 H1. 
    induction ps as [|phd ptl IH]; simpl.
    (*TODO: we actually need non-exhaustiveness here*)
    + admit.
    + intros d Hall1 Hall2 Hall3 Hall4.
      destruct phd as [phd tdh]; simpl in *.
      rewrite match_val_single_irrel with (Hval2:=(Forall_inv Hall2)).
      simpl.
      destruct (match_val_single gamma_valid pd vt v phd
        (Forall_inv Hall2) d) as [l1|] eqn : Hmatch.
      * (*use original IH*) rewrite Forall_forall in H0; rewrite H0 with (Hty1:=Hty1)(Hty2:=Forall_inv Hall1); simpl; auto.
        -- rewrite fmla_change_vv with (f:=f1)(v2:=vv); [reflexivity|].
          intros x Hinx. rewrite extend_val_notin; auto.
          rewrite <- (match_val_single_free_var _ _ _ _ _ _ _ _ _ Hmatch).
          intros Hinx1.
          apply (H1 x); split; auto. rewrite !in_app_iff; auto.
        -- eapply disj_sublist. apply H1. eapply sublist_trans. apply sublist_app_r.
          eapply sublist_trans. apply sublist_app_l. apply sublist_app_r.
      * (*Use IH*) apply IH.
        -- inversion H0; subst; auto.
        -- eapply disj_sublist. apply H1. unfold sublist. intros x. rewrite !in_app_iff.
          intros; destruct_all; auto.
Admitted.

Definition gen_bnd {b: bool} (t: gen_term b) : list vsymbol :=
  match b return gen_term b -> list vsymbol with
  | true => tm_bnd
  | false => fmla_bnd
  end t.

Lemma all_dec_eqb (b1 b2: bool):
  proj_sumbool _ _ (all_dec (b1 = b2)) = eqb b1 b2.
Proof.
  destruct (all_dec (b1 = b2)); subst; simpl.
  - destruct b2; reflexivity.
  - destruct b1; destruct b2; auto.
Qed.

Lemma t_insert_gen_rep {gamma} (gamma_valid: valid_context gamma) pd vt pf vv {b: bool}
  (t1 t2: gen_term b) (ty: gen_type b) Hty Hty1 Hty2
  (Hdisj: disj (gen_fv b t1) (gen_bnd t2)):
  formula_rep gamma_valid pd vt pf vv (t_insert_gen ty t1 t2) Hty =
  all_dec (gen_rep gamma_valid pd pf vt b vv ty t1 Hty1 = gen_rep gamma_valid pd pf vt b vv ty t2 Hty2).
Proof.
  destruct b; simpl.
  - apply t_insert_rep; auto.
  - rewrite all_dec_eqb. apply f_insert_rep; auto.
Qed.

Lemma t_insert_typed_inv {gamma} { ty t1 t2 }
  (Hty: formula_typed gamma (t_insert ty t1 t2)):
  term_has_type gamma t1 ty /\ term_has_type gamma t2 ty.
Proof.
  revert ty t1 Hty.
  apply (term_ind (fun t2 => forall ty t1 (Hty: formula_typed gamma (t_insert ty t1 t2)),
    term_has_type gamma t1 ty /\ term_has_type gamma t2 ty) (fun _ => True)); simpl; auto; intros;
  try solve[inversion Hty; subst; auto].
  - inversion Hty; subst. apply H0 in H6. 
    destruct_all. split; auto. constructor; auto.
  - inversion Hty; subst. apply H0 in H7. apply H1 in H8. destruct_all.
    split; auto. constructor; auto.
  - inversion Hty; subst.
    rewrite null_map in H8.
    split.
    + destruct ps as [|phd ptl]; try discriminate.
      simpl in H7.
      (*Idea: get first pattern and use IH*)
      specialize (H7 _ (or_introl eq_refl)). simpl in H7.
      rewrite Forall_forall in H0.
      apply H0 in H7; simpl; auto. destruct_all; auto.
    + constructor; auto.
      * (*Prove pat type*)
        intros x Hinx.
        specialize (H6 (fst x, t_insert ty t1 (snd x))).
        apply H6. rewrite in_map_iff. exists x. auto.
      * (*Prove term type*)
        intros x Hinx.
        specialize (H7 (fst x, t_insert ty t1 (snd x))).
        simpl in H7.
        forward H7.
        {
          rewrite in_map_iff; exists x; auto.
        }
        rewrite Forall_forall in H0; apply H0 in H7.
        -- destruct_all; assumption.
        -- rewrite in_map_iff; exists x; auto.
Qed.

Lemma f_insert_typed_inv {gamma} { f1 f2 }
  (Hty: formula_typed gamma (f_insert f1 f2)):
  formula_typed gamma f1 /\ formula_typed gamma f2.
Proof.
  revert f1 Hty.
  apply (formula_ind (fun _ => True) (fun f2 => forall f1 (Hty: formula_typed gamma (f_insert f1 f2)),
    formula_typed gamma f1 /\ formula_typed gamma f2)); simpl; auto; intros;
  try solve[inversion Hty; subst; auto].
  - inversion Hty; subst. apply H0 in H6. 
    destruct_all. split; auto. constructor; auto.
  - inversion Hty; subst. apply H0 in H7. apply H1 in H8. destruct_all.
    split; auto. constructor; auto.
  - inversion Hty; subst.
    rewrite null_map in H8.
    split.
    + destruct ps as [|phd ptl]; try discriminate.
      simpl in H7.
      (*Idea: get first pattern and use IH*)
      specialize (H7 _ (or_introl eq_refl)). simpl in H7.
      rewrite Forall_forall in H0.
      apply H0 in H7; simpl; auto. destruct_all; auto.
    + constructor; auto.
      * (*Prove pat type*)
        intros x Hinx.
        specialize (H6 (fst x, f_insert f1 (snd x))).
        apply H6. rewrite in_map_iff. exists x. auto.
      * (*Prove term type*)
        intros x Hinx.
        specialize (H7 (fst x,  f_insert f1 (snd x))).
        simpl in H7.
        forward H7.
        {
          rewrite in_map_iff; exists x; auto.
        }
        rewrite Forall_forall in H0; apply H0 in H7.
        -- destruct_all; assumption.
        -- rewrite in_map_iff; exists x; auto.
Qed.

Lemma t_insert_gen_typed_inv {gamma} {b} {ty: gen_type b} {t1 t2: gen_term b}
  (Hty: formula_typed gamma (t_insert_gen ty t1 t2)):
  @gen_typed gamma b t1 ty /\ @gen_typed gamma b t2 ty.
Proof.
  destruct b; simpl in *.
  - apply t_insert_typed_inv; auto.
  - apply f_insert_typed_inv; auto.
Qed.

Lemma gen_app_fv {b: bool} (ls: gen_sym b) (tys: list vty) (tms: list term):
  gen_fv b (gen_app b ls tys tms) =
  big_union vsymbol_eq_dec tm_fv tms.
Proof.
  destruct b; auto.
Qed.

Lemma a_convert_gen_bnd {b: bool} (t: gen_term b) (l: list vsymbol) (x: vsymbol):
  In x l ->
  ~ In x (gen_bnd (a_convert_gen t l)).
Proof.
  destruct b; simpl in *.
  - apply a_convert_t_bnd.
  - apply a_convert_f_bnd.
Qed.

Lemma gen_rep_a_convert {b: bool} {gamma} (gamma_valid: valid_context gamma) pd pf vt vv (ty: gen_type b)
  (e: gen_term b) (vs: list vsymbol) Hty1 Hty2:
  gen_rep gamma_valid pd pf vt b vv ty (a_convert_gen e vs) Hty1 =
  gen_rep gamma_valid pd pf vt b vv ty e Hty2.
Proof.
  destruct b; simpl in *.
  - erewrite term_rep_irrel. erewrite <- a_convert_t_rep. reflexivity.
  - erewrite fmla_rep_irrel. erewrite <- a_convert_f_rep. reflexivity.
Qed.

Ltac gen_dom_cast_eq :=
  match goal with
        | |- context [dom_cast ?d ?Heq ?t] => generalize dependent Heq
  end.

Definition gen_fpsym {b: bool} (ls: gen_sym b) : fpsym :=
  match b return gen_sym b -> fpsym with
  | true => f_sym
  | false =>p_sym
  end ls.

Check fun_defined.
Definition funpred_defined (gamma: context) {b: bool} :=
  match b return gen_sym b -> list vsymbol -> gen_term b -> Prop with
  | true => fun_defined gamma
  | false => pred_defined gamma
  end.

(*The main result: the axiom we add holds. We factor out because we need in multiple places*)
Lemma rec_axiom_true {gamma} (gamma_valid: valid_context gamma) pd pf vt vv
{b: bool} (ls: gen_sym b) (vs: list vsymbol) (e: gen_term b)
(pf_full: full_interp gamma_valid pd pf)
(Hty: formula_typed gamma (snd (rec_axiom ls vs e)))
(Hval: funpred_def_valid_type gamma (gen_funpred_def b ls vs e))
(Hdef: funpred_defined gamma ls vs e):
formula_rep gamma_valid pd vt pf vv
  (snd (rec_axiom ls vs e)) Hty.
Proof.
  assert (Hfull:=pf_full).
  destruct Hfull as [Hfun [Hpred _]].
  unfold rec_axiom. simpl.
  (*need for [fforalls_rep]*)
  assert (Hty1: formula_typed gamma
    (t_insert_gen (gen_sym_ret ls)
    (gen_app b ls (map vty_var (gen_sym_params ls))
    (map Tvar vs))
    (a_convert_gen e vs))).
  { unfold rec_axiom in Hty; simpl in Hty.
    apply fforalls_typed_inv in Hty; apply Hty.
  }
  rewrite fforalls_rep' with (Hval1:=Hty1).
  apply simpl_all_dec. intros h.
  assert (Hty2:=Hty1).
  apply t_insert_gen_typed_inv in Hty2.
  destruct Hty2 as [Htyapp Htyalph].
  rewrite t_insert_gen_rep with (Hty1:=Htyapp) (Hty2:=Htyalph).
  2: {
    (*Prove disj*)
    rewrite gen_app_fv. clear.
    intros x [Hinx1 Hinx2].
    simpl_set. destruct Hinx1 as [t [Hint Hinx1]].
    rewrite in_map_iff in Hint.
    destruct Hint as [v [Ht Hinv]]; subst.
    simpl in Hinx1. destruct Hinx1 as [Hvx | []]; subst.
    apply (a_convert_gen_bnd _ _ _ Hinv Hinx2).
  }
  apply simpl_all_dec.
  (*First, simplify alpha**)
  apply gen_funpred_def_valid_type in Hval.
  destruct Hval as [Htye [Hsubfv [Hsubty [Hnodup Hvs]]]].
  rewrite gen_rep_a_convert with (Hty2:=Htye).
  (*Need twice*)
  set (ls' := gen_fpsym ls).
  set (srts := (map (v_subst vt) (map vty_var (s_params ls')))) in *.
  assert (srts_len: length srts = length (s_params ls')).
  {
    subst srts. rewrite !map_length; auto.
  }
  assert (srts_eq: srts = map vt (s_params ls')). {
    unfold srts. rewrite !map_map. apply map_ext. intros a.
    apply sort_inj. reflexivity. 
  }
  assert (Hvt: vt_with_args vt (s_params ls') srts = vt).
  {
    rewrite srts_eq.
    rewrite vt_with_args_eq; auto.
    apply s_params_Nodup.
  }
  assert (Hvveq: forall x
        (Hinxfv: In x (gen_fv b e))
        (Heq: v_subst (vt_with_args vt (s_params ls') srts)
          (snd x) =
        v_subst vt (snd x))
        (Hlen1: length (map Tvar vs) = length (s_args ls') )
        (*= length (map vty_var (s_params ls)))*) Hlen2 Hall,
          substi_mult pd vt vv vs h x =
        dom_cast (dom_aux pd) Heq
          (val_with_args pd
          (vt_with_args vt (s_params ls') srts)
          (upd_vv_args_srts (s_params ls') srts
          (eq_sym srts_len) (s_params_Nodup ls') pd vt
          (substi_mult pd vt vv vs h))
          vs
          (get_arg_list pd vt (map vty_var (s_params ls'))
          (map Tvar vs)
          (term_rep gamma_valid pd vt pf
          (substi_mult pd vt vv vs h))
          (s_params_Nodup ls') Hlen1 Hlen2 Hall)
          x)).
  {
    intros x Hinxfv Heq Hlen1 Hlen2 Hall.
    assert (Hinvs: In x vs) by (apply Hsubfv in Hinxfv; auto).
    (*So look at nth*)
    destruct (In_nth _ _ vs_d Hinvs) as [j [Hj Hx]]; subst x.
    rewrite substi_mult_nth' with (Hi:=Hj); [| apply NoDup_map_inv in Hnodup; assumption].
    unfold upd_vv_args_srts.
    simpl in Hvs.
    assert (Hlslen: length (s_args ls') = length (gen_sym_args ls)). {
      destruct b; auto.
    }
    assert (Hvslen: length (s_args ls') = length vs) by (rewrite Hlslen, <- Hvs; rewrite map_length; auto).
    assert (Heqjth: nth j (sym_sigma_args ls' srts) s_int =
      v_subst (vt_with_args vt (s_params ls') srts) (snd (nth j vs vs_d))).
    {
      rewrite Hvt.
      unfold sym_sigma_args, ty_subst_list_s.
      rewrite map_nth_inbound with (d2:=vty_int); [| lia].
      replace (snd (nth j vs vs_d)) with (nth j (map snd vs) vty_int).
      2: { rewrite map_nth_inbound with (d2:=vs_d); auto. }
      rewrite Hvs. simpl.
      rewrite <- vt_with_args_cast with (vt:=vt); auto.
      - rewrite Hvt. destruct b; reflexivity.
      - intros x Hinx. pose proof (s_args_wf ls') as Hsub. unfold is_true in Hsub.
        rewrite <- (reflect_iff _ _ (check_args_correct _ _) ) in Hsub.
        specialize (Hsub (nth j (s_args ls') vty_int)); apply Hsub; auto.
        apply nth_In. lia.
      - apply s_params_Nodup.
    }
    rewrite val_with_args_in' with (i:=j)(Heq:=Heqjth); auto;
    [| apply NoDup_map_inv in Hnodup; assumption | unfold sym_sigma_args, ty_subst_list_s; 
      rewrite map_length; lia].
    rewrite !dom_cast_compose.
    (*Now deal with [get_arg_list]*) 
    assert (Hj': j < Datatypes.length (s_args ls')) by lia. 
    rewrite (get_arg_list_hnth_unif pd vt ls'
      (map Tvar vs) (term_rep gamma_valid pd vt pf
      (substi_mult pd vt vv vs h)) (ltac:(intros; apply term_rep_irrel))
      Hlen1 
      ) with (Hi:=Hj').
    rewrite !dom_cast_compose. symmetry.
    gen_dom_cast_eq.
    intros Heq2.
    (*Now simplify to variable*)
    match goal with
    | |- context [term_rep ?v ?pd ?vt ?pf ?vv ?t ?ty ?Hty] => generalize dependent Hty
    end.
    rewrite map_nth_inbound with (d2:=vs_d) by auto.
    intros Htyv.
    simpl_rep_full.
    unfold var_to_dom. rewrite !dom_cast_compose.
    gen_dom_cast_eq. intros Heq3.
    rewrite substi_mult_nth' with (Hi:=Hj); [| apply NoDup_map_inv in Hnodup; assumption ].
    rewrite !dom_cast_compose. apply dom_cast_eq.
  }
  (*Now case on b*)
  destruct b; simpl.
  * simpl_rep_full. unfold cast_dom_vty. rewrite !dom_cast_compose.
    gen_dom_cast_eq.
    intros Heq.
    rewrite (Hfun ls vs e Hdef srts srts_len _ vt (substi_mult pd vt vv vs h)).
    rewrite !dom_cast_compose.
    gen_dom_cast_eq.
    intros Heq2.
    rewrite tm_change_vt with (vt2:=vt)(vv2:=(substi_mult pd vt vv vs h))(Heq:=eq_sym Heq2).
    -- rewrite !dom_cast_compose, eq_trans_sym_inv_l. apply term_rep_irrel.
    -- (*prove vt equivalent*)
      intros x Hinx.
      rewrite srts_eq.
      rewrite vt_with_args_eq; auto.
      apply s_params_Nodup.
    -- (*prove vv equivalent*)
      intros x Hinxfv Heq3. apply Hvveq; auto.
  * (*Formula case - repetitive*)
    simpl_rep_full. 
    rewrite (Hpred ls vs e Hdef srts srts_len _ vt (substi_mult pd vt vv vs h)).
    rewrite fmla_change_vt with (vt2:=vt)(vv2:=(substi_mult pd vt vv vs h)).
    -- apply fmla_rep_irrel.
    -- (*prove vt equivalent*)
      intros x Hinx.
      rewrite srts_eq.
      rewrite vt_with_args_eq; auto.
      apply s_params_Nodup.
    -- (*prove vv equivalent*)
      intros x Hinxfv Heq. apply Hvveq. assumption.
Qed.


Theorem gen_axioms_sound which nonrec : sound_trans (single_trans (gen_axioms which nonrec)).
Proof.
  apply add_axioms_sound.
  - apply gen_axioms_typed.
  - intros.
    (*Now the hard part - show log conseq*)
    unfold log_conseq_gen.
    intros.
    assert (Hfull:=pf_full).
    unfold satisfies.
    intros.
    (*First, get more info about fmla*)
    rewrite in_map_iff in H.
    destruct H as [ax [Hfmla Hinax]]; subst.
    rewrite in_concat in Hinax.
    destruct Hinax as [constrs [Hinconstrs Hinax]]; subst.
    rewrite in_map_iff in Hinconstrs.
    destruct Hinconstrs as [d [Hconstrs Hind]]; subst.
    destruct d; try contradiction. 
    + unfold axioms_of_def in Hinax.
      rewrite <- In_rev, in_concat in Hinax.
      destruct Hinax as [axs [Hinaxs Hinax]].
      rewrite in_map_iff in Hinaxs.
      destruct Hinaxs as [fd [Haxs Hinfd]].
      destruct (gen_funpred_def_match fd) as [b [[ls vs] e]] eqn : Hgen; simpl in *. subst.
      destruct (which b ls) eqn : Hwhich; [| subst; contradiction].
      apply gen_funpred_def_match_eq in Hgen. subst.
      destruct Hinax as [Hinax | []]; subst.
      apply rec_axiom_true; auto.
      * apply (recursive_valid_type task_gamma_valid Hind Hinfd).
      * destruct b; simpl in *. 
        -- unfold fun_defined. left.
          exists l. split; auto. apply in_mutfuns; auto.
        -- unfold pred_defined; left.
          exists l; split; auto; apply in_mutfuns; auto.
    + destruct nonrec; [|contradiction].
      revert Hinax.
      unfold axioms_of_def.
      rewrite <- In_rev, in_concat. 
      simpl. intros [axs [[Hinaxs | []] Hax]].
      destruct (gen_funpred_def_match f) as [b [[ls vs] e]] eqn : Hgen; simpl in *.
      destruct (which b ls) eqn : Hwhich; [| subst; contradiction]. subst.
      destruct Hax as [Hax | []]. subst. 
      apply gen_funpred_def_match_eq in Hgen. subst.
      apply rec_axiom_true; auto.
      * apply (nonrec_valid_type task_gamma_valid Hind).
      * destruct b; simpl in *.  
        -- unfold fun_defined; auto.
        -- unfold pred_defined; auto.
Qed.     

(*Part 3: New Context*)

(*Just like with [eliminate_inductive], have to convert interpretations from 1 context to
  the other*)
Section NewContext.

(*Easier, fewer cases*)
Print Either.
Definition is_rec_nonrec (x: def) : Either (list funpred_def) (option funpred_def) :=
  match x with
  | recursive_def l => Left _ _ l
  | nonrec_def f => Right _ _ (Some f)
  | _ => Right _ _ None
  end.


Definition gen_new_ctx_gamma' which (nonrec: bool) (gamma: context) : context :=
  concat (map (fun x =>
    match (is_rec_nonrec x) with
    | Left l =>  rev (decl_list_of_def which false l)
    | Right (Some l) => if nonrec then rev (decl_list_of_def which true [l]) else [x]
    | Right None => [x]
    end) gamma).

Lemma gen_new_ctx_gamma_equiv which nonrec gamma:
  gen_new_ctx_gamma which nonrec gamma =
  gen_new_ctx_gamma' which nonrec gamma.
Proof.
  unfold gen_new_ctx_gamma, gen_new_ctx_gamma'.
  f_equal. apply map_ext.
  intros. destruct a; simpl; auto.
Qed.

Print decl_list_of_def.

Lemma app_nil_iff {A: Type} (l1 l2: list A):
  l1 ++ l2 = nil <-> l1 = nil /\ l2 = nil.
Proof.
  split.
  - apply app_eq_nil.
  - intros [Hl1 Hl2]; subst; auto.
Qed.

Lemma filter_map_in {A B: Type} (f: A -> option B) (l: list A) (x: B):
  In x (Pattern.filter_map f l) ->
  exists y, In y l /\ f y = Some x.
Proof.
  induction l as [| h t IH ]; simpl; [contradiction|].
  destruct (f h) as [z|] eqn : Hfh.
  - simpl. intros [Hzx | Hinx]; subst; eauto.
    apply IH in Hinx. destruct_all; eauto.
  - intros Hin. apply IH in Hin; destruct_all; eauto.
Qed.

Lemma in_filter_map {A B: Type} (f: A -> option B) (l: list A) (x: B) (y: A):
  In y l ->
  f y = Some x ->
  In x (Pattern.filter_map f l).
Proof.
  induction l as [| h t IH ]; simpl; [contradiction|].
  intros [Hhy | Hiny] Hfy; subst.
  - rewrite Hfy. simpl; auto.
  - destruct (f h); simpl; auto.
Qed.

Lemma in_filter_map_iff {A B: Type} (f: A -> option B) (l: list A) (x: B):
  In x (Pattern.filter_map f l) <->
  exists y, In y l /\ f y = Some x.
Proof.
  split. apply filter_map_in.
  intros [y [Hiny Hfy]]. apply (in_filter_map _ _ _ _ Hiny Hfy).
Qed.

Lemma get_recfun_defs_typesyms which nonrec: forall l,
  concat (map typesyms_of_def (rev (decl_list_of_def which nonrec l))) = nil.
Proof.
  intros l.
  unfold decl_list_of_def. rewrite map_rev, map_app, rev_app_distr, concat_app.
  apply app_nil_iff. split.
  - unfold decls_of_def. simpl.
    destruct (Pattern.filter_map _ l) as [| h t] eqn : Hpat; auto.
    destruct t as [| h2 t2]; simpl; auto.
    destruct nonrec; auto.
  - unfold decls_of_def. simpl.
    apply concat_nil_Forall.
    apply Forall_rev.
    rewrite Forall_map. rewrite Forall_forall. intros x Hinx.
    apply filter_map_in in Hinx.
    destruct Hinx as [y [Hiny Hx]].
    destruct (gen_funpred_def_match y) as [b [[ls vs] e]]; simpl in Hx.
    destruct (which b ls); inversion Hx; simpl; auto; destruct b; auto.
Qed.

Definition gen_syms_of_def {b: bool} : def -> list (gen_sym b) :=
  match b return def -> list (gen_sym b) with
  | true => funsyms_of_def
  | false => predsyms_of_def
  end.

Definition gen_syms_of_rec {b: bool} : list funpred_def -> list (gen_sym b) :=
  match b return list funpred_def -> list (gen_sym b) with
  | true => funsyms_of_rec
  | false => predsyms_of_rec
  end.

Definition gen_syms_of_nonrec {b: bool} : funpred_def -> list (gen_sym b) :=
  match b return funpred_def -> list (gen_sym b) with
  | true => funsyms_of_nonrec
  | false => predsyms_of_nonrec
  end.

Lemma gen_syms_of_def_recursive {b: bool} l:
 @gen_syms_of_def b (recursive_def l) = gen_syms_of_rec l.
Proof.
  destruct b; reflexivity.
Qed.

Lemma gen_syms_of_def_nonrec {b: bool} l:
 @gen_syms_of_def b (nonrec_def l) = gen_syms_of_nonrec l.
Proof.
  destruct b; reflexivity.
Qed.

Lemma gen_syms_of_abs {b: bool} l:
  @gen_syms_of_def b (gen_abs l) = [l].
Proof.
  destruct b; auto.
Qed.

Lemma in_gen_syms_of_rec {b: bool} (l: list funpred_def) (f: gen_sym b) :
  In f (gen_syms_of_rec l) <-> exists vs e, In (gen_funpred_def b f vs e) l.
Proof.
  destruct b; simpl in *.
  - unfold funsyms_of_rec.
    rewrite in_omap_iff. split.
    + intros [fd [Hinfd Hf]]. destruct fd; inversion Hf; subst. eexists. eexists. apply Hinfd.
    + intros [vs [e Hin]]. eexists. split; [apply Hin|reflexivity].
  - unfold predsyms_of_rec.
    rewrite in_omap_iff. split.
    + intros [fd [Hinfd Hf]]. destruct fd; inversion Hf; subst. eexists. eexists. apply Hinfd.
    + intros [vs [e Hin]]. eexists. split; [apply Hin|reflexivity].
Qed.

Lemma get_recfun_defs_syms which nonrec {b: bool}: forall l x,
  In x (concat (map (@gen_syms_of_def b) (rev (decl_list_of_def which nonrec l)))) <->
  In x (gen_syms_of_rec l).
Proof.
  intros l x.
  unfold decl_list_of_def. rewrite map_rev, map_app, rev_app_distr, concat_app, !in_app_iff.
  (*rewrite as partition*)
  rewrite (elements_in_partition (fun x => which b x) (gen_syms_of_rec l)).
  2: apply partition_as_filter.
  rewrite (or_comm (In x (filter _ _))).
  apply or_iff.
  - unfold decls_of_def. simpl.
    rewrite in_concat, in_filter, in_gen_syms_of_rec.
    setoid_rewrite <- In_rev.
    setoid_rewrite in_map_iff.
    split.
    + intros [l1 [[d [Hl1 Hind]] Hinx]]; subst.
      destruct (Pattern.filter_map _ _) as [| h [|h1 t]] eqn : Hpat; [contradiction| |].
      * assert (Hinh: In h [h]) by (simpl; auto).
        revert Hinh. rewrite <- Hpat; intros Hinh; apply filter_map_in in Hinh.
        destruct Hinh as [h1 [Hinh1 Hhh1]].
        destruct (gen_funpred_def_match h1) as [b1 [[ls vs] e]] eqn : Hdef; simpl in Hhh1.
        apply gen_funpred_def_match_eq in Hdef; subst; simpl in *.
        destruct (which b1 ls) eqn : Hwhich; inversion Hhh1; subst.
        destruct nonrec; simpl in Hind; destruct Hind as [Hhd | []]; subst;
        destruct b; destruct b1; simpl in Hinx; try contradiction;
        destruct Hinx as [Hls | []]; subst; rewrite Hwhich; split; auto;
        do 2 eexists; apply Hinh1.
      * simpl in Hind. destruct Hind as [Hd | []]; subst.
        rewrite <- Hpat in Hinx. clear Hpat.
        rewrite gen_syms_of_def_recursive, in_gen_syms_of_rec in Hinx.
        destruct Hinx as [vs [e Hinfd]].
        apply filter_map_in in Hinfd.
        destruct Hinfd as [fd1 [Hinfd1 Hfd]].
        destruct (gen_funpred_def_match fd1) as [b1 [[ls1 vs1] e1]] eqn : Hdef; simpl in Hfd.
        apply gen_funpred_def_match_eq in Hdef; subst; simpl in *.
        destruct (which b1 ls1) eqn : Hwhich; inversion Hfd; subst.
        destruct b; destruct b1; simpl in *; inversion H0; subst; rewrite Hwhich; split; auto;
        do 2 eexists; apply Hinfd1.
    + (*other direction*)
      intros [Hwhich [vs [e Hinfd]]].
      assert (Hfinpat: In (gen_funpred_def b x vs e) (Pattern.filter_map
        (fun x : funpred_def =>
      let (b, p) := gen_funpred_def_match x in let
        (p0, _) := p in let (ls, _) := p0 in if which b ls then
      None else Some x)
        l)).
      {
        eapply in_filter_map. apply Hinfd. 
        destruct (gen_funpred_def_match _) as [b1 [[ls1 vs1] e1]] eqn : Hdef.
        apply gen_funpred_def_match_eq in Hdef; subst; simpl in *.
        destruct b; destruct b1; simpl in *; inversion Hdef; subst;
        [destruct (which true x) | destruct (which false x)]; try discriminate; reflexivity.
      }
      destruct (Pattern.filter_map _ _) as [| h [|h1 t1]] eqn : Hpat; [contradiction| |].
      * simpl. destruct Hfinpat as [Hh | []]; subst.
        destruct nonrec.
        -- eexists. split. eexists. split. reflexivity.
          left; reflexivity. rewrite gen_syms_of_def_nonrec.
          destruct b; simpl in *; auto.
        -- eexists. split. eexists. split. reflexivity.
          left; reflexivity. rewrite gen_syms_of_def_recursive.
          destruct b; simpl in *; auto.
      * eexists. split. eexists. split. reflexivity. simpl. left; reflexivity.
        rewrite gen_syms_of_def_recursive. rewrite in_gen_syms_of_rec.
        exists vs. exists e. assumption.
  - (*Other proof - easier, dont case on pat result*)
    rewrite in_filter, in_concat.
    setoid_rewrite <- In_rev.
    setoid_rewrite in_map_iff.
    setoid_rewrite in_filter_map_iff.
    split.
    + intros [fs [[d [Hfs [fd [Hinfd Hfd]]]] Hinfs]]; subst.
      rewrite in_gen_syms_of_rec.
      destruct (gen_funpred_def_match fd) as [b1 [[ls vs] e]] eqn : Hdef; simpl in Hfd.
      apply gen_funpred_def_match_eq in Hdef; subst; simpl in *.
      destruct (which b1 ls) eqn : Hwhich; inversion Hfd; subst.
      (*b and b1 not the same*)
      destruct b; destruct b1; simpl in *; try contradiction;
      destruct Hinfs as [Hx | []]; subst; rewrite Hwhich; split; auto;
      do 2 eexists; eassumption.
    + rewrite in_gen_syms_of_rec. intros [Hwhich [vs [e Hinfd]]].
      eexists. split. 
      * eexists. split; [reflexivity|]. eexists. split; [apply Hinfd|].
        destruct (gen_funpred_def_match _) as [b1 [[ls1 vs1] e1]] eqn : Hdef.
        apply gen_funpred_def_match_eq in Hdef; subst; simpl in *.
        destruct b; destruct b1; inversion Hdef; subst;
        rewrite Hwhich; reflexivity.
      * rewrite gen_syms_of_abs. simpl. auto.
Qed.

(*The corollaries*)
Lemma get_recfun_defs_funsyms which nonrec: forall l x,
  In x (concat (map funsyms_of_def (rev (decl_list_of_def which nonrec l)))) <->
  In x (funsyms_of_rec l).
Proof.
  intros l x.
  apply get_recfun_defs_syms with (b:=true).
Qed.

Lemma get_recfun_defs_predsyms which nonrec: forall l x,
  In x (concat (map predsyms_of_def (rev (decl_list_of_def which nonrec l)))) <->
  In x (predsyms_of_rec l).
Proof.
  intros l x.
  apply get_recfun_defs_syms with (b:=false).
Qed.

Lemma funsyms_of_rec_single l:
  funsyms_of_rec [l] = funsyms_of_nonrec l.
Proof. unfold funsyms_of_rec, funsyms_of_nonrec. destruct l; simpl; reflexivity. Qed.

Lemma predsyms_of_rec_single l:
  predsyms_of_rec [l] = predsyms_of_nonrec l.
Proof. unfold predsyms_of_rec, predsyms_of_nonrec. destruct l; simpl; reflexivity. Qed.

(*The new context has the same signature*)
Lemma gen_new_ctx_gamma_eq_sig which nonrec gamma:
  eq_sig (gen_new_ctx_gamma' which nonrec gamma) gamma.
Proof.
  unfold gen_new_ctx_gamma'. induction gamma; simpl.
  - apply eq_sig_refl.
  - destruct (is_rec_nonrec a) as [l | l] eqn : Hrec.
    + destruct a; inversion Hrec; subst. (*rec case*)
      unfold eq_sig in *; simpl in *; split_all.
      * intros. unfold sig_t; simpl.
        rewrite map_app, concat_app, get_recfun_defs_typesyms; auto.
      * intros. unfold sig_f; simpl.
        rewrite map_app, concat_app, !in_app_iff, get_recfun_defs_funsyms.
        apply or_iff_compat_l; auto.
      * intros. unfold sig_p; simpl.
        rewrite map_app, concat_app, !in_app_iff, get_recfun_defs_predsyms.
        apply or_iff_compat_l; auto.
    + destruct l as [l|]; [|apply eq_sig_cons; auto]. (*nonrec case*)
      destruct a; inversion Hrec; subst.

      unfold eq_sig in *; simpl in *; split_all.
      * intros. unfold sig_t; simpl.
        rewrite map_app, concat_app. destruct nonrec; [rewrite get_recfun_defs_typesyms; auto|].
        simpl. auto.
      * intros. unfold sig_f; simpl.
        rewrite map_app, concat_app, !in_app_iff. destruct nonrec.
        -- rewrite get_recfun_defs_funsyms; rewrite funsyms_of_rec_single; 
           apply or_iff_compat_l; auto.
        -- simpl. rewrite app_nil_r. apply or_iff_compat_l; auto.
      * intros. unfold sig_p; simpl.
        rewrite map_app, concat_app, !in_app_iff. destruct nonrec.
        -- rewrite get_recfun_defs_predsyms; rewrite predsyms_of_rec_single; 
           apply or_iff_compat_l; auto.
        -- simpl. rewrite app_nil_r. apply or_iff_compat_l; auto.
Qed.

Lemma gen_abs_not_concrete{b} l:
  concrete_def (@gen_abs b l) = false.
Proof. destruct b; auto. Qed.

(*Suppose we have a recursive definition on list l. Then we can take a sublist of l
  and the definition is still a valid recursive function*)
(*TODO: we need both recursive and nonrecursive
  easist way probably with filter (as I am doing) - but ignore cases*)
(*Lemma filter_rec_def_valid gamma l (p: funpred_def -> bool):
  valid_context (recursive_def l :: gamma) ->
  valid_context (recursive_def (filter p l) :: 
    (map gen_abs (filter (fun x => negb (p x)) l)) :: gamma).
Proof.
  intros Hval. inversion Hval; subst; simpl in *.
  constructor; auto.
  - simpl. unfold funsyms_of_rec. *)
  
(*Let's see if we can prove
1. If we take any definition, and we convert all of its declared type/fun/predsysm to
  abstract symbols (in any order), then the resulting context is still well-formed
  (we may have proved similar for eliminate_inductive)
2. If we take a recursive definition and add some of the symbols as abstract and the rest as
  concrete, the result is still well-formed
3. Nonrec case follows from (1)*)

Print def. 

(*Prove for recursive definition only - TODO: should try to factor this out, but it is difficult*)

(*Prove generic for recursive: if we abstract some of them, then keep the rest in
  a recursive def, everything is still fine*)
Print valid_context.
(* 
Lemma filter_rec_def_valid gamma l (p: funpred_def -> bool):
  valid_context (recursive_def l :: gamma) ->
  valid_context (
    recursive_def (filter p l) :: 
    Pattern.filter_map (fun x => 
      match gen_funpred_def_match x with
      | (b, (ls, _, _)) => if which b ls

    (map gen_abs (filter (fun x => negb (p x)) l)) :: gamma). *)


(*To reduce number of cases*)
Lemma rewrite_concrete_recs which l:
  match snd (decls_of_def which false l) with
| Some d => [d]
| None => []
end =
match Pattern.filter_map
  (fun x : funpred_def =>
let (b, p) := gen_funpred_def_match x in let
  (p0, _) := p in let (ls, _) := p0 in if which b ls then
None else Some x)
  l with
| nil => nil
| l => [recursive_def l]
end.
Proof.
  simpl.
  destruct (Pattern.filter_map _ _); simpl; auto.
  destruct l0; auto.
Qed.

Lemma gen_abs_concrete {b: bool} (ls: gen_sym b):
  concrete_def (gen_abs ls) = false.
Proof.
  destruct b; auto.
Qed.

Lemma gen_abs_typesyms {b: bool} (ls: gen_sym b):
  typesyms_of_def (gen_abs ls) = nil.
Proof.
  destruct b; auto.
Qed.

Fixpoint sublist_strong {A: Type} (eq_dec: forall x y, {x = y} + {x <> y}) (l1 l2: list A): bool :=
  match l1, l2 with
  | nil, _ => true
  | x1 :: t1, x2 :: t2 => (eq_dec x1 x2 && sublist_strong eq_dec t1 t2) || sublist_strong eq_dec l1 t2
  | _, nil => false
  end.

Lemma sublist_strong_in {A: Type} eq_dec (l1 l2: list A):
  sublist_strong eq_dec l1 l2 ->
  sublist l1 l2.
Proof.
  revert l1. unfold sublist. induction l2 as [| h2 t2 IH]; simpl; intros [| h1 t1]; auto;
  try contradiction.
  intros Hsub x [Hx | Hinx]; subst; bool_hyps; destruct Hsub as [Hsub1 | Hsub2];
  bool_hyps; subst; auto.
  - destruct (eq_dec x h2); subst; auto. discriminate.
  - right. apply (IH _ Hsub2 x); simpl; auto.
  - destruct (eq_dec h1 h2); subst; auto; [|discriminate]. right.
    apply (IH t1 H0 x); auto.
  - right. apply (IH _ Hsub2 x); simpl; auto.
Qed.

Lemma sublist_strong_nodup {A: Type} eq_dec (l1 l2: list A):
  sublist_strong eq_dec l1 l2 ->
  NoDup l2 ->
  NoDup l1.
Proof.
  revert l1. induction l2 as [| h2 t2 IH]; simpl; intros [| h1 t1]; auto; try discriminate;
  [constructor|]. intros Hsub Hnodup.
  inversion Hnodup; subst.
  apply orb_true_iff in Hsub.
  destruct Hsub as [Hsub | Hsub].
  - apply andb_true_iff in Hsub. destruct Hsub as [Heq Hsub]. destruct (eq_dec h1 h2); [subst| discriminate].
    constructor; auto. intros Hin. apply (sublist_strong_in _ _ _ Hsub) in Hin. contradiction.
  - apply (IH _ Hsub); auto.
Qed.

Lemma sublist_strong_app {A: Type} eq_dec (l1 l2 l3 l4: list A):
  sublist_strong eq_dec l1 l2 ->
  sublist_strong eq_dec l3 l4 ->
  sublist_strong eq_dec (l1 ++ l3) (l2 ++ l4).
Proof.
  revert l1 l3 l4. induction l2 as [| x2 t2 IH]; simpl;
  intros [| x1 t1] l3 l4; simpl; auto.
  - intros _ Hsub.
    destruct l3 as [| x3 t3]; auto.
    apply orb_true_iff. right. apply (IH nil); auto. destruct t2; auto.
  - intros Hsub1 Hsub2. apply orb_true_iff in Hsub1. apply orb_true_iff.
    destruct Hsub1 as [Hsub1 | Hsub1].
    + apply andb_true_iff in Hsub1. destruct Hsub1 as [Heq Hsub1].
      destruct (eq_dec x1 x2); [subst | discriminate]. simpl.
      left. apply IH; auto.
    + right. apply (IH (x1 :: t1)); auto.
Qed.

Lemma sublist_strong_nil {A: Type} eq_dec (l: list A):
  sublist_strong eq_dec nil l.
Proof. destruct l; auto. Qed.

Lemma sublist_strong_refl {A: Type} eq_dec (l: list A):
  sublist_strong eq_dec l l.
Proof.
  induction l as [| h t IH]; auto; simpl.
  apply orb_true_iff. left. apply andb_true_iff. split; auto.
  destruct (eq_dec h h); auto.
Qed.

Lemma sublist_strong_rev {A: Type} eq_dec (l1 l2: list A):
  sublist_strong eq_dec l1 l2 ->
  sublist_strong eq_dec (rev l1) (rev l2).
Proof.
  revert l1. induction l2 as [| x2 t2 IH]; intros [|x1 t1]; simpl; auto.
  - intros. apply sublist_strong_nil.
  - intros Hsub. apply orb_true_iff in Hsub.
    destruct Hsub as [Hsub | Hsub].
    + apply andb_true_iff in Hsub.
      destruct Hsub as [Heq Hsub].
      destruct (eq_dec x1 x2); [subst| discriminate].
      apply sublist_strong_app; auto.
      apply sublist_strong_refl.
    + apply IH in Hsub.
      simpl in Hsub.
      pose proof (sublist_strong_app eq_dec (rev t1 ++ [x1]) (rev t2) nil  [x2] Hsub
        (sublist_strong_nil eq_dec _)) as Hsubapp.
      rewrite app_nil_r in Hsubapp. apply Hsubapp.
Qed.

Lemma concat_rev_single {A: Type} (l: list (list A))
  (Hall: Forall (fun x => length x <= 1) l):
  concat (rev l) = rev(concat l).
Proof.
  induction l as [| h t IH]; simpl; auto.
  inversion Hall; subst.
  rewrite concat_app, rev_app_distr; simpl.
  rewrite app_nil_r.
  rewrite IH; auto. f_equal.
  destruct h as [| h1 t1]; simpl; auto.
  simpl in *. destruct t1; auto; simpl in *; lia.
Qed.

(*The funsyms that are turned abstract are a (strong) subset of
  the recursive funsyms - the order matters for NoDup, although we could
  prove a Permutation if we needed*)
Lemma funsyms_rec_sublist_strong which b l:
   sublist_strong funsym_eq_dec (concat
    (map funsyms_of_def
    (rev (fst (decls_of_def which b l)))))
    (rev (funsyms_of_rec l)).
Proof.
  rewrite map_rev.
  rewrite concat_rev_single.
  2: {
    rewrite Forall_map. simpl. rewrite Forall_forall.
    intros x. rewrite in_filter_map_iff. intros [y [Hiny Hx]].
    destruct (gen_funpred_def_match y) as [b1 [[ls vs] e]] eqn : Hdef.
    apply gen_funpred_def_match_eq in Hdef. subst.
    destruct (which b1 ls) eqn : Hwhich; inversion Hx; subst.
    destruct b1; auto.
  }
  apply sublist_strong_rev.
  (*Now all revs are gone*)
  induction l as [| h t IH]; simpl; auto.
  destruct (gen_funpred_def_match h) as [b1 [[ls vs] e]] eqn : Hdef.
  apply gen_funpred_def_match_eq in Hdef. subst.
  destruct (which b1 ls) eqn : Hwhich.
  - simpl. destruct b1; simpl in *; auto.
    destruct (funsym_eq_dec ls ls); auto. simpl.
    rewrite IH; auto.
  - destruct b1; simpl in *; auto. rewrite IH.
    destruct (concat _); auto. apply orb_true_r.
Qed.

(*And the same for predsyms*)
Lemma predsyms_rec_sublist_strong which b l:
   sublist_strong predsym_eq_dec (concat
    (map predsyms_of_def
    (rev (fst (decls_of_def which b l)))))
    (rev (predsyms_of_rec l)).
Proof.
  rewrite map_rev.
  rewrite concat_rev_single.
  2: {
    rewrite Forall_map. simpl. rewrite Forall_forall.
    intros x. rewrite in_filter_map_iff. intros [y [Hiny Hx]].
    destruct (gen_funpred_def_match y) as [b1 [[ls vs] e]] eqn : Hdef.
    apply gen_funpred_def_match_eq in Hdef. subst.
    destruct (which b1 ls) eqn : Hwhich; inversion Hx; subst.
    destruct b1; auto.
  }
  apply sublist_strong_rev.
  (*Now all revs are gone*)
  induction l as [| h t IH]; simpl; auto.
  destruct (gen_funpred_def_match h) as [b1 [[ls vs] e]] eqn : Hdef.
  apply gen_funpred_def_match_eq in Hdef. subst.
  destruct (which b1 ls) eqn : Hwhich.
  - simpl. destruct b1; simpl in *; auto.
    destruct (predsym_eq_dec ls ls); auto. simpl.
    rewrite IH; auto.
  - destruct b1; simpl in *; auto. rewrite IH.
    destruct (concat _); auto. apply orb_true_r.
Qed.

Lemma typesyms_rec_nil which b l:
  concat
    (map typesyms_of_def
    (rev (fst (decls_of_def which b l)))) = nil.
Proof.
  apply concat_nil_Forall. rewrite Forall_map. apply Forall_rev.
  simpl. rewrite Forall_forall. intros x. rewrite in_filter_map_iff.
  intros [fd [Hinfd Hx]].
  destruct (gen_funpred_def_match fd) as [b1 [[ls vs] e]] eqn : Hdef.
  apply gen_funpred_def_match_eq in Hdef. subst.
  destruct (which b1 ls); inversion Hx; subst; simpl; auto.
  apply gen_abs_typesyms.
Qed.


(*Add abstract symbols from recursive def still well-founded*)
Lemma add_rec_abs_valid {gamma gamma1} which b
  (* (gamma_valid: valid_context gamma) *)
  (gamma1_valid: valid_context gamma1)
  (l: list funpred_def)
  (Hwf1: Forall (wf_funsym (recursive_def l :: gamma)) (funsyms_of_rec l))
  (Hwf2: Forall (wf_predsym (recursive_def l :: gamma)) (predsyms_of_rec l))
  (Hnotsig1: Forall (fun f : funsym => ~ In f (sig_f gamma)) (funsyms_of_rec l))
  (Hnotsig2: Forall (fun f : predsym => ~ In f (sig_p gamma)) (predsyms_of_rec l))
  (Hnodup1: NoDup (funsyms_of_rec l))
  (Hnodup2: NoDup (predsyms_of_rec l))
  (Htseq: forall x, In x (sig_t gamma1) <-> In x (sig_t gamma))
  (Hfseq: forall x, In x (sig_f gamma1) <-> In x (sig_f gamma))
  (Hpseq: forall x, In x (sig_p gamma1) <-> In x (sig_p gamma))
  :
  valid_context (rev (fst (decls_of_def which b l)) ++ gamma1).
Proof.
  pose proof (funsyms_rec_sublist_strong which b l) as Hfuns.
  assert (Hfuns1: forall x, In x (concat
    (map funsyms_of_def
    (rev (fst (decls_of_def which b l))))) ->
      In x (funsyms_of_rec l)).
  {
    apply sublist_strong_in in Hfuns. intros x Hinx.
    rewrite In_rev. apply Hfuns; auto.
  }
  pose proof (predsyms_rec_sublist_strong which b l) as Hpreds.
  assert (Hpreds1: forall x, In x (concat
    (map predsyms_of_def
    (rev (fst (decls_of_def which b l))))) ->
      In x (predsyms_of_rec l)).
  {
    apply sublist_strong_in in Hpreds. intros x Hinx.
    rewrite In_rev. apply Hpreds; auto.
  }
  pose proof (typesyms_rec_nil which b l) as Htys.
  apply valid_ctx_abstract_app; auto.
  try rewrite get_recfun_defs_typesyms;
  try rewrite get_recfun_defs_funsyms;
  try rewrite get_recfun_defs_predsyms; auto.
  - apply Forall_rev. simpl.
    rewrite Forall_forall. intros x.
    rewrite in_filter_map_iff. intros [y [Hiny Hx]].
    destruct (gen_funpred_def_match y) as [b1 [[ls vs] e]] eqn : Hdef.
    apply gen_funpred_def_match_eq in Hdef. subst.
    destruct (which b1 ls); inversion Hx; subst; simpl; auto.
    apply gen_abs_concrete.
  - (*Prove funsym well-formed according to this new context*) 
    rewrite Forall_forall in Hwf1 |- *.
    intros x Hinx. apply Hfuns1 in Hinx.
    apply wf_funsym_sublist with (g1:=(recursive_def l) :: gamma); auto.
    intros ts. simpl. apply Htseq.
  - (*Same for predsym*)
    rewrite Forall_forall in Hwf2 |- *.
    intros x Hinx. apply Hpreds1 in Hinx.
    apply wf_predsym_sublist with (g1:=(recursive_def l) :: gamma); auto.
    intros ts. simpl. apply Htseq.
  - (*Typesyms in signature*)
    rewrite Htys. constructor.
  - (*Prove funsyms not in signature*) rewrite Forall_forall in Hnotsig1 |- *. (*need H2*)
    intros x Hinx. apply Hfuns1 in Hinx.
    intros Hinx1. apply Hfseq in Hinx1.
    apply (Hnotsig1 x); auto.
  - (*Same for predsyms*) rewrite Forall_forall in Hnotsig2 |- *. (*need H3*)
    intros x Hinx. apply Hpreds1 in Hinx.
    intros Hinx1. apply Hpseq in Hinx1.
    apply (Hnotsig2 x); auto.
  - (*Nodups in added symbols*)
    rewrite Htys; auto; constructor.
  - (*NoDups in added funsyms*)
    apply (sublist_strong_nodup _ _ _ Hfuns). apply NoDup_rev. auto.
  - (*NoDups in added presyms*)
    apply (sublist_strong_nodup _ _ _ Hpreds). apply NoDup_rev. auto.
Qed.

(*See*)
Print valid_context.
Lemma valid_ctx_concrete_def {gamma} (d: def):
  (*d introduces no new typesyms*)
  typesyms_of_def d = nil ->
  Forall (wf_funsym gamma) (funsyms_of_def d) ->
  Forall (wf_predsym gamma) (predsyms_of_def d) ->
  (* Forall (fun t => ~ In t (sig_t gamma)) (concat (map typesyms_of_def l)) -> *)
  Forall (fun f => ~ In f (sig_f gamma)) (funsyms_of_def d) ->
  Forall (fun p => ~ In p (sig_p gamma)) (predsyms_of_def d) ->
  (* NoDup (concat (map typesyms_of_def l)) -> *)
  NoDup (funsyms_of_def d) ->
  NoDup (predsyms_of_def d) ->
  nonempty_def d ->
  valid_def (d :: gamma) d ->
  valid_context gamma ->
  valid_context (d :: gamma).
Proof.
  intros Htys Hwf1 Hwf2 Hsig1 Hsig2 Hn1 Hn2 Hne Hval gamma_valid.
  constructor; auto.
  - revert Hwf1. rewrite !Forall_forall; intros Hwf1 x Hinx.
    apply wf_funsym_expand; auto.
  - revert Hwf2. rewrite !Forall_forall; intros Hwf2 x Hinx.
    apply wf_predsym_expand; auto.
  - rewrite Htys. constructor.
  - rewrite Htys; constructor.
Qed.

Definition funpred_def_eq_dec (f1 f2: funpred_def) : {f1 = f2} + {f1 <> f2} :=
   (reflect_dec' (funpred_def_eqb_spec f1 f2)).

(*Sometimes it is easier to first match on l2*)
(* Lemma sublist_strong_rewrite {A: Type} eq_dec (l1 l2: list A):
  sublist_strong eq_dec l1 l2 =
  match l2 with
  | nil =>
    match l1 with
    | nil => true
    | _ => false
    end
  | x2 :: t2 =>
    match l1 with
    | nil => true
    | x1 :: t1 => (eq_dec x1 x2 && sublist_strong eq_dec t1 t2) || sublist_strong eq_dec l1 t2
    end
  end.
Proof.
  destruct l1; destruct l2; auto.
Qed. *)

Lemma sublist_strong_omap {A B: Type} (f: A -> option B) eq_dec1 eq_dec2 (l1 l2: list A):
  sublist_strong eq_dec1 l1 l2 ->
  sublist_strong eq_dec2 (omap f l1) (omap f l2).
Proof.
  revert l1. induction l2 as [| h2 t2 IH]; intros [| h1 t1]; simpl; auto.
  - intros _. apply sublist_strong_nil.
  - intros Hsub. apply orb_true_iff in Hsub. destruct Hsub as [Hsub | Hsub].
    + apply andb_true_iff in Hsub. destruct Hsub as [Heq Hsub].
      destruct (eq_dec1 h1 h2); subst; [|discriminate].
      apply IH in Hsub. destruct (f h2); simpl; auto.
      destruct (eq_dec2 b b); auto. rewrite Hsub; auto.
    + apply IH in Hsub. simpl in Hsub.
      destruct (f h2); auto.
      simpl. destruct (match f h1 with
        | Some y => y :: omap f t1
        | None => omap f t1
        end) eqn : Hmatch; auto.
      apply orb_true_iff. right; auto.
Qed.
(* 
Lemma sublist_strong_funsyms_of_rec l1 l2:
  sublist_strong funpred_def_eq_dec l1 l2 ->
  sublist_strong funsym_eq_dec (funsyms_of_rec l1) (funsyms_of_rec l2).
Proof.
  apply sublist_strong_omap.
Qed.



  unfold funsyms_of_rec. revert l1. induction l2 as [|h2 t2 IH]; intros [| h1 t1]; simpl; auto.
  - intros _. destruct h2; auto.
    apply sublist_strong_nil.
  - unfold is_true at 1. rewrite orb_true_iff, andb_true_iff. intros [[Heq Hsub]| Hsub].
    + destruct (funpred_def_eq_dec h1 h2); subst; [|discriminate].
      destruct h2; simpl; [|apply IH; auto].
      destruct (funsym_eq_dec f f); auto. rewrite IH; auto.
    + apply IH in Hsub. simpl in Hsub. destruct h2; auto.
      simpl.  destruct  apply IH. 
  
   simpl. *)

Lemma split_funpred_defs_partition_length l:
  length (fst (split_funpred_defs l)) =
  length (fst (partition (fun x => match x with | fun_def _ _ _  => true | _ => false end) l)) /\
  length (snd (split_funpred_defs l)) =
  length (snd (partition (fun x => match x with | fun_def _ _ _  => true | _ => false end) l))
  .
Proof.
  induction l as [|h t [IH1 IH2]]; simpl; auto; split; auto;
  rewrite (surjective_pairing (partition _ _)); simpl; destruct h; simpl; auto.
Qed.



(*Get the indices in the list corresponding to the sublist.
  TODO: need to prove sorted?*)
Lemma sublist_strong_indices {A: Type} eq_dec (d: A) (l1 l2: list A):
  sublist_strong eq_dec l1 l2 ->
  exists idxs, length idxs = length l1 /\
  Forall (fun i => i < length l2) idxs /\
  l1 = map (fun i => nth i l2 d) idxs.
Proof.
  revert l1. induction l2 as [| h2 t2 IH].
  - intros l1 Hsub. destruct l1; inversion Hsub. exists nil. auto.
  - simpl. intros [| h1 t1]; simpl.
    + intros _. exists nil. auto.
    + intros Hsub. apply orb_true_iff in Hsub.
      destruct Hsub as [Hsub | Hsub].
      * apply andb_true_iff in Hsub. destruct Hsub as [Heq Hsub].
        destruct (eq_dec h1 h2); subst; [|discriminate].
        apply IH in Hsub.
        destruct Hsub as [idxs [Hlen [Hall Ht1]]].
        exists (0 :: (map S idxs)).
        simpl. rewrite map_length, map_map, <- Ht1. split_all; auto.
        constructor; auto. lia. rewrite Forall_map. revert Hall. apply Forall_impl; intros; lia.
      * apply IH in Hsub.
        destruct Hsub as [idxs [Hlen [Hall Hht]]].
        exists (map S idxs). rewrite map_length, map_map, Forall_map. split_all; auto.
        revert Hall. apply Forall_impl; intros; lia.
Qed.

(*Prove that the new context is valid*)
Lemma gen_new_ctx_valid which nonrec gamma:
  valid_context gamma ->
  valid_context (gen_new_ctx_gamma' which nonrec gamma).
Proof.
  intros.
  induction H; simpl; try solve[constructor].
  assert (Hval2: valid_context (d :: gamma)) by (constructor; auto).
  unfold gen_new_ctx_gamma' in *. simpl.
  assert (Heqctx:=gen_new_ctx_gamma_eq_sig which nonrec gamma).
  unfold eq_sig in Heqctx. destruct Heqctx as [Htseq [Hfseq Hpseq]].
  destruct (is_rec_nonrec d) as [l| l] eqn : Hrec.
  - destruct d; inversion Hrec; subst. simpl in *.
    (*Annoying, we add both concrete and abstract symbols, so we cannot directly
      use [valid_ctx_abstract_app]*)
    unfold decl_list_of_def. rewrite rev_app_distr.
    rewrite rewrite_concrete_recs.
    (*2 parts: first, prove abstract is well-formed*)
    rewrite <- app_assoc.
    unfold gen_new_ctx_gamma' in Htseq, Hfseq, Hpseq.
    match goal with |- valid_context (?x ++ ?l ++ ?z) =>
      set (gamma1:=z) in *;
      assert (Hval3: valid_context (l ++ gamma1))
    end.
    {
      eapply add_rec_abs_valid; auto. all: auto.
    }
    destruct (Pattern.filter_map _ l) as [|h t] eqn : Hpat; [simpl; auto|].
    (*Prove that funsyms are [sublist_strong] of funsyms of l*)
    set (l1:=h :: t) in *.
    assert (Hsublist: sublist_strong funpred_def_eq_dec l1 l).
    {
      rewrite <- Hpat. clear. (*separate lemma?*)
      induction l as [| h t IH]; simpl; auto.
      destruct (gen_funpred_def_match h) as [b1 [[ls vs] e]] eqn : Hdef.
      apply gen_funpred_def_match_eq in Hdef. subst.
      destruct (which b1 ls) eqn : Hwhich.
      - simpl. (*destruct b1; simpl in *; auto.*)
        destruct (Pattern.filter_map _ _) eqn : Hpat; [simpl; auto|].
        apply orb_true_iff. right. auto.
      - simpl.
        destruct (funpred_def_eq_dec _ _); simpl; [| auto].
        rewrite IH; auto.
    }
    assert (Hfuns: sublist_strong funsym_eq_dec (funsyms_of_rec l1) (funsyms_of_rec l)).
    { eapply sublist_strong_omap; eauto. }
    assert (Hpreds: sublist_strong predsym_eq_dec (predsyms_of_rec l1) (predsyms_of_rec l)).
    { eapply sublist_strong_omap; eauto. }
    (*We also need to know that no funsym in these funsyms are in the abstract symbols*)
    assert (Hdisj1: (*TODO: does it need to be both?*)  disj (funsyms_of_rec l1)
      (concat (map funsyms_of_def (rev (fst (decls_of_def which false l)))))).
    {
      rewrite <- Hpat. simpl. unfold funsyms_of_rec. intros x [Hinx1 Hinx2].
      revert Hinx1 Hinx2.
      rewrite in_omap_iff, in_concat.
      setoid_rewrite in_filter_map_iff.
      setoid_rewrite in_map_iff.
      setoid_rewrite <- In_rev.
      setoid_rewrite in_filter_map_iff.
      intros [fd1 [[fd2 [Hinfd Hfd]] Hx]].
      intros [fs [[d [Hfs [fd3 [Hinfd3 Hd]]]] Hinx2]];
      destruct fd1; inversion Hx; subst.
      destruct (gen_funpred_def_match fd2) as [b1 [[ls1 vs1] e1]] eqn : Hdef1.
      destruct (gen_funpred_def_match fd3) as [b2 [[ls2 vs2] e2]] eqn : Hdef2.
      apply gen_funpred_def_match_eq in Hdef1, Hdef2. subst.
      destruct (which b1 ls1) eqn : Hwhich1; inversion Hfd.
      destruct (which b2 ls2) eqn : Hwhich2; inversion Hd; subst.
      destruct b2; simpl in Hinx2; [|contradiction].
      destruct Hinx2 as [Hxeq | []]; subst.
      destruct b1; inversion H11; subst.
      rewrite Hwhich1 in Hwhich2. discriminate.
    }
    (*Almost exactly the same, not great*)
    assert (Hdisj2: (*TODO: does it need to be both?*)  disj (predsyms_of_rec l1)
      (concat (map predsyms_of_def (rev (fst (decls_of_def which false l)))))).
    {
      rewrite <- Hpat. simpl. unfold predsyms_of_rec. intros x [Hinx1 Hinx2].
      revert Hinx1 Hinx2.
      rewrite in_omap_iff, in_concat.
      setoid_rewrite in_filter_map_iff.
      setoid_rewrite in_map_iff.
      setoid_rewrite <- In_rev.
      setoid_rewrite in_filter_map_iff.
      intros [fd1 [[fd2 [Hinfd Hfd]] Hx]].
      intros [fs [[d [Hfs [fd3 [Hinfd3 Hd]]]] Hinx2]];
      destruct fd1; inversion Hx; subst.
      destruct (gen_funpred_def_match fd2) as [b1 [[ls1 vs1] e1]] eqn : Hdef1.
      destruct (gen_funpred_def_match fd3) as [b2 [[ls2 vs2] e2]] eqn : Hdef2.
      apply gen_funpred_def_match_eq in Hdef1, Hdef2. subst.
      destruct (which b1 ls1) eqn : Hwhich1; inversion Hfd.
      destruct (which b2 ls2) eqn : Hwhich2; inversion Hd; subst.
      destruct b2; simpl in Hinx2; [contradiction|].
      destruct Hinx2 as [Hxeq | []]; subst.
      destruct b1; inversion H11; subst.
      rewrite Hwhich1 in Hwhich2. discriminate.
    }
    (* clear Hpat. *)
    simpl rev at 1. 
    assert (Hsigt: sublist (sig_t (recursive_def l :: gamma))
      (sig_t
      (rev (fst (decls_of_def which false l)) ++ gamma1))).
    {
      unfold sig_t. 
      rewrite map_app, concat_app.
      rewrite typesyms_rec_nil. simpl.
      intros ts Hints.
      apply Htseq; auto.
    }
    (*Second part: prove that adding the recursive definition is OK (TODO: separate lemma)*)
    (*I think prove the [sublist_strong] again*)
    apply valid_ctx_concrete_def; auto.
    + (*wf_funsym*) revert H0. 
      rewrite !Forall_forall. intros Hwf1 x Hinx.
      apply sublist_strong_in in Hfuns.
      apply Hfuns in Hinx.
      eapply wf_funsym_sublist.
      2: apply (Hwf1 x Hinx).
      apply Hsigt.
    + (*wf_predsym*)
      revert H1. rewrite !Forall_forall. intros Hwf2 x Hinx.
      apply sublist_strong_in in Hpreds.
      apply Hpreds in Hinx.
      eapply wf_predsym_sublist. 2: apply (Hwf2 x Hinx).
      apply Hsigt.
    + (*disjoint of funsyms*)
      revert H2. rewrite !Forall_forall.
      intros Hsig1 x Hinx1.
      unfold sig_f. rewrite map_app, concat_app, in_app_iff.
      intros [Hinx2 | Hinx2].
      * apply (Hdisj1 x); auto.
      * apply (Hsig1 x); auto.
        -- apply sublist_strong_in in Hfuns. auto.
        -- apply Hfseq; auto.
    + (*disjointness of predsyms*)
      revert H3. rewrite !Forall_forall.
      intros Hsig2 x Hinx1.
      unfold sig_p. rewrite map_app, concat_app, in_app_iff.
      intros [Hinx2 | Hinx2].
      * apply (Hdisj2 x); auto.
      * apply (Hsig2 x); auto.
        -- apply sublist_strong_in in Hpreds. auto.
        -- apply Hpseq; auto.
    + (*Nodup of funsyms*)
      apply (sublist_strong_nodup _ _ _ Hfuns); auto.
    + (*predsyms*) apply (sublist_strong_nodup _ _ _ Hpreds); auto.
    + (*The more interesting part - prove that the definition is valid*)
      revert H9.
      assert (forall l1 l2 gamma1 gamma2,
        (* (forall x, In x (sig_f gamma1) <-> In x (sig_f gamma2)) ->
        (forall x, In x (sig_t gamma1) <-> In x (sig_t gamma2)) ->
        (forall x, In x (sig_p gamma1) <-> In x (sig_p gamma2)) -> *)
        sublist_sig gamma2 gamma1 ->
        sublist (mut_of_context gamma2) (mut_of_context gamma1) ->
        sublist_strong funpred_def_eq_dec l1 l2 ->
        l1 <> nil ->
        funpred_valid gamma2 l2 ->
        funpred_valid gamma1 l1).
      { 
        (*TODO: separate lemma*)
        clear.
        intros l1 l2 gamma1 gamma2 Hsig Hmut Hsub Hnotnil. (*Hfs Hts Hps Hmut Hsub.*)
        unfold funpred_valid.
        intros [Hallval Hterm].
        split.
        - revert Hallval.
          rewrite !Forall_forall; intros Hallval x Hinx.
          assert (Hinx1: In x l2) by (apply (sublist_strong_in _ _ _ Hsub); auto).
          specialize (Hallval _ Hinx1).
          unfold funpred_def_valid_type in *.
          destruct x; destruct Hallval as [Hty [Hsubfv [Hsubty [Hn Hmap]]]]; split_all; auto.
          + (*Prove typing*)
            revert Hty. apply term_has_type_sublist; auto.
          + revert Hty. apply formula_typed_sublist; auto.
        - (*Interesting - termination*)
          revert Hterm.
          unfold funpred_def_term_exists.
          intros [m [params [vs [is Hterm]]]].
          exists m. exists params. exists vs.
          unfold funpred_def_term in Hterm.
          destruct Hterm as [Hl2 [Hlenvs [Hm_in [Hlenis [His [Hftys [Hptys [Hfparams [Hpparams [Hdecfun Hdecpred]]]]]]]]]].
          (*Difficulty: we know that l1 is a sublist of l2. We have to build up the appropriate list.
            We did this in the previous lemma (sublist_strong_indices)*)
          destruct (sublist_strong_indices _ fd_d _ _ Hsub) as [idxs [Hlen2 [Hallidx Hl1]]].
          set (is2 := map (fun i => nth i is 0) idxs).
          (*And a result we need from this*)
          assert (Hij: forall i, i < length l1 ->
            exists j, j < length l2 /\
            nth i l1 fd_d = nth j l2 fd_d /\
            nth i is2 0 = nth j is 0 (*/\
            (i < length (fst (split_funpred_defs l1)) <->
             j < length (fst (split_funpred_defs l2)))*)).
          {
            intros i Hi. exists (nth i idxs 0).
            (*Prove first 3 separately*)
            assert (Hnthi: nth i idxs 0 < Datatypes.length l2). {
              rewrite Forall_forall in Hallidx; apply Hallidx; apply nth_In; lia.
            }
            assert (Hnthl12: nth i l1 fd_d = nth (nth i idxs 0) l2 fd_d). {
              rewrite Hl1. rewrite map_nth_inbound with (d2:=0); auto. lia.
            }
            assert (Hnthis12: nth i is2 0 = nth (nth i idxs 0) is 0). {
              unfold is2. rewrite map_nth_inbound with (d2:=0); auto. lia.
            }
            split_all; auto.
            (* split; intros Hfstsplit.
            - 
            
             Print split_funpred_defs.
            
             Print funpred_defs_to_sns. assert (Hinfs: In (nth i idxs 0) (fst ( l1))).


            funpred_defs_to_sns_in_fst:
  forall (l : list funpred_def) (is : list nat) (x : fn),
  Datatypes.length l = Datatypes.length is ->
  In x (fst (funpred_defs_to_sns l is)) <->
  (exists i : nat,
     i < Datatypes.length (fst (split_funpred_defs l)) /\
     (let y := nth i (fst (split_funpred_defs l)) (id_fs, [], tm_d) in
      x = fundef_to_fn (fst (fst y)) (snd (fst y)) (snd y) (nth i is 0))) *)
          }
          (*Then indicies are (map (nth i is) idxs)*)
          assert (Hlen3: length is2 = length l1) by (unfold is2; rewrite map_length; auto).
          exists is2.
          unfold funpred_def_term. split_all; auto.
          + eapply mut_in_ctx_sublist; eassumption.
          + (*Prove bound on nth*) intros i Hi.
            rewrite Hlen3 in Hi.
            specialize (Hij i Hi).
            destruct Hij as [j [Hj [Hil1 Hiis2]]].
            rewrite Hiis2.
            specialize (His j (ltac:(lia))).
            revert His.
            pose proof (split_funpred_defs_length l1) as Hsplitlen.
            assert (Hi2: i < length (fst (split_funpred_defs l1)) \/
              length (fst (split_funpred_defs l1)) <= i < length l1) by lia.
            destruct Hi2 as [Hi2 | Hi2].
            * (*TODO: problem! this is the wrong index list!
                We really need the one corresponding to each part of [split_funpred_defs]
                and we can put them together
                So plan is
                1. proce [split_funpred_defs] equivalent to omap of partition
                  (maybe also prove map_filter equivalent to this too)
                2. prove that [sublist_strong] preserved under filter (and hence partition)
                3. combine with previous omap result to show that each side is sublist_strong
                4. use lemma to get 2 lists idx1 and idx2, concat together
                (should be OK because [funpred_defs_to_sns] does indeed split up)*)
              
            
            
             rewrite
            (*TODO: going to have to prove something about[split_funpred_defs]*)
            rewrite !app_nth1.
            
            * rewrite !app_nth1; [| rewrite map_length; lia ].
            Search split_funpred_defs.
              rewrite map_nth_inbound with (d2:=(id_fs, nil, tm_d)); 
            2: rewrite map_length.
            Search split_funpred_defs.

            split_funpred_defs_length:
  forall l : list funpred_def,
  Datatypes.length (fst (split_funpred_defs l)) +
  Datatypes.length (snd (split_funpred_defs l)) = 
  Datatypes.length l
            rewrite <- map_nth.
            rewrite app_nth1.
            rewrite map_nth_inbound.
          
          
           Search mut_in_ctx mut_of_context.
          simpl.
          (*Could say: if we have [sublist_strong], we can find a list of indices such that
            l1 = map (fun i => nth i l2 d) (idxs)
            and do the same for 
            *)
          
          spe
               split; auto.
              split_all; auto.
            intros [| h1 t1]; simpl.
          }
          assert (exists is': length is' = length l1)
          eexists.
          unfold funpred_def_term.

          (*What we want:
            must be the case that for all i, exists j,
              nth i l1 = nth j l2 /\
              nth i is' = nth j is *)

          



            (*TODO: this is what we need, not full iff*) unfold sublist_sig. 
            split_all; intros y Hiny; [apply Hts | apply Hfs | apply Hps]; auto.
            *  
              
               [apply Hfs ] 

        
        admit. }
      apply H9; auto.
      * intros x. pose proof (get_recfun_defs_funsyms which false l x) as Hfunseq.
        unfold sig_f.
        simpl concat at 2.
        rewrite in_app_iff, <- Hfunseq.
        simpl.
        rewrite map_app, concat_app, app_assoc. rewrite in_app_iff.
        apply or_iff; auto.
        unfold decl_list_of_def. rewrite !in_app_iff.
        rewrite rev_app_distr, map_app, concat_app.
        rewrite in_app_iff. apply or_iff; [|reflexivity].
        simpl. rewrite Hpat. unfold l1.
        destruct h; simpl; destruct t; simpl; try rewrite app_nil_r; reflexivity.
      * (*TODO: should be easier way to prove these*)
        intros x. pose proof (get_recfun_defs_typesyms which false l) as Htyseq.
        unfold decl_list_of_def in Htyseq.
        unfold sig_t. Opaque decls_of_def. simpl. Transparent decls_of_def. 
        rewrite map_app, concat_app.
        rewrite rev_app_distr, map_app, concat_app in Htyseq.
        apply app_eq_nil in Htyseq.
        destruct Htyseq as [_ Htyseq]; rewrite Htyseq. simpl; auto.
      * (*predsyms*)
        intros x. pose proof (get_recfun_defs_predsyms which false l x) as Hpredseq.
        unfold sig_p.
        simpl concat at 2.
        rewrite in_app_iff, <- Hpredseq.
        simpl.
        rewrite map_app, concat_app, app_assoc. rewrite in_app_iff.
        apply or_iff; auto.
        unfold decl_list_of_def. rewrite !in_app_iff.
        rewrite rev_app_distr, map_app, concat_app.
        rewrite in_app_iff. apply or_iff; [|reflexivity].
        simpl. rewrite Hpat. unfold l1.
        destruct h; simpl; destruct t; simpl; try rewrite app_nil_r; reflexivity. 
  - 
      *

        Search app nil.
        rewrite concat_app in Htyseq.
        simpl concat at 2.
        simpl. rewrite map_app, concat_app.
        unfold decl_list_of_def in Htyseq.
         simpl in Htyseq.
        rewrite in_app_iff.
        rewrite in_app_iff, <- Hfunseq.
        (* rewrite <- Hpat. *)
        simpl.
        rewrite map_app, concat_app, app_assoc. rewrite in_app_iff.
        apply or_iff; auto.
        unfold decl_list_of_def. rewrite !in_app_iff.
        rewrite rev_app_distr, map_app, concat_app.
        rewrite in_app_iff. apply or_iff; [|reflexivity].
        simpl. rewrite Hpat. unfold l1.
        destruct h; simpl; destruct t; simpl; try rewrite app_nil_r; reflexivity.

        
        
         destruct (Pattern.filter_map _ _) eqn : Hpat.
        Print decls_of_def.
        simpl.
        rewrite concat_app.
        rewrite map_app.
        rewrite comcat_app.
        apply or_iff; auto.
        Search (?P \/ ?Q <-> ?R \/ ?S).
        apply iff_congr.
        apply iff_compat.
        
         rewrite concat_app.
        unfold map.
        simpl.

        In x
  (concat
  (map funsyms_of_def
  (recursive_def l1 :: rev
  (fst
  (decls_of_def which false l)) ++
gamma1)))
        rewrite map_app.
        rewrite concat_app.
        simpl.
        revert Hfunseq.
        unfold sig_f.
        unfold decl_list_of_dec
         unfold decl_list_of_def in H10.
        rewrite in_app_iff in H10.
        simpl in H10. 
      
      
      
       Print decl_list_of_def. intros f. unfold sig_f. simpl.

      get_recfun_defs_funsyms

      unfold valid_def, funpred_valid.
      intros [Hallval Hterm].
      split.
      * revert Hallval. rewrite !Forall_forall. intros Hallval fd Hinfd.
      Print funsyms_of_rec.
        
        revert H9. unfold funpred_valid; intros [] funpred_def_valid_type.
      Print funpred_valid.
      simpl.
      simpl.

    
    
      apply Htseq in Hinx2.  apply Hinx1.
      
      
       apply Hdisj1 in Hinx1. apply sublist_strong_in in Hfuns.
        apply Hfuns in Hinx1.


        funsyms_rec_sublist_strong:
  forall (which : forall b : bool, gen_sym b -> bool) 
    (b : bool) (l : list funpred_def),
  sublist_strong funsym_eq_dec
    (concat (map funsyms_of_def (rev (fst (decls_of_def which b l)))))
    (rev (funsyms_of_rec l))
        
      Search decls_of_def funsyms_of_def.
      rewrite concat_app.
      Search decls_of_def fst.


      typesyms_rec_nil:
  forall (which : forall b : bool, gen_sym b -> bool) 
    (b : bool) (l : list funpred_def),
  concat (map typesyms_of_def (rev (fst (decls_of_def which b l)))) = []
      simpl.
      fold gamma1 in Htseq.
      rewrite Htseq.
      (*TODO*)
       auto.
      simpl.
    
    remember (h :: t) as l1 eqn : Hl1. clear Hl1.
    simpl. set (l1:=h :: t) in *. 
      simpl funsyms_of_def.
    
     unfold funsyms_of_def. simpl. Opaque cons.  simpl.
      (*TODO: move*)
     
    
    
     rewrite !Forall_forall. Search wf_funsym.
    
    constructor; auto.
    + simpl. 
      (*START*)
    
    constructor.
    
     simpl app at 1. 
    simpl.
    { simpl; auto. }
    simpl.
    apply valid_ctx_abstract_app;
    try rewrite get_recfun_defs_typesyms;
    try rewrite get_recfun_defs_funsyms;
    try rewrite get_recfun_defs_predsyms; auto.
    + (*Prove not concrete def*)
      rewrite Forall_forall. intros d.
      rewrite <- In_rev. unfold decl_list_of_def.
      rewrite in_app_iff. intros [Hind | Hind].
      * simpl in Hind. apply in_filter_map_iff in Hind.
        destruct Hind as [y [Hiny Hd]].
        destruct (gen_funpred_def_match _) as [b1 [[ls1 vs1] e1]] eqn : Hdef.
        destruct (which b1 ls1); inversion Hd; subst; auto.
        apply gen_abs_not_concrete.
      * destruct ()
        apply gen_funpred_def_match_eq in Hdef; subst; simpl in *.

  
   Check valid_ctx_abstract_app.
  destruct (is_ind d) eqn : Hind.
  - destruct d; inversion Hind; subst.
    simpl in *.
    (*Now we must simplify the wf_predsym/funsym context *)
    assert (Hallwfp: Forall (wf_predsym gamma) (predsyms_of_indprop l)).
    {
      revert H1. apply Forall_impl. intros a.
      apply wf_predsym_sublist; intros.
      unfold sublist. intros x Hinx. apply Hinx.
    } 
    apply valid_ctx_abstract_app;
    try rewrite get_indpred_defs_typesyms;
    try rewrite get_indpred_defs_funsyms;
    try rewrite get_indpred_defs_predsyms;
    auto.
    + rewrite Forall_forall. intros d.
      unfold get_indpred_defs.
      rewrite in_map_iff. intros [[p fs] [Hd Hinx]]; simpl in *; subst.
      reflexivity.
    + revert Hallwfp. apply Forall_impl.
      intros a. apply wf_predsym_sublist.
      intros x. apply Htseq.
    + rewrite Forall_forall; intros p Hinp.
      rewrite Hpseq.
      rewrite Forall_forall in H3; auto.
  - (*No change in context*)
    pose proof (gen_new_ctx_gamma_eq_sig (d :: gamma)) as Heq2.
    unfold gen_new_ctx_gamma in Heq2.
    simpl in Heq2. rewrite Hind in Heq2.
    simpl in *. assert (Heq3:=Heq2). unfold eq_sig in Heq2. 
    destruct Heq2 as [Htseq2 [Hfseq2 Hpseq2]].
    simpl. constructor; auto.
    + revert H0. apply Forall_impl. intros a.
      apply wf_funsym_sublist. 
      apply eq_sig_is_sublist, eq_sig_sym; auto.
    + revert H1. apply Forall_impl. intros a.
      apply wf_predsym_sublist.
      apply eq_sig_is_sublist, eq_sig_sym; auto.
    + rewrite Forall_forall. intros x Hinx.
      rewrite Hfseq.
      rewrite Forall_forall in H2; apply (H2 x); auto.
    + rewrite Forall_forall. intros x Hinx.
      rewrite Hpseq.
      rewrite Forall_forall in H3; apply (H3 x); auto.
    + rewrite Forall_forall. intros x Hinx.
      rewrite Htseq.
      rewrite Forall_forall in H4; apply (H4 x); auto.
    + (*The difficult part: proving that def is still valid*)
      revert H9.
      apply valid_def_sublist.
      * apply eq_sig_is_sublist, eq_sig_sym; auto.
      * pose proof (gen_new_ctx_gamma_sig_t (d :: gamma)).
        unfold gen_new_ctx_gamma in H9.
        simpl in H9. rewrite Hind in H9. auto.
      * pose proof (gen_new_ctx_gamma_mut (d :: gamma)).
        unfold gen_new_ctx_gamma in H9.
        simpl in H9. rewrite Hind in H9. auto.
Qed.

Lemma gen_new_ctx_sound which nonrec: sound_trans (single_trans (gen_new_ctx which nonrec)).
Proof.
  (*rewrite gen_new_ctx_rewrite.*) unfold sound_trans, single_trans.
  intros.
  simpl in H.
  specialize (H _ ltac:(left; auto)).
  unfold task_valid in *. simpl in *.
  split; auto.
  destruct t as [[gamma delta] goal]; simpl_task.
  destruct H as [Hwf Hval].
  intros.
  specialize (Hval (gen_new_ctx_valid _ gamma_valid) Hwf).
  unfold log_conseq in *.
  intros.
  (*Now, need to show that we can convert an interpretation
    for the full context into one of the weakened context*)
  specialize (Hval pd (gen_new_ctx_pf gamma_valid pd pf)
    (gen_new_ctx_pf_full gamma_valid pd pf pf_full)).
  prove_hyp Hval.
  {
    intros d Hd.
    erewrite satisfies_gen_new_ctx_pf. apply H.
    Unshelve. auto.
  }
  erewrite satisfies_gen_new_ctx_pf in Hval.
  apply Hval.
Qed.


(*Prove soundness*)
Theorem eliminate_definition_gen_sound which nonrec:
  sound_trans (eliminate_definition_gen which nonrec).
Proof.
  (*First, split into two parts*)
  rewrite sound_trans_ext.
  2: apply eliminate_definition_split.
  unfold eliminate_definition_alt.
  (*Prove sound by composition*)
  apply compose_single_trans_sound.
  (*TODO*)
  - (*The harder part*) apply gen_axioms_sound.
  - (*The easier part*) apply gen_new_ctx_sound.
  - (*All axioms are well-formed*) apply gen_axioms_wf.
Qed. 
