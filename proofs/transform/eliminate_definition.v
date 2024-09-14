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

Definition gen_new_ctx which (nonrec : bool) (t: task) : task :=
  let new_g :=
  concat (map (fun x =>
    match x with
    | recursive_def l => rev (decl_list_of_def which false l)
    | nonrec_def l => if nonrec then rev (decl_list_of_def which true [l]) else [x]
    | _ => [x]
    end) (task_gamma t)) in
  mk_task new_g (task_delta t) (task_goal t).

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
