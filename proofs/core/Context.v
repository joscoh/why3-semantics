(*Here we define a context (list of definitions)
  and provide useful utilities. We define a valid (well-typed)
  context in Typing.v*)
Require Export Syntax.

Definition context := list def.

(*The signature consists of all type symbols, function symbols,
  and predicate symbols given in a context *)
Definition sig_t (ctx: context) : list typesym :=
  concat (map typesyms_of_def ctx).

(*The funsyms in the signature are those from ADT constructors,
  recursive function definitions, and abstract definitions*)
Definition sig_f (ctx: context) : list funsym :=
  concat (map funsyms_of_def ctx).

(*Predsyms are similar, but include indprops instead of
  ADT constructors*)
Definition sig_p (ctx: context) : list predsym :=
  concat (map predsyms_of_def ctx).

(*Now we give some helpful utilities for the defined
  funsyms, predsyms, and bodies*)

Definition mut_of_context (c: context) : list mut_adt :=
  omap (fun d =>
    match d with
    | datatype_def m => Some m
    | _ => None
    end) c.

Definition mutfuns_of_context (c: context) : list (list funpred_def) :=
  fold_right (fun o acc =>
    match o with
    | recursive_def lf => lf :: acc
    | _ => acc
    end) nil c.

Definition indpreds_of_context (c: context) : 
list (list (predsym * list formula)) :=
omap (fun d =>
  match d with
  |inductive_def il => 
    Some (map (fun x => 
      match x with
      | ind_def p fs => (p, map snd fs)
      end) il)
  | _ => None
  end) c. 

Definition nonrec_of_context gamma : list funpred_def :=
  fold_right (fun o acc =>
    match o with
    | nonrec_def f => f :: acc
    | _ => acc
    end) nil gamma.

(*The concrete list of typesyms, funsyms, and predsyms*)
Definition typesyms_of_context (c: context) : list typesym :=
  concat (map typesyms_of_mut (mut_of_context c)).

Definition funsyms_of_context (c: context) : list funsym :=
  concat (map def_concrete_funsyms c). 

Definition predsyms_of_context (c: context) : list predsym :=
  concat (map def_concrete_predsyms c). 

(*Utilities for dealing with mutual types and context*)
(*We want booleans for proof irrelevance*)
Section MutADTUtil.

Definition mut_in_ctx (m: mut_adt) (gamma: context) :=
  in_bool mut_adt_dec m (mut_of_context gamma).

Lemma mut_in_ctx_eq: forall m gamma,
  mut_in_ctx m gamma <-> In m (mut_of_context gamma).
Proof.
  intros. symmetry. 
  apply (reflect_iff _ _ (in_bool_spec mut_adt_dec m (mut_of_context gamma))).
Qed.

Lemma mut_in_ctx_eq2: forall m gamma,
  mut_in_ctx m gamma <-> In (datatype_def m) gamma.
Proof.
  intros. rewrite mut_in_ctx_eq. symmetry.
  unfold mut_of_context, mut_in_ctx.
  rewrite in_omap_iff.
  split; intros.
  - exists (datatype_def m). auto.
  - destruct H as [d [Hind Hm]].
    destruct d; inversion Hm; subst; auto.
Qed.

Definition mut_typs_in_ctx (l: list alg_datatype) (gamma: context) :=
  exists (vars: list typevar) (H: nodupb typevar_eq_dec vars), 
  In (datatype_def (mk_mut l vars H)) gamma.

(*For recursive functions, it is VERY helpful for this to be
  a (proof irrelevant) boolean*)
Definition adt_in_mut (a: alg_datatype) (m: mut_adt) :=
  in_bool adt_dec a (typs m).

Definition ts_in_mut_list (ts: typesym) (m: list alg_datatype) : bool :=
  in_bool typesym_eq_dec ts (map adt_name m).

Lemma ts_in_mut_list_ex: forall ts m,
  ts_in_mut_list ts (typs m) -> { a | ts = adt_name a /\ 
  adt_in_mut a m}.
Proof.
  unfold adt_in_mut, ts_in_mut_list; intros. induction (typs m); simpl.
  - simpl in H. inversion H.
  - simpl in H.
    destruct (typesym_eq_dec ts (adt_name a)); subst.
    + apply (exist _ a). rewrite eq_dec_refl. split; auto.
    + specialize (IHl H).
      destruct IHl as [a' [Ha' Hina']].
      apply (exist _ a'). rewrite Hina'. subst; simpl_bool; split; auto.
Qed.

Lemma ts_in_mut_list_spec: forall ts m,
  ts_in_mut_list ts (typs m) <-> exists a, ts = adt_name a /\ 
  adt_in_mut a m.
Proof.
  intros. unfold adt_in_mut, ts_in_mut_list. induction (typs m); simpl.
  - split; intros; auto. inversion H. destruct H as [a [H]]; inversion H0.
  - split; intros.
    + destruct (typesym_eq_dec ts (adt_name a)).
      * subst. exists a. rewrite eq_dec_refl. split; auto.
      * apply IHl in H. destruct H as [a' [Ha' Hina']].
        subst. exists a'. rewrite Hina'. simpl_bool. split; auto.
    + destruct H as [a' [Ha' Hina']]; subst.
      destruct (adt_dec a' a); subst; simpl in Hina'.
      * rewrite eq_dec_refl. reflexivity.
      * apply orb_true_iff. right. apply IHl.
        exists a'. split; auto.
Qed.

Definition adt_mut_in_ctx (a: alg_datatype) (m: mut_adt) (gamma: context) :=
  adt_in_mut a m /\ mut_in_ctx m gamma.

Definition constr_in_adt (c: funsym) (a: alg_datatype) :=
  in_bool_ne funsym_eq_dec c (adt_constrs a).

Lemma constr_in_adt_eq c a:
  constr_in_adt c a <-> In c (adt_constr_list a).
Proof.
  unfold constr_in_adt.
  rewrite in_bool_ne_equiv.
  rewrite (reflect_iff _ _ (in_bool_spec funsym_eq_dec _ _)).
  reflexivity.
Qed.


(*Now we need utilities for finding the ADT/mutual adt that a
  type belongs to*)

(*For pattern matches (and for typing info), 
  we need to look at an element of type s, 
  determine if s is an ADT type, and if so,
  extract the components (constructor and args). We need
  a lot of machinery to do this; we do this here.*)

Definition find_ts_in_mut (ts: typesym) (m: mut_adt) : option alg_datatype :=
  find (fun a => typesym_eq_dec ts (adt_name a)) (typs m).

Lemma find_ts_in_mut_none: forall ts m,
  find_ts_in_mut ts m = None <->
  forall a, adt_in_mut a m -> adt_name a <> ts.
Proof.
  intros. unfold find_ts_in_mut.
  rewrite find_none_iff.
  split; intros Hall x Hin.
  - intro C; subst.
    apply in_bool_In in Hin.
    specialize (Hall _ Hin). simpl_sumbool. contradiction.
  - apply (In_in_bool adt_dec) in Hin.
    specialize (Hall _ Hin).
    destruct (typesym_eq_dec ts (adt_name x)); auto; subst;
    contradiction.
Qed.

Lemma find_ts_in_mut_some: forall ts m a,
  find_ts_in_mut ts m = Some a ->
  adt_in_mut a m /\ adt_name a = ts.
Proof.
  intros ts m a Hf. apply find_some in Hf.
  destruct Hf as [Hin Heq].
  split; auto. apply In_in_bool; auto.
  simpl_sumbool.
Qed.

Lemma find_ts_in_mut_iff: forall ts m a,
  NoDup (map adt_name (typs m)) ->
  (find_ts_in_mut ts m = Some a) <-> (adt_in_mut a m /\ adt_name a = ts).
Proof.
  intros. eapply iff_trans. apply find_some_nodup.
  - intros. repeat simpl_sumbool.
    apply (NoDup_map_in H); auto.
  - simpl. unfold adt_in_mut. split; intros [Hin Hname];
    repeat simpl_sumbool; split; auto; try simpl_sumbool;
    apply (reflect_iff _ _ (in_bool_spec adt_dec a (typs m))); auto.
Qed.

Definition vty_in_m (m: mut_adt) (vs: list vty) (v: vty) : bool :=
  match v with
  | vty_cons ts vs' => 
    ssrbool.isSome (find_ts_in_mut ts m) &&
    list_eqb vty_eqb vs' vs
  | _ => false
  end.

Definition vty_m_adt (m: mut_adt) (vs: list vty) (v: vty) : option (alg_datatype) :=
  match v with
  | vty_cons ts vs' =>
      if list_eq_dec vty_eq_dec vs' vs then
         find_ts_in_mut ts m
      else None
  | _ => None
  end.

Lemma vty_in_m_spec (m: mut_adt) (vs: list vty) (v: vty):
  reflect 
  (exists a, adt_in_mut a m /\ v = vty_cons (adt_name a) vs)
  (vty_in_m m vs v) .
Proof.
  unfold vty_in_m. destruct v; try solve[apply ReflectF; intros [a [Ha Heq]]; inversion Heq].
  destruct (find_ts_in_mut t m) eqn : Hfind; simpl.
  - apply find_ts_in_mut_some in Hfind.
    destruct Hfind; subst.
    destruct (list_eqb_spec _ vty_eq_spec l vs); subst; simpl.
    + apply ReflectT. exists a. split; auto.
    + apply ReflectF. intros [a' [Ha' Heq]]; inversion Heq; subst;
      contradiction.
  - apply ReflectF. rewrite find_ts_in_mut_none in Hfind.
    intros [a [Ha Heq]]; subst.
    inversion Heq; subst.
    apply (Hfind a Ha); auto.
Qed. 

Definition vsym_in_m (m: mut_adt) (vs: list vty) (x: vsymbol) : bool :=
  vty_in_m m vs (snd x).


(*From a list of vsymbols, keep those which have type vty_cons a ts
  for some a in mut_adt m*)
Definition vsyms_in_m (m: mut_adt) (vs: list vty) (l: list vsymbol) :
  list vsymbol :=
  filter (vsym_in_m m vs) l.

(*A more useful formulation*)
Lemma vsyms_in_m_in (m: mut_adt) (vs: list vty) (l: list vsymbol):
  forall x, In x (vsyms_in_m m vs l) <-> In x l /\ exists a,
    adt_in_mut a m /\ snd x = vty_cons (adt_name a) vs.
Proof.
  intros. unfold vsyms_in_m, vsym_in_m, vty_in_m.
  rewrite in_filter. rewrite and_comm. bool_to_prop.
  destruct x; simpl in *. destruct v; try (solve[split; [intro C; inversion C | 
    intros [a [a_in Hty]]; inversion Hty]]).
  unfold ssrbool.isSome.
  destruct (find_ts_in_mut t m) eqn : Hts; simpl.
  - destruct (list_eqb_spec _ vty_eq_spec l0 vs); subst; simpl; split;
    intros; auto; try tf.
    + exists a. apply find_ts_in_mut_some in Hts. destruct Hts.
      subst. split; auto.
    + destruct H as [a' [Ha' Hty]]. inversion Hty; subst; auto.
  - split; [intro C; inversion C | intros [a [Ha Hty]]].
    rewrite find_ts_in_mut_none in Hts.
    inversion Hty; subst.
    apply Hts in Ha. contradiction.
Qed.

Definition constr_in_m (f: funsym) (m: mut_adt) : bool :=
  existsb (fun a => constr_in_adt f a) (typs m).

End MutADTUtil.

(*Similar defs for recursive functions and inductive predicates*)
Section RecFunUtil.

Definition funsym_in_mutfun (f: funsym) (l: list funpred_def) : bool :=
  in_bool funsym_eq_dec f (funsyms_of_rec l).

Definition get_mutfun_fun (f: funsym) (gamma': context) : option (list funpred_def) :=
  find (funsym_in_mutfun f) (mutfuns_of_context gamma').

Definition predsym_in_mutfun (p: predsym) (l: list funpred_def) : bool :=
  in_bool predsym_eq_dec p (predsyms_of_rec l).

Definition get_mutfun_pred (p: predsym) (gamma': context) : option (list funpred_def) :=
  find (predsym_in_mutfun p) (mutfuns_of_context gamma').

Lemma in_mutfuns gamma (l: list funpred_def) :
  In l (mutfuns_of_context gamma) <->
  In (recursive_def l) gamma.
Proof.
  induction gamma; simpl; auto; try reflexivity.
  destruct a; simpl in *; split; intros; destruct_all;
  try discriminate; try (rewrite IHgamma); auto;
  try (rewrite <- IHgamma); auto.
  inversion H; subst; auto.
Qed.

Lemma in_fun_def l f a b:
  In (fun_def f a b) l ->
  In f (funsyms_of_rec l).
Proof.
  simpl; induction l; simpl; auto; intros.
  destruct H; subst; simpl; auto.
  destruct a0; simpl; try right; auto.
Qed.

Lemma in_pred_def l p a b:
  In (pred_def p a b) l ->
  In p (predsyms_of_rec l).
Proof.
  simpl; induction l; simpl; auto; intros.
  destruct H; subst; simpl; auto.
  destruct a0; simpl; try right; auto.
Qed.

Definition pred_in_indpred (p: predsym) (l: list (predsym * list formula)) :=
  in_bool predsym_eq_dec p (map fst l).

Definition indpred_def_to_indpred (i: indpred_def) : 
  predsym * list formula :=
  match i with
  | ind_def p l => (p, map snd l)
  end.

Definition get_indpred (l: list indpred_def) :
  list (predsym * list formula) :=
  map indpred_def_to_indpred l.

Lemma in_inductive_ctx gamma l: In (inductive_def l) gamma ->
  In (get_indpred l) (indpreds_of_context gamma).
Proof.
  clear.
  intros. induction gamma; simpl in *; auto.
  destruct a; destruct H; try discriminate; auto.
  - inversion H; subst. simpl. left.
    reflexivity.
  - simpl. right. auto.
Qed.

Lemma pred_in_indpred_iff p l:
  pred_in_indpred p (get_indpred l) <->
  In p (predsyms_of_indprop l).
Proof.
  unfold pred_in_indpred.
  induction l; simpl; split; auto; try discriminate; bool_to_prop;
  intros; destruct_all; auto.
  - simpl_sumbool. destruct a; auto.
  - apply IHl in H. auto.
  - destruct a; simpl. left. destruct (predsym_eq_dec p p); auto.
  - right. apply IHl; auto.
Qed.

Lemma in_indpreds_of_context c l:
  In l (indpreds_of_context c) -> 
  exists l2, In (inductive_def l2) c /\
  get_indpred l2 = l.
Proof.
  clear. induction c; simpl; intros.
  destruct H.
  destruct a; try solve[ apply IHc in H; destruct H as [l2 H];
    destruct_all; exists l2; auto].
  simpl in H. destruct H; [| apply IHc in H; destruct_all; exists x; auto].
  subst. exists l0. split; auto.
Qed.

End RecFunUtil.

(*Find a typesym in a context*)
Section FindTS.

Variable gamma: context.

Definition find_ts_in_ctx (ts: typesym) : option (mut_adt * alg_datatype) :=
  fold_right (fun m acc => 
    match (find_ts_in_mut ts m) with
    | Some a => Some (m, a)
    | None => acc
    end) None (mut_of_context gamma).

(*These specs make no assumptions about the context*)
Lemma find_ts_in_ctx_none (ts: typesym):
  reflect (forall (a: alg_datatype) (m: mut_adt),
    mut_in_ctx m gamma -> adt_in_mut a m ->
    adt_name a <> ts) (negb (ssrbool.isSome (find_ts_in_ctx ts))).
Proof.
  unfold find_ts_in_ctx, mut_in_ctx.
  induction (mut_of_context gamma); simpl.
  - apply ReflectT. intros a m H; inversion H.
  - destruct (find_ts_in_mut ts a) eqn : Hinmut; simpl.
    + apply ReflectF. intro C.
      apply find_ts_in_mut_some in Hinmut.
      destruct Hinmut. subst. apply (C a0 a); auto.
      rewrite eq_dec_refl; auto. 
    + rewrite find_ts_in_mut_none in Hinmut. 
      destruct IHl.
      * apply ReflectT. intros.
        destruct (mut_adt_dec m a); simpl in H; subst.
        apply (Hinmut _ H0); auto.
        apply (n _ m); auto.
      * apply ReflectF. intros C.
        apply n. intros a' m Hin. apply C. 
        rewrite Hin, orb_true_r. auto.
Qed.

Lemma find_ts_in_ctx_none_iff (ts: typesym):
  (forall (a: alg_datatype) (m: mut_adt),
    mut_in_ctx m gamma -> adt_in_mut a m ->
    adt_name a <> ts) <-> find_ts_in_ctx ts = None.
Proof.
  rewrite (reflect_iff _ _ (find_ts_in_ctx_none ts)).
  destruct (find_ts_in_ctx ts); simpl; split; intros; auto; discriminate.
Qed.

Lemma find_ts_in_ctx_some (ts: typesym) m a:
  find_ts_in_ctx ts = Some (m, a) ->
  mut_in_ctx m gamma /\ adt_in_mut a m /\
  ts = adt_name a.
Proof.
  unfold find_ts_in_ctx, mut_in_ctx.
  induction (mut_of_context gamma); simpl; auto; intros; try discriminate.
  destruct (find_ts_in_mut ts a0) eqn : Hfind.
  - inversion H; subst.
    apply find_ts_in_mut_some in Hfind. destruct_all.
    rewrite eq_dec_refl; auto.
  - apply IHl in H. destruct_all; subst. split; auto.
    rewrite H, orb_true_r; auto.
Qed.

End FindTS.

(*Lemmas about signature*)
Lemma constr_in_adt_def a m f:
  adt_in_mut a m ->
  constr_in_adt f a ->
  In f (funsyms_of_mut m).
Proof.
  intros a_in c_in.
  unfold funsyms_of_mut.
  rewrite in_concat. exists (adt_constr_list a).
  apply in_bool_In in a_in.
  apply in_bool_ne_In in c_in.
  split; auto. rewrite in_map_iff. exists a; auto.
Qed.

Lemma constr_in_sig_f gamma m a c:
  mut_in_ctx m gamma ->
  adt_in_mut a m ->
  constr_in_adt c a ->
  In c (sig_f gamma).
Proof.
  intros m_in a_in c_in.
  unfold sig_f.
  rewrite in_concat.
  exists (funsyms_of_mut m).
  split.
  - rewrite in_map_iff. exists (datatype_def m); split; auto.
    apply mut_in_ctx_eq2; auto.
  - apply (constr_in_adt_def a m c); auto.
Qed. 

Lemma concat_map_sublist {A B: Type} (f1 f2: A -> list B) l:
  (forall x, In x l -> sublist (f1 x) (f2 x)) ->
  sublist (concat (map f1 l)) (concat (map f2 l)).
Proof.
  unfold sublist; intros Hin x.
  rewrite !in_concat.
  intros [l2 [Hinl2 Hinx]].
  rewrite in_map_iff in Hinl2.
  destruct Hinl2 as [a [Hfa Hina]]; subst.
  apply Hin in Hinx; auto.
  exists (f2 a). split; auto. rewrite in_map_iff.
  eexists; eauto.
Qed.

(*All concrete defs are in the sig*)
Lemma concrete_in_sig gamma:
  Forall (fun t => In t (sig_t gamma)) (typesyms_of_context gamma) /\
  Forall (fun f => In f (sig_f gamma)) (funsyms_of_context gamma) /\
  Forall (fun p => In p (sig_p gamma)) (predsyms_of_context gamma).
Proof.
  split_all.
  - rewrite Forall_forall.
    intros x.
    unfold typesyms_of_context, sig_t,
    typesyms_of_def, mut_of_context.
    rewrite !in_concat; intros [tsl [Hintsl Hinx]].
    rewrite in_map_iff in Hintsl. exists tsl.
    destruct Hintsl as [m [Htsl Hinm]]; subst.
    split; auto.
    rewrite in_omap_iff in Hinm.
    rewrite in_map_iff.
    destruct Hinm as [d [Hind Hd]].
    exists d.
    destruct d; inversion Hd; subst. auto.
  - rewrite Forall_forall.
    intros x.
    apply concat_map_sublist.
    intros. unfold sublist.
    intros. apply concrete_in_def_funsym; auto.
  - rewrite Forall_forall.
    intros x.
    apply concat_map_sublist.
    intros. unfold sublist.
    intros. apply concrete_in_def_predsym; auto.
Qed. 

Lemma ts_in_cases {gamma}
(ts: typesym):
In ts (sig_t gamma) ->
In (abs_type ts) gamma \/
exists m a, mut_in_ctx m gamma /\ adt_in_mut a m /\
  ts = adt_name a.
Proof.
  intros Hts.
  unfold sig_t in Hts.
  rewrite in_concat in Hts.
  destruct Hts as [l [Hinl Hints]].
  rewrite in_map_iff in Hinl.
  destruct Hinl as [d [Hl Hind]]; subst.
  destruct d; simpl in Hints; try solve[inversion Hints].
  - right. exists m. unfold typesyms_of_mut in Hints.
    rewrite in_map_iff in Hints.
    destruct Hints as [a [Hts Hina]]; subst.
    exists a. split_all; auto.
    apply mut_in_ctx_eq2; auto.
    apply In_in_bool; auto.
  - destruct Hints as [Ht | []]; subst. auto.
Qed.

(*Equivalent signatures*)

Definition sublist_sig (g1 g2: context) : Prop :=
  sublist (sig_t g1) (sig_t g2) /\
  sublist (sig_f g1) (sig_f g2) /\
  sublist (sig_p g1) (sig_p g2).

Definition eq_sig (g1 g2: context) : Prop :=
  (forall x, In x (sig_t g1) <-> In x (sig_t g2)) /\
  (forall x, In x (sig_f g1) <-> In x (sig_f g2)) /\
  (forall x, In x (sig_p g1) <-> In x (sig_p g2)).

Lemma eq_sig_refl: forall l, eq_sig l l.
Proof.
  intros. unfold eq_sig; split_all; intros; reflexivity.
Qed.

Lemma eq_sig_cons: forall x l1 l2,
  eq_sig l1 l2 ->
  eq_sig (x :: l1) (x :: l2).
Proof.
  intros. unfold eq_sig in *. split_all; intros;
  unfold sig_t, sig_f, sig_p in *; simpl;
  rewrite !in_app_iff; apply or_iff_compat_l; auto.
Qed.

Lemma eq_sig_sublist g1 g2:
  eq_sig g1 g2 <-> sublist_sig g1 g2 /\ sublist_sig g2 g1.
Proof.
  unfold eq_sig, sublist_sig. split; intros; 
  destruct_all; split_all; unfold sublist in *; intros; auto;
  try (apply H; auto); try (apply H0; auto); try (apply H1; auto);
  split; intros; auto.
Qed.

Lemma eq_sig_is_sublist g1 g2:
  eq_sig g1 g2 ->
  sublist_sig g1 g2.
Proof.
  rewrite eq_sig_sublist; intros [H1 H2]; auto.
Qed.

Lemma eq_sig_sym g1 g2:
  eq_sig g1 g2 ->
  eq_sig g2 g1.
Proof.
  unfold eq_sig. intros; destruct_all; split_all; intros; auto;
  symmetry; auto.
Qed.

(*Idents*)

Definition idents_of_def (d: def) : list string :=
  map (fun (x: funsym) => s_name x) (funsyms_of_def d) ++ 
  map (fun (x: predsym) => s_name x) (predsyms_of_def d) ++ 
  map ts_name (typesyms_of_def d).

Definition idents_of_context (gamma: context) : list string :=
  concat (map idents_of_def gamma).

Lemma idents_of_context_app l1 l2:
  idents_of_context (l1 ++ l2) = idents_of_context l1 ++ idents_of_context l2.
Proof.
  induction l1 as [| h1 t1 IH]; simpl; auto.
  unfold idents_of_context in *; simpl in *.
  rewrite IH, <- app_assoc.
  reflexivity.
Qed. 

Lemma idents_of_context_split gamma:
  Permutation (idents_of_context gamma)
    (concat (map (fun d => map (fun x : funsym => s_name x) (funsyms_of_def d)) gamma) ++
     concat (map (fun d => map (fun x : predsym => s_name x) (predsyms_of_def d)) gamma) ++
     concat (map (fun d => map ts_name (typesyms_of_def d)) gamma)).
Proof.
  induction gamma as [| d gamma IH]; simpl; auto.
  unfold idents_of_context in *; simpl.
  unfold idents_of_def.
  (*Now we need to do all the reordering*)
  (*First is easy*)
  rewrite <- !app_assoc.
  apply Permutation_app_head.
  eapply Permutation_trans.
  2: apply Permutation_app_swap_app.
  apply Permutation_app_head.
  rewrite app_assoc.
  eapply Permutation_trans.
  2:  apply Permutation_app_swap_app.
  rewrite <- !app_assoc.
  apply Permutation_app_head. apply IH.
Qed.

Lemma typesyms_of_context_idents gamma:
  sublist_strong string_dec (map ts_name (typesyms_of_context gamma)) (idents_of_context gamma).
Proof.
  induction gamma as [| d gamma IH]; simpl; auto.
  unfold idents_of_context; simpl.
  unfold typesyms_of_context in *.
  destruct d; try solve[apply sublist_strong_app_l; auto].
  simpl. rewrite map_app.
  apply sublist_strong_app; auto.
  unfold idents_of_def.
  rewrite !app_assoc.
  apply sublist_strong_app_l, sublist_strong_refl.
Qed. 

Lemma funsyms_of_context_idents gamma:
  sublist_strong string_dec (map (fun (x: funsym) => s_name x) (funsyms_of_context gamma)) (idents_of_context gamma).
Proof.
  induction gamma as [| d gamma IH]; simpl; auto.
  unfold idents_of_context; simpl.
  unfold funsyms_of_context in *.
  destruct d; try solve[apply sublist_strong_app_l; auto];
  simpl; rewrite map_app; apply sublist_strong_app; auto;
  unfold idents_of_def; apply sublist_strong_app_r; auto;
  apply sublist_strong_refl.
Qed.

Lemma predsyms_of_context_idents gamma:
  sublist_strong string_dec (map (fun (x: predsym) => s_name x) (predsyms_of_context gamma)) (idents_of_context gamma).
Proof.
  induction gamma as [| d gamma IH]; simpl; auto.
  unfold idents_of_context; simpl.
  unfold predsyms_of_context in *.
  destruct d; try solve[apply sublist_strong_app_l; auto];
  simpl; rewrite map_app; apply sublist_strong_app; auto;
  unfold idents_of_def; 
  apply sublist_strong_app_l, sublist_strong_app_r, sublist_strong_refl.
Qed.

Lemma sig_t_in_idents gamma:
  sublist (map ts_name (sig_t gamma)) (idents_of_context gamma).
Proof.
  induction gamma as [| d1 g1 IH]; simpl; auto.
  - apply sublist_refl.
  - unfold sig_t, idents_of_context in *; simpl; auto.
    rewrite map_app. apply sublist_app2; auto.
    unfold idents_of_def. rewrite app_assoc. 
    apply sublist_app_r.
Qed. 

Lemma sig_f_in_idents gamma:
  sublist (map (fun (x: funsym) => s_name x) (sig_f gamma)) (idents_of_context gamma).
Proof.
  induction gamma as [| d1 g1 IH]; simpl; auto.
  - apply sublist_refl.
  - unfold sig_f, idents_of_context in *; simpl; auto.
    rewrite map_app. apply sublist_app2; auto.
    unfold idents_of_def. apply sublist_app_l. 
Qed. 

Lemma sig_p_in_idents gamma:
  sublist (map (fun (x: predsym) => s_name x) (sig_p gamma)) (idents_of_context gamma).
Proof.
  induction gamma as [| d1 g1 IH]; simpl; auto.
  - apply sublist_refl.
  - unfold sig_p, idents_of_context in *; simpl; auto.
    rewrite map_app. apply sublist_app2; auto.
    unfold idents_of_def. eapply sublist_trans. 2: apply sublist_app_r. 
    apply sublist_app_l. 
Qed. 

Lemma sub_sig_idents g1 g2:
  sublist_sig g1 g2 ->
  (forall x, In x (idents_of_context g1) -> In x (idents_of_context g2)).
Proof.
  unfold sublist_sig.
  unfold sig_t, sig_f, sig_p, idents_of_context, idents_of_def.
  intros [Ht [Hf Hp]] x.
  rewrite !in_concat. setoid_rewrite in_map_iff. 
  intros [l [[d [Hl Hind]] Hinx]]; subst.
  rewrite !in_app_iff in Hinx.
  destruct Hinx as [Hinx | [Hinx | Hinx]].
  - rewrite in_map_iff in Hinx. destruct Hinx as [f [Hx Hinf]]; subst.
    specialize (Hf f). forward Hf.
    { rewrite in_concat. exists (funsyms_of_def d). split; auto. rewrite in_map_iff;
      eauto. }
    rewrite in_concat in Hf. destruct Hf as [fs [Hinfs Hinf2]].
    rewrite in_map_iff in Hinfs.
    destruct Hinfs as [d2 [Hfs Hind2]]; subst.
    (*Now we have g2, can instantiate exists*)
    eexists. split.
    + exists d2. split. reflexivity. auto.
    + rewrite !in_app_iff. left. rewrite in_map_iff. exists f; auto.
  - (*predsym*)
    rewrite in_map_iff in Hinx. destruct Hinx as [f [Hx Hinf]]; subst.
    specialize (Hp f). forward Hp.
    { rewrite in_concat. exists (predsyms_of_def d). split; auto. rewrite in_map_iff;
      eauto. }
    rewrite in_concat in Hp. destruct Hp as [fs [Hinfs Hinf2]].
    rewrite in_map_iff in Hinfs.
    destruct Hinfs as [d2 [Hfs Hind2]]; subst.
    (*Now we have g2, can instantiate exists*)
    eexists. split.
    + exists d2. split. reflexivity. auto.
    + rewrite !in_app_iff. right; left. rewrite in_map_iff. exists f; auto.
  - (*typesym*)
    rewrite in_map_iff in Hinx. destruct Hinx as [f [Hx Hinf]]; subst.
    specialize (Ht f). forward Ht.
    { rewrite in_concat. exists (typesyms_of_def d). split; auto. rewrite in_map_iff;
      eauto. }
    rewrite in_concat in Ht. destruct Ht as [fs [Hinfs Hinf2]].
    rewrite in_map_iff in Hinfs.
    destruct Hinfs as [d2 [Hfs Hind2]]; subst.
    (*Now we have g2, can instantiate exists*)
    eexists. split.
    + exists d2. split. reflexivity. auto.
    + rewrite !in_app_iff. right; right. rewrite in_map_iff. exists f; auto.
Qed.

Lemma eq_sig_idents g1 g2:
  eq_sig g1 g2 ->
  (forall x, In x (idents_of_context g1) <-> In x (idents_of_context g2)).
Proof.
  rewrite eq_sig_sublist.
  intros [Hsub1 Hsub2].
  intros x.
  split; intros Hinx; eapply sub_sig_idents; eauto.
Qed.