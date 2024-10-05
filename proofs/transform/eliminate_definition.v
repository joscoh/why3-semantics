Require Import Task.
Require Import Alpha GenElts.
Require Import eliminate_inductive. (*TODO: not great, factor out common stuff*)
Require Import PatternProofs.
Require Import Denotational2.
Require Import Exhaustive.
Set Bullet Behavior "Strict Subproofs".

(*TODO: move*)
Lemma app_nil_iff {A: Type} (l1 l2: list A):
  l1 ++ l2 = nil <-> l1 = nil /\ l2 = nil.
Proof.
  split.
  - apply app_eq_nil.
  - intros [Hl1 Hl2]; subst; auto.
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

Lemma sublist_strong_filter {A: Type} eq_dec (p: A -> bool) (l1 l2: list A):
  sublist_strong eq_dec l1 l2 ->
  sublist_strong eq_dec (filter p l1) (filter p l2).
Proof.
  revert l1. induction l2 as [|h2 t2 IH]; intros [| h1 t1]; simpl; auto.
  - intros _. apply sublist_strong_nil.
  - intros Hsub. apply orb_true_iff in Hsub. destruct Hsub as [Hsub | Hsub].
    + apply andb_true_iff in Hsub. destruct Hsub as [Heq Hsub].
      destruct (eq_dec h1 h2); subst; [|discriminate].
      destruct (p h2); auto. simpl.
      destruct (eq_dec h2 h2); auto. rewrite IH; auto.
    + apply IH in Hsub. simpl in Hsub.
      destruct (p h2); auto. simpl.
      destruct (if p h1 then h1 :: filter p t1 else filter p t1); auto.
      apply orb_true_iff; right; auto.
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

Lemma omap_app {A B: Type} (f: A -> option B) (l1 l2: list A):
  omap f (l1 ++ l2) = omap f l1 ++ omap f l2.
Proof.
  induction l1 as [| h t IH]; simpl; auto.
  destruct (f h); simpl; auto.
  rewrite IH; auto.
Qed.

Lemma sublist_app2 {A: Type} (l1 l2 l3 l4: list A):
  sublist l1 l3 ->
  sublist l2 l4 ->
  sublist (l1 ++ l2) (l3 ++ l4).
Proof.
  intros Hsub1 Hsub2 x. rewrite !in_app_iff. intros [Hinx1 | Hinx1]; [left | right]; auto.
Qed.

Lemma sublist_nil_l {A: Type} (l: list A):
  sublist nil l.
Proof.
  intros x. contradiction.
Qed.

Lemma sublist_cons_l {A: Type} x (l1 l2: list A):
  sublist l1 l2 ->
  sublist (x :: l1) (x :: l2).
Proof.
  intros Hsub y; simpl.
  intros [Hxy | Hiny]; subst; auto.
Qed.


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
        try (intros x; rewrite in_map_iff; intros [y [Hx Hiny]]; subst; simpl; auto);
        try (rewrite Forall_map, Forall_forall in H0); auto.
    revert H9. apply compile_bare_single_ext_simpl.
    rewrite map_map; reflexivity.
  - intros Hty1 Hty2.
    apply (formula_ind (fun _ => True) (fun f2 => forall f1 (Hty1: formula_typed gamma f1) 
      (Hty2: formula_typed gamma f2),
      formula_typed gamma (f_insert f1 f2))); intros; simpl; auto; 
        try solve[apply F_Eq; assumption]; inversion Hty3; subst; constructor; auto; 
        try (intros x; rewrite in_map_iff; intros [y [Hx Hiny]]; subst; simpl; auto);
        try (rewrite Forall_map, Forall_forall in H0); auto.
    revert H8. apply compile_bare_single_ext_simpl.
    rewrite map_map; reflexivity.
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
  sublist (gen_fv t) vs /\
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
Lemma t_insert_rep {gamma} (gamma_valid: valid_context gamma) pd pdf vt pf vv ty t1 t2 Hty Hty1 Hty2
  (Hdisj: disj (tm_fv t1) (tm_bnd t2)):
  formula_rep gamma_valid pd pdf vt pf vv (t_insert ty t1 t2) Hty =
  all_dec (term_rep gamma_valid pd pdf vt pf vv t1 ty Hty1 =
    term_rep gamma_valid pd pdf vt pf vv t2 ty Hty2).
Proof.
  revert vv t1 Hdisj Hty Hty1 Hty2.
  apply (term_ind (fun t2 => forall vv t1,
    disj (tm_fv t1) (tm_bnd t2) ->
    forall Hty Hty1 Hty2,
    formula_rep gamma_valid pd pdf vt pf vv
    (t_insert ty t1 t2) Hty =
  all_dec
    (term_rep gamma_valid pd pdf vt pf vv t1 ty Hty1 =
  term_rep gamma_valid pd pdf vt pf vv t2 ty Hty2)) (fun _ => True)); simpl; intros; simpl_rep_full; auto.
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
    + erewrite (term_rep_irrel _ _ _ _ _ _ tm1). reflexivity.
    + intros x Hinx. unfold substi. destruct (vsymbol_eq_dec x v); subst; auto.
      exfalso. apply (H1 v); split; simpl; auto.
  - (*Tif*)
    rewrite fmla_rep_irrel with (Hval2:= (proj2' (proj2' (ty_if_inv Hty2)))).
    destruct (formula_rep _ _ _ _ _ _ f _) eqn : Hrep.
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
    (*Need existence of [match_rep] by exhaustiveness*)
    pose proof (well_typed_sem_exhaust gamma_valid pd pdf pf vt vv true ty
      tm v ps Hty2 (proj1' (ty_match_inv Hty2))) as [p [Htyp [Hinp Hmatchp]]].
    generalize dependent (term_rep gamma_valid pd pdf vt pf vv tm v
      (proj1' (ty_match_inv Hty2))).
    (*Get hypotheses we need*)
    clear -H0 H1 Hinp. (*do we need Hty2/info about pattern typing?*)
    induction ps as [|phd ptl IH]; simpl.
    + contradiction.
    + intros d Hmatch1 Hall1 Hall2 Hall3 Hall4.
      destruct phd as [phd tdh]; simpl in *.
      rewrite match_val_single_irrel with (Hval2:=(Forall_inv Hall2)).
      simpl.
      destruct (match_val_single gamma_valid pd pdf vt v phd
        (Forall_inv Hall2) d) as [l1|] eqn : Hmatch.
      * (*use original IH*) rewrite Forall_forall in H0; rewrite H0 with (Hty1:=Hty1)(Hty2:=Forall_inv Hall1); simpl; auto.
        -- rewrite tm_change_vv with (t:=t1)(v2:=vv); [reflexivity|].
          intros x Hinx. rewrite extend_val_notin; auto.
          rewrite <- (match_val_single_free_var _ _ _ _ _ _ _ _ _ _ Hmatch).
          intros Hinx1.
          apply (H1 x); split; auto. rewrite !in_app_iff; auto.
        -- eapply disj_sublist. apply H1. eapply sublist_trans. apply sublist_app_r.
          eapply sublist_trans. apply sublist_app_l. apply sublist_app_r.
      * (*Use IH*) apply IH; auto.
        -- inversion H0; subst; auto.
        -- eapply disj_sublist. apply H1. unfold sublist. intros x. rewrite !in_app_iff.
          intros; destruct_all; auto.
        -- destruct Hinp; subst; auto.
          (*Contradicts [match_val_single] exhaustive*)
          simpl in Hmatch1.
          erewrite match_val_single_irrel in Hmatch.
          rewrite Hmatch in Hmatch1. discriminate.
  - (*epsilon*)
    split_all_dec_eq; auto; [ apply term_rep_irrel|].
    f_equal. repeat (apply functional_extensionality_dep; intros).
    erewrite fmla_rep_irrel.
    erewrite fmla_change_vv. reflexivity.
    intros y Hiny. unfold substi. destruct (vsymbol_eq_dec y v); subst; auto.
    unfold eq_sym; simpl. apply dom_cast_eq.
Qed.

(*And the same for formulas - can we prove easier?*)
Lemma f_insert_rep {gamma} (gamma_valid: valid_context gamma) pd pdf vt pf vv f1 f2 Hty Hty1 Hty2
  (Hdisj: disj (fmla_fv f1) (fmla_bnd f2)):
  formula_rep gamma_valid pd pdf vt pf vv (f_insert f1 f2) Hty =
  eqb (formula_rep gamma_valid pd pdf vt pf vv f1 Hty1)
    (formula_rep gamma_valid pd pdf vt pf vv f2 Hty2).
Proof.
  revert vv f1 Hdisj Hty Hty1 Hty2.
  apply (formula_ind (fun _ => True) (fun f2 => forall vv f1,
    disj (fmla_fv f1) (fmla_bnd f2) ->
    forall Hty Hty1 Hty2,
    formula_rep gamma_valid pd pdf vt pf vv
    (f_insert f1 f2) Hty =
  eqb
    (formula_rep gamma_valid pd pdf vt pf vv f1 Hty1)
  (formula_rep gamma_valid pd pdf vt pf vv f2 Hty2))); simpl; intros; simpl_rep_full; auto;
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
    + erewrite (term_rep_irrel _ _ _ _ _ _ tm). reflexivity.
    + intros x Hinx. unfold substi. destruct (vsymbol_eq_dec x v); subst; auto.
      exfalso. apply (H1 v); split; simpl; auto.
  - (*Fif*)
    rewrite fmla_rep_irrel with (Hval2:= (proj1' (typed_if_inv Hty2))).
    destruct (formula_rep _ _ _ _ _ _ f1 _) eqn : Hrep.
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
    (*Need existence of [match_rep] by exhaustiveness*)
    pose proof (well_typed_sem_exhaust gamma_valid pd pdf pf vt vv false tt
      tm v ps Hty2 (proj1' (typed_match_inv Hty2))) as [p [Htyp [Hinp Hmatchp]]].
    generalize dependent (term_rep gamma_valid pd pdf vt pf vv tm v
      (proj1' (typed_match_inv Hty2))).
    clear -H0 H1 Hinp. 
    induction ps as [|phd ptl IH]; simpl.
    + contradiction.
    + intros d Hmatch1 Hall1 Hall2 Hall3 Hall4.
      destruct phd as [phd tdh]; simpl in *.
      rewrite match_val_single_irrel with (Hval2:=(Forall_inv Hall2)).
      simpl.
      destruct (match_val_single gamma_valid pd pdf vt v phd
        (Forall_inv Hall2) d) as [l1|] eqn : Hmatch.
      * (*use original IH*) rewrite Forall_forall in H0; rewrite H0 with (Hty1:=Hty1)(Hty2:=Forall_inv Hall1); simpl; auto.
        -- rewrite fmla_change_vv with (f:=f1)(v2:=vv); [reflexivity|].
          intros x Hinx. rewrite extend_val_notin; auto.
          rewrite <- (match_val_single_free_var _ _ _ _ _ _ _ _ _ _ Hmatch).
          intros Hinx1.
          apply (H1 x); split; auto. rewrite !in_app_iff; auto.
        -- eapply disj_sublist. apply H1. eapply sublist_trans. apply sublist_app_r.
          eapply sublist_trans. apply sublist_app_l. apply sublist_app_r.
      * (*Use IH*) apply IH; auto.
        -- inversion H0; subst; auto.
        -- eapply disj_sublist. apply H1. unfold sublist. intros x. rewrite !in_app_iff.
          intros; destruct_all; auto.
        -- destruct Hinp; subst; auto.
          (*Contradicts [match_val_single] exhaustive*)
          simpl in Hmatch1.
          erewrite match_val_single_irrel in Hmatch.
          rewrite Hmatch in Hmatch1. discriminate.
Qed.

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

Lemma t_insert_gen_rep {gamma} (gamma_valid: valid_context gamma) pd pdf vt pf vv {b: bool}
  (t1 t2: gen_term b) (ty: gen_type b) Hty Hty1 Hty2
  (Hdisj: disj (gen_fv t1) (gen_bnd t2)):
  formula_rep gamma_valid pd pdf vt pf vv (t_insert_gen ty t1 t2) Hty =
  all_dec (gen_rep gamma_valid pd pdf pf vt vv ty t1 Hty1 = gen_rep gamma_valid pd pdf pf vt vv ty t2 Hty2).
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
      * (*Prove exhaust*)
        revert H8. apply compile_bare_single_ext_simpl.
        rewrite map_map; reflexivity.
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
      * (*Prove exhaust*)
        revert H8. apply compile_bare_single_ext_simpl.
        rewrite map_map; reflexivity.
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
  gen_fv (gen_app b ls tys tms) =
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

Lemma gen_rep_a_convert {b: bool} {gamma} (gamma_valid: valid_context gamma) pd pdf pf vt vv (ty: gen_type b)
  (e: gen_term b) (vs: list vsymbol) Hty1 Hty2:
  gen_rep gamma_valid pd pdf pf vt vv ty (a_convert_gen e vs) Hty1 =
  gen_rep gamma_valid pd pdf pf vt vv ty e Hty2.
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

Definition funpred_defined (gamma: context) {b: bool} :=
  match b return gen_sym b -> list vsymbol -> gen_term b -> Prop with
  | true => fun_defined gamma
  | false => pred_defined gamma
  end.

(*The main result: the axiom we add holds. We factor out because we need in multiple places*)
Lemma rec_axiom_true {gamma} (gamma_valid: valid_context gamma) pd pdf pf vt vv
{b: bool} (ls: gen_sym b) (vs: list vsymbol) (e: gen_term b)
(pf_full: full_interp gamma_valid pd pf)
(Hty: formula_typed gamma (snd (rec_axiom ls vs e)))
(Hval: funpred_def_valid_type gamma (gen_funpred_def b ls vs e))
(Hdef: funpred_defined gamma ls vs e):
formula_rep gamma_valid pd pdf vt pf vv
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
        (Hinxfv: In x (gen_fv e))
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
          (term_rep gamma_valid pd pdf vt pf
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
      (map Tvar vs) (term_rep gamma_valid pd pdf vt pf
      (substi_mult pd vt vv vs h)) (ltac:(intros; apply term_rep_irrel))
      Hlen1 
      ) with (Hi:=Hj').
    rewrite !dom_cast_compose. symmetry.
    gen_dom_cast_eq.
    intros Heq2.
    (*Now simplify to variable*)
    match goal with
    | |- context [term_rep ?v ?pd ?pdf ?vt ?pf ?vv ?t ?ty ?Hty] => generalize dependent Hty
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

(*Gives us fewer cases*)
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
  (Hnoconstrs: Forall (fun f => f_is_constr f = false) (funsyms_of_rec l))
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
  - (*No marked constrs in added funsyms*)
    rewrite Forall_forall in Hnoconstrs |- *. auto.
Qed.

(*A hack*)
Definition is_constr_gen {b: bool} (ls: gen_sym b) : bool :=
  match b return gen_sym b -> bool with
  | true => fun f => f_is_constr f
  | false => fun _ => false
  end ls.

(*Version for nonrec*)
Lemma add_nonrec_abs_valid {gamma gamma1} b1 ls1 vs1 e1
  (gamma1_valid: valid_context gamma1):
  let fd := (gen_funpred_def b1 ls1 vs1 e1) in forall
  (Hwf1: Forall (wf_funsym (nonrec_def fd :: gamma)) (funsyms_of_nonrec fd))
  (Hwf2: Forall (wf_predsym (nonrec_def fd :: gamma)) (predsyms_of_nonrec fd))
  (Hnotsig1: Forall (fun f : funsym => ~ In f (sig_f gamma)) (funsyms_of_nonrec fd))
  (Hnotsig2: Forall (fun f : predsym => ~ In f (sig_p gamma)) (predsyms_of_nonrec fd))
  (Htseq: forall x, In x (sig_t gamma1) <-> In x (sig_t gamma))
  (Hfseq: forall x, In x (sig_f gamma1) <-> In x (sig_f gamma))
  (Hpseq: forall x, In x (sig_p gamma1) <-> In x (sig_p gamma))
  (Hnoconstr: is_constr_gen ls1 = false),
  valid_context ((gen_abs ls1) :: gamma1).
Proof.
  intros fd; intros.
  apply valid_ctx_abstract_app with (l:=[gen_abs ls1]); auto.
  - constructor; auto. rewrite gen_abs_concrete; reflexivity.
  - (*well-formed*)
    simpl. destruct b1; simpl in *; auto. constructor; auto.
    inversion Hwf1; subst. 
    apply wf_funsym_sublist with (g1:=(nonrec_def fd :: gamma)); auto.
    intros t. unfold sig_t. simpl. apply Htseq.
  - (*Well-formed predicate*)
    simpl. destruct b1; simpl in *; auto. constructor; auto.
    inversion Hwf2; subst. 
    apply wf_predsym_sublist with (g1:=(nonrec_def fd :: gamma)); auto.
    intros t. unfold sig_t. simpl. apply Htseq.
  - (*typesyms in signature*)
    simpl. rewrite app_nil_r.
    destruct b1; simpl; auto.
  - (*funsyms notin signature*)
    simpl. rewrite app_nil_r. destruct b1; simpl in *; auto. constructor; auto.
    inversion Hnotsig1; rewrite Hfseq; auto.
  - (*predsyms*)
    simpl. rewrite app_nil_r. destruct b1; simpl in *; auto. constructor; auto.
    inversion Hnotsig2; rewrite Hpseq; auto.
  - (*Nodup is trivial*) simpl. destruct b1; simpl; constructor.
  - simpl. destruct b1; rewrite app_nil_r; simpl; repeat(constructor; auto).
  - simpl. destruct b1; rewrite app_nil_r; simpl; repeat(constructor; auto). 
  - simpl. destruct b1; simpl; constructor; auto.
Qed.

(*Add a concrete def with no typesyms to a context*)
Lemma valid_ctx_concrete_def {gamma} (d: def):
  (*d introduces no new typesyms*)
  typesyms_of_def d = nil ->
  Forall (wf_funsym gamma) (funsyms_of_def d) ->
  Forall (wf_predsym gamma) (predsyms_of_def d) ->
  Forall (fun f => ~ In f (sig_f gamma)) (funsyms_of_def d) ->
  Forall (fun p => ~ In p (sig_p gamma)) (predsyms_of_def d) ->
  NoDup (funsyms_of_def d) ->
  NoDup (predsyms_of_def d) ->
  nonempty_def d ->
  valid_constrs_def d ->
  valid_def (d :: gamma) d ->
  valid_context gamma ->
  valid_context (d :: gamma).
Proof.
  intros Htys Hwf1 Hwf2 Hsig1 Hsig2 Hn1 Hn2 Hne Hconstrs Hval gamma_valid.
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

Lemma split_funpred_defs_partition_length l:
  length (fst (split_funpred_defs l)) =
  length (fst (partition (fun x => match x with | fun_def _ _ _  => true | _ => false end) l)) /\
  length (snd (split_funpred_defs l)) =
  length (snd (partition (fun x => match x with | fun_def _ _ _  => true | _ => false end) l)).
Proof.
  induction l as [|h t [IH1 IH2]]; simpl; auto; split; auto;
  rewrite (surjective_pairing (partition _ _)); simpl; destruct h; simpl; auto.
Qed.

Lemma split_funpred_defs_fst_equiv il:
  fst (split_funpred_defs il) =
  omap (fun x => match x with | fun_def f vs t => Some (f, vs, t) | _ => None end)
    (filter (fun d => match d with | fun_def _ _ _ => true | _ => false end) il).
Proof.
  induction il as [| h t IH]; simpl; auto.
  destruct h; simpl; try rewrite IH; auto.
Qed.

Lemma split_funpred_defs_snd_equiv il:
  snd (split_funpred_defs il) =
  omap (fun x => match x with | pred_def f vs t => Some (f, vs, t) | _ => None end)
    (filter (fun d => match d with | pred_def _ _ _ => true | _ => false end) il).
Proof.
  induction il as [| h t IH]; simpl; auto.
  destruct h; simpl; try rewrite IH; auto.
Qed.

(*Annoying but we need it*)
Definition fs_vs_tm_eq_dec (x y: funsym * (list vsymbol) * term):
  {x = y} + {x <> y} :=
  tuple_eq_dec (tuple_eq_dec funsym_eq_dec (list_eq_dec vsymbol_eq_dec)) term_eq_dec x y.
Definition ps_vs_fmla_eq_dec (x y: predsym * (list vsymbol) * formula):
  {x = y} + {x <> y} :=
  tuple_eq_dec (tuple_eq_dec predsym_eq_dec (list_eq_dec vsymbol_eq_dec)) formula_eq_dec x y.

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

Lemma funpred_defs_to_sns_fst_length l is:
  length l = length is ->
  length (fst (funpred_defs_to_sns l is)) = length (fst (split_funpred_defs l)).
Proof.
  intros Hlen.
  unfold funpred_defs_to_sns.
  simpl. rewrite map_length, combine_length, firstn_length.
  pose proof (split_funpred_defs_length l). lia.
Qed.


Definition fn_eq_dec f1 f2 := reflect_dec' (fn_eqb_spec f1 f2).
Definition pn_eq_dec p1 p2 := reflect_dec' (pn_eqb_spec p1 p2).

(*Prove that [decrease_fun] continues to hold on a subset (strong) of the fn and pn lists*)
Lemma decrease_fun_subset_aux (fn1 fn2: list fn) (pn1 pn2: list pn) m vs
  (Hsub1: sublist fn1 fn2)
  (Hsub2: sublist pn1 pn2)
  (Hn1: NoDup (map fn_sym fn2))
  (Hn2: NoDup (map pn_sym pn2)) 
  (t: term) (f: formula):
  (forall small hd (Hdec: decrease_fun fn2 pn2 small hd m vs t), decrease_fun fn1 pn1 small hd m vs t) /\
  (forall small hd (Hdec: decrease_pred fn2 pn2 small hd m vs f), decrease_pred fn1 pn1 small hd m vs f).
Proof.
  revert t f; apply term_formula_ind; try solve[intros; constructor];
  try solve[intros; inversion Hdec; constructor; auto].
  - (*Tfun case*)
    intros f1 tys tms IH small hd Hdec. inversion Hdec; subst.
    + (*Either f_decl is in fn1 or not*)
      destruct (in_dec fn_eq_dec f_decl fn1) as [Hin | Hnotin].
      * eapply Dec_fun_in; eauto.
        revert IH H11. rewrite !Forall_forall. auto.
      * apply Dec_fun_notin; auto.
        -- rewrite in_map_iff. intros [f2 [Hfsym Hinf2]].
          assert (f_decl = f2). { symmetry. eapply NoDup_map_in; eauto. }
          subst; contradiction.
        -- rewrite Forall_forall in H11, IH; auto.
    + apply Dec_fun_notin; auto.
      * intros Hinf1.
        apply (sublist_map fn_sym) in Hsub1.
        apply Hsub1 in Hinf1. contradiction.
      * rewrite Forall_forall in IH; auto.
  - intros tm ty ps IH1 IHps small hd Hdec.
    rewrite Forall_map in IHps. rewrite Forall_forall in IHps.
    inversion Hdec; subst.
    + apply Dec_tmatch; auto.
    + apply Dec_tmatch_constr; auto.
    + apply Dec_tmatch_rec; auto.
  - intros f1 tys tms IH small hd Hdec. inversion Hdec; subst.
    + (*Either f_decl is in fn1 or not*)
      destruct (in_dec pn_eq_dec p_decl pn1) as [Hin | Hnotin].
      * eapply Dec_pred_in; eauto.
        revert IH H11. rewrite !Forall_forall. auto.
      * apply Dec_pred_notin; auto.
        -- rewrite in_map_iff. intros [f2 [Hfsym Hinf2]].
          assert (p_decl = f2). { symmetry. eapply NoDup_map_in; eauto. }
          subst; contradiction.
        -- rewrite Forall_forall in H11, IH; auto.
    + apply Dec_pred_notin; auto.
      * intros Hinf1.
        apply (sublist_map pn_sym) in Hsub2.
        apply Hsub2 in Hinf1. contradiction.
      * rewrite Forall_forall in IH; auto.
  - intros tm ty ps IH1 IHps small hd Hdec.
    rewrite Forall_map in IHps. rewrite Forall_forall in IHps.
    inversion Hdec; subst.
    + apply Dec_fmatch; auto.
    + apply Dec_fmatch_constr; auto.
    + apply Dec_fmatch_rec; auto.
Qed.

Definition decrease_fun_subset fn1 fn2 pn1 pn2
  (Hsub1: sublist fn1 fn2)
  (Hsub2: sublist pn1 pn2)
  (Hn1: NoDup (map fn_sym fn2))
  (Hn2: NoDup (map pn_sym pn2)) 
  m vs small hd t :=
  proj_tm (decrease_fun_subset_aux fn1 fn2 pn1 pn2 m vs Hsub1 Hsub2 Hn1 Hn2) t small hd.
Definition decrease_pred_subset fn1 fn2 pn1 pn2
  (Hsub1: sublist fn1 fn2)
  (Hsub2: sublist pn1 pn2)
  (Hn1: NoDup (map fn_sym fn2))
  (Hn2: NoDup (map pn_sym pn2)) 
  m vs small hd f :=
  proj_fmla (decrease_fun_subset_aux fn1 fn2 pn1 pn2 m vs Hsub1 Hsub2 Hn1 Hn2) f small hd.

(*A key part of the proof: prove the new, truncated recursive definition well-formed.
  Termination is the trickiest part*)
Lemma sublist_strong_rec_wf l1 l2 gamma1 gamma2
  (Hwf: wf_context gamma2)
  (Hsig: sublist_sig gamma2 gamma1)
  (Hmut: sublist (mut_of_context gamma2) (mut_of_context gamma1))
  (Hsub: sublist_strong funpred_def_eq_dec l1 l2)
  (Hnotnil: l1 <> nil)
  (Hinmut: In l2 (mutfuns_of_context gamma2)):
  funpred_valid gamma2 l2 ->
  funpred_valid gamma1 l1.
Proof.
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
  - (*The hard part - termination*)
    revert Hterm.
    unfold funpred_def_term_exists.
    intros [m [params [vs [is Hterm]]]].
    exists m. exists params. exists vs.
    unfold funpred_def_term in Hterm.
    destruct Hterm as [Hl2 [Hlenvs [Hm_in [Hlenis [His [Hftys [Hptys [Hfparams [Hpparams [Hdecfun Hdecpred]]]]]]]]]].
    (*We need to get index lists - compose index lists (from [sublist_strong indicies] for
      each side of [split_funpred_defs])*)
    assert (Hsub1: sublist_strong fs_vs_tm_eq_dec (fst (split_funpred_defs l1)) (fst (split_funpred_defs l2))).
    {
      rewrite !split_funpred_defs_fst_equiv. eapply sublist_strong_omap.
      eapply sublist_strong_filter. apply Hsub.
    }
    assert (Hsub2: sublist_strong ps_vs_fmla_eq_dec (snd (split_funpred_defs l1)) (snd (split_funpred_defs l2))).
    {
      rewrite !split_funpred_defs_snd_equiv. eapply sublist_strong_omap.
      eapply sublist_strong_filter. apply Hsub.
    }
    (*Difficulty: we know that l1 is a sublist of l2. We have to build up the appropriate list.
      We did this in the previous lemma (sublist_strong_indices)*)
    destruct (sublist_strong_indices _ (id_fs, nil, tm_d) _ _ Hsub1) as [idx1 [Hlen1 [Hallidx1 Hfst]]].
    destruct (sublist_strong_indices _ (id_ps, nil, Ftrue) _ _ Hsub2) as [idx2 [Hlen2 [Hallidx2 Hsnd]]].
    set (is1:= map (fun i => nth i is 0) idx1).
    set (is2:= map (fun i => nth (length (fst (split_funpred_defs l2)) + i) is 0) idx2).
    (*And results we need from this*)
    assert (Hij1: forall i, i < length (fst (split_funpred_defs l1)) ->
      exists j, j < length (fst (split_funpred_defs l2)) /\
      nth i (fst (split_funpred_defs l1)) (id_fs, nil, tm_d) =
      nth j (fst (split_funpred_defs l2)) (id_fs, nil, tm_d) /\
      nth i is1 0 = nth j is 0).
    {
      intros i Hi. exists (nth i idx1 0). split_all.
      - rewrite Forall_forall in Hallidx1. apply Hallidx1; auto. apply nth_In; lia.
      - rewrite Hfst. rewrite map_nth_inbound with (d2:=0); auto. lia.
      - unfold is1. rewrite map_nth_inbound with (d2:=0); auto; lia.
    }
    assert (Hij2: forall i, i < length (snd (split_funpred_defs l1)) ->
      exists j, j < length (snd (split_funpred_defs l2)) /\
      nth i (snd (split_funpred_defs l1)) (id_ps, nil, Ftrue) =
      nth j (snd (split_funpred_defs l2)) (id_ps, nil, Ftrue) /\
      nth i is2 0 = nth (length (fst (split_funpred_defs l2)) + j) is 0).
    {
      intros i Hi. exists (nth i idx2 0). split_all.
      - rewrite Forall_forall in Hallidx2. apply Hallidx2; auto. apply nth_In; lia.
      - rewrite Hsnd. rewrite map_nth_inbound with (d2:=0); auto. lia.
      - unfold is2. rewrite map_nth_inbound with (d2:=0); auto. lia.
    }
    (*Then indicies are (is1 ++ is2)*)
    exists (is1 ++ is2).
    assert (Hlen3: length is1 = length (fst (split_funpred_defs l1))) by (unfold is1; rewrite map_length; auto).
    assert (Hlen4: length is2 = length (snd (split_funpred_defs l1))) by (unfold is2; rewrite map_length; auto).
    pose proof (split_funpred_defs_length l1) as Hsplitlen.
    pose proof (split_funpred_defs_length l2) as Hsplitlen2.
    (*Need for fun/pred termination*)
    assert (Hsubfst: sublist (fst (funpred_defs_to_sns l1 (is1 ++ is2)))
    (fst (funpred_defs_to_sns l2 is))).
    {
      intros x.
      rewrite !funpred_defs_to_sns_in_fst; [| lia | rewrite app_length; lia]; simpl.
      intros [i [Hi Hx]]; subst.
      specialize (Hij1 i (ltac:(lia))).
      destruct Hij1 as [j [Hj [Hnthij Hnthij2]]].
      rewrite app_nth1 by lia.
      rewrite Hnthij, Hnthij2. exists j. auto.
    }
    assert (Hsubsnd: sublist (snd (funpred_defs_to_sns l1 (is1 ++ is2)))
    (snd (funpred_defs_to_sns l2 is))).
    {
      intros x.
      rewrite !funpred_defs_to_sns_in_snd; [| lia | rewrite app_length; lia].
      rewrite !funpred_defs_to_sns_fst_length; [| lia|  rewrite app_length; lia]. simpl.
      intros [i [Hi Hx]]; subst.
      specialize (Hij2 i (ltac:(lia))).
      destruct Hij2 as [j [Hj [Hnthij Hnthij2]]].
      rewrite app_nth2 by lia.
      rewrite <- Hlen3.
      replace (length is1 + i - length is1) with i by lia.
      rewrite Hnthij, Hnthij2. exists j. auto.
    }

    unfold funpred_def_term. split_all; auto.
    + eapply mut_in_ctx_sublist; eassumption.
    + rewrite app_length. lia.
    + (*Prove bound on nth*) intros i Hi.
      rewrite app_length in Hi.
      assert (Hi2: i < length is1 \/ length is1 <= i < length l1) by lia.
      destruct Hi2 as [Hi2 | Hi2].
      * rewrite !app_nth1; auto; [|rewrite map_length; lia].
        rewrite map_nth_inbound with (d2:=(id_fs, nil, tm_d)) by lia.
        specialize (Hij1 i (ltac:(lia))).
        destruct Hij1 as [j [Hj [Hnthij Hnthij2]]].
        rewrite Hnthij, Hnthij2.
        specialize (His j (ltac:(lia))).
        revert His. rewrite app_nth1 by (rewrite map_length; lia).
        rewrite map_nth_inbound with (d2:=(id_fs, nil, tm_d)); auto.
      * rewrite !app_nth2; auto; [|rewrite map_length; lia| lia].
        rewrite map_length, map_nth_inbound with (d2:=(id_ps, nil, Ftrue)) by lia.
        specialize (Hij2 (i - length is1) (ltac:(lia))).
        destruct Hij2 as [j [Hj [Hnthij Hnthij2]]].
        rewrite <- Hlen3, Hnthij, Hnthij2.
        specialize (His (length (fst (split_funpred_defs l2)) + j) (ltac:(lia))).
        revert His. rewrite app_nth2; rewrite map_length; [|lia].
        rewrite TerminationChecker.plus_minus.
        rewrite map_nth_inbound with (d2:=(id_ps, nil, Ftrue)); auto.
    + (*And prove all [decrease_fun]*)
      rewrite Forall_forall.
      intros f.  rewrite funpred_defs_to_sns_in_fst by (rewrite app_length; lia).
      intros [i [Hi Hy]].
      set (y:=nth i (fst (split_funpred_defs l1)) (id_fs, [], tm_d)) in *.
      simpl in Hy; subst.
      rewrite app_nth1 by lia. Opaque funpred_defs_to_sns. simpl.
      specialize (Hij1 i (ltac:(lia))).
      destruct Hij1 as [j [Hj [Hnthij Hnthij2]]].
      rewrite Hnthij2.
      rewrite Forall_forall in Hdecfun.
      specialize (Hdecfun (let y := (nth j (fst (split_funpred_defs l2)) (id_fs, nil, tm_d))
        in fundef_to_fn (fst (fst y)) (snd (fst y)) (snd y) (nth j is 0))).
      rewrite <-  Hnthij in Hdecfun.
      eapply decrease_fun_subset.  
      5: { apply Hdecfun. apply funpred_defs_to_sns_in_fst; auto. exists j; auto. split; auto.
        rewrite Hnthij. auto. }
      all: auto.
      all: eapply funpred_defs_to_sns_NoDup; eauto.
    + (*[decrease_pred] similar*)
      rewrite Forall_forall.
      intros f.  rewrite funpred_defs_to_sns_in_snd by (rewrite app_length; lia).
      rewrite funpred_defs_to_sns_fst_length by (rewrite app_length; lia).
      intros [i [Hi Hy]].
      set (y:=nth i (snd (split_funpred_defs l1)) (id_ps, [], Ftrue)) in *.
      simpl in Hy; subst.
      rewrite app_nth2 by lia. Opaque funpred_defs_to_sns. simpl.
      specialize (Hij2 i (ltac:(lia))).
      destruct Hij2 as [j [Hj [Hnthij Hnthij2]]]. subst y; simpl.
      rewrite <- Hlen3. replace (length is1 + i - length is1) with i by lia.
      rewrite Hnthij, Hnthij2.
      rewrite Forall_forall in Hdecpred.
      specialize (Hdecpred (let y := (nth j (snd (split_funpred_defs l2)) (id_ps, nil, Ftrue))
        in preddef_to_pn (fst (fst y)) (snd (fst y)) (snd y) (nth (length (fst (split_funpred_defs l2)) + j) is 0))).
      set (y2:=(nth j (snd (split_funpred_defs l2)) (id_ps, nil, Ftrue))) in *.
      simpl in Hdecpred.
      eapply decrease_pred_subset.  
      5: { apply Hdecpred. apply funpred_defs_to_sns_in_snd; auto. exists j; auto. split; auto.
        rewrite funpred_defs_to_sns_fst_length; auto.
      }
      all: auto.
      all: eapply funpred_defs_to_sns_NoDup; eauto.
Qed.



Lemma decl_list_of_def_muts which b l:
  mut_of_context (rev (decl_list_of_def which b l)) = nil.
Proof.
  unfold decl_list_of_def. simpl.
  rewrite rev_app_distr, mut_of_context_app.
  apply app_nil_iff. split.
  - destruct (Pattern.filter_map _ _) as [|h t]; simpl; auto.
    destruct t; simpl; auto.
    destruct b; simpl; auto.
  - induction l as [| h t IH]; simpl; auto.
    destruct (gen_funpred_def_match h) as [b1 [[ls vs] e]] eqn : Hdef.
    apply gen_funpred_def_match_eq in Hdef. subst.
    destruct (which b1 ls); simpl; auto.
    rewrite mut_of_context_app; simpl. 
    destruct b1; simpl in *; rewrite app_nil_r; auto.
Qed.

Lemma gen_new_ctx_gamma_mut which nonrec gamma:
  mut_of_context (gen_new_ctx_gamma' which nonrec gamma) = mut_of_context gamma.
Proof.
  unfold gen_new_ctx_gamma'. induction gamma; simpl; auto.
  destruct (is_rec_nonrec a) eqn : Hind.
  - destruct a; inversion Hind; subst.
    rewrite mut_of_context_app.
    rewrite decl_list_of_def_muts; auto.
  - destruct o as [x|].
    + destruct a; inversion Hind; subst. 
      destruct nonrec; auto.
      rewrite mut_of_context_app, decl_list_of_def_muts. simpl; auto.
    + destruct a; simpl; auto. f_equal; auto. 
Qed.

Lemma sig_t_app l1 l2:
  sig_t (l1 ++ l2) = sig_t l1 ++ sig_t l2.
Proof. unfold sig_t. rewrite map_app, concat_app. reflexivity. Qed. 

Lemma decl_list_of_def_sig_t which nonrec l:
sig_t (rev (decl_list_of_def which nonrec l)) = nil.
Proof. apply get_recfun_defs_typesyms. Qed.

Lemma gen_new_ctx_gamma_sig_t which nonrec gamma:
  sig_t (gen_new_ctx_gamma' which nonrec gamma) = sig_t gamma.
Proof.
  unfold gen_new_ctx_gamma'. induction gamma; simpl; auto.
  destruct (is_rec_nonrec a) eqn : Hind.
  - destruct a; inversion Hind; subst.
    replace (recursive_def l :: gamma) with ([recursive_def l] ++ gamma) by reflexivity.
    rewrite !sig_t_app. rewrite decl_list_of_def_sig_t; auto. 
  - destruct o as [x|].
    + destruct a; inversion Hind; subst. 
      destruct nonrec; auto.
      replace (nonrec_def x :: gamma) with ([nonrec_def x] ++ gamma) by reflexivity.
      rewrite !sig_t_app. rewrite !decl_list_of_def_sig_t; auto. 
    + destruct a; simpl; auto; unfold sig_t;simpl; f_equal; auto.
Qed.

Lemma valid_context_change_tl {gamma1 gamma} {d: def}
  (Hval: valid_context (d :: gamma))
  (Hval2: valid_context gamma1)
  (Hmut: mut_of_context gamma = mut_of_context gamma1)
  (Ht: sig_t gamma = sig_t gamma1) (*TODO: comes from inhab check, could probably
    relax and use the smaller length for the lemma*)
  (Htseq: forall x, In x (sig_t gamma1) <-> In x (sig_t gamma))
  (Hfseq: forall x, In x (sig_f gamma1) <-> In x (sig_f gamma))
  (Hpseq: forall x, In x (sig_p gamma1) <-> In x (sig_p gamma)):
  valid_context (d :: gamma1).
Proof.
  inversion Hval; subst. constructor; auto.
  - revert H2. rewrite !Forall_forall. intros Hwf1 x Hinx.
    eapply wf_funsym_sublist. 2: apply Hwf1; auto.
    unfold sig_t. simpl.
    apply sublist_app2; auto; [apply sublist_refl |intros t; apply Htseq].
  - revert H3. rewrite !Forall_forall. intros Hwf1 x Hinx.
    eapply wf_predsym_sublist. 2: apply Hwf1; auto.
    unfold sig_t. simpl.
    apply sublist_app2; auto; [apply sublist_refl |intros t; apply Htseq].
  - revert H4. rewrite !Forall_forall. setoid_rewrite Hfseq. auto.
  - revert H5. rewrite !Forall_forall. setoid_rewrite Hpseq. auto.
  - revert H6. rewrite !Forall_forall. setoid_rewrite Htseq. auto.
  - eapply valid_def_sublist. 4: apply H12.
    + unfold sublist_sig, sig_t, sig_f, sig_p; simpl.
      split_all; apply sublist_app2; auto; try solve[apply sublist_refl];
      intros x; [apply Htseq | apply Hfseq | apply Hpseq].
    + unfold sig_t. simpl. f_equal. apply Ht.
    + unfold mut_of_context. simpl. destruct d; simpl; auto. f_equal; auto.
Qed.

Lemma convert_is_constr fs:
  (forallb (fun f => negb (f_is_constr f)) fs) <->
  Forall (fun f => f_is_constr f = false) fs.
Proof.
  unfold is_true; rewrite forallb_forall, Forall_forall;
  split; intros Hallin x Hin; specialize (Hallin _ Hin);
  destruct (f_is_constr x); auto.
Qed.

Lemma sublist_strong_forallb {A: Type} (p: A -> bool) eq_dec (l1 l2: list A):
  sublist_strong eq_dec l1 l2 ->
  forallb p l2 ->
  forallb p l1.
Proof.
  intros Hsub Hall.
  apply sublist_strong_in in Hsub.
  unfold is_true in *.
  rewrite forallb_forall in Hall |-  *. auto.
Qed.
  
(*Prove that the new context is valid*)
Lemma gen_new_ctx_valid which nonrec gamma:
  valid_context gamma ->
  valid_context (gen_new_ctx_gamma' which nonrec gamma).
Proof.
  intros.
  pose proof (gen_new_ctx_gamma_mut which nonrec gamma) as Hmuts.
  pose proof (gen_new_ctx_gamma_sig_t which nonrec gamma) as Hsigteq.
  induction H; simpl; try solve[constructor]. (*TODO: see if we put here or just prove at end*)
  assert (Hval2: valid_context (d :: gamma)) by (constructor; auto).
  unfold gen_new_ctx_gamma' in *. simpl in Hmuts, Hsigteq |- *.
  assert (Heqctx:=gen_new_ctx_gamma_eq_sig which nonrec gamma).
  unfold eq_sig in Heqctx. destruct Heqctx as [Htseq [Hfseq Hpseq]].
  rewrite mut_of_context_app in Hmuts.
  rewrite sig_t_app in Hsigteq.
  destruct (is_rec_nonrec d) as [l| [fd |]] eqn : Hrec.
  - (*recursive case*) destruct d; inversion Hrec; subst. simpl in *.
    rewrite decl_list_of_def_muts in Hmuts. simpl in Hmuts.
    rewrite decl_list_of_def_sig_t in Hsigteq. simpl in Hsigteq.
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
      apply convert_is_constr; auto.
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
      destruct b1; inversion H12; subst.
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
      destruct b1; inversion H12; subst.
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
    + (*constrs*) simpl. 
      apply (sublist_strong_forallb (fun f => negb(f_is_constr f))) in  Hfuns; [|assumption].
      destruct h; simpl; auto.
    + (*The more interesting part - prove that the definition is valid*)
      revert H10.
      apply sublist_strong_rec_wf; auto.
      * apply valid_context_wf; auto.
      * (*Prove [sublist_sig]*)
        unfold sublist_sig. split_all.
        -- (*typesyms*)
          unfold sig_t at 2. Opaque decls_of_def. simpl. apply Hsigt. Transparent decls_of_def.
        -- (*funsyms*)
          intros x. pose proof (get_recfun_defs_funsyms which false l x) as Hfunseq.
          unfold sig_f. (*generalize dependent l1.*) (*To stop Coq from unfolding this, why is this so hard?*) 
          simpl. rewrite map_app, concat_app, app_assoc. rewrite !in_app_iff.
          apply or_iff; auto.
          rewrite <- Hfunseq.
          unfold decl_list_of_def. 
          rewrite rev_app_distr, map_app, concat_app.
          rewrite in_app_iff. apply or_iff; [|reflexivity].
          simpl. rewrite Hpat. unfold l1.
          destruct h; simpl; destruct t; simpl; try rewrite app_nil_r; reflexivity.
        -- (*predsyms*)
          intros x. pose proof (get_recfun_defs_predsyms which false l x) as Hfunseq.
          unfold sig_p. (*generalize dependent l1.*) (*To stop Coq from unfolding this, why is this so hard?*) 
          simpl. rewrite map_app, concat_app, app_assoc. rewrite !in_app_iff.
          apply or_iff; auto.
          rewrite <- Hfunseq.
          unfold decl_list_of_def. 
          rewrite rev_app_distr, map_app, concat_app.
          rewrite in_app_iff. apply or_iff; [|reflexivity].
          simpl. rewrite Hpat. unfold l1.
          destruct h; simpl; destruct t; simpl; try rewrite app_nil_r; reflexivity.
      * (*Prove [mut_of_context] sublist - dont add anything*)
        Opaque decls_of_def.
        simpl.  Transparent decls_of_def. rewrite mut_of_context_app.
        (*TODO: START HERE*)
        match goal with |- sublist ?x (?y ++ ?z) =>
          let H := fresh in
          assert (H: y = nil); [| rewrite H]
        end.
        2: {
          simpl. intros x. rewrite <- Hmuts. auto.
        }
        pose proof (decl_list_of_def_muts which false l) as Hmut2.
        unfold decl_list_of_def in Hmut2.
        rewrite rev_app_distr,  mut_of_context_app in Hmut2.
        apply app_nil_iff in Hmut2.
        apply Hmut2.
      * unfold l1; inv Hlist.
      * simpl. auto.
  - (*nonrec case*)
    destruct d; inversion Hrec; subst. simpl in *.
    unfold decl_list_of_def at 1.
    unfold decl_list_of_def at 1 in Hmuts.
    unfold decl_list_of_def at 1 in Hsigteq.
    simpl in Hmuts, Hsigteq |- *.
    destruct (gen_funpred_def_match fd) as [b1 [[ls1 vs1] e1]] eqn : Hdef.
    rewrite gen_funpred_def_match_eq in Hdef. subst.
    assert (Hmuts2: mut_of_context (rev ([gen_abs ls1] ++ [])) = nil).
    { simpl. destruct b1; auto. }
    assert (Hsig2: sig_t (rev ([gen_abs ls1] ++ [])) = nil).
    { simpl. destruct b1; auto. }
    destruct nonrec; [destruct (which b1 ls1) eqn : Hwhich|].
    (*TODO: last 2 cases are the same, solve*)
    + (*Add abstract symbol*) simpl.
      rewrite Hmuts2 in Hmuts.
      rewrite Hsig2 in Hsigteq.
      eapply add_nonrec_abs_valid with (vs1:=vs1)(e1:=e1); eauto.
      (*prove constr*) destruct b1; simpl in *; auto. destruct (f_is_constr ls1); auto. 
    + (*Don't change context*)
      simpl. auto.
      eapply valid_context_change_tl. apply Hval2. all: auto.
    + simpl. auto.
      eapply valid_context_change_tl. apply Hval2. all: auto.
  - (*No change to context*) simpl.
    replace (d :: gamma) with ([d] ++ gamma) in Hsigteq by reflexivity.
    rewrite sig_t_app in Hsigteq.
    apply app_inv_head in Hsigteq.
    match goal with 
    | H: mut_of_context ?x ++ ?y = _ |- _ =>
      let H2 := fresh "Hmut" in
      assert (H2: y = mut_of_context gamma)
    end.
    { destruct d; simpl in Hmuts; auto. inversion Hmuts; auto. }
    eapply valid_context_change_tl. apply Hval2. all: auto.
Qed.

End NewContext.


(*Convert an interpretation from gamma into one onto
  [gen_new_ctx_gamma gamma].
  This is very simple; we use the same funs and preds*)

(*Note: these lemmas are exactly the same as [eliminate_inductive]. Can we generalize?*)

Lemma gen_new_ctx_funs_constrs which nonrec  {gamma} (gamma_valid: valid_context gamma) 
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf):
  forall (m : mut_adt) (a : alg_datatype) 
    (c : funsym) (Hm : mut_in_ctx m (gen_new_ctx_gamma' which nonrec gamma)) 
    (Ha : adt_in_mut a m) (Hc : constr_in_adt c a)
    (srts : list sort)
    (Hlens : Datatypes.length srts =
              Datatypes.length (m_params m))
    (args : arg_list (domain (dom_aux pd))
              (sym_sigma_args c srts)),
  funs gamma_valid pd pf c srts args =
  constr_rep_dom (gen_new_ctx_valid which nonrec _ gamma_valid) m Hm srts Hlens 
    (dom_aux pd) a Ha c Hc (adts 
      (change_gamma_dom_full (eq_sym (gen_new_ctx_gamma_mut which nonrec gamma)) pd pdf) m srts) args.
Proof.
  intros.
  assert (m_in: mut_in_ctx m gamma). {
    revert Hm. apply mut_in_ctx_sublist.
    rewrite gen_new_ctx_gamma_mut. apply incl_refl.
  }
  rewrite (constrs _ pd pdf pf m a c m_in Ha Hc srts Hlens).
  unfold constr_rep_dom.
  simpl. unfold change_gamma_adts. simpl.
  f_equal.
  - f_equal.
    + f_equal. f_equal. apply bool_irrelevance.
    + f_equal. apply UIP_dec, sort_eq_dec.
  - apply constr_rep_change_gamma.
Qed.

Definition gen_new_ctx_pf which nonrec {gamma} (gamma_valid: valid_context gamma) 
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf):
pi_funpred (gen_new_ctx_valid which nonrec _ gamma_valid) pd 
  (change_gamma_dom_full (eq_sym (gen_new_ctx_gamma_mut which nonrec gamma)) pd pdf) :=
Build_pi_funpred (gen_new_ctx_valid which nonrec _ gamma_valid) pd _
  (funs gamma_valid pd pf)
  (preds gamma_valid pd pf)
  (gen_new_ctx_funs_constrs which nonrec gamma_valid pd pdf pf).

(*And we prove that every formula true under this pf in gamma'
  is true under the original in gamma, and vice versa.
  This is trivial*)
Lemma tm_gen_new_ctx_pf which nonrec {gamma} (gamma_valid: valid_context gamma) 
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
(vt: val_typevar) (vv: val_vars pd vt) (t: term) (ty: vty)
(Hty1: term_has_type gamma t ty)
(Hty2: term_has_type (gen_new_ctx_gamma' which nonrec gamma) t ty):
term_rep (gen_new_ctx_valid which nonrec _ gamma_valid) pd _ vt
  (gen_new_ctx_pf which nonrec gamma_valid pd pdf pf) vv t ty Hty2 =
term_rep gamma_valid pd pdf vt pf vv t ty Hty1.
Proof.
  apply term_change_gamma_pf; simpl; auto.
  rewrite gen_new_ctx_gamma_mut; auto.
Qed.

Lemma fmla_gen_new_ctx_pf which nonrec {gamma} (gamma_valid: valid_context gamma) 
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
(vt: val_typevar) (vv: val_vars pd vt) (f: formula)
(Hty1: formula_typed gamma f)
(Hty2: formula_typed (gen_new_ctx_gamma' which nonrec gamma) f):
formula_rep (gen_new_ctx_valid which nonrec _ gamma_valid) pd _ vt
  (gen_new_ctx_pf which nonrec gamma_valid pd pdf pf) vv f Hty2 =
formula_rep gamma_valid pd pdf vt pf vv f Hty1.
Proof.
  apply fmla_change_gamma_pf; simpl; auto.
  rewrite gen_new_ctx_gamma_mut; auto.
Qed.

Lemma decl_list_of_def_mutfuns which nonrec l:
  sublist (concat (mutfuns_of_context
    (rev (decl_list_of_def which nonrec l)))) l.
Proof.
  unfold decl_list_of_def. rewrite rev_app_distr, mutfuns_of_context_app, concat_app.
  apply app_sublist.
  - simpl.
    assert (Hsubpat: sublist (Pattern.filter_map
      (fun x : funpred_def =>
    let (b, p) := gen_funpred_def_match x in let (p0, _) :=
      p in let (ls, _) := p0 in if which b ls then None else
    Some x)
      l) l).
    {
      intros x. rewrite in_filter_map_iff. intros [d [Hind Hx]].
      destruct (gen_funpred_def_match d) as [b1 [[ls vs] e]] eqn : Hdef.
      apply gen_funpred_def_match_eq in Hdef. subst.
      destruct (which b1 ls); inversion Hx; subst; auto.
    }
    destruct (Pattern.filter_map _ l) as [| h t] eqn : Hpat; auto.
    destruct t as [| h2 t2]; [destruct nonrec|]; auto.
    + simpl. apply sublist_nil_l.
    + simpl. rewrite app_nil_r; auto.
  - simpl.
    match goal with |- sublist ?x ?l => let H := fresh in
      assert (H: x = nil); [| rewrite H; apply sublist_nil_l]
    end.
    induction l as [| h t IH]; simpl; auto.
    destruct (gen_funpred_def_match h) as [b1 [[ls vs] e]] eqn : Hdef.
    apply gen_funpred_def_match_eq in Hdef. subst.
    destruct (which b1 ls); simpl; auto.
    rewrite mutfuns_of_context_app; simpl.
    destruct b1; simpl; rewrite app_nil_r; auto.
Qed.

Lemma decl_list_of_def_nonrec_mutfuns which f:
  (concat (mutfuns_of_context
    (rev (decl_list_of_def which true [f])))) = nil.
Proof.
  unfold decl_list_of_def. rewrite rev_app_distr, mutfuns_of_context_app, concat_app.
  simpl.
  destruct (gen_funpred_def_match f) as [b1 [[ls vs] e]] eqn : Hdef.
  apply gen_funpred_def_match_eq in Hdef. subst.
  destruct (which b1 ls); simpl; auto.
  destruct b1; auto.
Qed.

Lemma gen_new_ctx_gamma_mutfuns which nonrec gamma:
  sublist (concat (mutfuns_of_context (gen_new_ctx_gamma' which nonrec gamma)))
    (concat (mutfuns_of_context gamma)).
Proof.
  unfold gen_new_ctx_gamma'.
  induction gamma as [| gh gtl IH]; simpl; auto; [apply sublist_refl|].
  rewrite mutfuns_of_context_app, concat_app.
  destruct (is_rec_nonrec gh) as [l|[fd|]] eqn : Hisrec.
  - destruct gh; inversion Hisrec; subst. clear Hisrec.
    simpl.
    apply sublist_app2; auto.
    apply decl_list_of_def_mutfuns.
  - (*nonrec*)
    destruct gh; inversion Hisrec; subst.
    destruct nonrec; simpl; auto.
    rewrite decl_list_of_def_nonrec_mutfuns.
    auto.
  - (*other*)
    destruct gh; inversion Hisrec; subst; auto.
Qed.

Lemma nonrec_of_context_app l1 l2:
  nonrec_of_context (l1 ++ l2) = nonrec_of_context l1 ++ nonrec_of_context l2.
Proof.
  induction l1 as [| h t IH]; simpl; auto.
  destruct h; simpl; auto. f_equal; auto.
Qed.

Lemma decl_list_of_def_recursive_nonrec which l:
  (nonrec_of_context
    (rev (decl_list_of_def which false l))) = nil.
Proof.
  unfold decl_list_of_def. rewrite rev_app_distr, nonrec_of_context_app.
  apply app_nil_iff.
  split.
  - simpl. destruct (Pattern.filter_map _ _) as [| h [|h1 t1]]; simpl; auto.
  - simpl.
    induction l as [| h t IH]; simpl; auto.
    destruct (gen_funpred_def_match h) as [b1 [[ls vs] e]] eqn : Hdef.
    apply gen_funpred_def_match_eq in Hdef. subst.
    destruct (which b1 ls); simpl; auto; rewrite nonrec_of_context_app; simpl;
    destruct b1; simpl; rewrite app_nil_r; auto.
Qed.


Lemma decl_list_of_def_nonrec which fd:
  sublist (nonrec_of_context
  (rev (decl_list_of_def which true [fd]))) [fd].
Proof.
  unfold decl_list_of_def. simpl.
  destruct (gen_funpred_def_match fd) as [b1 [[ls vs] e]] eqn : Hdef.
  apply gen_funpred_def_match_eq in Hdef. subst.
  destruct (which b1 ls); simpl; auto; [| apply sublist_refl].
  destruct b1; simpl; auto; apply sublist_nil_l.
Qed.

Lemma gen_new_ctx_gamma_nonrec which nonrec gamma:
  sublist (nonrec_of_context (gen_new_ctx_gamma' which nonrec gamma))
    (nonrec_of_context gamma).
Proof.
  unfold gen_new_ctx_gamma'.
  induction gamma as [| gh gtl IH]; simpl; auto; [apply sublist_refl|].
  rewrite nonrec_of_context_app.
  destruct (is_rec_nonrec gh) as [l|[fd|]] eqn : Hisrec.
  - destruct gh; inversion Hisrec; subst. clear Hisrec.
    rewrite decl_list_of_def_recursive_nonrec. auto.
  - (*nonrec*)
    destruct gh; inversion Hisrec; subst.
    destruct nonrec; simpl; auto; [| apply sublist_cons_l; auto].
    replace (fd :: nonrec_of_context gtl) with ([fd] ++ nonrec_of_context gtl) by reflexivity.
    apply sublist_app2; auto. apply decl_list_of_def_nonrec.
  - (*other*)
    destruct gh; inversion Hisrec; subst; auto.
Qed.

Lemma nonrec_def_of_context d gamma:
  In (nonrec_def d) gamma <-> In d (nonrec_of_context gamma).
Proof.
  induction gamma as [| h t [IH1 IH2]]; simpl; [reflexivity|].
  split.
  - intros [Hh | Hin]; subst; simpl; auto. destruct h; simpl; eauto.
  - destruct h; simpl; auto. intros [Hh | Hind]; subst; auto.
Qed.

(*And the corollary, about concrete funs*)
Lemma gen_new_ctx_fun_defined which nonrec gamma f args body:
  fun_defined (gen_new_ctx_gamma' which nonrec gamma) f args body ->
  fun_defined gamma f args body.
Proof.
  unfold fun_defined.
  intros [[fs [Hinfs inf]] | Hnonrec].
  - assert (Hin1: In (fun_def f args body) (concat (mutfuns_of_context gamma))).
    {
      eapply (gen_new_ctx_gamma_mutfuns which nonrec).
      rewrite in_concat. exists fs; auto. 
    }
    rewrite in_concat in Hin1.
    left; auto.
  - right.
    rewrite nonrec_def_of_context in Hnonrec.
    rewrite nonrec_def_of_context.
    apply gen_new_ctx_gamma_nonrec in Hnonrec. auto.
Qed.

(*preds is identical*)
Lemma gen_new_ctx_pred_defined which nonrec gamma p args body:
  pred_defined (gen_new_ctx_gamma' which nonrec gamma) p args body ->
  pred_defined gamma p args body.
Proof.
  unfold pred_defined.
  intros [[fs [Hinfs inf]] | Hnonrec].
  - assert (Hin1: In (pred_def p args body) (concat (mutfuns_of_context gamma))).
    {
      eapply (gen_new_ctx_gamma_mutfuns which nonrec).
      rewrite in_concat. exists fs; auto. 
    }
    rewrite in_concat in Hin1.
    left; auto.
  - right.
    rewrite nonrec_def_of_context in Hnonrec.
    rewrite nonrec_def_of_context.
    apply gen_new_ctx_gamma_nonrec in Hnonrec. auto.
Qed.

Lemma indpreds_of_decl_list_of_def which nonrec l:
  indpreds_of_context (rev (decl_list_of_def which nonrec l)) = nil.
Proof.
  unfold decl_list_of_def.
  rewrite rev_app_distr, indpreds_of_context_app.
  apply app_nil_iff. split.
  - simpl. destruct (Pattern.filter_map _ _) as [| h1 [|h2 t2]] eqn : Hpat; simpl; auto.
    destruct nonrec; auto.
  - simpl. induction l as [| h t IH]; simpl; auto.
    destruct (gen_funpred_def_match h) as [b1 [[ls vs] e]] eqn : Hdef.
    apply gen_funpred_def_match_eq in Hdef. subst.
    destruct (which b1 ls); simpl; auto.
    rewrite indpreds_of_context_app; simpl. destruct b1; simpl; auto; rewrite app_nil_r; auto.
Qed.

Lemma gen_new_ctx_gamma_indpreds which nonrec gamma:
  indpreds_of_context (gen_new_ctx_gamma' which nonrec gamma) =
  indpreds_of_context gamma.
Proof.
  unfold gen_new_ctx_gamma'.
  induction gamma as [| gh gtl IH]; simpl; auto.
  rewrite indpreds_of_context_app, IH.
  destruct (is_rec_nonrec gh) as [l|[fd|]] eqn : Hisrec.
  - destruct gh; inversion Hisrec; subst. clear Hisrec.
    rewrite indpreds_of_decl_list_of_def. auto.
  - (*nonrec*)
    destruct gh; inversion Hisrec; subst.
    destruct nonrec; simpl; auto.
    rewrite indpreds_of_decl_list_of_def; auto.
  -(*other*)
    destruct gh; inversion Hisrec; subst; auto.
Qed. 

(*And now we prove that if pf is full, so is
  [gen_new_ctx_pf] (not true in the other direction of course -
  recfuns wont necessarily hold)*)
Lemma gen_new_ctx_pf_full which nonrec {gamma} (gamma_valid: valid_context gamma) 
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf):
full_interp gamma_valid pd pf ->
full_interp (gen_new_ctx_valid which nonrec _ gamma_valid) pd 
  (gen_new_ctx_pf which nonrec gamma_valid pd pdf pf).
Proof.
  unfold full_interp; intros [Hfun [Hpred [Hconstr Hleast]]]; split_all.
  - clear -Hfun.
    intros. simpl.
    assert (f_in': fun_defined gamma f args body). {
      apply gen_new_ctx_fun_defined in f_in; auto.
    }
    erewrite (Hfun f args body f_in' srts srts_len a vt vv).
    erewrite tm_gen_new_ctx_pf.
    apply dom_cast_eq.
  - clear -Hpred.
    intros. simpl.
    assert (p_in': pred_defined gamma p args body). {
      apply gen_new_ctx_pred_defined in p_in; auto.
    }
    erewrite (Hpred p args body p_in' srts srts_len a vt vv).
    symmetry.
    apply fmla_gen_new_ctx_pf.
  - clear -Hconstr.
    intros.
    assert (Hin:=l_in).
    rewrite gen_new_ctx_gamma_indpreds in Hin.
    specialize (Hconstr l Hin p fs p_in srts srts_len vt vv f f_in).
    erewrite fmla_rep_irrel.
    erewrite fmla_gen_new_ctx_pf.
    apply Hconstr.
    Unshelve.
    apply (indprop_fmla_valid (gen_new_ctx_valid which nonrec gamma gamma_valid) l_in p_in f_in).
  - clear -Hleast.
    intros.
    assert (Hin:=l_in).
    rewrite gen_new_ctx_gamma_indpreds in Hin.
    specialize (Hleast l Hin p p_in fs srts srts_len a vt vv Ps).
    apply Hleast; auto.
    intros fs1 Hform Hinfs1.
    assert (Hall: Forall (formula_typed (gen_new_ctx_gamma' which nonrec gamma)) fs1).
    {
      revert Hform. rewrite !Forall_forall. intros Hall x Hinx.
      eapply formula_typed_sublist. 3: apply Hall; auto.
      - apply eq_sig_is_sublist, eq_sig_sym, gen_new_ctx_gamma_eq_sig.
      - rewrite gen_new_ctx_gamma_mut; apply sublist_refl. 
    }
    specialize (H fs1 Hall Hinfs1).
    revert H.
    erewrite dep_map_ext. intros Hand; apply Hand.
    intros x y1 y2 Hinx.
    apply fmla_change_gamma_pf; auto.
    + rewrite gen_new_ctx_gamma_mut. reflexivity.
    + intros p1 srts1 a1 Hinp1.
      simpl.
      apply find_apply_pred_ext; auto.
Qed.

Lemma satisfies_gen_new_ctx_pf which nonrec
{gamma} (gamma_valid: valid_context gamma) 
(pd: pi_dom) (pdf: pi_dom_full gamma pd) (pf: pi_funpred gamma_valid pd pdf)
(pf_full: full_interp gamma_valid pd pf)
(pf_full2: full_interp (gen_new_ctx_valid which nonrec _ gamma_valid) pd
  (gen_new_ctx_pf which nonrec gamma_valid pd pdf pf))
(f: formula)
(Hty1: formula_typed gamma f)
(Hty2: formula_typed (gen_new_ctx_gamma' which nonrec gamma) f):
satisfies (gen_new_ctx_valid which nonrec gamma gamma_valid) pd _
  (gen_new_ctx_pf which nonrec gamma_valid pd pdf pf) pf_full2 f
  Hty2 <->
satisfies gamma_valid pd pdf pf pf_full f Hty1.
Proof.
  unfold satisfies. split; intros.
  specialize (H vt vv).
  erewrite fmla_gen_new_ctx_pf in H.
  apply H.
  erewrite fmla_gen_new_ctx_pf. apply H.
Qed.

Lemma gen_new_ctx_sound which nonrec: sound_trans (single_trans (gen_new_ctx which nonrec)).
Proof.
  unfold gen_new_ctx.
  unfold sound_trans, single_trans.
  intros.
  setoid_rewrite gen_new_ctx_gamma_equiv in H.
  simpl in H.
  specialize (H _ ltac:(left; auto)).
  unfold task_valid in *. simpl in *.
  split; auto.
  destruct t as [[gamma delta] goal]; simpl_task.
  destruct H as [Hwf Hval].
  intros.
  specialize (Hval (gen_new_ctx_valid which nonrec _ gamma_valid) Hwf).
  unfold log_conseq in *.
  intros.
  (*Now, need to show that we can convert an interpretation
    for the full context into one of the weakened context*)
  specialize (Hval pd _ (gen_new_ctx_pf which nonrec gamma_valid pd pdf pf)
    (gen_new_ctx_pf_full which nonrec gamma_valid pd pdf pf pf_full)).
  prove_hyp Hval.
  {
    intros d Hd.
    erewrite satisfies_gen_new_ctx_pf. apply H.
    Unshelve. auto.
  }
  erewrite satisfies_gen_new_ctx_pf in Hval.
  apply Hval.
Qed.

Lemma typed_gen_new_ctx which nonrec t:
  task_wf t -> task_wf (gen_new_ctx which nonrec t).
Proof.
  destruct t as [[gamma delta] goal].
  intros Hwf.
  inversion Hwf. simpl_task.
  pose proof (gen_new_ctx_valid which nonrec _ task_gamma_valid) as Hval.
  unfold gen_new_ctx. rewrite gen_new_ctx_gamma_equiv. simpl_task.
  constructor; simpl_task; auto.
  - revert task_delta_typed.
    apply Forall_impl.
    intros f. apply formula_typed_sublist.
    + apply eq_sig_is_sublist. apply eq_sig_sym. 
      apply gen_new_ctx_gamma_eq_sig.
    + rewrite gen_new_ctx_gamma_mut. apply sublist_refl.
  - inversion task_goal_typed. constructor; auto.
    revert f_ty. apply formula_typed_sublist.
    + apply eq_sig_is_sublist. apply eq_sig_sym. 
      apply gen_new_ctx_gamma_eq_sig.
    + rewrite gen_new_ctx_gamma_mut. apply sublist_refl.
Qed.


(*1 final result: [gen_axioms] produces well-formed goals.
  We essentially proved this with [gen_axioms_typed]*)
Lemma gen_axioms_wf which nonrec: forall t, task_wf t -> task_wf (gen_axioms which nonrec t).
Proof.
  intros. destruct t as [[gamma delta] goal];
  unfold gen_axioms, add_axioms; simpl_task.
  inversion H. constructor; simpl_task; auto.
  (*We already proved typing*) 
  rewrite !map_app.
  rewrite Forall_app. split; auto.
  rewrite Forall_forall.
  apply (gen_axioms_typed which nonrec (gamma, delta, goal)). auto.
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
  - (*Soundness of axioms*) apply gen_axioms_sound.
  - (*Well-typed context*) apply gen_new_ctx_sound.
  - (*All axioms are well-formed*) 
    unfold typed_single_trans. apply gen_axioms_wf.
Qed.

Theorem eliminate_definition_gen_typed which nonrec:
  typed_trans (eliminate_definition_gen which nonrec).
Proof.
  rewrite typed_trans_ext.
  2: apply eliminate_definition_split.
  unfold eliminate_definition_alt.
  apply compose_single_trans_typed.
  - unfold typed_single_trans.
    apply gen_axioms_wf.
  - unfold typed_single_trans.
    apply typed_gen_new_ctx.
Qed.

End Proofs.