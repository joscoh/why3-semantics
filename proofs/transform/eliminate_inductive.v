(*Axiomatizes inductive predicates*)
Require Import Task.
(*We keep this as close as possible to the why3 version, only changes
  1. don't (yet) simplify formulas
  2. we add assumptions in delta rather than gamma, why3 only has
    1 context. But the meaning is the same*)

(*Put our [ind_def] in the same form as their [ind_decl]*)
Definition get_ind_data (i: indpred_def) : predsym * list (string * formula) :=
  match i with
  | ind_def p l => (p, l)
  end.


Definition create_param_decl (p: predsym) : def :=
  abs_pred p.

Definition log {A: Type} acc (x: predsym * A) :=
  create_param_decl (fst x) :: acc.
(*For us, not a decl, just a list of named formulas*)
Definition axm acc (x: string * formula) : list (string * formula) :=
  x :: acc.
Definition imp {A: Type} acc (x: A * (list (string * formula))) :=
  fold_left axm (snd x) acc.

(*Simplify and formulas - TODO; prove semantically
  equivalent to and*)
Definition t_and_simp f1 f2 :=
  match f1, f2 with
  | Ftrue, _ => f2
  | _, Ftrue => f1
  | Ffalse, _ => f1
  | _, Ffalse => f2
  | _, _ => if formula_eq_dec f1 f2 then f1 else
    Fbinop Tand f1 f2
  end.

Fixpoint fold_left2 {A B C: Type}
  (f: A -> B -> C -> A) (accu: A) (l1: list B) (l2: list C) : A :=
  match l1, l2 with
  | a1 :: l1, a2 :: l2 => fold_left2 f (f accu a1 a2) l1 l2
  | _, _ => accu
  end.

(*TODO: move*)
Lemma fold_left2_combine  {A B C: Type} (f: A -> B -> C -> A)
  acc l1 l2:
  fold_left2 f acc l1 l2 =
  fold_left (fun x y => f x (fst y) (snd y)) (combine l1 l2) acc.
Proof.
  revert acc. revert l2. induction l1; simpl; intros; auto.
  destruct l2; simpl; auto.
Qed.

(*We do not use nested recursion to make proving easier*)
(*This function takes in a list of terms, all of which
  are Tvar _ and a formula, and it produces the
  inversion formula for a single constructor.
  For example: the constructor
  even_S: forall n, even n -> even (S (S n))
  and variable y produce the formula
  (exists n, even n /\ y = S (S n))
  *)
Fixpoint descend (vs: list term) (f: formula) :=
  match f with
  | Fquant Tforall x f => 
    (*Only difference is in how we handle binders
      TODO: need to handle the case when a variable is
      in the arguments is bound here - do alpha renaming before?*)
    Fquant Texists x (descend vs f)
  | Fbinop Timplies g f =>
    Fbinop Tand g (descend vs f)
  | Fpred p tys tms =>
    (*We need an additional parameter for the types*)
    let marry acc v x := t_and_simp acc (Feq (fst x) v (snd x)) in
    fold_left2 marry Ftrue vs (combine 
      (*The types map is a bit complicated - they do
        typechecking on the fly*)
      (map (ty_subst (s_params p) tys) (s_args p)) tms)
  | Flet t v f => Flet t v (descend vs f)
  | _ => f (*cannot be reached*)
  end.
Definition exi {A: Type} (vs: list term) (x: A * formula) :=
  descend vs (snd x).

Require Import GenElts.

(*A bit different - we make sure names do not clash*)
Definition create_vsymbols (avoid: list vsymbol) (tys: list vty) : 
  list vsymbol :=
  combine (gen_strs (length tys) avoid) tys.

(*This is a partial function in why3, we give a default val here*)
Definition map_join_left {A B: Type} (d: B) (map: A -> B) (join: B -> B -> B) 
  (l: list A) : B :=
  match l with
  | x :: xl => fold_left (fun acc x => join acc (map x)) xl (map x)
  | _ => d
  end.

Definition t_or (f1 f2: formula) := Fbinop Tor f1 f2.

(*Generate the entire inversion axiom - the why3 version includes
  the cons in [inv] (below), but it is easier to reason
  about this independently*)
Definition inv_aux {A: Type}
  (x: predsym * list (A * formula)) :
  (string * formula) :=
  let ps := fst x in
  let al := snd x in
  (*Create vsymbols for the predicate's arguments - we use
    [gen_strs] to avoid clashing with variables defined already*)
  let vl := create_vsymbols (concat (map fmla_bnd (map snd al))) 
    (s_args ps) in
  (*make these terms (TODO: maybe do in function instead?)*)
  let tl := map Tvar vl in
  (*Create the predsym applied to these arguments
    NOTE: since the vsymbols we created were based on the 
    predsym's args, this must be polymorphic *)
  let hd := Fpred ps (map vty_var (s_params ps)) tl in
  (*Get the disjunction of the all of the inversion 
    cases given above
    Ex: even gives: (y = 0 \/ exists n, even n /\ y = S (S n))*)
  let dj := map_join_left Ftrue (exi tl) t_or al in
  (*NOTE: we do not yet simplify by removing quantifiers*)
  let hsdj := dj in
  (*Then make this forall y, ...*)
  let ax := fforalls vl hsdj in
  (*Create the name for the inversion axiom*)
  let nm := ((s_name ps) ++ "_inversion"%string)%string in
  (*Put it all together*)
  (nm, ax).

  Definition inv {A: Type} (acc: list (string * formula)) 
  (x: predsym * list (A * formula)) :=
  inv_aux x :: acc.

(*Create the new definitions and axioms*)
Definition elim (d: def) : list def * list (string * formula) :=
  match d with
  | inductive_def il =>
    (*Get in the same form as why3: tuples instead of ind_def*)
    let il' := map get_ind_data il in
    (*Create abstract predicate defs for inductive predicates here -
      a bit clunky compared to theirs because we don't use tuples*)
    let dl1 := fold_left log il' nil in
    (*Create constructor axioms*)
    let dl2 := fold_left imp il' nil in
    (*Create inversion axioms - most interesting part*)
    let dl3 := fold_left inv il' dl2 in
    (*TODO: they reverse the list, do we need to?*)
    (dl1, rev dl3)
  | _ => ([d], nil)
  end.

(*trans_decl is like "flat_map" - go through
  context of task, for each, get additional things to add
  to gamma and delta - add them all*)
(*We just build up the new gamma and delta*)
(*This differs a bit from why3's implementation
  TODO: maybe change a bit*)
Definition trans_decl (f: def -> list def * list (string * formula)) 
  (t: task) : task :=
  let (g, d) :=
  List.fold_left (fun acc x =>
    let (g, d) := f x in
    let t := acc in
    (g ++ fst t, d ++ snd t)
  ) (task_gamma t) (nil, nil) in
  mk_task (List.rev g) (List.rev d ++ task_delta t) (task_goal t).

Definition eliminate_inductive : trans :=
  fun t => [trans_decl elim t].

(*Proofs*)

(*Step 1: Reasoning about gamma and delta together is hard.
  We can compose this into 2 separate transformations and
  prove each one sound independently*)

(*So we give an alternate, though equivalent, version that
  is easier to reason about*)

(*We consider the transformation as acting on each
  individual indprop separately, then combining at the end*)
Print imp.
Check inv_aux.
(*We use map instead of fold_left*)
Definition build_ind_axioms (il: list indpred_def) :
  list (string * formula) :=
  let il' := map get_ind_data il in
  let dl2 := concat (map snd il') in
  let addl := map inv_aux il' in
  dl2 ++ addl.

Definition get_indpred_defs (il: list indpred_def) : list def :=
  let il' := map get_ind_data il in
  map (fun x => create_param_decl (fst x)) il'.

(*We have two transformations: one that generates axioms, one that
  changes gamma*)
Definition gen_axioms (t: task) : task :=
  let new_d :=
  concat (map (fun x =>
    match x with
    | inductive_def il => rev (build_ind_axioms il)
    | _ => []
    end) (task_gamma t)) in
  mk_task (task_gamma t) (new_d ++ task_delta t) (task_goal t).

Definition gen_new_ctx (t: task) : task :=
  let new_g :=
  concat (map (fun x =>
    match x with
    | inductive_def il => get_indpred_defs il
    | _ => [x]
    end) (task_gamma t)) in
  mk_task new_g (task_delta t) (task_goal t).

Definition compose_single_trans (f1 f2: task -> task) :=
  single_trans (fun x => f2 (f1 x)).

(*TODO: should this be a part? maybe organize a bit differently?*)

(*This decomposition is justified in the following lemma:*)
Lemma compose_single_trans_sound f1 f2:
  sound_trans (single_trans f1) ->
  sound_trans (single_trans f2) ->
  (*TODO: really not great*)
  (forall x, task_wf x -> task_wf (f1 x)) ->
  sound_trans (compose_single_trans f1 f2).
Proof.
  unfold sound_trans, compose_single_trans, single_trans. 
  intros. simpl in *.
  apply H; auto. intros t2 [Heq | []]; subst.
  apply H0; auto.
Qed.

Definition eliminate_inductive_alt : trans :=
  compose_single_trans gen_axioms gen_new_ctx.

(*Prove equivalence*)
Set Bullet Behavior "Strict Subproofs".

Check concat.

Lemma rev_app {A: Type} (l1 l2: list A):
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  revert l2; induction l1; simpl; intros; auto.
  rewrite app_nil_r; auto.
  rewrite IHl1, app_assoc; auto.
Qed.

(*Lemma concat_rev {A: Type} (l: list (list A)):
  concat (rev l) = rev (concat l).
Proof.
  induction l; simpl; auto.
  rewrite concat_app, rev_app, IHl; simpl.
  Search rev app. rev_app.*)

(*Prove the smaller equivalences: get_indpred_defs and 
  get_indpred_axioms
  *)
Lemma get_indpred_defs_eq (il: list indpred_def) :
  get_indpred_defs il = 
  rev (fst (elim (inductive_def il))).
Proof.
  unfold get_indpred_defs, elim; simpl.
  rewrite <- fold_left_rev_right.
  rewrite <- (rev_involutive (map get_ind_data il)) at 1.
  rewrite map_rev. (*Coq is smart*) reflexivity.
Qed.

Lemma axm_rev acc l:
  fold_left axm l acc = rev l ++ acc.
Proof.
  revert acc. induction l; simpl; intros; auto.
  rewrite IHl, <- app_assoc. reflexivity.
Qed.

(*Awkward: igives [l1, l2, l3], gives rev l3 ++ rev l2 ++ rev l1 *)
Lemma fold_imp_eq {A: Type} (acc: list (A * list (string * formula)))
   base:
  fold_left imp acc base = concat (rev (map (fun x => rev (snd x)) acc)) ++ base.
Proof.
  revert base. induction acc; simpl; intros; auto.
  rewrite IHacc. unfold imp. rewrite axm_rev.
  rewrite !app_assoc. f_equal.
  rewrite concat_app. simpl. rewrite app_nil_r. 
  reflexivity.
Qed.

Lemma fold_inv_eq {A: Type} (acc: list (predsym * list (A * formula))) 
base:
  fold_left inv acc base = rev (map inv_aux acc) ++ base.
Proof.
  revert base. induction acc; simpl; intros; auto.
  rewrite IHacc. unfold inv.
  rewrite <- app_assoc. reflexivity.
Qed. 

(*All the awful rev and concat stuff goes away*)
Lemma build_ind_axioms_eq il:
  build_ind_axioms il =
  snd (elim (inductive_def il)).
Proof.
  unfold build_ind_axioms; simpl.
  rewrite fold_imp_eq, fold_inv_eq.
  rewrite rev_app, rev_involutive.
  f_equal.
  rewrite app_nil_r.
  induction (map get_ind_data il); simpl; auto.
  rewrite concat_app, rev_app; simpl.
  rewrite IHl, app_nil_r, rev_involutive.
  reflexivity.
Qed.

Lemma eliminate_inductive_split: forall t,
  eliminate_inductive t =
  eliminate_inductive_alt t.
Proof.
  intros. unfold eliminate_inductive, eliminate_inductive_alt,
  compose_single_trans, single_trans.
  f_equal.
  unfold trans_decl, gen_new_ctx, gen_axioms.
  destruct t as [[gamma delta] goal]; simpl_task.
  rewrite (surjective_pairing (fold_left
  (fun (acc : list def * list (string * formula)) (x : def) =>
   let (g, d) := elim x in (g ++ fst acc, d ++ snd acc)) gamma (
  [], []))); simpl. f_equal. f_equal.
  - (*Prove gamma equivalent*)
    (*Eliminate fold_left*)
    rewrite <- fold_left_rev_right.
    rewrite <- (rev_involutive gamma) at 2.
    rewrite map_rev.
    induction (rev gamma); simpl; auto.
    rewrite (surjective_pairing (elim a)); simpl.
    rewrite rev_app.
    destruct a; simpl; try rewrite IHl, concat_app; auto.
    rewrite get_indpred_defs_eq; simpl; rewrite app_nil_r; auto.
  - (*Prove delta part*)
    f_equal. rewrite <- fold_left_rev_right.
    rewrite <- (rev_involutive gamma) at 2.
    rewrite map_rev.
    induction (rev gamma); simpl; auto.
    rewrite (surjective_pairing (elim a)); simpl.
    destruct a; simpl; try rewrite concat_app; simpl;
    try rewrite IHl, app_nil_r; auto.
    rewrite build_ind_axioms_eq. simpl.
    rewrite rev_app, IHl, app_nil_r.
    reflexivity.
Qed. 

(*Part 2: Prove that the axioms are correct*)

(*First, a version of the deduction theorem:
  it suffices to show that all of the axioms we add to delta
  are implied by delta*)
