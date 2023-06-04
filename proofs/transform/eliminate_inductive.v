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
  Print formula_typed.
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

(*Generate the entire inversion axiom*)
(*TODO: prob take acc out and do separately*)
Definition inv {A: Type} (acc: list (string * formula)) 
  (x: predsym * list (A * formula)) :
  list (string * formula) :=
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
  (nm, ax) :: acc.

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
    (dl1, dl3)
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
  mk_task (List.rev g) (task_delta t ++ List.rev d) (task_goal t).

Definition eliminate_inductive : trans :=
  fun t => [trans_decl elim t].

