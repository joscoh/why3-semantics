Require Export Coq.Strings.String.
Require Export Coq.ZArith.BinInt.
Require Export Coq.Arith.PeanoNat.
Require Export Coq.Lists.List.
Export ListNotations.

(*Type variable (ex: a)*)
Definition typevar : Type := string. 

Definition typevar_eq_dec : forall (t1 t2: typevar),
  {t1 = t2} + {t1 <> t2} := string_dec.

(*Type symbol (ex: list a)*)
Record typesym : Type := mk_ts {
  ts_name : string;
  ts_arity: nat
  }.

Lemma typesym_eq_dec: forall (t1 t2: typesym),
  {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality. apply Nat.eq_dec. apply string_dec.
Defined.

(*Value types*)
Inductive vty : Type :=
  | vty_int : vty
  | vty_real : vty
  (*| vty_bool : vty
  | vty_func: vty -> vty -> vty
  | vty_pred: vty -> vty*)
  (*| vty_tuple: vty -> vty -> vty*)
  | vty_var: typevar -> vty
  | vty_cons: typesym -> list vty -> vty. (*TODO: do we need this? Can we make it non-list?*)

Definition vty_eq_dec: forall (v1 v2: vty), {v1 = v2} + {v1 <> v2}.
Admitted.
(*TODO: need better induction*)

(*Type substitution (assign meaning to a type variables)*)
Fixpoint ty_subst_single (v: typevar) (t: vty) (expr: vty) : vty :=
  match expr with
  | vty_int => vty_int
  | vty_real => vty_real
  | vty_var tv => if typevar_eq_dec v tv then t else vty_var tv
  | vty_cons ts typs =>
      vty_cons ts (map (ty_subst_single v t) typs)
  end.

(*Substitute a list of typevars*)
Definition ty_subst (vs: list typevar) (ts: list vty) (expr: vty) : vty :=
  fold_right (fun x acc => ty_subst_single (fst x) (snd x) acc) expr (combine vs ts).

Definition ty_subst_list (vs: list typevar) (ts: list vty) (exprs: list vty) : list vty :=
  map (ty_subst vs ts) exprs.

(* Sorts *)

(*Get the type variables in a type. There may be duplicates, but that is fine*)
Fixpoint type_vars (t: vty) : list typevar :=
  match t with
  | vty_int => nil
  | vty_real => nil
  | vty_var v => [v]
  | vty_cons sym ts => fold_right (fun x acc => type_vars x ++ acc) nil ts
  end.
  
Definition is_sort (t: vty) : bool :=
  match (type_vars t) with
  | nil => true
  | _ => false
  end.

Definition sort : Type := {t: vty | is_true (is_sort t)}.
(*TODO: see if we need an alternate definition*)

Lemma int_is_sort: is_true (is_sort vty_int).
Proof.
  unfold is_sort; simpl. auto.
Qed.

Definition s_int : sort := exist _ vty_int int_is_sort.

Lemma real_is_sort: is_true (is_sort vty_real).
Proof.
  unfold is_sort; simpl. auto.
Qed.

Definition s_real : sort := exist _ vty_real real_is_sort.

Definition sublist {A: Type} (l1 l2: list A) : Prop :=
    forall x, In x l1 -> In x l2.

(*We want to know that when we substitute in sorts for type variables,
  the result is a sort *)
(*TODO: this - after we have better induction principle for types*)