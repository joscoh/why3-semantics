Require Export Coq.Lists.List.
Require Export Coq.Bool.Bool.
Require Export Coq.Logic.Eqdep_dec.
From mathcomp Require all_ssreflect.

Coercion proj_sumbool (A B: Prop) (H: {A} + {B}) : bool :=
  if H then true else false.
Coercion is_true : bool >-> Sortclass.

Lemma is_false {P: Type}: false -> P.
Proof.
discriminate.
Qed.

Lemma bool_irrelevance (b: bool) (p1 p2: b): p1 = p2.
Proof.
  apply UIP_dec, bool_dec.
Qed.

(*Boolean-valued version of [in], not [in_dec]*)
Section Inb.

Context {T: Type}.
Variable (T_dec: forall (x y: T), {x = y} + {x <> y}).

Definition inb (x: T) (l: list T) : bool :=
  fold_right (fun y acc => ((T_dec x y) || acc)) false l.

Lemma inb_spec (x: T) (l: list T): reflect (In x l) (inb x l).
Proof.
  induction l; simpl.
  - apply ReflectF; auto.
  - apply ssr.ssrbool.orPP; auto.
    destruct (T_dec x a); subst; simpl;
    [apply ReflectT | apply ReflectF]; auto.
Qed.

End Inb.