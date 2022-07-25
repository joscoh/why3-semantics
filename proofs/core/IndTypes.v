Require Import Syntax.
Require Import Typing.
Require Import Types.

Inductive W (A: Set) (B: A -> Set) : Set :=
  mkW : forall (a: A) (f: B a -> W A B), W A B.

Inductive empty :=.

(*Ex: for nats*)
Definition wnat := W bool (fun b => if b then unit else empty).
Definition w0 : wnat.
apply mkW with (a:=false).
intro C. destruct C.
Defined.

Definition wS (n: wnat): wnat.
apply mkW with (a:=true).
intro C. apply n.
Defined.

(*Let's try list*)
Definition wlist (A: Set) := W (option A) (fun b => match b with | None => empty | Some a => unit end).

Definition wnil (A: Set) : wlist A.
Proof.
  apply mkW with (a:=None).
  intro C. destruct C.
Defined.

Definition wcons (A: Set) (x: A) (tl: wlist A) :=
  mkW  _ _ (Some x) (fun _ => tl).

(*Let's do binary trees*)

Inductive tree (A: Set) : Set :=
  | leaf
  | node : A -> tree A -> tree A -> tree A.

Definition wtree (A: Set) := W (option A) (fun x =>
  match x with |None => empty | Some a => bool end).

Definition wleaf (A: Set) : wtree A.
apply mkW with (a:=None).
intro C. destruct C.
Defined.

Definition wnode (A: Set) (x: A) (lt: wtree A) (rt: wtree A) :=
  mkW (option A) (fun x =>
  match x with |None => empty | Some a => bool end) (Some x) 
  (fun b => if b then lt else rt).

(*Let's test this*)
Inductive foo (A: Set) :=
  mkfoo : A -> (nat -> foo A) -> foo A.

Definition wfoo (A: Set) := W A (fun _ => nat).

Definition wmkfoo (A: Set) (x: A) (f: nat -> wfoo A) : wfoo A.
apply mkW with (a:=x). apply f.
Defined.

(*Now here is the problem - we dont know how many constructors there are*)
(*for list: 1, for tree: 2, for above: infinite
but what about when there is some value of constructors that we don't know?
existential?*)

(*Type of cardinality n*)
Definition bound (n: nat) : Set := {x : nat | x < n}.

(*We can solve our problem by changing the base type A to take in
  the number of constructors as well, then choose a type that
  has that number of constructors*)

  (*Here is rose tree:*)
Definition wrose (A: Set) := W (A * nat) (fun x => bound (snd x)).
Require Import Coq.Lists.List.
Definition wrnode (A: Set) (x: A) (l: list (wrose A)) : wrose A.
Proof.
  apply mkW with (a:=(x, (length l))).
  simpl. intros Hb.
  destruct Hb.
  destruct (nth_error l x0) eqn : Hnth.
  - apply w.
  - apply nth_error_Some in l0. rewrite Hnth in l0. contradiction.
Defined.

(*Problem: we would need a version of nth for wlist as well*)
(*Basically, we can see these nested inductives as containers,
  so we need 3 things:
  1. Definition of size of container
  2. Function pick: nat -> elt of container (or option)
  3. Proof that if n < size c, then pick n = Some x
  Can this be done automatically? maybe not
  For now, do simple ADTS
  *)

(*Let's do either*)
Inductive either (A B: Set) : Set :=
  | Left: A -> either A B
  | Right: B -> either A B.

(*Ok, let's try*)
(*For first pass, suppose it only includes base types (int and real), type variables,
  and inductive definitions for current typesym
  then, see if we can add abstract types (maybe parameterized? - how to do?)
  Tests will be
  - unit, bool, type with small finite number
  - nat, list, either, option
  - tree, many constructor, more exotic types
*)

(*let's do some simple easy ones*)
Definition wunit := W unit (fun _ => empty).

Definition wtt : wunit := mkW _ _ tt (fun (e: empty) => match e with end).

Definition wbool := W bool (fun _ => empty).

Definition wtrue : wbool := mkW _ _ true (fun (e: empty) => match e with end).

Definition wfalse : wbool := mkW _ _ false (fun (e: empty) => match e with end).

(*Trying to see best finite encoding*)
Fixpoint finite (n: nat) : Set :=
  match n with
  | O => unit
  | S n' => option (finite n')
  end.

Fixpoint fin_list (n: nat) : list (finite n).
induction n.
- apply [tt].
- destruct n.
  + apply [Some tt; None].
  + apply (None :: map Some IHn).
Defined.

Lemma fin_list_all: forall (n: nat) (x: finite n),
  In x (fin_list n).
Proof.
  induction n; simpl; intros.
  - destruct x. left; auto.
  - destruct n.
    + simpl in x. destruct x.
      * destruct u. left; auto.
      * right; left; auto.
    + destruct x. 2: left; auto.
      right. rewrite in_map_iff. exists f. split; auto.
Qed.

Lemma NoDup_map_inj: forall {A B: Type} (f: A -> B) (l: list A),
  (forall x y, f x = f y -> x = y) ->
  NoDup l ->
  NoDup (map f l).
Proof.
  intros; induction l; simpl. constructor.
  inversion H0; subst.
  constructor.
  - rewrite in_map_iff. intros [x [Hx Hinx]].
    apply H in Hx. subst. contradiction.
  - auto.
Qed.

Lemma fin_list_nodup: forall (n: nat),
  NoDup (fin_list n).
Proof.
  induction n; simpl.
  - constructor. intro C; inversion C. constructor.
  - destruct n.
    + repeat (constructor; auto; try (intro C; inversion C; inversion H)).
    + constructor.
      * intro C. rewrite in_map_iff in C. destruct C as [o [Hcon _]]. inversion Hcon.
      * apply NoDup_map_inj. intros x y Hxy; auto. inversion Hxy; auto.
        apply IHn.
Qed. 

Definition plus (A B: Set) : Set := either A B.

Definition mult (A B: Set) : Set := (A * B).

Definition emp_fun {A: Type} : empty -> A := (fun (e: empty) => match e with end).


Definition wunit' := W (finite 0) (fun _ => empty).

Definition wtt' : wunit' := mkW _ _ tt emp_fun. 

Definition wbool' := W (finite 1) (fun _ => empty).

Definition wtrue' : wbool' := mkW _ _ (Some tt) emp_fun.

Definition wweek := W (finite 6) (fun _ => empty).

Definition wmonday : wweek := mkW _ _ None emp_fun.
Definition wtuesday: wweek := mkW _ _ (Some None) emp_fun.
Definition wwednesday: wweek := mkW _ _ (Some (Some None)) emp_fun.
Definition wthursday: wweek := mkW _ _ (Some (Some (Some None))) emp_fun.
Definition wfriday: wweek := mkW _ _ (Some (Some (Some (Some None)))) emp_fun.
Definition wsaturday: wweek := mkW _ _ (Some (Some (Some (Some (Some None))))) emp_fun.
Definition wsunday: wweek:= mkW _ _ (Some (Some (Some (Some (Some (Some tt)))))) emp_fun.

(*First, trivial one for easy types*)
Definition mk_adt (ts: typesym) (constrs: list funsym) : Set :=
  let fintype := finite ((length constrs) - 1) in
  W fintype (fun _ => empty).

(*This will be more complicated later*)
Definition constr_rep (ts: typesym) (constrs: list funsym) :
  list (funsym * (mk_adt ts constrs)).
Proof.
  apply (combine constrs 
    (map (fun f => mkW _ _ f emp_fun) (fin_list (length constrs - 1)))).
Defined.

Section Tests.

Notation mk_fs name params args ret_ts ret_args := 
  (Build_funsym name params args (vty_cons ret_ts ret_args) eq_refl eq_refl eq_refl).

Definition find {A B: Type} (eq_dec: forall (x y : A), {x = y} + {x <> y}) 
  (l: list (A * B)) (x: A) : option B :=
  fold_right (fun y acc => if eq_dec (fst y) x then Some (snd y) else acc) None l.

Notation find_constr ts constrs x :=
  (find funsym_eq_dec (constr_rep ts constrs) x). 

(*Unit*)
Definition ts_unit : typesym := mk_ts "unit" nil eq_refl.
Definition aunit := mk_adt ts_unit 
  [ mk_fs "tt" nil nil ts_unit nil].

Lemma aunit_correct: aunit = W unit (fun _ => empty).
Proof. reflexivity. Qed.

Eval compute in find_constr ts_unit [ mk_fs "tt" nil nil ts_unit nil]
  (mk_fs "tt" nil nil ts_unit nil).

Eval compute in string_dec "a" "b".

Definition ta : typevar := "a"%string.
Definition tb : typevar := "b"%string.
(*
Eval vm_compute in vty_eq_dec (vty_var ta) (vty_var tb).

Eval compute in vty_eq_dec (vty_var "a") (vty_var "b").
*)
  Eval compute in (funsym_eq_dec (mk_fs "tt" nil nil ts_unit nil) (mk_fs "tt" nil nil ts_unit nil) ).

(*TODO: try with ssreflect to see if we can get that stuff computes
  easier and faster*)

Eval compute in (map snd (constr_rep   ts_unit [ mk_fs "tt" nil nil ts_unit nil])).
  
  
  =
  Some (mkW _ _ None emp_fun).

(*Bool*)
Definition ts_bool : typesym := mk_ts "bool" nil eq_refl.
Definition abool := mk_adt ts_bool
  [mk_fs "true" nil nil ts_bool nil;
   mk_fs "false" nil nil ts_bool nil].

Lemma abool_correct: abool = W (option unit) (fun _ => empty).
Proof. reflexivity. Qed.

(*Days of the week*)
Definition ts_week : typesym := mk_ts "days" nil eq_refl.
Definition aweek := mk_adt ts_week
  [mk_fs "mon" nil nil ts_week nil;
   mk_fs "tues" nil nil ts_week nil;
   mk_fs "wed" nil nil ts_week nil;
   mk_fs "thurs" nil nil ts_week nil;
   mk_fs "fri" nil nil ts_week nil;
   mk_fs "sat" nil nil ts_week nil;
   mk_fs "sun" nil nil ts_week nil].

Lemma aweek_correct: aweek = 
  W (option (option (option (option (option (option unit)))))) (fun _ => empty).
Proof. reflexivity. Qed.



  reflexivity.
Qed.
Eval compute in aunit.



Definition mk_adt (ts: typesym) (constrs: list funsym) : Set :=
  let 


Definition weither (A: Set) (B: Set) := W 

  (*
Definition wrnode' (A: Set) (x: A) (l: wlist (wrose A)) : wrose A.*)
Proof.
  apply mkW with 

(*What about the following?*)
Inductive bar (A: Set) : Set :=
  | mkbar: A -> tree 

(*I think we can use this more generally with bounded types*)

(*Here is what we need:
  our type must be "sum" of all constructors

  for each constructor
  1. get non-inductive arguments, cardinalities  (TODO: need to figure out opaque types - can these appear)
      should be base type or type variable - this will contribute to A (will be sum of all)
  2. the function will be a match on the argument, which will have a case for each
  constructor, for each match,
  for all inductive arguments of the same type, we add 1 (and just iterate through in order)
  (NOTE: has to be uniform)
  
  then, need to figure out inductives of different type (if different type
  and default args, then can just roll that into (1), but need size)

  hmm, will be complicated - let's start after, build up
  see if we can do one with tree of these types (and maybe non-uniform)
  what does it even mean to have a tree there?

      2. get inductive arguments of same inductive type, 



    if single constructor, 
*)

  Search nth_error.
  apply (mkW) with (a:=x). intros h. destruct h.

(*Let's do a rose tree variant*)
Inductive weirdrose (A: Set) :=
  weirdnode : A -> (nat -> option (weirdrose A)) -> weirdrose A.

Definition wwrose (A: Set) := W A (fun _ => option nat).

Definition wwnode (A: Set) (x: A) (f: nat -> option (wwrose A)): wwrose A.
apply (mkW) with (a:=x).
intros o.
destruct o.
apply f in n. destruct n.
apply w.

apply f.



(*Let's try rose trees*)

Inductive rose (A: Set) :=
  root : A -> list (rose A) -> rose A.

Definition wrose (A: Set) := W A (fun x => nat).

Definition wroot (A: Set) (x: A) (l: wlist (wrose A)) : wrose A.
apply mkW with (a:=x).
intros n.

:=
  mkW A (fun _ => nat) x
  (fun (n: nat) => if n <? length l then nth n l else )
*)

if b then A else empty).

Definition wnil (A: Set) : wlist A.
Proof.
  apply mkW with (a:=false).
  intro C. destruct C.
Defined.

Definition wcons (A: Set) (x: A) (tl: wlist A) : wlist A :=
  mkW true (fun )



(f:= fun _ => n).

  fun w => mkW true (fun n =>)

inversion C.
:= mkW false

inductive W (A : Set) (B : A -> Set) : Set :=

MkW : forall (a : A) (f : B a -> W A B), W A B.