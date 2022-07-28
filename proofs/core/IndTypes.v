Require Import Syntax.
Require Import Typing.
Require Import Types.
Require Import Coq.Lists.List.

From mathcomp Require all_ssreflect.
Set Bullet Behavior "Strict Subproofs".

Inductive rose (A: Set) : Set :=
  | Node : A -> list (rose A) -> rose A.

Inductive perfect (A : Set) : Set :=
  | Two : perfect (A * A) -> perfect A
  | One: A -> perfect A.
(*
Section W.

Variable (I: Set).
Variable (A: I -> Set).
Variable (B: forall (i: I) (j: I), A i -> Set).

Inductive IW : I -> Set :=
  | mkW : forall (i: I) (a: A i) (f: forall j, B i j a -> IW j), IW i.

End W.
*)
Inductive W (A: Set) (B: A -> Set) : Set :=
  mkW : forall (a: A) (f: B a -> W A B), W A B.

Inductive empty :=.

(*Some manual tests (will delete)*)
Section Manual.

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

(*let's do some simple easy ones*)
Definition wunit := W unit (fun _ => empty).

Definition wtt : wunit := mkW _ _ tt (fun (e: empty) => match e with end).

Definition wbool := W bool (fun _ => empty).

Definition wtrue : wbool := mkW _ _ true (fun (e: empty) => match e with end).

Definition wfalse : wbool := mkW _ _ false (fun (e: empty) => match e with end).

End Manual.

(*Some facilities for building up types:*)
Section TypeOps.

(*A type with (A + B) elements*)
Inductive either (A B: Set) : Set :=
  | Left: A -> either A B
  | Right: B -> either A B.

(*A type with n elements, for finite n*)
Fixpoint finite (n: nat) : Set :=
  match n with
  | O => empty
  | S O => unit
  | S n' => option (finite n')
  end.

Fixpoint fin_list (n: nat) : list (finite n).
induction n.
- apply nil. 
- destruct n; simpl.
  + apply [tt].
  + destruct n.
    * apply [None; Some tt].
    * apply (None :: map Some IHn).
Defined.
(*TODO: see if we need these lemmas*)
(*
Lemma fin_list_all: forall (n: nat) (x: finite n),
  In x (fin_list n).
Proof.
  induction n; simpl; intros.
  - destruct x.
  - destruct n.
  - destruct x; left; auto.
  - destruct n.
    + simpl in x. destruct x.
      * destruct u. right; left; auto.
      * left; auto.
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
Qed. *)

(*Operations on types*)

(*Addition*)
Definition plus (A B: Set) : Set := either A B.

(*Multiplication*)
Definition mult (A B: Set) : Set := (A * B).

End TypeOps.

(*Now, we come to the construction. We do this in 3 parts:
  1. Build up the base type (A)
  2. Build up the function (A -> Set)
  3. Put together*)
Section ADTConstr.

Import all_ssreflect.

Variable vars: typevar -> Set.
(*Variable abstract: typesym -> *)

(*Construct the base type*)

Definition get_vty_base (v: vty) : option Set :=
  match v with
  | vty_int => Some Z
  | vty_real => Some R
  | vty_var x => Some (vars x) (*TODO: this *) (*(fun (A: Set) => A)*)
  | vty_cons ts vs => None (*for now*)
  end.

Definition sprod (A B: Set) : Set := A * B.

(*TODO: try to get rid of extra: (_ * unit) - this is ok because
  we multiply by 0, but it makes things messier*)

(*A function to take a list of sets and create the product of all of them.
  The naive way gives lots of extra (_ * unit) *)
Definition big_sprod (l: list (option Set)) : Set :=
  let o := fold_right (fun v acc =>
    match v, acc with
    | Some t, Some t' => Some (sprod t t')
    | None, x => x
    | x, _ => x
    end) None l in
  match o with
  | Some t => t
  | None => unit
  end.

Definition build_vty_base (l: list vty) : Set :=
  big_sprod (map get_vty_base l).

Definition build_constr_base (c: funsym) : Set :=
  build_vty_base (s_args c).

Fixpoint build_base (constrs: list funsym) : Set :=
  match constrs with
  | [f] => build_constr_base f
  | f :: fs => either (build_constr_base f) (build_base fs)
  | nil => unit
  end.

  (*Construct the function for recursion*)

(*Count number of recursive occurrences (NOTE: doesnt work for non-uniform recursion)*)
Definition count_rec_occ (ts: typesym) (c: funsym) :=
  fold_right (fun v acc => 
    match v with
    | vty_cons ts' vs => (if typesym_eqb ts ts' (*typesym_eq_dec ts ts'*) then 1 else 0)
    | _ => 0
    end + acc) 0 (s_args c).

Definition build_constr_rec (ts: typesym) (c: funsym) : Set :=
  finite (count_rec_occ ts c).


Definition cast_build_base {c1 c2: list funsym} (H: c1 = c2) (x: build_base c1) :
  build_base c2.
Proof.
  subst. apply x.
Defined.
(*This is still a bit ugly because of the equality and cast
  Otherwise Coq cannot tell that fs = x :: tl, so it can't simplify and
  prove termination at the same time*)
Fixpoint build_rec (ts: typesym) (constrs: list funsym) {struct constrs} : (build_base constrs -> Set) :=
  match constrs with
  | nil => fun _ => empty
  | f :: fs =>
    (match fs as l return fs = l -> (build_base (f :: l) -> Set) with
    | nil => fun _ _ => build_constr_rec ts f
    | x :: tl => fun Heq (o: build_base (f :: x :: tl)) =>
      match o with
      | Left _ => build_constr_rec ts f
      | Right y => build_rec ts fs (cast_build_base (esym Heq) y)
      end
    end) erefl
  end.

(*Alternatively, build with tactics*)
Definition build_rec' (ts: typesym) (constrs: list funsym) : (build_base constrs -> Set).
  induction constrs.
  - simpl. intros. apply empty.
  - destruct constrs.
    + simpl. intros. apply (build_constr_rec ts a).
    + intros O. destruct O.
      * apply (build_constr_rec ts a).
      * apply IHconstrs. apply b.
Defined.

Lemma build_rec_eq: forall ts constrs x,
  build_rec ts constrs x = build_rec' ts constrs x.
Proof.
  intros. 
  intros; induction constrs; simpl; auto.
  destruct constrs; auto.
  destruct x; auto.
Qed.

(*Can handle simple inductive types, no polymorphism, abstract types,
  or nested/non-uniform recursion*)
Definition mk_adt (ts: typesym) (constrs: list funsym) : Set :=
  W (build_base constrs) (build_rec ts constrs).

(*We write our own boolean "in" function to avoid some problems with
  computability and ssreflect*)
Fixpoint in_bool {A: Type} (eq: A -> A -> bool) (x: A) (l: list A) : bool :=
  match l with
  | nil => false
  | hd :: tl => eq x hd || in_bool eq x tl
  end.

Definition funsym_in (f: funsym) (l: list funsym) : bool :=
  in_bool funsym_eqb f l.

Lemma funsym_in_spec: forall f l,
  funsym_in f l = (f \in l).
Proof.
  rewrite /funsym_in.
  move=>f l; elim: l => [//= | h t /= IH].
  by rewrite in_cons IH.
Qed.

(*Get the type (in the Either) corresponding to this constructor*)
(*A (non-typechecking) version of the below, for clarity:

  Fixpoint get_constr_type (ts: typesym) (constrs: list funsym) (f: funsym)
  (Hin: in_sum funsym_eq_dec f constrs) (c: build_constr_base f) : build_base constrs :=
  match constrs with
  | nil => tt
  | x :: xs =>
    match xs with
    | nil => match (funsym_eq_dec f x) with
              | left Heq => c
              | right _ => exfalso
              end
    | y :: ys =>
      match (funsym_eq_dec f x) with
      | left Heq => Left _ _ c
      | right _ => Right (get_constr_type ts xs f _ c)
      end
    end
  end.
*)

Lemma not_false: ~ false.
Proof. by []. Qed.

(*TODO: Maybe change to In once we test computability*)
Definition get_constr_type (ts: typesym) (constrs: list funsym) (f: funsym) 
  (Hin: funsym_in f constrs)
  (*(Hin: In f constrs)*)
  (c: build_constr_base f) : 
  (build_base constrs).
Proof.
  unfold funsym_in in Hin.
  (*apply (in_in_sum funsym_eq_dec) in Hin.*)
  induction constrs.
  - simpl. apply tt.
  - simpl. destruct constrs.
    + simpl in Hin. destruct (funsym_eqb_axiom f a).
      * subst. apply c. 
      * exfalso. apply not_false. apply Hin.
    + simpl in Hin. destruct (funsym_eqb_axiom f a).
      * subst. apply Left. apply c.
      * apply Right. apply IHconstrs. apply Hin.
Defined.

(*A generic map from a finite type to a bounded list : TODO change finite to nat and
use nth?*)
Definition blist (A: Type) (n: nat) : Type := {l : list A | length l = n}.
Definition finmap_list {A: Type} (n: nat) (l: blist A n) (f: finite n) : A.
Proof.
  induction n; simpl in *.
  - destruct f.
  - destruct n as [|n'].
    + destruct l. destruct x. inversion e.
      apply a.
    + destruct l. destruct x. inversion e.
      destruct f.
      (*Some case: use IH*)
      * apply IHn. apply exist with (x:=x). inversion e. reflexivity.
        apply f.
      (*None case: use head of list*)
      * apply a.
Defined.   

(*Now, we show that if we get the type corresponding to some
  constructor f, it is really just the type that counts the number
  of recursive instances in f*)
Lemma build_rec_get_constr_type: forall (ts: typesym) (constrs: list funsym) (f: funsym)
(*(Hin: in_sum funsym_eq_dec f constrs)*)
(Hin: funsym_in f constrs)
(c: build_constr_base f) ,
build_rec ts constrs (get_constr_type ts constrs f Hin c) =
finite (count_rec_occ ts f).
Proof.
  intros. unfold funsym_in in Hin. induction constrs.
  - inversion Hin.
  - simpl. destruct constrs; simpl in Hin; destruct (funsym_eqb_axiom f a); subst; auto.
    + exfalso. apply not_false. apply Hin.
    + apply IHconstrs.
Qed.

(*Now we need the function: given an ADT, a constructor of that ADT,
  instances of the (non-recursive) arguments for the ADT, and a list
  of recursive arguments of the correct size, create the function that
  picks the appropriate inductive argument and applies one of the
  arguments*)
(*Idea: get the Set from the function (build_rec ts constrs),
  this will be of the form match x with | Left _ _ _ => t1 | Right _ _ _ => t2 ...
  so we need to get ti, which is a finite type with the number of inductive calls
  in the constructor. Then, we need to match on this, have a map from finite n ->
  each of the inductive calls from x*)
Definition get_constr_fun (ts: typesym) (constrs: list funsym) (f: funsym)
  (Hin: funsym_in f constrs)
  (*(Hin: In f constrs)*) (c: build_constr_base f) 
  (x: blist (mk_adt ts constrs) (count_rec_occ ts f)):
  build_rec ts constrs (get_constr_type ts constrs f Hin c) -> mk_adt ts constrs.
Proof.
  rewrite build_rec_get_constr_type. apply (finmap_list _ x).
Defined.

(*Finally, create the constructor encoding*)
Definition make_constr (ts: typesym) (constrs: list funsym) (f: funsym)
  (*(Hin: In f constrs)*)
  (Hin: funsym_in f constrs)
  (*(Hin: in_sum funsym_eq_dec f constrs) *) (c: build_constr_base f) 
  (x: blist (mk_adt ts constrs) (count_rec_occ ts f)) :
  mk_adt ts constrs :=
  mkW (build_base constrs) (build_rec ts constrs) 
  (get_constr_type ts constrs f Hin c) (get_constr_fun ts constrs f Hin c x).

End ADTConstr.

(*Just for tests*)
Require Import Coq.Logic.FunctionalExtensionality.
Section Tests.

Notation mk_fs name params args ret_ts ret_args := 
  (Build_funsym name params args (vty_cons ret_ts (map vty_var ret_args)) eq_refl eq_refl eq_refl).

(*
Definition find {A B: Type} (eq_dec: forall (x y : A), {x = y} + {x <> y}) 
  (l: list (A * B)) (x: A) : option B :=
  fold_right (fun y acc => if eq_dec (fst y) x then Some (snd y) else acc) None l.

Notation find_constr ts constrs x :=
  (find funsym_eq_dec (constr_rep ts constrs) x).
*)

Definition triv_vars : typevar -> Set := fun _ => empty.

(*Unit*)
Definition ts_unit : typesym := mk_ts "unit" nil eq_refl.
Definition aunit := mk_adt triv_vars ts_unit 
  [ mk_fs "tt" nil nil ts_unit nil].

Lemma aunit_correct: aunit = W unit (fun _ => empty).
Proof. reflexivity. Qed.

Definition ta : typevar := "a"%string.
Definition tb : typevar := "b"%string.

(*
Lemma att_correct: 
(map snd (constr_rep ts_unit [ mk_fs "tt" nil nil ts_unit nil])) =
[mkW unit _ tt emp_fun].
Proof. reflexivity. Qed.*)


Ltac destruct_either :=
  repeat match goal with
  | x: either ?a ?b |- _ => destruct x 
  end; auto.

Ltac solve_adt_eq :=
  vm_compute; f_equal; apply functional_extensionality;
  intros; destruct_either.

(*Bool*)
Definition ts_bool : typesym := mk_ts "bool" nil eq_refl.
Definition abool := mk_adt triv_vars ts_bool
  [mk_fs "true" nil nil ts_bool nil;
   mk_fs "false" nil nil ts_bool nil].

Lemma abool_correct: abool = W (either unit unit) (fun _ => empty).
Proof. solve_adt_eq. Qed.

(*
Lemma abool_constrs_correct:
  map snd (constr_rep ts_bool [mk_fs "true" nil nil ts_bool nil;
  mk_fs "false" nil nil ts_bool nil]) =
  [mkW _ _ None emp_fun; mkW _ _ (Some tt) emp_fun].
Proof. reflexivity. Qed.
*)

(*Days of the week*)
Definition ts_week : typesym := mk_ts "days" nil eq_refl.
Definition aweek := mk_adt triv_vars ts_week
  [mk_fs "mon" nil nil ts_week nil;
   mk_fs "tues" nil nil ts_week nil;
   mk_fs "wed" nil nil ts_week nil;
   mk_fs "thurs" nil nil ts_week nil;
   mk_fs "fri" nil nil ts_week nil;
   mk_fs "sat" nil nil ts_week nil;
   mk_fs "sun" nil nil ts_week nil].

Lemma aweek_correct: aweek = 
  W (either unit (either unit (either unit (either unit 
    (either unit (either unit unit)))))) (fun _ => empty).
Proof.
  solve_adt_eq. 
Qed. 

(*Types with arguments*)

(*Simple type with 2 int constructors*)
Inductive num : Set :=
  | npos : Z -> num
  | nneg : Z -> num
  | nzero : num.

Definition ts_num : typesym := mk_ts "num" nil eq_refl.
Definition anum := mk_adt triv_vars ts_num
  [mk_fs "npos" nil [vty_int] ts_num nil;
   mk_fs "nneg" nil [vty_int] ts_num nil;
   mk_fs "nzero" nil nil ts_num nil].

Lemma anum_correct: anum =
  W (either Z (either Z unit)) (fun _ => empty).
Proof.
  solve_adt_eq.
Qed.

(*Type with mix of int and real arguments*)
Inductive test1 : Set :=
  | test1a : Z -> Z -> test1
  | test1b: test1
  | test1c : R -> Z -> test1
  | test1d: R -> R -> R -> test1.

Definition ts_test1 : typesym := mk_ts "test1" nil eq_refl.
Definition atest1 := mk_adt triv_vars ts_test1
  [mk_fs "test1a" nil [vty_int; vty_int] ts_test1 nil;
   mk_fs "test1b" nil nil ts_test1 nil;
   mk_fs "test1c" nil [vty_real; vty_int] ts_test1 nil;
   mk_fs "test1d" nil [vty_real; vty_real; vty_real] ts_test1 nil].

Lemma atest1_correct : atest1 =
  W 
  (either (Z * Z) (either unit (either (R * Z) (R * (R * R)))))
    (fun _ => empty).
Proof.
  solve_adt_eq.
Qed.

(*Simple Inductive types (no polymorphism, no nested recursion, 
  only uniform recursion)*)

(*Nat*)
Definition ts_nat : typesym := mk_ts "nat" nil eq_refl.
Definition anat := mk_adt triv_vars ts_nat
  [mk_fs "O" nil nil ts_nat nil;
   mk_fs "S" nil [vty_cons ts_nat nil] ts_nat nil].

Lemma anat_correct: anat =
  W (either unit unit) (fun (x: either unit unit) =>
    match x with
    | Left  _ => empty
    | Right _ => unit
    end).
Proof. reflexivity. Qed.

(*Int list*)
Definition ts_intlist : typesym := mk_ts "intlist" nil eq_refl.
Definition aintlist := mk_adt triv_vars ts_intlist
  [mk_fs "nil" nil nil ts_intlist nil;
   mk_fs "cons" nil [vty_int; vty_cons ts_intlist nil] ts_intlist nil].

Lemma aintlist_correct: aintlist =
  W (either unit Z) (fun x =>
    match x with
    | Left _ => empty
    | Right _ => unit
    end).
Proof. reflexivity. Qed. 

(*Int binary tree*)
Definition ts_inttree : typesym := mk_ts "inttree" nil eq_refl.
Definition ainttree := mk_adt triv_vars ts_inttree
  [mk_fs "leaf" nil nil ts_inttree nil;
   mk_fs "node" nil [vty_int; vty_cons ts_inttree nil; vty_cons ts_inttree nil]
    ts_inttree nil].

Lemma ainttree_correct: ainttree =
  W (either unit Z) (fun x =>
    match x with
    | Left _ => empty
    | Right _ => option unit
    end).
Proof. reflexivity. Qed.

(*More complicated simple inductive type*)
Inductive test2 : Set :=
  | test2a: Z -> test2
  | test2b: test2 -> test2
  | test2c: test2 -> R -> test2 -> test2 -> test2
  | test2d: Z -> Z -> test2 -> test2.

Definition ts_test2 : typesym := mk_ts "test2" nil eq_refl.
Definition atest2:= mk_adt triv_vars ts_test2
  [mk_fs "test2a" nil [vty_int] ts_test2 nil;
  mk_fs "test2b" nil [vty_cons ts_test2 nil] ts_test2 nil;
  mk_fs "test2c" nil [vty_cons ts_test2 nil; vty_real; vty_cons ts_test2 nil;
    vty_cons ts_test2 nil] ts_test2 nil;
  mk_fs "test2d" nil [vty_int; vty_int; vty_cons ts_test2 nil] ts_test2 nil].

Lemma atest2_correct : atest2 =
  W (either Z (either unit (either R (Z * Z))))
    (fun x =>
      match x with
      | Left  _ => empty
      | Right (Left _) => unit
      | Right (Right (Left _)) => option (option unit)
      | Right _ => unit
      end).
Proof. reflexivity. Qed.

(*Polymorphism*)
Definition one_var (A: Set) : typevar -> Set :=
  fun t => if String.eqb ta t then A else empty.
Definition two_var (A: Set) (B: Set) : typevar -> Set :=
  fun t => if String.eqb ta t then A else
           if String.eqb tb t then B else
           empty.

(*Option type*)
Definition ts_option : typesym := mk_ts "option" [ta] eq_refl.
Definition aoption (A: Set) := mk_adt (one_var A) ts_option
  [mk_fs "None" [ta] nil ts_option [ta];
   mk_fs "Some" [ta] [vty_var ta] ts_option [ta]].

Lemma aoption_correct: forall (A: Set),
  aoption A = W (either unit A) (fun _ => empty).
Proof.
  intros. solve_adt_eq.
Qed. 

(*Either type*)
Definition ts_either: typesym := mk_ts "either" [ta; tb] eq_refl.
Definition aeither (A: Set) (B: Set) := mk_adt (two_var A B) ts_either
  [mk_fs "Left" [ta; tb] [vty_var ta] ts_either [ta; tb];
   mk_fs "Right" [ta; tb] [vty_var tb] ts_either [ta; tb]].

Lemma aeither_correct: forall (A: Set) (B: Set),
  aeither A B = W (either A B) (fun _ => empty).
Proof.
  intros. solve_adt_eq.
Qed.

(*List type*)
Definition ts_list: typesym := mk_ts "list" [ta] eq_refl.
Definition alist (A: Set) := mk_adt (one_var A) ts_list
  [mk_fs "Nil" [ta] nil ts_list [ta];
   mk_fs "Cons" [ta] [vty_var ta; vty_cons ts_list [vty_var ta]] ts_list [ta]].

Lemma alist_correct: forall (A: Set),
  alist A = W (either unit A) (fun x =>
    match x with
    | Left _ => empty
    | Right _ => unit
    end).
Proof. intros. solve_adt_eq. 
Qed. 

(*Binary tree*)
Definition ts_tree: typesym := mk_ts "tree" [ta] eq_refl.
Definition atree (A: Set) := mk_adt (one_var A) ts_tree
  [mk_fs "Leaf" [ta] nil ts_tree [ta];
   mk_fs "Node" [ta] 
    [vty_var ta; vty_cons ts_tree [vty_var ta]; vty_cons ts_tree [vty_var ta]]
    ts_tree [ta]].

Lemma atree_correct: forall (A: Set),
  atree A = W (either unit A)
    (fun x => match x with
              | Left _ => empty
              | Right _ => option unit
              end).
Proof. intros; solve_adt_eq. Qed.

End Tests.