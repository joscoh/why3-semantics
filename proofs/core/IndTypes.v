Require Import Syntax.
Require Import Typing.
Require Import Types.
Require Import Coq.Lists.List.

(*From mathcomp Require all_ssreflect.
Set Bullet Behavior "Strict Subproofs".*)

Inductive rose (A: Set) : Set :=
  | Node : A -> list (rose A) -> rose A.

Inductive perfect (A : Set) : Set :=
  | Two : perfect (A * A) -> perfect A
  | One: A -> perfect A.

Section W.
(*I is the index (think of this as the number of types in the mut. rec. type)
  A gives the base type for each type in the MR type (it is Either _ _) where
  each _ gives the arguments needed for the corresponding constructor
  B gives the number of recursive calls to a given type for a given type and
  constructor of that type. i is the index of the current type, j is the index
  of another type, A i is a constructor of type i, and the Set tells the number
  of calls to j*)
Variable (I: Set).
Variable (A: I -> Set).
Variable (B: forall (i: I) (j: I), A i -> Set).

Inductive W : I -> Set :=
  | mkW : forall (i: I) (a: A i) (f: forall j, B i j a -> W j), W i.

End W.

(*Inductive W (A: Set) (B: A -> Set) : Set :=
  mkW : forall (a: A) (f: B a -> W A B), W A B.*)

Inductive empty :=.

(*Some manual tests (will delete)*)
Section Manual.

(*Ex: for nats*)
Definition wnat := W unit (fun _ => bool) (fun i j b => if b then unit else empty) tt.
Definition w0 : wnat.
apply (mkW _ _ _ tt false). intros. destruct H.
Defined.

Definition wS (n: wnat): wnat.
apply mkW with (a:=true).
intros. destruct j. apply n.
Defined.

(*Let's try list*)
Definition wlist (A: Set) := W unit (fun _ => option A) 
  (fun _ _ b => match b with | None => empty | Some a => unit end) tt.

Definition wnil (A: Set) : wlist A.
Proof.
  apply mkW with (a:=None). intros. destruct H.
Defined.
(*Could be a problem: need to know instance of unit and tt are equal*)
Definition wcons (A: Set) (x: A) (tl: wlist A) : wlist A.
Proof.
  apply (mkW _ _ _ tt (Some x)).
  intros. destruct j. apply tl.
Defined.
(* mkW  _ _ _ tt (Some x) (fun _ _ => tl).*)

(*Let's do binary trees*)

Inductive tree (A: Set) : Set :=
  | leaf
  | node : A -> tree A -> tree A -> tree A.

Definition wtree (A: Set) : Set := W unit (fun _ => option A) (fun _ _ x =>
  match x with |None => empty | Some a => bool end) tt.

Definition wleaf (A: Set) : wtree A.
apply mkW with (a:=None).
intros. destruct H.
Defined.

Definition wnode (A: Set) (x: A) (lt: wtree A) (rt: wtree A) : wtree A.
refine (mkW _ _ _ tt (Some x) _).
intros. destruct j. destruct H.
- apply lt.
- apply rt.
Defined.
 (*(fun _ x =>
  match x with |None => empty | Some a => bool end)*) 
(*
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
*)
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

Definition blist (A: Type) (n: nat) : Type := {l : list A | length l = n}.

Definition mk_blist {A} (n: nat) (l: list A) (Hn: length l =? n) : blist A n.
apply (exist _ l). apply Nat.eqb_eq. apply Hn.
Defined.

Variable gamma: context.

Variable vars: typevar -> Set.
Variable abstract: forall (t: typesym), list vty -> Set.
(*TODO: require that if length of input != ts_args t, then give empty*)
Variable abstract_wf: forall (t: typesym) (l: list vty),
  length l <> length (ts_args t) ->
  abstract t l = empty.

(*Construct the base type*)

Definition get_vty_base (v: vty) : option Set :=
  match v with
  | vty_int => Some Z
  | vty_real => Some R
  | vty_var x => Some (vars x)
  | vty_cons ts vs => 
    match (find_constrs gamma ts) with
    | None => Some (abstract ts vs) 
    | Some constrs => None (*TODO: for now*)
    end
     (*for now*)
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
      | Left _ _ _ => build_constr_rec ts f
      | Right _ _ y => build_rec ts fs (cast_build_base (eq_sym Heq) y)
      end
    end) eq_refl
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

(*For now, see what happens with alternate finite type*)

(*Definition finite' (n: nat) : Set := {x : nat | x < n}.*)

(*Mutual recursion*)
(*
Print alg_datatype.
Definition def_adt : typesym * list funsym :=
  (mk_ts "a" nil eq_refl, nil).*)

Print nth.
Definition fin_nth {A: Type} (l: list A) (n: finite (length l)) : A.
Proof.
  remember (length l) as m.
  generalize dependent l. induction m; intros.
  - inversion n.
  - simpl in n. destruct l.
    + inversion Heqm.
    + simpl in Heqm. inversion Heqm.
      destruct m.
      * apply a.
      * destruct n.
        -- apply (IHm f l H0).
        -- apply a.
Defined.

  (*Now (tentatively) has mutual recursion*)
  (*TODO: try with proofs (no default args) - right now
  can't match
    But may not work - doesnt know that finite 1 -> 0 and so on
    TODO: see tomorrow*)
Definition mk_adts (l: list (typesym * list funsym)) : finite (length l) -> Set :=
  W (finite (length l)) (fun n => build_base (snd (fin_nth l n)))
    (fun (this: finite _) (i: finite _) => 
      build_rec (fst (fin_nth l i))
        (snd (fin_nth l this))).

(*For the singleton list*)
(*
Definition single_fin (n: nat) (Hn: n = 1) : finite n.
Proof.
  subst.
  apply tt.
Defined.*)

(*For non-mutual types*)
Definition mk_adt (ts: typesym) (constrs: list funsym) : Set :=
  mk_adts [(ts, constrs)] tt. 
(*TODO: (Plan)
1. clean up this file
2. do constructors for mut. rec. types
3. implement nested types by transforming 
4. add tests (rose tree and 1 more complicated (maybe w mut rec))
5. do constructors for this
(would like to get this done this week)
6. go back and add this to semantics
7. add to denotational semantics+handle pattern matching

For nested types, see notes (add here)

*)

(*Can handle simple inductive types, no polymorphism, abstract types,
  or nested/non-uniform recursion*)
(*Definition mk_adt (ts: typesym) (constrs: list funsym) : Set :=
  W (finite 1) (fun i => build_base constrs) (fun i j => build_rec ts constrs) tt.*)

(*A version of "In" that we can use in proofs of Type*)
Fixpoint in_bool {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
  (x: A) (l: list A) : bool :=
  match l with
  | nil => false
  | y :: tl => eq_dec x y || in_bool eq_dec x tl
  end.
(*Fixpoint in_sum {A: Type} 
  (eq_dec: forall (x y: A), {x=y} + {x <> y}) (x: A) (l: list A) : Type :=
  match l with
  | nil => False
  | y :: tl => if eq_dec x y then True else in_sum eq_dec x tl
  end.*)

(*With decidable equality, this is equivalent to regular In*)
(*
Lemma in_in_sum: forall {A: Type} 
(eq_dec: forall (x y: A), {x=y} + {x <> y}) (x: A) (l: list A),
In x l ->
in_sum eq_dec x l.
Proof.
  rewrite /funsym_in.
  move=>f l; elim: l => [//= | h t /= IH].
  by rewrite in_cons IH.
Qed.

Lemma in_sum_in: forall {A: Type}
(eq_dec: forall (x y: A), {x=y} + {x <> y}) (x: A) (l: list A),
in_sum eq_dec x l ->
In x l.
Proof.
  intros; induction l; simpl. inversion X.
  simpl in X. destruct (eq_dec x a); subst; [left | right]; auto.
Qed.
  *)
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

(*TODO: Maybe change to In once we test computability*)
Definition get_constr_type (ts: typesym) (constrs: list funsym) (f: funsym) 
  (*(Hin: In f constrs)*) (Hin: in_bool funsym_eq_dec f constrs)
  (c: build_constr_base f) : 
  (build_base constrs).
Proof.
  induction constrs.
  - apply tt.
  - simpl. destruct constrs.
    + simpl in Hin.
      destruct (funsym_eq_dec f a).
      * rewrite <- e. apply c.
      * inversion Hin.
    + simpl in Hin.
      destruct (funsym_eq_dec f a).
      * apply Left. rewrite <- e. apply c. 
      * apply Right. apply IHconstrs. apply Hin.
Defined.


(*A generic map from a finite type to a bounded list : TODO change finite to nat and
use nth?*)


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
Definition build_rec_get_constr_type: forall (ts ts': typesym) (constrs: list funsym) (f: funsym)
(Hin: in_bool funsym_eq_dec f constrs)
(c: build_constr_base f) ,
build_rec ts' constrs (get_constr_type ts constrs f Hin c) =
finite (count_rec_occ ts' f).
Proof.
  intros. induction constrs.
  - inversion Hin.
  - simpl. destruct constrs; simpl in Hin; destruct (funsym_eq_dec f a).
    + rewrite e. reflexivity.
    + inversion Hin.
    + rewrite e. reflexivity.
    + apply IHconstrs.
Defined.

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
  (Hin: in_bool funsym_eq_dec f constrs)
  (*(Hin: In f constrs)*) (c: build_constr_base f) 
  (x: blist (mk_adt ts constrs) (count_rec_occ ts f)):
  build_rec ts constrs (get_constr_type ts constrs f Hin c) -> mk_adt ts constrs.
Proof.
  rewrite build_rec_get_constr_type. apply (finmap_list _ x).
Defined.

(*Finally, create the constructor encoding*)
(*TODO*)

Print mkW.

Definition tuple_eq_dec {A B} (eq1: forall (x y: A), {x = y} + {x <> y})
  (eq2: forall (x y: B), {x = y} + {x <> y}) :
  forall (x y : (A * B)), {x = y} + { x <> y}.
Proof.
  intros. destruct x; destruct y.
  destruct (eq1 a a0); [subst |right; intro C; inversion C; subst; contradiction].
  destruct (eq2 b b0); [subst | right; intro C; inversion C; subst; contradiction].
  left. reflexivity.
Defined.


Definition make_constr (l: list (typesym * list funsym)) (n: finite (length l))
  (f: funsym)
  (Hin: in_bool funsym_eq_dec f (snd (fin_nth l n)))
  (c: build_constr_base f)
  (recs: forall (x: finite (length l)), blist (mk_adts l x) 
    (count_rec_occ (fst (fin_nth l x)) f)) :
  mk_adts l n.
Proof.
  apply (mkW)with (a:=get_constr_type (fst (fin_nth l n)) _ f Hin c).
  intros j. intros.
  rewrite (build_rec_get_constr_type (fst(fin_nth l n)) (fst(fin_nth l j)) _ f Hin c) in H.
  specialize (recs j). apply (finmap_list _ recs H).
Defined.

Print make_constr.

(*For non-mut-rec*)
Definition make_constr_simple (ts: typesym) (constrs: list funsym) (f: funsym)
(Hin: in_bool funsym_eq_dec f constrs)
(c: build_constr_base f)
(recs: blist (mk_adt ts constrs) (count_rec_occ ts f)) :
mk_adt ts constrs.
Proof.
  apply make_constr with(f:=f).
  - apply Hin.
  - apply c.
  - intros. destruct x. apply recs.
Defined. 

(*
Definition make_constr (ts: typesym) (constrs: list funsym) (f: funsym)
  (*(Hin: In f constrs)*)
  (Hin: in_bool funsym_eq_dec f constrs) (c: build_constr_base f) 
  (x: blist (mk_adt ts constrs) (count_rec_occ ts f)) :
  mk_adt ts constrs :=
  mkW unit (fun _ => build_base constrs) (fun i _ => build_rec ts constrs) 
  tt (get_constr_type ts constrs f Hin c) (fun (u: unit) => 
    match u with
    | tt => get_constr_fun ts constrs f Hin c x
    end).*)
End ADTConstr.

(*Just for tests*)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep_dec.

(* Mutual recursion means we need additional typecasts and axioms
  to deal with the dependent functions. We do that here. Since this is
  only for testing, we don't introduce any axioms into the semantics*)
Require Import Coq.Logic.ClassicalFacts.
  Section Cast.
  
  (*Cast 1 type to another*)
  Definition cast {A1 A2: Set} (H: A1 = A2) (x: A1) : A2.
  Proof.
    subst. apply x.
  Defined.
  
  (*We need UIP, so we assume it directly (rather than something like
    excluded middle or proof irrelevance, which implies UIP)*)
  Axiom UIP: forall {A: Type} {x y : A} (H1 H2: x = y), H1 = H2.
  
  Lemma cast_left: forall {A B A' B': Set} (H1: A = A') (H2: B = B') (H3: either A B = either A' B') x,
    cast H3 (Left A B x) = Left A' B' (cast H1 x).
  Proof.
    intros. subst. unfold cast. unfold eq_rec_r. simpl. unfold eq_rec. unfold eq_rect.
    assert (H3 = eq_refl) by apply UIP.
    rewrite H. reflexivity.
  Qed.
  
  Lemma cast_right: forall {A B A' B': Set} (H1: A = A') (H2: B = B') (H3: either A B = either A' B') x,
  cast H3 (Right A B x) = Right A' B' (cast H2 x).
  Proof.
  intros. subst. unfold cast. unfold eq_rec_r. simpl. unfold eq_rec. unfold eq_rect.
  assert (H3 = eq_refl) by apply UIP.
  rewrite H. reflexivity.
  Qed.
  
  Lemma eq_idx {I: Set} {A1 A2 : I -> Set} (Heq: A1 = A2)
    (i: I): A1 i = A2 i.
  Proof.
    rewrite Heq. reflexivity.
  Defined.
  
  (*A version of [f_equal] for W types*)
  Lemma w_eq_aux: forall {I: Set} (A1 A2: I -> Set) (Heq: A1 = A2)
    (B1: forall i: I, I -> A1 i -> Set)
    (B2: forall i: I, I -> A2 i -> Set),
    (forall i j a, B1 i j a = B2 i j (cast (eq_idx Heq i) a)) ->
    W I A1 B1 = W I A2 B2.
  Proof.
    intros.
    subst. f_equal. repeat(apply functional_extensionality_dep; intros).
    rewrite H. reflexivity.
  Qed.

  Lemma eq_idx' {I: Set} {A: I -> Set} (B: forall i: I, I -> A i -> Set) {i j: I}
    (a1 a2: A i) (Heq: a1 = a2) : B i j a1 = B i j a2.
  Proof.
    rewrite Heq. reflexivity.
  Defined.

  Lemma mkW_eq_aux: forall {I: Set} (A: I -> Set) (B: forall i: I, I -> A i -> Set) (i: I)
    (a1 a2: A i) (Heq: a1 = a2) (f1: forall j, B i j a1 -> W I A B j)
    (f2: forall j, B i j a2 -> W I A B j),
    (forall j b, f1 j b = f2 j (cast (eq_idx' B a1 a2 Heq) b)) ->
    mkW I A B i a1 f1 = mkW I A B i a2 f2.
  Proof.
    intros. subst. f_equal. repeat (apply functional_extensionality_dep; intros).
    rewrite H. reflexivity.
  Qed. 
  
  End Cast.

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
Definition triv_syms: typesym -> list vty -> Set := fun _ _ => empty.
Definition triv_context : context := nil.

Notation triv_adt := (mk_adt triv_context triv_vars triv_syms).
Notation triv_constr := (make_constr_simple triv_context triv_vars triv_syms).

Definition emp_fun {A: Type} : empty -> A := fun x =>
match x with end.

(*Unit*)
Definition ts_unit : typesym := mk_ts "unit" nil eq_refl.
Definition fs_tt := mk_fs "tt" nil nil ts_unit nil.


Definition aunit := triv_adt ts_unit [ fs_tt].

Definition att := triv_constr ts_unit [fs_tt] fs_tt eq_refl tt
  (mk_blist 0 nil eq_refl). 

Lemma aunit_correct: aunit = W (finite 1) (fun _ => unit) (fun _ _ _ => empty) tt.
Proof. reflexivity. Qed. 

Lemma all_funsym_refl: forall {f: funsym} (H: f = f),
  H = eq_refl.
Proof.
  intros. apply UIP_dec. intros. eapply reflect_dec. apply funsym_eqb_spec.
Qed.

Lemma att_correct: att = mkW (finite 1) (fun _ => unit)
  (fun _ _ _ => empty) tt tt (fun _ => emp_fun).
Proof.
  unfold att. simpl. vm_compute.
  rewrite (all_funsym_refl (reflect_true (funsym_eqb_spec fs_tt fs_tt) _)).
  reflexivity.
Qed.

Definition ta : typevar := "a"%string.
Definition tb : typevar := "b"%string.

Ltac destruct_either :=
  repeat match goal with
  | x: either ?a ?b |- _ => destruct x 
  end; auto.

Ltac solve_adt_eq :=
  vm_compute; f_equal; repeat(apply functional_extensionality_dep; intros);
  intros; destruct_either.

(*Bool*)
Definition ts_bool : typesym := mk_ts "bool" nil eq_refl.
Definition fs_true := mk_fs "true" nil nil ts_bool nil.
Definition fs_false := mk_fs "false" nil nil ts_bool nil.

Definition abool := triv_adt ts_bool
  [fs_true; fs_false].

Lemma abool_correct: abool = W unit (fun i => either unit unit)
  (fun _ _ _ => empty) tt.
Proof. solve_adt_eq. Qed. 

Definition atrue := triv_constr ts_bool [fs_true; fs_false] fs_true
  eq_refl tt (mk_blist 0 nil eq_refl).
Definition afalse := triv_constr ts_bool [fs_true; fs_false] fs_false
  eq_refl tt (mk_blist 0 nil eq_refl).

(*CANNOT use vm_compute: proof term blows up*)
Lemma atrue_correct: atrue = mkW (finite 1) _ _ tt (Left _ _ tt) (fun _ => emp_fun).
Proof. unfold atrue. simpl.
unfold triv_constr. simpl.
unfold make_constr. simpl.
match goal with | |- mkW ?i ?a ?b ?x ?a1 ?f = mkW ?i ?a ?b ?x ?a2 ?f2 =>
  assert (a1 = a2) end.
- f_equal. unfold eq_rect.
  rewrite (all_funsym_refl (reflect_true _ _)).
  reflexivity.
- apply mkW_eq_aux with (Heq:=H).
  intros.
  unfold eq_rect.
  unfold eq_ind_r. unfold eq_ind.
  rewrite (all_funsym_refl (eq_sym _)).
  destruct b.
Qed.

(*Days of the week*)
Definition ts_week : typesym := mk_ts "days" nil eq_refl.
Definition aweek := triv_adt ts_week
  [mk_fs "mon" nil nil ts_week nil;
   mk_fs "tues" nil nil ts_week nil;
   mk_fs "wed" nil nil ts_week nil;
   mk_fs "thurs" nil nil ts_week nil;
   mk_fs "fri" nil nil ts_week nil;
   mk_fs "sat" nil nil ts_week nil;
   mk_fs "sun" nil nil ts_week nil].

Lemma aweek_correct: aweek = 
  W unit (fun _ => either unit (either unit (either unit (either unit 
    (either unit (either unit unit)))))) (fun _ _ _ => empty) tt.
Proof. solve_adt_eq. Qed.

(*Types with arguments*)

(*Simple type with 2 int constructors*)
Inductive num : Set :=
  | npos : Z -> num
  | nneg : Z -> num
  | nzero : num.

Definition ts_num : typesym := mk_ts "num" nil eq_refl.
Definition anum := triv_adt ts_num
  [mk_fs "npos" nil [vty_int] ts_num nil;
   mk_fs "nneg" nil [vty_int] ts_num nil;
   mk_fs "nzero" nil nil ts_num nil].

Lemma anum_correct: anum =
  W unit (fun _ => either Z (either Z unit)) (fun _ _ _ => empty) tt.
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
Definition atest1 := triv_adt ts_test1
  [mk_fs "test1a" nil [vty_int; vty_int] ts_test1 nil;
   mk_fs "test1b" nil nil ts_test1 nil;
   mk_fs "test1c" nil [vty_real; vty_int] ts_test1 nil;
   mk_fs "test1d" nil [vty_real; vty_real; vty_real] ts_test1 nil].

Lemma atest1_correct : atest1 =
  W unit 
  (fun _ =>either (Z * Z) (either unit (either (R * Z) (R * (R * R)))))
    (fun _ _ _ => empty) tt.
Proof.
  solve_adt_eq.
Qed.

(*Simple Inductive types (no polymorphism, no nested recursion, 
  only uniform recursion)*)

(*Nat*)
Definition ts_nat : typesym := mk_ts "nat" nil eq_refl.
Definition fs_O: funsym := mk_fs "O" nil nil ts_nat nil.
Definition fs_S: funsym := mk_fs "S" nil [vty_cons ts_nat nil] ts_nat nil.
Definition nat_cxt : context := [datatype_def [alg_def ts_nat [fs_O; fs_S]]].

Definition anat := mk_adt nat_cxt triv_vars triv_syms  ts_nat
  [fs_O; fs_S].

Lemma anat_correct: anat =
  W unit (fun _ => either unit unit) (fun _ _ (x: either unit unit) =>
    match x with
    | Left  _ _ _ => empty
    | Right _ _ _ => unit
    end) tt.
Proof. reflexivity. Qed.

Definition aS (l: anat) := make_constr_simple nat_cxt triv_vars triv_syms ts_nat [fs_O; fs_S] fs_S
  eq_refl tt (mk_blist 1 [l] eq_refl).

Lemma aS_correct: forall l, aS l = mkW (finite 1) _ _ tt (Right _ _ tt) (fun x _ =>
  match x with
  | tt => l
  end).
Proof.
  intros. unfold aS. simpl. unfold make_constr_simple. simpl.
  unfold make_constr. simpl.
  match goal with | |- mkW ?i ?a ?b ?x ?a1 ?f = mkW ?i ?a ?b ?x ?a2 ?f2 =>
  assert (a1 = a2) end.
  - f_equal. unfold eq_rect.
    rewrite (all_funsym_refl (reflect_true _ _)). reflexivity.
  - apply mkW_eq_aux with (Heq:=H).
    intros. destruct j; reflexivity.
Qed.


(*Int list*)
Definition ts_intlist : typesym := mk_ts "intlist" nil eq_refl.
Definition fs_intnil : funsym := mk_fs "nil" nil nil ts_intlist nil.
Definition fs_intcons: funsym := 
  mk_fs "cons" nil [vty_int; vty_cons ts_intlist nil] ts_intlist nil.
Definition intlist_cxt : context := [datatype_def [alg_def ts_intlist [fs_intnil; fs_intcons]]].
Definition aintlist := mk_adt intlist_cxt triv_vars triv_syms ts_intlist
  [ fs_intnil; fs_intcons].

Lemma aintlist_correct: aintlist =
  W unit (fun _ => either unit Z) (fun _ _ x =>
    match x with
    | Left _ _ _ => empty
    | Right _ _ _ => unit
    end) tt.
Proof. reflexivity. Qed. 

(*Int binary tree*)
Definition ts_inttree : typesym := mk_ts "inttree" nil eq_refl.
Definition fs_intleaf:= mk_fs "leaf" nil nil ts_inttree nil.
Definition fs_intnode := mk_fs "node" nil [vty_int; vty_cons ts_inttree nil; vty_cons ts_inttree nil]
ts_inttree nil.
Definition inttree_cxt : context := [datatype_def [alg_def ts_inttree
  [fs_intleaf; fs_intnode]]].
Definition ainttree := mk_adt inttree_cxt triv_vars triv_syms ts_inttree
  [fs_intleaf; fs_intnode].

Lemma ainttree_correct: ainttree =
  W unit (fun _ => either unit Z) (fun _ _ x =>
    match x with
    | Left _ _ _ => empty
    | Right _ _ _ => option unit
    end) tt.
Proof. reflexivity. Qed.

(*More complicated simple inductive type*)
Inductive test2 : Set :=
  | test2a: Z -> test2
  | test2b: test2 -> test2
  | test2c: test2 -> R -> test2 -> test2 -> test2
  | test2d: Z -> Z -> test2 -> test2.

Definition ts_test2 : typesym := mk_ts "test2" nil eq_refl.
Definition fs_test2a := mk_fs "test2a" nil [vty_int] ts_test2 nil.
Definition fs_test2b := mk_fs "test2b" nil [vty_cons ts_test2 nil] ts_test2 nil.
Definition fs_test2c := mk_fs "test2c" nil [vty_cons ts_test2 nil; vty_real; vty_cons ts_test2 nil;
vty_cons ts_test2 nil] ts_test2 nil.
Definition fs_test2d := mk_fs "test2d" nil [vty_int; vty_int; vty_cons ts_test2 nil] ts_test2 nil.

Definition test2_cxt := [datatype_def [alg_def ts_test2 [fs_test2a; fs_test2b; fs_test2c; fs_test2d]]].

Definition atest2:= mk_adt test2_cxt triv_vars triv_syms ts_test2
  [ fs_test2a; fs_test2b; fs_test2c; fs_test2d].

Lemma atest2_correct : atest2 =
  W unit (fun _ => either Z (either unit (either R (Z * Z))))
    (fun _ _ x =>
      match x with
      | Right _ _ (Left _ _ _) => unit
      | Left _ _  _ => empty
      | Right _ _ (Right _ _ (Left _ _ _)) => option (option unit)
      | Right _ _ _ => unit
      end) tt.
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
Definition fs_none := mk_fs "None" [ta] nil ts_option [ta].
Definition fs_some := mk_fs "Some" [ta] [vty_var ta] ts_option [ta].
Definition option_cxt := [datatype_def [alg_def ts_option [fs_none; fs_some]]].

Definition aoption (A: Set) := mk_adt option_cxt (one_var A) triv_syms ts_option
  [fs_none; fs_some].

Lemma aoption_correct: forall (A: Set),
  aoption A = W unit (fun _ => either unit A) (fun _ _ _ => empty) tt.
Proof.
  intros. solve_adt_eq.
Qed. 

(*Either type*)
Definition ts_either: typesym := mk_ts "either" [ta; tb] eq_refl.
Definition fs_left := mk_fs "Left" [ta; tb] [vty_var ta] ts_either [ta; tb].
Definition fs_right := mk_fs "Right" [ta; tb] [vty_var tb] ts_either [ta; tb].
Definition either_cxt := [datatype_def [alg_def ts_either [fs_left; fs_right]]].

Definition aeither (A: Set) (B: Set) := mk_adt either_cxt (two_var A B) triv_syms ts_either
  [fs_left; fs_right].
  
Lemma aeither_correct: forall (A: Set) (B: Set),
  aeither A B = W unit (fun _ => either A B) (fun _ _ _ => empty) tt.
Proof.
  intros. solve_adt_eq.
Qed.

(*List type*)
Definition ts_list: typesym := mk_ts "list" [ta] eq_refl.
Definition fs_nil := mk_fs "Nil" [ta] nil ts_list [ta].
Definition fs_cons := mk_fs "Cons" [ta] [vty_var ta; vty_cons ts_list [vty_var ta]] ts_list [ta].
Definition list_cxt := [datatype_def [alg_def ts_list [fs_nil; fs_cons]]].

Definition alist (A: Set) := mk_adt list_cxt (one_var A) triv_syms ts_list
  [ fs_nil; fs_cons ].

Lemma alist_correct: forall (A: Set),
  alist A = W unit (fun _ => either unit A) (fun _ _ x =>
    match x with
    | Left _ _ _ => empty
    | Right _ _ _ => unit
    end) tt.
Proof. intros. solve_adt_eq. 
Qed. 

(*Binary tree*)
Definition ts_tree: typesym := mk_ts "tree" [ta] eq_refl.
Definition fs_leaf := mk_fs "Leaf" [ta] nil ts_tree [ta].
Definition fs_node := mk_fs "Node" [ta] 
[vty_var ta; vty_cons ts_tree [vty_var ta]; vty_cons ts_tree [vty_var ta]]
ts_tree [ta].
Definition tree_cxt := [datatype_def [alg_def ts_tree [fs_leaf; fs_node]]].

Definition atree (A: Set) := mk_adt tree_cxt (one_var A) triv_syms ts_tree
  [fs_leaf; fs_node].

Lemma atree_correct: forall (A: Set),
  atree A = W unit (fun _ => either unit A)
    (fun _ _ x => match x with
              | Left _ _ _ => empty
              | Right _ _ _ => option unit
              end) tt.
Proof. intros; solve_adt_eq. Qed.

(*Abstract type tests*)
(*Test using simple wrapper type: Inductive wrap = Wrap (abs)*)

(*Abstract type with no arguments*)
Definition ts_abs := mk_ts "abs" nil eq_refl.
Definition ts_wrap1: typesym := mk_ts "wrap1" nil eq_refl.
Definition fs_wrap1 := mk_fs "Wrap" nil [vty_cons ts_abs nil] ts_wrap1 nil.
Definition wrap1_cxt := [datatype_def [alg_def ts_wrap1 [fs_wrap1]]].

Definition abs_map1 (A: Set) (ts: typesym) (vs: list vty) : Set :=
  if typesym_eqb ts ts_abs then A else empty.

Definition awrap1 (A: Set) := mk_adt wrap1_cxt triv_vars (abs_map1 A) ts_wrap1
  [fs_wrap1].

Definition awrap1_correct: forall (A: Set),
  awrap1 A = W unit (fun _ => A) (fun _ _ _ => empty) tt.
Proof.
  intros. reflexivity. Qed. 

(*Abstract type with 2 arguments*)
Definition ts_abs2 := mk_ts "abs" [ta; tb] eq_refl.
Definition ts_wrap2: typesym := mk_ts "wrap2" [ta; tb] eq_refl.
Definition fs_wrap2 := mk_fs "Wrap" [ta; tb] 
  [vty_cons ts_abs2 [vty_var ta; vty_var tb]] ts_wrap1 [ta; tb].
Definition wrap2_cxt := [datatype_def [alg_def ts_wrap2 [fs_wrap2]]].

Definition abs_map2 (A: Set) (ts: typesym) (vs: list vty) : Set :=
  if typesym_eqb ts ts_abs2 then A else empty.

Definition awrap2 (A B C: Set) := mk_adt wrap2_cxt (two_var B C) (abs_map2 A) ts_wrap2
  [fs_wrap2].

Definition awrap2_correct: forall (A B C: Set),
  awrap2 A B C = W unit (fun _  => A) (fun _ _ _ => empty) tt.
Proof.
  intros. reflexivity. Qed. 

(*Mutually recursive type*)

(*A very simple mutually recursive type*)
Inductive mutA : Set :=
  | mk_A1 : mutA
  | mk_A2 : mutB -> mutA
with mutB : Set :=
  | mk_B : mutA -> mutB.

Definition ts_mutA := mk_ts "mutA" nil eq_refl.
Definition ts_mutB := mk_ts "mutB" nil eq_refl.
Definition fs_mk_A1 := mk_fs "mk_A1" nil nil ts_mutA nil.
Definition fs_mk_A2 := mk_fs "mk_A2" nil [vty_cons ts_mutB nil] ts_mutA nil.
Definition fs_mk_B := mk_fs "mk_B" nil [vty_cons ts_mutA nil] ts_mutB nil.

Definition mutAB_ctx := [datatype_def [alg_def ts_mutA [fs_mk_A1; fs_mk_A2];
alg_def ts_mutB [fs_mk_B]]].

Definition amutAB := mk_adts mutAB_ctx triv_vars triv_syms
  [(ts_mutA, [fs_mk_A1; fs_mk_A2]); (ts_mutB, [fs_mk_B])].
Definition amutA := amutAB None.
Definition amutB := amutAB (Some tt).



Lemma amutAB_correct: amutAB =
  W (option unit) (fun x => match x with
                    | None => either unit unit
                    | Some _ => unit
                    end)
  (fun this other x =>
    match this, x with
    | None, Left _ _ _ => empty (*First constructor of mutA has no recursive calls*)
    | None, Right _ _ _ => (*Second constructor of mutA has 1 call to mutB*)
      match other with
      | None => empty
      | _ => unit
      end
    | Some _, _ => (*Constructor of mutB has 1 call to mutA*)
      match other with
      | Some _ => empty
      | None => unit
      end
    end).
Proof.
  unfold amutAB. unfold mk_adts.  simpl.
  unfold build_base. unfold fin_nth. simpl.
  unfold eq_rect_r. simpl.
  match goal with | |- W ?x ?a ?b = W ?x ?a2 ?b2 => assert (a = a2) end.
  - apply functional_extensionality_dep; intros.
    destruct x; simpl; reflexivity.
  - apply w_eq_aux with(Heq:=H).
    intros.
    destruct i; destruct j; simpl; try reflexivity;
    destruct a; try (rewrite (cast_left eq_refl eq_refl));
    try (rewrite (cast_right eq_refl eq_refl)); reflexivity.
Qed.

(*Now we test a mutually recursive constructor*)
Definition a_mk_A2 (b: amutB) := make_constr mutAB_ctx triv_vars triv_syms 
[(ts_mutA, [fs_mk_A1; fs_mk_A2]); (ts_mutB, [fs_mk_B])] None fs_mk_A2 eq_refl tt
(*creating this map is annoying, need better method*)
(fun x => match x with
          | None =>  exist (fun l => length l = 0) nil eq_refl
          | Some tt => 
              exist (fun (l: list (amutAB (Some tt))) => length l = 1) [b] eq_refl
          end).

Lemma a_mk_A2_correct: forall (b: amutB),
  a_mk_A2 b = mkW (finite 2) _ _ None (Right _ _ tt) (fun j x =>
    match j, x with
    | Some tt, _ => b
    | None, y => match y with end
    end).
Proof.
  intros. unfold a_mk_A2. simpl. unfold make_constr. simpl.
  match goal with | |- mkW ?i ?a ?b ?x ?a1 ?f = mkW ?i ?a ?b ?x ?a2 ?f2 =>
  assert (a1 = a2) end.
  - f_equal. unfold eq_rect.
    rewrite (all_funsym_refl (reflect_true _ _)). reflexivity.
  - apply mkW_eq_aux with (Heq:=H).
    intros j x.
    destruct j.
    + destruct f. reflexivity.
    + destruct x.
Qed.

(*A simple model of our terms and formulas*)
Inductive tm : Set :=
  | tm_const: Z -> tm
  | tm_if: fmla -> tm -> tm -> tm
with fmla : Set :=
  | fm_eq: tm -> tm -> fmla
  | fm_true : fmla
  | fm_false: fmla.

Definition ts_tm := mk_ts "tm" nil eq_refl.
Definition ts_fmla := mk_ts "fmla" nil eq_refl.
Definition fs_tm_const := mk_fs "tm_const" nil [vty_int] ts_tm nil.
Definition fs_tm_if := mk_fs "tm_if" nil [vty_cons ts_fmla nil; vty_cons ts_tm nil;
  vty_cons ts_tm nil] ts_tm nil.
Definition fs_fm_eq := mk_fs "fm_eq" nil [vty_cons ts_tm nil; vty_cons ts_tm nil]
  ts_fmla nil.
Definition fs_fm_true := mk_fs "fm_true" nil nil ts_fmla nil.
Definition fs_fm_false := mk_fs "fm_false" nil nil ts_fmla nil.

Definition tm_fmla_ctx := [datatype_def[alg_def ts_tm [fs_tm_const; fs_tm_if];
  alg_def ts_fmla [fs_fm_eq; fs_fm_true; fs_fm_false]]].

Definition atm_fmla := mk_adts tm_fmla_ctx triv_vars triv_syms 
  [(ts_tm, [fs_tm_const; fs_tm_if]); 
   (ts_fmla, [fs_fm_eq; fs_fm_true; fs_fm_false])].

Definition atm := atm_fmla None.
Definition afmla := atm_fmla (Some tt).

Lemma atm_correct: atm_fmla = W (option unit) 
(fun x => match x with
  | None => either Z unit
  | Some _ => either unit (either unit unit)
  end)
(fun this other x =>
  match this, x with
  | None, Left _ => empty (*term const has no recursive calls*)
  | None, Right _ => (*term if has 1 call to fmla, 2 to term*)
    match other with
    | None => finite 2
    | _ => finite 1
    end
  | Some _, Left _ => (*fmla eq has 2 to term, 0 to fmla*)
    match other with
    | None => finite 2
    | _ => empty
    end
  | Some _, Right _ => empty (*true and false have no recursive calls*)
  end).
Proof.
  unfold atm_fmla. unfold mk_adts.  simpl.
  unfold build_base. unfold fin_nth. simpl.
  unfold eq_rect_r. simpl.
  match goal with | |- W ?x ?a ?b = W ?x ?a2 ?b2 => assert (a = a2) end.
  - apply functional_extensionality_dep; intros.
    destruct x; simpl; reflexivity.
  - apply w_eq_aux with(Heq:=H).
    intros.
    destruct i; destruct j; simpl; try reflexivity;
    destruct a; try (rewrite (cast_left eq_refl eq_refl));
    try (rewrite (cast_right eq_refl eq_refl)); try reflexivity;
    match goal with | |- match ?e with | @Left _ _ _ => ?t | @Right _ _ _ => ?u end = ?x => destruct e end;
    reflexivity.
Qed.

End Tests.