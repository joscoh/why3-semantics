Require Import Syntax.
Require Import Typing.
Require Import Types.
Require Import Coq.Lists.List.
Require Import Hlist.

Require Import Coq.Logic.Eqdep_dec.
(*Need eq_rect_eq for injectivity of constructors and test cases*)
Require Import Coq.Program.Equality.
(*Used for constructor existence, injectivity of constructors, and test cases*)
Require Import Coq.Logic.FunctionalExtensionality.

(*Dealing with finite types*)

From mathcomp Require all_ssreflect fintype finfun.
Set Bullet Behavior "Strict Subproofs".

Section SSReflect.

Import all_ssreflect fintype finfun.

Section Finite.

(*Mathcomp has lots of utilities for finite types. For our purposes, we don't
  want to use their ordinal ('I_n) type, since we want to be able to pattern match
  on the type. But we can show our finite type is isomorphic, and we use their
  n.-tuple type for length-indexed lists, as well as some results about nth,
  tuples, lists, and finite types.*)

Inductive empty : Set :=.

Fixpoint finite (n: nat) : Set :=
  match n with
  | O => empty
  | S O => unit
  | S n' => option (finite n')
  end.

Lemma no_ord_0 (x: 'I_0) : False.
destruct x.
inversion i.
Qed.

Lemma lt_S {m n}: m < n.+1 -> {m = 0} + {0 < m /\ m.-1 < n}.
Proof.
  case: (m == 0) /eqP.
  - intros. by left.
  - intros. right. assert (0 < m). {
      move: n0 => /eqP. by rewrite lt0n.
    } split => //.
    rewrite -subn1 ltn_subLR //.
Qed.

Section FiniteOrd.

Definition ord_to_finite {n: nat} (x: 'I_n) : finite n.
Proof.
  induction n.
  - exact (False_rect _ (no_ord_0 x)).
  - simpl. destruct n.
    + exact tt.
    + destruct x. destruct (lt_S i).
      * exact None.
      * exact (Some (IHn (Ordinal (proj2 a)))).
Defined.

(*Lemma to rewrite with*)
Lemma ord_to_finite_S: forall {n: nat} (x: 'I_n.+1),
  ord_to_finite x =
  (match n as n' return 'I_n'.+1 -> finite n'.+1 with
  | O => fun _ => tt
  | S m' => fun y =>
      match y with
      | Ordinal m Hlt =>
        match (lt_S Hlt) with
        | left Heq => None
        | right Hlt' => Some (ord_to_finite (Ordinal (proj2 Hlt')))
        end
      end
  end) x.
Proof.
  intros. destruct n; auto.
Qed.

Definition finite_to_nat {n: nat} (x: finite n) : nat.
Proof.
  induction n.
  - exact (match x with end).
  - destruct n.
    + apply 0.
    + destruct x.
      * exact (IHn f).+1.
      * exact 0.
Defined.

(*Rewrite lemma*)
Lemma finite_to_nat_S: forall {n: nat} (x: finite n.+1),
  finite_to_nat x =
  (match n as m return finite m.+1 -> nat with
                    | 0 => fun _ => 0
                    | n' => fun y => match y with
                            | Some f => (@finite_to_nat n' f).+1
                            | None => 0
                            end
                    end) x.
Proof.
  intros. destruct n; auto.
Qed.

Lemma finite_to_nat_bound: forall {n: nat} (x: finite n),
  finite_to_nat x < n.
Proof.
  intros. induction n.
  - inversion x.
  - rewrite finite_to_nat_S. destruct n.
    + reflexivity.
    + destruct x.
      * simpl. rewrite -(addn1 (finite_to_nat f)) -(addn1 n.+1) ltn_add2r.
        apply IHn.
      * by [].
Qed.

Definition finite_to_ord {n: nat} (x: finite n) : 'I_n :=
  Ordinal (finite_to_nat_bound x).

(*The proof of isomoprhism*)
Lemma finite_ord_cancel: forall {n: nat},
  cancel (@finite_to_ord n) (ord_to_finite).
Proof.
  move => n x. unfold finite_to_ord.
  generalize dependent (finite_to_nat_bound x).
  induction n; intros.
  - inversion x.
  - rewrite ord_to_finite_S. destruct n.
    + destruct x; reflexivity.
    + destruct (@lt_S (@finite_to_nat n.+2 x) n.+1 i).
      * destruct x; auto. inversion e.
      * destruct x. 2: { destruct a. inversion i0. }
        f_equal. apply IHn.
Qed.

Lemma ord_finite_cancel: forall {n: nat},
  cancel (@ord_to_finite n) (finite_to_ord).
Proof.
  move => n x. induction n; intros.
  - exfalso. by apply no_ord_0.
  - rewrite ord_to_finite_S; destruct n.
    + apply ord_inj; simpl. destruct x.
      destruct m; [|inversion i]. reflexivity.
    + destruct x.
      destruct (@lt_S m (S n) i).
      * subst. apply ord_inj; reflexivity.
      * apply ord_inj. specialize (IHn (Ordinal (proj2 a))).
        apply (f_equal (@nat_of_ord _)) in IHn.
        simpl. simpl in IHn. rewrite IHn {IHn} prednK //. apply a.
Qed.

(*With this isomorphism, we can get many mathcomp structures for free.*)
Section Mixins.

Variable m: nat.
Notation finm := (finite m).
Notation finite_ord_cancel' := (@finite_ord_cancel m).
Notation ord_finite_cancel' := (@ord_finite_cancel m).

Definition finite_eqMixin := CanEqMixin finite_ord_cancel'.
Canonical finite_eqType := EqType finm finite_eqMixin.
Definition finite_choiceMixin := CanChoiceMixin finite_ord_cancel'.
Canonical finite_choiceType := ChoiceType finm finite_choiceMixin.
Definition finite_countMixin := CanCountMixin finite_ord_cancel'.
Canonical finite_countType := CountType finm finite_countMixin.

Definition finite_finMixin := CanFinMixin finite_ord_cancel'.
Canonical finite_finType := FinType finm finite_finMixin.

End Mixins.

Lemma finite_eq_dec: forall (n: nat) (x y: finite n),
  { x = y } + { x <> y}.
Proof.
  intros. apply (reflect_dec _ _ (@eqP _ x y)).
Qed.

End FiniteOrd.

(*Get nth element of a list*)
(*While we could convert to an ordinal and use ssreflect's
tuple and finite libraries, this does not compute and it makes
test cases awful. So it is a bit more work, but it is worth defining
a separate function that computes.*)

Fixpoint fin_nth_aux {A: Type} {n: nat} (l: list A)
  (Hl: length l = n) (x: finite n) : A :=
  match n as n' return length l = n' -> finite n' -> A with
  | O => fun _ x => match x with end
  | S m => 
    match l as l' return length l' = m.+1 -> finite m.+1 -> A with
    | nil => fun Hlen2 _ => False_rect _ (O_S _ Hlen2)
    | a :: tl => 
      match m as m' return length (a::tl) = m'.+1 -> finite m'.+1 -> A with
      | O => fun _ _ => a
      | S k => fun Hlen3 f3 =>
        match f3 with
        | Some y => fin_nth_aux tl 
                        (Nat.succ_inj (length tl) k.+1 Hlen3) y
        | None => a
        end
      end
    end
  end Hl x.


(*Definition fin_nth_aux {A: Type} {n: nat} (l: list A) (Hl: length l = n)
  (x: finite n) : A.
Proof.
  generalize dependent l; induction n; intros l Hl.
  - exact (match x with end).
  - destruct l. 
    + exact (False_rect _ (O_S _ Hl)).
    + destruct n.
      * exact a.
      * destruct x.
        -- exact (IHn f l (Nat.succ_inj (length l) n.+1 Hl)).
        -- exact a.
Defined.*)

Lemma fin_nth_aux_proof_irrel: forall {A: Type} {n: nat} {l: list A}
  (H1 H2: length l = n) (x: finite n),
  fin_nth_aux l H1 x = fin_nth_aux l H2 x.
Proof.
  intros A n. induction n; simpl; intros; subst.
  - destruct x.
  - destruct l.
    + inversion H1.
    + destruct n.
      * reflexivity.
      * destruct x.
        -- apply IHn.
        -- reflexivity.
Qed.

(*rewrite lemma - might not need*)
Lemma fin_nth_cons {A: Type} {n: nat} (x1 x2: A) (l: list A) 
  (Hl1: length (x1 :: x2 :: l) = n.+2) (Hl2: length (x2 :: l) = n.+1)
  (f: finite n.+2) :
  fin_nth_aux (x1 :: x2 :: l) Hl1 f = 
    match f with
    | Some y => fin_nth_aux (x2 :: l) Hl2 y
    | None => x1
    end.
Proof.
  simpl. destruct f; auto.
  destruct n; auto. destruct f; auto.
  apply fin_nth_aux_proof_irrel.
Qed.

Definition fin_nth {A: Type} (l: list A): finite (length l) -> A :=
  fin_nth_aux l erefl.

Lemma fin_nth_in: forall {A: Type} (l: list A) (n: finite (length l)),
  In (fin_nth l n) l.
Proof.
  intros. unfold fin_nth. generalize dependent (erefl (length l)). 
  induction l; auto; intros.
  - inversion n.
  - simpl in n. destruct l; simpl in *.
    left. reflexivity.
    destruct n.
    + specialize (IHl y). right. apply IHl.
    + left. reflexivity.
Qed. 

(*Get nth elt of tuple*)

Definition tnthS {n: nat} {T: Type} (t: n.-tuple T) (x: finite n) : T :=
  fin_nth_aux (tval t) (size_tuple t) x.

Definition tnthS_equiv: forall {n: nat} {T: Type} (t: n.-tuple T) (x: finite n),
  tnthS t x = tnth t (finite_to_ord x).
Proof.
  intros. unfold tnthS. unfold tnth.
  move: (tnth_default t (finite_to_ord x)).
  destruct t. simpl.
  move: (size_tuple (Tuple (n:=n) (tval:=tval) i)).
  simpl. clear i. move: tval.
  induction n; intros.
  - inversion x.
  - rewrite finite_to_nat_S. destruct tval. inversion size_tuple.
    destruct n.
    + reflexivity.
    + destruct x.
      * apply (IHn f tval _ tnth_default).
      * reflexivity.
Qed.

(* For any function f: finite n -> finite m -> A, we can consider this as 
  a function which first produces an m-tuple, then selects the correct element. *)

Definition finite_fun_tuple {n: nat} {A: finite n -> Type} 
(ns: finite n -> nat)
(f: forall (j: finite n) (x: finite (ns j)), A j):
{h: forall j: finite n, (ns j).-tuple (A j) |  forall j (k: finite (ns j)),
f j k = tnthS (h j) k }. 
Proof.
  refine (exist _ (fun j => tcast (card_ord (ns j)) [ tuple of [seq (f j) i | i <- (map (@ord_to_finite _) (enum 'I_(ns j)))]]) _).
  intros.
  rewrite tnthS_equiv tcastE !tnth_map. f_equal.
  rewrite (tnth_nth (finite_to_ord k))/=.
  apply (can_inj (@finite_ord_cancel _)).
  rewrite ord_finite_cancel.
  apply val_inj => /=.
  rewrite nth_enum_ord //.
  apply finite_to_nat_bound.
Qed.

End Finite.

(*W-types*)

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

(*A type with (A + B) elements*)
Inductive either (A B: Set) : Set :=
  | Left: A -> either A B
  | Right: B -> either A B.

(*Now, we come to the construction. We do this in 3 parts:
  1. Build up the base type (A)
  2. Build up the function (A -> Set)
  3. Put together*)
Section ADTConstr.

Variable gamma: context.

Variable vars: typevar -> Set.
Variable abstract: forall (t: typesym), list vty -> Set.

Variable abstract_wf: forall (t: typesym) (l: list vty),
  length l <> length (ts_args t) ->
  abstract t l = empty.

(*Construct the base type*)

(*Filter out the inductive types*)
Definition get_nonind_vtys (l: list vty) : list vty :=
  filter (fun v => match v with 
                    | vty_cons ts vs =>
                      ~~isSome (find_constrs gamma ts)
                    | _ => true
                    end) l.

Fixpoint big_sprod (l: list Set) : Set :=
  match l with
  | nil => unit
  | [x] => x
  | x :: xs => (x * (big_sprod xs))%type
  end.

Definition build_vty_base (l: list vty) : Set :=
  big_sprod (map (fun v => 
    match v with
    | vty_int => Z
    | vty_real => R
    | vty_var x => vars x
    | vty_cons ts vs => (abstract ts vs)
    end) (get_nonind_vtys l)).

(*This gives the base type for a single constructor. It will be (_ * _ * ... * _),
  where each _ is one of the nontrivial, nonrecursive arguments*)
Definition build_constr_base (c: funsym) : Set :=
  build_vty_base (s_args c).

(*There are two possible options for the base type, each with pros and cons:
  1. Define the base type as the iterated Either of the base of each constructor.
    This makes pattern matching nice, and makes the types readable (for example, 
    List A would be Either unit A). But the proofs are very difficult, because
    we need induction for everything (to determine which constructor we are in) and
    proofs due not reduce due to equality issues (so some "obvious" lemmas with
    equality are very difficult).
  2. Define the base type simply as the type of constructors in the list, along
    with an instance of their [build_constr_base]. This is much, much nicer 
    to use in proofs, as it reduces, requires no induction 
    (we already have the constructor available),
    and has all the useful information already encapsulated in the type. But it
    does not allow nice pattern matching and makes the types into a cryptic
    nested sigma type.
  We choose to use the 1st method because we want to make sure we can test the
  encoding, which can get quite complicated. Some of the proofs (of constructor
  existence) are harder but provable.
  Either way, this will be hidden by an API for the main semantics, so some
  difficult proofs are not a problem for the rest of the semantics.*)
Fixpoint build_base (constrs: ne_list funsym) : Set :=
  match constrs with
  | ne_hd hd => build_constr_base hd
  | ne_cons hd tl => either (build_constr_base hd) (build_base tl)
  end.

(*Step 2: Construct the function for recursion*)

Definition rec_occ_fun (ts: typesym) : vty -> bool :=
  (fun v => 
    match v with
    | vty_cons t vs => typesym_eq_dec t ts && 
                       list_eq_dec vty_eq_dec vs (map vty_var (ts_args ts))
    | _ => false
  end).

(*Count number of recursive occurrences (NOTE: doesnt work for non-uniform 
  or nested recursion)*)
Definition count_rec_occ (ts: typesym) (c: funsym) :=
  length (filter (rec_occ_fun ts) (s_args c)).

Definition build_constr_rec (ts: typesym) (c: funsym) : Set :=
   finite (count_rec_occ ts c).

(*This is the recursive function for the W type:
  it takes in an instance of the constrs base type, and for the base type
  belonging to constructor i, the result is the finite type of the number of
  recursive occurrences of ts in i *)
(*This is one of the places where the [ne_list] simplifies things; otherwise, we need
  a nested pattern match and the dependent pattern match becomes very complicated.*)
Fixpoint build_rec (ts: typesym) (constrs: ne_list funsym) {struct constrs} : (build_base constrs -> Set) :=
  match constrs with
  | ne_hd f => fun _ => build_constr_rec ts f
  | ne_cons f fs => fun o =>
    match o with
    | Left _ => build_constr_rec ts f
    | Right y => build_rec ts fs y
    end
  end.

(*The full encoding of ADTs*)

(*This handles mutual recursion (but not nested recursion at the moment).
  Mutual recursion is not too bad, we just need to be careful to call [build_rec]
  with the correct typesym to count.*)
Definition mk_adts (m: list alg_datatype) : finite (length m) -> Set :=
  W (finite (length m)) (fun n => build_base (adt_constrs (fin_nth m n)))
    (fun (this: finite _) (i: finite _) => 
      build_rec (adt_name (fin_nth m i))
        (adt_constrs (fin_nth m this))).

(*For non-mutual types*)
Definition mk_adt (ts: typesym) (constrs: ne_list funsym) : Set :=
  mk_adts [alg_def ts constrs] tt. 

(** Constructors *)
(*Generating the constructor takes a decent amount of effort. 
First, we need to
  transform an instance of the arguments of the constructor ([build_constr_base])
  into an instance of the base type ([build_base]).
Then, we need to know that [build_rec] of a constructor base type is
  just the finite type counting the number of occurrences (the dependent types
  make this non-trivial to prove).
  Equality isn't quite enough; this requires rewriting and doesn't reduce. Instead,
  we define functions mapping one to the other (that are really the identity, but
  Coq doesn't know that) and show that they are inverses.
Then, our constructor is essentially a mapping between a finite type and
  a tuple of the same size (defined above). *)

(*Step 1: transform instance of [build_constr_base] to instance of [build_base].
  The function is conceptually simple (walk through list until we find the correct
  constructor), dependent types make it very hard to write by hand.*)
Definition get_constr_type (ts: typesym) (constrs: ne_list funsym) (f: funsym) 
  (Hin: in_bool_ne funsym_eq_dec f constrs)
  (c: build_constr_base f) : 
  (build_base constrs).
Proof.
  induction constrs; simpl; simpl in Hin; destruct (funsym_eq_dec f a).
  - rewrite <- e. apply c.
  - exfalso. apply (not_false Hin).
  - apply Left. rewrite <- e. apply c.
  - apply Right. apply (IHconstrs Hin).
Defined.

(*The by-hand version (TODO: do we need this?)*)
Fixpoint get_constr_type' (ts: typesym) (constrs: ne_list funsym) (f: funsym)
  (Hin: in_bool_ne funsym_eq_dec f constrs)
  (c: build_constr_base f):
  build_base constrs :=
  (match constrs as cs return in_bool_ne funsym_eq_dec f cs -> build_base cs with
  | ne_hd a => fun Hin' =>
    match (funsym_eq_dec f a) as b return b -> build_base (ne_hd a) with
    | left Heq => fun _ => (ltac:(rewrite <- Heq; apply c))
    | right Hneq => fun b => False_rect _ (not_false b)
    end Hin'
  | ne_cons a tl => fun Hin' =>
    (match (funsym_eq_dec f a) as b 
      return b || in_bool_ne funsym_eq_dec f tl -> build_base (ne_cons a tl)
    with
    | left Heq => fun _ =>Left _ _ (ltac:(rewrite <- Heq; apply c))
    | right Hneq => fun Hin'' => Right _ _ (get_constr_type' ts tl f Hin'' c)
    end) Hin' 
  end) Hin.

Lemma get_constr_type_eq: forall ts constrs f (Hin: in_bool_ne funsym_eq_dec f constrs)
  (c: build_constr_base f),
    get_constr_type ts constrs f Hin c = get_constr_type' ts constrs f Hin c.
Proof.
  intros. induction constrs; simpl; auto;
  simpl in Hin;
  destruct (funsym_eq_dec f a); auto. rewrite IHconstrs; auto.
Qed.

(*Now, we show that if we get the type corresponding to some
  constructor f, it is really just the type that counts the number
  of recursive instances in f*)
Definition build_rec_get_constr_type: forall (ts ts': typesym) (constrs: ne_list funsym) 
  (f: funsym) (Hin: in_bool_ne funsym_eq_dec f constrs)
  (c: build_constr_base f) ,
  build_rec ts' constrs (get_constr_type ts constrs f Hin c) =
  finite (count_rec_occ ts' f).
Proof.
  intros. induction constrs; simpl; simpl in Hin;
  destruct (funsym_eq_dec f a); subst; auto.
  exfalso. apply (not_false Hin).
Qed.

(*As noted above, we really need to transform one to the other, and rewriting
  with [build_rec_get_constr_type] leads to a term that doesn't reduce. *)
Definition build_rec_to_finite {ts ts': typesym} {constrs: ne_list funsym} 
  {f: funsym} {Hin: in_bool_ne funsym_eq_dec f constrs}
  {c: build_constr_base f}
  (x: build_rec ts' constrs (get_constr_type ts constrs f Hin c)) :
  finite (count_rec_occ ts' f).
Proof.
  intros. induction constrs; simpl in x; simpl in Hin; destruct (funsym_eq_dec f a).
  - rewrite e. apply x.
  - exfalso. apply (not_false Hin).
  - rewrite e. apply x.
  - apply (IHconstrs Hin x).
Defined.

Definition finite_to_build_rec: forall {ts ts': typesym} {constrs: ne_list funsym} 
  {f: funsym} {Hin: in_bool_ne funsym_eq_dec f constrs}
  {c: build_constr_base f}
  (x: finite (count_rec_occ ts' f)),
  build_rec ts' constrs (get_constr_type ts constrs f Hin c).
Proof.
  intros. induction constrs; simpl; simpl in Hin; destruct (funsym_eq_dec f a).
  - rewrite <- e. apply x.
  - apply (False_rec _ (not_false Hin)).
  - rewrite <- e. apply x.
  - apply (IHconstrs Hin).
Defined.


Lemma build_rec_finite_inv1: forall {ts ts': typesym} {constrs: ne_list funsym} 
{f: funsym} {Hin: in_bool_ne funsym_eq_dec f constrs}
{c: build_constr_base f} 
(x: build_rec ts' constrs (get_constr_type ts constrs f Hin c)),
(@finite_to_build_rec ts ts' constrs f Hin c 
  (build_rec_to_finite x)) = x.
Proof.
  intros. induction constrs; simpl in Hin; simpl in x; simpl;
  destruct (funsym_eq_dec f a); subst; auto. exfalso. apply (not_false Hin).
Qed.

Lemma build_rec_finite_inv2: forall {ts ts': typesym} {constrs: ne_list funsym} 
{f: funsym} {Hin: in_bool_ne funsym_eq_dec f constrs}
{c: build_constr_base f} 
(x: finite (count_rec_occ ts' f)),
(@build_rec_to_finite ts ts' constrs f Hin c 
  (finite_to_build_rec x)) = x.
Proof.
  intros. induction constrs; simpl in Hin; simpl in x; simpl;
  destruct (funsym_eq_dec f a); subst; auto. exfalso. apply (not_false Hin).
Qed.

(*Finally, create the constructor encoding: given a mutually recursive type,
  an index into the type, a constructor in the constructors of that index,
  and the arguments to the constructor (recursive and non-recursive), we encode
  the constructor such that the function matches on the mutually recursive index and
  an instance, uses
  the fact that this is equivalent to just the number of recursive occurrences of
  this index, and constructs a finite mapping; ie: applying the nth argument to the
  nth recursive call.*)

Definition make_constr (m: list alg_datatype) (n: finite (length m))
  (f: funsym)
  (Hin: in_bool_ne funsym_eq_dec f (adt_constrs (fin_nth m n)))
  (c: build_constr_base f)
  (recs: forall (x: finite (length m)), 
    (count_rec_occ (adt_name (fin_nth m x)) f).-tuple (mk_adts m x)) :
  mk_adts m n := mkW (finite (length m)) _ _ n 
    (get_constr_type (adt_name (fin_nth m n)) _ f Hin c)
    (fun j H => tnthS (recs j) (build_rec_to_finite H)).

(*For non-mutually-recursive-types *)
Definition make_constr_simple (ts: typesym) (constrs: ne_list funsym) (f: funsym)
(Hin: in_bool_ne funsym_eq_dec f constrs)
(c: build_constr_base f)
(recs: (count_rec_occ ts f).-tuple (mk_adt ts constrs)) :
mk_adt ts constrs.
Proof.
  apply (make_constr [alg_def ts constrs] tt f Hin c).
  intros x. destruct x. apply recs.
Defined.

(* Theorems about ADTs*)

(*From an instance b of [build_base l], we can get the constructor corresponding to
  this, as well as the [build_constr_base f] that is wrapped inside b.*)
Definition get_funsym_base (ts: typesym) 
  (l: ne_list funsym) (Huniq: nodupb funsym_eq_dec (ne_list_to_list l)) 
  (b: build_base l) :
  { f: funsym & {Hin: in_bool_ne funsym_eq_dec f l & 
    {b1: build_constr_base f | b = get_constr_type ts l f Hin b1}}}.
Proof.
  induction l; simpl in b.
  - simpl. apply (existT _ a).
    destruct (funsym_eq_dec a a);[|contradiction]; simpl.
    apply (existT _ isT).
    apply (exist _ b).
    unfold eq_rect. assert (e = erefl) by (apply UIP_dec; apply funsym_eq_dec).
    rewrite H; reflexivity.
  - simpl. destruct b.
    + apply (existT _ a). destruct (funsym_eq_dec a a); [|contradiction].
      simpl. apply (existT _ isT). apply (exist _ b). f_equal.
      unfold eq_rect.
      assert (e = erefl) by (apply UIP_dec; apply funsym_eq_dec).
      rewrite H. reflexivity.
    + simpl in Huniq. rewrite nodupb_cons in Huniq.
      apply andb_true_iff in Huniq.
      destruct Huniq as [Heq Huniq].
      specialize (IHl Huniq b).
      destruct IHl as [f [Hinf [b1 Hb1]]].
      apply (existT _ f).
      destruct (funsym_eq_dec f a).
      * subst. rewrite <- in_bool_ne_equiv in Heq. 
        rewrite Hinf in Heq. inversion Heq.
      * apply (existT _ Hinf). apply (exist _ b1). f_equal. apply Hb1.
Qed.

(*1. Every ADT created by constructor*)
(*A key lemma/function: Every instance of an ADT was created by a constructor, and
  moreover, we can find which constructor and the arguments to which that
  constructor was applied (assuming functional extensionality).
  NOTE: in principle, it may be possible to remove the dependence on functional
  extensionality by using Mathcomp's finfun type for finite functions. However,
  this would require significant refactoring and makes other parts of the
  proofs quite complicated. Since we assume this axiom elsewhere anyway, it is OK.*)
Definition find_constr: forall (m: list alg_datatype) (n: finite (length m))
  (Huniq: forall constrs, In constrs (map adt_constrs m) -> 
    nodupb funsym_eq_dec (ne_list_to_list constrs))
  (x: mk_adts m n),
  {f: funsym & {t: in_bool_ne funsym_eq_dec f (adt_constrs (fin_nth m n)) * build_constr_base f *
     forall (x: finite (length m)), 
     (count_rec_occ (adt_name (fin_nth m x)) f).-tuple (mk_adts m x) 
     | 
      x = make_constr m n f (fst (fst t)) (snd (fst t)) (snd t)}}.
Proof.
  intros. unfold mk_adts in x. dependent destruction x.
  unfold make_constr.
  set (constrs:= (fin_nth m i)) in *.
  assert (Huniqc: nodupb funsym_eq_dec (ne_list_to_list (adt_constrs constrs))). {
    apply Huniq. rewrite in_map_iff. exists constrs. split; auto.
    subst constrs. apply fin_nth_in.
  }
  pose proof (get_funsym_base (adt_name constrs) (adt_constrs constrs) Huniqc a).
  destruct H as [f' [Hin [b1 Ha]]].
  apply (existT _ f').
  (*construct the function we need*)
  unshelve epose (g:=_ : forall j: finite (Datatypes.length m),
    finite (count_rec_occ (adt_name (fin_nth m j)) f') ->
    W (finite (Datatypes.length m))
      (fun n : finite (Datatypes.length m) => build_base (adt_constrs (fin_nth m n)))
      (fun this i : finite (Datatypes.length m) =>
       build_rec (adt_name (fin_nth m i)) (adt_constrs (fin_nth m this))) j). {
        intros j t. apply f. subst. apply finite_to_build_rec. apply t.
       }
  (*Transform this to a function on tuples with [finite_fun_tuple]]*)
  pose proof (@finite_fun_tuple (length m) _ (fun j => count_rec_occ (adt_name (fin_nth m j)) f') g) as h.
  destruct h as [h Hhg].
  apply exist with (x:=(Hin, b1, h)).
  simpl. subst. f_equal.
  (*To prove the functions equal, we need functional extensionality*)
  repeat (apply functional_extensionality_dep; intros).
  rewrite <- (Hhg x _).
  subst g. simpl. f_equal. unfold eq_rec_r. simpl.
  rewrite build_rec_finite_inv1. reflexivity.
Qed.

(*2. Constructors are disjoint *)

(*First, two injectivity lemmas about [get_constr_type]*)
Lemma get_constr_type_inj1: forall (ts: typesym) (constrs: ne_list funsym) 
  (f1 f2: funsym) (Hin1: in_bool_ne funsym_eq_dec f1 constrs)
  (Hin2: in_bool_ne funsym_eq_dec f2 constrs)
  (c1: build_constr_base f1)
  (c2: build_constr_base f2),
  get_constr_type ts constrs f1 Hin1 c1 = get_constr_type ts constrs f2 Hin2 c2 ->
  f1 = f2.
Proof.
  intros. induction constrs;
  simpl in H; simpl in Hin1; simpl in Hin2;
  destruct (funsym_eq_dec f1 a); 
  destruct (funsym_eq_dec f2 a); subst; auto;
  try solve[inversion Hin1]; try solve[inversion Hin2];
  inversion H.
  apply (IHconstrs Hin1 Hin2 H1).
Qed.

Lemma get_constr_type_inj2: forall (ts: typesym) (constrs: ne_list funsym)
  (f: funsym) (Hin: in_bool_ne funsym_eq_dec f constrs)
  (c1: build_constr_base f)
  (c2: build_constr_base f),
  get_constr_type ts constrs f Hin c1 = get_constr_type ts constrs f Hin c2 ->
  c1 = c2.
Proof.
  intros. induction constrs; simpl in Hin; simpl in H; destruct (funsym_eq_dec f a);
  subst; auto; try solve[inversion Hin]; inversion H; auto.
  apply (IHconstrs Hin H1).
Qed.

(*Second result: no two different constructors, no matter their arguments, can
  produce the same instance of the W-type (no axioms needed)*)
Lemma constrs_disjoint: forall (m: list alg_datatype) (n: finite (length m))
  (f1 f2: funsym) (Hin1: in_bool_ne funsym_eq_dec f1 (adt_constrs (fin_nth m n)))
  (Hin2: in_bool_ne funsym_eq_dec f2 (adt_constrs (fin_nth m n)))
  (c1: build_constr_base f1)
  (c2: build_constr_base f2)
  (recs1: forall (x: finite (length m)), 
    (count_rec_occ (adt_name (fin_nth m x)) f1).-tuple (mk_adts m x) )
  (recs2: forall (x: finite (length m)), 
    (count_rec_occ (adt_name (fin_nth m x)) f2).-tuple (mk_adts m x) ),
  f1 <> f2 ->
  make_constr m n f1 Hin1 c1 recs1 <> make_constr m n f2 Hin2 c2 recs2.
Proof.
  intros. intro C. inversion C; subst.
  apply inj_pair2_eq_dec in H1.
  - apply get_constr_type_inj1 in H1. subst; contradiction.
  - apply finite_eq_dec.
Qed.

Lemma fun_args_eq_dep: forall {A : Type} {B: A -> Type} (f g: forall(x: A), B x) (x: A),
  f = g ->
  f x = g x.
Proof.
  intros. subst. reflexivity.
Qed.

(*3. Constructors are injective (this needs eq_rect_eq (UIP))*)
Lemma constrs_inj: forall (m: list alg_datatype) (n: finite (length m))
  (f: funsym) (Hin: in_bool_ne funsym_eq_dec f (adt_constrs (fin_nth m n)))
  (c1 c2: build_constr_base f)
  (recs1 recs2: forall (x: finite (length m)), 
    (count_rec_occ (adt_name (fin_nth m x)) f).-tuple (mk_adts m x) ),
  make_constr m n f Hin c1 recs1 = make_constr m n f Hin c2 recs2 ->
  c1 = c2 /\ (forall x, recs1 x = recs2 x).
Proof.
  intros. dependent destruction H.
  assert (c1 = c2) by (apply (get_constr_type_inj2 _ _ _ _ _ _ x)).
  split; auto.
  subst. dependent destruction H.
  intros x2.
  apply eq_from_tnth. move => y.
  replace y with (finite_to_ord (ord_to_finite y)) by apply ord_finite_cancel.
  rewrite <- !tnthS_equiv.
  apply fun_args_eq_dep with(x:=x2) in x.
  apply fun_args_eq_dep with (x:=(finite_to_build_rec (ord_to_finite y))) in x.
  rewrite build_rec_finite_inv2 in x. apply x.
Qed.

End ADTConstr.

Ltac destruct_list :=
  match goal with
  | |- context [ match ?l with | nil => ?x1 | a :: b => ?x2 end] =>
    destruct l 
  end.

(*Convert between elements in a list and finite values*)
(*TODO: move*)
Section InFin.

Context {A: Type}.
Variable eq_dec: forall (x y : A), {x = y} + {x <> y}.

Definition get_idx (x: A) (l: list A) (Hin: in_bool eq_dec x l) 
  : finite (length l).
Proof.
  induction l.
  - exfalso. exact (not_false Hin).
  - simpl in Hin. destruct l.
    + exact tt.
    + destruct (eq_dec x a).
      * exact None.
      * exact (Some (IHl Hin)).
Defined.

Lemma get_idx_correct (x: A) (l: list A) (Hin: in_bool eq_dec x l) :
  fin_nth l (get_idx x l Hin) = x.
Proof.
  unfold fin_nth. generalize dependent (erefl (length l)).
  induction l; intros; simpl.
  - inversion Hin.
  - destruct l; simpl.
    + simpl in Hin. destruct (eq_dec x a); subst; auto.
      inversion Hin.
    + simpl in Hin. destruct (eq_dec x a); subst; auto.
      apply IHl.
Qed.
(*
Lemma fin_nth_aux_inj {n: nat} {l: list A} (x y: finite n)
  (Hl1 Hl2: length l = n) :
  fin_nth_aux l Hl1 x = fin_nth_aux l Hl2 y ->
  x = y.
Proof.
  revert Hl1 Hl2. generalize dependent l.
  induction n; simpl; intros; subst.
  - destruct x.
  - destruct l.
    + inversion Hl1.
    + simpl in H. destruct n.
      * destruct x; destruct y; reflexivity.
      * destruct x; destruct y; auto.
        f_equal. eapply IHn. apply H.
        (*ugh, obviously this is not true - need no dups*)  
    
    
    simpl in H. destruct x; destruct y; reflexivity.
  
  induction l; simpl; intros; subst.
  - destruct x.
  - destruct l.
    + destruct x; destruct y; reflexivity.
    + simpl length in H.
    
    
    
    simpl in H. simpl in H. 

Lemma fin_nth_inj {l: list A} ( x y: finite (length l)) :
  fin_nth l x = fin_nth l y ->
  x = y.
Proof.
  unfold fin_nth. generalize dependent (erefl (length l)).
  induction l; simpl; intros.
  - destruct x.
  - destruct l.
    + destruct x; destruct y. reflexivity.
    + simpl in H. destruct x.
      * destruct y.
        -- f_equal. eapply IHl. apply H.
        -- Print fin_nth_aux. inversion H. simpl in H.
    
    dest*)
    
(*TODO: do we need a version of get_idx that works on n more generally?*)
(*might not be generalizable enough*)
(*Yes, I need either a generalized version of [get_idx] or maybe
  just a handwritten version (or a rewrite lemma)*)
  (*Damn, this is not true - what about repeats in the list?
  TODO: need additional assumptions - no duplicates in
  mutual recursion list*)
Lemma get_idx_fin {l: list A} {x: finite (length l)} 
  (Hin: in_bool eq_dec (fin_nth l x) l) :
  get_idx (fin_nth l x) l Hin = x.
Proof.
  unfold fin_nth. generalize dependent Hin.
  induction l; intros; simpl.
  - inversion Hin.
  -  inversion sim
  remember (length l) as n.
  
  induction l; intros; simpl.
  - inversion Hin.
  - destruct l.
  
  generalize dependent (erefl (length l)). generalize dependent Hin.

End InFin.

(*TODO: dont duplicate*)
Ltac right_dec := 
  solve[let C := fresh "C" in right; intro C; inversion C; try contradiction].

Definition adt_dec: forall (x1 x2: alg_datatype), {x1 = x2} + {x1 <> x2}.
intros [t1 c1] [t2 c2].
destruct (typesym_eq_dec t1 t2); [|right_dec].
destruct (ne_list_eq_dec funsym_eq_dec c1 c2); [|right_dec].
left. rewrite e e0; reflexivity.
Defined.

(*Facilities to build ADTs*)
Section Build.

(*We provide a nicer interface to build an AST, using a context,
  function symbols, and the like rather than finite values and ne_lists.*)
Variable s: sig.
Variable gamma: context.
Variable gamma_valid: valid_context s gamma.

Variable m : mut_adt.
Definition adts := typs m.

Variable m_in : mut_in_ctx m gamma.

Variable srts : list Types.sort.

Variable srts_len: length srts = length (m_params m).

Definition sigma : vty -> Types.sort :=
  ty_subst_s (m_params m)  srts.

(*TODO: do we need this?*)
(*Variable srts_len : length srts = length (ts_args adt_name).*)

Variable domain: Types.sort -> Set.

(*Variable map - evaluate the variable after substituting with the
  sort given by the map sigma (args -> sorts)*)
Definition var_map : typevar -> Set :=
  fun v => domain (sigma (vty_var v)).

(*Abstract typesym map - all typesyms are applied to sorts so 
  this works*)
Definition typesym_map : typesym -> list vty -> Set :=
  fun ts vs =>
    domain (typesym_to_sort ts (map sigma vs)).

(*A nicer interface for the ADT*)

Definition adt_rep (a: alg_datatype) (a_in: adt_in_mut a m)
 := mk_adts gamma var_map typesym_map adts
  (get_idx adt_dec a adts (In_in_bool adt_dec _ _ a_in)).

(*Now we want to make an interface for the constructor. This is harder.*)
(*We need to build the [build_constr_base] and the recursive map.
  We can do this by filtering the input [arg_list], which is not
  conceptually difficult, but involves lots of annoying dependent types*)

(*The ADT we want to build the constructor for*)
Variable t: alg_datatype.

Variable c: funsym.
Variable c_in : constr_in_adt c t.
Variable t_in: adt_in_mut t m.
(*TODO: prove this later*)
(*
Axiom c_wf: s_params c = ts_args (adt_name t).*)

Variable dom_int: domain s_int = Z.
Variable dom_real: domain s_real = R.

Definition arg_list (domain: Types.sort -> Set) := hlist domain.

Definition sigma_args : list Types.sort :=
  map sigma (s_args c).

Definition sigma_ret: Types.sort :=
  sigma (s_ret c).

(*Part 1: make_constr_base*)

(*Lemmas we need for the proof obligations:*)

Lemma sigma_int: sigma vty_int = s_int.
Proof.
  apply sort_inj; reflexivity.
Qed.

Lemma sigma_real: sigma vty_real = s_real.
Proof.
  apply sort_inj; reflexivity.
Qed.

(*TODO: move*)
Lemma ty_subst_s_cons: forall (vs: list typevar) (ts: list Types.sort)
  (t: typesym) (args: list vty),
  ty_subst_s vs ts (vty_cons t args) = typesym_to_sort t (ty_subst_list_s vs ts args).
Proof.
  intros. unfold ty_subst_list_s, ty_subst_s, v_subst. simpl. apply sort_inj; simpl.
  f_equal.
  apply list_eq_ext'; rewrite !map_length; auto.
  intros n d Hn. rewrite -> !(map_nth_inbound) with (d2:=d) by auto.
  rewrite -> (map_nth_inbound) with (d2:=s_int) by (rewrite map_length; auto).
  rewrite -> (map_nth_inbound) with (d2:=d) by auto.
  reflexivity.
Qed.

Lemma sigma_cons: forall t l,
  sigma (vty_cons t l) = typesym_to_sort t (map sigma l).
Proof.
  intros. apply ty_subst_s_cons.
Qed.

Definition build_sprod_cons {a: Set} {l: list Set}
  (x: a) (tl: big_sprod l) :
  big_sprod (a :: l) :=
  match l as l' return big_sprod l' -> big_sprod (a :: l') with
  | nil => fun _ => x
  | y :: ys => fun tl => (x, tl)
  end tl.

(*The function, built with tactics*)
(*TODO: if rewrite gives problems, use similar as before with
  function and inverses*)
Definition args_to_constr_base (a: arg_list domain sigma_args):
  build_constr_base gamma var_map typesym_map c.
Proof.
  unfold build_constr_base. unfold sigma_args in a.
  induction (s_args c).
  - exact tt.
  - unfold build_vty_base in *. simpl.
    set (Hd:=hlist_hd a).
    set (Hal:=hlist_tl a).
    destruct a0.
    + (*NOTE: ssreflect rewrite doesnt work, regular does*)
      rewrite -> sigma_int, dom_int in Hd.
      exact (build_sprod_cons Hd (IHl Hal)).
    + rewrite -> sigma_real, dom_real in Hd.
      exact (build_sprod_cons Hd (IHl Hal)).
    + exact (build_sprod_cons Hd (IHl Hal)).
    + destruct (find_constrs gamma t0).
      * exact (IHl Hal).
      * rewrite -> sigma_cons in Hd.
        exact (build_sprod_cons Hd (IHl Hal)).
Defined.

(*Part 2: build the recursive arguments*)

(*First, we do in terms of finite args, then we will convert
  to a more friendly interface*)
(*Hmm, might want to keep things bool*)

Variable dom_adts: forall (a: alg_datatype) (Hin: adt_in_mut a m),
  domain (typesym_to_sort (adt_name a) srts) =
  adt_rep a Hin.
Print adt_rep.
(*A more convenient format for us in proofs:*)
Lemma dom_adts_fin: forall (x: finite (length adts)),
  domain (typesym_to_sort (adt_name (fin_nth adts x)) srts) =
  mk_adts gamma var_map typesym_map adts x.
Proof.
  intros. rewrite dom_adts. apply fin_nth_in.
  intros Hin.
  unfold adt_rep.
  f_equal. Search get_idx.
  reflexivity.
  unfold adt_in_mut.

Variable dom_adts : forall (x: finite (length adts)),
  domain (typesym_to_sort (adt_name (fin_nth adts x)) srts) =
  adt_rep (fin_nth adts x) (fin_nth_in _ x).

(*TODO: move lemmas*)
Lemma in_filter: forall {A: Type}
  (f: A -> bool) (l: list A) (x: A),
  In x (filter f l) <-> f x /\ In x l.
Proof.
  intros. induction l; simpl; auto.
  - split; auto. intros [_ Hf]; destruct Hf.
  - destruct (f a) eqn : Hfa; subst.
    + simpl. split; intros.
      * destruct H; subst.
        -- split; auto.
        -- split; auto. apply IHl. auto.
           right. apply IHl. apply H.
      * destruct H. destruct H0; auto.
        right. apply IHl. auto.
    + split; intros.
      * split; auto. apply IHl; auto. right. apply IHl. auto.
      * destruct H. destruct H0; subst. rewrite Hfa in H. inversion H.
        apply IHl. split; auto.
Qed.

  (*TODO: move*)
  
  Lemma ty_subst_fun_nth: forall (vars: list typevar) (vs: list vty)
    (d: vty) (n: nat) (a: typevar) (s: vty),
    length vars = length vs ->
    (n < length vars) %coq_nat ->
    NoDup vars ->
    ty_subst_fun vars vs d (List.nth n vars a) = List.nth n vs s.
  Proof.
    intros vars vs d n a s'. revert n. revert vs. induction vars.
    - simpl; intros; lia.
    - intros; destruct vs.
      + inversion H.
      + destruct n.
        * simpl. destruct (typevar_eq_dec a0 a0); auto. contradiction.
        * simpl.
          inversion H1; subst. simpl in H0.
          destruct (typevar_eq_dec (List.nth n vars a) a0); subst; auto.
          -- exfalso. apply H4. apply nth_In. lia.
          -- apply IHvars; try lia. inversion H; auto. assumption.
Qed.


Lemma subst_same: forall (vars: list typevar) (srts: list Types.sort),
  length vars = length srts ->
  NoDup vars ->
  map (fun x => ty_subst_s vars srts (vty_var x)) vars = srts.
Proof.
  intros. apply list_eq_ext'; rewrite map_length; auto. intros n d Hd.
  assert (a: typevar). apply "A"%string.
  rewrite -> (map_nth_inbound) with (d2:=a); auto.
  unfold ty_subst_s. apply sort_inj; simpl.
  rewrite -> ty_subst_fun_nth with(s:=vty_int); try lia; unfold sorts_to_tys.
  rewrite -> (map_nth_inbound) with (d2:=d). reflexivity. lia.
  rewrite map_length; lia.
  assumption.
Qed.

Definition cast_list {A B: Set} (l: list A) (Heq: A = B) : list B :=
  match Heq with
  | erefl => l
  end.

Lemma cast_list_length: forall {A B: Set} (l: list A) (Heq: A = B),
  length (cast_list l Heq) = length l.
Proof.
  intros. unfold cast_list. destruct Heq. reflexivity.
Qed.

Definition tup_of_list {A: Type} {n: nat} {l: list A} (Hl: length l = n) :
  n.-tuple A := (Tuple (introT eqP Hl)).

(*To build the recursive instance function, we do the following: 
  take the input arg list and filter out the domain elements 
  corresponding to the recursive calls on the type represented by
  the input (a finite value choosing which mutually recursive type
  we are dealing with). This is conceptually simple, but the dependent
  types make things quite complicated. We factor out the proofs into
  two intermediate lemmas; then the definition becomes quite simple.*)

(*Intermediate lemmas:*)

(*Part 1: When we filter the arg list, everything has the same type
  (and therefore, we can transform the result into a list)*)
Lemma filter_args_same (x: finite (length adts)) :
  Forall (fun y => y = typesym_to_sort (adt_name (fin_nth adts x)) srts)
    (List.map sigma (List.filter (rec_occ_fun (adt_name (fin_nth adts x)))
      (s_args c))).
Proof.
  set (ts:= (adt_name (fin_nth adts x))) in *.
  apply Forall_forall. intros s' Hins'.
  rewrite in_map_iff in Hins'. destruct Hins' as [v [Hv Hinv]]; subst.
  rewrite in_filter in Hinv. destruct Hinv.
  unfold rec_occ_fun in H. destruct v; try solve[inversion H].
  apply andb_prop in H. destruct H.
  destruct (typesym_eq_dec t0 ts); subst; try solve[inversion H].
  clear H.
  destruct (list_eq_dec vty_eq_dec l [seq vty_var i | i <- ts_args ts]);
    subst; try solve[inversion H1]. clear H1.
  rewrite sigma_cons. f_equal.
  assert (ts_args ts = m_params m). {
    subst ts. apply (@adt_args s gamma gamma_valid).
    unfold adt_mut_in_ctx. split; auto.
    unfold adt_in_mut. apply fin_nth_in.
  }
  rewrite H.
  rewrite <- map_comp. apply subst_same. 
  rewrite srts_len; reflexivity.
  destruct m; simpl. apply /nodup_NoDup. apply m_nodup.
Qed.

(*Part 2: The length of the casted list (casted from domain _ to a
  W-type via the [dom_adts] assumption) is correct*)
Lemma filter_args_length (a: arg_list domain sigma_args) 
  (x: finite (length adts)) :
  length (
    cast_list (
      hlist_to_list (
        hlist_map_filter sigma a 
          (rec_occ_fun (adt_name (fin_nth adts x)))
        )
        (filter_args_same x)
    ) 
  (dom_adts x)) = count_rec_occ (adt_name (fin_nth adts x)) c.
Proof.
  rewrite cast_list_length hlist_to_list_length hlength_eq map_length.
  reflexivity.
Qed.

(*The final function is easy: just make a tuple from the list
  which we already proved has the correct length in the last lemma.
  This hides the ugly proofs.*)
Definition args_to_ind_base (a: arg_list domain sigma_args) :
  forall (x: finite (length adts)), 
    (count_rec_occ (adt_name (fin_nth adts x)) c).-tuple
      (adt_rep (fin_nth adts x) (fin_nth_in _ x)) :=
  fun x => tup_of_list (filter_args_length a x).

(*Now we can build the constructor corresponding to the function
  symbol c*)
  Check adt_rep.
  Search t.
  Check make_constr.
  Print adt_rep.
Definition constr_rep (a: arg_list domain sigma_args) :=
  make_constr gamma _ _ _ _ _ _ (args_to_constr_base a)
    (args_to_ind_base a).



  adt_rep (fin_nth adts x) (fin_nth_in _ x).

End Build.

Check args_to_ind_base.

(* TODO: Handle nested types*)

(*
(*We handle nested recursive types (ex: data rose = Node (list rose)) by
  transforming this into a mutually recursive type and using the above.
  We need to generate ismorphic ADTs and maps between them*)

Definition typesym_in (ts: typesym) (v: vty) :=
  match v with
  | vty_cons ts' vs => typesym_eqb ts ts' || existsb (typesym_in ts) vs
  | _ => false
  end.
Print typesym.

(*Really, we want to generate a unique ID for each new typesym (what if someone
names their type int or something and screws everything up?)*)

Definition new_ts (ts: typesym) (vs: list vty) : typesym.
Admitted.

Definition tuple_eq_dec {A B: Type} (eq1: forall (x y : A), {x = y} + {x <> y})
(eq2: forall (x y : B), {x = y} + {x <> y}) :
(forall (x y : A * B), {x = y} + {x <> y}).
Proof.
  intros. destruct x; destruct y.
  destruct (eq1 a a0).
  - rewrite e. destruct (eq2 b b0).
    + rewrite e0. left. reflexivity.
    + right. intro C; inversion C; contradiction.
  - right; intro C; inversion C; contradiction.
Defined.

(*TODO: move*)
Definition adts_of_context (gamma: context) : list (list (typesym * list funsym)) :=
  fold_right (fun x acc => match x with
  | datatype_def algs => 
    map (fun a => match a with |alg_def ts constrs => (ts, constrs) end) algs :: acc
  | _ => acc
  end) nil gamma.

(*Get the entire mutually recursive type a typesym is associated with*)
Definition find_mut_adt (gamma: context) (t: typesym) : 
  option (list (typesym * list funsym)) :=
  fold_right (fun x acc =>
    if in_dec typesym_eq_dec t (map fst x) then Some x else acc
    ) None (adts_of_context gamma).

(*Specialize the type (ex: go from list 'a -> list_int) *)
(*How can we do this for mutually recursive types?
  ex: what if we had the following?*)
(*Damn it, need params*)
Lemma NoDup_nodupb: forall {A: Type} (eq_dec: forall (x y : A), {x = y} + {x <> y})
  (l: list A), NoDup l -> nodupb eq_dec l.
Proof.
  intros. eapply (reflect_iff) in H. apply H. apply nodup_NoDup.
Qed.


(*Want to substitute *)
Definition funsym_subst (tyvars: list typevar) (vs: list vty) (f: funsym) : funsym :=
  Build_funsym (s_name f) (big_union typevar_eq_dec type_vars vs)
  (ty_subst_list (s_params f) vs (s_args f))
  (ty_subst (s_params f) vs (s_ret f))
    (NoDup_nodupb typevar_eq_dec _ (big_union_nodup _ _ _)) .

Definition adt_subst (ts: typesym) (constrs: list funsym) (vs: list vty) : list funsym :=
  map (funsym_subst (ts_args ts) vs) constrs.

(*Problem: we need to do multiple substitutions - or we need something like longest
  prefix match - ex: list (list (X))*)

Definition get_rec_isos_aux (l: list typesym) (args: list vty) : list (vty * typesym * list funsym) :=
  fold_right (fun x acc => match x with
  | vty_cons ts vs =>
      match (find_mut_adt gamma ts) with
      | None => acc
      | Some adt => 
        if negb(in_bool typesym_eq_dec ts l) &&
            existsb (fun t => existsb (fun v => typesym_in t v) vs) l then
            (*hmm this is more annoying than i thought - what args to give to mut rec?*)
            union _ (map )
            union (tuple_eq_dec vty_eq_dec typesym_eq_dec) 
              [(x, new_ts, ] acc else acc
  | _ =>  acc
  end) nil args.

Definition get_rec_isos_constr (l: list typesym) (constr: funsym) :=
  get_rec_isos_aux l  (s_args constr).

(*Step 2: generate the new ADTs (with no substitution)*)
Definition gen_new_adt (l: list typesym) (args: list vty) : list (vty * )

  
  )

*)

(** Testing **)

Lemma all_funsym_refl: forall {f: funsym} (H: f = f),
  H = erefl.
Proof.
  intros. apply UIP_dec. intros. eapply reflect_dec. apply funsym_eqb_spec.
Qed.
(*We need some axioms for testing: dependent functional extensionality,
  and for mutually recursive types, Uniqueness of Identity Proofs*)

(* Mutual recursion means we need additional typecasts and axioms
  to deal with the dependent functions. We do that here. Since this is
  only for testing, we don't introduce any axioms into the semantics*)
(*Require Import Coq.Logic.ClassicalFacts.*)

  Section Cast.
  
  (*Cast 1 type to another*)
  Definition cast {A1 A2: Set} (H: A1 = A2) (x: A1) : A2.
  Proof.
    subst. apply x.
  Defined.
  
  (*We need UIP, so we assume it directly (rather than something like
    excluded middle or proof irrelevance, which implies UIP)*)
  Axiom UIP: forall {A: Type}, EqdepFacts.UIP_ A.
  
  Lemma cast_left: forall {A B A' B': Set} (H1: A = A') (H2: B = B') (H3: either A B = either A' B') x,
    cast H3 (Left A B x) = Left A' B' (cast H1 x).
  Proof.
    intros. subst. unfold cast, eq_rec_r, eq_rec, eq_rect. simpl.
    assert (H3 = erefl) by apply UIP.
    rewrite H. reflexivity.
  Qed.
  
  Lemma cast_right: forall {A B A' B': Set} (H1: A = A') (H2: B = B') (H3: either A B = either A' B') x,
  cast H3 (Right A B x) = Right A' B' (cast H2 x).
  Proof.
    intros. subst. unfold cast, eq_rec_r, eq_rec, eq_rect. simpl.
    assert (H3 = erefl) by apply UIP.
    rewrite H. reflexivity.
  Qed.
  
  Lemma eq_idx {I: Set} {A1 A2 : I -> Set} (Heq: A1 = A2)
    (i: I): A1 i = A2 i.
  Proof.
    rewrite Heq. reflexivity.
  Defined.
  
  (*A version of [f_equal] for W types*)
  Lemma w_eq: forall {I: Set} (A1 A2: I -> Set) (Heq: A1 = A2)
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

  (*A version of [f_equal] for mkW*)
  Lemma mkW_eq: forall {I: Set} (A: I -> Set) (B: forall i: I, I -> A i -> Set) (i: I)
    (a1 a2: A i) (Heq: a1 = a2) (f1: forall j, B i j a1 -> W I A B j)
    (f2: forall j, B i j a2 -> W I A B j),
    (forall j b, f1 j b = f2 j (cast (eq_idx' B a1 a2 Heq) b)) ->
    mkW I A B i a1 f1 = mkW I A B i a2 f2.
  Proof.
    intros. subst. f_equal. repeat (apply functional_extensionality_dep; intros).
    rewrite H. reflexivity.
  Qed. 
  
End Cast.

(* We give many unit tests of increasing complexity to validate the encoding
  and ensure that the encodings can be proved equivalent to simpler, expected forms.*)

Section Tests.

(** Utilities for building tests *)

Notation mk_fs name params args ret_ts ret_args := 
  (Build_funsym name params args (vty_cons ret_ts (map vty_var ret_args)) erefl erefl erefl).

Definition triv_vars : typevar -> Set := fun _ => empty.
Definition triv_syms: typesym -> list vty -> Set := fun _ _ => empty.
Definition triv_context : context := nil.

Notation triv_adt := (mk_adt triv_context triv_vars triv_syms).

Notation triv_constr := (make_constr_simple triv_context triv_vars triv_syms).

Definition emp_fun {A: Type} : empty -> A := fun e =>
  match e with end.



Definition ta : typevar := "a"%string.
Definition tb : typevar := "b"%string.

(** Tactics *)

Ltac destruct_either :=
  repeat match goal with
  | x: either ?a ?b |- _ => destruct x 
  end; auto.

(*Solves ADT equality*)
Ltac solve_adt_eq :=
  vm_compute; f_equal; repeat(apply functional_extensionality_dep; intros);
  intros; destruct_either.

(*Tactic for proving constructors equal*)
Ltac revert_eqs:=
  repeat match goal with
  | H: ?x = ?y |- _ => generalize dependent H
  end.

Lemma unit_dec : forall (x y: unit), { x = y} + { x <> y}.
Proof.
  intros. left. destruct x; destruct y; reflexivity.
Qed.

(*The main tactic: basically it does the following:
  1. unfold basic definitions
  2. apply mkW_eq and prove the associated equality
  3. unfold all casts and rewrites
  4. try to prove that all equalities reduce with UIP_dec*)
Ltac prove_constr :=
  unfold triv_constr, make_constr_simple, make_constr; simpl;
  let He := fresh "Heq" in
  match goal with | |- mkW ?i ?a ?b ?x ?a1 ?f = mkW ?i ?a ?b ?x ?a2 ?f2 =>
    assert (He: a1 = a2);
  [unfold eq_rect; rewrite (all_funsym_refl (reflect_true _ _)); reflexivity|
  apply (mkW_eq a b x a1 a2 He); intros; revert_eqs;
  unfold cast, eq_rec_r, eq_rec, eq_rect, eq_idx', eq_ind_r, eq_ind (*eq_rect, eq_ind_r, eq_ind, eq_rec_r), eq_rec*);
  repeat (progress (try rewrite (all_funsym_refl (reflect_true _ _));
    try rewrite (all_funsym_refl (eq_sym _)))); intros;
    repeat match goal with
    | H: ?x = ?x |- _ => let He := fresh in 
      assert (He: H = eq_refl) by (apply UIP_dec; try (apply unit_dec));
      rewrite He; simpl
    end]; try reflexivity; auto
  end.

(** Tests *)

(*Unit*)
Definition ts_unit : typesym := mk_ts "unit" nil.
Definition fs_tt := mk_fs "tt" nil nil ts_unit nil.
Definition unit_constrs := list_to_ne_list [fs_tt] erefl.

Definition aunit := triv_adt ts_unit unit_constrs.

Definition att := triv_constr ts_unit unit_constrs fs_tt erefl tt
  (mk_tuple 0 nil erefl). 

Lemma aunit_correct: aunit = W unit (fun _ => unit) (fun _ _ _ => empty) tt.
Proof. reflexivity. Qed. 

Lemma att_correct: att = mkW (finite 1) _ _ tt tt (fun _ => emp_fun).
Proof.
  unfold att. prove_constr. destruct b.
Qed.

(*Bool*)
Definition ts_bool : typesym := mk_ts "bool" nil.
Definition fs_true := mk_fs "true" nil nil ts_bool nil.
Definition fs_false := mk_fs "false" nil nil ts_bool nil.
Definition bool_constrs := list_to_ne_list [fs_true; fs_false] erefl.

Definition abool := triv_adt ts_bool bool_constrs.

Lemma abool_correct: abool = W unit (fun i => either unit unit)
  (fun _ _ _ => empty) tt.
Proof. solve_adt_eq. Qed. 

Definition atrue := triv_constr ts_bool bool_constrs fs_true
  erefl tt (mk_tuple 0 nil erefl).
Definition afalse := triv_constr ts_bool bool_constrs fs_false
  erefl tt (mk_tuple 0 nil erefl).

Lemma atrue_correct: atrue = mkW (finite 1) _ _ tt (Left _ _ tt) (fun _ => emp_fun).
Proof. 
  unfold atrue. prove_constr. destruct b.
Qed.

(*Days of the week*)
Definition ts_week : typesym := mk_ts "days" nil.
Definition week_constrs := list_to_ne_list
[mk_fs "mon" nil nil ts_week nil;
mk_fs "tues" nil nil ts_week nil;
mk_fs "wed" nil nil ts_week nil;
mk_fs "thurs" nil nil ts_week nil;
mk_fs "fri" nil nil ts_week nil;
mk_fs "sat" nil nil ts_week nil;
mk_fs "sun" nil nil ts_week nil] erefl.
Definition aweek := triv_adt ts_week week_constrs.

Lemma aweek_correct: aweek = 
  W unit (fun _ => either unit (either unit (either unit (either unit 
    (either unit (either unit unit)))))) (fun _ _ _ => empty) tt.
Proof. solve_adt_eq. Qed.

(*Types with arguments*)

(*Simple type with 2 int constructors (in some tests, we now give the Coq versions
  of the types to make it clear what is being tested)*)
Inductive num : Set :=
  | npos : Z -> num
  | nneg : Z -> num
  | nzero : num.

Definition ts_num : typesym := mk_ts "num" nil.
Definition num_constrs := list_to_ne_list 
[mk_fs "npos" nil [vty_int] ts_num nil;
mk_fs "nneg" nil [vty_int] ts_num nil;
mk_fs "nzero" nil nil ts_num nil] erefl.
Definition anum := triv_adt ts_num num_constrs.

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

Definition ts_test1 : typesym := mk_ts "test1" nil.
Definition test1_constrs := list_to_ne_list
[mk_fs "test1a" nil [vty_int; vty_int] ts_test1 nil;
   mk_fs "test1b" nil nil ts_test1 nil;
   mk_fs "test1c" nil [vty_real; vty_int] ts_test1 nil;
   mk_fs "test1d" nil [vty_real; vty_real; vty_real] ts_test1 nil] erefl.
Definition atest1 := triv_adt ts_test1 test1_constrs.

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
Definition ts_nat : typesym := mk_ts "nat" nil.
Definition fs_O: funsym := mk_fs "O" nil nil ts_nat nil.
Definition fs_S: funsym := mk_fs "S" nil [vty_cons ts_nat nil] ts_nat nil.
Definition nat_cxt : context := [datatype_def [alg_def ts_nat [fs_O; fs_S]]].
Definition nat_constrs := list_to_ne_list [fs_O; fs_S] erefl.

Definition anat := mk_adt nat_cxt triv_vars triv_syms  ts_nat nat_constrs.

Lemma anat_correct: anat =
  W unit (fun _ => either unit unit) (fun _ _ (x: either unit unit) =>
    match x with
    | Left  _ => empty
    | Right _ => unit
    end) tt.
Proof. reflexivity. Qed.

Definition aS (l: anat) := make_constr_simple nat_cxt triv_vars triv_syms ts_nat nat_constrs fs_S
  erefl tt (mk_tuple 1 [l] erefl).

Lemma aS_correct: forall l, aS l = mkW (finite 1) _ _ tt (Right _ _ tt) (fun x _ =>
  match x with
  | tt => l
  end).
Proof.
  intros. unfold aS. prove_constr.
  destruct j; reflexivity.
Qed.

(*Int list*)
Definition ts_intlist : typesym := mk_ts "intlist" nil.
Definition fs_intnil : funsym := mk_fs "nil" nil nil ts_intlist nil.
Definition fs_intcons: funsym := 
  mk_fs "cons" nil [vty_int; vty_cons ts_intlist nil] ts_intlist nil.
Definition intlist_cxt : context := [datatype_def [alg_def ts_intlist [fs_intnil; fs_intcons]]].
Definition intlist_constrs := list_to_ne_list [ fs_intnil; fs_intcons] erefl.
Definition aintlist := mk_adt intlist_cxt triv_vars triv_syms ts_intlist intlist_constrs.

Lemma aintlist_correct: aintlist =
  W unit (fun _ => either unit Z) (fun _ _ x =>
    match x with
    | Left _ => empty
    | Right _ => unit
    end) tt.
Proof. reflexivity. Qed. 

(*Int binary tree*)
Definition ts_inttree : typesym := mk_ts "inttree" nil.
Definition fs_intleaf:= mk_fs "leaf" nil nil ts_inttree nil.
Definition fs_intnode := mk_fs "node" nil [vty_int; vty_cons ts_inttree nil; vty_cons ts_inttree nil]
ts_inttree nil.
Definition inttree_cxt : context := [datatype_def [alg_def ts_inttree
  [fs_intleaf; fs_intnode]]].
Definition inttree_constrs := list_to_ne_list [fs_intleaf; fs_intnode] erefl.
Definition ainttree := mk_adt inttree_cxt triv_vars triv_syms ts_inttree inttree_constrs.

Lemma ainttree_correct: ainttree =
  W unit (fun _ => either unit Z) (fun _ _ x =>
    match x with
    | Left _ => empty
    | Right _ => option unit
    end) tt.
Proof. reflexivity. Qed.

(*More complicated simple inductive type*)
Inductive test2 : Set :=
  | test2a: Z -> test2
  | test2b: test2 -> test2
  | test2c: test2 -> R -> test2 -> test2 -> test2
  | test2d: Z -> Z -> test2 -> test2.

Definition ts_test2 : typesym := mk_ts "test2" nil.
Definition fs_test2a := mk_fs "test2a" nil [vty_int] ts_test2 nil.
Definition fs_test2b := mk_fs "test2b" nil [vty_cons ts_test2 nil] ts_test2 nil.
Definition fs_test2c := mk_fs "test2c" nil [vty_cons ts_test2 nil; vty_real; vty_cons ts_test2 nil;
vty_cons ts_test2 nil] ts_test2 nil.
Definition fs_test2d := mk_fs "test2d" nil [vty_int; vty_int; vty_cons ts_test2 nil] ts_test2 nil.

Definition test2_cxt := [datatype_def [alg_def ts_test2 [fs_test2a; fs_test2b; fs_test2c; fs_test2d]]].
Definition test2_constrs := list_to_ne_list [ fs_test2a; fs_test2b; fs_test2c; fs_test2d] erefl.
Definition atest2:= mk_adt test2_cxt triv_vars triv_syms ts_test2 test2_constrs.

Lemma atest2_correct : atest2 =
  W unit (fun _ => either Z (either unit (either R (Z * Z))))
    (fun _ _ x =>
      match x with
      | Right (Left _) => unit
      | Left   _ => empty
      | Right (Right (Left _)) => option (option unit)
      | Right _ => unit
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
Definition ts_option : typesym := mk_ts "option" [ta].
Definition fs_none := mk_fs "None" [ta] nil ts_option [ta].
Definition fs_some := mk_fs "Some" [ta] [vty_var ta] ts_option [ta].
Definition option_cxt := [datatype_def [alg_def ts_option [fs_none; fs_some]]].
Definition option_constrs := list_to_ne_list [fs_none; fs_some] erefl.

Definition aoption (A: Set) := mk_adt option_cxt (one_var A) triv_syms ts_option
  option_constrs.

Lemma aoption_correct: forall (A: Set),
  aoption A = W unit (fun _ => either unit A) (fun _ _ _ => empty) tt.
Proof.
  intros. solve_adt_eq.
Qed. 

(*Either type*)
Definition ts_either: typesym := mk_ts "either" [ta; tb].
Definition fs_left := mk_fs "Left" [ta; tb] [vty_var ta] ts_either [ta; tb].
Definition fs_right := mk_fs "Right" [ta; tb] [vty_var tb] ts_either [ta; tb].
Definition either_cxt := [datatype_def [alg_def ts_either [fs_left; fs_right]]].
Definition either_constrs := list_to_ne_list [fs_left; fs_right] erefl.

Definition aeither (A: Set) (B: Set) := mk_adt either_cxt (two_var A B) triv_syms ts_either
  either_constrs.
  
Lemma aeither_correct: forall (A: Set) (B: Set),
  aeither A B = W unit (fun _ => either A B) (fun _ _ _ => empty) tt.
Proof.
  intros. solve_adt_eq.
Qed.

(*List type*)
Definition ts_list: typesym := mk_ts "list" [ta].
Definition fs_nil := mk_fs "Nil" [ta] nil ts_list [ta].
Definition fs_cons := mk_fs "Cons" [ta] [vty_var ta; vty_cons ts_list [vty_var ta]] ts_list [ta].
Definition list_cxt := [datatype_def [alg_def ts_list [fs_nil; fs_cons]]].
Definition list_constrs := list_to_ne_list [ fs_nil; fs_cons ] erefl.

Definition alist (A: Set) := mk_adt list_cxt (one_var A) triv_syms ts_list
  list_constrs.

Lemma alist_correct: forall (A: Set),
  alist A = W unit (fun _ => either unit A) (fun _ _ x =>
    match x with
    | Left _ => empty
    | Right _ => unit
    end) tt.
Proof. intros. solve_adt_eq. 
Qed. 

(*Binary tree*)
Definition ts_tree: typesym := mk_ts "tree" [ta].
Definition fs_leaf := mk_fs "Leaf" [ta] nil ts_tree [ta].
Definition fs_node := mk_fs "Node" [ta] 
[vty_var ta; vty_cons ts_tree [vty_var ta]; vty_cons ts_tree [vty_var ta]]
ts_tree [ta].
Definition tree_cxt := [datatype_def [alg_def ts_tree [fs_leaf; fs_node]]].
Definition tree_constrs := list_to_ne_list [fs_leaf; fs_node] erefl.

Definition atree (A: Set) := mk_adt tree_cxt (one_var A) triv_syms ts_tree
  tree_constrs.

Lemma atree_correct: forall (A: Set),
  atree A = W unit (fun _ => either unit A)
    (fun _ _ x => match x with
              | Left _ => empty
              | Right _ => option unit
              end) tt.
Proof. intros; solve_adt_eq. Qed.

(*Abstract type tests*)
(*Test using simple wrapper type: Inductive wrap = Wrap (abs)*)

(*Abstract type with no arguments*)
Definition ts_abs := mk_ts "abs" nil.
Definition ts_wrap1: typesym := mk_ts "wrap1" nil.
Definition fs_wrap1 := mk_fs "Wrap" nil [vty_cons ts_abs nil] ts_wrap1 nil.
Definition wrap1_cxt := [datatype_def [alg_def ts_wrap1 [fs_wrap1]]].

Definition abs_map1 (A: Set) (ts: typesym) (vs: list vty) : Set :=
  if typesym_eqb ts ts_abs then A else empty.

Definition wrap1_constrs := list_to_ne_list [fs_wrap1] erefl.

Definition awrap1 (A: Set) := mk_adt wrap1_cxt triv_vars (abs_map1 A) ts_wrap1
  wrap1_constrs.

Definition awrap1_correct: forall (A: Set),
  awrap1 A = W unit (fun _ => A) (fun _ _ _ => empty) tt.
Proof.
  intros. reflexivity. Qed. 

(*Abstract type with 2 arguments*)
Definition ts_abs2 := mk_ts "abs" [ta; tb].
Definition ts_wrap2: typesym := mk_ts "wrap2" [ta; tb].
Definition fs_wrap2 := mk_fs "Wrap" [ta; tb] 
  [vty_cons ts_abs2 [vty_var ta; vty_var tb]] ts_wrap1 [ta; tb].
Definition wrap2_cxt := [datatype_def [alg_def ts_wrap2 [fs_wrap2]]].

Definition abs_map2 (A: Set) (ts: typesym) (vs: list vty) : Set :=
  if typesym_eqb ts ts_abs2 then A else empty.

Definition wrap2_constrs := list_to_ne_list [fs_wrap2] erefl.

Definition awrap2 (A B C: Set) := mk_adt wrap2_cxt (two_var B C) (abs_map2 A) ts_wrap2
  wrap2_constrs.

Definition awrap2_correct: forall (A B C: Set),
  awrap2 A B C = W unit (fun _  => A) (fun _ _ _ => empty) tt.
Proof.
  intros. reflexivity. Qed. 

(*Mutually recursive type*)

Ltac destruct_option :=
  repeat match goal with
  | H: option ?X |- _ => destruct H
  end.

Ltac simpl_build_base :=
  repeat match goal with
  | H: (build_base ?a ?b ?c ?d) |- _ => simpl in H
  end.


Ltac solve_mut_eq :=
  unfold mk_adts, fin_nth, eq_rect_r; simpl;
  match goal with | |- W ?x ?a ?b = W ?x ?a2 ?b2 =>
    let He := fresh "Heq" in assert (Heq: a = a2);[
      let x := fresh "x" in 
        apply functional_extensionality_dep; intros x; destruct x;
        simpl; reflexivity |
      apply w_eq with (Heq:= He); intros;
      destruct_option; simpl; try reflexivity;
      simpl_build_base; destruct_either;
      try(rewrite cast_left; try reflexivity);
      try (rewrite cast_right; try reflexivity);
      auto]
  end.
(*
  - apply functional_extensionality_dep; intros.
    destruct x; simpl; reflexivity.
  - apply w_eq with(Heq:=H).
    intros.
    destruct i; destruct j; simpl; try reflexivity;
    destruct a; try(rewrite cast_left; try reflexivity);
    try (rewrite cast_right; try reflexivity).
*)

(*A very simple mutually recursive type*)
Inductive mutA : Set :=
  | mk_A1 : mutA
  | mk_A2 : mutB -> mutA
with mutB : Set :=
  | mk_B : mutA -> mutB.

Definition ts_mutA := mk_ts "mutA" nil.
Definition ts_mutB := mk_ts "mutB" nil.
Definition fs_mk_A1 := mk_fs "mk_A1" nil nil ts_mutA nil.
Definition fs_mk_A2 := mk_fs "mk_A2" nil [vty_cons ts_mutB nil] ts_mutA nil.
Definition fs_mk_B := mk_fs "mk_B" nil [vty_cons ts_mutA nil] ts_mutB nil.

Definition mutAB_ctx := [datatype_def [alg_def ts_mutA [fs_mk_A1; fs_mk_A2];
alg_def ts_mutB [fs_mk_B]]].
Definition mutAB_constrs :=
  [(ts_mutA, list_to_ne_list [fs_mk_A1; fs_mk_A2] erefl); 
    (ts_mutB, list_to_ne_list [fs_mk_B] erefl)].

Definition amutAB := mk_adts mutAB_ctx triv_vars triv_syms mutAB_constrs.
Definition amutA := amutAB None.
Definition amutB := amutAB (Some tt).

Lemma amutAB_correct: amutAB =
  W (option unit) (fun x => match x with
                    | None => either unit unit
                    | Some _ => unit
                    end)
  (fun this other x =>
    match this, x with
    | None, Left _ => empty (*First constructor of mutA has no recursive calls*)
    | None, Right  _ => (*Second constructor of mutA has 1 call to mutB*)
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
  unfold amutAB. solve_mut_eq.
Qed.

(*Now we test a mutually recursive constructor*)
Definition a_mk_A2 (b: amutB) := make_constr mutAB_ctx triv_vars triv_syms 
mutAB_constrs None fs_mk_A2 erefl tt
(*creating this map is annoying, need better method*)
(fun x => match x with
          | None => mk_tuple 0 nil erefl
          | Some tt => mk_tuple 1 [b] erefl
          end).

Lemma a_mk_A2_correct: forall (b: amutB),
  a_mk_A2 b = mkW (finite 2) _ _ None (Right _ _ tt) (fun j x =>
    match j, x with
    | Some tt, _ => b
    | None, y => match y with end
    end).
Proof.
  intros. unfold a_mk_A2. prove_constr.
  destruct j.
  - destruct u. reflexivity.
  - destruct b0.
Qed.

(*A simple model of our terms and formulas*)
Inductive tm : Set :=
  | tm_const: Z -> tm
  | tm_if: fmla -> tm -> tm -> tm
with fmla : Set :=
  | fm_eq: tm -> tm -> fmla
  | fm_true : fmla
  | fm_false: fmla.

Definition ts_tm := mk_ts "tm" nil.
Definition ts_fmla := mk_ts "fmla" nil.
Definition fs_tm_const := mk_fs "tm_const" nil [vty_int] ts_tm nil.
Definition fs_tm_if := mk_fs "tm_if" nil [vty_cons ts_fmla nil; vty_cons ts_tm nil;
  vty_cons ts_tm nil] ts_tm nil.
Definition fs_fm_eq := mk_fs "fm_eq" nil [vty_cons ts_tm nil; vty_cons ts_tm nil]
  ts_fmla nil.
Definition fs_fm_true := mk_fs "fm_true" nil nil ts_fmla nil.
Definition fs_fm_false := mk_fs "fm_false" nil nil ts_fmla nil.

Definition tm_fmla_ctx := [datatype_def[alg_def ts_tm [fs_tm_const; fs_tm_if];
  alg_def ts_fmla [fs_fm_eq; fs_fm_true; fs_fm_false]]].

Definition tm_fmla_constrs :=
  [(ts_tm, list_to_ne_list [fs_tm_const; fs_tm_if] erefl); 
   (ts_fmla, list_to_ne_list [fs_fm_eq; fs_fm_true; fs_fm_false] erefl)].

Definition atm_fmla := mk_adts tm_fmla_ctx triv_vars triv_syms 
  tm_fmla_constrs.

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
  unfold atm_fmla. solve_mut_eq.
Qed.

(*Test polymorphism + mutual recursion*)

(*Right now, we support only limited polymorphism + mutual recursion, in the
  following senses:
  1. For any polymorphic inductive type, all recursive instances must have
    the same type parameters
  2. For any mutually-recursive instance, it must also be the case that any recursive
    calls to any inductive type have the same (syntactic) type paramters as
    the definition of that type. For example,
    
    type test1 'a =
    Test1 'a (test2 'a)
    with test2 'a =
    Test2 (test1 'a)

    is allowed, but

    type test3 'a =
    Test3 'a (test4 'a)
    with test4 'b =
    Test4 (test3 'b)
     
    is not.

  Extending this to deal with more sophisticated calls is non-trivial, and can
  quickly extend into full-blown nonuniform recursion. For now, we assume this
  restriction.
  TODO: is this actually restrictive, ie: can we always transform into something
  of this form? Maybe not because of non-uniformity, take for example:
  type test5 'a 'b =
  Test5 (test6 'a) | Test5' (test6 'b)
  with test6 'a =
  A | Test6 (test5 'a 'a)

  where the constraint that 'a = 'b for the test6 argument might not be possible
  to encode.
    *)

(*An encoding of rose trees*)
(*NOTE: in why3, the parameters to mutually recursive types do NOT have
  to be the same, unlike in Coq*)
  Inductive rose (A: Set) : Set :=
  | rnode: A -> treelist A -> rose A
with treelist (A: Set) : Set :=
  | tnil : treelist A
  | tcons: rose A -> treelist A -> treelist A.



Definition ts_rose := mk_ts "rose" [ta].
Definition ts_treelist := mk_ts "treelist" [ta].
Definition fs_rnode := mk_fs "rnode" [ta] 
  [vty_var ta; vty_cons ts_treelist [vty_var ta]]
  ts_rose [ta].
Definition fs_tnil := mk_fs "tnil" [ta] []
  ts_treelist [ta].
Definition fs_tcons := mk_fs "tcons" [ta]
  [vty_cons ts_rose [vty_var ta]; vty_cons ts_treelist [vty_var ta]]
  ts_treelist [ta].

Definition rose_ctx := [datatype_def [alg_def ts_rose [fs_rnode];
  alg_def ts_treelist [fs_tnil; fs_tcons]]].
Definition rose_constrs :=
    [(ts_rose, list_to_ne_list [fs_rnode] erefl);
     (ts_treelist, list_to_ne_list [fs_tnil; fs_tcons] erefl)].

Definition arose_treelist (A: Set) := mk_adts rose_ctx (one_var A) triv_syms
  rose_constrs.
Definition arose (A: Set) := arose_treelist A None.
Definition atreelist (A: Set) := arose_treelist A (Some tt).

Lemma arose_correct (A: Set) : arose_treelist A =
  W (option unit)
  (fun x => match x with
  | None => A
  | Some _ => either unit unit
  end)
  (fun this other x =>
    match this, x with
    | None, _ => (*rose has 1 call to treelist, 0 to rose*)
      match other with
      | None => empty
      | Some _ => unit
      end
    | Some _, Left _ => empty (*tnil has no calls*)
    | Some _, Right _ => unit (*tcons has 1 call to each*)
    end).
Proof.
  unfold arose_treelist. solve_mut_eq.
Qed.

(*Test a constructor with mutual recursive calls and polymorphism.*)
Definition a_tcons (A: Set) (r: arose A) (l: atreelist A) := 
  make_constr rose_ctx (one_var A) triv_syms rose_constrs (Some tt)
  fs_tcons erefl tt
  (fun x => match x with
            | None => mk_tuple 1 [r] erefl
            | Some tt => mk_tuple 1 [l] erefl
            end).

Lemma a_tcons_correct: forall (A: Set) (r: arose A) (l: atreelist A),
  a_tcons A r l = mkW (option unit) _ _ (Some tt) (Right _ _ tt)
  (fun j x =>
    match j, x with
    | None, _ => r
    | Some tt, _ => l
    end).
Proof.
  intros.
  unfold a_tcons. prove_constr. destruct j.
  - destruct u. reflexivity.
  - reflexivity.
Qed. 

End Tests.

End SSReflect.