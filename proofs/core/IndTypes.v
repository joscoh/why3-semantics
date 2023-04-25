Require Export Typing.
Require Import Coq.Lists.List.
Require Export Hlist.
(*For a test, TODO delete*)
Require Import Coq.Reals.Reals.

(*Need eq_rect_eq for injectivity of constructors and test cases*)
Require Import Coq.Program.Equality.
(*Used for constructor existence, injectivity of constructors, and test cases*)
Require Export Coq.Logic.FunctionalExtensionality.
(*We assume [eq_rect_eq], equivalent to UIP, for some proofs*)
Require Import Coq.Logic.EqdepFacts. (*TODO: do we need this*)

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

(*We also want to go from a nat to a finite type*)

Definition lt_to_ssr {m n: nat} (H: (m < n)%coq_nat) : ssrnat.leq (S m) n :=
  introT ltP H.
Definition nat_to_finite {n: nat} (m: nat) (Hm: (m < n)%coq_nat) : finite n :=
  ord_to_finite (fintype.Ordinal (lt_to_ssr Hm)).

Lemma nat_to_finite_inv {n: nat} (m: finite n) 
  (Hm: (finite_to_nat m < n)%coq_nat):
  nat_to_finite (finite_to_nat m) Hm = m.
Proof.
  rewrite /nat_to_finite.
  apply (can_inj finite_ord_cancel).
  rewrite ord_finite_cancel/finite_to_ord.
  f_equal.
  by apply bool_irrelevance.
Qed.

Lemma finite_to_nat_inv {n: nat} (m: nat) (Hm: (m < n)%coq_nat):
  finite_to_nat (nat_to_finite m Hm) = m.
Proof.
  rewrite /nat_to_finite.
  have-: (finite_to_ord (ord_to_finite (fintype.Ordinal (n:=n) (m:=m) (lt_to_ssr Hm))) =
  fintype.Ordinal (lt_to_ssr Hm)) by rewrite ord_finite_cancel.
  rewrite /finite_to_ord => Hord.
  by apply (f_equal (@nat_of_ord n)) in Hord.
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

Lemma fin_nth_aux_irrel: forall {A: Type} {n: nat} {l: list A}
  (Hl1 Hl2: length l = n) (x: finite n),
  fin_nth_aux l Hl1 x = fin_nth_aux l Hl2 x.
Proof.
  intros A n. induction n; simpl; intros; subst.
  - destruct x.
  - destruct l.
    + inversion Hl1.
    + destruct n.
      * destruct x; reflexivity.
      * destruct x.
        -- simpl. apply IHn.
        -- reflexivity.
Qed.

Lemma fin_nth_aux_in: forall {A: Type} {n: nat} {l: list A}
  (Hl: length l = n) (x : finite n),
  In (fin_nth_aux l Hl x) l.
Proof.
  intros A n. induction n; simpl; intros; subst.
  - destruct x.
  - destruct l.
    + inversion Hl.
    + destruct n.
      * destruct x; simpl. left; auto.
      * destruct x.
        -- simpl. right. apply IHn.
        -- left. reflexivity.
Qed.

Lemma fin_nth_aux_inj: forall {A: Type} {n: nat} {l: list A}
  (Hn: NoDup l)
  (H1 H2: length l = n) (x y: finite n),
  fin_nth_aux l H1 x = fin_nth_aux l H2 y ->
  x = y.
Proof.
  intros A n. induction n; simpl; intros; subst.
  - destruct x.
  - destruct l.
    + inversion H1.
    + destruct n.
      * destruct x; destruct y. reflexivity.
      * assert (~ In a l) by (inversion Hn; auto).
        destruct x; destruct y; auto; simpl in H.
        -- f_equal. eapply IHn. 2: apply H.
          inversion Hn; subst; auto.
        -- rewrite <- H in H0.
          exfalso. apply H0.
          apply fin_nth_aux_in.
        -- rewrite H in H0.
          exfalso. apply H0.
          apply fin_nth_aux_in.
Qed.

Definition fin_nth {A: Type} (l: list A): finite (length l) -> A :=
  fin_nth_aux l erefl.

Lemma fin_nth_in: forall {A: Type} (l: list A) (n: finite (length l)),
  In (fin_nth l n) l.
Proof.
  intros. apply fin_nth_aux_in.
Qed.

Lemma fin_nth_aux_map {n: nat} {A B: Type} (f: A -> B)
  (l: list A) (x: finite n) (Hn: length l = n) (Hn2: length (map f l) = n) :
  f (fin_nth_aux l Hn x) = fin_nth_aux (map f l) Hn2 x.
Proof.
  generalize dependent l.
  revert x f.
  induction n; simpl; intros; subst.
  - destruct x.
  - destruct l.
    + inversion Hn.
    + destruct n.
      * destruct x. reflexivity.
      * destruct x.
        -- rewrite IHn. simpl in Hn. inversion Hn. rewrite map_length.
           reflexivity.
           intros. simpl.
           apply fin_nth_aux_irrel.
        -- reflexivity.
Qed. 

(*Convert between elements in a list and finite values*)
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

Lemma fin_nth_inj {l: list A} ( x y: finite (length l)) :
  NoDup l ->
  fin_nth l x = fin_nth l y ->
  x = y.
Proof.
  intros.
  apply fin_nth_aux_inj in H0; subst; auto.
Qed.
    
(*The other direction of the inverse proof*)
Lemma get_idx_fin {l: list A} {x: finite (length l)} 
  (Hl: NoDup l)
  (Hin: in_bool eq_dec (fin_nth l x) l) :
  get_idx (fin_nth l x) l Hin = x.
Proof.
  apply fin_nth_inj. auto.
  rewrite get_idx_correct. reflexivity.
Qed.

End InFin.

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

Definition tup_of_list {A: Type} {n: nat} {l: list A} (Hl: length l = n) :
  n.-tuple A := (Tuple (introT eqP Hl)).

Lemma nth_equiv {A: Type} (d: A) (l: list A) (i: nat):
  nth d l i = List.nth i l d.
Proof.
  move: l. elim: i => [/= [// | //]| n' IH [// | h tl /=]].
  by apply IH.
Qed.

Lemma tnthS_tup_of_list {A: Type} {n: nat} (l: list A) 
  (Hl: length l = n) (d: A) (i: nat) (Hi: (i < n)%coq_nat):
  tnthS (tup_of_list Hl) (nat_to_finite i Hi) = List.nth i l d.
Proof.
  by rewrite /tup_of_list tnthS_equiv 
    (@tnth_nth _ _ d)/= finite_to_nat_inv nth_equiv.
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

(*Now, we come to the construction. We do this in 3 parts:
  1. Build up the base type (A)
  2. Build up the function (A -> Set)
  3. Put together*)
Section ADTConstr.

Variable vars: typevar -> Set.
Variable abstract: forall (t: typesym), list vty -> Set.

Section Full.

Variable m: list alg_datatype.

(*Variable gamma: context.*)

(*Variable abstract_wf: forall (t: typesym) (l: list vty),
  length l <> length (ts_args t) ->
  abstract t l = empty.*)

(*Construct the base type*)

(*Filter out the inductive types*)
(*TODO: I think this should ONLY count types in current mut type*)
Definition get_nonind_vtys (l: list vty) : list vty :=
  filter (fun v => match v with 
                    | vty_cons ts vs =>
                      ~~ (ts_in_mut_list ts m)
                    | _ => true
                    end) l.

Fixpoint big_sprod (l: list Set) : Set :=
  match l with
  | nil => unit
  | [x] => x
  | x :: xs => (x * (big_sprod xs))%type
  end.

Definition vty_to_set (v: vty) : Set :=
  match v with
  | vty_int => Z
  | vty_real => QArith_base.Q
  | vty_var x => vars x
  | vty_cons ts vs => abstract ts vs
  end.

Definition build_vty_base (l: list vty) : Set :=
  big_sprod (map vty_to_set (get_nonind_vtys l)).

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
  | ne_cons hd tl => Either (build_constr_base hd) (build_base tl)
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
  Definition count_rec_occ_aux (l: list vty) (ts: typesym) (c: funsym) :=
    length (filter (rec_occ_fun ts) l).

Definition count_rec_occ (ts: typesym) (c: funsym) :=
  count_rec_occ_aux (s_args c) ts c.

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
Definition mk_adts : finite (length m) -> Set :=
  W (finite (length m)) (fun n => build_base (adt_constrs (fin_nth m n)))
    (fun (this: finite _) (i: finite _) => 
      build_rec (adt_name (fin_nth m i))
        (adt_constrs (fin_nth m this))).

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
(*TODO: change to cast*)
(*
Lemma build_rec_finite_inj: forall {ts ts': typesym} {constrs: ne_list funsym}
{f: funsym} {Hin: in_bool_ne funsym_eq_dec f constrs}
{c1 c2: build_constr_base f}
(x1: build_rec ts' constrs (get_constr_type ts constrs f Hin c1))
(x2: build_rec ts' constrs (get_constr_type ts constrs f Hin c2)),
@build_rec_to_finite ts ts' constrs f Hin c1 x1 =
@build_rec_to_finite ts ts' constrs f Hin c2 x2.
Proof.
  intros. induction constrs; simpl in Hin, x1, x2.
  - simpl. destruct (funsym_eq_dec f a) ; subst; auto.
    unfold eq_rec_r, eq_rec, eq_rect. simpl.
    
    reflexivity.
    *)

(*Finally, create the constructor encoding: given a mutually recursive type,
  an index into the type, a constructor in the constructors of that index,
  and the arguments to the constructor (recursive and non-recursive), we encode
  the constructor such that the function matches on the mutually recursive index and
  an instance, uses
  the fact that this is equivalent to just the number of recursive occurrences of
  this index, and constructs a finite mapping; ie: applying the nth argument to the
  nth recursive call.*)

Definition make_constr (n: finite (length m))
  (f: funsym)
  (Hin: in_bool_ne funsym_eq_dec f (adt_constrs (fin_nth m n)))
  (c: build_constr_base f)
  (recs: forall (x: finite (length m)), 
    (count_rec_occ (adt_name (fin_nth m x)) f).-tuple (mk_adts x)) :
  mk_adts n := mkW (finite (length m)) _ _ n 
    (get_constr_type (adt_name (fin_nth m n)) _ f Hin c)
    (fun j H => tnthS (recs j) (build_rec_to_finite H)).

End Full.

Section Simple.

(*For non-mutually-recursive-types *)
Definition mk_adt (ts: typesym) (constrs: ne_list funsym) : Set :=
  mk_adts [alg_def ts constrs] tt.

Definition make_constr_simple (ts: typesym) (constrs: ne_list funsym) (f: funsym)
(Hin: in_bool_ne funsym_eq_dec f constrs)
(c: build_constr_base [alg_def ts constrs] f)
(recs: (count_rec_occ ts f).-tuple (mk_adt ts constrs)) :
mk_adt ts constrs.
Proof.
  apply (make_constr [alg_def ts constrs] tt f Hin c).
  intros x. destruct x. apply recs.
Defined.

End Simple.

(* Theorems about ADTs*)
Section Theorems.

Variable m : list alg_datatype.

(*From an instance b of [build_base l], we can get the constructor corresponding to
  this, as well as the [build_constr_base f] that is wrapped inside b.*)
Definition get_funsym_base (ts: typesym) 
  (l: ne_list funsym) (Huniq: nodupb funsym_eq_dec (ne_list_to_list l)) 
  (b: build_base m l) :
  { f: funsym & {Hin: in_bool_ne funsym_eq_dec f l & 
    {b1: build_constr_base m f | b = get_constr_type m ts l f Hin b1}}}.
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
Definition find_constr: forall (n: finite (length m))
  (Huniq: forall constrs, In constrs (map adt_constrs m) -> 
    nodupb funsym_eq_dec (ne_list_to_list constrs))
  (x: mk_adts m n),
  {f: funsym & {t: in_bool_ne funsym_eq_dec f (adt_constrs (fin_nth m n)) * build_constr_base m f *
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
      (fun n : finite (Datatypes.length m) => build_base m (adt_constrs (fin_nth m n)))
      (fun this i : finite (Datatypes.length m) =>
       build_rec m (adt_name (fin_nth m i)) (adt_constrs (fin_nth m this))) j). {
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
  (c1: build_constr_base m f1)
  (c2: build_constr_base m f2),
  get_constr_type m ts constrs f1 Hin1 c1 = get_constr_type m ts constrs f2 Hin2 c2 ->
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
  (c1: build_constr_base m f)
  (c2: build_constr_base m f),
  get_constr_type m ts constrs f Hin c1 = get_constr_type m ts constrs f Hin c2 ->
  c1 = c2.
Proof.
  intros. induction constrs; simpl in Hin; simpl in H; destruct (funsym_eq_dec f a);
  subst; auto; try solve[inversion Hin]; inversion H; auto.
  apply (IHconstrs Hin H1).
Qed.

(*Second result: no two different constructors, no matter their arguments, can
  produce the same instance of the W-type (no axioms needed)*)
Lemma constrs_disjoint: forall (n: finite (length m))
  (f1 f2: funsym) (Hin1: in_bool_ne funsym_eq_dec f1 (adt_constrs (fin_nth m n)))
  (Hin2: in_bool_ne funsym_eq_dec f2 (adt_constrs (fin_nth m n)))
  (c1: build_constr_base m f1)
  (c2: build_constr_base m f2)
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
  intros. destruct H. reflexivity. 
Defined.

(*3. Constructors are injective (this needs eq_rect_eq (UIP))*)
Lemma constrs_inj: forall (n: finite (length m))
  (f: funsym) (Hin: in_bool_ne funsym_eq_dec f (adt_constrs (fin_nth m n)))
  (c1 c2: build_constr_base m f)
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
  apply fun_args_eq_dep with (x:=(finite_to_build_rec m (ord_to_finite y))) in x.
  rewrite build_rec_finite_inv2 in x. apply x.
Qed.

End Theorems.

End ADTConstr.

Ltac destruct_list :=
  match goal with
  | |- context [ match ?l with | nil => ?x1 | a :: b => ?x2 end] =>
    destruct l 
  end.



(*Facilities to build ADTs*)
Section Build.

(*We provide a nicer interface to build an AST, using a context,
  function symbols, and the like rather than finite values and ne_lists.
  This way, in the semantics, we don't need to worry about the 
  specifics of W-types, finite types, etc, but rather we can work
  at the higher level of the context and function symbols and just have
  an API for working with ADT representations.*)
Context {s: sig} {gamma: context}.
Variable gamma_valid: valid_context s gamma.

Variable m : mut_adt.
Definition adts := typs m.

Variable m_in : mut_in_ctx m gamma.

Variable srts : list Types.sort.

Variable srts_len: length srts = length (m_params m).

Definition sigma : vty -> Types.sort :=
  ty_subst_s (m_params m)  srts.

Variable domain_aux: Types.sort -> Set.

Definition domain (s: Types.sort) : Set :=
  match sort_to_ty s with
  | vty_int => Z
  | vty_real => QArith_base.Q
  | _ => domain_aux s
  end.

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
 := mk_adts var_map typesym_map adts
  (get_idx adt_dec a adts a_in).

(*Now we want to make an interface for the constructor. This is harder.*)
(*We need to build the [build_constr_base] and the recursive map.
  We can do this by filtering the input [arg_list], which is not
  conceptually difficult, but involves lots of annoying dependent types*)

(*The ADT we want to build the constructor for*)
Variable t: alg_datatype.
Variable t_in: adt_in_mut t m.

Section Constr.

Variable c: funsym.
Variable c_in : constr_in_adt c t.

Definition arg_list (domain: Types.sort -> Set) := hlist domain.

Definition sigma_args : list Types.sort :=
  map sigma (s_args c).

Definition sigma_ret: Types.sort :=
  sigma (f_ret c).

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

(*The function to build the constr_base, built with tactics*)

(*Need aux version so that l is sufficiently general for induction*)

Definition sigma_aux (l: list vty) := map sigma l.
Lemma sigma_aux_args: sigma_aux (s_args c) = sigma_args.
Proof. reflexivity. Qed.

Definition domain_sigma_int_Z (x: domain (sigma vty_int)) : Z.
rewrite sigma_int in x. exact x.
Defined.

(*TODO: should we move this somewhere else?*)
Section DomCast.

Definition dom_cast {v1 v2: Types.sort} (Heq: v1 = v2) (x: domain v1) : 
  domain v2 :=
  scast (f_equal domain Heq) x.

Lemma dom_cast_twice: forall {v1 v2: Types.sort} (Heq: v1 = v2) x,
  dom_cast Heq (dom_cast (esym Heq) x) = x.
Proof.
  intros. destruct Heq; reflexivity.
Qed.

Lemma dom_cast_inj: forall {v1 v2: Types.sort} (Heq: v1 = v2) (x1 x2: domain v1),
  dom_cast Heq x1 = dom_cast Heq x2 ->
  x1 = x2.
Proof.
  intros. destruct Heq. apply H.
Qed.

Lemma dom_cast_compose {s1 s2 s3: Types.sort}
  (Heq1: s2 = s3) (Heq2: s1 = s2) x:
  dom_cast Heq1 (dom_cast Heq2 x) =
  dom_cast (eq_trans Heq2 Heq1) x.
Proof.
  subst. reflexivity.
Qed.

Lemma dom_cast_eq {s1 s2: Types.sort} (H1 H2: s1 = s2) x:
  dom_cast H1 x = dom_cast H2 x.
Proof.
  subst. unfold dom_cast. simpl.
  assert (H2 = erefl). apply UIP_dec. apply sort_eq_dec.
  rewrite H.
  reflexivity.
Qed.

Lemma dom_cast_refl {s1} (H: s1 = s1) x:
  dom_cast H x = x.
Proof.
  assert (H = erefl). apply UIP_dec. apply sort_eq_dec.
  subst; reflexivity.
Qed.

Lemma rewrite_dom_cast: forall (v1 v2: Types.sort) (Heq: v1 = v2)
  x,
  scast (f_equal domain Heq) x = dom_cast Heq x.
Proof.
  intros. reflexivity.
Qed.

End DomCast.

Definition args_to_constr_base_aux (l: list vty) 
  (a: arg_list domain (sigma_aux l)) :
  build_vty_base var_map typesym_map adts l.
Proof.
  induction l.
  - exact tt.
  - unfold build_vty_base in *. simpl.
    set (Hd:=hlist_hd a).
    set (Hal:=hlist_tl a).
    destruct a0.
    + exact (build_sprod_cons Hd (IHl Hal)).
    + exact (build_sprod_cons Hd (IHl Hal)). 
    + exact (build_sprod_cons Hd (IHl Hal)).
    + generalize dependent (ts_in_mut_list t0 adts); intros b.
      destruct b.
      * exact (IHl Hal).
      * exact (build_sprod_cons (dom_cast (sigma_cons t0 l0) Hd) (IHl Hal)).
Defined.

Definition args_to_constr_base (a: arg_list domain sigma_args):
  build_constr_base var_map typesym_map adts c :=
  args_to_constr_base_aux (s_args c) a.

(*Part 2: build the recursive arguments*)

(*We assume that the domain of all adts is given by [adt_rep]
  (which we will require of all possible valid domains)*)
Variable dom_adts: forall (a: alg_datatype) (Hin: adt_in_mut a m),
  domain (typesym_to_sort (adt_name a) srts) =
  adt_rep a Hin.

(*A more convenient format for us in proofs:*)
Lemma dom_adts_fin: forall (x: finite (length adts)),
  domain (typesym_to_sort (adt_name (fin_nth adts x)) srts) =
  mk_adts var_map typesym_map adts x.
Proof.
  intros. rewrite dom_adts. apply In_in_bool. apply fin_nth_in.
  intros Hin.
  unfold adt_rep.
  f_equal.
  rewrite get_idx_fin. reflexivity.
  apply (adts_nodups gamma_valid m_in).
Qed.

(*Now we need some intermediate results about casting (some are not
  used until later)*)
(*TODO: move?*)
Section Cast.
(*Cast a list - can't use scast bc list is Type -> Type*)
Definition cast_list {A B: Set} (l: list A) (Heq: A = B) : list B :=
  match Heq with
  | erefl => l
  end.

Lemma cast_list_length: forall {A B: Set} (l: list A) (Heq: A = B),
  length (cast_list l Heq) = length l.
Proof.
  intros. unfold cast_list. destruct Heq. reflexivity.
Qed.

Lemma cast_nil: forall {A B} (H: A = B),
  cast_list nil H = nil.
Proof.
  intros. unfold cast_list. destruct H. reflexivity.
Qed. 

Lemma cast_list_cons: forall {A B: Set} (x: A)(l: list A) (Heq: A = B),
  cast_list (x :: l) Heq = scast Heq x :: cast_list l Heq.
Proof.
  intros. subst. reflexivity.
Qed.

Lemma cast_list_inj: forall {A B: Set} {l1 l2: seq A}(Heq: A = B),
  cast_list l1 Heq = cast_list l2 Heq ->
  l1 = l2.
Proof.
  intros. destruct Heq. simpl in H. subst; auto.
Qed.

Lemma cast_list_nth: forall {A B: Set} (l: list A) (Heq: A = B)
  (d': B)
  (i: nat),
  List.nth i (cast_list l Heq) d' = 
    scast Heq (List.nth i l (scast (Logic.eq_sym Heq) d')).
Proof.
  intros. subst. reflexivity.
Qed. 


(*Cast an [arg_list] - here we use a type with decidable equality*)
Definition cast_arg_list {domain: Types.sort -> Set} {l1 l2}
  (Heq: l1 = l2) (x: arg_list domain l1) : arg_list domain l2 :=
  scast (f_equal (fun x => arg_list domain x) Heq) x.

Lemma cast_arg_list_twice {domain: Types.sort -> Set} {l1 l2}
  (Heq: l1 = l2) (x: arg_list domain l2) :
  cast_arg_list Heq (cast_arg_list (esym Heq) x) = x.
Proof.
  destruct Heq. reflexivity.
Qed.

Lemma cast_arg_list_eq {d: Types.sort -> Set} {l1 l2: list Types.sort} (Heq1 Heq2: l1 = l2) 
  (a: arg_list d l1):
  cast_arg_list Heq1 a = cast_arg_list Heq2 a.
Proof.
  subst. assert (Heq2 = erefl). apply UIP_dec. apply list_eq_dec.
  apply sort_eq_dec. subst. reflexivity.
Qed.

Lemma cast_arg_list_inj: forall {domain: Types.sort -> Set} 
  {l1 l2: list Types.sort} (Heq: l1 = l2) (a1 a2: arg_list domain l1),
  cast_arg_list Heq a1 = cast_arg_list Heq a2 ->
  a1 = a2.
Proof.
  intros. destruct Heq. apply H.
Qed.

Definition cast_nth_eq {A: Set} {l1 l2: list A} (Heq: l1 = l2)
  (i: nat) (d: A) : List.nth i l1 d = List.nth i l2 d :=
  f_equal (fun (x: list A) => List.nth i x d) Heq.

Lemma hnth_cast_arg_list {domain: Types.sort -> Set} {l1 l2}
(Heq: l1 = l2) (x: arg_list domain l1) (i: nat) (d: Types.sort)
  (d1: domain d):
  hnth i (cast_arg_list Heq x) d d1 =
  scast (f_equal domain (cast_nth_eq Heq i d)) (hnth i x d d1).
Proof.
  destruct Heq. reflexivity.
Qed.

Lemma cons_inj_hd {A: Type} {x y: A} {l1 l2: list A}
  (C: x :: l1 = y :: l2):
  x = y.
Proof.
  injection C; auto.
Defined.

Lemma cons_inj_tl {A: Type} {x y : A} {l1 l2: list A}:
  x :: l1 = y :: l2 ->
  l1 = l2.
Proof.
  intros C. injection C. auto.
Defined.

Lemma cast_arg_list_cons {h1 h2: Types.sort} {d: Types.sort -> Set} {s1 s2: list Types.sort} 
  {x} {a}
  (Heq: h1 :: s1 = h2 :: s2):
  cast_arg_list Heq (HL_cons _ h1 s1 x a) =
  HL_cons d h2 s2 (scast (f_equal d (cons_inj_hd Heq)) x) 
    (cast_arg_list (cons_inj_tl Heq) a).
Proof.
  inversion Heq. subst.
  assert (Heq = erefl).
  apply UIP_dec. apply list_eq_dec. apply sort_eq_dec.
  subst. reflexivity. 
Qed.

Lemma hlist_tl_cast {d} {s1 s2: Types.sort} {t1 t2: list Types.sort}  
  (Heq: (s1:: t1) = (s2:: t2)) a:
  hlist_tl (cast_arg_list Heq a) = 
    @cast_arg_list d _ _ (cons_inj_tl Heq) (hlist_tl a).
Proof.
  inversion Heq. subst.
  assert (Heq = erefl). apply UIP_dec. apply list_eq_dec.
    apply sort_eq_dec. subst. reflexivity.
Qed.

Lemma hlist_hd_cast {d: Types.sort -> Set} 
  {s1 s2: Types.sort} {t1 t2: list Types.sort}
  {a: arg_list d (s1 :: t1)}
  (Heq1: s1 :: t1 = s2 :: t2)
  (Heq2: s1 = s2):
  hlist_hd (cast_arg_list Heq1 a) =
  scast (f_equal d Heq2) (hlist_hd a).
Proof.
  subst. inversion Heq1; subst.
  assert (Heq1 = erefl).
    apply UIP_dec. apply list_eq_dec. apply sort_eq_dec.
  subst. reflexivity.
Qed. 

Lemma cast_arg_list_compose {d: Types.sort -> Set} 
  {l1 l2 l3: list Types.sort} (Heq: l1 = l2)
  (Heq2: l2 = l3)
  (x: arg_list d l1):
  cast_arg_list Heq2 (cast_arg_list Heq x) =
  cast_arg_list (eq_trans Heq Heq2) x.
Proof.
  unfold cast_arg_list. rewrite scast_scast.
  rewrite eq_trans_map_distr. reflexivity.
Qed.

End Cast.

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
Lemma filter_args_same (l: list vty) (x: finite (length adts)) :
  Forall (fun y => y = typesym_to_sort (adt_name (fin_nth adts x)) srts)
    (List.map sigma (List.filter (rec_occ_fun (adt_name (fin_nth adts x)))
      l)).
Proof.
  set (ts:= (adt_name (fin_nth adts x))) in *.
  apply Forall_forall. intros s' Hins'.
  rewrite in_map_iff in Hins'. destruct Hins' as [v [Hv Hinv]]; subst.
  rewrite in_filter in Hinv. destruct Hinv.
  unfold rec_occ_fun in H. destruct v; try solve[inversion H].
  apply andb_prop in H. destruct H.
  destruct (typesym_eq_dec t0 ts); subst; try solve[inversion H].
  clear H.
  destruct (list_eq_dec vty_eq_dec l0 [seq vty_var i | i <- ts_args ts]);
    subst; try solve[inversion H1]. clear H1.
  rewrite sigma_cons. f_equal.
  assert (ts_args ts = m_params m). {
    subst ts. apply (@adt_args s gamma gamma_valid).
    unfold adt_mut_in_ctx. split; auto.
    apply In_in_bool. apply fin_nth_in.
  }
  rewrite H.
  rewrite <- map_comp. apply subst_same. 
  rewrite srts_len; reflexivity.
  clear -m. (*TODO: separate lemma*)
  destruct m; simpl. apply /nodup_NoDup. apply m_nodup.
Qed.

(*Part 2: The length of the casted list (casted from domain _ to a
  W-type via the [dom_adts] assumption) is correct*)
Lemma filter_args_length (l: list vty) (a: arg_list domain (sigma_aux l)) 
  (x: finite (length adts)) :
  length (
    cast_list (
      hlist_to_list (
        hlist_map_filter sigma a 
          (rec_occ_fun (adt_name (fin_nth adts x)))
        )
        (filter_args_same l x)
    ) 
  (dom_adts_fin x)) = count_rec_occ_aux l (adt_name (fin_nth adts x)) c.
Proof.
  rewrite cast_list_length hlist_to_list_length hlength_eq map_length.
  reflexivity.
Qed.

Definition args_to_ind_base_aux (l: list vty) 
  (a: arg_list domain (sigma_aux l)) :
  forall (x: finite (length adts)), 
    (count_rec_occ_aux l (adt_name (fin_nth adts x)) c).-tuple
      (mk_adts var_map typesym_map adts x) :=
  fun x => tup_of_list (filter_args_length l a x).

(*The final function is easy: just make a tuple from the list
  which we already proved has the correct length in the last lemma.
  This hides the ugly proofs.*)
Definition args_to_ind_base (a: arg_list domain sigma_args) :
  forall (x: finite (length adts)), 
    (count_rec_occ (adt_name (fin_nth adts x)) c).-tuple
      (mk_adts var_map typesym_map adts x) :=
  args_to_ind_base_aux (s_args c) a.

(* The interesting part is done, but we need to cast the result from
  an [adt_rep] to an element of the appropriate domain. We need
  a few lemmas to do this, mainly about substitution. *)

(*TODO: where to put?*)
Definition sym_sigma_args (sym: fpsym) (s: list Types.sort) : list Types.sort :=
  ty_subst_list_s (s_params sym) s (s_args sym).
(*Definition funsym_sigma_args (f: funsym) (s: list Types.sort) : list Types.sort :=
  ty_subst_list_s (s_params f) s (s_args f).*)

(*More casting we need: TODO: should it go here or elsewhere?*)
Definition funsym_sigma_ret (f: funsym) (s: list Types.sort) : Types.sort :=
  ty_subst_s (s_params f) s (f_ret f).

Lemma adt_typesym_funsym:
  typesym_to_sort (adt_name t) srts = funsym_sigma_ret c srts.
Proof.
  unfold funsym_sigma_ret, typesym_to_sort.
  apply sort_inj; simpl.
  rewrite (adt_constr_ret gamma_valid m_in t_in); auto.
  simpl. f_equal.
  rewrite <- subst_same at 1.
  2: symmetry; apply srts_len.
  rewrite -!map_comp.
  apply map_ext_in_iff.
  intros. simpl. f_equal. symmetry.
  apply (adt_constr_params gamma_valid m_in t_in c_in).
  clear -m. destruct m; simpl.
  apply /nodup_NoDup. apply m_nodup.
Qed. 

Lemma sigma_args_eq: sym_sigma_args c srts = sigma_args.
Proof.
  unfold sym_sigma_args. unfold sigma_args.
  unfold ty_subst_list_s.
  unfold sigma.
  assert (s_params c = m_params m). {
    eapply adt_constr_params; eassumption. 
  }
  rewrite H. reflexivity.
Qed. 

(*One lemma we need for [constr_rep]*)
Lemma constr_in_lemma :
     (in_bool_ne funsym_eq_dec c
        (adt_constrs
           (fin_nth adts 
            (get_idx adt_dec t adts t_in)))).
Proof.
  rewrite get_idx_correct. apply c_in.
Qed.

(*Now we can build the constructor corresponding to the function
  symbol c using the two functions from before*)
Definition constr_rep (a: arg_list domain (sym_sigma_args c srts)) :
  adt_rep t t_in :=
  make_constr _ _ _ _ _ constr_in_lemma 
    (args_to_constr_base (cast_arg_list sigma_args_eq a))
    (args_to_ind_base (cast_arg_list sigma_args_eq a)).

(*We cast the result to the appropriate domain for the semantics*)
Definition constr_rep_dom (a: arg_list domain (sym_sigma_args c srts)) :
  domain (funsym_sigma_ret c srts) := 
  scast 
    (*equality proof*)
    (etrans (esym (dom_adts t t_in)) 
      (f_equal domain adt_typesym_funsym)
    ) 
    (*the real value*)
    (constr_rep a).

(*Now comes the second part: the inverse function (ie: go from a
  constr_base and a function to an arg_list). This is a lot trickier
  to define and the inverse proof is not easy*)
Section Inv.

Variable m_unif: uniform m.

(*Lemmas and definitions we need for the inverse function:*)

Lemma adt_names_inj: forall x y,
  adt_name (fin_nth adts x) = adt_name (fin_nth adts y) ->
  x = y.
Proof.
  intros. assert (NoDup (map adt_name adts)). {
    apply (adts_names_nodups gamma_valid). assumption. 
  }
  unfold fin_nth in H.
  assert (length (map adt_name adts) = length adts). {
    rewrite map_length. reflexivity.
  }
  rewrite -> !fin_nth_aux_map with(f:=adt_name)(Hn2:=H1) in H.
  apply fin_nth_aux_inj in H; auto.
Qed.

Definition safehead {A: Type} (l: list A) (Hl: 0 < length l) : A.
destruct l.
- exact (False_rect _ (not_false Hl)).
- exact a.
Defined.

Lemma safehead_tl: forall {A: Type} (l: list A) (Hl: 0 < length l),
  safehead l Hl :: tl l = l.
Proof.
  intros. destruct l; try reflexivity.
  inversion Hl.
Qed.

Lemma tl_len {A: Type} (l: list A): length (tl l) = (length l).-1.
Proof.
  destruct l; reflexivity.
Qed.

(*Dealing with the function in the recursive case is hard. When
  we have a mutually recursive instance, we need to update the
  function appropriately. We do that below; this is a lemma we need*)
Lemma split_arg_func_lemma1 (ts: typesym) l0 l a
(Hl0: l0 = [seq vty_var i | i <- m_params m])
(f: forall x, list (mk_adts var_map typesym_map adts x))
(Hf: forall x: finite (length adts), length (f x) = 
    count_rec_occ_aux (vty_cons ts l0 :: l) (adt_name (fin_nth adts x)) c)
(Htsa: ts = adt_name a)
    (Hina: adt_in_mut a m):
    0 < length (f (get_idx adt_dec _ _ Hina)).
Proof.
  rewrite Hf. rewrite get_idx_correct. unfold count_rec_occ_aux. simpl.
    destruct (typesym_eq_dec ts (adt_name a)); auto; try contradiction.
    assert (l0 = [seq vty_var i | i <- ts_args (adt_name (fin_nth adts (get_idx adt_dec _ _  Hina)))]).
    {
      subst. 
      rewrite get_idx_correct. f_equal. symmetry.
      apply (adt_args gamma_valid). split; assumption.
    }
    rewrite get_idx_correct in H.
    destruct (list_eq_dec vty_eq_dec l0 [seq vty_var i | i <- ts_args (adt_name a)]); try contradiction.
    simpl. by [].
Qed.

Lemma split_arg_func_lemma2 (ts: typesym) l0
(Hl0: l0 = [seq vty_var i | i <- m_params m]):
    [seq sigma i | i <- l0] = srts.
Proof.
  unfold sigma. subst. rewrite -map_comp. unfold "\o".
    apply subst_same. rewrite srts_len; auto.
    clear -m. (*TODO: separate lemma*)
    destruct m; simpl. apply /nodup_NoDup. apply m_nodup.
Qed.

Lemma get_ind_arg (ts: typesym) l0 l a Hina
(Hta: ts = adt_name a)
(Hl0: l0 = [seq vty_var i | i <- m_params m])
(Heq: domain (sigma (vty_cons ts l0)) = adt_rep a Hina)
(f: forall x, list (mk_adts var_map typesym_map adts x))
(Hf: forall x: finite (length adts), length (f x) = 
    count_rec_occ_aux (vty_cons ts l0 :: l) (adt_name (fin_nth adts x)) c):
(domain (sigma (vty_cons ts l0))).
Proof.
  exact (scast (esym Heq) 
    (safehead _ (split_arg_func_lemma1 ts l0 l a Hl0 f Hf Hta Hina))).
Defined.

(*The updated function - proof is below*)
Definition split_arg_func (ts: typesym) l0 l
(Hts: ts_in_mut_list ts adts)
(Hl0: l0 = [seq vty_var i | i <- m_params m])
(f: forall x, list (mk_adts var_map typesym_map adts x))
(Hf: forall x: finite (length adts), length (f x) = 
    count_rec_occ_aux (vty_cons ts l0 :: l) (adt_name (fin_nth adts x)) c):
(forall x, list (mk_adts var_map typesym_map adts x)).
Proof.
  apply ts_in_mut_list_ex in Hts.
  destruct Hts as [a [Ha Hina]].
  intros x.
    (*specialize (f x).*)
    (*2 cases; x = idx of a and not*)
    destruct (finite_eq_dec _ x (get_idx adt_dec _ _ Hina)).
    + exact (tl (f x)).
    + exact (f x).
Defined.

(*This proof is ugly but we make it opaque*)
Lemma split_arg_func_invar (ts: typesym) l0 l
(Hts: ts_in_mut_list ts adts)
(Hl0: l0 = [seq vty_var i | i <- m_params m])
(f: forall x, list (mk_adts var_map typesym_map adts x))
(Hf: forall x: finite (length adts), length (f x) = 
    count_rec_occ_aux (vty_cons ts l0 :: l) (adt_name (fin_nth adts x)) c):
forall x, length (split_arg_func ts l0 l Hts Hl0 f Hf x) =
  count_rec_occ_aux l (adt_name (fin_nth adts x)) c.
Proof.
  intros. unfold split_arg_func. simpl.
  destruct (ts_in_mut_list_ex ts m Hts). destruct a. simpl.
  unfold count_rec_occ_aux in *.
  simpl in Hf.
  specialize (Hf x).
  destruct (typesym_eq_dec ts (adt_name (fin_nth adts x))).
  - assert (x0 = fin_nth adts x). {
      subst. assert (x0 = fin_nth adts (get_idx adt_dec x0 adts i)). {
        rewrite get_idx_correct. reflexivity.
      }
      rewrite H in e.
      apply adt_names_inj in e. subst. rewrite get_idx_correct.
      reflexivity.
    }
    destruct ( list_eq_dec vty_eq_dec l0
    [seq vty_var i | i <- ts_args (adt_name (fin_nth adts x))]).
    + destruct (finite_eq_dec (Datatypes.length adts) x
    (get_idx adt_dec x0 (typs m) i)).
      * simpl in Hf. rewrite tl_len Hf. reflexivity.
      *  subst. exfalso. apply n. rewrite get_idx_fin. reflexivity.
        apply (adts_nodups gamma_valid). apply m_in.
    + (*contradicts uniformity*)
      subst. exfalso. apply n. f_equal. symmetry. apply (adt_args gamma_valid).
      split; auto.
  - subst. destruct (finite_eq_dec (Datatypes.length adts) x
      (get_idx adt_dec x0 (typs m) i)).
    + subst. exfalso. apply n. rewrite get_idx_correct. reflexivity.
    + simpl in Hf. apply Hf.
Qed. 

(*If the typesym is not a recursive instance, we have the following:*)
Lemma args_func_false_case1: forall (x: finite (Datatypes.length adts)) ts,
ts_in_mut_list ts adts = false -> 
proj_sumbool _ _ (typesym_eq_dec ts (adt_name (fin_nth adts x))) = false.
Proof.
  intros.
  destruct (typesym_eq_dec ts (adt_name (fin_nth adts x))); auto.
  assert (ts_in_mut_list ts adts = true). {
    apply ts_in_mut_list_spec. exists (fin_nth adts x). split; auto.
    apply In_in_bool. apply fin_nth_in.
  }
  rewrite H0 in H; inversion H.
Qed.

Definition is_nonind (v: vty) :=
  match v with
  | vty_cons t0 _ => negb (ts_in_mut_list t0 adts)
  | _ => true
  end.

(*Break apart a [big_sprod] without explicitly destructing, which
  causes dependent type issues*)
Definition get_sprod_parts {a l} (Ha: is_nonind a)
  (x: big_sprod
  [seq vty_to_set var_map typesym_map i
     | i <- get_nonind_vtys adts (a :: l)]) :
  domain (sigma a) *
  big_sprod [seq vty_to_set var_map typesym_map i | i <- get_nonind_vtys adts l].
Proof.
  simpl in x. destruct a; simpl in x; try solve [
  destruct ([seq vty_to_set var_map typesym_map i | i <- get_nonind_vtys adts l]); simpl;
  try exact (x, tt);
  try exact x].
  simpl in Ha.
  destruct (ts_in_mut_list t0 adts).
  + exfalso. exact (not_false Ha).
  + simpl in x.
    destruct ([seq vty_to_set var_map typesym_map i | i <- get_nonind_vtys adts l]); simpl.
    exact (dom_cast (esym (sigma_cons _ _)) x, tt).
    exact (dom_cast (esym (sigma_cons _ _)) x.1, x.2).
Defined. 

(*While the W type uses a function from (finite n) to tuples
  of length (count_rec_occ (fin_nth x) c) and of type 
  (mk_adts (fin_nth x)), using this directly makes the proofs
  horrible due to all of the dependent types. Instead, we operate
  on functions giving lists, and we have a separate lemma that
  says that all of the lists have the right length. Then, we can
  prove a lemma separately from giving the function definition, and
  we don't need to mix proofs in with the function definition.
  We provide this transformation here:*)

(*Convert between function to list with proof of lengths and tuple*)
Definition f_to_tuple_f {n} {B: finite n -> Type} 
  {lens: finite n -> nat}
  (f: forall x: finite n, list (B x))
  (Hf: forall x: finite n, lens x = length (f x)) :
  (forall x: finite n, (lens x).-tuple (B x)).
Proof.
  intros x.
  apply (@Tuple _ _ (take (lens x) (f x))).
  apply (introT eqP).
  apply size_takel.
  apply eq_leq.
  apply Hf.
Defined.

Definition tuple_f_to_f {n} {B: finite n -> Type}
  {lens: finite n -> nat}
  (f: forall x: finite n, (lens x).-tuple (B x)) :
  forall x: finite n, list (B x).
Proof.
  intros x.
  apply (tval (f x)).
Defined.

Lemma tuple_f_to_f_proof {n} {B: finite n -> Type}
{lens: finite n -> nat}
(f: forall x: finite n, (lens x).-tuple (B x)) :
(forall x: finite n, lens x = length (tuple_f_to_f f x)).
Proof.
  intros. unfold tuple_f_to_f.
  destruct (f x). simpl.
  move: i => /eqP Hi. by rewrite -Hi.
Qed.

Lemma tuple_f_to_f_inj: forall {n} {B: finite n -> Type}
{lens: finite n -> nat}
(f1 f2: forall x: finite n, (lens x).-tuple (B x)),
tuple_f_to_f f1 = tuple_f_to_f f2 ->
f1 = f2.
Proof.
  intros n B lens f1 f2. unfold tuple_f_to_f.
  intros.
  apply functional_extensionality_dep. intros.
  apply val_inj. simpl. apply (fun_args_eq_dep _ _ x) in H.
  apply H.
Qed.

(*We don't actually use this lemma - all we use is [tuple_f_to_f_inj]*)
Lemma f_to_tuple_f_inv {n} {B: finite n -> Type} 
{lens: finite n -> nat}
(f: forall x: finite n, list (B x))
(Hf: forall x: finite n, lens x = length (f x)) :
tuple_f_to_f (f_to_tuple_f f Hf) = f.
Proof.
  unfold tuple_f_to_f. unfold f_to_tuple_f.
  apply functional_extensionality_dep; intros.
  simpl.
  apply take_oversize.
  rewrite Hf. apply eq_leq. reflexivity.
Qed.

(*The last lemma: to simplify a particular sequence of casts in
  the proof, we need to assume UIP. We prove this
  using [Eqdep.Eq_rect_eq.eq_rect_eq]; this shows up
  in other places via theorems about existT and it therefore
  reduces the axioms we need*)

  Lemma scast_cast_scast_uip: forall {v1 v2: Types.sort} {A1: Set} 
  (H1: domain v1 = A1) (H2: v2 = v1) (H3: A1 = domain v2) y, 
  @scast (domain v1) A1 H1 
    (@cast (domain v2) (domain v1) (@f_equal Types.sort Type domain v2 v1 H2) 
      (@scast A1 (domain v2) H3 y))= y.
  Proof.
    intros. subst.
    simpl. assert (H3 = erefl) by (apply UIP). subst. reflexivity.
  Qed. 
  


(*Several of the cases are identical.*)
Ltac solve_cast_list_eq l :=
  unfold args_to_ind_base_aux;
  apply functional_extensionality_dep; intros x;
    f_equal;
  apply list_eq_ext';
  rewrite !hlist_to_list_length 
    !hlength_eq !map_length //;
  intros n d Hn;
  assert (Hn': (n < length (map sigma (filter (rec_occ_fun (adt_name (fin_nth adts x)))l)))%coq_nat) by 
    (rewrite map_length; apply Hn);
  assert (Hsint: domain s_int) by (unfold domain; simpl; apply 0%Z);
  erewrite -> !hlist_to_list_nth_dec' with(Hi:=Hn') (d1:=s_int) (d2:=Hsint);
  try apply sort_eq_dec;
  apply cast_eq; [apply sort_eq_dec | apply d].

(*The general inverse function. It uses a generic list l to allow
  for general enough induction. It gives a (horrible) function which
  is the inverse of [args_to_constr_base_aux] and [args_to_ind_base_aux],
  but that is OK, we never use the definition of this function; we only
  need to know that it exists and it is truly an inverse. This turns out
  to be much easier than defining a (only slightly less horrible)
  separate function then proving inverse properties later.*)
Definition constr_ind_to_args_aux (l: list vty) (Hl: uniform_list m l)
  (b: build_vty_base var_map typesym_map adts l)
  (i: forall x: finite (length adts), list (mk_adts var_map typesym_map adts x))
  (Hi: forall x: finite (length adts), length (i x) = 
    count_rec_occ_aux l (adt_name (fin_nth adts x)) c) :
  {a: arg_list domain (sigma_aux l) |
  args_to_constr_base_aux l a = b /\
  (tuple_f_to_f (args_to_ind_base_aux l a)) = i}.
Proof.
  unfold count_rec_occ_aux in i.
  unfold rec_occ_fun in i.
  unfold tuple_f_to_f.
  generalize dependent i.
  induction l; intros.
  - simpl. apply (exist _ (@HL_nil _ domain)).
    destruct b. split; auto.
    unfold args_to_ind_base_aux. apply functional_extensionality_dep.
      intros. rewrite cast_nil.
      unfold count_rec_occ_aux in Hi. simpl in Hi.
      specialize (Hi x). apply length_zero_iff_nil in Hi.
      rewrite Hi; auto. 
  - simpl. unfold build_vty_base in *.
    simpl in b.
    destruct a; simpl in b.
    + simpl in i.
      set (x:=(@get_sprod_parts vty_int _ erefl b)).
      specialize (IHl (uniform_list_cons Hl) x.2 i Hi).
      destruct IHl as [atl [Hat1 Hat2]].
      apply (exist _ (HL_cons _ (sigma vty_int) _ x.1  atl)).
      simpl.
      split.
      * rewrite Hat1. clear Hat1. unfold build_sprod_cons.  simpl.
        subst x. simpl in *.
        destruct ([seq vty_to_set var_map typesym_map i | i <- get_nonind_vtys adts l]).
        -- reflexivity.
        -- destruct b; reflexivity.
      * rewrite <- Hat2. subst x. simpl in *. clear.
      destruct ([seq vty_to_set var_map typesym_map i | i <- get_nonind_vtys adts l]);
      solve_cast_list_eq l. 
    + simpl in i.
      set (x:=(@get_sprod_parts vty_real _ erefl b)).
      specialize (IHl (uniform_list_cons Hl) x.2 i Hi).
      destruct IHl as [atl [Hat1 Hat2]].
      apply (exist _ (HL_cons _ (sigma vty_real) _ x.1  atl)).
      simpl.
      split.
      * rewrite Hat1. clear Hat1. unfold build_sprod_cons.  simpl.
        subst x. simpl in *.
        destruct ([seq vty_to_set var_map typesym_map i | i <- get_nonind_vtys adts l]).
        -- reflexivity.
        -- destruct b; reflexivity.
      * rewrite <- Hat2. subst x. simpl in *. clear.
        destruct ([seq vty_to_set var_map typesym_map i | i <- get_nonind_vtys adts l]);
        solve_cast_list_eq l.
    + simpl in i.
      set (x:=(@get_sprod_parts (vty_var t0) _ erefl b)).
      specialize (IHl (uniform_list_cons Hl) x.2 i Hi).
      destruct IHl as [atl [Hat1 Hat2]].
      apply (exist _ (HL_cons _ (sigma (vty_var t0)) _ x.1  atl)).
      simpl.
      split.
      * rewrite Hat1. clear Hat1. unfold build_sprod_cons.  simpl.
        subst x. simpl in *.
        destruct ([seq vty_to_set var_map typesym_map i | i <- get_nonind_vtys adts l]).
        -- reflexivity.
        -- destruct b; reflexivity.
      * rewrite <- Hat2. subst x. simpl in *. clear.
        destruct ([seq vty_to_set var_map typesym_map i | i <- get_nonind_vtys adts l]);
        solve_cast_list_eq l.
    + simpl in *. (*the hard case*)
      destruct (ts_in_mut_list t0 adts) eqn : Hind.
      * (*case with mutual type*)
        simpl in b.
        assert (Hl0: l0 = map vty_var (m_params m)). {
          unfold uniform_list in Hl. rewrite Hind in Hl. simpl in Hl.
          move: Hl => /andP [Hl _]. simpl_sumbool.
        }
        assert (Hl': uniform_list m (vty_cons t0 l0 :: l)). {
          simpl. auto.
        }
        specialize (IHl (uniform_list_cons Hl') b ((split_arg_func t0 l0 l Hind Hl0 i Hi))
          (split_arg_func_invar t0 l0 l Hind Hl0 i Hi)).
        destruct IHl as [atl [Hat1 Hat2]].
        destruct (ts_in_mut_list_ex t0 m Hind). destruct a.
        assert (domain (sigma (vty_cons t0 l0)) = adt_rep x H0). {
          rewrite sigma_cons. rewrite split_arg_func_lemma2.
          rewrite H. apply dom_adts. exact t0. exact Hl0.
        }
        apply (exist _ (HL_cons domain (sigma (vty_cons t0 l0)) _ 
          (get_ind_arg t0 l0 l x H0 H Hl0 H1 i Hi) atl)).
        simpl in *. 
        split.
        -- assumption.
        -- apply functional_extensionality_dep. intros x'.
          clear -Hat2.
          unfold split_arg_func in *. destruct (ts_in_mut_list_ex). 
          destruct a. simpl in *.
          generalize dependent (filter_args_same (vty_cons t0 l0 :: l) x').
          simpl.
          (*Here, we have to handle the cases based on the variable x*)
          destruct (typesym_eq_dec t0 (adt_name (fin_nth adts x'))).
          ++ (*case 1: x' corresponds to t0*) 
            assert (x0 = fin_nth adts x'). {
              subst. 
              assert (Hx0: x0 = fin_nth adts (get_idx adt_dec x0 adts i0)) by (rewrite get_idx_correct; reflexivity). 
              rewrite Hx0 in e0.
              apply adt_names_inj in e0. subst. rewrite get_idx_correct.
              reflexivity.
            }
            (*The list is correct by context validity*) 
            destruct (list_eq_dec vty_eq_dec l0
            [seq vty_var i | i <- ts_args (adt_name (fin_nth adts x'))]).
            2 : {
              exfalso. apply n. subst. f_equal. symmetry. apply (adt_args gamma_valid).
              split; auto.
            }
            simpl. unfold get_ind_arg. intros Hf.
            rewrite cast_list_cons.
            assert (x' = (get_idx adt_dec x (typs m) H0)). {
              subst. unfold adt_in_mut in H0. 
              assert (x = fin_nth adts (get_idx adt_dec x adts H0)).
                rewrite get_idx_correct. reflexivity.
              rewrite H2 in H. apply adt_names_inj in H.
              subst. reflexivity.
            }
            subst; simpl. (*Here, we need UIP*)
            rewrite scast_cast_scast_uip.
            set (x':=(get_idx adt_dec x (typs m) H0)).
            apply (fun_args_eq_dep _ _ x') in Hat2.
            simpl in Hat2. clear -Hat2. 
            (*use the IH, which tells us about values of i*)
            destruct (finite_eq_dec (Datatypes.length adts) x'
            (get_idx adt_dec
              (fin_nth adts
                  (get_idx adt_dec x (typs m) H0)) 
              (typs m) i0)); try contradiction.
            {
              rewrite -> hlist_to_list_irrel with (Ha2:=(filter_args_same l x')) by apply sort_eq_dec.
              rewrite Hat2.
              apply safehead_tl.
            }
            {
              (*contradiction case*)
              exfalso. apply n. rewrite get_idx_fin.
              subst x'; reflexivity.
              apply (adts_nodups gamma_valid); auto.
            }
        ++ (*case where we are NOT seeing t0*) simpl.
          intros Hf.
          apply (fun_args_eq_dep _ _ x') in Hat2.
          simpl in Hat2.
          rewrite -> hlist_to_list_irrel with (Ha2:=(filter_args_same l x'))
            by apply sort_eq_dec.
          rewrite Hat2. destruct (finite_eq_dec (Datatypes.length adts) x'
          (get_idx adt_dec x0 (typs m) i0)).
          {
            (*another contradiction*)
            exfalso. apply n. subst. rewrite get_idx_correct. reflexivity.
          }
          {
            reflexivity.
          }
      * (*non-recursive instance case*)
        assert (Hi': forall x, length (i x) = count_rec_occ_aux l (adt_name (fin_nth adts x)) c). {
          intros. specialize (Hi x). rewrite Hi. unfold count_rec_occ_aux; simpl.
          rewrite -> args_func_false_case1 by auto. reflexivity. 
        }
        assert (Hl': uniform_list m (vty_cons t0 l0 :: l)). {
          simpl. auto.
        } simpl in b.
        (*use the function for the false case*)
        unshelve epose (b':=_:big_sprod [seq vty_to_set var_map typesym_map i |
          i <- get_nonind_vtys adts l]). {
            clear -b.
            destruct ([seq vty_to_set var_map typesym_map i | i <- get_nonind_vtys adts l]).
            exact tt. exact b.2.
          }
        unshelve epose (y:=_:domain (sigma (vty_cons t0 l0))). {
          clear -b. destruct ([seq vty_to_set var_map typesym_map i | i <- get_nonind_vtys adts l]).
          exact (dom_cast (esym (sigma_cons _ _)) b).
          exact (dom_cast (esym (sigma_cons _ _)) b.1).
        }
        specialize (IHl (uniform_list_cons Hl') b' i Hi').
        destruct IHl as [atl [Hat1 Hat2]].
        subst b'.
        apply (exist _ (HL_cons domain (sigma (vty_cons t0 l0)) _ y  atl)).
        simpl. subst y. simpl in *. 
        split.
        -- rewrite Hat1. clear Hat1. unfold build_sprod_cons. simpl.
           clear.
           destruct ([seq vty_to_set var_map typesym_map i | i <- get_nonind_vtys adts l]);
          rewrite dom_cast_twice; try (destruct b); reflexivity.
        -- rewrite <- Hat2. apply functional_extensionality_dep; intros.
          unfold args_to_ind_base_aux in *. simpl in *. clear -Hind.
          destruct ([seq vty_to_set var_map typesym_map i | i <- get_nonind_vtys adts l]); simpl;
          (*two identical cases*)
          f_equal; generalize dependent (filter_args_same (vty_cons t0 l0 :: l) x);
          simpl; rewrite args_func_false_case1; simpl; auto; intros Hf;
          apply hlist_to_list_irrel; apply sort_eq_dec.
Qed.

(*Finally, the complete inverse function. We use Qed, since we
  don't care about the body of the function, only that it is
  correct*)
Definition constr_ind_to_args 
(b: build_constr_base var_map typesym_map adts c)
(i: forall x: finite (length adts), 
  (count_rec_occ (adt_name (fin_nth adts x)) c).-tuple 
    (mk_adts var_map typesym_map adts x)) :
{a: arg_list domain sigma_args |
  args_to_constr_base a = b /\
  args_to_ind_base a = i}.
Proof.
  (*TODO: separate lemma?*)
  assert (Hunif: uniform_list m (s_args c)). {
    unfold uniform in m_unif.
    assert (Hu:=m_unif). unfold is_true in Hu.
    rewrite forallb_forall in Hu.
    specialize (Hu t (in_bool_In _ _ _ t_in)).
    rewrite forallb_forall in Hu.
    assert (Hinc: In c (ne_list_to_list (adt_constrs t))). {
      apply /in_bool_spec. rewrite <- in_bool_ne_equiv.
      apply c_in.
    }
    exact (Hu c Hinc).
  }
  pose proof (constr_ind_to_args_aux _ Hunif b (tuple_f_to_f i)).
  assert (forall x : finite (Datatypes.length adts),
  Datatypes.length (tuple_f_to_f i x) =
  count_rec_occ_aux (s_args c) (adt_name (fin_nth adts x)) c). {
    intros. unfold tuple_f_to_f. destruct (i x); simpl.
    apply /eqP. apply i0.
  }
  specialize (H H0).
  destruct H as [a [Hb Hi]].
  apply (exist _ a). split; auto.
  apply tuple_f_to_f_inj in Hi. apply Hi.
Qed.

End Inv.

End Constr.

(*Here we give the 3 properties of ADTs expressed only in terms
  of funsyms, arg_list, adt_rep, and constr_rep. Thus, our
  semantics do not need to directly reason about finite types,
  W-types, or the explicit functions above.*)

Variable dom_adts: forall (a: alg_datatype) (Hin: adt_in_mut a m),
domain (typesym_to_sort (adt_name a) srts) =
adt_rep a Hin.

Variable m_unif: uniform m.

(*Now, the main result we need: given an instance x of an adt rep,
  we can always find a constructor and an args list whose rep equals x*)
(*Needs funext and UIP*)
Definition find_constr_rep (x: adt_rep t t_in) :
  {f: funsym & {Hf: constr_in_adt f t * arg_list (domain) (sym_sigma_args f srts) |
  x = constr_rep f (fst Hf) dom_adts (snd Hf)}}.
Proof.
  assert (Hcons: (forall constrs : ne_list funsym,
  In constrs [seq adt_constrs i | i <- typs m] ->
  nodupb funsym_eq_dec (ne_list_to_list constrs))). {
    intros.
    eapply constrs_nodups. apply gamma_valid. apply m_in.
    apply H.
  }
  pose proof 
    (find_constr var_map typesym_map (typs m)
    (get_idx adt_dec t (typs m) t_in) Hcons).
  unfold adt_rep in x.
  specialize (X x).
  destruct X as [f Hf].
  destruct Hf as [[[Hinf base] inds] Hx]. subst.
  apply (existT _ f).
  assert (f_in: constr_in_adt f t). {
    rewrite get_idx_correct in Hinf. apply Hinf. 
  }
  destruct (constr_ind_to_args f f_in dom_adts m_unif base inds) as 
  [a [Hbase Hinds]].
  apply (exist _ (f_in, 
    (cast_arg_list (esym (sigma_args_eq f f_in)) a))).
  simpl. unfold constr_rep.
  f_equal.
  - apply bool_irrelevance.
  - rewrite cast_arg_list_twice. subst. reflexivity.
  - rewrite cast_arg_list_twice. subst. reflexivity.
Qed.

(*Constructors are disjoint (axiom-free)*)
Lemma constr_rep_disjoint: forall {f1 f2: funsym}
{f1_in: constr_in_adt f1 t} {f2_in: constr_in_adt f2 t}
(a1: arg_list domain (sym_sigma_args f1 srts))
(a2: arg_list domain (sym_sigma_args f2 srts)),
f1 <> f2 ->
constr_rep f1 f1_in dom_adts a1 <>
constr_rep f2 f2_in dom_adts a2.
Proof.
  intros.
  unfold constr_rep. apply constrs_disjoint. auto.
Qed.

(*Preliminary lemmas for injectivity:*)

Lemma build_sprod_cons_inj: forall {A: Set} {l: seq Set} {x: A} y 
  {l1: big_sprod l} l2,
build_sprod_cons x l1 = build_sprod_cons y l2 ->
x = y /\ l1 = l2.
Proof.
  intros. unfold build_sprod_cons in H. destruct l; subst.
  split; auto. unfold big_sprod in l1, l2. destruct l1; destruct l2; reflexivity.
  inversion H; subst; split; reflexivity.
Qed.

(*The big lemma we need for injectivity: if [args_to_constr_base]
  and [args_to_ind_base] are equal, then so are the underlying
  arg lists*)
Lemma args_to_base_inj: forall (l: seq vty) c
  (Hl: uniform_list m l)
  (a1 a2: arg_list domain (sigma_aux l)),
  args_to_constr_base_aux l a1 = args_to_constr_base_aux l a2 ->
  (forall x, args_to_ind_base_aux c dom_adts l a1 x =
    args_to_ind_base_aux c dom_adts l a2 x) ->
  a1 = a2.
Proof.
  intros. induction l; simpl in *.
  - rewrite (hlist_nil a1). rewrite (hlist_nil a2). reflexivity.
  - rewrite (hlist_inv a1). rewrite (hlist_inv a2).
     destruct a.
    + apply build_sprod_cons_inj in H. destruct H.
      f_equal. apply H.
      apply IHl; auto. intros x.
      specialize (H0 x). clear -H0.
      unfold args_to_ind_base_aux in *.
      apply val_inj; simpl. 
      apply ((f_equal val)) in H0. simpl in H0.
      f_equal.
      apply cast_list_inj in H0.
      apply hlist_to_list_inj in H0; [|apply sort_eq_dec].
      rewrite H0. reflexivity.
    + apply build_sprod_cons_inj in H. destruct H.
      f_equal. apply H.
      apply IHl; auto. intros x.
      specialize (H0 x). clear -H0.
      unfold args_to_ind_base_aux in *.
      apply val_inj; simpl. 
      apply ((f_equal val)) in H0. simpl in H0.
      f_equal.
      apply cast_list_inj in H0.
      apply hlist_to_list_inj in H0; [|apply sort_eq_dec].
      rewrite H0. reflexivity.
    + apply build_sprod_cons_inj in H. destruct H.
      f_equal. apply H.
      apply IHl; auto. intros x.
      specialize (H0 x). clear -H0.
      unfold args_to_ind_base_aux in *.
      apply val_inj; simpl. 
      apply ((f_equal val)) in H0. simpl in H0.
      f_equal.
      apply cast_list_inj in H0.
      apply hlist_to_list_inj in H0; [|apply sort_eq_dec].
      rewrite H0. reflexivity.
    + simpl in H.
      (*clear -H.*) 
       generalize dependent H.
       unfold build_vty_base.
       simpl.
       destruct (ts_in_mut_list t0 adts) eqn : Hin; intros H.
       * (*mutual case*) (*f_equal.*)
        assert (Hin':=Hin). move: Hin => /in_bool_spec. rewrite in_map_iff => [[a [Ha Hina]]].
          subst. move: Hina => /(in_bool_spec adt_dec) Hina.
        assert (Hfeq:=H0).
        specialize (H0 (get_idx _ a adts Hina)).
        unfold args_to_ind_base_aux in H0.
        apply (f_equal val) in H0. generalize dependent H0.
        simpl. generalize dependent (filter_args_same (vty_cons (adt_name a) l0 :: l)
        (get_idx adt_dec a adts Hina)). simpl.
        (*Once again, lots of annoying cases - TODO: is there better way?*)
        destruct (typesym_eq_dec (adt_name a)
        (adt_name (fin_nth adts (get_idx adt_dec a adts Hina)))).
        2 : {
          exfalso. apply n. f_equal. rewrite get_idx_correct. reflexivity.
        }
        destruct (list_eq_dec vty_eq_dec l0
        [seq vty_var i
            | i <- ts_args
                    (adt_name
                        (fin_nth adts (get_idx adt_dec a adts Hina)))]).
        2 : {
          (*Here we need uniformity - or else we lose some info and
            we cannot prove injectivity*)
          exfalso. apply n. rewrite get_idx_correct.
          move: Hl => /andP[/implyP Hunif _].
          specialize (Hunif Hin').
          simpl_sumbool.
          rewrite -> (@adt_args _ _ gamma_valid) with (m:=m)=>//.
        }
        simpl. intros Hf.
        rewrite !cast_list_cons. intros Heq. inversion Heq.
        f_equal.
        -- apply scast_inj in H1. apply cast_inj in H1. apply H1.
        -- apply IHl.
          ++ move: Hl => /andP[_ Hl]//.
          ++ apply H.
          ++ clear -Hfeq H2. intros x.
             specialize (Hfeq x).
             (*TODO: we need some other info I think*)
             unfold args_to_ind_base_aux in *.
             apply val_inj; simpl.
             apply (f_equal val) in Hfeq; simpl in Hfeq.
             move: Hfeq.
             generalize dependent (filter_args_same (vty_cons (adt_name a) l0 :: l) x).
             simpl.
             destruct (typesym_eq_dec (adt_name a) (adt_name (fin_nth adts x))).
             {
              (*when we deal with the current one - did most of the work already*)
              intros _ _.
              assert (get_idx adt_dec a adts Hina = x). {
                assert (a = fin_nth adts (get_idx _ _ _ Hina)) by 
                  (rewrite get_idx_correct; reflexivity).
                rewrite H in e. apply adt_names_inj in e.
                auto.
              }
              subst.
              f_equal. apply cast_list_inj in H2.
              rewrite -> (hlist_to_list_irrel) with (Ha2:=(Forall_inv_tail Hf)) by 
                apply sort_eq_dec.
              rewrite H2. apply hlist_to_list_irrel. apply sort_eq_dec.
             }
             {
              (*deal with others*) simpl. intros Hf'.
              intros Heq. f_equal. apply cast_list_inj in Heq.
              rewrite -> (hlist_to_list_irrel) with (Ha2:=Hf') by 
                apply sort_eq_dec.
              rewrite Heq. apply hlist_to_list_irrel. apply sort_eq_dec.
             }
       * (*no mutual occurrence*)
        apply build_sprod_cons_inj in H.
        destruct H as [Hhd Htl].
        f_equal.
        apply dom_cast_inj in Hhd.
        apply Hhd.
        apply IHl; auto. move: Hl => /andP[_ H]//.
        intros x. specialize (H0 x). clear -H0 Hin.
        unfold args_to_ind_base_aux in *.
        apply val_inj; simpl.
        apply (f_equal val) in H0; simpl in H0.
        move: H0.
        generalize dependent (filter_args_same (vty_cons t0 l0 :: l) x).
        simpl. destruct (typesym_eq_dec t0 (adt_name (fin_nth adts x))).
        -- (*not possible to be eq, or else in mut*)
          exfalso. subst. unfold ts_in_mut_list in Hin.
          move: Hin => /(in_bool_spec typesym_eq_dec).
          rewrite in_map_iff. intro C.
          apply C. exists (fin_nth adts x). split; auto. apply fin_nth_in.
        -- simpl. intros Hf Heq.
          f_equal. apply cast_list_inj in Heq.
          rewrite -> hlist_to_list_irrel with (Ha2:=Hf) by apply sort_eq_dec.
          rewrite Heq. apply hlist_to_list_irrel. apply sort_eq_dec.
Qed.

(*Constructors are injective. Requires UIP*)
Lemma constr_rep_inj: forall {f: funsym}
{f_in: constr_in_adt f t}
(a1 a2: arg_list domain (sym_sigma_args f srts)),
constr_rep f f_in dom_adts a1 = constr_rep f f_in dom_adts a2 ->
a1 = a2.
Proof.
  intros. unfold constr_rep in H.
  apply constrs_inj in H.
  destruct H as [Hb Hi].
  unfold args_to_constr_base in Hb.
  unfold args_to_ind_base in Hi.
  unfold sym_sigma_args in a1, a2.
  assert (cast_arg_list (sigma_args_eq f f_in) a1 =
  (cast_arg_list (sigma_args_eq f f_in) a2)). {
    eapply args_to_base_inj. 2: apply Hb. 2: apply Hi.
    (*TODO: separate lemma*)
    unfold uniform in m_unif.
    assert (Hu:=m_unif). unfold is_true in Hu.
    rewrite forallb_forall in Hu.
    specialize (Hu t (in_bool_In _ _ _ t_in)).
    rewrite forallb_forall in Hu.
    assert (Hinf: In f (ne_list_to_list (adt_constrs t))). {
      apply /in_bool_spec. rewrite <- in_bool_ne_equiv.
      apply f_in.
    }
    exact (Hu f Hinf).
  }
  apply cast_arg_list_inj in H. apply H.
Qed.

End Build.

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

  Section Cast.

  (*Some results about casts require UIP*)
  
  (*We need UIP, so we assume it directly (rather than something like
    excluded middle or proof irrelevance, which implies UIP)*)
  
  Lemma scast_left: forall {A B A' B': Set} (H1: A = A') (H2: B = B') (H3: Either A B = Either A' B') x,
    scast H3 (Left A B x) = Left A' B' (scast H1 x).
  Proof.
    intros. subst. unfold scast, eq_rec_r, eq_rec, eq_rect.
    assert (H3 = erefl) by apply UIP.
    rewrite H. reflexivity.
  Qed.
  
  Lemma scast_right: forall {A B A' B': Set} (H1: A = A') (H2: B = B') (H3: Either A B = Either A' B') x,
  scast H3 (Right A B x) = Right A' B' (scast H2 x).
  Proof.
    intros. subst. unfold scast, eq_rec_r, eq_rec, eq_rect. simpl.
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
    (forall i j a, B1 i j a = B2 i j (scast (eq_idx Heq i) a)) ->
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
    (forall j b, f1 j b = f2 j (scast (eq_idx' B a1 a2 Heq) b)) ->
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
  (Build_funsym (Build_fpsym name params args erefl erefl) 
    (vty_cons ret_ts (map vty_var ret_args)) erefl).

Definition triv_vars : typevar -> Set := fun _ => empty.
Definition triv_syms: typesym -> list vty -> Set := fun _ _ => empty.
Definition triv_context : context := nil.

Notation triv_adt := (mk_adt triv_vars triv_syms).

Notation triv_constr := (make_constr_simple triv_vars triv_syms).

Definition emp_fun {A: Type} : empty -> A := fun e =>
  match e with end.

Definition ta : typevar := "a"%string.
Definition tb : typevar := "b"%string.

Definition mk_tuple {A: Type} (n: nat) (l: list A) (Hl: size l == n) :
  n.-tuple A := Tuple Hl.

Notation mk_ne l :=
  (list_to_ne_list l erefl).

Notation triv_mut l :=
  (mk_mut l nil erefl).

(** Tactics *)

Ltac destruct_Either :=
  repeat match goal with
  | x: Either ?a ?b |- _ => destruct x 
  end; auto.

(*Solves ADT equality*)
Ltac solve_adt_eq :=
  vm_compute; f_equal; repeat(apply functional_extensionality_dep; intros);
  intros; destruct_Either.

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
  [unfold eq_rect; rewrite (all_funsym_refl (elimT _ _)); reflexivity|
  apply (mkW_eq a b x a1 a2 He); intros; revert_eqs;
  unfold cast, eq_rec_r, eq_rec, eq_rect, eq_idx', eq_ind_r, eq_ind (*eq_rect, eq_ind_r, eq_ind, eq_rec_r), eq_rec*);
  repeat (progress (try rewrite (all_funsym_refl (elimT _ _));
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

Lemma abool_correct: abool = W unit (fun i => Either unit unit)
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
  W unit (fun _ => Either unit (Either unit (Either unit (Either unit 
    (Either unit (Either unit unit)))))) (fun _ _ _ => empty) tt.
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
  W unit (fun _ => Either Z (Either Z unit)) (fun _ _ _ => empty) tt.
Proof.
  solve_adt_eq.
Qed.

(*Type with mix of int and real arguments*)
Inductive test1 : Set :=
  | test1a : Z -> Z -> test1
  | test1b: test1
  | test1c : QArith_base.Q -> Z -> test1
  | test1d: QArith_base.Q -> QArith_base.Q -> QArith_base.Q -> test1.

Definition ts_test1 : typesym := mk_ts "test1" nil.
Definition test1_constrs := list_to_ne_list
[mk_fs "test1a" nil [vty_int; vty_int] ts_test1 nil;
   mk_fs "test1b" nil nil ts_test1 nil;
   mk_fs "test1c" nil [vty_real; vty_int] ts_test1 nil;
   mk_fs "test1d" nil [vty_real; vty_real; vty_real] ts_test1 nil] erefl.
Definition atest1 := triv_adt ts_test1 test1_constrs.

Lemma atest1_correct : atest1 =
  W unit 
  (fun _ =>Either (Z * Z) 
  (Either unit (Either (QArith_base.Q * Z) (QArith_base.Q * (QArith_base.Q * QArith_base.Q)))))
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
Definition nat_cxt : context := 
    [datatype_def (triv_mut [alg_def ts_nat (mk_ne [fs_O; fs_S])])].
Definition nat_constrs := list_to_ne_list [fs_O; fs_S] erefl.

Definition anat := mk_adt triv_vars triv_syms  ts_nat nat_constrs.

Lemma anat_correct: anat =
  W unit (fun _ => Either unit unit) (fun _ _ (x: Either unit unit) =>
    match x with
    | Left  _ => empty
    | Right _ => unit
    end) tt.
Proof. reflexivity. Qed.

Definition aS (l: anat) := make_constr_simple triv_vars triv_syms ts_nat nat_constrs fs_S
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
Definition intlist_cxt : context := 
    [datatype_def (triv_mut [alg_def ts_intlist 
      (mk_ne [fs_intnil; fs_intcons])])].
Definition intlist_constrs := list_to_ne_list [ fs_intnil; fs_intcons] erefl.
Definition aintlist := mk_adt triv_vars triv_syms ts_intlist intlist_constrs.

Lemma aintlist_correct: aintlist =
  W unit (fun _ => Either unit Z) (fun _ _ x =>
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
Definition inttree_cxt : context := 
  [datatype_def (triv_mut [alg_def ts_inttree
  (mk_ne [fs_intleaf; fs_intnode])])].
Definition inttree_constrs := list_to_ne_list [fs_intleaf; fs_intnode] erefl.
Definition ainttree := mk_adt triv_vars triv_syms ts_inttree inttree_constrs.

Lemma ainttree_correct: ainttree =
  W unit (fun _ => Either unit Z) (fun _ _ x =>
    match x with
    | Left _ => empty
    | Right _ => option unit
    end) tt.
Proof. reflexivity. Qed.

(*More complicated simple inductive type*)
Inductive test2 : Set :=
  | test2a: Z -> test2
  | test2b: test2 -> test2
  | test2c: test2 -> QArith_base.Q -> test2 -> test2 -> test2
  | test2d: Z -> Z -> test2 -> test2.

Definition ts_test2 : typesym := mk_ts "test2" nil.
Definition fs_test2a := mk_fs "test2a" nil [vty_int] ts_test2 nil.
Definition fs_test2b := mk_fs "test2b" nil [vty_cons ts_test2 nil] ts_test2 nil.
Definition fs_test2c := mk_fs "test2c" nil [vty_cons ts_test2 nil; vty_real; vty_cons ts_test2 nil;
vty_cons ts_test2 nil] ts_test2 nil.
Definition fs_test2d := mk_fs "test2d" nil [vty_int; vty_int; vty_cons ts_test2 nil] ts_test2 nil.

Definition test2_cxt := [datatype_def 
  (triv_mut [alg_def ts_test2 
    (mk_ne [fs_test2a; fs_test2b; fs_test2c; fs_test2d])])].
Definition test2_constrs := list_to_ne_list [ fs_test2a; fs_test2b; fs_test2c; fs_test2d] erefl.
Definition atest2:= mk_adt triv_vars triv_syms ts_test2 test2_constrs.

Lemma atest2_correct : atest2 =
  W unit (fun _ => Either Z (Either unit (Either QArith_base.Q (Z * Z))))
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
Definition option_cxt := [datatype_def 
  (mk_mut [alg_def ts_option (mk_ne [fs_none; fs_some])] [ta] erefl)].
Definition option_constrs := list_to_ne_list [fs_none; fs_some] erefl.

Definition aoption (A: Set) := mk_adt (one_var A) triv_syms ts_option
  option_constrs.

Lemma aoption_correct: forall (A: Set),
  aoption A = W unit (fun _ => Either unit A) (fun _ _ _ => empty) tt.
Proof.
  intros. solve_adt_eq.
Qed. 

(*Either type*)
Definition ts_Either: typesym := mk_ts "Either" [ta; tb].
Definition fs_left := mk_fs "Left" [ta; tb] [vty_var ta] ts_Either [ta; tb].
Definition fs_right := mk_fs "Right" [ta; tb] [vty_var tb] ts_Either [ta; tb].
Definition Either_cxt := [datatype_def 
  (mk_mut [alg_def ts_Either (mk_ne [fs_left; fs_right])] [ta; tb] erefl)].
Definition Either_constrs := list_to_ne_list [fs_left; fs_right] erefl.

Definition aEither (A: Set) (B: Set) := mk_adt (two_var A B) triv_syms ts_Either
  Either_constrs.
  
Lemma aEither_correct: forall (A: Set) (B: Set),
  aEither A B = W unit (fun _ => Either A B) (fun _ _ _ => empty) tt.
Proof.
  intros. solve_adt_eq.
Qed.

(*List type*)
Definition ts_list: typesym := mk_ts "list" [ta].
Definition fs_nil := mk_fs "Nil" [ta] nil ts_list [ta].
Definition fs_cons := mk_fs "Cons" [ta] [vty_var ta; vty_cons ts_list [vty_var ta]] ts_list [ta].
Definition list_cxt := [datatype_def 
  (mk_mut [alg_def ts_list (mk_ne [fs_nil; fs_cons])] [ta] erefl)].
Definition list_constrs := list_to_ne_list [ fs_nil; fs_cons ] erefl.

Definition alist (A: Set) := mk_adt (one_var A) triv_syms ts_list
  list_constrs.

Lemma alist_correct: forall (A: Set),
  alist A = W unit (fun _ => Either unit A) (fun _ _ x =>
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
Definition tree_cxt := [datatype_def 
  (mk_mut [alg_def ts_tree (mk_ne [fs_leaf; fs_node])] [ta] erefl)].
Definition tree_constrs := list_to_ne_list [fs_leaf; fs_node] erefl.

Definition atree (A: Set) := mk_adt (one_var A) triv_syms ts_tree
  tree_constrs.

Lemma atree_correct: forall (A: Set),
  atree A = W unit (fun _ => Either unit A)
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
Definition wrap1_cxt := [datatype_def 
  (triv_mut [alg_def ts_wrap1 (mk_ne [fs_wrap1])])].

Definition abs_map1 (A: Set) (ts: typesym) (vs: list vty) : Set :=
  if typesym_eqb ts ts_abs then A else empty.

Definition wrap1_constrs := list_to_ne_list [fs_wrap1] erefl.

Definition awrap1 (A: Set) := mk_adt triv_vars (abs_map1 A) ts_wrap1
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
Definition wrap2_cxt := [datatype_def 
  (mk_mut [alg_def ts_wrap2 (mk_ne [fs_wrap2])] [ta; tb] erefl)].

Definition abs_map2 (A: Set) (ts: typesym) (vs: list vty) : Set :=
  if typesym_eqb ts ts_abs2 then A else empty.

Definition wrap2_constrs := list_to_ne_list [fs_wrap2] erefl.

Definition awrap2 (A B C: Set) := mk_adt (two_var B C) (abs_map2 A) ts_wrap2
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
      simpl_build_base; destruct_Either;
      try(rewrite scast_left; try reflexivity);
      try (rewrite scast_right; try reflexivity);
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

Definition mutAB_ctx := [datatype_def 
  (triv_mut [alg_def ts_mutA (mk_ne [fs_mk_A1; fs_mk_A2]);
alg_def ts_mutB (mk_ne [fs_mk_B])])].

Definition mutAB_constrs :=
  [alg_def ts_mutA (list_to_ne_list [fs_mk_A1; fs_mk_A2] erefl); 
   alg_def ts_mutB (list_to_ne_list [fs_mk_B] erefl)].

Definition amutAB := mk_adts triv_vars triv_syms mutAB_constrs.
Definition amutA := amutAB None.
Definition amutB := amutAB (Some tt).

Lemma amutAB_correct: amutAB =
  W (option unit) (fun x => match x with
                    | None => Either unit unit
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
Definition a_mk_A2 (b: amutB) := make_constr triv_vars triv_syms 
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

Definition tm_fmla_ctx := [datatype_def
  (triv_mut [alg_def ts_tm (mk_ne [fs_tm_const; fs_tm_if]);
  alg_def ts_fmla (mk_ne [fs_fm_eq; fs_fm_true; fs_fm_false])])].

Definition tm_fmla_constrs :=
  [alg_def ts_tm (list_to_ne_list [fs_tm_const; fs_tm_if] erefl); 
   alg_def ts_fmla (list_to_ne_list [fs_fm_eq; fs_fm_true; fs_fm_false] erefl)].

Definition atm_fmla := mk_adts triv_vars triv_syms 
  tm_fmla_constrs.

Definition atm := atm_fmla None.
Definition afmla := atm_fmla (Some tt).

Lemma atm_correct: atm_fmla = W (option unit) 
(fun x => match x with
  | None => Either Z unit
  | Some _ => Either unit (Either unit unit)
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

Definition rose_ctx := [datatype_def 
  (mk_mut [alg_def ts_rose (mk_ne [fs_rnode]);
  alg_def ts_treelist (mk_ne [fs_tnil; fs_tcons])] [ta] erefl)].
Definition rose_constrs :=
    [alg_def ts_rose (list_to_ne_list [fs_rnode] erefl);
     alg_def ts_treelist (list_to_ne_list [fs_tnil; fs_tcons] erefl)].

Definition arose_treelist (A: Set) := mk_adts (one_var A) triv_syms
  rose_constrs.
Definition arose (A: Set) := arose_treelist A None.
Definition atreelist (A: Set) := arose_treelist A (Some tt).

Lemma arose_correct (A: Set) : arose_treelist A =
  W (option unit)
  (fun x => match x with
  | None => A
  | Some _ => Either unit unit
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
  make_constr (one_var A) triv_syms rose_constrs (Some tt)
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