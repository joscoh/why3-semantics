Require Import Syntax.
Require Import Typing.
Require Import Types.
Require Import Coq.Lists.List.

(*Dealing with finite types*)
(*TODO: should we re-export stuff in separate section to prevent ssreflect
  elsewhere?*)
From mathcomp Require all_ssreflect fintype finfun.
Set Bullet Behavior "Strict Subproofs".

Section SSReflect.

Import all_ssreflect fintype finfun.

Section Finite.

(*To handle finite types, we use mathcomp/ssreflect. It has almost everything
  we need, except that the ordinal type is in Type, not Set. So we define
  an isomorphic type, and just convert.*)

Definition fin_nth_aux {A: Type} (s: seq A) (n: 'I_(size s)) : A :=
  tnth (in_tuple s) n.

Section OrdS.

Context (n: nat).

Inductive ordinalS : Set :=
  OrdinalS : forall m: nat, m < n -> ordinalS.

Definition ord_to_ordS : 'I_n -> ordinalS := fun o =>
  OrdinalS _ (ltn_ord o).

Definition ordS_to_ord : ordinalS -> 'I_n :=
  fun o => match o with
            | OrdinalS _ lt => Ordinal lt
            end.

Lemma ord_ordS_cancel: cancel ord_to_ordS ordS_to_ord.
Proof.
  move=>x/=.
  by apply val_inj.
Qed.

Lemma ordS_ord_cancel: cancel ordS_to_ord ord_to_ordS.
Proof.
  move=>[x ltx]/=.
  rewrite /ord_to_ordS/=. f_equal.
  apply bool_irrelevance.
Qed.

Definition ordS_eqMixin := CanEqMixin ordS_ord_cancel.
Canonical ordS_eqType := EqType ordinalS ordS_eqMixin.
Definition ordS_choiceMixin := CanChoiceMixin ordS_ord_cancel.
Canonical ordS_choiceType := ChoiceType ordinalS ordS_choiceMixin.
Definition ordS_countMixin := CanCountMixin ordS_ord_cancel.
Canonical ordS_countType := CountType ordinalS ordS_countMixin.

Definition ordS_finMixin := CanFinMixin ordS_ord_cancel.
Canonical ordS_finType := FinType ordinalS ordS_finMixin.

End OrdS.

(*The two operations we need: get the nth element of a tuple and 
  get the nth element of a list, assuming bounds*)
Definition tnthS {n: nat} {T: Type} (t: n.-tuple T) (x: ordinalS n) : T :=
  tnth t (ordS_to_ord n x).

Definition fin_nth {A: Type} (s: seq A) (n: ordinalS (size s)) : A :=
  tnthS (in_tuple s) n.

(* For any function f: ordinal n -> ordinal m -> A, we can consider this as 
  a function which first produces an m-tuple, then selects the correct element. *)
Definition finite_fun_blist {n: nat} {A: ordinalS n -> Type} 
(ns: ordinalS n -> nat)
(f: forall (j: ordinalS n) (x: ordinalS (ns j)), A j):
{h: forall j: ordinalS n, (ns j).-tuple (A j) |  forall j (k: ordinalS (ns j)),
f j k = tnthS (h j) k }. 
Proof.
  refine (exist _ (fun j => tcast (card_ord (ns j)) [ tuple of [seq (f j) i | i <- (map (@ord_to_ordS _) (enum 'I_(ns j)))]]) _).
  intros.
  rewrite /tnthS tcastE !tnth_map. f_equal.
  rewrite (tnth_nth (ordS_to_ord _ k))/=.
  apply (can_inj (@ordS_ord_cancel _)).
  rewrite ord_ordS_cancel.
  apply val_inj => /=.
  by rewrite nth_enum_ord.
Qed. 

End Finite.


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

(*Some facilities for building up types:*)
Section TypeOps.

(*A type with 0 elements*)
Definition empty : Set := (ordinalS 0).
(*Inductive empty :=.*)

(*A type with (A + B) elements*)
(*TODO: delete?*)
Inductive either (A B: Set) : Set :=
  | Left: A -> either A B
  | Right: B -> either A B.

End TypeOps.

(*A bool-valued version of "In" that we can use in proofs of Type*)
Fixpoint in_bool {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y})
  (x: A) (l: list A) : bool :=
  match l with
  | nil => false
  | y :: tl => eq_dec x y || in_bool eq_dec x tl
  end.

(*For the eventual API*)
Lemma in_bool_spec: forall {A: Type} (eq_dec: forall (x y : A), {x = y} + {x <> y})
  (x: A) (l: list A), reflect (In x l) (in_bool eq_dec x l).
Proof.
  intros. induction l; simpl.
  - constructor. auto.
  - destruct (eq_dec x a); simpl.
    + subst. apply ReflectT. left. auto.
    + destruct IHl.
      * apply ReflectT. right; auto.
      * apply ReflectF. intros [c1 | c2]; subst; contradiction.
Qed.

Lemma In_in_bool: forall {A: Type} (eq_dec: forall (x y : A), {x = y} + {x <> y})
(x: A) (l: list A),
  In x l ->
  in_bool eq_dec x l.
Proof.
  intros. eapply reflect_iff in H. apply H. apply in_bool_spec.
Qed.

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

Definition get_vty_base (v: vty) : option Set :=
  match v with
  | vty_int => Some Z
  | vty_real => Some R
  | vty_var x => Some (vars x)
  | vty_cons ts vs => 
    match (find_constrs gamma ts) with
    | None => Some (abstract ts vs) 
    | Some constrs => None (*These will be handled elsewhere*)
    end
  end.

Definition sprod (A B: Set) : Set := A * B.

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

(*This gives the base type for a single constructor. It will be (_ * _ * ... * _),
  where each _ is one of the nontrivial, nonrecursive arguments*)
Definition build_constr_base (c: funsym) : Set :=
  build_vty_base (s_args c).

(*This gives the combined base type for all constructors - the iterated
  Either of each constructor*)
(*There are two possible options for the base type, each with pros and cons:
  1. Define the base type as the iterated Either of the base of each constructor.
    This makes pattern matching nice, and makes the types readable (for example, 
    List A would be Either unit A). But the proofs are very difficult, because
    we need induction for everything (to determine which constructor we are in) and
    proofs due not reduce due to equality issues (so some "obvious" lemmas with
    equality are not provable).
  2. Define the base type simply as the type of constructors in the list, along
    with an instance of their base type. This is much, much nicer to use in proofs,
    as it reduces, requires no induction (we already have the constructor available),
    and has all the useful information already encapsulated in the type. But it
    does not allow nice pattern matching and makes the types into a cryptic
    nested sigma type.
  We choose to use the 2nd method because the proofs become much simpler. These types
  are only used in specifications, so we do not expect readability to be as much 
  of an issue. The test cases become much worse.*)
Definition build_base (constrs: list funsym) : Set :=
  { x: {f: funsym & build_constr_base f} | in_bool funsym_eq_dec (projT1 x) constrs}.

(*Setp 2: Construct the function for recursion*)

(*Count number of recursive occurrences (NOTE: doesnt work for non-uniform recursion)*)
Definition count_rec_occ (ts: typesym) (c: funsym) :=
  fold_right (fun v acc => 
    match v with
    | vty_cons ts' vs => (if typesym_eqb ts ts' then 1 else 0)
    | _ => 0
    end + acc) 0 (s_args c).

Definition build_constr_rec (ts: typesym) (c: funsym) : Set :=
   ordinalS (count_rec_occ ts c).

(*This suffices for the 2nd method for [build_base]; otherwise, we would need
  extra recursive functions to find which constructor we are in, and we would
  need dependent type casts.*)

(*The full encoding of ADTs*)

(*This handles mutual recursion (but not nested recursion at the moment).*)
Definition mk_adts (l: list (typesym * list funsym)) : ordinalS (length l) -> Set :=
  W (ordinalS (length l)) (fun n => build_base (snd (fin_nth l n)))
    (fun this i (x: build_base (snd (fin_nth l this))) => 
    build_constr_rec (fst (fin_nth l i)) (projT1 (proj1_sig x))).

Lemma lt_01: 0 < 1.
by [].
Qed.

(*For non-mutual types*)
Definition mk_adt (ts: typesym) (constrs: list funsym) : Set :=
  mk_adts [(ts, constrs)] (OrdinalS _ _ lt_01). 


(** Constructors *)

(*Generating the constructors is not too complicated given our choice of encoding.
  The constructor function (the non-trivial part) takes in the [build_base],
  knows what constructor we are dealing with, and, knowing the number of times
  the given type symbol is used recursively, selects the nth argument of the
  input list to apply to the nth recursive call.
  
  With the alternate encoding, we would need a recursive function to find which
  constructor we are in, then a recursive lemma to prove that the (A i) actually
  equals the finite type with the number of recursive calls, then we would need to
  use this lemma to manually create a mapping (and this dependent type casting will
  lead to terms that don't reduce).
  *)

  (*A slightly nicer form to get the [build_base] for a constructor*)
Definition get_constr_type (ts: typesym) (constrs: list funsym) (f: funsym) 
  (Hin: in_bool funsym_eq_dec f constrs)
  (c: build_constr_base f) : 
  (build_base constrs) := exist _ (existT _ f c) Hin.

(*Create the constructor encoding: given a mutually recursive type,
  an index into the type, a constructor in the constructors of that index,
  and the arguments to the constructor (recursive and non-recursive), we encode
  the constructor such that the function matches on the mutually recursive index and
  an instance, uses
  the fact that this is equivalent to just the number of recursive occurrences of
  this index, and constructs a finite mapping; ie: applying the nth argument to the
  nth recursive call.*)
Definition make_constr (l: list (typesym * list funsym)) (n: ordinalS (length l))
  (f: funsym)
  (Hin: in_bool funsym_eq_dec f (snd (fin_nth l n)))
  (c: build_constr_base f)
  (recs: forall (x: ordinalS (length l)), 
    (count_rec_occ (fst (fin_nth l x)) f).-tuple (mk_adts l x) ) :
  mk_adts l n :=
  (mkW (ordinalS (length l)) _ _ _ 
    (get_constr_type (fst (fin_nth l n)) _ f Hin c) 
    (fun j X => tnthS (recs j) X)).

(*For non-mutually-recursive-types *)
Definition make_constr_simple (ts: typesym) (constrs: list funsym) (f: funsym)
(Hin: in_bool funsym_eq_dec f constrs)
(c: build_constr_base f)
(recs: (count_rec_occ ts f).-tuple (mk_adt ts constrs)) :
mk_adt ts constrs.
Proof.
  apply make_constr with(f:=f).
  - apply Hin.
  - apply c.
  - intros. destruct x. simpl in i.
    simpl. have: m < 1 by []. rewrite ltnS leqn0 => /eqP Hm. subst. simpl.
    unfold mk_adt in recs. by have->: i = lt_01 by apply bool_irrelevance.
Defined. 

(* Theorems about ADTs*)

Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.

(*1. Every ADT created by constructor*)
(*A key lemma/function: Every instance of an ADT was created by a constructor, and
  moreover, we can find which constructor (assuming functional extensionality).
  NOTE: in principle, it may be possible to remove the dependence on functional
  extensionality by using Mathcomp's finfun type for finite functions. However,
  this would require significant refactoring and makes other parts of the
  proofs quite complicated. Since we assume this axiom elsewhere anyway, it is OK.*)
Definition all_constrs: forall (l: list (typesym * list funsym)) (n: ordinalS (length l))
  (x: mk_adts l n),
  {f: funsym & {t: in_bool funsym_eq_dec f (snd (fin_nth l n)) * build_constr_base f *
     forall (x: ordinalS (length l)), 
      (count_rec_occ (fst (fin_nth l x)) f).-tuple (mk_adts l x) 
     | x = make_constr l n f (fst (fst t)) (snd (fst t)) (snd t)}}.
Proof.
  intros. unfold mk_adts in x. dependent destruction x.
  unfold make_constr.
  destruct a as [[f' base] Hinf']. simpl in *.
  apply (existT _ f').
  pose proof (@finite_fun_blist (length l) _ (fun j => count_rec_occ (fst (fin_nth l j)) f') f) as h.
  destruct h as [h Hhf].
  apply exist with (x:=(Hinf', base, h)).
  f_equal.
  do 2 (apply functional_extensionality_dep; intros).
  rewrite Hhf. reflexivity. 
Qed.

(*2. Constructors are disjoint *)
Lemma constrs_disjoint: forall (l: list (typesym * list funsym)) (n: ordinalS (length l))
  (f1 f2: funsym) (Hin1: in_bool funsym_eq_dec f1 (snd (fin_nth l n)))
  (Hin2: in_bool funsym_eq_dec f2 (snd (fin_nth l n)))
  (c1: build_constr_base f1)
  (c2: build_constr_base f2)
  (recs1: forall (x: ordinalS (length l)), 
    (count_rec_occ (fst (fin_nth l x)) f1).-tuple (mk_adts l x) )
  (recs2: forall (x: ordinalS (length l)), 
    (count_rec_occ (fst (fin_nth l x)) f2).-tuple (mk_adts l x) ),
  f1 <> f2 ->
  make_constr l n f1 Hin1 c1 recs1 <> make_constr l n f2 Hin2 c2 recs2.
Proof.
  intros. intro C. inversion C; subst; contradiction.
Qed.

Lemma fun_args_eq: forall {A B : Type} (f g: A -> B) (x: A),
f = g ->
f x = g x.
Proof.
intros. subst. reflexivity.
Qed.

Lemma fun_args_eq_dep: forall {A : Type} {B: A -> Type} (f g: forall(x: A), B x) (x: A),
  f = g ->
  f x = g x.
Proof.
  intros. subst. reflexivity.
Qed.

(*3. Constructors are injective (this needs functional extensionality and UIP)*)
Lemma constrs_inj: forall (l: list (typesym * list funsym)) (n: ordinalS (length l))
(f: funsym) (Hin: in_bool funsym_eq_dec f (snd (fin_nth l n)))
(c1 c2: build_constr_base f)
(recs1 recs2: forall (x: ordinalS (length l)), 
  (count_rec_occ (fst (fin_nth l x)) f).-tuple (mk_adts l x) ),
make_constr l n f Hin c1 recs1 = make_constr l n f Hin c2 recs2 ->
c1 = c2 /\ recs1 = recs2.
Proof.
  intros. dependent destruction H. rename x into Heq. split; auto.
  apply functional_extensionality_dep. intros i.
  apply fun_args_eq_dep with(x:=i) in Heq.
  apply eq_from_tnth. move => y.
  apply fun_args_eq_dep with (x:=(ord_to_ordS _ y)) in Heq.
  unfold tnthS in Heq. rewrite ord_ordS_cancel in Heq. apply Heq.
Qed.

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

End ADTConstr.

(** Testing **)

(*TODO: this is all screwed up because of the changes to [build_base] and the
  tests don't work. They are also much less useful. We should either remove them
  or try to come up with some way to make them nicer. For now, they are commented out.*)
  (*

(*We need some axioms for testing: dependent functional extensionality,
  and, for mutually recursive types, Uniqueness of Identity Proofs*)
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
    assert (H3 = erefl) by apply UIP.
    rewrite H. reflexivity.
  Qed.
  
  Lemma cast_right: forall {A B A' B': Set} (H1: A = A') (H2: B = B') (H3: either A B = either A' B') x,
  cast H3 (Right A B x) = Right A' B' (cast H2 x).
  Proof.
    intros. subst. unfold cast. unfold eq_rec_r. simpl. unfold eq_rec. unfold eq_rect.
    assert (H3 = erefl) by apply UIP.
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

  (*A version of [f_equal] for mkW*)
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

(*For testing purposes, we provide an altnerative to [build_base], which is
very unweildy due to dependent types. This was what we used before. It makes
proofs MUCH worse but is easier to work with.*)
Section BuildBaseAlt.

Variable gamma: context.

Variable vars: typevar -> Set.
Variable abstract: forall (t: typesym), list vty -> Set.

Fixpoint build_base' (constrs: list funsym) : Set :=
match constrs with
  | [f] => build_constr_base gamma vars abstract f
  | f :: fs => either (build_constr_base gamma vars abstract f) (build_base' fs)
  | nil => empty
  end.

Definition bb_to_bb' (constrs: list funsym) (x: build_base gamma vars abstract constrs) : build_base' constrs.
Proof.
  unfold build_base in x.
  induction constrs.
  - simpl in x. destruct x as [_ Hf]. inversion Hf.
  - destruct constrs.
    + simpl. destruct x as [[f base] Hinf]. simpl in Hinf. destruct (funsym_eq_dec f a).
      rewrite <- e. apply base. inversion Hinf.
    + destruct x as [[f' base] Hinf']. simpl in Hinf'.
      destruct (funsym_eq_dec f' a). apply Left. rewrite <- e. apply base.
      apply Right. apply IHconstrs.
      apply (exist _ (existT _ f' base)).
      apply Hinf'.
Defined.

Definition bb'_to_bb (constrs: list funsym) (x: build_base' constrs) : build_base gamma vars abstract constrs.
Proof.
  unfold build_base. induction constrs.
  - simpl. simpl in x. inversion x. inversion H.
  - simpl in x. destruct constrs.
    + apply (exist _ (existT _ a x)). 
      simpl. destruct (funsym_eq_dec a a). reflexivity. contradiction.
    + destruct x.
      * apply (exist _ (existT _ a b)).
        simpl. destruct (funsym_eq_dec a a). reflexivity. contradiction.
      * apply IHconstrs in b.
        destruct b as [[f' base] Hinf'].
        apply (exist _ (existT _ f' base)).
        simpl. destruct (funsym_eq_dec f' a). reflexivity. apply Hinf'.
Defined.
(*
Lemma bb_to_bb'_inv: forall (constrs: list funsym) (x: build_base gamma vars abstract constrs),
  bb'_to_bb constrs (bb_to_bb' constrs x) = x.
Proof.
  intros. unfold build_base in x. induction constrs.
  - destruct x. inversion i.
  - destruct constrs; simpl.
    + simpl in *. destruct x as [[f' base] Hinf']. simpl.
      destruct (funsym_eq_dec f' a).


Search (?x || ?y = true).
        
        
        destruct (funsym_eq_dec f' a)
        simpl.
      
      simpl. 
  
  
  unfol simpl in x.
*)

End BuildBaseAlt.

(* We give many unit tests of increasing complexity to validate the encoding
  and ensure that the encodings can be proved equivalent to simpler, expected forms.*)

Section Tests.

(* Utilities for building tests *)

Notation mk_fs name params args ret_ts ret_args := 
  (Build_funsym name params args (vty_cons ret_ts (map vty_var ret_args)) erefl).

Definition triv_vars : typevar -> Set := fun _ => empty.
Definition triv_syms: typesym -> list vty -> Set := fun _ _ => empty.
Definition triv_context : context := nil.

Notation triv_adt := (mk_adt triv_context triv_vars triv_syms).
Notation triv_constr := (make_constr_simple triv_context triv_vars triv_syms).
(*
Definition bb'_to_bb_cast (gamma: context) (vars: typevar -> Set) 
(syms: typesym -> list vty -> Set) (cs: list funsym) s
(Hs: build_base' gamma vars syms cs = s) : build_base' gamma vars syms cs.
Proof.
  rewrite Hs. apply s.



  (s)
*)
Notation triv_bb'_to_bb := (bb'_to_bb triv_context triv_vars triv_syms).
Notation triv_build_base := (build_base triv_context triv_vars triv_syms).

Definition emp_fun {A: Type} : empty -> A.
intros e. destruct e. inversion i.
Defined. 


(*Unit*)
Definition ts_unit : typesym := mk_ts "unit" nil erefl.
Definition fs_tt := mk_fs "tt" nil nil ts_unit nil.

Definition aunit := triv_adt ts_unit [ fs_tt].

Definition att := triv_constr ts_unit [fs_tt] fs_tt erefl tt
  (in_tuple nil).
(*
Definition cast_base (cs: list funsym) (s: Set) (Hs: build_base' )
*)
(*
Lemma test: triv_build_base [fs_tt] = unit.
Proof.
  unfold triv_build_base. simpl.
  reflexivity.
*)
(*  Lemma test:
  build_base' triv_context triv_vars triv_syms [fs_tt] = unit.
  Proof.
    reflexivity.
  Qed.

Lemma test: bb'_to_bb triv_context triv_vars triv_syms [fs_tt] unit =
  triv_build_base [fs_tt].

triv_build_base [fs_tt] = triv_bb_to_bb' [fs_tt] unit.
Proof.
  vm_compute.*)
(*
Check W.
Check triv_build_base.
Check 
Lemma aunit_correct: aunit = W (finite 1) (fun _ => triv_bb'_to_bb [fs_tt]) (fun _ _ _ => empty) tt.
Proof. 
  unfold aunit, triv_adt, mk_adts, triv_build_base. simpl. f_equal.
  repeat(apply functional_extensionality_dep; intros).
  destruct x1 as [[f base] Hf]. simpl in *. destruct (funsym_eq_dec f fs_tt); auto; subst.
  reflexivity. inversion Hf.
Qed. 
*)

Definition def_adt : typesym * list funsym := (ts_unit, [fs_tt]).

Lemma nat_lt_1: forall n,
  n < 1 ->
  n = 0.
Proof.
  move => x. by rewrite ltnS leqn0 => /eqP Hm.
Qed.

(*This is a LOT more work than the previous version: was only reflexivity there*)
Lemma aunit_correct: aunit = W (ordinalS 1) (fun x => triv_build_base [fs_tt]) (fun _ _ _ => empty) (OrdinalS _ _ lt_01).
Proof. 
  unfold aunit, triv_adt, mk_adts, triv_build_base. simpl.
  match goal with 
  | |- W ?I1 ?A1 ?B1 ?x1 = W ?I1 ?A2 ?B2 ?x2 => assert (He: A1 = A2)
  end.
  - repeat (apply functional_extensionality_dep; intros).
    unfold fin_nth, tnthS. simpl. destruct x.
    have Hm: m = 0 by apply nat_lt_1. by subst.
  - erewrite w_eq_aux with(Heq:=He). reflexivity.
  intros.
  simpl. destruct a. destruct x. move: i0. simpl in *.
  destruct i, j. rewrite /fin_nth /tnthS/= !(tnth_nth def_adt)/=.
  have->: m = 0 by apply nat_lt_1.
  have->/=: m0 = 0 by apply nat_lt_1.
  destruct (funsym_eq_dec x fs_tt) => [|//]. subst.
  move =>_. unfold build_constr_rec. unfold count_rec_occ. simpl.
  reflexivity.
Qed.

(*
Ltac prove_constr :=
  unfold triv_constr, make_constr_simple, make_constr; simpl;
  let He := fresh "Heq" in
  match goal with | |- mkW ?i ?a ?b ?x ?a1 ?f = mkW ?i ?a ?b ?x ?a2 ?f2 =>
    assert (He: a1 = a2) end;
  [unfold eq_rect; rewrite (all_funsym_refl (reflect_true _ _)); reflexivity|
  apply mkW_eq_aux with (Heq:=He); intros; unfold eq_rect, eq_ind_r, eq_ind;
  try rewrite (all_funsym_refl (eq_sym _))].
  *)

Lemma att_correct: att = mkW (ordinalS 1) _ _ (OrdinalS _ _ lt_01) (OrdinalS _ _ lt_01) (fun _ => emp_fun).
Proof.
  unfold att. prove_constr.
  destruct b.
Qed.

Lemma att_correct: att = mkW (finite 1) _ _ tt tt (fun _ => emp_fun).
Proof.
  unfold att. prove_constr.
  destruct b.
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


Lemma atrue_correct: atrue = mkW (finite 1) _ _ tt (Left _ _ tt) (fun _ => emp_fun).
Proof. 
  unfold atrue. prove_constr. destruct b.
Qed.

Require Import Coq.Program.Equality.

Lemma all_w: forall (I: Set) (A: I -> Set) (B: forall i : I, I -> A i -> Set) (i: I)
  (x: W I A B i),
  exists (a: A i) (f: forall (j: I), B i j a -> W I A B j),
    x = mkW I A B i a f.
Proof.
  intros. dependent destruction x. exists a. exists f. reflexivity.
Qed.

Lemma all_bool: forall (x: abool), x = atrue \/ x = afalse.
Proof.
  intros. unfold abool in x. unfold triv_adt in x.
  unfold mk_adts in x. dependent destruction x. simpl in *.
  destruct a.
  - left. rewrite atrue_correct. simpl.
    unfold build_constr_base. simpl. unfold build_vty_base. simpl.
    unfold big_sprod. simpl.
    (*ok**)
    reflexivity.
    reflexivity.
    reflexivity. unfold atrue. unfold triv_constr. unfold make_constr. simpl.


    destruct x.

  subst.
  
  simpl in x.

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
  intros. unfold aS. prove_constr.
  destruct j; reflexivity.
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
  unfold amutAB, mk_adts, build_base, fin_nth, eq_rect_r. simpl.
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
          | None => mk_blist 0 nil eq_refl
          | Some tt => mk_blist 1 [b] eq_refl
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
  - destruct f. reflexivity.
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
  | None, Left _ _ _ => empty (*term const has no recursive calls*)
  | None, Right _ _ _ => (*term if has 1 call to fmla, 2 to term*)
    match other with
    | None => finite 2
    | _ => finite 1
    end
  | Some _, Left _ _ _ => (*fmla eq has 2 to term, 0 to fmla*)
    match other with
    | None => finite 2
    | _ => empty
    end
  | Some _, Right _ _ _ => empty (*true and false have no recursive calls*)
  end).
Proof.
  unfold atm_fmla, mk_adts, build_base, fin_nth, eq_rect_r; simpl.
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
*)

End SSReflect.