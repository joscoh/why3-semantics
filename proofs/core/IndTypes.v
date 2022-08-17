Require Import Syntax.
Require Import Typing.
Require Import Types.
Require Import Coq.Lists.List.

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
Inductive empty :=.

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

(*Bounded lists*)
Definition blist (A: Type) (n: nat) : Type := {l : list A | length l = n}.

Definition mk_blist {A} (n: nat) (l: list A) (Hn: length l =? n) : blist A n.
apply (exist _ l). apply Nat.eqb_eq. apply Hn.
Defined.

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
    | Some constrs => None (*These will be handled elseqhere*)
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
  Search sigT.

Definition build_base (constrs: list funsym) : Set :=
  { x: {f: funsym & build_constr_base f} | in_bool funsym_eq_dec (projT1 x) constrs}.
(*  { l: list (nat * {f: funsym & build_constr_base f}) |
    map (fun x => projT1 (snd x)) l = constrs /\
    map fst l  = seq 0 (length constrs)}.*)
  
  (*match constrs with
  | [f] => build_constr_base f
  | f :: fs => either (build_constr_base f) (build_base fs)
  | nil => unit
  end.*)

(*Setp 2: Construct the function for recursion*)

(*Count number of recursive occurrences (NOTE: doesnt work for non-uniform recursion)*)
Definition count_rec_occ (ts: typesym) (c: funsym) :=
  fold_right (fun v acc => 
    match v with
    | vty_cons ts' vs => (if typesym_eqb ts ts' then 1 else 0)
    | _ => 0
    end + acc) 0 (s_args c).

Definition build_constr_rec (ts: typesym) (c: funsym) : Set :=
  finite (count_rec_occ ts c).

(*Definition cast_build_base {c1 c2: list funsym} (H: c1 = c2) (x: build_base c1) :
  build_base c2.
Proof.
  subst. apply x.
Defined.*)
(**)
(*
Definition build_rec (ts: typesym) (constrs: list funsym) (b: build_base constrs) : Set :=
  match b with
  | exist 

(*This is the recursive function for the W type:
  it takes in an instance of the constrs base type, and for the base type
  belonging to constructor i, the result is the finite type of the number of
  recursive occurrences of ts in i *)
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

(*Alternatively, build with tactics (arguably cleaner to read but not use)*)
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
Qed.*)

(*The full encoding of ADTs*)

(*This handles mutual recursion (but not nested recursion at the moment).
  Mutual recursion is not too bad, we just need to be careful to call [build_rec]
  with the correct typesym to count.*)
Definition mk_adts (l: list (typesym * list funsym)) : finite (length l) -> Set :=
  W (finite (length l)) (fun n => build_base (snd (fin_nth l n)))
    (fun (this: finite _) (i: finite _) (x: build_base (snd (fin_nth l this))) => 
    build_constr_rec (fst (fin_nth l i)) (projT1 (proj1_sig x))).
  (*    build_rec (fst (fin_nth l i))
        (snd (fin_nth l this))).*)

(*For non-mutual types*)
Definition mk_adt (ts: typesym) (constrs: list funsym) : Set :=
  mk_adts [(ts, constrs)] tt. 



(** Constructors *)

(*Generating the constructor takes a decent amount of effort. 
First, we need to
  transform an instance of the arguments of the constructor ([build_constr_base])
  into an instance of the base type ([build_base]).
Then, we need to know that [build_rec] of a constructor base type is
  just the finite type counting the number of occurrences (the dependent types
  make this non-trivial to prove).
Then, we define a mapping between a finite type and a bounded list of
  the same size.
Finally, we can use these pieces to define the constructor encoding. *)

(*Step1: transform instance of [build_constr_base] to instance of [build_base].
  The function is conceptually simple (walk through list until we find the correct
  constructor), dependent types make it very hard to write by hand.*)

Definition get_constr_type (ts: typesym) (constrs: list funsym) (f: funsym) 
  (Hin: in_bool funsym_eq_dec f constrs)
  (c: build_constr_base f) : 
  (build_base constrs) := exist _ (existT _ f c) Hin.
(*Proof.
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
Defined.*)

(*Now, we show that if we get the type corresponding to some
  constructor f, it is really just the type that counts the number
  of recursive instances in f*)
(*We need this to be Defined so that we can simplify in [make_constr] without
  axioms*)
  
(*Definition build_rec_get_constr_type: forall (ts ts': typesym) (constrs: list funsym) 
  (f: funsym) (Hin: in_bool funsym_eq_dec f constrs)
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
Defined.*)

(*A generic map from a finite type to a bounded list *)
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

(*Finally, create the constructor encoding: given a mutually recursive type,
  an index into the type, a constructor in the constructors of that index,
  and the arguments to the constructor (recursive and non-recursive), we encode
  the constructor such that the function matches on the mutually recursive index and
  an instance, uses
  the fact that this is equivalent to just the number of recursive occurrences of
  this index, and constructs a [finmap_list]; ie: applying the nth argument to the
  nth recursive call.*)

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
  simpl in H. unfold build_constr_rec in H.
  specialize (recs j). apply (finmap_list _ recs H).
Defined.
(*
Print make_constr.
  rewrite (build_rec_get_constr_type (fst(fin_nth l n)) (fst(fin_nth l j)) _ f Hin c) in H.
  specialize (recs j). apply (finmap_list _ recs H).
Defined.*)

  (*New plan: use ssreflect fintypes, prove that build_rec gives a fintype,
    then, just define *)

(*For non-mutually-recursive-types *)
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

Require Import Coq.Program.Equality.
Require Import Coq.Logic.Eqdep_dec.

Lemma all_funsym_refl: forall {f: funsym} (H: f = f),
  H = eq_refl.
Proof.
  intros. apply UIP_dec. intros. eapply reflect_dec. apply funsym_eqb_spec.
Qed.

Lemma isT : is_true true.
Proof. auto. Qed.

Lemma in_bool_dec: forall {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y}) x l,
  proj_sumbool _  _ (in_dec eq_dec x l) = in_bool eq_dec x l.
Proof.
  intros. induction l; simpl; auto.
  destruct (eq_dec a x); subst; simpl.
  destruct (eq_dec x x); auto. contradiction.
  destruct (eq_dec x a); auto; subst; try contradiction; simpl.
  destruct (in_dec eq_dec x l); simpl; auto.
Qed.

(*Lemma list_eq_dec_cons: forall {A: Type} (eq_dec: forall (x y : A), { x = y} + { x <> y})
  (x: A) (l: list A)*)

(*TODO: move - this is very ssreflect-like - also very ugly proof*)
Lemma nodupb_cons {A: Type} (eq_dec: forall (x y : A), {x = y} + {x <> y}) 
  (x: A) (l: list A) :
  nodupb eq_dec (x :: l) = negb (in_bool eq_dec x l) && nodupb eq_dec l.
Proof.
  intros.
  destruct (nodup_NoDup eq_dec (x :: l)).
  - inversion n; subst.
    rewrite <- in_bool_dec. destruct (in_dec eq_dec x l); simpl; auto; try contradiction.
    destruct (nodup_NoDup eq_dec l); auto. contradiction.
  - rewrite <- in_bool_dec. destruct (in_dec eq_dec x l); auto; simpl.
    destruct (nodup_NoDup eq_dec l); auto. exfalso. apply n. constructor; auto.
Qed.
(*
Definition get_funsym_base (ts: typesym) 
  (l: list funsym) (Hl: l <> nil) (Huniq: nodupb funsym_eq_dec l) (b: build_base l) :
  { f: funsym & {Hin: in_bool funsym_eq_dec f l & 
    {b1: build_constr_base f | b = get_constr_type ts l f Hin b1}}}.
Proof.
  unfold build_base in b.
  destruct b as [[f Hbase] Hinf]. simpl in Hinf.
  apply (existT _ f).
  apply (existT _ Hinf).
  apply (exist _ Hbase). reflexivity. f_equal.
  simpl.
  induction l; simpl in b.
  - contradiction.
  - destruct l.
    + apply (existT _ a). simpl.
      destruct (funsym_eq_dec a a); simpl; auto. 2: contradiction.
      unfold eq_rect.
      rewrite (all_funsym_refl e).
      apply (existT _ isT).
      apply (exist _ b). reflexivity.
    + destruct b.
      * apply (existT _ a).
        simpl. destruct (funsym_eq_dec a a); [|contradiction].
        simpl. unfold eq_rect. rewrite (all_funsym_refl e).
        apply (existT _ isT).
        apply (exist _ b). reflexivity.
      * simpl. rewrite nodupb_cons in Huniq.
        assert (Hfl: f :: l <> []) by (intro C; inversion C).
        specialize (IHl Hfl).
        apply andb_true_iff in Huniq. destruct Huniq as [Hnotin Huniq].
        specialize (IHl Huniq b).
        destruct IHl as [f' Hf']. apply (existT _ f').
        destruct (funsym_eq_dec f' a).
        -- subst. destruct Hf'.
          rewrite x in Hnotin. inversion Hnotin.
        -- simpl. destruct Hf' as [Hin [b1 Hb]].
          apply (existT _ Hin). apply (exist _ b1).
          rewrite Hb. reflexivity.
Qed.*)

Lemma fin_nth_in: forall {A: Type} (l: list A) (n: finite (length l)),
  In (fin_nth l n) l.
Proof.
  intros. induction l; auto.
  - inversion n.
  - simpl in n. destruct l; simpl in *.
    left. reflexivity.
    destruct n.
    + specialize (IHl y). right. apply IHl.
    + left. reflexivity.
Qed. 

Require Import Coq.Logic.FunctionalExtensionality.

(*Easiest: enumerate all finite elements*)
Definition all_fins (m: nat) : list (finite m).
induction m as [| m' IHm'].
- apply nil.
- destruct m' as [| m''].
  + apply [tt].
  + apply (map Some IHm' ++ [None]).
Defined.

Lemma all_fins_all: forall (m: nat) (x: finite m),
  In x (all_fins m).
Proof.
  intros. induction m; simpl.
  - inversion x.
  - destruct m.
    + destruct x. left; auto.
    + simpl in x. apply in_or_app. destruct x.
      * left. rewrite in_map_iff. specialize (IHm y).
        exists y. split; auto.
      * right. left. auto.
Qed.

Lemma NoDup_map_inj: forall {A B: Type} (f: A -> B)
  (inj: forall x y, f x = f y -> x = y)
  (l: list A),
  NoDup l ->
  NoDup (map f l).
Proof.
  intros; induction l; simpl. constructor.
  inversion H; subst.
  constructor. rewrite in_map_iff. intro C.
  destruct C as [x [Hx Hinx]]. apply inj in Hx. subst.
  contradiction.
  auto.
Qed.

Lemma app_cons: forall {A: Type} (x: A) (l: list A),
  [x] ++ l = x :: l.
Proof.
  intros. reflexivity.
Qed.

Lemma all_fins_nodup: forall (m: nat),
  NoDup (all_fins m).
Proof.
  intros; induction m; simpl.
  - constructor.
  - destruct m.
    + constructor; auto. constructor.
    + rewrite <- rev_involutive, rev_app_distr.
      apply NoDup_rev. simpl rev at 1.
      rewrite app_cons. apply NoDup_cons.
      * rewrite <- in_rev,  in_map_iff. intro C.
        destruct C as [x [Hx Hinx]]. inversion Hx.
      * apply NoDup_rev. apply NoDup_map_inj; auto.
        intros x y Hxy. inversion Hxy. auto.
Qed.

Lemma all_fins_length: forall (m: nat),
  length (all_fins m) = m.
Proof.
  induction m; simpl; auto.
  destruct m.
  - reflexivity.
  - rewrite app_length, map_length. simpl length at 2.
    rewrite Nat.add_1_r. auto.
Qed.

Definition make_blist {A: Type} (m: nat) (l: list A) (H: length l = m) : blist A m :=
  exist _ l H.

Lemma cast_fin {n m: nat} (Hnm: m = n) (x: finite n) : finite m.
rewrite Hnm. apply x.
Defined.

Lemma cast_fin_none: forall {n m: nat} (Hnm: S (S m) = S (S n)),
  cast_fin Hnm None = None.
Proof.
  intros. unfold cast_fin. unfold eq_rec_r, eq_rec, eq_rect, eq_sym.
  assert (n = m). {
    inversion Hnm. reflexivity.
  } subst. assert (Hnm = eq_refl) by (apply UIP_dec, Nat.eq_dec).
  rewrite H. reflexivity.
Qed.

Print nth.

Lemma not_ltbnn: forall n, ~(n <? n).
Proof.
  intros. rewrite Nat.ltb_irrefl. intro C; inversion C.
Qed.

Lemma not_ltbsz: forall n, ~(S n <? 0).
Proof.
  intros. intro C. inversion C.
Qed.

Lemma ltb_inj: forall n m, (S n <? S m) = (n <? m).
Proof.
  intros. destruct (Nat.ltb_spec0 n m); simpl;
  destruct (Nat.ltb_spec0 (S n) (S m)); simpl; auto; lia.
Qed.

Lemma ltb_inj': forall n m, (S n <? S m) -> (n <? m).
Proof.
  intros n m. rewrite ltb_inj. auto.
Qed.

Lemma ltb_trans: forall {n m p}, (n <? m) -> (m <? p) -> (n <? p).
Proof.
  intros. destruct (Nat.ltb_spec0 n m); simpl; try inversion H.
  destruct (Nat.ltb_spec0 m p); simpl; try inversion H0.
  destruct (Nat.ltb_spec0 n p); simpl; auto. lia.
Qed.

Lemma ltbs: forall n, (n <? S n).
Proof.
  intros. destruct (Nat.ltb_spec0 n (S n)); auto; lia.
Qed.

Definition nth_inb {A: Type} (n: nat) (l: list A) (Hn: n <? length l) : A.
Proof.
  generalize dependent l; induction n; intros.
  - destruct l.
    + exfalso. apply (not_ltbnn 0 Hn).
    + apply a.
  - destruct l.
    + exfalso. apply (not_ltbsz n Hn).
    + apply (IHn l (ltb_inj' n (length l) Hn)).
Defined.
(*
Definition nth' {A: Type} (n: nat) (l: list A) (default: A) : A.
Proof.
  revert l. induction n; intros.
  - destruct l.
    + apply default.
    + apply a.
  - destruct l.
    + apply default.
    + apply IHn. apply l.
Defined.

Lemma nth_equiv: forall {A: Type} (n: nat) (l: list A) (d: A),
  nth n l d = nth' n l d.
Proof.
  intros. revert l. induction n; intros; destruct l; simpl; auto.
Qed.*)



Print nth.

(*First, make proof generic*)
Lemma nth_inb_map: forall {A B: Type} (f: A -> B) (l: list A) (n: nat) 
  (Hn1: n <? length l) (Hn2: n <? length (map f l)),
  nth_inb n (map f l) Hn2 = f (nth_inb n l Hn1).
Proof.
  intros A B f l n. revert l. induction n; intros; destruct l; simpl.
  - inversion Hn1.
  - reflexivity.
  - inversion Hn1.
  - erewrite <- IHn. reflexivity.
Qed.

Definition nat_of_fin {m: nat} (x: finite m) : nat.
induction m.
- inversion x.
- destruct m.
  + simpl in x. apply 0.
  + destruct x.
    * apply IHm. apply f.
    * apply (S m).
Defined.

Lemma nat_of_fin_range: forall {m: nat} (x: finite m),
  nat_of_fin x < m.
Proof.
  intros. induction m.
  - inversion x.
  - destruct m.
    + simpl; lia.
    + destruct x.
      * assert (@nat_of_fin (S (S m)) (@Some (finite (S m)) f) = nat_of_fin f) by reflexivity.
        specialize (IHm f). lia.
      * simpl. lia.
Qed.

Lemma nat_of_fin_inj: forall {m: nat} (x y: finite m),
  nat_of_fin x = nat_of_fin y ->
  x = y.
Proof.
  intros. induction m.
  - inversion x.
  - destruct m.
    + destruct x; destruct y. reflexivity.
    + destruct x; destruct y;
      try (replace (@nat_of_fin (S (S m)) (@None (finite (S m)))) 
        with (S m) in H by reflexivity);
      try (replace (@nat_of_fin (S (S m)) (@Some (finite (S m)) f)) 
        with (nat_of_fin f) in H by reflexivity); auto.
      * f_equal. apply IHm. auto.
      * pose proof (nat_of_fin_range f). lia.
      * pose proof (nat_of_fin_range f). lia.
Qed.

Lemma nat_of_fin_surj: forall {n m: nat} (Hn: n < m),
  exists (x: finite m), nat_of_fin x = n.
Proof.
  intros. induction m.
  - lia.
  - destruct m.
    + assert (n = 0) by lia; subst. exists tt. reflexivity.
    + assert (n = S m \/ n < S m) by lia.
      destruct H.
      * subst. exists None. reflexivity.
      * apply IHm in H. destruct H as [x Hx]. exists (Some x). apply Hx.
Qed.

(*TODO: need inverse (with ssreflect we can get for free but whatever)*)

(*TODO: is this the way to do with IH?*)
Lemma fin_blist_proof: forall {m: nat} {A: Type} (b: blist A m) (k: finite m),
  nat_of_fin k <? length (proj1_sig b).
Proof.
  intros. apply Nat.ltb_lt. 
  replace (length (proj1_sig b)) with m.
  apply nat_of_fin_range. destruct b. simpl. auto.
Qed.

(*TODO: define finmap list differently so this lemma isnt needed*)
Lemma finmap_list_nth: forall {m: nat} {A: Type} (b: blist A m) (k: finite m),
  finmap_list _ b k = nth_inb (nat_of_fin k) (proj1_sig b) (fin_blist_proof b k).
Proof.
  intros. generalize dependent (fin_blist_proof b k).
  induction m; intros.
  - destruct k.
Admitted. 

(*Many lemmas are way easier just using "nth", as long as we have a 
  default element*)
Lemma nth_inb_nth: forall {A: Type} (n: nat) (l: list A) (Hn: n <? length l) (x: A),
  nth_inb n l Hn = nth n l x.
Proof.
  intros A n. induction n; intros; destruct l; simpl; auto; inversion Hn.
Qed.

Definition fin_default (m: nat) : finite (S m) :=
  match m with
  | O => tt
  | _ => None
  end.

Lemma nth_all_fins: forall (m: nat) (k: finite m) 
(H: nat_of_fin k <? length (all_fins m)),
nth_inb (nat_of_fin k) (all_fins m) H = k.
Proof.
  intros. destruct m.
  - inversion k.
  - rewrite nth_inb_nth with (x:=fin_default m).
    generalize dependent (fin_default m).
    induction (S m) as [| m' IHm'].
    + inversion k.
    + destruct m' as [| m''].
      * simpl. destruct k. reflexivity.
      * intros default.
      replace (all_fins (S (S m''))) with (map Some (all_fins (S m'')) ++ [None]) by reflexivity.
        destruct k.
        -- replace (@nat_of_fin (S (S m'')) (Some f)) with (nat_of_fin f) by reflexivity.
          rewrite app_nth1 by 
            (rewrite map_length, all_fins_length; apply nat_of_fin_range).
          rewrite map_nth_inbound with (d2:= fin_default m'') by 
            (rewrite all_fins_length; apply nat_of_fin_range).
          f_equal. apply IHm'.
          rewrite all_fins_length. apply Nat.ltb_lt. apply nat_of_fin_range.
        -- replace (@nat_of_fin (S (S m'')) (@None (finite (S m'')))) with (S m'') by reflexivity.
          rewrite app_nth2; rewrite map_length, all_fins_length; auto.
          rewrite Nat.sub_diag. reflexivity.
Qed.

Definition finite_fun_blist {n: nat} {A: finite n -> Type} 
(ns: finite n -> nat)
(f: forall (j: finite n) (x: finite (ns j)), A j):
{h: forall j: finite n, blist (A j) (ns j) |  forall j (k: finite (ns j)),
  f j k = finmap_list (ns j) (h j) k}.
Proof.
  (*Let's do blist first*)
  refine (exist _ (fun j => make_blist (ns j) (map (fun fin => f j fin) (all_fins (ns j))) 
    (eq_trans (map_length _ _) (all_fins_length (ns j)))) _).
  intros.
  rewrite finmap_list_nth. simpl.
  assert (nat_of_fin k <? length (all_fins (ns j))). {
    rewrite all_fins_length. apply Nat.ltb_lt. apply nat_of_fin_range.
  }
  rewrite nth_inb_map with (Hn1 :=H).
  rewrite nth_all_fins. reflexivity.
Qed.

(*Can we prove this?*)
(*TODO: use ssreflect to remove functional extensionality axiom*)
Lemma all_constrs: forall (l: list (typesym * list funsym)) (n: finite (length l))
  (Hnontriv: forall constrs, In constrs (map snd l) -> constrs <> nil)
  (Huniq: forall constrs, In constrs (map snd l) -> nodupb funsym_eq_dec constrs)
  (x: mk_adts l n),
  {f: funsym & {t: in_bool funsym_eq_dec f (snd (fin_nth l n)) * build_constr_base f *
     forall (x: finite (length l)), blist (mk_adts l x) 
    (count_rec_occ (fst (fin_nth l x)) f) | 
      x = make_constr l n f (fst (fst t)) (snd (fst t)) (snd t)}}.
Proof.
  intros. unfold mk_adts in x. dependent destruction x.
  unfold make_constr.
  set (constrs:= (fin_nth l i)) in *.
  unfold build_base in a.
  destruct a as [[f' base] Hinf']. simpl in *.
  apply (existT _ f').
  unfold build_constr_rec in f.
  pose proof (@finite_fun_blist (length l) _ (fun j => count_rec_occ (fst (fin_nth l j)) f') f) as h.
  destruct h as [h Hhf].
  apply exist with (x:=(Hinf', base, h)).
  f_equal. repeat (apply functional_extensionality_dep; intros).
  rewrite Hhf. reflexivity.
Qed.

(* Handle nested types*)
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
  - simpl. simpl in x. inversion x.
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
  (Build_funsym name params args (vty_cons ret_ts (map vty_var ret_args)) eq_refl).

Definition triv_vars : typevar -> Set := fun _ => empty.
Definition triv_syms: typesym -> list vty -> Set := fun _ _ => empty.
Definition triv_context : context := nil.

Notation triv_adt := (mk_adt triv_context triv_vars triv_syms).
Notation triv_constr := (make_constr_simple triv_context triv_vars triv_syms).

Notation triv_bb_to_bb' := (bb_to_bb' triv_context triv_vars triv_syms).
Notation triv_build_base := (build_base triv_context triv_vars triv_syms).

Definition emp_fun {A: Type} : empty -> A := fun x =>
match x with end.



(*Unit*)
Definition ts_unit : typesym := mk_ts "unit" nil eq_refl.
Definition fs_tt := mk_fs "tt" nil nil ts_unit nil.

Definition aunit := triv_adt ts_unit [ fs_tt].

Definition att := triv_constr ts_unit [fs_tt] fs_tt eq_refl tt
  (mk_blist 0 nil eq_refl). 

Lemma aunit_correct: aunit = W (finite 1) (fun _ => triv_build_base [fs_tt]) (fun _ _ _ => empty) tt.
Proof. 
  unfold aunit, triv_adt, mk_adts, triv_build_base. simpl. f_equal.
  repeat(apply functional_extensionality_dep; intros).
  destruct x1 as [[f base] Hf]. simpl in *. destruct (funsym_eq_dec f fs_tt); auto; subst.
  reflexivity. inversion Hf.
Qed. 

Ltac prove_constr :=
  unfold triv_constr, make_constr_simple, make_constr; simpl;
  let He := fresh "Heq" in
  match goal with | |- mkW ?i ?a ?b ?x ?a1 ?f = mkW ?i ?a ?b ?x ?a2 ?f2 =>
    assert (He: a1 = a2) end;
  [unfold eq_rect; rewrite (all_funsym_refl (reflect_true _ _)); reflexivity|
  apply mkW_eq_aux with (Heq:=He); intros; unfold eq_rect, eq_ind_r, eq_ind;
  try rewrite (all_funsym_refl (eq_sym _))].

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