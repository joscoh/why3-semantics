(*Recursive Functions*)
Require Import Syntax.
Require Import Types.
Require Import Typing.
Require Import Semantics.
Require Import IndTypes.
Require Import Hlist.
Require Import Denotational.
From Equations Require Import Equations.
Require Import Coq.Logic.Eqdep_dec.

(*First, define syntactic restriction on functions*)

(*For our purposes here, a function declaration is a tuple
  consisting of the name, arguments, index of the argument that
  is decreasing, and body*)
Record fn := mk_fn {fn_name: funsym; fn_args: list vsymbol;
  fn_idx : nat; fn_idx_in: fn_idx <? length fn_args}.
Record pn := mk_pn {pn_name: predsym; pn_args: list vsymbol;
  pn_idx: nat; pn_idx_in: pn_idx <? length pn_args}.

(*TODO: combine with [predsym_in]*)
Fixpoint funsym_in_tm (f: funsym) (t: term) : bool :=
  match t with
  | Tfun fs _ tms => funsym_eq_dec f fs || existsb (funsym_in_tm f) tms
  | Tlet t1 _ t2 => funsym_in_tm f t1 || funsym_in_tm f t2
  | Tif f1 t1 t2 => funsym_in_fmla f f1 || funsym_in_tm f t1 ||
    funsym_in_tm f t2
  | Tmatch t1 _ ps => funsym_in_tm f t1 ||
    existsb (fun x => funsym_in_tm f (snd x)) ps
  | Teps f1 _ => funsym_in_fmla f f1
  | _ => false
  end
  with funsym_in_fmla (f: funsym) (f1: formula) : bool :=
  match f1 with
  | Fpred _ _ tms => existsb (funsym_in_tm f) tms
  | Feq _ t1 t2 => funsym_in_tm f t1 || funsym_in_tm f t2
  | Fbinop _ fm1 fm2 => funsym_in_fmla f fm1 || funsym_in_fmla f fm2
  | Fquant _ _ f' | Fnot f' => funsym_in_fmla f f'
  | Flet t _ f' => funsym_in_tm f t || funsym_in_fmla f f'
  | Fif fm1 fm2 fm3 => funsym_in_fmla f fm1 || funsym_in_fmla f fm2 ||
    funsym_in_fmla f fm3
  | Fmatch t _ ps => funsym_in_tm f t ||
    existsb (fun x => funsym_in_fmla f (snd x)) ps
  | _ => false
  end.

Fixpoint test {A: Type} (l: list A) : list A :=
  match l with
  | nil => nil
  | x :: t =>
    match t with
    | nil => nil
    | y :: v => test v
    end
  end.

Fixpoint test2 {A: Type} (l: list A) : list A :=
  match (length l =? 8) with
  | true => nil
  | false => match l with
                | nil => nil
                | x :: t => test2 t
                end
  end.

Fixpoint testpred {A: Type} (l1 l2: list A) : Prop :=
  forall x,
    match l1 with
    | nil => False
    | _ :: t => testpred t x
    end.

(*PROBLEM! My syntax is not correct - functions and predicates
  can be recursive together - so we need something like:
  list (Either fn pn)
  or maybe nicer - list of fs followed by list of ps
  (we can always reorder)*)

(*The list of vsymbols denotes all variables we "know" to be
  smaller than the argument, which is the second argument to the
  relation*)
(*TODO: do as "set", remove bound vars*)
Inductive decrease_fun (fs: list fn) (ps: list pn) : 
  list vsymbol -> vsymbol -> term -> Prop :=
  (*First, the recursive function call case*)
  | Dec_fun_in: forall (small: list vsymbol) (hd: vsymbol) 
    (f: funsym) (f_decl: fn) (l: list vty) (ts: list term),
    In f_decl fs ->
    f = fn_name f_decl ->
    (*The decreasing argument must be in our list of decreasing terms*)
    In (nth (fn_idx f_decl) (fn_args f_decl) vs_d) small ->
    (*None of [fs] of [ps] appear in the terms*) 
    (*TODO: will likely need this to show we can ignore function binding in interp for recursive cases*)
    (forall f t, In f fs -> In t ts -> negb (funsym_in_tm (fn_name f) t)) ->
    (forall p t, In p ps -> In t ts -> negb (predsym_in_term (pn_name p) t)) ->
    (*Then this recursive call is valid*)
    decrease_fun fs ps small hd (Tfun f l ts)
  (*Other function call*)
  | Dec_fun_notin: forall (small: list vsymbol) (hd: vsymbol) 
    (f: funsym) (l: list vty) (ts: list term),
    ~ In f (map fn_name fs) ->
    (*In this case, just recursive*)
    Forall (decrease_fun fs ps small hd) ts ->
    decrease_fun fs ps small hd (Tfun f l ts)
  (*Pattern match on var - this is how we add new, smaller variables*)
  | Dec_tmatch: forall (small: list vsymbol) (hd: vsymbol)
    (mvar: vsymbol) (v: vty) (pats: list (pattern * term)),
    (*TODO: can we only match on a variable?*)
    mvar = hd \/ In mvar small ->
    (*TODO: don't allow repeated matches on same variable*)
    Forall (fun x => decrease_fun fs ps (pat_fv (fst x) ++ small) mvar (snd x)) pats ->
    decrease_fun fs ps small hd (Tmatch (Tvar mvar) v pats) 
  (*Other pattern match is recursive case*)
  | Dec_tmatch_rec: forall (small: list vsymbol) (hd: vsymbol)
    (tm: term) (v: vty) (pats: list (pattern * term)),
    ~(exists var, tm = Tvar var /\ (var = hd \/ In var small)) ->
    Forall (fun x => decrease_fun fs ps small hd (snd x)) pats ->
    decrease_fun fs ps small hd (Tmatch tm v pats)
  (*Now the easy cases: Constants, Variables always decreasing*)
  | Dec_var: forall (small : list vsymbol) (hd: vsymbol) (v: vsymbol),
    decrease_fun fs ps small hd (Tvar v)
  | Dec_const: forall (small : list vsymbol) (hd: vsymbol) (c: constant),
    decrease_fun fs ps small hd (Tconst c)
  (*Recursive cases: let, if, eps*)
  | Dec_tlet: forall (small: list vsymbol) (hd: vsymbol) (t1: term)
    (v: vsymbol) (t2: term),
    decrease_fun fs ps small hd t1 ->
    decrease_fun fs ps small hd t2 ->
    decrease_fun fs ps small hd (Tlet t1 v t2)
  | Dec_tif: forall (small: list vsymbol) (hd: vsymbol) (f1: formula)
    (t1 t2: term),
    decrease_pred fs ps small hd f1 ->
    decrease_fun fs ps small hd t1 ->
    decrease_fun fs ps small hd t2 ->
    decrease_fun fs ps small hd (Tif f1 t1 t2)
  | Dec_eps: forall (small: list vsymbol) (hd: vsymbol) (f: formula)
    (v: vsymbol),
    decrease_pred fs ps small hd f ->
    decrease_fun fs ps small hd (Teps f v)
(*This is very similar*)
with decrease_pred (fs: list fn) (ps: list pn) : 
  list vsymbol -> vsymbol -> formula -> Prop :=
  (*First, the recursive predicate call case*)
  | Dec_pred_in: forall (small: list vsymbol) (hd: vsymbol) 
    (p: predsym) (p_decl: pn) (l: list vty) (ts: list term),
    In p_decl ps ->
    p = pn_name p_decl ->
    (*The decreasing argument must be in our list of decreasing terms*)
    In (nth (pn_idx p_decl) (pn_args p_decl) vs_d) small ->
    (*None of [fs] or[ps] appear in the terms*) 
    (*TODO: will likely need this to show we can ignore function binding in interp for recursive cases*)
    (forall f t, In f fs -> In t ts -> negb (funsym_in_tm (fn_name f) t)) ->
    (forall p t, In p ps -> In t ts -> negb (predsym_in_term (pn_name p) t)) ->
    (*Then this recursive call is valid*)
    decrease_pred fs ps small hd (Fpred p l ts)
  (*Other predicate call*)
  | Dec_pred_notin: forall (small: list vsymbol) (hd: vsymbol) 
    (p: predsym) (l: list vty) (ts: list term),
    ~ In p (map pn_name ps) ->
    (*In this case, just recursive*)
    Forall (decrease_fun fs ps small hd) ts ->
    decrease_pred fs ps small hd (Fpred p l ts)
  (*Pattern match on var - this is how we add new, smaller variables*)
  | Dec_fmatch: forall (small: list vsymbol) (hd: vsymbol)
    (mvar: vsymbol) (v: vty) (pats: list (pattern * formula)),
    (*TODO: can we only match on a variable?*)
    mvar = hd \/ In mvar small ->
    (*TODO: don't allow repeated matches on same variable*)
    Forall (fun x => decrease_pred fs ps (pat_fv (fst x) ++ small) mvar (snd x)) pats ->
    decrease_pred fs ps small hd (Fmatch (Tvar mvar) v pats) 
  (*Other pattern match is recursive case*)
  | Dec_fmatch_rec: forall (small: list vsymbol) (hd: vsymbol)
    (tm: term) (v: vty) (pats: list (pattern * formula)),
    ~(exists var, tm = Tvar var /\ (var = hd \/ In var small)) ->
    Forall (fun x => decrease_pred fs ps small hd (snd x)) pats ->
    decrease_pred fs ps small hd (Fmatch tm v pats)
  (*Easy cases: true, false*)
  | Dec_true: forall (small: list vsymbol) (hd: vsymbol),
    decrease_pred fs ps small hd Ftrue
  | Dec_false: forall (small: list vsymbol) (hd: vsymbol),
    decrease_pred fs ps small hd Ffalse
  (*Recursive cases: quantifier, eq, binop, let, if*)
  | Dec_quant: forall (small: list vsymbol) (hd: vsymbol)
    (q: quant) (v: vsymbol) (f: formula),
    decrease_pred fs ps small hd f ->
    decrease_pred fs ps small hd (Fquant q v f)
  | Dec_eq: forall (small: list vsymbol) (hd: vsymbol)
    (ty: vty) (t1 t2: term),
    decrease_fun fs ps small hd t1 ->
    decrease_fun fs ps small hd t2 ->
    decrease_pred fs ps small hd (Feq ty t1 t2)
  | Dec_binop: forall (small: list vsymbol) (hd: vsymbol)
    (b: binop) (f1 f2: formula),
    decrease_pred fs ps small hd f1 ->
    decrease_pred fs ps small hd f2 ->
    decrease_pred fs ps small hd (Fbinop b f1 f2)
  | Dec_flet: forall (small: list vsymbol) (hd: vsymbol) (t1: term)
    (v: vsymbol) (f: formula),
    decrease_fun fs ps small hd t1 ->
    decrease_pred fs ps small hd f ->
    decrease_pred fs ps small hd (Flet t1 v f)
  | Dec_fif: forall (small: list vsymbol) (hd: vsymbol) 
    (f1 f2 f3: formula),
    decrease_pred fs ps small hd f1 ->
    decrease_pred fs ps small hd f2 ->
    decrease_pred fs ps small hd f3 ->
    decrease_pred fs ps small hd (Fif f1 f1 f2)
    .
    
(*TODO: write decidable version*)


(*Now let's see what the signature for such a function looks like*)

(*Want: Definition _ : forall (f: funsym) (srts: list sort),
  arg_list (domain (dom_aux pd)) (funsym_sigma_args f srts) ->
  domain (dom_aux pd (funsym_sigma_ret f srts))
  *)

Section FunDef.


Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma)
{pd: pi_dom} (all_unif: forall m, mut_in_ctx m gamma -> IndTypes.uniform m)
  {vt: @val_typevar sigma} {pf: pi_funpred gamma_valid pd}.
 
Notation domain := (domain (dom_aux pd)).
Notation val x :=  (v_subst (v_typevar vt) x).


(*We will handle mutual recursion by giving an index*)
(*i is the index of the function that we build - TODO: should this
  be bounded/dependent*)

(*This is the "inner" function, assuming we already have the argument
  that is recursive*)
(*Require Import Denotational.*)


(*TODO: where do we need the bodies?*)
Variable (fs: list fn) (ps: list pn).

(*Let's try this at first*)
Inductive list_rel {A: Type} : list A -> list A -> Prop :=
  | LR_constr: forall x t l,
    l = x :: t ->
    list_rel t l.

Lemma list_rel_wf: forall A, well_founded (@list_rel A).
Proof.
  intros. unfold well_founded. intros. induction a; simpl.
  constructor. intros. inversion H; subst. inversion H0.
  constructor. intros. inversion H; subst.
  inversion H0; subst. apply IHa.
Defined.

(*OK, how about mutual recursive type*)
Unset Elimination Schemes.
Inductive rosetree {A: Type} : Type :=
  | Leaf: A -> rosetree
  | Node: roselist -> rosetree
with roselist {A: Type} : Type :=
  | RL_nil : roselist
  | RL_cons: rosetree -> roselist -> roselist.
Set Elimination Schemes.

Scheme rosetree_ind := Induction for rosetree Sort Prop with
roselist_ind := Induction for roselist Sort Prop.


Inductive Either (A B: Type) : Type :=
  | Left: A -> Either A B
  | Right: B -> Either A B.


(*Now can we get a wf relation?*)
Inductive rose_rel {A: Type} : Either (@rosetree A) (@roselist A) -> 
  Either (@rosetree A) (@roselist A) -> Prop :=
  | RR_constr1: forall rt rl,
    rt = Node rl ->
    rose_rel (Right _ _ rl) (Left _ _ rt)
  | RR_constr2: forall rt rl x,
    rl = RL_cons rt x ->
    rose_rel (Left _ _ rt) (Right _ _ rl)
  | RR_constr3: forall rl1 rl2 x,
    rl1 = RL_cons x rl2 ->
    rose_rel (Right _ _ rl2) (Right _ _ rl1).

Set Bullet Behavior "Strict Subproofs".

Definition prop_either {A B: Type} (P: A -> Prop) (P1: B -> Prop):
  Either A B -> Prop :=
  fun x =>
  match x with
  | Left y => P y
  | Right y => P1 y
  end.

(*Lemma rose_tree_list_ind {A: Type} (P: @rosetree A -> Prop)
(P0: roselist -> Prop)
(Hleaf: forall a, P (Leaf a))
(Hnode: forall r, P0 r -> P(Node r))
(Hnil: P0 RL_nil)
(Hcons: forall r, P r -> forall r0, P0 r0 -> P0 (RL_cons r r0)):
*)

Definition either_rose_ind {A: Type} (P: @rosetree A -> Prop)
  (P0: roselist -> Prop) (P3: Either rosetree roselist -> Prop)
  (Hleaf: forall a, P (Leaf a))
  (Hnode: forall r, P0 r -> P(Node r))
  (Hnil: P0 RL_nil)
  (Hcons: forall r, P r -> forall r0, P0 r0 -> P0 (RL_cons r r0))
  (Hp3_1: forall x, P3 (Left _ _ x) <-> P x)
  (Hp3_2: forall x, P3 (Right _ _ x) <-> P0 x)
  :
  forall (x: Either rosetree roselist), P3 x.
Proof.
  intros. destruct x.
  - rewrite Hp3_1. apply rosetree_ind with(P0:=P0); auto.
  - rewrite Hp3_2. apply roselist_ind with(P:=P); auto.
Qed.

Lemma rose_rel_wf: forall A, well_founded (@rose_rel A).
Proof.
  intros. unfold well_founded.
  apply either_rose_ind with(P:= fun x => Acc rose_rel (Left _ _ x))
    (P0:= fun y => Acc rose_rel (Right _ _ y)); intros.
  - constructor. intros. inversion H; subst. inversion H2.
  - constructor. intros. inversion H0; subst.
    inversion H3; subst. apply H.
  - constructor. intros. inversion H; subst; inversion H2.
  - constructor. intros. inversion H1; subst;
    inversion H4; subst; assumption.
  - reflexivity.
  - reflexivity.
Qed.

Instance rose_rel_wf': WellFounded
(Telescopes.tele_measure (Telescopes.tip (Either rosetree roselist))
   (Either rosetree (@roselist nat)) (fun o : Either rosetree roselist => o)
   rose_rel).
Proof.
  unfold WellFounded. apply rose_rel_wf.
Defined. 

Equations rose_size (*{A: Type}*) (o: Either (@rosetree nat) (@roselist nat)) : nat
  by wf o (@rose_rel nat) :=
  rose_size (Left (Leaf x)) := 1;
  rose_size (Left (Node l)) := rose_size (Right _ _ l);
  rose_size (Right RL_nil) := 0;
  rose_size (Right (RL_cons t ls)) :=
    rose_size (Left _ _ t) + rose_size (Right _ _ ls).
Next Obligation.
  constructor. reflexivity.
Defined.
Next Obligation.
  eapply RR_constr2. reflexivity.
Defined.
Next Obligation.
  eapply RR_constr3. reflexivity.
Defined.

(*Next, want to make polymoprhic by including type there*)
(*Now can we get a wf relation?*)
Inductive rose_rel2: {A: Type & Either (@rosetree A) (@roselist A)} -> 
  {A: Type & Either (@rosetree A) (@roselist A)} -> Prop :=
  | RR_constr1': forall A rt rl,
    rt = Node rl ->
    rose_rel2 (existT _ A (Right _ _ rl)) (existT _ A (Left _ _ rt))
  | RR_constr2': forall A rt rl x,
    rl = RL_cons rt x ->
    rose_rel2 (existT _ A (Left _ _ rt)) (existT _ A (Right _ _ rl))
  | RR_constr3': forall A rl1 rl2 x,
    rl1 = RL_cons x rl2 ->
    rose_rel2 (existT _ A (Right _ _ rl2)) (existT _ A (Right _ _ rl1)).

Lemma rose_rel2_wf:well_founded (rose_rel2).
Proof.
  unfold well_founded.
  (*Can intros A because it is fixed (by definition) - will
    this be true in why3 types?*)
  intros [A o]. revert o.
  apply either_rose_ind with(P:= fun x => Acc rose_rel2 (existT _ A (Left _ _ x)))
    (P0:= fun y => Acc rose_rel2 (existT _ A (Right _ _ y))); intros.
  - constructor. intros. inversion H; subst. inversion H3.
  - constructor. intros. inversion H0; subst.
    inversion H4; subst.
    (*In real one, will be able to have decidable types
    (quantify with vty)*)
    apply Eqdep.EqdepTheory.inj_pair2 in H2.
    (*Hmm, annoying things with existT - ToDO*)
    (*apply Eqdep_dec.inj_pair2_eq_dec in H2.*)
    subst. assumption.
  - constructor. intros. inversion H; subst; inversion H3.
  - constructor. intros. inversion H1; subst; inversion H5;
    apply Eqdep.EqdepTheory.inj_pair2 in H3;
    apply Eqdep.EqdepTheory.inj_pair2 in H4; subst; assumption.
  - reflexivity.
  - reflexivity.
Qed.

Instance rose_rel2_wf': WellFounded
(Telescopes.tele_measure
   (Telescopes.tip {A : Type & Either rosetree roselist})
   {A : Type & Either rosetree roselist}
   (fun o : {A : Type & Either rosetree roselist} => o) rose_rel2).
Proof.
  apply rose_rel2_wf.
Defined.

Equations rose_size2 (*{A: Type}*) 
  (o: {A: Type & Either (@rosetree A) (@roselist A) }) : nat
  by wf o (rose_rel2) :=
  rose_size2 (existT _ A (Left (Leaf x))) := 1;
  rose_size2 (existT _ A (Left (Node l))) := 
    rose_size2 (existT _ A (Right _ _ l));
  rose_size2 (existT _ A (Right RL_nil)) := 0;
  rose_size2 (existT _ A (Right (RL_cons t ls))) :=
    rose_size2 (existT _ A (Left _ _ t)) + rose_size2 (existT _ A (Right _ _ ls)).
Next Obligation.
  constructor. reflexivity.
Defined.
Next Obligation.
  eapply RR_constr2'. reflexivity.
Defined.
Next Obligation.
  eapply RR_constr3'. reflexivity.
Defined.

(*OK, so now I want to try a non-terminating function
  using my approach, and see where it goes wrong*)

(*Idea: function on two lists, pattern match on both*)
(*
Fixpoint foo {A: Type} (l1 l2: list A)  : list A :=
  match l1, l2 with
  | x1 :: t1, x2 :: t2 => foo t1 (x1 :: x2 :: t2)
  | _, x2 :: t2 => foo [x2] t2
  | _, _ => nil
  
  end.
*)

(*Now we will define a well-founded relation on
  pairs of lists*)
(*Is this well-founded?*)
Definition pairlist_rel : 
  (bool * (list nat * list nat)) -> (bool * (list nat * list nat)) -> Prop :=
  fun x1 x2 =>
    match x1, x2 with
    | (b1, (l11, l12)), (b2, (l21, l22)) =>
    list_rel (if b1 then l11 else l12) (if b2 then l21 else l22)
    end.

(*
Lemma pairlist_rel_wf: well_founded pairlist_rel.

Good, we can't prove this - but what should we do?
  Key idea: every invocation of the SAME function must use the same
  index.

  For non mutual - we have a single index, look at
  arg_lists, compare this single (fixed) index.
  This should be prvable: example 
*)
Definition pairlist_fstrel: (bool * (list nat * list nat)) ->
  (bool * (list nat * list nat)) -> Prop :=
  fun x1 x2 =>
  match x1, x2 with
    | (b1, (l11, l12)), (b2, (l21, l22)) =>
    if b1 && b2 then list_rel l11 l21 else False
  end.

Lemma pairlist_rel_wf: well_founded pairlist_fstrel.
Proof.
  unfold well_founded. intros.
  destruct a as [b [l1 l2]].
  revert l2.
  (*Key: Only need to generalize/do induction on l1*)
  induction l1; simpl.
  - constructor. intros. unfold pairlist_fstrel in H.
    destruct y; destruct p. destruct b0; destruct b; inversion H.
    inversion H0.
  - constructor. intros. unfold pairlist_fstrel in H.
    destruct y; destruct p. destruct b0; destruct b; inversion H.
    subst. inversion H0; subst.
    apply IHl1.
Qed.

(*For the mutual case, we will need a different index
  for each function*)
(*How can we prove that this is WF? I guess our relation is
  something like:
  {f: funsym & funsym_sigma_args sigma f}
  or so, then internally we use the index
  How can we model this here?
  *) 

(*I think - do single first, then worry about mutual when we
  see what we need - should be OK*)

(*TODO: first, we will do this for the non-mutual case with
  just a single function. Then, we will add mutual recursion*)

(*Let's define the relation*)


(*TODO: see if we need*)
Lemma val_sorts_eq (srts: list sort):
  map (v_subst (v_typevar vt)) (map sort_to_ty srts) = srts.
Proof.
  apply list_eq_ext'; rewrite !map_length; auto.
  intros.
  rewrite map_nth_inbound with(d2:=vty_int). 2: rewrite map_length; lia.
  rewrite map_nth_inbound with(d2:=d); auto.
  symmetry. apply subst_sort_eq.
Qed.

(*Induction for ADTS*)
Section Induction.

(*First, we need an induction principle for ADTs (TODO: move
  to IndTypes?)
  We of course rely on the induction principle for W-types, but
  our encoding is very complicated, so it is very difficult
  to get this into a usable form. We need lots of typecasts
  and intermediate results
  *)

Definition cast_w {I: Set} {A: I -> Set} {B: forall i: I, I -> A i -> Set}
  {i1 i2: I} (Heq: i1 = i2) (w: W I A B i1) : W I A B i2 :=
  match Heq with
  | eq_refl => w
  end.

Definition cast_a {I: Set} {A: I -> Set} {i1 i2: I} (Heq: i1 = i2)
  (a: A i1) : A i2 := scast (f_equal A Heq) a.

Definition cast_b {I: Set} {A: I -> Set} {B: forall i: I, I -> A i -> Set}
  {i1 i2 j: I} (Heq: i1 = i2) {a: A i1} (b: B i1 j a) :
    B i2 j (cast_a Heq a).
  destruct Heq. exact b.
Defined.

Lemma cast_a_sym {I: Set} {A: I -> Set} {i1 i2: I} (Heq: i1 = i2)
(a: A i1): cast_a (eq_sym Heq) (cast_a Heq a) = a.
Proof.
  unfold cast_a. subst. reflexivity.
Defined. 

Lemma cast_w_mkw {I: Set} {A: I -> Set} {B: forall i: I, I -> A i -> Set}
{i1 i2: I} (Heq: i1 = i2) (a: A i1) (f: forall j: I, B i1 j a -> W I A B j):
  cast_w Heq (mkW I A B i1 a f) =
  mkW I A B i2 (cast_a Heq a) 
  (fun (j: I) (b: B i2 j (@cast_a I A _ _ Heq a)) =>
    let b' : B i1 j (cast_a (eq_sym Heq) (cast_a Heq a)) 
      := cast_b (eq_sym Heq) b in
    let b'': B i1 j a := scast (f_equal (B i1 j) (cast_a_sym Heq a)) b' in
    f j b'').
Proof.
  unfold cast_w. subst. simpl. unfold cast_a. simpl.
  unfold scast, cast_a_sym. f_equal.
Qed. 

Lemma cast_i (m: mut_adt) (m_in: mut_in_ctx m gamma) (i: finite (length (adts m))):
  i = get_idx adt_dec (fin_nth (adts m) i) (adts m)
  (In_in_bool adt_dec (fin_nth (adts m) i) (typs m) (fin_nth_in (adts m) i)).
Proof.
  rewrite get_idx_fin; auto.
  apply (adts_nodups gamma_valid). apply m_in.
Qed.

Definition cast_adt_rep {m srts t1 t2 tin1 tin2}
  (H: t1 = t2)
  (x: adt_rep m srts (dom_aux pd) t1 tin1):
  adt_rep m srts (dom_aux pd) t2 tin2.
  revert x. unfold adt_rep, mk_adts.
  apply cast_w. subst. f_equal. apply bool_irrelevance.
Defined.

(*Relies on decidability of domain*)
Lemma cast_w_twice {I: Set} {A: I -> Set} {B: forall i: I, I -> A i -> Set}
{i1 i2: I}
(eq_dec: forall x y: I, {x=y} + {x<>y})
(Heq: i1 = i2) (Heq2: i2 = i1) (w: W I A B i1):
  cast_w Heq2 (cast_w Heq w) = w.
Proof.
  subst. unfold cast_w. assert (Heq2=eq_refl). apply UIP_dec. auto.
  rewrite H. reflexivity.
Qed.

(*We can rewrite under a proposition for equivalent ADTs*)
(*These lemmas show why it is critical to have a bool for t_in*)
Lemma rewrite_P {m srts}
(P: forall t t_in, adt_rep m srts (dom_aux pd) t t_in -> Prop):
forall t1 t2 t_in1 t_in2 (Ht: t1 = t2) x,
  P t1 t_in1 x <-> P t2 t_in2 (cast_adt_rep Ht x).
Proof.
  intros. unfold cast_adt_rep. unfold cast_w, eq_ind_r, eq_ind.
  subst. simpl. 
  destruct ((bool_irrelevance (adt_in_mut t2 m) t_in1 t_in2)).
  simpl. reflexivity.
Qed.

Lemma map_map_eq {A B: Type} (f: A -> B) (l: list A):
  seq.map f l = map f l.
Proof. reflexivity. Qed.

(*TODO: maybe separate out into separate lemma*)
(*We show that if the interpretation of a type is
  the ADT applied to sorts, the type of the constructor
  must have been the ADT name applied to the args.
  This is not as trivial as it would seem; we need to
  show it cannot be some typesym which is given the ADT
  as an interpretation. We do this by showing such a
  list would be impossible to construct in the following
  few functions. This seems a bit hacky:*)

(*A list of the "smaller" types contained in a type*)
Definition subterm_ty (v: vty) : list vty :=
  match v with
  | vty_cons _ tys => tys
  | _ => nil
  end.

Fixpoint vty_size (v: vty) : nat :=
  match v with
  | vty_int => 1
  | vty_real => 1
  | vty_var _ => 1
  | vty_cons _ ts => 1 + sum (map vty_size ts)
  end.

Definition vtys_size (l: list vty) : nat :=
  sum (map vty_size l).

Lemma vty_size_eq (v: vty):
  vty_size v =
  match v with
  | vty_int => 1
  | vty_real => 1
  | vty_var _ => 1
  | vty_cons _ ts => 1 + vtys_size ts
  end.
Proof.
  destruct v; auto.
Qed.

(*The size of a single type is smaller than 
  the whole list*)
Lemma vtys_size_in (l: list vty) (t: vty):
  In t l ->
  vty_size t <= vtys_size l.
Proof.
  unfold vtys_size.
  induction l; simpl; intros; auto. destruct H.
  destruct H; subst; try lia.
  specialize (IHl H). lia.
Qed.
  
(*An obvious lemma but one that is tricky to prove.
  We prove this by giving the above size function
  and proving that if (vty_cons t l) is in l, then
  it has a smaller size than l, a contradiction *)
(*Note: I believe that the same proof holds for any
  coutable type*)
Lemma sub_not_whole : forall t l,
   ~ In (vty_cons t l) l.
Proof.
  intros. intro C.
  apply vtys_size_in in C.
  rewrite vty_size_eq in C. lia.
Qed.

(*As a corollary, we get the following*)
Lemma list_srts_not_whole (n: nat) (tys: list vty) (ts: typesym):
  nth n tys vty_int <> vty_cons ts tys.
Proof.
  assert (n < length tys \/ length tys <= n) by lia. destruct H.
  - intro C.
    apply (sub_not_whole ts tys). rewrite <- C.
    apply nth_In; auto.
  - rewrite nth_overflow; auto. intro C; inversion C.
Qed. 

Theorem adts_from_constrs {m: mut_adt} (m_in: mut_in_ctx m gamma)
  (i: finite (length (adts m))) (c: funsym) 
  (c_in: constr_in_adt c (fin_nth (adts m) i))
  (t': alg_datatype) (t_in': adt_in_mut t' m)
  (j: nat) (srts: list sort)
  (Hj: j < Datatypes.length (s_args c))
  (Hlen: Datatypes.length srts = Datatypes.length (m_params m))
  (Hnth: nth j (funsym_sigma_args c srts) s_int =
    typesym_to_sort (adt_name t') srts):
  nth j (s_args c) vty_int =
    vty_cons (adt_name t') (map vty_var (ts_args (adt_name t'))).
Proof.
  assert (Hini: adt_in_mut (fin_nth (adts m) i) m). {
    apply In_in_bool. apply fin_nth_in.
  }
  assert (Hparams: (s_params c) = (m_params m)). {
    eapply adt_constr_params. apply gamma_valid.
    auto. apply Hini. apply c_in. 
  }
  revert Hnth.
  unfold funsym_sigma_args, typesym_to_sort, ty_subst_list_s.
  rewrite map_nth_inbound with(d2:=vty_int); auto.
  unfold ty_subst_s, v_subst; intros Heq.
  inversion Heq. clear Heq.
  destruct (nth j (s_args c) vty_int) eqn : Hnth; simpl in H0;
  try solve[inversion H0].
  - destruct (in_dec typevar_eq_dec t (s_params c)).
    + destruct (In_nth _ _ EmptyString i0) as [n [Hn Hnthn]].
      rewrite <- Hnthn in H0.
      rewrite ty_subst_fun_nth with(s:=vty_int) in H0; auto.
      * unfold sorts_to_tys in H0.
        exfalso.
        (*We get contradiction: can't have srts inside srts
          This proves that this case cannot happen*)
        apply (list_srts_not_whole n (sorts_to_tys srts) (adt_name t')); auto.
      * unfold sorts_to_tys. rewrite map_length, Hlen, Hparams.
        reflexivity.
      * apply s_params_Nodup.
    + rewrite ty_subst_fun_notin in H0; auto. inversion H0.
  - (*The case that can actually happen: cons*)
    inversion H0; subst. clear H0. 
    (*Use uniformity - just instantiate all hyps, takes a while
      should automate*)
    assert (Hunif: uniform m). {
      apply all_unif. auto.
    }
    unfold uniform in Hunif. unfold is_true in Hunif. 
    rewrite forallb_forall in Hunif.
    specialize (Hunif (fin_nth (adts m) i) (in_bool_In _ _ _ Hini)).
    rewrite forallb_forall in Hunif.
    specialize (Hunif c).
    assert (Hinc: In c (ne_list_to_list (adt_constrs (fin_nth (adts m) i)))). {
      apply in_bool_ne_In with(eq_dec:=funsym_eq_dec).
      apply c_in.
    }
    specialize (Hunif Hinc).
    unfold uniform_list in Hunif.
    rewrite forallb_forall in Hunif.
    assert (Hincons: In (vty_cons (adt_name t') l) (s_args c)). {
      rewrite <- Hnth. apply nth_In; auto.
    }
    specialize (Hunif _ Hincons). simpl in Hunif.
    rewrite implb_true_iff in Hunif.
    assert (Htsin: ts_in_mut_list (adt_name t') (typs m)). {
      unfold adt_in_mut in t_in'. 
      unfold ts_in_mut_list. apply In_in_bool. rewrite in_map_iff.
      exists t'. split; auto. apply (in_bool_In _ _ _ t_in'). 
    }
    specialize (Hunif Htsin). simpl_sumbool.
    f_equal.
    erewrite adt_args with(m:=m); [| apply gamma_valid |].
    + reflexivity.
    + unfold adt_mut_in_ctx. split; auto.
Qed.

(*TODO: move this*)
(*Suppose we know that the ith element of a list satisfies a predicate.
  Then we can find a j such that nth j (filter p l) = nth i l;
  and moreover, we know exactly which j*)

Definition idx_filter {A: Type} (p: A -> bool) (l: list A)
  (n: nat) := length (filter p (firstn n l)).

Lemma idx_filter_length {A: Type} (p: A -> bool) (l: list A)
  (n: nat) (Hn: n < length l) (d: A):
  p (nth n l d) ->
  idx_filter p l n < length (filter p l).
Proof.
  generalize dependent n.
  unfold idx_filter. induction l; intros; simpl; auto. inversion Hn.
  simpl in Hn. destruct n; simpl.
  - simpl in H. rewrite H. simpl; lia.
  - simpl in H.
    specialize (IHl n (ltac:(lia)) H).
    destruct (p a); simpl; lia.
Qed.

Lemma idx_filter_le {A: Type} (p: A -> bool) (l: list A)
(n: nat):
idx_filter p l n <= length (filter p l).
Proof.
  unfold idx_filter.
  revert n. induction l; simpl; intros; destruct n; simpl; auto.
  - lia.
  - specialize (IHl n). destruct (p a); simpl; lia.
Qed.

Lemma firstn_skipn_nth {A: Type} (n: nat) (l: list A) (d: A):
  n < length l ->
  l = firstn n l ++ (nth n l d) :: skipn (S n) l.
Proof.
  revert n. induction l; simpl; intros.
  - inversion H.
  - destruct n; auto.
    simpl firstn. rewrite <- app_comm_cons.
    f_equal. apply IHl. lia.
Qed. 

Lemma idx_filter_correct {A: Type} (p: A -> bool) (l: list A)
  (n: nat) (Hn: n < length l) (d: A):
  p (nth n l d) ->
  nth (idx_filter p l n) (filter p l) d = nth n l d.
Proof.
  intros. unfold idx_filter.
  generalize dependent n. induction l; simpl; intros.
  - inversion Hn.
  - destruct n.
    + simpl. rewrite H. reflexivity.
    + simpl firstn. simpl filter.
      destruct (p a); simpl; apply IHl; auto; lia.
Qed.

(*We need this specific function and j value for the following
  lemma:*)
Lemma hnth_hlist_map_filter  {A B: Set} {f: A -> Set} {l: list B}
(f1: B -> A) (h: hlist f (map f1 l)) (g: B -> bool) j d1 d2 d3
(eq_dec: forall (x y: A), {x = y} + {x <> y})
(Hij: (nth j (map f1 l) d1) = (nth (idx_filter g l j) (map f1 (filter g l)) d1))
(Hg: g (nth j l d2)):
  hnth (idx_filter g l j) (hlist_map_filter f1 h g) d1 d3 =
  (scast (f_equal f Hij) (hnth j h d1 d3)).
Proof.
  revert Hij.
  generalize dependent j.
  induction l; intros; simpl in Hij |- *.
  - destruct j; simpl in *; subst;
    assert (Hij = eq_refl) by (apply UIP_dec; apply eq_dec);
    rewrite H; simpl; reflexivity.
  - destruct j; simpl in Hij |- *.
    + unfold idx_filter in *. simpl in *.
      destruct (g a) eqn : Ha; simpl in *.
      * assert (Hij = eq_refl). apply UIP_dec. apply eq_dec.
        rewrite H; reflexivity.
      * inversion Hg.
    + unfold idx_filter in *; simpl in *.
      destruct (g a) eqn : Ha; simpl in *;
      apply IHl; auto.
Qed.

(*Casting over dependent types/build_rec;
  this is where things get very tricky*)

Definition cast_dep {A: Set} (B: A -> Set) 
  {a1 a2: A} (Heq: a1 = a2) (x: B a1) : B a2 :=
  scast (f_equal B Heq) x.

(*Another level*)
Definition cast_dep' {A: Set} (B: A -> Set) (C: forall (a: A), B a -> Set)
  {a1 a2: A} (Heq: a1 = a2) (x: B a1) (y: C a1 x) :
  C a2 (cast_dep B Heq x).
  destruct Heq. unfold cast_dep. exact y.
Defined.

Lemma cast_fun' {T: Set} {A: Type} {B: A -> T -> Type} 
  {C: A -> Type} {t1 t2: T} 
  {f: forall (x: A)(y: B x t1), C x} (Heq: t1 = t2):
  forall x y,
  (cast (f_equal (fun (x: T) => forall (a: A)(b: B a x), C a) Heq) f) x y = 
  (fun (x: A) (y: B x t2) => 
    f x (cast (f_equal (B x) (Logic.eq_sym Heq)) y)) x y.
Proof.
  destruct Heq. simpl. intros. reflexivity.
Qed.

Lemma scast_get_constr_type {m: mut_adt}
  {i1 i2: finite (length (adts m))} (Heqi: i1 = i2)
  {vars typesyms c Hinc Hinc' x}:
  scast (f_equal 
    (fun n => build_base vars typesyms (adts m)
    (adt_constrs (fin_nth (adts m) n))) Heqi)
  (get_constr_type vars typesyms (adts m) (adt_name (fin_nth (adts m) i1))
    (adt_constrs (fin_nth (adts m) i1)) c Hinc x) =
  get_constr_type vars typesyms (adts m) (adt_name (fin_nth (adts m) i2))
    (adt_constrs (fin_nth (adts m) i2)) c Hinc' x.
Proof.
  unfold scast. destruct Heqi. simpl.
  assert (Hinc = Hinc') by (apply bool_irrelevance).
  rewrite H. reflexivity.
Qed.

(*Cast from one [build_rec] to another*)
Definition cast_build_rec_gen {m: mut_adt} {constrs1 constrs2}
  (Heq: constrs1 = constrs2) vars typesyms ts ts1 ts2 c Hinc1 Hinc2 b1 b2:
    build_rec vars typesyms (adts m) ts constrs1
      (get_constr_type vars typesyms (adts m) ts1 constrs1 c Hinc1 b1) ->
    build_rec vars typesyms (adts m) ts constrs2
      (get_constr_type vars typesyms (adts m) ts2 constrs2 c Hinc2 b2).
Proof.
  destruct Heq. assert (Hinc1 = Hinc2) by apply bool_irrelevance.
  intros A.
  apply finite_to_build_rec.
  eapply build_rec_to_finite. apply A.
Defined.

(*Annoying dependent reasons why we need extra typesym*)
Lemma build_rec_to_finite_cast {m: mut_adt} {constrs1 constrs2}
(Heq: constrs1 = constrs2) vars typesyms ts ts1 ts2 ts3 
  (Hts: ts2 = ts3) c Hinc1 Hinc2 b1 b2 x:
  @build_rec_to_finite vars typesyms (adts m) ts3 ts constrs2 c Hinc2 b2
    (cast_build_rec_gen Heq vars typesyms ts ts1 ts2 c Hinc1 Hinc2 b1 b2 x) =
  build_rec_to_finite vars typesyms (adts m) x.
Proof.
  destruct Hts.
  unfold cast_build_rec_gen. subst.
  rewrite build_rec_finite_inv2. reflexivity.
Qed.

Definition cast_build_rec {m: mut_adt} {i1 i2: finite (length (adts m))} 
(Heqi: i1 = i2)
vars typesyms ts c Hinc  x:
build_rec vars typesyms (adts m) ts (adt_constrs (fin_nth (adts m) i1))
  (get_constr_type vars typesyms (adts m) (adt_name (fin_nth (adts m) i1))
  (adt_constrs (fin_nth (adts m) i1)) c Hinc x) ->
build_rec vars typesyms (adts m) ts (adt_constrs (fin_nth (adts m) i2))
(scast (f_equal 
(fun n => build_base vars typesyms (adts m)
(adt_constrs (fin_nth (adts m) n))) Heqi)
(get_constr_type vars typesyms (adts m) (adt_name (fin_nth (adts m) i1))
(adt_constrs (fin_nth (adts m) i1)) c Hinc x)).
apply (cast_dep' 
  (fun i : finite (Datatypes.length (adts m)) =>
    build_base vars typesyms (adts m) (adt_constrs (fin_nth (adts m) i)))
  (fun (i : finite (Datatypes.length (adts m)))
    (t : build_base vars typesyms (adts m)
      (adt_constrs (fin_nth (adts m) i))) =>
    build_rec vars typesyms (adts m) ts (adt_constrs (fin_nth (adts m) i)) t)
  Heqi).
Defined.

(*Injectivity for [existT]*)

Lemma existT_inj_dec {U: Type} {P: U -> Type} (eq_dec: forall x y : U, {x = y} + {x <> y}) {x1 x2: U} {H1: P x1} (H2: P x2):
  existT P x1 H1 = existT P x2 H2 ->
  {Heq: x1 = x2 & H2 = cast (f_equal P Heq) H1}.
Proof.
  intros. assert (Hex:=H).
  apply EqdepFacts.eq_sigT_fst in H. subst.
  apply inj_pair2_eq_dec in Hex. 2: apply eq_dec. subst.
  apply (existT _ (Logic.eq_refl)). reflexivity.
Qed.

Lemma existT_inj {U: Type} {P: U -> Type} {x1 x2: U} {H1: P x1} (H2: P x2):
  existT P x1 H1 = existT P x2 H2 ->
  {Heq: x1 = x2 & H2 = cast (f_equal P Heq) H1}.
Proof.
  intros. assert (Hex:=H).
  apply EqdepFacts.eq_sigT_fst in H. subst.
  apply Eqdep.EqdepTheory.inj_pair2 in Hex. subst.
  apply (existT _ (Logic.eq_refl)). reflexivity.
Qed.

Lemma scast_scast {A B C: Set} (H1: B = A) (H2: C = B) x:
  scast H1 (scast H2 x) = scast (eq_trans H2 H1) x.
Proof.
  subst. reflexivity.
Qed.

(*Finally, we define a generalized induction principle on ADTs: 
  - Suppose we have P, a proposition on all ADTs in mut adt m
  - Suppose we know that, for any instance x = c(args) of
    an ADT in m, if P holds for all elements of args which are
    recursive, then P holds of x
  - Then P holds for all instances of ADTs in m  
  *)
Theorem adt_rep_ind m m_in srts
  (Hlen: length srts = length (m_params m)) 
  (P: forall t t_in, adt_rep m srts (dom_aux pd) t t_in -> Prop):
  (forall t t_in (x: adt_rep m srts (dom_aux pd) t t_in) 
    (c: funsym) (Hc: constr_in_adt c t) (a: arg_list domain (funsym_sigma_args c srts))
    (Hx: x = constr_rep gamma_valid m m_in srts Hlen (dom_aux pd) t t_in c
      Hc (Semantics.adts pd m srts) a),
    (forall i t' t_in' Heq, i < length (s_args c) ->
      (*If nth i a has type adt_rep ..., then P holds of it*)
      P t' t_in' (scast (Semantics.adts pd m srts t' t_in') 
        (dom_cast _ Heq (hnth i a s_int (dom_int pd)))) 
      ) ->
    P t t_in x
    ) ->
  forall t t_in (x: adt_rep m srts (dom_aux pd) t t_in),
  P t t_in x.
Proof.
  intros.
  unfold adt_rep in x, P. unfold mk_adts in x, P.
  (*We use [W_ind], the induction principle for
  indexed W types. There is a LOT of work needed to
  use it for this*)
  pose proof (W_ind (finite (length (adts m)))
  (fun n : finite (Datatypes.length (adts m)) =>
    build_base (var_map m srts (dom_aux pd))
    (typesym_map m srts (dom_aux pd)) (adts m)
    (adt_constrs (fin_nth (adts m) n)))
  (fun this i : finite (Datatypes.length (adts m)) =>
    build_rec (var_map m srts (dom_aux pd))
      (typesym_map m srts (dom_aux pd)) (adts m)
      (adt_name (fin_nth (adts m) i))
      (adt_constrs (fin_nth (adts m) this)))
  (*instantiate P*)
  (fun i w => P (fin_nth (adts m) i)
    (In_in_bool adt_dec _ _ (fin_nth_in (adts m) i)) 
    (cast_w (cast_i m m_in i) w))
  ) as wind.
  (*There are two goals: show that W_ind allows us to
    conclude P ..., then prove that the hypotheses
    are satisfied. The first part is much easier, so we
    do it first*)
  match goal with
  | H: ?P -> ?Q |- _ => let Hhyp := fresh "Hindh" in
    assert (Hhyp: P); [clear H|specialize (H Hhyp); clear Hhyp]
  end.
  2: {
    specialize (wind 
      (get_idx _ t (adts m) t_in) x).
      simpl in wind.
    clear -wind.
    revert wind.
    assert (Ht: (fin_nth (adts m) (get_idx adt_dec t (adts m) t_in)) = t). {
      apply get_idx_correct.
    }
    rewrite rewrite_P with(P:=P)(t2:=t)(t_in2:=t_in)(Ht:=Ht).
    assert ((cast_adt_rep Ht
    (cast_w (cast_i m m_in (get_idx adt_dec t (adts m) t_in)) x)) = x). {
      clear. unfold cast_adt_rep.
      apply cast_w_twice.
      apply finite_eq_dec.
    }
  rewrite <- H at 2. auto.
  }
  (*The hard part: prove that the IH's coincide*)
  intros i a f IH.
  rewrite cast_w_mkw. simpl.
  match goal with
  | |- P ?i ?h ?y => set (x':=y) in *
  end.
  (*Idea: x' is some instance of W type (ith in m)
    we can find the constructor c and args such that x' = c(args)
    Then we use (complicated, dependent) inversion to
    connect the components of x' with those of the constructor and args
    *)
  destruct (find_constr_rep gamma_valid m m_in srts Hlen (dom_aux pd)
    (fin_nth (adts m) i) (In_in_bool adt_dec _ _ (fin_nth_in (adts m) i))
    (Semantics.adts pd m srts) (all_unif m m_in) x') as [c [[c_in args] Hx']].
  (*Here, we need info about a*)
  assert (Hnodupb: nodupb funsym_eq_dec
    (ne_list_to_list (adt_constrs (fin_nth (adts m) i)))). {
    eapply constrs_nodups with(m:=m). apply gamma_valid. auto.
    rewrite in_map_iff. exists (fin_nth (adts m) i). split; auto.
    apply fin_nth_in.
  }
  destruct (get_funsym_base (var_map m srts (dom_aux pd))
    (typesym_map m srts (dom_aux pd)) (adts m) 
    (adt_name (fin_nth (adts m) i))
    (adt_constrs (fin_nth (adts m) i)) Hnodupb a
    ) as [c' [Hinc' [b1 Ha]]].
  assert (c = c'). {
    (*Idea: we know from x' + inversion that [get_constr_types]
      agree, use injectivity*)
    unfold constr_rep in Hx'.
    unfold make_constr in Hx'.
    subst x'.
    inversion Hx'. clear Hx'.
    apply inj_pair2_eq_dec in H1. 2: apply finite_eq_dec.
    revert H1.
    unfold cast_a.
    (*want to prove, essentially, that a = get_constr_type c b,
      for appropriate b (from [get_funsym_base])*)
    rewrite Ha.
    rewrite scast_get_constr_type with(Hinc':=
    (constr_in_lemma m (fin_nth (adts m) i)
    (In_in_bool adt_dec (fin_nth (adts m) i) (adts m)
      (fin_nth_in (adts m) i)) c' Hinc')).
    intros Hconstrs.
    apply get_constr_type_inj1 in Hconstrs.
    subst; auto.
  }
  subst c'.
  (*Now we know about a. This is helpful*)
  specialize (H _ _ x' c c_in args Hx').
  apply H.
  (*Now we need to show that the [forall i] condition
    corresponds to that in the IH. This is the hardest part*)
  (*clear -IH Hlen c_in all_unif Ha.*)
  intros j t' t_in' Heq Hj.
  specialize (IH (get_idx adt_dec t' (adts m) t_in')).
  assert (Heq': nth j (s_args c) vty_int =
    vty_cons (adt_name t') (map vty_var (ts_args (adt_name t')))). {
    apply adts_from_constrs with(i:=i)(srts:=srts); auto.
  }
  subst a.
  (*Now we use [finite_to_build_rec] to get our b, which is
    the value [idx_filter] corresponding to j cast to a finite type*)
  assert (Hp: rec_occ_fun (adt_name t') (nth j (s_args c) vty_int)). {
    unfold rec_occ_fun. rewrite Heq'.
    bool_to_prop. split; simpl_sumbool.
  }
  pose proof (idx_filter_length _ _ _ Hj vty_int Hp) as Hn.
  pose proof (idx_filter_correct _ _ _ Hj vty_int Hp) as Hni.
  set (n:= (idx_filter (rec_occ_fun (adt_name t')) (s_args c) j)) in *.
  (*Build finite value*)
  assert ( Hn': n < (count_rec_occ
    (adt_name (fin_nth (adts m) 
      (get_idx adt_dec t' (adts m) t_in'))) c)). {
    rewrite get_idx_correct.
    apply Hn.
  }
  set (fin:=nat_to_finite n Hn').
  set (br:=(@finite_to_build_rec 
  (var_map m srts (dom_aux pd))
  (typesym_map m srts (dom_aux pd))
  (adts m)
  (adt_name (fin_nth (adts m) i))
  (adt_name (fin_nth (adts m) (get_idx adt_dec t' (adts m) t_in')))
  (adt_constrs (fin_nth (adts m) i))
  c Hinc' b1 fin
  )).
  specialize (IH br).
  (*Now, we need to cast*)
  revert IH.
  assert (Ht: fin_nth (adts m) (get_idx adt_dec t' (adts m) t_in') = t'). {
    apply get_idx_correct.
  }
  rewrite rewrite_P with(P:=P)(t2:=t')(t_in2:=t_in')(Ht:=Ht).
  (*The "only" thing that remains is to show that these last
    two casted ADTs are equal. This is not easy*)
  assert ((cast_adt_rep Ht
    (cast_w (cast_i m m_in (get_idx adt_dec t' (adts m) t_in'))
      (f (get_idx adt_dec t' (adts m) t_in')
        br))) =
            (scast (Semantics.adts pd m srts t' t_in')
            (dom_cast (dom_aux pd) Heq (hnth j args s_int (dom_int pd))))). {
    unfold cast_adt_rep. rewrite cast_w_twice. 2: apply finite_eq_dec.
    (*Now we need to know something about f, again by
      inversion on x'*)
    unfold constr_rep in Hx'.
    unfold make_constr in Hx'.
    subst x'.
    inversion Hx'. clear Hx'.
    clear H1.
    apply existT_inj_dec in H2. 2: apply finite_eq_dec.
    destruct H2 as [Heq1 Hexeq].
    assert (Heq1 = Logic.eq_refl). {
      apply UIP_dec. apply finite_eq_dec.
    }
    rewrite H0 in Hexeq. simpl in Hexeq. clear H0.
    (*Here (and in other places), we need UIP*)
    apply existT_inj in Hexeq. destruct Hexeq as [Heq2 Hexeq].
    apply fun_args_eq_dep with(x:=(get_idx adt_dec t' (adts m) t_in')) in Hexeq.
    (*Idea: specialize with correct type, will need to simplify casts,
      get equivalence for f*)
    unfold cast_a in Hexeq.
    (*We use a cast on the [build_rec] to specialize the function*)
    set (br_cast := (cast_build_rec (cast_i m m_in i)
    (var_map m srts (dom_aux pd))
    (typesym_map m srts (dom_aux pd)) 
    (adt_name (fin_nth (adts m) (get_idx adt_dec t' (adts m) t_in')))
    c Hinc' b1 br
    )).
    apply fun_args_eq_dep with (x:=br_cast) in Hexeq.
    (*Now we have an equivalence for f, we need to simplify everything*)
    (*TO deal with implicit args, use tactics*)
    match goal with 
    | H: f ?i ?br' = ?z |- f ?i ?br = ?y => assert (Hbr: br = br');
      [|rewrite <- Hbr in H; rewrite H; clear Hbr]
    end.
    {
      clear. (*Now, just casting*) subst br br_cast.
      generalize dependent (cast_i m m_in i). intros. destruct e. simpl.
      reflexivity.
    }
    (*simplify casts in function*)
    (*this is a bit awful because we need all the function types*)
    rewrite (@cast_fun' _ 
      (finite (Datatypes.length (adts m)))
      (fun j0 a => build_rec (var_map m srts (dom_aux pd))
        (typesym_map m srts (dom_aux pd)) (adts m)
        (adt_name (fin_nth (adts m) j0))
        (adt_constrs
          (fin_nth (adts m)
              (get_idx adt_dec (fin_nth (adts m) i) 
                (adts m)
                (In_in_bool adt_dec (fin_nth (adts m) i) 
                    (adts m) (fin_nth_in (adts m) i))))) a)
      (fun (j0 : finite (Datatypes.length (adts m))) => 
      W (finite (Datatypes.length (adts m)))
        (fun n0 : finite (Datatypes.length (adts m)) =>
        build_base (var_map m srts (dom_aux pd))
          (typesym_map m srts (dom_aux pd)) (adts m)
          (adt_constrs (fin_nth (adts m) n0)))
        (fun this i0 : finite (Datatypes.length (adts m)) =>
        build_rec (var_map m srts (dom_aux pd))
          (typesym_map m srts (dom_aux pd)) (adts m)
          (adt_name (fin_nth (adts m) i0))
          (adt_constrs (fin_nth (adts m) this))) j0)
      _ _ _ Heq2).
    (*Now we have 2 goals: show that the finite types are
      equivalent, then prove that the values are the same.
      Both involve some awful casts, particularly the first one*)
    subst br_cast.
    match goal with
    | |- tnthS ?x ?y = ?z => assert (Hfin: y = fin); [|rewrite Hfin; clear Hfin]
    end.
    { 
      clear. subst fin.
      unfold cast_a in Heq2. unfold scast in Heq2.
      unfold cast_build_rec.
      (*We need to collapse these casts into one. The dependent
        types are awful, we need to be more generic; we do that here.
        This assertion is as general as we can be with a cast and cast_dep'
        in there*)
      assert (forall vars typesyms i1 i2 (Heqi: i1 = i2) ts c Hinc Hinc2 b1 b2
        (br: build_rec vars typesyms (adts m) ts (adt_constrs (fin_nth (adts m) i1))
          (get_constr_type vars typesyms (adts m) 
          (adt_name (fin_nth (adts m) i1)) (adt_constrs (fin_nth (adts m) i1)) c
          Hinc b1))
        (Heqx: get_constr_type vars typesyms (adts m) 
          (adt_name (fin_nth (adts m) i2)) 
          (adt_constrs (fin_nth (adts m) i2))
          c Hinc2 b2 =(cast_dep
          (fun i : finite (Datatypes.length (adts m)) =>
          build_base vars typesyms (adts m) (adt_constrs (fin_nth (adts m) i)))
          Heqi
          (get_constr_type vars typesyms (adts m)
            (adt_name (fin_nth (adts m) i1))
            (adt_constrs (fin_nth (adts m) i1)) c Hinc b1)))
          ,
        cast (@f_equal _ Type (fun (a: build_base vars typesyms (adts m)
          (adt_constrs (fin_nth (adts m) i2))) =>
          (build_rec vars typesyms (adts m) ts
          (adt_constrs (fin_nth (adts m) i2))) a) _ _ (Logic.eq_sym Heqx))
        (cast_dep' (fun i => build_base vars typesyms (adts m)
          (adt_constrs (fin_nth (adts m) i)))
          (fun i t => build_rec vars typesyms (adts m) ts
            (adt_constrs (fin_nth (adts m) i)) t)
          Heqi
          (get_constr_type vars typesyms (adts m) (adt_name (fin_nth (adts m) i1))
            (adt_constrs (fin_nth (adts m) i1)) c Hinc b1) br) =
          (cast_build_rec_gen (f_equal (fun x => adt_constrs (fin_nth (adts m) x)) Heqi)
            vars typesyms ts _ (adt_name (fin_nth (adts m) i1)) c _ Hinc2 _ b2 br)). {
          clear.
          intros. destruct Heqi.
          simpl.
          unfold cast_dep in Heqx. simpl in Heqx.
          assert (Hinc = Hinc2) by apply bool_irrelevance.
          subst.
          assert (b2 = b1) by (apply get_constr_type_inj2 in Heqx; subst; auto).
          subst.
          assert (Heqx = Logic.eq_refl). {
            (*rely on UIP here*)
            apply IndTypes.UIP.
          }
          subst. simpl.
          rewrite build_rec_finite_inv1. reflexivity.
        }
        (*With that lemma, we can rewrite*)
        rewrite (H (var_map m srts (dom_aux pd))
        (typesym_map m srts (dom_aux pd)) _ _ (cast_i m m_in i) ).
        (*Now we have a [build_rec_to_finite] of a single cast*)
        rewrite build_rec_to_finite_cast.
        2: {
          rewrite (cast_i m m_in i) at 1. reflexivity. }
        (*Finally, no more casting! Just need to show that
          finite types equal*)
        subst br.
        rewrite build_rec_finite_inv2.
        reflexivity.
    }
    (*Now, we show that this really is the nth of [args_to_ind_base].
      This will involve pushing the [tnthS] through the layers,
      introducing many, many casts. Then we simplify at the end*)
    clear Hexeq Heq2 Heq1 Ht.
    unfold args_to_ind_base, args_to_ind_base_aux.
    subst fin.
    (*need a default adt*)
    set (d_adt:= scast (Semantics.adts pd m srts t' t_in')
    (dom_cast (dom_aux pd) Heq (hnth j args s_int (dom_int pd)))).
    (*1. Push through [tup_of_list]*)
    rewrite tnthS_tup_of_list with(d:=d_adt).
    (*2. Push through [cast_list]*)
    rewrite cast_list_nth.
    (*3. Push through [hlist_to_list]*)
    assert (Hn2: n <
    Datatypes.length
      (map (IndTypes.sigma m srts)
        (filter
            (rec_occ_fun
              (adt_name (fin_nth (adts m) (get_idx adt_dec t' (adts m) t_in'))))
            (s_args c)))). {
    rewrite map_length. apply Hn'. }
    rewrite hlist_to_list_nth_dec_set' with(Hi:=Hn2)(d1:=s_int)(d2:=dom_int pd).
    2: apply sort_eq_dec.
    (*4. Push through [hlist_map_filter]. Here we need
      the fact that n is [idx_filter j], but annoying the function
      in the [hlist_map_filter] is a bit different (though equal)*)
    subst d_adt.
    assert (Hnalt: n = idx_filter (rec_occ_fun
    (adt_name
      (fin_nth (adts m) (get_idx adt_dec t' (adts m) t_in'))))
      (s_args c) j). {
      subst n. f_equal. rewrite get_idx_correct. reflexivity.
    }
    generalize dependent n; intros. subst n.
    assert (Hnth': nth j (map (IndTypes.sigma m srts) (s_args c)) s_int =
    nth
      (idx_filter
        (rec_occ_fun
            (adt_name (fin_nth (adts m) (get_idx adt_dec t' (adts m) t_in'))))
        (s_args c) j)
      (map (IndTypes.sigma m srts)
        (filter
            (rec_occ_fun
              (adt_name (fin_nth (adts m) (get_idx adt_dec t' (adts m) t_in'))))
            (s_args c))) s_int). {
      rewrite map_nth_inbound with(d2:=vty_int); auto.
      rewrite (map_nth_inbound) with(d2:=vty_int); auto.
      f_equal. rewrite <- Hni. f_equal. f_equal. rewrite get_idx_correct.
      reflexivity.
    }
    rewrite hnth_hlist_map_filter with(d2:=vty_int)(Hij:=Hnth').
    2: apply sort_eq_dec.
    2: {
      rewrite get_idx_correct. auto.
    }
    (*5. Push through [cast_arg_list]*)
    rewrite hnth_cast_arg_list.
    (*Final cast simplification*)
    clear.
    (*Need UIP*)
    assert (forall {A B C D E: Set} x
      (H1: B = A) (H2: C = B) (H3: D = C) (H4: E = D)
      (H5: E = A),
      scast H1 (scast H2 (scast H3 (scast H4 x))) =
      scast H5 x). {
        clear. intros. subst. simpl.
        assert (H5 = eq_refl). apply IndTypes.UIP. subst. reflexivity.
    }
    generalize dependent (hnth j args s_int (dom_int pd)); intros d.
    unfold dom_cast.
    erewrite H.
    rewrite scast_scast. reflexivity.
  }
  (*And we are finally done!*)
  rewrite <- H0. intros X; apply X.
Qed.

(*Print Assumptions adt_rep_ind.*)

End Induction.

(*TODO: don't require [is_sort_adt] and spec, just require hypotheses*)
(*TODO: change to use similar method as induction (and
  pattern amtch)*)
Inductive adt_smaller: {t: {ty: vty | valid_type sigma ty} & 
  domain (val (proj1_sig t))} ->
  {t: {ty: vty | valid_type sigma ty} & domain (val (proj1_sig t))} -> Prop :=
  | ADT_small: forall (x1 x2: {t: {ty: vty | valid_type sigma ty} & domain (val (proj1_sig t))})  
    ty Hval1 Hval2 d1 d2 m a ts srts
    (*NOTE: in general, not all same type, need 2 tys*)
    (Hx1: x1 = existT _ (exist (valid_type sigma) ty Hval2) d1)
    (Hx2: x2 = existT _ (exist _ ty Hval1) d2)
    (Hisadt: is_sort_adt (val ty) = 
      Some (m, a, ts, srts)),
    let adt_spec := (is_sort_adt_spec gamma_valid _ _ _ _ _ Hisadt) in
    let Hseq := proj1 adt_spec in
    let a_in := proj1 (proj2 adt_spec) in
    let m_in :=  proj1 (proj2 (proj2 adt_spec)) in
    (*cast to adt type*)
    let adt : adt_rep m srts (dom_aux pd) a a_in :=
      scast (Semantics.adts pd m srts a a_in) (dom_cast _ Hseq d2) in 
    (*need lengths lemma*)
    let lengths_eq : length srts = length (m_params m) :=
      adt_srts_length_eq gamma_valid Hisadt Hval2 in 
    (*Now we get the constructor c and arg_list a such
      that d2 = [[c(a)]]*)
    let Hrep := find_constr_rep gamma_valid m m_in srts lengths_eq
      (dom_aux pd) a a_in (Semantics.adts pd m srts) 
        (all_unif m m_in) adt in
    let c : funsym := projT1 Hrep in
    let c_in : constr_in_adt c a :=
      fst (proj1_sig (projT2 Hrep)) in
    let args : arg_list domain (funsym_sigma_args c srts) := 
      snd (proj1_sig (projT2 Hrep)) in
    let args' := cast_arg_list 
      (f_equal (funsym_sigma_args c) (eq_sym (val_sorts_eq srts))) args in
    (*Then it must be the case that d1 equals
      one of the arguments in args*)
      (*TODO: need lengths of (s_params c)*)
    let lens : length (s_params c) = length (m_params m) :=
      f_equal (@length _) (adt_constr_params gamma_valid m_in a_in c_in) in
    let lens': length (s_params c) = length srts :=
      eq_trans lens (eq_sym lengths_eq) in
    let lens'' : length (s_params c) = length (map sort_to_ty srts) :=
      eq_trans lens' (eq_sym (map_length sort_to_ty srts)) in
    let val_args := funargs_to_vals pd vt c (map sort_to_ty srts) lens''
      (*lens'*) args' in
    (exists i
    (*TODO: remove this, just use scast with equality on
    [funsym_sigma_args]*)
    (Heq: (nth i
    (map (v_subst (v_typevar vt))
       (map (ty_subst (s_params c) (map sort_to_ty srts)) (s_args c)))
    s_int) = val ty), i < hlength val_args /\
    (*TODO: need some type equality*)
    d2 = dom_cast _ Heq (hnth i val_args s_int (dom_int pd))) ->
    adt_smaller x1 x2.

(*Let's see how awful this is - I know I will need induction*)
(*
Lemma adt_smaller_wf: well_founded adt_smaller.
Proof.
  unfold well_founded.
  intros a. destruct a as [[ty Hval] d].
  simpl in *.
  destruct (@is_sort_adt gamma (val ty)) eqn : Hisadt.
  (*Can't be None, contradiction*)
  2: {
    constructor. intros.
    inversion H; subst.
    apply EqdepFacts.eq_sigT_fst in Hx2.
    apply EqdepFacts.eq_sig_fst in Hx2. subst.
    clear -Hisadt Hisadt0. exfalso.
    rewrite Hisadt in Hisadt0. inversion Hisadt0.
  }
  destruct p as [[[m a] ts] srts].
  (*Need to do induction on w-type, so we get that*)
  remember (
    let adt_spec := (is_sort_adt_spec gamma_valid _ _ _ _ _ Hisadt) in
    let Hseq := proj1 adt_spec in
    let a_in := proj1 (proj2 adt_spec) in
    let m_in :=  proj1 (proj2 (proj2 adt_spec)) in
    (*cast to adt type*)
      scast (Semantics.adts pd m srts a a_in) (dom_cast _ Hseq d)
  ) as adt.*)

End FunDef.


  (*



(*Assume we have some relation (TODO: need to find out which)*)
(*TODO: on domains, will have precondition that they are adt*)
Axiom adt_smaller:
  (*We hide the type because they may not be the same,
    for instance with a mutually recursive type*)
  {t: vty & domain (val t)} ->
  {t: vty & domain (val t)} -> Prop.
Axiom adt_smaller_wf: well_founded adt_smaller.
Require Import Denotational.
Check funsym_subst_eq.
Check v_subst.

(*TODO: think we will need something better than
  [get_arg_list] - we will want direct, invertible
  conversion functions*)

(*Because input to this will be with funsym_sigma_args
  but our inductive relation should really use
  an arg_list of (domain (val x))*)
(*Want generic way to convert between them*)

(*Next, we lift this to (nat, [arg_list]) pairs,
  where the nat represents the index of the smaller
  argument*)
(*TODO: do we need proof nat is in bounds?*)
Definition arg_list_smaller:
  {x: { t: nat * list sort | fst t < length (snd t) } & 
    arg_list domain (snd (proj1_sig x))} ->
  {x: { t: nat * list sort | fst t < length (snd t) } & 
  arg_list domain (snd (proj1_sig x))} -> 
  Prop.
Proof.
  intros x1 x2.
  destruct x1 as [[[n1 s1] Hn1] al1].
  destruct x2 as [[[n2 s2] Hn2] al2].
  Check hnth.
  remember (hnth n1 al1 s_int (dom_int pd)) as y.
  simpl in y.
  remember (hnth n2 al2 s_int (dom_int pd)) as z.
  simpl in z.
  Print existT.
  (*Ah, we need a list we are using val for*)
  (*See how Denotational does it*)
  apply (adt_smaller (existT _ (nth n1 s1 s_int)  y) (existT _ z)).
  Print domain.
  Print dom_aux.
  Search dom_aux s_int.
  simpl in y.
  (nat * {s: list sort & arg_list domain s}) ->
  (nat * {s: list sort & arg_list domain s}) ->
  Prop.
intros x1 x2.


(*Need to lift this to arg list*)
(*TODO: relate to above, need def*)
(*TODO: do we need index here? Or can we use exists?*)
Axiom arg_list_smaller: forall (srts: list sort),
  arg_list domain srts ->
  arg_list domain srts -> Prop.
Axiom arg_list_smaller_wf : forall (srts: list sort),
  well_founded (arg_list_smaller srts).

  (*Hmm, think about this*)
  (*What I think: we need an index, we need to say
    that the specific type argument is smaller
    (arg lists may not be same type)
    But even these may not be same type
    so our relation might need to be on 2 things of different
    types or like {x : ty & domain (val ty)}
    i think (bc of non-uniformity) tihs is caused by
    mutually-recursive types
    *)

  (*try to do on paper, let's see*)
Definition input_smaller: forall i1 i2 srts1 srts2,
  {b : bool &
         {t
         : {i : nat | i < (if b then i1 else i2)} &
         arg_list domain
           (if b then srts1 else srts2)}} ->
  {b : bool &
         {t
         : {i : nat | i < (if b then i1 else i2)} &
         arg_list domain
           (if b then srts1 else srts2)}} ->
  Prop := fun i1 i2 srts1 srts2 x1 x2 =>
  arg_list_smaller _ (projT2 (projT2 x1)) (projT2 (projT2 x2)). 
Proof.


(*TODO: need to prove our relation on pairs is well-founded*)

(*Should do the well-founded proofs I think, at least
  seeing how they fit together*)
(*OR: assume well-founded and then see what we need/have
  in the recursive cases*)
(*TODO: is there a better way to handle this return type?*)
(*We could say that i is between 0 and length fs + length ps
  and then produce a list of all the return types (with map)
  and just take nth i from there - could be weird with Type though
  will have to construct bool and correct index in function*)


(*Really, we need the relation on pairs: our input should*)

(*OK: here's what I think:
  We have the lists fs and ps
  So the recursive input is: bool * nat * arg_list
  arg_list also depends on the input type
  because we need to know if funsym_sigma_args or predsym_sigma_args
  or maybe {b: bool & {i: nat | if b then i < length fs else i < length ps}} * arg_list
  then the return type is:
  (if b then domain (funsym_sigma_ret (nth i fs) srts) else bool)

  *)

Print pi_funpred.
(*TODO: move*)
Definition ps_d : predsym := 
    Build_predsym EmptyString nil nil eq_refl eq_refl.
Definition fs_d : funsym :=
    Build_funsym EmptyString nil nil vty_int eq_refl eq_refl eq_refl.

(*This is the version for the function body*)
Definition build_indfun (small: list vsymbol) 
(hd: string) (hd_ty: vty)
(hd_idx: nat) (vv: val_vars pd vt) (body: term) (ty: vty) 
(*(arg: domain (dom_aux pd) (v_subst (v_typevar vt)) ty)*)
(Hty: term_has_type sigma body ty)
(Hdec: decrease_fun fs ps small (hd, hd_ty) body)
(Hinvar: forall x, In x (map fst small) ->
  adt_smaller _ (vv (x, hd_ty)) (vv (hd, hd_ty)))
(*Then, the actual inputs to the function*)
(srts: list sort)
(args: {b: bool & {t: {i : nat | i < if b then length fs else length ps} &
  arg_list domain (if b then (funsym_sigma_args (nth (proj1_sig t) (map fn_name fs) fs_d) srts) 
    else (predsym_sigma_args (nth (proj1_sig t) (map pn_name ps) ps_d) srts))}}) :
(if (projT1 args) then domain (val ty)
  else bool).
Proof.
  revert args.
  apply (@Fix _ _ 
    (arg_list_smaller_wf hd_idx (funsym_sigma_args f srts))
    (fun _ => domain (funsym_sigma_ret f srts))).
  (*So this is the function body that we need*)
  intros.

  (*Let's try this manually*)

(*First, we give the inner function that we will give to Fix*)
(*This is a Fixpoint for the term/formula rep recursion*)
Fixpoint indfun_term_rep (i: nat) (small: list vsymbol) 
(hd: string) (hd_ty: vty) (f: funsym)
(hd_idx: nat) (vv: val_vars pd vt) (body: term) (ty: vty) 
(*(arg: domain (dom_aux pd) (v_subst (v_typevar vt)) ty)*)
(Hty: term_has_type sigma body ty)
(Hdec: decrease_fun fs ps small (hd, hd_ty) body)
(Hinvar: forall x, In x (map fst small) ->
  adt_smaller _ (vv (x, hd_ty)) (vv (hd, hd_ty)))
(*Then, the actual inputs to the function*)
(srts: list sort)
(args: arg_list domain (funsym_sigma_args f srts))
(rec: forall y: arg_list domain (funsym_sigma_args f srts),
  arg_list_smaller hd_idx (funsym_sigma_args f srts) y args ->
  domain (funsym_sigma_ret f srts)) {struct body} :
domain (funsym_sigma_ret f srts) :=
match body with
|
(*TODO: need to have formulas too, and not using mutual recursion at all*)




(*Most generic: assume we have the vsymbol and SOME 
  list such that [decrease_fun] holds; we will instatiate them
  later. We will need another hypothesis about the invariant
  of the list (relating to valuation most likely)*)
Program Fixpoint build_indfun (i: nat) (small: list vsymbol) 
  (hd: string) (hd_ty: vty) (f: funsym)
  (hd_idx: nat) (vv: val_vars pd vt) (body: term) (ty: vty) 
  (*(arg: domain (dom_aux pd) (v_subst (v_typevar vt)) ty)*)
  (Hty: term_has_type sigma body ty)
  (Hdec: decrease_fun fs ps small (hd, hd_ty) body)
  (Hinvar: forall x, In x (map fst small) ->
    adt_smaller _ (vv (x, hd_ty)) (vv (hd, hd_ty)))
  (*Then, the actual inputs to the function*)
  (srts: list sort)
  (args: arg_list domain (funsym_sigma_args f srts))
  (H: well_founded (arg_list_smaller hd_idx (funsym_sigma_args f srts)))
  {wf  args}  :
  domain (funsym_sigma_ret f srts)
  :=
  match (domain_ne pd (val vt ty)) with
      | DE x => x 
      end. 
  
  .
  by wf args (arg_list_smaller_wf hd_idx (funsym_sigma_args f srts)) := .
  domain (dom_aux pd (funsym_sigma_ret f srts))
  (args: )


Definition build_functions (fs: list (fn * term)) (ps: list (pn * formula)) :
  forall (i: nat) (Hi: i < length fs + length ps)




(*Now we will (try to) write an inductive relation on [adt_rep]s
  (or maybe domains) that is well-founded, expressing the "structurally
  smaller" relation*)
(*Typecasting will be annoying*)
Inductive adt_smaller (m: mut_adt) (a: alg_datatype):  



  that is 
  of ADTS
  that is 

Print pi_dom.
Search adt_rep.
Check find_constr_rep.
Search mk_adts.
Print adt_rep.


find_constr_rep:
  forall {s : sig} {gamma : context} (gamma_valid : valid_context s gamma)
	(m : mut_adt) (m_in : mut_in_ctx m gamma) (srts : list sort)
    (srts_len : Datatypes.length srts = Datatypes.length (m_params m))
    (domain_aux : sort -> Set) (t : alg_datatype) 
    (t_in : adt_in_mut t m)
    (dom_adts : forall (a : alg_datatype) (Hin : adt_in_mut a m),
                domain domain_aux (typesym_to_sort (adt_name a) srts) =
                adt_rep m srts domain_aux a Hin),
  uniform m ->
  forall x : adt_rep m srts domain_aux t t_in,
  {f : funsym &
  {Hf
  : constr_in_adt f t *
    arg_list (domain domain_aux) (funsym_sigma_args f srts)
  | x =
    constr_rep gamma_valid m m_in srts srts_len domain_aux t t_in f 
      (fst Hf) dom_adts (snd Hf)}}



      Notation term_rep := (term_rep gamma_valid pd all_unif vt pf).
      Notation formula_rep := (formula_rep gamma_valid pd all_unif vt pf).


      *)