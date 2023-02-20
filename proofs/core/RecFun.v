(*Recursive Functions*)
Require Import Syntax.
Require Import Types.
Require Import Typing.
Require Import Semantics.

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

Require Import IndTypes.
From Equations Require Import Equations.
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
Require Import Hlist.

(*TODO: where do we need the bodies?*)
Variable (fs: list fn) (ps: list pn).
Print well_founded.

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
Search mk_adts.
Print pi_dom.
Require Import Denotational.
Check is_sort_adt_spec.
Print match_val_single.
Check funargs_to_vals.
Check is_sort_adt_spec.
Print typesym_to_sort.
Check typesym_to_sort_proof.
Search m_params s_params.
Print val.
Locate adts.
Print Semantics.adts.


Lemma val_sorts_eq (srts: list sort):
  map (v_subst (v_typevar vt)) (map sort_to_ty srts) = srts.
Proof.
  apply list_eq_ext'; rewrite !map_length; auto.
  intros.
  rewrite map_nth_inbound with(d2:=vty_int). 2: rewrite map_length; lia.
  rewrite map_nth_inbound with(d2:=d); auto.
  symmetry. apply subst_sort_eq.
Qed.

(*
domain
    (nth i
       (map (v_subst (v_typevar vt))
          (map (ty_subst (s_params c) (map sort_to_ty srts)) (s_args c)))
       s_int)" while it is expected to have type"
 domain
    (val (proj1_sig (exist (fun ty : vty => valid_type sigma ty) ty Hval1)))

*)

Definition cast_w {I: Set} {A: I -> Set} {B: forall i: I, I -> A i -> Set}
  {i1 i2: I} (Heq: i1 = i2) (w: W I A B i1) : W I A B i2 :=
  match Heq with
  | eq_refl => w
  end.
Print W.

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

Require Import Coq.Logic.Eqdep_dec.

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

(*
Lemma cast_adt_rep_w {srts t1 t2 tin1 tin2}
  (H: t1 = t2) H1
  x:
  cast_adt_rep H (cast_w H1 x) = x.

  W (finite (Datatypes.length (adts m)))
      (fun n : finite (Datatypes.length (adts m)) =>
       build_base (var_map m srts (dom_aux pd))
         (typesym_map m srts (dom_aux pd)) (adts m)
         (adt_constrs (fin_nth (adts m) n)))
      (fun this i : finite (Datatypes.length (adts m)) =>
       build_rec (var_map m srts (dom_aux pd))
         (typesym_map m srts (dom_aux pd)) (adts m)
         (adt_name (fin_nth (adts m) i))
         (adt_constrs (fin_nth (adts m) this)))
      (get_idx adt_dec t (adts m) t_in)
Ht: fin_nth (adts m) (get_idx adt_dec t (adts m) t_in) = t
1/1
P t t_in
  (cast_adt_rep Ht
     (cast_w (cast_i m m_in (get_idx adt_dec t (adts m) t_in)) x)) ->
P t t_in x

*)

(*
Definition cast_adt_rep {m srts t t_in1 t_in2}
  (Heq: t_in1 = t_in2)
  (x: adt_rep m srts (dom_aux pd) t t_in1):
  adt_rep m srts (dom_aux pd) t t_in2 :=
  match Heq with
  | eq_refl => x
  end.*)
  
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

(*TODO: move*)
(*
Lemma v_subst_aux_inv f ty name args:
  v_subst_aux f ty = vty_cons name args ->
  ty = vty_cons name args.
Proof.
  intros. destruct ty; simpl in H; try solve[inversion H].

  2: {}



v_subst_aux
       (fun x : typevar =>
        ty_subst_fun (s_params c) (sorts_to_tys srts) vty_int x)
       (nth j (s_args c) vty_int) =
     vty_cons (adt_name t') (seq.map sort_to_ty srts)

*)
  (*i =
 get_idx adt_dec (fin_nth (adts m) i) (adts m)
   *)
(*Yes, change to boolean*)
(*We should be able to do better - we know the recursive instances*)
Lemma adt_rep_ind m m_in srts
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
  (*
  (*Make generic in choice of t, t_in*)
  assert (fin_nth (adts m) (get_idx adt_dec t (adts m) (In_in_bool adt_dec t (typs m) t_in)) = t). {
    apply get_idx_correct.
  }

  generalize dependent H. revert P.
  generalize dependent ((get_idx adt_dec t (adts m) (In_in_bool adt_dec t (typs m) t_in))).
  Search get_idx.
*)
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
  (fun i w => P (fin_nth (adts m) i) (*TODO*) 
    (In_in_bool adt_dec _ _ (fin_nth_in (adts m) i)) 
    (cast_w (cast_i m m_in i) w))
  ) as wind.
  (*TODO: fix*)
  match goal with
  | H: ?P -> ?Q |- _ => let Hhyp := fresh "Hindh" in
    assert (Hhyp: P); [clear H|specialize (H Hhyp); clear Hhyp]
  end.
  2: {
    specialize (wind 
      (get_idx _ t (adts m) t_in) x).
      simpl in wind.
    clear -wind.
    (*TODO: might need to make adt_in_mut a bool*)
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
  (*OK, now we need to prove IH equivalence*)
  intros i a f IH.
  (*Now we need to use our inductive assumption*)
  rewrite cast_w_mkw. simpl.
  match goal with
  | |- P ?i ?h ?y => set (x':=y) in *
  end.
  destruct (find_constr_rep gamma_valid m m_in srts Hlen (dom_aux pd)
    (fin_nth (adts m) i) (In_in_bool adt_dec _ _ (fin_nth_in (adts m) i))
    (Semantics.adts pd m srts) (all_unif m m_in) x') as [c [[c_in args] Hx']].
  specialize (H _ _ x' c c_in args Hx').
  apply H.
  (*Now we need to show that the [forall i] condition
    corresponds to that in the IH*)
  clear -IH.
  intros j t' t_in' Heq Hj.
  specialize (IH (get_idx adt_dec t' (adts m) t_in')).
  Print rec_occ_fun.
  (*Which [build_rec] do we need?*)
  (*Ah, we need to know which occurrence this i is
    so we should specialize with (j: finite (count_rec_occ ts c)
    where ts is the typesym we are looking at (ts' name)
    and j is the number ocurring before i*)
  assert (Hnth: exists l, nth j (s_args c) vty_int = vty_cons (adt_name t') l). {
    revert Heq. unfold funsym_sigma_args. 
    unfold ty_subst_list_s.
    rewrite (map_nth_inbound) with(d2:= vty_int); auto.
    (*Problem: what if one of our srts includes an inductive
      type? Feel like we dealt with this before*)
    (*Need to think about this*)
    (*TODO: I think I should modify the IH, only require
      this holds of all cases when nth (s_args i ...) has the
      correct type (and then cast from there) - also modify relation
      
      Complicated case: say we have wlist a and we interpret a
      in our valuation as (list int) (coq type)
      then arguments to cons are (list int) and (list (list int)) in coq
      i believe this is valid - uniformity is syntactic, not semantic
      but we don't want to allow recursion on the 1st argument
      (or rather, we can't say that this prop holds on the first argument)
      ok in pattern matching because there we work on the reps directly
      so if we interpret A as list, it is OK - any property we want to
      prove had better not depend on that because we require it to be
      true for all possible valuations
      think about if pattern matching is OK or if this ruins stuff
      so we should change this
      
      **)
    Search ty_subst_s typesym_to_sort.
    unfold typesym_to_sort, ty_subst_s, v_subst. intros.
    inversion Heq.
    Search v_subst_aux.
    unfold v_subst_aux in H0.
    intros [Hnth].
    rewrite <- ty_subst_s_cons.
    Search typesym_to_sort.
    
    unfold seq.map. rewrite map_map. rewrite map_nth.
  }
  assert ()

  assert ()

  Print build_constr_rec.



  unfold scast. 
  apply IH.

  unfold build_rec.
  Search constr_rep.

  find_constr_rep:
  forall {s : sig} {gamma : context} (gamma_valid : valid_context s gamma)
	(m : mut_adt) (m_in : mut_in_ctx m gamma) (srts : list sort)
    (srts_len : Datatypes.length srts = Datatypes.length (m_params m))
    (domain_aux : sort -> Set) (t : alg_datatype) 
    (t_in : adt_in_mut t m)
    (dom_adts : forall (a : alg_datatype) (Hin : adt_in_mut a m),
                IndTypes.domain domain_aux
                  (typesym_to_sort (adt_name a) srts) =
                adt_rep m srts domain_aux a Hin),
  uniform m ->
  forall x : adt_rep m srts domain_aux t t_in,
  {f : funsym &
  {Hf
  : constr_in_adt f t *
    arg_list (IndTypes.domain domain_aux) (funsym_sigma_args f srts)
  | x =
    constr_rep gamma_valid m m_in srts srts_len domain_aux t t_in f 
      (fst Hf) dom_adts (snd Hf)}}



  unfold constr_rep, make_constr in H.
    eapply H.
    + unfold constr_rep. unfold make_constr. simpl.
      (*yikes, this is awful - todo: plan this out on paper, might
        be easier*)
      reflexivity.
    f_equal.
  

  match 
  Print Ltac prove_hyp.
  assert ()


  eapply W_ind with(I:=(finite (length (adts m))))
  (A:=)
  (B:=)
  (P:= fun i w => P (fin_nth (adts m) i)  _).
  (i:=(get_idx adt_dec t (adts m) (In_in_bool adt_dec t (typs m) t_in))) (w:=x).
2: apply x.
(*Need to prove that IH coincides*)
intros i a f Hindf.
(*Now we need to know that x is the application of a constructor*)
destruct (find_constr_rep gamma_valid m m_in srts Hlen (dom_aux pd) 
  t t_in (Semantics.adts pd m srts) (all_unif _ m_in) x) as [c [[c_in args] Hx]].
simpl in Hx.
Check W_ind.

eapply Hindf.
Print build_rec.


rewrite Hx.
Search mkW.
intros.


revert x.
  
  Check W_ind. apply W_ind with(P:=P).


(*TODO: don't require spec, just require hypotheses*)
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
(*
Section WAlt.

Variable A: Set.
Variable B : A -> Set.

Inductive W : Set :=
  | mkW : forall (a: A) (f: B a -> W), W.

Check W_ind.

Check mk_adts.
Check find_constr_rep.
*)
(*
Definition fin_nth_in_mut (m: mut_adt) (i: finite (length (adts m))):
  adt_in_mut (fin_nth (adts m) i) m :=
  fin_nth_in (adts m) i.
Proof.
  apply fin_nth_in.
  unfold adt_in_mut. apply fin_nth_in. Search In fin_nth.
*)


adt_rep m srts (dom_aux pd) a a_in :=
      scast (Semantics.adts pd m srts a a_in) (dom_cast _ Hseq d2) in 
    (*need lengths lemma*)
    let lengths_eq : length srts = length (m_params m) :=
      adt_srts_length_eq gamma_valid Hisadt Hval2 in 
    (*Now we get the constructor c and arg_list a such
      that d2 = [[c(a)]]*)
    let Hrep := find_constr_rep gamma_valid m m_in srts lengths_eq
      (dom_aux pd) a a_in (Semantics.adts pd m srts) 
        (all_unif m m_in) adt in

(*Let's see*)
(*So what is the lemma that we want to prove?*)
(*we have a prop (P: adt_rep m srts dom_aux a a_in -> Prop)

  suppose that for any a in [adt_rep...], if P holds
  of all recursive instances (given by get_constrs),
  then P holds of a

  then P holds of any a

  and we want: suppose that P is true 
*)

Lemma mk_adts_ind (vars: typevar -> Set) (abstract : typesym -> list vty -> Set)
  (m: list alg_datatype) (P: forall (i: finite (length m)), 
    mk_adts vars abstract m i -> Prop),
  (forall (i: finite (length m)), (a: build_base vars abstract m (adt_constrs (fin_nth m i))),
    )


W_ind
	 : forall (I : Set) (A : I -> Set) (B : forall i : I, I -> A i -> Set)
         (P : forall i : I, W I A B i -> Prop),
       (forall (i : I) (a : A i) (f : forall j : I, B i j a -> W I A B j),
        (forall (j : I) (b : B i j a), P j (f j b)) -> P i (mkW I A B i a f)) ->
       forall (i : I) (w : W I A B i), P i w

     mk_adts = 
fun (vars : typevar -> Set) (abstract : typesym -> list vty -> Set)
  (m : list alg_datatype) =>
W (finite (Datatypes.length m))
  (fun n : finite (Datatypes.length m) =>
   build_base vars abstract m (adt_constrs (fin_nth m n)))
  (fun this i : finite (Datatypes.length m) =>
   build_rec vars abstract m (adt_name (fin_nth m i))
	 (adt_constrs (fin_nth m this)))


   adt_rep = 
fun (m : mut_adt) (srts : list sort) (domain_aux : sort -> Set)
  (a : alg_datatype) (a_in : adt_in_mut a m) =>
mk_adts (var_map m srts domain_aux) (typesym_map m srts domain_aux) 
  (adts m) (get_idx adt_dec a (adts m) (In_in_bool adt_dec a (typs m) a_in))



(*Let's see how awful this is - I know I will need induction*)
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
  ) as adt.
  Print adt_rep.
  Print mk_adts.
  Print W_ind.




  induction adt.



    Search (exist ?x ?y ?z = exist ?x ?a ?b).
    Print Assumptions EqdepFacts.eq_sigT_fst.
    Search (existT ?x ?b ?y = existT ?x ?a ?z).
    clear -ty0 ty
    simpl in *.
    dependent destruction H.
    inversion H; subst.

    unfold adt_smaller in H.
    unfold Acc.

  } 
  Some (m, a, ts, srts)))

  
  destruct a. simpl.



    (*TODO: make more generic function to convert between
    funsym_sigma_args and val list*)
    



      match (is_sort_adt_spec _ _ _ _ _ Hisadt) with
      | conj Hseq (conj a_in (conj m_in Htseq)) =>
        (*We cast to get an ADT, now that we know that this actually is
          an ADT*)
        let adt : adt_rep m srts (dom_aux pd) a a_in :=
          scast (adts pd m srts a a_in) (dom_cast _ Hseq d) in
       
        (*Need a lemma about lengths for [find_constr_rep]*)
        let lengths_eq : length srts = length (m_params m) := 
          adt_srts_length_eq Hisadt Hval in

        (*The key part: get the constructor c and arg_list a
          such that d = [[c(a)]]*)
        let Hrep := find_constr_rep gamma_valid m m_in srts lengths_eq 
          (dom_aux pd) a a_in (adts pd m srts) 
          (all_unif m m_in) adt in


    () 



adts : forall (m : mut_adt) (srts : list sort) 
             (a : alg_datatype) (Hin : adt_in_mut a m),
           IndTypes.domain dom_aux (typesym_to_sort (adt_name a) srts) =
           adt_rep m srts dom_aux a Hin

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
  that is *)

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