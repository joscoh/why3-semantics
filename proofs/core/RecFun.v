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
Search s_int.
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
    (Heq: (nth i
    (map (v_subst (v_typevar vt))
       (map (ty_subst (s_params c) (map sort_to_ty srts)) (s_args c)))
    s_int) = val ty), i < hlength val_args /\
    (*TODO: need some type equality*)
    d2 = dom_cast _ Heq (hnth i val_args s_int (dom_int pd))) ->
    adt_smaller x1 x2.


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