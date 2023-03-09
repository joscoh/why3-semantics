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

Set Bullet Behavior "Strict Subproofs".

(*First, define syntactic restriction on functions*)

(*For our purposes here, a function declaration is a tuple
  consisting of the name, arguments, index of the argument that
  is decreasing, and body*)
Record fn := mk_fn {fn_name: funsym; fn_args: list vsymbol;
  fn_idx : nat; fn_body: term; fn_idx_in: fn_idx <? length fn_args;
  fn_args_len: length fn_args =? length (s_args fn_name)}.
Record pn := mk_pn {pn_name: predsym; pn_args: list vsymbol;
  pn_idx: nat; pn_body: formula; pn_idx_in: pn_idx <? length pn_args;
  pn_args_len: length pn_args =? length (p_args pn_name)}.

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

(*TODO: move maybe*)
(*All variables from a pattern that are strictly "smaller" than
  the matched value*)
Fixpoint pat_constr_vars (p: pattern) : list vsymbol :=
  match p with
  | Pconstr c tys ps =>
    (*Once we bind in a constructor, all vars are smaller*) 
    big_union vsymbol_eq_dec pat_fv ps
  | Por p1 p2 => 
    (*Those smaller in both patterns are smaller*)
    intersect vsymbol_eq_dec (pat_constr_vars p1) (pat_constr_vars p2)
  | Pbind p _ => pat_constr_vars p
  (*Vars are not smaller unless we are already in a constructor*)
  | _ => nil
  end.

(*PROBLEM! My syntax is not correct - functions and predicates
  can be recursive together - so we need something like:
  list (Either fn pn)
  or maybe nicer - list of fs followed by list of ps
  (we can always reorder)*)

(*The list of vsymbols denotes all variables we "know" to be
  smaller than the argument, which is the second argument to the
  relation*)
(*TODO: add mut and vs - require that type is correct*)
(*We have the relation : dec fs ps small hd m vs t ->
  means that 
  1. all ocurrences of functions/pred syms in fs and ps 
    occur where the decreasing argument comes from small,
    which is a list of elements that are smaller than hd
    and which come from the same mut adt as hd
  
  Hmm, how do we want to do this?
  Would like to avoid dependent types if possible
  but don't want invariant across whole thing
  maybe do invariants separately

  *)

(*From a list of vsymbols, keep those which have type vty_cons a ts
  for some a in mut_adt m*)
Definition vsyms_in_m (m: mut_adt) (vs: list vty) (l: list vsymbol) :
  list vsymbol :=
  filter (fun v => 
    match (snd v) with
    | vty_cons ts vs' => 
      ssrbool.isSome (find_ts_in_mut ts m) &&
      list_eq_dec vty_eq_dec vs' vs
    | _ => false
    end) l.

(*A more useful formulation*)
Lemma vsyms_in_m_in (m: mut_adt) (vs: list vty) (l: list vsymbol):
  forall x, In x (vsyms_in_m m vs l) <-> In x l /\ exists a,
    adt_in_mut a m /\ snd x = vty_cons (adt_name a) vs.
Proof.
  intros. unfold vsyms_in_m.
  rewrite in_filter. rewrite and_comm. bool_to_prop.
  destruct x; simpl in *. destruct v; try (solve[split; [intro C; inversion C | 
    intros [a [a_in Hty]]; inversion Hty]]).
  unfold ssrbool.isSome.
  destruct (find_ts_in_mut t m) eqn : Hts; simpl.
  - destruct (list_eq_dec vty_eq_dec l0 vs); subst; simpl; split;
    intros; auto; try tf.
    + exists a. apply find_ts_in_mut_some in Hts. destruct Hts.
      subst. split; auto.
    + destruct H as [a' [Ha' Hty]]. inversion Hty; subst; auto.
  - split; [intro C; inversion C | intros [a [Ha Hty]]].
    rewrite find_ts_in_mut_none in Hts.
    inversion Hty; subst.
    apply Hts in Ha. contradiction.
Qed.

(*TODO: do we need m and vs in here? Or should it be separate?*)
Inductive decrease_fun (fs: list fn) (ps: list pn) : 
  list vsymbol -> vsymbol -> mut_adt -> list vty -> term -> Prop :=
  (*Before any of the constructor cases, if none of fs or ps appear
    in t, then t is trivially a decreasing function*)
  | Dec_notin_t: forall (small: list vsymbol) (hd: vsymbol) (m: mut_adt)
    (vs: list vty) (t: term),
    (forall f, In f fs -> negb (funsym_in_tm (fn_name f) t)) ->
    (forall p, In p ps -> negb (predsym_in_term (pn_name p) t)) ->
    decrease_fun fs ps small hd m vs t
  (*First, the recursive function call case*)
  | Dec_fun_in: forall (small: list vsymbol) (hd: vsymbol) (m: mut_adt)
    (vs: list vty) 
    (f: funsym) (f_decl: fn) (l: list vty) (ts: list term) (x: vsymbol),
    In f_decl fs ->
    f = fn_name f_decl ->
    (*The decreasing argument is a variable in our list of decreasing terms*)
    In x small ->
    nth (fn_idx f_decl) ts tm_d = Tvar x ->
    (*Uniformity: we must be applying the function uniformly
      (TODO: make this separate?)*)
    l = map vty_var (s_params f) ->
    (*None of [fs] of [ps] appear in the terms*) 
    (*TODO: will likely need this to show we can ignore function binding in interp for recursive cases*)
    Forall (fun t => forall f,  In f fs -> negb (funsym_in_tm (fn_name f) t)) ts ->
    Forall (fun t => forall p, In p ps -> negb (predsym_in_term (pn_name p) t)) ts ->
    (*Then this recursive call is valid*)
    decrease_fun fs ps small hd m vs (Tfun f l ts)
  (*Other function call*)
  | Dec_fun_notin: forall (small: list vsymbol) (hd: vsymbol)
    (m: mut_adt) (vs: list vty) 
    (f: funsym) (l: list vty) (ts: list term),
    ~ In f (map fn_name fs) ->
    (*In this case, just recursive*)
    Forall (decrease_fun fs ps small hd m vs) ts ->
    decrease_fun fs ps small hd m vs (Tfun f l ts)
  (*Pattern match on var - this is how we add new, smaller variables*)
  | Dec_tmatch: forall (small: list vsymbol) (hd: vsymbol) (m: mut_adt)
    (vs: list vty)
    (mvar: vsymbol) (v: vty) (pats: list (pattern * term)),
    (*TODO: can we only match on a variable?*)
    mvar = hd \/ In mvar small ->
    (*TODO: don't allow repeated matches on same variable*)
    Forall (fun x => decrease_fun fs ps 
      (*remove pat_fv's (bound), add back constr vars (smaller)*)
      (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars (fst x))) 
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
        small)) mvar m vs (snd x)) pats ->
    decrease_fun fs ps small hd m vs (Tmatch (Tvar mvar) v pats) 
  (*Other pattern match is recursive case*)
  | Dec_tmatch_rec: forall (small: list vsymbol) (hd: vsymbol)
    m vs
    (tm: term) (v: vty) (pats: list (pattern * term)),
    ~(exists var, tm = Tvar var /\ (var = hd \/ In var small)) ->
    decrease_fun fs ps small hd m vs tm ->
    Forall (fun x => decrease_fun fs ps 
      (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
      hd m vs (snd x)) pats ->
    decrease_fun fs ps small hd m vs (Tmatch tm v pats)
  (*Now the easy cases: Constants, Variables always decreasing*)
  | Dec_var: forall (small : list vsymbol) (hd: vsymbol) m vs (v: vsymbol),
    decrease_fun fs ps small hd m vs (Tvar v)
  | Dec_const: forall (small : list vsymbol) (hd: vsymbol) m vs (c: constant),
    decrease_fun fs ps small hd m vs (Tconst c)
  (*Recursive cases: let, if, eps*)
  | Dec_tlet: forall (small: list vsymbol) (hd: vsymbol) m vs (t1: term)
    (v: vsymbol) (t2: term),
    decrease_fun fs ps small hd m vs t1 ->
    (*v is bound, so it is no longer smaller in t2*)
    decrease_fun fs ps (remove vsymbol_eq_dec v small) hd m vs t2 ->
    decrease_fun fs ps small hd m vs (Tlet t1 v t2)
  | Dec_tif: forall (small: list vsymbol) (hd: vsymbol) m vs (f1: formula)
    (t1 t2: term),
    decrease_pred fs ps small hd m vs f1 ->
    decrease_fun fs ps small hd m vs t1 ->
    decrease_fun fs ps small hd m vs t2 ->
    decrease_fun fs ps small hd m vs (Tif f1 t1 t2)
  | Dec_eps: forall (small: list vsymbol) (hd: vsymbol) m vs (f: formula)
    (v: vsymbol),
    decrease_pred fs ps (remove vsymbol_eq_dec v small) hd m vs f ->
    decrease_fun fs ps small hd m vs (Teps f v)
(*This is very similar*)
with decrease_pred (fs: list fn) (ps: list pn) : 
  list vsymbol -> vsymbol -> mut_adt -> list vty -> formula -> Prop :=
  | Dec_notin_f: forall (small: list vsymbol) (hd: vsymbol) (m: mut_adt)
  (vs: list vty) (fmla: formula),
  (forall f, In f fs -> negb (funsym_in_fmla (fn_name f) fmla)) ->
  (forall p, In p ps -> negb (predsym_in (pn_name p) fmla)) ->
  decrease_pred fs ps small hd m vs fmla
  (*First, the recursive predicate call case*)
  | Dec_pred_in: forall (small: list vsymbol) (hd: vsymbol) m vs
    (p: predsym) (p_decl: pn) (l: list vty) (ts: list term) x,
    In p_decl ps ->
    p = pn_name p_decl ->
    (*The decreasing argument must be in our list of decreasing terms*)
    In x small ->
    nth (pn_idx p_decl) ts tm_d = Tvar x ->
    (*Uniformity: we must be applying the function uniformly
    (TODO: make this separate?)*)
    l = map vty_var (p_params p) ->
    (*None of [fs] or[ps] appear in the terms*) 
    (*TODO: will likely need this to show we can ignore function binding in interp for recursive cases*)
    (forall f t, In f fs -> In t ts -> negb (funsym_in_tm (fn_name f) t)) ->
    (forall p t, In p ps -> In t ts -> negb (predsym_in_term (pn_name p) t)) ->
    (*Then this recursive call is valid*)
    decrease_pred fs ps small hd m vs (Fpred p l ts)
  (*Other predicate call*)
  | Dec_pred_notin: forall (small: list vsymbol) (hd: vsymbol) m vs
    (p: predsym) (l: list vty) (ts: list term),
    ~ In p (map pn_name ps) ->
    (*In this case, just recursive*)
    Forall (decrease_fun fs ps small hd m vs) ts ->
    decrease_pred fs ps small hd m vs (Fpred p l ts)
  (*Pattern match on var - this is how we add new, smaller variables*)
  | Dec_fmatch: forall (small: list vsymbol) (hd: vsymbol) m vs
    (mvar: vsymbol) (v: vty) (pats: list (pattern * formula)),
    (*TODO: can we only match on a variable?*)
    mvar = hd \/ In mvar small ->
    (*TODO: don't allow repeated matches on same variable*)
    Forall (fun x => decrease_pred fs ps 
     (*remove pat_fv's (bound), add back constr vars (smaller)*)
     (union vsymbol_eq_dec (vsyms_in_m m vs (pat_constr_vars (fst x))) 
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) 
        small)) mvar m vs (snd x)) pats ->
    decrease_pred fs ps small hd m vs (Fmatch (Tvar mvar) v pats) 
  (*Other pattern match is recursive case*)
  | Dec_fmatch_rec: forall (small: list vsymbol) (hd: vsymbol) m vs
    (tm: term) (v: vty) (pats: list (pattern * formula)),
    ~(exists var, tm = Tvar var /\ (var = hd \/ In var small)) ->
    Forall (fun x => decrease_pred fs ps small hd m vs (snd x)) pats ->
    decrease_pred fs ps small hd m vs (Fmatch tm v pats)
  (*Easy cases: true, false*)
  | Dec_true: forall (small: list vsymbol) (hd: vsymbol) m vs,
    decrease_pred fs ps small hd m vs Ftrue
  | Dec_false: forall (small: list vsymbol) (hd: vsymbol) m vs,
    decrease_pred fs ps small hd m vs Ffalse
  (*Recursive cases: quantifier, eq, binop, let, if*)
  | Dec_quant: forall (small: list vsymbol) (hd: vsymbol) m vs
    (q: quant) (v: vsymbol) (f: formula),
    decrease_pred fs ps (remove vsymbol_eq_dec v small) hd m vs f ->
    decrease_pred fs ps small hd m vs (Fquant q v f)
  | Dec_eq: forall (small: list vsymbol) (hd: vsymbol) m vs
    (ty: vty) (t1 t2: term),
    decrease_fun fs ps small hd m vs t1 ->
    decrease_fun fs ps small hd m vs t2 ->
    decrease_pred fs ps small hd m vs (Feq ty t1 t2)
  | Dec_binop: forall (small: list vsymbol) (hd: vsymbol) m vs
    (b: binop) (f1 f2: formula),
    decrease_pred fs ps small hd m vs f1 ->
    decrease_pred fs ps small hd m vs f2 ->
    decrease_pred fs ps small hd m vs (Fbinop b f1 f2)
  | Dec_flet: forall (small: list vsymbol) (hd: vsymbol) m vs (t1: term)
    (v: vsymbol) (f: formula),
    decrease_fun fs ps small hd m vs t1 ->
    decrease_pred fs ps (remove vsymbol_eq_dec v small) hd m vs f ->
    decrease_pred fs ps small hd m vs (Flet t1 v f)
  | Dec_fif: forall (small: list vsymbol) (hd: vsymbol) m vs
    (f1 f2 f3: formula),
    decrease_pred fs ps small hd m vs f1 ->
    decrease_pred fs ps small hd m vs f2 ->
    decrease_pred fs ps small hd m vs f3 ->
    decrease_pred fs ps small hd m vs (Fif f1 f1 f2)
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

(*TODO: where do we need the bodies?*)
Variable (fs: list fn) (ps: list pn).

Variable fs_uniq: NoDup (map fn_name fs).
Variable fs_typed: Forall (fun f => term_has_type sigma (fn_body f) (s_ret (fn_name f))) fs.

(*OK, how about mutual recursive type*)
(*TODO: remove this once we have function, this is just for testing*)
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

Section WellFounded.

(*The [adt_smaller] relation is conceptually simple:
  both types are instances of ADTs from mut adt m, the second
  is c(args), and the first is in the args of the second*)
Inductive adt_smaller: 
  {ty: vty &  domain (val ty)} -> {ty: vty & domain (val ty)} -> Prop :=
  | ADT_small: forall 
    (x1 x2: {ty: vty &  domain (val ty)})
    ty1 ty2 (*(Hval1: valid_type sigma ty1)
    (Hval2: valid_type sigma ty2)*) (d1: domain (val ty1)) 
    (d2: domain (val ty2)) m a1 a2 srts c args
    (Hx1_1: projT1 x1 = ty1)
    (Hx1_2: d1 = (dom_cast (dom_aux pd) 
      (f_equal (fun x => val x) Hx1_1) (projT2 x1)))
    (Hx2_1: projT1 x2 = ty2)
    (Hx2_2: d2 = (dom_cast (dom_aux pd) 
      (f_equal (fun x => val x) Hx2_1) (projT2 x2)))
    (Hty1: val ty1 = typesym_to_sort (adt_name a1) srts)
    (Hty2: val ty2 = typesym_to_sort (adt_name a2) srts) (*TODO: srts same?*)
    (a_in1: adt_in_mut a1 m)
    (a_in2: adt_in_mut a2 m)
    (m_in: mut_in_ctx m gamma)
    (c_in: constr_in_adt c a2)
    (lengths_eq: length srts = length (m_params m)),
    let adt2 : adt_rep m srts (dom_aux pd) a2 a_in2 :=
      scast (Semantics.adts pd m srts a2 a_in2) (dom_cast _ Hty2 d2) in
    let adt1: adt_rep m srts (dom_aux pd) a1 a_in1 :=
      scast (Semantics.adts pd m srts a1 a_in1) (dom_cast _ Hty1 d1) in
    forall (Hadt2: adt2 = constr_rep gamma_valid m m_in srts
      lengths_eq (dom_aux pd) a2 a_in2 c c_in (Semantics.adts pd m srts) args),
    (exists i Heq, 
    i < length (s_args c) /\
    adt1 = scast (Semantics.adts pd m srts a1 a_in1) 
      (dom_cast (dom_aux pd) Heq (hnth i args s_int (dom_int pd)))) ->
    adt_smaller x1 x2.

(*TODO: move*)
(*We show that [is_sort_adt] is Some for adts*)
Lemma is_sort_adt_adt a srts m:
  mut_in_ctx m gamma ->
  adt_in_mut a m ->
  @is_sort_adt gamma (typesym_to_sort (adt_name a) srts) =
    Some (m, a, (adt_name a), srts).
Proof.
  intros m_in a_in.
  unfold is_sort_adt. simpl.
  assert (@find_ts_in_ctx gamma (adt_name a) = Some (m, a)). {
    apply (@find_ts_in_ctx_iff sigma); auto.
  }
  rewrite H. simpl. 
  f_equal. f_equal.
  apply is_sort_cons_sorts_eq.
Qed.

Lemma scast_rev {A B: Set} (H: A = B) {x y} (Heq: x = scast H y) :
  y = scast (eq_sym H) x.
Proof.
subst. reflexivity.
Qed.

Lemma typesym_to_sort_inj t1 t2 s1 s2:
  typesym_to_sort t1 s1 = typesym_to_sort t2 s2 ->
  t1 = t2 /\ s1 = s2.
Proof.
  unfold typesym_to_sort. intros. inversion H; subst.
  split; auto.
  apply seq.inj_map in H2; auto.
  unfold ssrfun.injective. intros.
  apply sort_inj. auto.
Qed.

Lemma scast_eq_sym {A B: Set} (Heq: A = B) x:
  scast (eq_sym Heq) (scast Heq x) = x.
Proof.
  subst. reflexivity.
Qed.

(*Now we prove that this is well_founded. Basically our proof
  consists of 3 parts:
  1. Show that the second element of the relation has to be
  an ADT
  2. Apply our induction principle from above and do
  various inversions and to show that the generated variables
  are equivalent, allowing us to apply the IH
  3. Apply the IH
  This requires UIP (and funext from adt_rep_ind)*)
Lemma adt_smaller_wf: well_founded adt_smaller.
Proof.
  unfold well_founded. 
  intros a. destruct a as [ty d].
  simpl in *.
  destruct (@is_sort_adt gamma (val ty)) eqn : Hisadt.
  (*Can't be None, contradiction*)
  2: {
    constructor. intros.
    inversion H; subst.
    simpl in Hty2.
    rewrite Hty2 in Hisadt.
    rewrite (is_sort_adt_adt _ _ _ m_in a_in2) in Hisadt.
    inversion Hisadt.
  }
  destruct p as [[[m a] ts] srts].
  (*We need to know about the length of the srts list*)
  destruct (Nat.eq_dec (length srts) (length (m_params m))).
  2: {
    constructor. intros. inversion H; subst.
    simpl in Hty2.
    rewrite Hty2 in Hisadt.
    rewrite (is_sort_adt_adt _ _ _ m_in a_in2) in Hisadt.
    inversion Hisadt; subst.
    rewrite lengths_eq in n. contradiction.
  }
  rename e into Hlen.
  (*Need an adt_rep to do induction on*)
  set (adt_spec := (is_sort_adt_spec gamma_valid _ _ _ _ _ Hisadt)).
  pose proof (proj1 adt_spec) as Hseq.
  pose proof (proj1 (proj2 adt_spec)) as a_in.
  pose proof (proj1 (proj2 (proj2 adt_spec))) as m_in.
  clear adt_spec.
  remember (scast (Semantics.adts pd m srts a a_in) (dom_cast _ Hseq d)) as adt.
  revert Heqadt.
  unfold dom_cast. rewrite scast_scast. intros Hd.
  apply scast_rev in Hd.
  generalize dependent ((eq_sym
  (eq_trans (f_equal domain Hseq) (Semantics.adts pd m srts a a_in)))).
  intros Heqadt Hd. subst.
  (*Here, we use induction*)
  apply (adt_rep_ind m m_in srts Hlen (fun t t_in x =>
    forall ty1 Heq, val ty1 = typesym_to_sort (adt_name t) srts ->
    Acc adt_smaller (existT (fun ty0 => domain (val ty0)) ty1 
      (scast Heq x)))); auto.
  intros t t_in x c Hc args Hx IH ty1 Heq Hty1.
  constructor.
  intros y Hsmall.
  remember (scast Heq x) as x2. inversion Hsmall. subst.
  simpl in *. unfold dom_cast in adt1, adt2. simpl in adt1, adt2.

  destruct H as [i [Heqith [Hi Hadt1]]].
  (*Need to prove lots of equalities before applying the IH. First,
    a2's name and srts*)
  assert (adt_name a2 = adt_name t /\ srts0 = srts). {
    apply typesym_to_sort_inj; rewrite <- Hty2; auto.
  }
  destruct H;subst srts0.
  (*Now prove m equal*)
  assert (m = m0) by
    (apply (@mut_adts_inj _ _ gamma_valid) with(a1:=t)(a2:=a2); auto).
  subst m0.
  (*Now prove a2 and t equal*)
  assert (a2 = t) by
    (apply (adt_names_inj' gamma_valid a_in2); auto).
  subst t.
  clear H.
  (*Now we need to deal with adt1 and adt2*)
  subst adt1. apply scast_inj in Hadt1.
  unfold dom_cast in Hadt1.
  destruct y as [ty2 d2]. simpl in *.
  symmetry in Hadt1.
  apply scast_rev in Hadt1. subst.
  (*From adt2, get info about c*)
  subst adt2. rewrite !scast_scast in Hadt2.
  assert (m_in = m_in0) by apply bool_irrelevance.
  subst m_in0.
  assert (Hlen = lengths_eq). {
    clear. generalize dependent (length srts); intros.
    subst. apply UIP_dec. apply Nat.eq_dec.
  }
  subst lengths_eq. 
  assert (a_in2 = t_in). {
    apply bool_irrelevance.
  }
  subst a_in2.
  assert (eq_trans Heq
  (eq_trans (f_equal domain Hty2)
     (Semantics.adts pd m srts a2 t_in)) = eq_refl). {
  (*HERE, we need UIP*)
    clear. apply IndTypes.UIP. }
  rewrite H in Hadt2. simpl in Hadt2.
  clear H.
  (*Now we use injectivity*)
  destruct (funsym_eq_dec c c0). 2: {
    exfalso. 
    apply (constr_rep_disjoint gamma_valid _ _ _ _ _ _ _ _ _ _ n Hadt2).
  }
  subst c0.
  assert (Hc = c_in). apply bool_irrelevance. subst Hc.
  apply constr_rep_inj in Hadt2. 2: apply all_unif; auto.
  subst args0.
  (*Now, we can apply the IH*)
  specialize (IH _ _ a_in1 Heqith Hi ty2).
  (*We don't need UIP here if we build a proof term carefully*)
  set (Hrep := (eq_trans (eq_sym (Semantics.adts pd m srts a1 a_in1))
  (eq_sym (f_equal domain Hty0)))).
  specialize (IH Hrep Hty0).
  match goal with
  | H: Acc ?y (existT ?g1 ?ty1 ?x1) |- Acc ?y (existT ?g ?ty2 ?x2) =>
    let Heq := fresh "Heq" in
    assert (Heq: x1 = x2); [|rewrite <- Heq; auto]
  end. clear.
  generalize dependent (val ty2). intros; subst. simpl.
  subst Hrep. simpl. rewrite scast_eq_sym.
  reflexivity.
Qed.

(*Now, transitive closure*)
Inductive R_trans {A: Type} (R: A -> A -> Prop) : A -> A -> Prop :=
  | Rtrans_once: forall x y,
    R x y ->
    R_trans R x y
  | Rtrans_multi: forall x y z,
    R_trans R x y ->
    R y z ->
    R_trans R x z.

(*Proof of transitive closure wf from 
  [https://madiot.fr/pso/tp6.html]*)
Lemma Acc_inv {A : Type} (R : A -> A -> Prop) x y: 
  R x y -> Acc R y -> Acc R x.
Proof.
  intros. apply H0. auto.
Qed.

Lemma Acc_trans {A : Type} (R : A -> A -> Prop) :
  forall x, Acc R x -> Acc (R_trans R) x.
Proof.
  intros. induction H.
  constructor. intros.
  inversion H1; subst.
  - apply H0; auto.
  - eapply Acc_inv. apply H2. apply H0. auto.
Qed.

Lemma R_trans_wf {A: Type} (R: A -> A -> Prop):
  well_founded R ->
  well_founded (R_trans R).
Proof.
  intros Hr.
  unfold well_founded.
  intros. apply Acc_trans. apply Hr.
Qed.

(*The transitive closure of [adt_smaller]*)
Definition adt_smaller_trans := R_trans adt_smaller.
Definition adt_smaller_trans_wf := R_trans_wf adt_smaller adt_smaller_wf.

(*Part 2: lift to [arg_list]*)

(*TODO: do version with predsyms also*)
(*
Variable srts: list sort.*)

Definition hide_ty {ty: vty} (d: domain (val ty)) :
  {x: vty & domain (val x)} := existT _ ty d.

(*Lemma for casting*)
Lemma arg_nth_eq srts (f: funsym) (i: nat) (Hi: i < length (s_args f)) :
  nth i (funsym_sigma_args f srts) s_int =
  val (ty_subst (s_params f) (sorts_to_tys srts)
    (nth i (s_args f) vty_int)).
Proof.
  assert ((ty_subst (s_params f) (sorts_to_tys srts) (nth i (s_args f) vty_int)) =
  (ty_subst_s (s_params f) srts (nth i (s_args f) vty_int))). {
    unfold ty_subst_s, ty_subst, v_subst. simpl. reflexivity. }
  rewrite H. clear H.
  unfold funsym_sigma_args, ty_subst_list_s.
  rewrite map_nth_inbound with(d2:=vty_int); auto.
  apply subst_sort_eq.
Qed.

Lemma fn_idx_bound (f: fn) : fn_idx f < length (s_args (fn_name f)).
Proof.
  destruct f; simpl in *.
  apply Nat.eqb_eq in fn_args_len0. rewrite <- fn_args_len0.
  apply Nat.ltb_lt. apply fn_idx_in0.
Qed.

Definition cast_funargs (srts: list sort) {f1 f2: funsym} (H: f1 = f2) :
  funsym_sigma_args f1 srts = funsym_sigma_args f2 srts :=
  f_equal (fun x => funsym_sigma_args x srts) H.

Definition packed_args : Set :=
    {x: {f: fn | In f fs} & {srts: list sort & arg_list domain (funsym_sigma_args (fn_name (proj1_sig x)) srts)}}.


(*The relation is simple: the (fn_idx)th element of the 1st
  arg_list must be smaller than the second*)
Inductive arg_list_smaller: 
 packed_args -> packed_args ->
  Prop :=
  | AL_small: forall 
    (x1: packed_args) 
    (x2: packed_args)
    (f1 f2: fn) 
    srts
    (Hsrts1: projT1 (projT2 x1) = srts)
    (Hsrts2: projT1 (projT2 x2) = srts)
    (a1: arg_list domain (funsym_sigma_args (fn_name f1) srts)) 
    (a2: arg_list domain (funsym_sigma_args (fn_name f2) srts))
    (Hf1: f1 = proj1_sig (projT1 x1))
    (Hf2: f2 = proj1_sig (projT1 x2))
    (Ha1: a1 = cast_arg_list 
      (eq_trans (cast_funargs (projT1 (projT2 x1)) (eq_sym (f_equal fn_name Hf1)))
        (f_equal (funsym_sigma_args (fn_name f1)) Hsrts1))
      (projT2 (projT2 x1)))
    (Ha2: a2 = 
    cast_arg_list 
      (eq_trans (cast_funargs (projT1 (projT2 x2)) (eq_sym (f_equal fn_name Hf2)))
        (f_equal (funsym_sigma_args (fn_name f2)) Hsrts2))
      (projT2 (projT2 x2))),
    adt_smaller_trans 
      (hide_ty (dom_cast _ (arg_nth_eq srts (fn_name f1) (fn_idx f1) (fn_idx_bound f1)) 
        (hnth (fn_idx f1) a1 s_int (dom_int pd))))
      (hide_ty (dom_cast _ (arg_nth_eq srts (fn_name f2) (fn_idx f2) (fn_idx_bound f2)) 
        (hnth (fn_idx f2) a2 s_int (dom_int pd)))) ->
    arg_list_smaller x1 x2.

(*Now we prove that this is well-founded using
  well-founded induction on [adt_smaller_trans].
  This proof is actually very easy*)
Lemma arg_list_smaller_wf: well_founded arg_list_smaller.
Proof.
  unfold well_founded. intros a.
  (*Now we get y to induct on*)
  set (a2 :=projT2 (projT2 a)). simpl in a2.
  set (srts:=projT1(projT2 a)) in *.
  set (f2:= proj1_sig (projT1 a)). 
  remember ((hide_ty (dom_cast _ (arg_nth_eq srts (fn_name f2) (fn_idx f2) (fn_idx_bound f2)) 
  (hnth (fn_idx f2) a2 s_int (dom_int pd))))) as y.
  subst a2 f2 srts.
  generalize dependent a. revert y.
  (*Apply IH*)
  match goal with
  | |- forall y, ?P => apply (well_founded_ind (adt_smaller_trans_wf)
    (fun y => P)) end. 
  (*Rest is direct from IH and inversion on rel*)
  intros x IH a2 Hx.
  constructor.
  intros a1 Hsmall.
  inversion Hsmall; subst.
  destruct a1; destruct a2; simpl in *.
  destruct s; destruct s0; subst; simpl in *. subst. simpl in *.
  eapply IH. 
  apply H. reflexivity.
Defined.

(*TODO: don't think we need the transitive closure of this, but see*)

(*TODO: move srts*)

End WellFounded.

(*TODO: move*)
(*We can make this opaque: we don't actually need
  to compute with this (TODO: should this be Defined?)*)
Definition find_fn (f: funsym) (l: list fn) : 
Either
  {f': fn | In f' l /\ f = fn_name f'}
  (~ In f (map fn_name l)).
induction l; simpl.
- apply Right. auto.
- destruct IHl.
  + destruct s as [f' [Hinf' Hf]]; subst.
    apply Left. apply (exist _ f'). split; auto.
  + destruct (funsym_eq_dec (fn_name a) f).
    * subst. apply Left. apply (exist _ a). split; auto.
    * apply Right. intros [Heq | Hin]; subst; auto.
Qed.

(*So we need other hypotheses about vt, params, etc*)

(*Since vt is fixed through everything (we are requiring all
  mutually recursive functions to have the same params)
  This is a restriction on why3 (maybe), but I am OK with that
  we can assume some property of it, then build it up later
  *)
Variable params: list typevar.
Variable params_eq: forall f, In f fs -> s_params (fn_name f) = params.
(*Variable srts_len: length srts = length params.*)
Variable f_typevars: forall f, In f fs -> 
  forall ty, In ty (s_ret (fn_name f) :: s_args (fn_name f)) ->
  forall x, In x (type_vars ty) ->
  In x params.
(*Will come from wf_context*)

(*We need to build a new val_typevar, we cannot assume this
  or maybe it is OK*)

Definition vt_eq srts:= forall i, i < length params ->
  (v_typevar vt) (nth i params EmptyString) = nth i srts s_int.

(*The mut adt we are recursing on*)
Variable m: mut_adt.
Variable vs: list vty.

(*TODO: will need to add this to typing*)

(*TODO: I think: need hypothesis about relationship
  between s_args and fn_args - also move to typing/put in
  definition of funpred_def maybe*)
Variable args_agree: forall f, In f fs ->
  map snd (fn_args f) = s_args (fn_name f).

Variable recurse_on_adt: forall f, In f fs ->
  exists a,
  adt_in_mut a m /\ snd(nth (fn_idx f) (fn_args f) vs_d) =
    vty_cons (adt_name a) vs.
(*Now we can prove the lemma to convert*)


(*Invert [decrease_fun] for funs - 2 cases*)

(*TODO: need invariant that all elements in small have correct
  types (I think) - easy to show it is preserved*)

(*TODO: change nil to ps*)
Lemma dec_inv_tfun_in {small: list vsymbol} {hd: vsymbol} {f: funsym}
  {l: list vty} {ts: list term}
  (Hde: decrease_fun fs nil small hd m vs (Tfun f l ts)) 
  {fn_def: fn} 
  (Hin: In fn_def fs)
  (Hfeq: f = fn_name fn_def):
  l = map vty_var (s_params f) /\
  Forall (fun t => forall f, In f fs -> negb (funsym_in_tm (fn_name f) t)) ts /\
  Forall (fun t => forall p, In p nil -> negb (predsym_in_term (pn_name p) t)) ts.
Proof.
  inversion Hde; subst.
  - exfalso. specialize (H _ Hin).
    simpl in H. destruct (funsym_eq_dec (fn_name fn_def) (fn_name fn_def));
    simpl in H; try inversion H. contradiction.
  - split; auto.
  - exfalso. apply H5. rewrite in_map_iff. exists fn_def. split; auto.
Qed.

Lemma dec_inv_tfun_arg {small: list vsymbol} {hd: vsymbol} {f: funsym}
{l: list vty} {ts: list term}
(Hde: decrease_fun fs nil small hd m vs (Tfun f l ts)) 
{fn_def: fn} 
(Hin: In fn_def fs)
(Hfeq: f = fn_name fn_def):
exists x, In x small /\  nth (fn_idx fn_def) ts tm_d = Tvar x.
Proof.
  inversion Hde; subst.
  - exfalso. specialize (H _ Hin).
    simpl in H. destruct (funsym_eq_dec (fn_name fn_def) (fn_name fn_def));
    simpl in H; try inversion H. contradiction.
  - assert (fn_def = f_decl). apply (NoDup_map_in fs_uniq Hin H2 H3).
    subst. exists x. split; auto.
  - exfalso. apply H5. rewrite in_map_iff. exists fn_def. split; auto.
Qed. 

Lemma dec_inv_tfun_notin {small: list vsymbol} {hd: vsymbol} {f: funsym}
{l: list vty} {ts: list term}
(Hde: decrease_fun fs nil small hd m vs (Tfun f l ts)) 
(Hnotin: ~ In f (map fn_name fs)) :
Forall (decrease_fun fs nil small hd m vs) ts.
Proof.
  inversion Hde; subst.
  - rewrite Forall_forall. intros.
    apply Dec_notin_t.
    + intros. specialize (H _ H2). simpl in H.
      bool_hyps. rewrite existsb_false in H3.
      rewrite Forall_forall in H3. specialize (H3 _ H1).
      rewrite H3; auto.
    + intros. specialize (H0 _ H2). simpl in H0.
      bool_hyps. rewrite existsb_false in H0.
      rewrite Forall_forall in H0. specialize (H0 _ H1).
      rewrite H0; auto.
  - exfalso. apply Hnotin. rewrite in_map_iff.
    exists f_decl. split; auto.
  - auto.
Qed.

(*As a corollary, we get that [decrease_fun] holds recursively*)
Corollary dec_inv_tfun_rec {small: list vsymbol} {hd: vsymbol} {f: funsym}
  {l: list vty} {ts: list term}
  (Hde: decrease_fun fs nil small hd m vs (Tfun f l ts)) :
  Forall (fun t => decrease_fun fs nil small hd m vs t) ts.
Proof.
  destruct (in_dec funsym_eq_dec f (map fn_name fs)).
  - rewrite in_map_iff in i. destruct i as [fn_def [Hfeq Hin]].
    apply dec_inv_tfun_in with(fn_def:=fn_def) in Hde; auto.
    destruct_all.
    revert H0 H1. rewrite !Forall_forall; intros.
    apply Dec_notin_t; auto.
  - eapply dec_inv_tfun_notin. apply Hde. auto.
Qed.

Definition term_has_type_cast {t1 t2: term} {ty: vty} (Heq: t1 = t2)
  (Hty: term_has_type sigma t1 ty) : term_has_type sigma t2 ty :=
  match Heq with
  | eq_refl => Hty
  end.

(*We need a very complicated and ugly version of
  [get_arg_list] for this case. Both the inner function
  is much more complicated (requiring many more conditions)
  and the output is a sigma type because we need additional
  information about the output, and proving it later gives
  Coq a LOT of trouble in the later termination check.
  We give this version here; the real function has this
  inlined as a nested fix (or else Coq cannot prove
  termination). But later TODO, we will prove a lemma
  that relates them so that we have a nicer form to use*)

(*First, a lemma for the hard case so that the proof term
  (which we need to build manually for inlining)
  is not that horrible*)

Lemma arg_list_case_1
(v: val_vars pd vt)
(y: vsymbol)
(d: {ty : vty & domain (val ty)})
(f: funsym)
(vs': list vty)
(small: list vsymbol)
(Hsmall: forall x : vsymbol, In x small -> adt_smaller_trans (hide_ty (v x)) d)
(rep: forall (t : term) (ty : vty) (small : list vsymbol)
        (Hty : term_has_type sigma t ty),
      decrease_fun fs [] small y m vs t ->
      (forall x : vsymbol, In x small -> adt_smaller_trans (hide_ty (v x)) d) ->
      {d : domain (val ty)
      | forall (x : vsymbol) (Heqx : t = Tvar x),
        d =
        dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0)
             (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
          (var_to_dom pd vt v x)})
(Hparamslen: Datatypes.length vs' = Datatypes.length (s_params f))
(thd: term)
(ttl: list term)
(Hdecs: Forall (fun t : term => decrease_fun fs [] small y m vs t) (thd :: ttl))
(ahd: vty)
(atl: list vty)
(Heq: Datatypes.length (thd :: ttl) = Datatypes.length (ahd :: atl))
(Htys: Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
         (combine (thd :: ttl) (map (ty_subst (s_params f) vs') (ahd :: atl))))
(vs_small: vsymbol)
(Hthd: nth 0 (thd :: ttl) tm_d = Tvar vs_small):
exists
(ty' : vty) (Hty' : term_has_type sigma (Tvar vs_small) ty') 
(Heq0 : val ty' = ty_subst_s (s_params f) (map (fun x : vty => val x) vs') ahd),
dom_cast (dom_aux pd)
  (funsym_subst_eq (s_params f) vs' (v_typevar vt) ahd (s_params_Nodup f)
     (eq_sym Hparamslen))
  (proj1_sig
     (rep thd (ty_subst (s_params f) vs' ahd) small (Forall_inv Htys)
        (Forall_inv Hdecs) Hsmall)) =
dom_cast (dom_aux pd) Heq0
  (dom_cast (dom_aux pd)
     (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
     (var_to_dom pd vt v vs_small)).
Proof.
  exists (ty_subst (s_params f) vs' ahd).
  exists (eq_ind (nth 0 (thd :: ttl) tm_d)
  (fun t : term => term_has_type sigma t (ty_subst (s_params f) vs' ahd))
  (Forall_inv Htys) (Tvar vs_small) Hthd).
  exists (funsym_subst_eq (s_params f) vs' (v_typevar vt) ahd
      (s_params_Nodup _) (eq_sym Hparamslen)) .
  (*simpl.*)
  destruct (rep thd (ty_subst (s_params f) vs' ahd) small 
    (Forall_inv Htys) (Forall_inv Hdecs) Hsmall) as [rep1 rep2].
  simpl.
  rewrite (rep2 vs_small Hthd).
  reflexivity.
(*Needs to be transparent for termination*)
Defined.

(*The function we need (TODO: change name)*)
Fixpoint get_arg_list_ext_aux' {v : val_vars pd vt} {y d} (f: funsym)
  {vs': list vty} {ts: list term} (*{ty: vty}*)
  {small}
  (Hsmall: forall x, In x small ->
  adt_smaller_trans (hide_ty (v x)) d)
  (rep: forall (t: term) (ty: vty) (small: list vsymbol)
      (Hty: term_has_type sigma t ty)
      (Hdec: decrease_fun fs nil small y m vs t)
      (Hsmall: forall x, In x small ->
          (*TODO: type restriction here?*)
          adt_smaller_trans (hide_ty (v x)) d),
      {d: domain (val ty) | forall x (Heqx: t = Tvar x),
          d = dom_cast _ (f_equal (fun x => val x) 
            (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
            (var_to_dom _ vt v x)})
  (Hparamslen: length vs' = length (s_params f))
  {struct ts}:
  forall args
  (Hargslen: length ts = length args)
  (Hall: Forall (fun x => term_has_type sigma (fst x) (snd x))
    (combine ts (map (ty_subst (s_params f) vs') args)))
  (Hdec: Forall (fun t => decrease_fun fs nil small y m vs t) ts),
  {a: arg_list domain (ty_subst_list_s (s_params f) 
    (map (fun x => val x) vs') args) |
    forall (j: nat) (Hj: j < length ts) vs_small,
    nth j ts tm_d = Tvar vs_small ->
    exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
        Heq,
    (*Avoids the need to relate hnth to term_rep_aux (nth) by
    directly giving the result we need*)
    hnth j a s_int (dom_int pd) =
    dom_cast (dom_aux pd) Heq
      (dom_cast (dom_aux pd)
        (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
        (var_to_dom pd vt v vs_small))} :=
match ts as ts'
  return forall args,
  length ts' = length args ->
  Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
    (combine ts' (map (ty_subst (s_params f) vs') args)) ->
  Forall (fun t : term => decrease_fun fs [] small y m vs t) ts' ->
  {a: arg_list domain (ty_subst_list_s (s_params f) 
    (map (fun x => val x) vs') args) |
    forall (j: nat) (Hj: j < length ts') vs_small,
    nth j ts' tm_d = Tvar vs_small ->
    exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
        Heq,
    hnth j a s_int (dom_int pd) =
    dom_cast (dom_aux pd) Heq
      (dom_cast (dom_aux pd)
        (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
        (var_to_dom pd vt v vs_small))} 
  with
  | nil => fun args Hlen _ _ => 
      match args as a' return length nil = length a' -> 
      {a: arg_list domain (ty_subst_list_s (s_params f) 
        (map (fun x => val x) vs') a') |
        forall (j: nat) (Hj: j < length nil) vs_small,
        nth j nil tm_d = Tvar vs_small ->
        exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
            Heq,
        hnth j a s_int (dom_int pd) =
        dom_cast (dom_aux pd) Heq
          (dom_cast (dom_aux pd)
            (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
            (var_to_dom pd vt v vs_small))} 
      with 
      (*Both get contradictions here*)
      | nil => fun Hlena => exist _ (@HL_nil _ _) 
        (fun j Hj => False_rect _ (Nat.nlt_0_r j Hj))
      | ahd :: atl => fun Heq => False_rect _ (Nat.neq_0_succ (length atl) Heq)
      end Hlen
  | thd :: ttl => 
    fun args Hlen Htys Hdecs => 
    match args as a' return length (thd :: ttl) = length a' ->
      Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
        (combine (thd :: ttl) (map (ty_subst (s_params f) vs') a')) ->
      {a: arg_list domain (ty_subst_list_s (s_params f) 
        (map (fun x => val x) vs') a') |
        forall (j: nat) (Hj: j < length (thd :: ttl)) vs_small,
        nth j (thd :: ttl) tm_d = Tvar vs_small ->
        exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
            Heq,
        hnth j a s_int (dom_int pd) =
        dom_cast (dom_aux pd) Heq
          (dom_cast (dom_aux pd)
            (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
            (var_to_dom pd vt v vs_small))} 
      with
      | nil => fun Hlen =>
        False_rect _ (Nat.neq_succ_0 (length ttl) Hlen)
      | ahd :: atl => fun Heq Htys =>
        exist _ (HL_cons _ _ _ (dom_cast (dom_aux pd)
        (funsym_subst_eq (s_params f) vs' (v_typevar vt) ahd
         (s_params_Nodup _) (eq_sym Hparamslen)) 
          (proj1_sig (rep _ _ _ (Forall_inv Htys) (Forall_inv Hdecs) Hsmall))) 
          (proj1_sig (get_arg_list_ext_aux'  f  Hsmall rep Hparamslen atl 
            (Nat.succ_inj (length ttl) (length atl) Heq)
            (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) 
        (*build the function for second part*)
        (fun j => 
          match j as j' return j' < length (thd :: ttl) ->
            forall (vs_small: vsymbol),
            nth j' (thd :: ttl) tm_d = Tvar vs_small ->
            exists
              (ty' : vty) (Hty' : term_has_type sigma (Tvar vs_small) ty') 
            (Heq0 : val ty' =
                    nth j'
                      (ty_subst_list_s (s_params f) (map (fun x : vty => val x) vs') (ahd :: atl))
                      s_int),
              hnth j'
                (HL_cons domain (ty_subst_s (s_params f) (map (v_subst (v_typevar vt)) vs') ahd)
                  (ty_subst_list_s (s_params f) (map (fun x : vty => val x) vs') atl)
                  (dom_cast (dom_aux pd)
                      (funsym_subst_eq (s_params f) vs' (v_typevar vt) ahd 
                        (s_params_Nodup f) (eq_sym Hparamslen))
                      (proj1_sig
                        (rep (fst (thd, ty_subst (s_params f) vs' ahd))
                            (snd (thd, ty_subst (s_params f) vs' ahd)) small 
                            (Forall_inv Htys) (Forall_inv Hdecs) Hsmall)))
                  (proj1_sig (get_arg_list_ext_aux' f Hsmall
                     rep Hparamslen atl
                      (Nat.succ_inj (Datatypes.length ttl) (Datatypes.length atl) Heq)
                      (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) s_int 
                (dom_int pd) =
              dom_cast (dom_aux pd) Heq0
                (dom_cast (dom_aux pd)
                  (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
                  (var_to_dom pd vt v vs_small))
          with
          | 0 => 
            (*Case when j = 0*)
            fun _ vs_small Hthd => 
              arg_list_case_1 v y d f vs' small Hsmall rep Hparamslen thd ttl 
                Hdecs ahd atl Heq Htys vs_small Hthd
          | S j' => 
            (fun Hj vs_small Hnth =>
            (proj2_sig (get_arg_list_ext_aux' f Hsmall rep Hparamslen atl 
            (Nat.succ_inj (length ttl) (length atl) Heq)
            (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)) j'
            (Arith_prebase.lt_S_n j' (length ttl) Hj) vs_small Hnth
            ) )
          end)
      end Hlen Htys
  end.

  (*A computable version - why is standard version not computable?*)
Definition proj1' {A B: Prop} (H: A /\ B) : A :=
  match H with
  | conj x x0 => x
  end.

Definition proj2' {A B: Prop} (H: A /\ B) : B :=
  match H with
  | conj x x0 => x0
  end.

(*Is this the lemma we need?*)

Lemma map_vars_srts srts: 
  length srts = length params ->
  vt_eq srts ->
  map (fun x => val x) (map vty_var params) = srts.
Proof.
  intros srts_len vt_eq.
  rewrite map_map. apply list_eq_ext'; rewrite map_length; auto;
  intros n d Hn.
  rewrite map_nth_inbound with(d2:= EmptyString); auto.
  apply sort_inj. simpl.
  rewrite vt_eq; auto. erewrite nth_indep; auto. lia.
Qed.

Lemma map_vals_srts' srts f:
  length srts = length params ->
  vt_eq srts ->
  In f fs ->
  map (fun x => val x) (map vty_var (s_params (fn_name f))) = srts.
Proof.
  intros.
  rewrite params_eq; auto. apply map_vars_srts; auto.
Qed.


(*I think we need to assume uniform functions for this to work*)

(*So we need to say: all have same params
  and
  any invocation of any of the functions in fs
  have to be with (map vty_var params)
  
  Then, we know (from some stuff proved before)
  that val vt of this is just srts (similar to ADTs)

  problem: vt should not be same in outer and inner
  i think that inner (in term_rep_aux) needs to have
  vt (nth i params) = nth i srts
  outer not necessarily
  so we may need to carry this around in a proof

  *)
(* TODO: after uniform, with assumption
Lemma fun_args_srts (f: fn)  (vs: list vty) (ts: list term) :
  length vs = length srts ->
  In f fs ->
  Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
    (combine ts (map (ty_subst (s_params (fn_name f)) vs) (s_args (fn_name f)))) ->
  (map (fun x => val x) vs) = srts.
Proof.
  intros.
  apply list_eq_ext'; rewrite map_length; auto.
  intros n d Hn.
  rewrite map_nth_inbound with(d2:=vty_int); auto.
  erewrite v_ty_subst_eq with(params:=params) (srts:=srts); auto.
*)

(*TODO: fix the smaller relation - can only add things of
  correct type
  So if x (vsymbol) has type vty_cons ts vs,
  and if ts is in mut adt m,
  only add things of form vty_cons ts' vs, for ts' in m
  Or we can say (since it must be case that structurally dec on ADT,
    say: we have mut adt m, adt a in m such that x has type 
    vty_cons (adt_name a) vs)

    need vs because we cannot recurse on list bool if arg
    is list int 
    hmm, do we need - seems like uniformity should rule this out
    dont add for now, might need later
  
  *)


(*TODO: move to typing (I think)*)
(*2 parts to condition
  1. All function and pred symbols in def have same params
  2. All functions/pred symbols in def appear in each term/fmla
    applied to same arguments*)

(*TODO: need something about *)



(*Idea should be:
  suppose have params and srts with length params = length srts

  Suppose that vt matches params to appropriate srts

  let ty be a vty and suppose that all typevars in vty are in 
  params. Then val vt ty = ty_subst_s params srts ty

  (*NOTE: showed this in [v_ty_subst_eq]*)

  then, if we know that each of vs has type corresponding to
  s_args f, and that all typevars must be in s_params,
  we get that (map (val vt) vs = funsym_sigma_args srts)
  or something
  (*TODO: this*)

*)


  Lemma eq_trans_refl {A: Set} {x1 x2: A} (H: x1 = x2):
  eq_trans eq_refl H = H.
  Proof.
    destruct H. reflexivity.
  Qed.

(*rewrite our cast into a [cast_arg_list] so we can simplify*)
Lemma scast_funsym_args_eq {f: funsym} {s1 s2: list sort}
  (Heq: s1 = s2) x:
  scast (f_equal (fun x => arg_list domain (funsym_sigma_args f x)) Heq)
    x =
  cast_arg_list (f_equal (fun x => funsym_sigma_args f x) Heq) x.
Proof.
  destruct Heq. reflexivity.
Qed.

Lemma ty_subst_fun_params_id: forall params d v,
  In v params ->
  ty_subst_fun params (map vty_var params) d v = vty_var v.
Proof.
  intros. induction params0. inversion H.
  simpl. simpl in H. destruct (typevar_eq_dec v a); subst; auto.
  simpl. destruct H; subst; auto. contradiction.
Qed.

Lemma map_id' {A : Type} (f: A -> A) l:
  Forall (fun x => f x = x) l ->
  map f l = l.
Proof.
  induction l; simpl; intros; auto. inversion H; subst; auto.
  rewrite H2. f_equal; auto.
Qed.

Lemma ty_subst_params_id: forall params x,
  (forall v, In v (type_vars x) -> In v params) ->
  ty_subst params (map vty_var params) x = x.
Proof.
  intros. unfold ty_subst. induction x; simpl; auto.
  apply ty_subst_fun_params_id. apply H. simpl; auto.
  f_equal. apply map_id'.
  revert H0. rewrite !Forall_forall; intros.
  apply H0; auto. intros. apply H. simpl. simpl_set; auto.
  exists x. split; auto.
Qed.

(*I believe we have the following*)

Lemma dom_cast_compose {domain_aux: sort -> Set} {s1 s2 s3: sort}
  (Heq1: s2 = s3) (Heq2: s1 = s2) x:
  dom_cast domain_aux Heq1 (dom_cast domain_aux Heq2 x) =
  dom_cast domain_aux (eq_trans Heq2 Heq1) x.
Proof.
  subst. reflexivity.
Qed.

(*The type doesn't actually matter for [adt_smaller]; only
  the value. Thus, we can cast and still have the relation hold*)
Lemma adt_smaller_hide_cast {ty1 ty2: vty} (x: domain (val ty1)) 
  (y: {t: vty & domain (val t)}) (Heq: val ty1 = val ty2):
  adt_smaller (hide_ty x) y ->
  adt_smaller (hide_ty (dom_cast (dom_aux pd) Heq x)) y.
Proof.
  intros. unfold hide_ty in *. destruct y as [ty_y dy].
  rename x into dx. inversion H. subst x1 x2.
  simpl in *. subst ty0. subst ty3. simpl in *.
  unfold dom_cast in Hx1_2, Hx2_2. simpl in Hx1_2, Hx2_2. subst d1 d2.
  eapply (ADT_small _ _ ty2 ty_y (dom_cast (dom_aux pd) Heq dx) 
    dy m0 a1 a2 srts c args _ _ _ _ (eq_trans (eq_sym Heq) Hty1) 
    Hty2 a_in1 a_in2 m_in c_in lengths_eq).
  Unshelve. all: try reflexivity.
  - apply Hadt2.
  - destruct H0 as [i [Heq' [Hi Had1]]].
    exists i. exists Heq'. split; auto.
    subst adt1. rewrite <- Had1.
    (*Need to cancel out eq_sym*)
    unfold dom_cast; rewrite !scast_scast.
    rewrite eq_trans_assoc, <- eq_trans_map_distr.
    rewrite eq_trans_assoc, eq_trans_sym_inv_r.
    rewrite eq_trans_refl.
    reflexivity.
Qed.

(*And for transitive version:*)

Lemma adt_smaller_trans_hide_cast {ty1 ty2: vty} (x: domain (val ty1)) 
  (y: {t: vty & domain (val t)}) (Heq: val ty1 = val ty2):
  adt_smaller_trans (hide_ty x) y ->
  adt_smaller_trans (hide_ty (dom_cast (dom_aux pd) Heq x)) y.
Proof.
  intros.
  remember (hide_ty x) as x'.
  generalize dependent x.
  induction H; intros; subst.
  - constructor. apply adt_smaller_hide_cast; auto.
  - eapply Rtrans_multi.
    apply IHR_trans. reflexivity. auto.
Qed.

Lemma v_subst_aux_sort_eq (v: typevar -> vty) (t: vty):
  (forall x, In x (type_vars t) -> is_sort (v x)) ->
  is_sort (v_subst_aux v t).
Proof.
  intros. induction t; simpl; intros; auto.
  apply H. left; auto.
  apply is_sort_cons_iff.
  intros. rewrite in_map_iff in H1.
  destruct H1 as [y [Hy Hiny]]; subst.
  rewrite Forall_forall in H0. apply H0; auto.
  intros. apply H. simpl. simpl_set. exists y. split; auto.
Qed.

(*Create the valuation given a list of sorts and variables*)
Fixpoint val_with_args (vv: val_vars pd vt) (vars: list vsymbol) 
  {srts: list sort}
  (a: arg_list domain srts) :
  val_vars pd vt :=
  fun (x: vsymbol) =>
  match vars, a with
  | hd :: tl, HL_cons shd stl d t =>
     (*Need to know that types are equal so we can cast the domain*)
     match (vty_eq_dec (val (snd x))) shd with
     | left Heq => if vsymbol_eq_dec hd x then 
        dom_cast _ (sort_inj (eq_sym Heq)) d
         else val_with_args vv tl t x
     | _ => val_with_args vv tl t x
     end
  | _, _ => vv x
  end.

  (*Basically UIP for x = y instead of x = x*)
Lemma dec_uip_diff {A: Set} {x1 x2: A} 
  (eq_dec: forall (x y: A), {x= y} + {x <> y}) 
  (H1 H2: x1 = x2):
  H1 = H2.
Proof.
  subst. apply UIP_dec. auto.
Qed.

(*The spec: suppose that length vars = length srts
  and that for all i, snd (nth i vars) = val (nth i s_args).
  Then val_with_args vv (nth i vars) = nth i a*)
Lemma val_with_args_in vv (vars: list vsymbol) (srts: list sort)
  (a: arg_list domain srts)
  (Hnodup: NoDup vars)
  (Hlen: length vars = length srts)
  (Htys: forall i, i < length vars -> 
    val(snd (nth i vars vs_d)) =
    nth i srts s_int):
  forall i (Hi: i < length vars),
  val_with_args vv vars a (nth i vars vs_d) =
  dom_cast _ (eq_sym (Htys i Hi)) (hnth i a s_int (dom_int pd)).
Proof.
  intros. generalize dependent srts. generalize dependent i.
  induction vars; simpl; intros.
  - inversion Hi.
  - destruct a0.
    + inversion Hlen.
    + simpl. destruct i.
      * (*i=0*) 
        destruct (vsymbol_eq_dec a a); try contradiction.
        destruct (vty_eq_dec (v_subst_aux (fun x0 : typevar => v_typevar vt x0) (snd a)) x); subst.
        -- unfold dom_cast.
          f_equal. f_equal. apply dec_uip_diff. apply sort_eq_dec.
        -- exfalso. apply n.
          specialize (Htys 0 ltac:(lia)).
          simpl in Htys. subst. reflexivity.
      * (*i <> 0*) inversion Hnodup; subst.
        destruct (vty_eq_dec
        (v_subst_aux (fun x0 : typevar => v_typevar vt x0) (snd (nth i vars vs_d))) x).
        -- destruct (vsymbol_eq_dec a (nth i vars vs_d)).
          ++ exfalso; subst. apply H1. apply nth_In; auto. simpl in Hi. lia.
          ++ erewrite IHvars; auto. f_equal. f_equal.
            apply dec_uip_diff. apply sort_eq_dec.
            Unshelve. apply Nat.succ_lt_mono; auto.
            intros.
            apply (Htys (S i0)); lia.
        -- erewrite IHvars; auto. f_equal. apply dec_uip_diff.
          apply sort_eq_dec. Unshelve.
          apply Nat.succ_lt_mono; auto.
          intros.
          apply (Htys (S i0)); lia.
Qed.

(*The other case is much easier*)
Lemma val_with_args_notin vv (vars: list vsymbol) (srts: list sort)
  (a: arg_list domain srts) (x : vsymbol)
  (Hnotinx: ~ In x vars):
  val_with_args vv vars a x = vv x.
Proof.
  generalize dependent srts. induction vars; simpl; intros; auto.
  destruct a0; auto.
  simpl in Hnotinx. not_or Hx.
  destruct (vty_eq_dec (v_subst_aux (fun x1 : typevar => v_typevar vt x1) (snd x)) x0).
  - destruct (vsymbol_eq_dec a x); subst; auto; contradiction.
  - apply IHvars; auto.
Qed.

Lemma fn_ret_cast_eq (f: fn) (Hinf: In f fs)
  (srts: list sort)
  (args: arg_list domain (funsym_sigma_args (fn_name f) srts))
  (Hlen: length srts = length params) (*TODO: see*)
  (Hvt_eq: vt_eq srts):
  val (s_ret (fn_name f)) = funsym_sigma_ret (fn_name f) srts.
Proof.
  unfold funsym_sigma_ret. rewrite params_eq; auto.
  apply v_ty_subst_eq; auto.
  - rewrite <- (params_eq _ Hinf); auto. apply s_params_Nodup.
  - eapply f_typevars. apply Hinf. left; auto.
Qed.

(*TODO: move, and see if we need m and vs in context
  Probably, so we know which m and vs we are recursing on,
    but where do we need this? TODO: see*)
Variable fs_dec: Forall (fun f => decrease_fun fs nil (*TODO*) nil 
  (nth (fn_idx f) (fn_args f) vs_d) m vs (fn_body f)) fs.

Lemma Forall_In {A: Type} {P: A -> Prop} {l: list A} {x: A}:
  Forall P l ->
  In x l ->
  P x.
Proof.
  induction l; simpl; intros; destruct H0; subst; inversion H; auto.
Qed.

(*Lift relation to dependent pairs*)
Definition R_projT1 {A : Type} (B: A -> Type) (R: A -> A -> Prop) :
  {x: A & B x} -> {x : A & B x} -> Prop :=
  fun x y => R (projT1 x) (projT1 y).

Lemma wf_projT1 {A : Type} {B: A -> Type} {R: A -> A -> Prop}
  (wf: well_founded R):
  well_founded (R_projT1 B R).
Proof.
  unfold R_projT1.
  assert (forall (z: {x : A & B x}),
    Acc R (projT1 z) ->
    Acc (fun (x : {x : A & B x}) (y : {x0 : A & B x0}) => 
      R (projT1 x) (projT1 y)) z).
  {
    intros. destruct z as [a b]. simpl in *.
    generalize dependent b.
    induction H.
    intros. constructor. intros.
    simpl in H1.
    destruct y as [y1 y2]. simpl in *.
    apply H0. auto.
  }
  unfold well_founded. intros.
  apply H. apply wf.
Qed. (*TODO: Defined?*)

Definition packed_args2 := {fa: packed_args &
(val_vars pd vt *
         (Datatypes.length (projT1 (projT2 fa)) = Datatypes.length params /\
          vt_eq (projT1 (projT2 fa))))%type}.

Definition pack_args (fa: packed_args) (v: val_vars pd vt)
  (Hsrts: length (projT1 (projT2 fa)) = length params /\
  vt_eq (projT1 (projT2 fa))) :
  packed_args2 :=
  existT _ fa (v, Hsrts). 

(*TODO: better way*)
(*Handle contradictions in term_rep_aux, only
  var case matters*)
Lemma const_not_var {c x}:
  Tconst c <> Tvar x.
Proof.
  intros. discriminate.
Qed.

Lemma fun_not_var {f l ts x}:
  Tfun f l ts <> Tvar x.
Proof.
  discriminate.
Qed.

Lemma tlet_not_var {t1 v t2 x}:
  Tlet t1 v t2 <> Tvar x.
Proof.
  discriminate.
Qed.

Lemma tif_not_var {f1 t2 t3 x}:
  Tif f1 t2 t3 <> Tvar x.
Proof.
  discriminate.
Qed.

Lemma tmatch_not_var {t1 v1 ps' x}:
  Tmatch t1 v1 ps' <> Tvar x.
Proof.
  discriminate.
Qed.

Lemma teps_not_var {f1 v x}:
  Teps f1 v <> Tvar x.
Proof.
  discriminate.
Qed.

(*Only interesting case*)
Lemma var_case ty x v Hty' Heq: (fun d : domain (val ty) =>
forall (x0 : vsymbol) (Heqx : Tvar x = Tvar x0),
d =
dom_cast (dom_aux pd)
  (f_equal (fun x : vty => val x)
     (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty')))) 
  (var_to_dom pd vt v x0))
 (dom_cast (dom_aux pd) (f_equal (fun x : vty => val x) (eq_sym Heq))
    (var_to_dom pd vt v x)).
Proof.
  simpl. intros. injection Heqx. intros; subst.
  simpl. f_equal. apply dec_uip_diff. apply sort_eq_dec.
Qed.

Lemma rewrite_dom_cast: forall (v1 v2: sort) (Heq: v1 = v2)
  x,
  scast (f_equal domain Heq) x = dom_cast (dom_aux pd) Heq x.
Proof.
  intros. reflexivity.
Qed.
Print decrease_fun.
(*Inversion lemmas for decreasing*)


(*If no funsym or predsym appears in t, *)
(*Lemma dec_fun_weaken: forall fs ps y t small x,
  (forall f, In f fs -> negb (funsym_in_tm (fn_name f) t)) ->
  (forall p, In p ps -> negb (predsym_in_term (pn_name p) t)) ->
  decrease_fun fs ps (remove vsymbol_eq_dec x small) y m vs t.
Proof.
  intros. a inversion H; subst.
  - apply Dec_notin_t; auto.
  - destruct (vsymbol_eq_dec x x0).
    + subst. apply Dec_fun_notin. apply Dec_fun_in with(f_decl:=f_decl)(x:=x0); auto.
*)
(*TODO: later wont need extra fs and ps*)
Lemma dec_inv_tlet {fs' ps' tm1 x tm2 small y}:
  decrease_fun fs' ps' small y m vs (Tlet tm1 x tm2) ->
  decrease_fun fs' ps' small y m vs tm1 /\
  decrease_fun fs' ps' (remove vsymbol_eq_dec x small) y m vs tm2.
Proof.
  intros. inversion H; subst.
  - (*No funsym case*)
    simpl in H0, H1.
    split; apply Dec_notin_t; intros.
    + apply H0 in H2. bool_hyps. rewrite H2; auto.
    + apply H1 in H2. bool_hyps. rewrite H2; auto.
    + apply H0 in H2. bool_hyps. rewrite H3; auto.
    + apply H1 in H2. bool_hyps. rewrite H3; auto.
  - split; auto.
Qed.

(*Case analysis for [tmatch]*)
Definition tmatch_case (tm: term) (hd: vsymbol) (small: list vsymbol) :
  Either {mvar: vsymbol | tm = Tvar mvar /\
    (mvar = hd \/ In mvar small)}
    (~ exists var, tm = Tvar var /\ (var = hd \/ In var small)).
Proof.
  destruct tm; try solve[apply Right; intros [var [Ht]]; inversion Ht].
  destruct (vsymbol_eq_dec v hd).
  - subst. apply Left. apply (exist _ hd).  split; auto.
  - destruct (in_dec vsymbol_eq_dec v small).
    + apply Left. apply (exist _ v). split; auto.
    + apply Right. intros [var [Ht [Hvar | Hinvar]]]; subst; 
      inversion Ht; subst; contradiction.
Qed.

(*Inversion lemmas for [tmatch]*)
Lemma dec_inv_tmatch_fst {fs' ps' tm small hd v pats}:
  decrease_fun fs' ps' small hd m vs (Tmatch tm v pats) ->
  decrease_fun fs' ps' small hd m vs tm.
Proof.
  intros. inversion H; subst.
  - simpl in H0, H1. apply Dec_notin_t; intros x Hinx;
    [apply H0 in Hinx | apply H1 in Hinx]; bool_hyps;
    rewrite H2; auto.
  - apply Dec_notin_t; simpl; auto.
  - auto.
Qed. 

Lemma dec_inv_tmatch_var {fs' ps' tm small hd mvar v pats}
  (Htm: tm = Tvar mvar /\ (mvar = hd \/ In mvar small)):
  decrease_fun fs' ps' small hd m vs (Tmatch tm v pats) ->
  Forall
  (fun x : pattern * term =>
   decrease_fun fs' ps'
     (union vsymbol_eq_dec
        (vsyms_in_m m vs (pat_constr_vars (fst x)))
        (remove_all vsymbol_eq_dec (pat_fv (fst x)) small))
     mvar m vs (snd x)) pats.
Proof.
  intros. inversion H; subst.
  - (*No funsym or predsym occurrence*)
    rewrite Forall_forall. intros.
    apply Dec_notin_t; intros y Hiny;
    [apply H0 in Hiny | apply H1 in Hiny];
    simpl in Hiny; bool_hyps;
    rewrite existsb_false in H4;
    rewrite Forall_forall in H4;
    rewrite H4; auto.
  - destruct Htm as [Ht _]. inversion Ht; subst. auto.
  - exfalso. apply H7. exists mvar. auto.
Qed.

Lemma dec_inv_tmatch_notvar {fs' ps' tm small hd v pats}
  (Htm: ~ exists var, tm = Tvar var /\ (var = hd \/ In var small)):
  decrease_fun fs' ps' small hd m vs (Tmatch tm v pats) ->
  Forall (fun x => decrease_fun fs' ps' 
    (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) hd m vs (snd x)) pats.
Proof.
  intros. inversion H; subst.
  - rewrite Forall_forall. intros.
    apply Dec_notin_t; intros y Hiny;
    [apply H0 in Hiny | apply H1 in Hiny];
    simpl in Hiny; bool_hyps;
    rewrite existsb_false in H4;
    rewrite Forall_forall in H4;
    rewrite H4; auto.
  - exfalso. apply Htm. exists mvar. auto.
  - auto.
Qed.


Lemma in_remove {A: Type} {P: A -> Prop} {l: list A} {x: A}
  {eq_dec: forall (x y: A), {x=y} +{x <> y}}:
  (forall x, In x l -> P x) ->
  (forall y, In y (remove eq_dec x l) -> P y).
Proof.
  intros. simpl_set. destruct H0. apply H; auto.
Qed.


(*Now we prove one of the key results: we call the
  function on smaller inputs, according to our well-founded
  relation. We do this in 2 parts*)

(*First, show it holds for any [arg_list] satisfying a property
  of its hnth elements which are variables.
  This does NOT use term_rep_aux*)
Lemma func_smaller_case_gen (v:val_vars pd vt) (input: packed_args2)  :
let fa:= projT1 input in
let f1:= proj1_sig (projT1 fa) in
let y:= nth (fn_idx f1) (fn_args f1) vs_d in 
let a1:= projT2 (projT2 fa) in
let Hsrts:= snd (projT2 input) in
let srts_len:= proj1' Hsrts in
let vt_eq_srts:= proj2' Hsrts in
let srts:= projT1 (projT2 fa) in
let d:= hide_ty
(dom_cast (dom_aux pd)
   (arg_nth_eq srts (fn_name f1) (fn_idx f1) (fn_idx_bound f1))
   (hnth (fn_idx f1) a1 s_int (dom_int pd))) in
forall (small: list vsymbol)
  (ty: vty) (f: funsym) (l: list vty) (ts: list term)
  (Hty': term_has_type sigma (Tfun f l ts) ty)
  (Hdec': decrease_fun fs [] small y m vs (Tfun f l ts))
  (x: {f' : fn | In f' fs /\ f = fn_name f'})
  (Hsmall: forall x : vsymbol,
    In x small -> adt_smaller_trans (hide_ty (v x)) d)
(args: arg_list domain
  (ty_subst_list_s 
    (s_params f)
    (map (fun x : vty => val x) l) (s_args f)))
(Hnth': forall (i: nat) vs_small,
  nth i ts tm_d = Tvar vs_small ->
  i < length ts ->
  exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
  Heq,
  hnth i args s_int (dom_int pd) =
dom_cast (dom_aux pd) Heq
  (dom_cast (dom_aux pd)
     (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
     (var_to_dom pd vt v vs_small))),

let Hinv:= fun_ty_inversion sigma f l ts ty Hty' in

let Hdec2:= dec_inv_tfun_rec Hdec' in
let Hall:= proj1' (proj2' (proj2' (proj2' (proj2' Hinv)))) in
let Hargslen:= proj1' (proj2' (proj2' Hinv)) in
let Hparamslen:= proj1' (proj2' (proj2' (proj2' Hinv))) in

let fn_def:= proj1_sig x in
let f_fn:= proj2' (proj2_sig x) in
let fn_in:= proj1' (proj2_sig x)  in
let l_eq:= proj1' (dec_inv_tfun_in Hdec' fn_in f_fn) in
let srts_eq:= eq_trans
(f_equal
   (fun x : funsym =>
    map (fun x0 : vty => val x0) (map vty_var (s_params x)))
   f_fn) (map_vals_srts' srts fn_def srts_len vt_eq_srts fn_in) in

let l_eq2:= eq_trans (eq_sym srts_eq)
(f_equal (fun x : list vty => map (fun x0 : vty => val x0) x)
   (eq_sym l_eq)) in
let args':= scast
           (f_equal
              (fun x : list sort => arg_list domain (funsym_sigma_args f x))
              (eq_sym l_eq2)) args in
let args'':= scast
(f_equal
   (fun x : funsym => arg_list domain (funsym_sigma_args x srts))
   f_fn) args' in
let ind_arg:= existT
(fun x : {f : fn | In f fs} =>
 {srts : list sort &
 arg_list domain
   (funsym_sigma_args (fn_name (proj1_sig x)) srts)})
(exist (fun f : fn => In f fs) fn_def fn_in)
(existT
   (fun srts : list sort =>
    arg_list domain
      (funsym_sigma_args
         (fn_name
            (proj1_sig
               (exist (fun f : fn => In f fs) fn_def fn_in)))
         srts)) srts args'') in
let ind_arg':= pack_args ind_arg v (conj srts_len vt_eq_srts) in
R_projT1
(fun fa0 : packed_args =>
 (val_vars pd vt *
  (Datatypes.length (projT1 (projT2 fa0)) = Datatypes.length params /\
   vt_eq (projT1 (projT2 fa0))))%type) arg_list_smaller ind_arg' input.
Proof.
  intros.
  unfold R_projT1.
  subst ind_arg' ind_arg args'' args' l_eq2 f_fn srts_eq l_eq d
    Hargslen Hparamslen Hall Hdec2 srts fa Hinv.
  unfold pack_args.
  simpl in *.
  
  destruct x as [x [i Hfeq]]; subst. 
  simpl.
  (*We avoid evars as much as possible to make the proof faster*)
  apply (AL_small 
    (*We need to give the 1st arg or else Coq has problems*)
    (existT
    (fun x0 : {f : fn | In f fs} =>
    {srts : list sort &
    arg_list domain (funsym_sigma_args (fn_name (proj1_sig x0)) srts)})
    (exist (fun f : fn => In f fs) fn_def fn_in)
    (existT
      (fun srts : list sort =>
        arg_list domain (funsym_sigma_args (fn_name fn_def) srts))
      (projT1 (projT2 (projT1 input)))
      (scast
          (f_equal
            (fun x0 : list sort => arg_list domain (funsym_sigma_args (fn_name x) x0))
            (eq_sym
                (eq_trans
                  (eq_sym
                      (eq_trans eq_refl
                        (map_vals_srts' (projT1 (projT2 (projT1 input))) fn_def
                            srts_len vt_eq_srts fn_in)))
                  (f_equal (fun x0 : list vty => map (fun x1 : vty => val x1) x0)
                      (eq_sym (proj1' (dec_inv_tfun_in Hdec' fn_in eq_refl)))))))
          args))) 
    _ _ _ (projT1 (projT2 (projT1 input))) 
    eq_refl eq_refl _ _ eq_refl eq_refl eq_refl eq_refl).
    simpl. rewrite eq_trans_refl.
    unfold cast_arg_list.
    rewrite scast_funsym_args_eq. simpl.
    rewrite hnth_cast_arg_list. 
    unfold cast_nth_eq.
    rewrite eq_trans_sym_distr, eq_sym_map_distr,
    !eq_sym_involutive, !eq_trans_map_distr, !f_equal_compose.
    generalize dependent  (dec_inv_tfun_in Hdec' i eq_refl).
    intros. destruct H as [Heq [Hall1 Hall2]]. subst. 
    generalize dependent (map_vals_srts' (projT1 (projT2 (projT1 input))) fn_def srts_len
    vt_eq_srts fn_in).
    intros.
    subst f1 y a1 srts_len vt_eq_srts.
    destruct input as [fa [v' [srts_len vt_eq_srts]]].
    simpl in *.
    destruct fa; destruct s; simpl in *. subst.
    simpl.
    (*Now we need to know about hnth of get_arg_list_ext, from
      our assumption*)
    assert (Hidx: fn_idx fn_def < Datatypes.length ts). {
      rewrite (proj1' (proj2' (proj2' (fun_ty_inversion sigma (fn_name x)
      (map vty_var (s_params (fn_name x))) ts ty Hty')))).
      apply fn_idx_bound.
    }
    subst fn_def.
    (*Now we know that (nth (fn_idx x) ts tm_d) is a var in small*)
    destruct (dec_inv_tfun_arg Hdec' i eq_refl) as [vs_small [Hinvs Hvar]].
    destruct (Hnth' (fn_idx x) vs_small Hvar Hidx) as [ty2 [Hty2 [Heq Hnth'']]].
    unfold funsym_sigma_args.
    rewrite Hnth''.
    unfold var_to_dom.
    rewrite rewrite_dom_cast.
    rewrite !dom_cast_compose.
    (*Now, this is just a casted version of the smaller assumption we
      have. So we can use [adt_smaller_trans_hide_cast]*)
    apply adt_smaller_trans_hide_cast. exact (Hsmall _ Hinvs).
Defined.

(*And the full result, a corollary of the above*)
Lemma func_smaller_case (v:val_vars pd vt) (input: packed_args2)  :
let fa:= projT1 input in
let f1:= proj1_sig (projT1 fa) in
let y:= nth (fn_idx f1) (fn_args f1) vs_d in 
let a1:= projT2 (projT2 fa) in
let Hsrts:= snd (projT2 input) in
let srts_len:= proj1' Hsrts in
let vt_eq_srts:= proj2' Hsrts in
let srts:= projT1 (projT2 fa) in
let d:= hide_ty
(dom_cast (dom_aux pd)
   (arg_nth_eq srts (fn_name f1) (fn_idx f1) (fn_idx_bound f1))
   (hnth (fn_idx f1) a1 s_int (dom_int pd))) in
forall (small: list vsymbol)
  (ty: vty) (f: funsym) (l: list vty) (ts: list term)
  (Hty': term_has_type sigma (Tfun f l ts) ty)
  (Hdec': decrease_fun fs [] small y m vs (Tfun f l ts))
  (x: {f' : fn | In f' fs /\ f = fn_name f'})
  (Hsmall: forall x : vsymbol,
    In x small -> adt_smaller_trans (hide_ty (v x)) d)
  (term_rep_aux: forall v (t : term) 
      (ty : vty) (small : list vsymbol)
      (Hty : term_has_type sigma t ty),
    decrease_fun fs [] small y m vs t ->
    (forall x : vsymbol,
    In x small -> adt_smaller_trans (hide_ty (v x)) d) ->
    {d : domain (val ty)
    | forall (x : vsymbol) (Heqx : t = Tvar x),
      d =
      dom_cast (dom_aux pd)
        (f_equal (fun x0 : vty => val x0)
          (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
        (var_to_dom pd vt v x)}),
let get_arg_list_ext_aux':= fix get_arg_list_ext_aux' (f: funsym)
{vs': list vty} {ts: list term} (*{ty: vty}*)
(Hparamslen: length vs' = length (s_params f))
{struct ts}:
forall args
(Hargslen: length ts = length args)
(Hall: Forall (fun x => term_has_type sigma (fst x) (snd x))
  (combine ts (map (ty_subst (s_params f) vs') args)))
(Hdec: Forall (fun t => decrease_fun fs nil small y m vs t) ts),
{a: arg_list domain (ty_subst_list_s (s_params f) 
  (map (fun x => val x) vs') args) |
  forall (j: nat) (Hj: j < length ts) vs_small,
  nth j ts tm_d = Tvar vs_small ->
  exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
      Heq,
  (*Avoids the need to relate hnth to term_rep_aux (nth) by
  directly giving the result we need*)
  hnth j a s_int (dom_int pd) =
  dom_cast (dom_aux pd) Heq
    (dom_cast (dom_aux pd)
      (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
      (var_to_dom pd vt v vs_small))} :=
match ts as ts'
return forall args,
length ts' = length args ->
Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
  (combine ts' (map (ty_subst (s_params f) vs') args)) ->
Forall (fun t : term => decrease_fun fs [] small y m vs t) ts' ->
{a: arg_list domain (ty_subst_list_s (s_params f) 
  (map (fun x => val x) vs') args) |
  forall (j: nat) (Hj: j < length ts') vs_small,
  nth j ts' tm_d = Tvar vs_small ->
  exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
      Heq,
  hnth j a s_int (dom_int pd) =
  dom_cast (dom_aux pd) Heq
    (dom_cast (dom_aux pd)
      (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
      (var_to_dom pd vt v vs_small))} 
with
| nil => fun args Hlen _ _ => 
    match args as a' return length nil = length a' -> 
    {a: arg_list domain (ty_subst_list_s (s_params f) 
      (map (fun x => val x) vs') a') |
      forall (j: nat) (Hj: j < length nil) vs_small,
      nth j nil tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} 
    with 
    (*Both get contradictions here*)
    | nil => fun Hlena => exist _ (@HL_nil _ _) 
      (fun j Hj => False_rect _ (Nat.nlt_0_r j Hj))
    | ahd :: atl => fun Heq => False_rect _ (Nat.neq_0_succ (length atl) Heq)
    end Hlen
| thd :: ttl => 
  fun args Hlen Htys Hdecs => 
  match args as a' return length (thd :: ttl) = length a' ->
    Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
      (combine (thd :: ttl) (map (ty_subst (s_params f) vs') a')) ->
    {a: arg_list domain (ty_subst_list_s (s_params f) 
      (map (fun x => val x) vs') a') |
      forall (j: nat) (Hj: j < length (thd :: ttl)) vs_small,
      nth j (thd :: ttl) tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} 
    with
    | nil => fun Hlen =>
      False_rect _ (Nat.neq_succ_0 (length ttl) Hlen)
    | ahd :: atl => fun Heq Htys =>
      exist _ (HL_cons _ _ _ (dom_cast (dom_aux pd)
      (funsym_subst_eq (s_params f) vs' (v_typevar vt) ahd
      (s_params_Nodup _) (eq_sym Hparamslen)) 
        (proj1_sig (term_rep_aux v _ _ _ (Forall_inv Htys) (Forall_inv Hdecs) Hsmall))) 
        (proj1_sig (get_arg_list_ext_aux'  f  Hparamslen atl 
          (Nat.succ_inj (length ttl) (length atl) Heq)
          (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) 
      (*build the function for second part*)
      (fun j => 
        match j as j' return j' < length (thd :: ttl) ->
          forall (vs_small: vsymbol),
          nth j' (thd :: ttl) tm_d = Tvar vs_small ->
          exists
            (ty' : vty) (Hty' : term_has_type sigma (Tvar vs_small) ty') 
          (Heq0 : val ty' =
                  nth j'
                    (ty_subst_list_s (s_params f) (map (fun x : vty => val x) vs') (ahd :: atl))
                    s_int),
            hnth j'
              (HL_cons domain (ty_subst_s (s_params f) (map (v_subst (v_typevar vt)) vs') ahd)
                (ty_subst_list_s (s_params f) (map (fun x : vty => val x) vs') atl)
                (dom_cast (dom_aux pd)
                    (funsym_subst_eq (s_params f) vs' (v_typevar vt) ahd 
                      (s_params_Nodup f) (eq_sym Hparamslen))
                    (proj1_sig
                      (term_rep_aux v (fst (thd, ty_subst (s_params f) vs' ahd))
                          (snd (thd, ty_subst (s_params f) vs' ahd)) small 
                          (Forall_inv Htys) (Forall_inv Hdecs) Hsmall)))
                (proj1_sig (get_arg_list_ext_aux' f  Hparamslen atl
                    (Nat.succ_inj (Datatypes.length ttl) (Datatypes.length atl) Heq)
                    (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) s_int 
              (dom_int pd) =
            dom_cast (dom_aux pd) Heq0
              (dom_cast (dom_aux pd)
                (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
                (var_to_dom pd vt v vs_small))
        with
        | 0 => 
          (*Case when j = 0*)
          fun _ vs_small Hthd => 
            arg_list_case_1 v y d f vs' small Hsmall (term_rep_aux v) Hparamslen thd ttl 
              Hdecs ahd atl Heq Htys vs_small Hthd
        | S j' => 
          (fun Hj vs_small Hnth =>
          (proj2_sig (get_arg_list_ext_aux' f Hparamslen atl 
          (Nat.succ_inj (length ttl) (length atl) Heq)
          (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)) j'
          (Arith_prebase.lt_S_n j' (length ttl) Hj) vs_small Hnth
          ) )
        end)
    end Hlen Htys
end in
let Hinv:= fun_ty_inversion sigma f l ts ty Hty' in


let Hdec2:= dec_inv_tfun_rec Hdec' in
let Hall:= proj1' (proj2' (proj2' (proj2' (proj2' Hinv)))) in
let Hargslen:= proj1' (proj2' (proj2' Hinv)) in
let Hparamslen:= proj1' (proj2' (proj2' (proj2' Hinv))) in
let args := proj1_sig (get_arg_list_ext_aux' f Hparamslen (s_args f) Hargslen
Hall Hdec2) in

let fn_def:= proj1_sig x in
let f_fn:= proj2' (proj2_sig x) in
let fn_in:= proj1' (proj2_sig x)  in
let l_eq:= proj1' (dec_inv_tfun_in Hdec' fn_in f_fn) in
let srts_eq:= eq_trans
(f_equal
   (fun x : funsym =>
    map (fun x0 : vty => val x0) (map vty_var (s_params x)))
   f_fn) (map_vals_srts' srts fn_def srts_len vt_eq_srts fn_in) in

let l_eq2:= eq_trans (eq_sym srts_eq)
(f_equal (fun x : list vty => map (fun x0 : vty => val x0) x)
   (eq_sym l_eq)) in
let args':= scast
           (f_equal
              (fun x : list sort => arg_list domain (funsym_sigma_args f x))
              (eq_sym l_eq2)) args in
let args'':= scast
(f_equal
   (fun x : funsym => arg_list domain (funsym_sigma_args x srts))
   f_fn) args' in
let ind_arg:= existT
(fun x : {f : fn | In f fs} =>
 {srts : list sort &
 arg_list domain
   (funsym_sigma_args (fn_name (proj1_sig x)) srts)})
(exist (fun f : fn => In f fs) fn_def fn_in)
(existT
   (fun srts : list sort =>
    arg_list domain
      (funsym_sigma_args
         (fn_name
            (proj1_sig
               (exist (fun f : fn => In f fs) fn_def fn_in)))
         srts)) srts args'') in
let ind_arg':= pack_args ind_arg v (conj srts_len vt_eq_srts) in
R_projT1
(fun fa0 : packed_args =>
 (val_vars pd vt *
  (Datatypes.length (projT1 (projT2 fa0)) = Datatypes.length params /\
   vt_eq (projT1 (projT2 fa0))))%type) arg_list_smaller ind_arg' input.
Proof.
  intros.
  apply func_smaller_case_gen with(ty:=ty)(Hty':=Hty').
  exact Hsmall.
  intros.
  apply (proj2_sig ((get_arg_list_ext_aux'0 f l ts Hparamslen (s_args f) Hargslen Hall Hdec2))).
  exact H0.
  exact H.
Defined.

Lemma small_remove_lemma_gen (v: val_vars pd vt) (x: vsymbol)  
  (t: domain (val (snd x))) (small: list vsymbol)
  {P: forall (ty: vty), domain (val ty) -> Prop}:
  (forall x, In x small -> P _ (v x)) ->
  (forall y, In y (remove vsymbol_eq_dec x small) -> 
    P _ (substi pd vt v x t y)).
Proof.
  intros. unfold substi. simpl_set. destruct H0.
  destruct (vsymbol_eq_dec y x); subst; auto; try contradiction.
Qed.

Lemma small_remove_lemma (v: val_vars pd vt) (x: vsymbol)
  (t: domain (val (snd x))) {small d} 
  (Hsmall: forall x, In x small -> adt_smaller_trans (hide_ty (v x)) d):
  forall y, In y (remove vsymbol_eq_dec x small) ->
  adt_smaller_trans (hide_ty (substi pd vt v x t y)) d.
Proof.
  intros.
  apply small_remove_lemma_gen with(small:=small)(P:=(fun ty y =>
    adt_smaller_trans (hide_ty y) d)); auto.
Qed.

(*Let's try to prove our match lemma*)
(*TODO: not quite: need to make sure the types match*)
Lemma match_val_single_smaller_aux (v: val_vars pd vt) (ty: vty)
  (Hval: valid_type sigma ty)
  (d: domain (val ty)):
  (forall (p: pattern) 
    (l: list (vsymbol * {t : vty & domain (val t)})),
    match_val_single gamma_valid pd all_unif vt ty Hval d p = Some l ->
    (forall y, In y (map snd l) ->
    (*Either y is the same as d or it is smaller*)
    y = hide_ty d \/
    adt_smaller_trans y (hide_ty d)) /\
    forall f tys ts, p = Pconstr f tys ts ->
    forall y, In y (map snd l) ->
    adt_smaller_trans y (hide_ty d)).
Proof.
(*TODO: Prove*)
Admitted.

(*Didn't need in Denotational, need now*)
Lemma ty_match_inv_pats
{s t ty1 ty2 xs} (H: term_has_type s (Tmatch t ty1 xs) ty2):
Forall (fun x => pattern_has_type s (fst x) ty1) xs.
Proof.
  inversion H; subst. rewrite Forall_forall. auto.
Qed.

(*First (recursive) case for small lemma when we add valuations
  from [match_val_single]*)
Lemma match_val_single_small1 { v ty1 Hval dom_t p l small d ty'}:
  pattern_has_type sigma p ty' ->
  match_val_single gamma_valid pd all_unif vt ty1 Hval dom_t p = Some l ->
  (forall x, In x small -> adt_smaller_trans (hide_ty (v x)) d) ->
  (forall x, In x (remove_all vsymbol_eq_dec (pat_fv p) small) ->
    adt_smaller_trans (hide_ty (extend_val_with_list pd vt v l x)) d).
Proof.
  intros. simpl_set. destruct H2.
  rewrite extend_val_with_list_notin'; auto.
  eapply match_val_single_free_var in H0. rewrite <- H0. auto.
  apply H.
Qed.
(*
forall x : vsymbol,
  In x (remove vsymbol_eq_dec v1 small) ->
  adt_smaller_trans
    (hide_ty
       (substi pd vt v v1
          (proj1_sig (term_rep_aux v tm1 (snd v1) small Ht1 Hdec1 Hsmall)) x)) d*)

(*Finally, start building the real function. We separate into
  pieces to avoid too many layers of nested recursion and to
  make things easier for Coq's termination checker*)

Section TermRepAux.

Variable (input: packed_args2)
(rec:(forall
  y : packed_args2,
  (R_projT1 _ arg_list_smaller) y input ->
  domain (funsym_sigma_ret (fn_name (proj1_sig (projT1 (projT1 y)))) 
    (projT1 (projT2 (projT1 y)))))).

Notation fa := (projT1 input).
Notation Hsrts := (snd (projT2 input)).
Notation f1 := (proj1_sig (projT1 fa)).
Notation a1 := (projT2 (projT2 fa)).
Notation srts := (projT1 (projT2 fa)).
Notation srts_len := (proj1' Hsrts).
Notation vt_eq_srts := (proj2' Hsrts).
(*d is the ADT instance we must be smaller than to recurse*)
Notation d := ((hide_ty (dom_cast _ 
(arg_nth_eq srts (fn_name f1) (fn_idx f1) (fn_idx_bound f1)) 
(hnth (fn_idx f1) a1 s_int (dom_int pd))))).
(*y is the vsymbol we must be syntactically decreasing on*)
Notation y := (nth (fn_idx f1) (fn_args f1) vs_d).

(*The body of [term_rep_aux]*)
Definition term_rep_aux_body 
(term_rep_aux: forall (v: val_vars pd vt) 
  (t: term) (ty: vty) (small: list vsymbol)
  (Hty: term_has_type sigma t ty)
  (Hdec: decrease_fun fs nil small y m vs t)
  (Hsmall: forall x, In x small ->
    (*TODO: type restriction here?*)
    adt_smaller_trans (hide_ty (v x)) d),
  {d: domain (val ty) | forall x (Heqx: t = Tvar x),
    d = dom_cast _ (f_equal (fun x => val x) 
      (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
      (var_to_dom _ vt v x)})
(v: val_vars pd vt)
(t: term)
(ty: vty)
(small: list vsymbol)
(Hty: term_has_type sigma t ty)
(Hdec: decrease_fun fs nil small y m vs t)
(Hsmall: forall x, In x small ->
  (*TODO: type restriction here?*)
  adt_smaller_trans (hide_ty (v x)) d):
{d: domain (val ty) | forall x (Heqx: t = Tvar x),
  d = dom_cast _ (f_equal (fun x => val x) 
    (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
    (var_to_dom _ vt v x)} :=
  match t as tm return forall (Hty': term_has_type sigma tm ty),
  decrease_fun fs nil small y m vs tm -> 
  {d: domain (val ty) | forall x (Heqx: tm = Tvar x),
  d = dom_cast _ (f_equal (fun x => val x) 
    (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty'))))
    (var_to_dom _ vt v x)} with
(*Some cases are identical to [term_rep]*)
| Tconst (ConstInt z) => fun Hty' _ =>
  let Htyeq : vty_int = ty :=
    eq_sym (ty_constint_inv Hty') in

  exist _ (cast_dom_vty pd Htyeq z)
    (fun x Heqx => False_rect _ (const_not_var Heqx)) 
| Tconst (ConstReal r) => fun Hty' _ =>
  let Htyeq : vty_real = ty :=
    eq_sym (ty_constreal_inv Hty') in

  exist _ (cast_dom_vty pd Htyeq r)
    (fun x Heqx => False_rect _ (const_not_var Heqx)) 
| Tvar x => fun Hty' _ =>
  let Heq : ty = snd x := ty_var_inv Hty' in
  (exist _ 
    (dom_cast _ (f_equal (fun x => val x) (eq_sym Heq)) 
    (var_to_dom _ vt v x)) (var_case ty x v Hty' Heq))
(*The function case is one of the 2 interesting cases*)
| Tfun f l ts => fun Hty' Hdec' =>

  (*Some proof we need; we give types for clarity*)
  let Htyeq : ty_subst (s_params f) l (s_ret f) = ty :=
    eq_sym (ty_fun_ind_ret Hty') in
  (*The main typecast: v(sigma(ty_ret)) = sigma'(ty_ret), where
    sigma sends (s_params f)_i -> l_i and 
    sigma' sends (s_params f) _i -> v(l_i)*)
  let Heqret : v_subst (v_typevar vt) (ty_subst (s_params f) l (s_ret f)) =
    ty_subst_s (s_params f) (map (v_subst (v_typevar vt)) l) (s_ret f) :=
      funsym_subst_eq (s_params f) l (v_typevar vt) (s_ret f) (s_params_Nodup f)
      (tfun_params_length Hty') in

  (*This is a horrible function, hopefully eventually
  I can take it out but I doubt it*)
  let fix get_arg_list_ext_aux' (f: funsym)
    {vs': list vty} {ts: list term}
    (Hparamslen: length vs' = length (s_params f))
    {struct ts}:
    forall args
    (Hargslen: length ts = length args)
    (Hall: Forall (fun x => term_has_type sigma (fst x) (snd x))
      (combine ts (map (ty_subst (s_params f) vs') args)))
    (Hdec: Forall (fun t => decrease_fun fs nil small y m vs t) ts),
    {a: arg_list domain (ty_subst_list_s (s_params f) 
      (map (fun x => val x) vs') args) |
      forall (j: nat) (Hj: j < length ts) vs_small,
      nth j ts tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      (*Avoids the need to relate hnth to term_rep_aux (nth) by
      directly giving the result we need*)
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} :=
  match ts as ts'
    return forall args,
    length ts' = length args ->
    Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
      (combine ts' (map (ty_subst (s_params f) vs') args)) ->
    Forall (fun t : term => decrease_fun fs [] small y m vs t) ts' ->
    {a: arg_list domain (ty_subst_list_s (s_params f) 
      (map (fun x => val x) vs') args) |
      forall (j: nat) (Hj: j < length ts') vs_small,
      nth j ts' tm_d = Tvar vs_small ->
      exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
          Heq,
      hnth j a s_int (dom_int pd) =
      dom_cast (dom_aux pd) Heq
        (dom_cast (dom_aux pd)
          (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
          (var_to_dom pd vt v vs_small))} 
    with
    | nil => fun args Hlen _ _ => 
        match args as a' return length nil = length a' -> 
        {a: arg_list domain (ty_subst_list_s (s_params f) 
          (map (fun x => val x) vs') a') |
          forall (j: nat) (Hj: j < length nil) vs_small,
          nth j nil tm_d = Tvar vs_small ->
          exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
              Heq,
          hnth j a s_int (dom_int pd) =
          dom_cast (dom_aux pd) Heq
            (dom_cast (dom_aux pd)
              (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
              (var_to_dom pd vt v vs_small))} 
        with 
        (*Both get contradictions here*)
        | nil => fun Hlena => exist _ (@HL_nil _ _) 
          (fun j Hj => False_rect _ (Nat.nlt_0_r j Hj))
        | ahd :: atl => fun Heq => False_rect _ (Nat.neq_0_succ (length atl) Heq)
        end Hlen
    | thd :: ttl => 
      fun args Hlen Htys Hdecs => 
      match args as a' return length (thd :: ttl) = length a' ->
        Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
          (combine (thd :: ttl) (map (ty_subst (s_params f) vs') a')) ->
        {a: arg_list domain (ty_subst_list_s (s_params f) 
          (map (fun x => val x) vs') a') |
          forall (j: nat) (Hj: j < length (thd :: ttl)) vs_small,
          nth j (thd :: ttl) tm_d = Tvar vs_small ->
          exists (ty': vty) (Hty': term_has_type sigma (Tvar vs_small) ty') 
              Heq,
          hnth j a s_int (dom_int pd) =
          dom_cast (dom_aux pd) Heq
            (dom_cast (dom_aux pd)
              (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
              (var_to_dom pd vt v vs_small))} 
        with
        | nil => fun Hlen =>
          False_rect _ (Nat.neq_succ_0 (length ttl) Hlen)
        | ahd :: atl => fun Heq Htys =>
          exist _ (HL_cons _ _ _ (dom_cast (dom_aux pd)
          (funsym_subst_eq (s_params f) vs' (v_typevar vt) ahd
          (s_params_Nodup _) (eq_sym Hparamslen)) 
            (proj1_sig (term_rep_aux v _ _ _ (Forall_inv Htys) (Forall_inv Hdecs) Hsmall))) 
            (proj1_sig (get_arg_list_ext_aux'  f  Hparamslen atl 
              (Nat.succ_inj (length ttl) (length atl) Heq)
              (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) 
          (*build the function for second part*)
          (fun j => 
            match j as j' return j' < length (thd :: ttl) ->
              forall (vs_small: vsymbol),
              nth j' (thd :: ttl) tm_d = Tvar vs_small ->
              exists
                (ty' : vty) (Hty' : term_has_type sigma (Tvar vs_small) ty') 
              (Heq0 : val ty' =
                      nth j'
                        (ty_subst_list_s (s_params f) (map (fun x : vty => val x) vs') (ahd :: atl))
                        s_int),
                hnth j'
                  (HL_cons domain (ty_subst_s (s_params f) (map (v_subst (v_typevar vt)) vs') ahd)
                    (ty_subst_list_s (s_params f) (map (fun x : vty => val x) vs') atl)
                    (dom_cast (dom_aux pd)
                        (funsym_subst_eq (s_params f) vs' (v_typevar vt) ahd 
                          (s_params_Nodup f) (eq_sym Hparamslen))
                        (proj1_sig
                          (term_rep_aux v (fst (thd, ty_subst (s_params f) vs' ahd))
                              (snd (thd, ty_subst (s_params f) vs' ahd)) small 
                              (Forall_inv Htys) (Forall_inv Hdecs) Hsmall)))
                    (proj1_sig (get_arg_list_ext_aux' f  Hparamslen atl
                        (Nat.succ_inj (Datatypes.length ttl) (Datatypes.length atl) Heq)
                        (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)))) s_int 
                  (dom_int pd) =
                dom_cast (dom_aux pd) Heq0
                  (dom_cast (dom_aux pd)
                    (f_equal (fun x0 : vty => val x0) (eq_sym (ty_var_inv Hty')))
                    (var_to_dom pd vt v vs_small))
            with
            | 0 => 
              (*Case when j = 0*)
              fun _ vs_small Hthd => 
                arg_list_case_1 v y d f vs' small Hsmall (term_rep_aux v) Hparamslen thd ttl 
                  Hdecs ahd atl Heq Htys vs_small Hthd
            | S j' => 
              (fun Hj vs_small Hnth =>
              (proj2_sig (get_arg_list_ext_aux' f Hparamslen atl 
              (Nat.succ_inj (length ttl) (length atl) Heq)
              (Forall_inv_tail Htys) (Forall_inv_tail Hdecs)) j'
              (Arith_prebase.lt_S_n j' (length ttl) Hj) vs_small Hnth
              ) )
            end)
        end Hlen Htys
    end in

  let Hinv := fun_ty_inversion _ _ _ _ _ Hty' in 
  let Hargslen := proj1' (proj2' (proj2' Hinv)) in
  let Hparamslen := proj1' (proj2' (proj2' (proj2' Hinv))) in
  let Hall := proj1' (proj2' (proj2' (proj2' (proj2' Hinv)))) in
  let Hdec2 := dec_inv_tfun_rec Hdec' in

  (*Get argument to apply recursively*)
  let args : arg_list domain (funsym_sigma_args f 
    (map (fun x => val x) l))  :=
    proj1_sig (get_arg_list_ext_aux' f Hparamslen (s_args f) Hargslen
    Hall Hdec2) in

  (*If f is in fs, then we need to make a recursive call*)
  match (find_fn f fs) with
  | Left x =>
    let fn_def : fn := proj1_sig x in
    let fn_in: In fn_def fs := proj1' (proj2_sig x) in
    let f_fn : f = fn_name fn_def := proj2' (proj2_sig x) in

    let l_eq : l = map vty_var (s_params f) :=
      proj1' (dec_inv_tfun_in Hdec' fn_in f_fn) in

    (*With l_eq, we can begin casting*)
    let srts_eq : map (fun x => val x) (map vty_var (s_params f)) =
      srts :=
      eq_trans (f_equal (fun x => map (fun x => val x) (map vty_var (s_params x)))
        f_fn)
        (map_vals_srts' srts fn_def srts_len vt_eq_srts fn_in) in

    let l_eq2: srts = map (fun x => val x) l :=
      eq_trans (eq_sym srts_eq) 
        (f_equal (fun x => map (fun x => val x) x) (eq_sym l_eq)) in

    let args': arg_list domain (funsym_sigma_args f srts) 
      :=
      scast (f_equal (fun x => arg_list domain (funsym_sigma_args f x)) 
        (eq_sym l_eq2)) args in
    let args'' : arg_list domain (funsym_sigma_args (fn_name fn_def) srts) :=
      scast (f_equal (fun x => arg_list domain (funsym_sigma_args x srts))
        f_fn) args' in

    let ind_arg : packed_args
    
    := existT _ (exist _ fn_def fn_in) (existT _ srts args'') in
    let ind_arg' : packed_args2 :=
      pack_args ind_arg v (conj srts_len vt_eq_srts) in
    (*TODO: it is v, right? Because rec changes val*)
    (*Here is our recursive call. We have to cast the result*)
    let ret_val : 
      domain
        (funsym_sigma_ret (fn_name (proj1_sig (projT1 (projT1 ind_arg'))))
        (projT1 (projT2 (projT1 ind_arg')))) :=
      (rec ind_arg' 
        (*Proof of smaller*)
        (func_smaller_case v input small ty f l ts Hty' Hdec' x Hsmall
          term_rep_aux)) in

    (*Now we have to cast in the reverse direction*)
    (*First, get in terms of f*)
    let ret1 : domain (funsym_sigma_ret f srts) :=
      dom_cast (dom_aux pd) 
        (f_equal (fun x => funsym_sigma_ret x srts) (eq_sym f_fn)) ret_val in

    let ret2 : 
      domain (ty_subst_s (s_params f) 
        (map (v_subst (v_typevar vt)) l) (s_ret f)) :=
      dom_cast (dom_aux pd) 
        (f_equal (fun x => ty_subst_s (s_params f) x (s_ret f))
        l_eq2) ret1 in

        exist _ (cast_dom_vty pd Htyeq 
          (dom_cast (dom_aux pd) (eq_sym Heqret) ret2)) (
            fun x Heqx => False_rect _ (fun_not_var Heqx)
          )

  | Right Hnotin =>
    (*Otherwise, use funs*)

  (* The final result is to apply [funs] to the [arg_list] created recursively
    from the argument domain values. We need two casts to make the dependent
    types work out*)

  (exist _ (cast_dom_vty pd Htyeq (
    dom_cast (dom_aux pd)
      (eq_sym Heqret)
        ((funs gamma_valid pd pf f 
          (map (fun x => val x) l)) args))) 
          (fun x Heqx => False_rect _ (fun_not_var Heqx)))
  end

(*Tlet is pretty simple. We need a lemma to show that we mantain
  the Hsmall invariant (holds because substi replaces the variable
  that we substitute in)
  We also have an awkward exist (proj1_sig _) H, because the inductive
  proof is not quite right, though both are trivial*)
| Tlet tm1 v1 tm2 => fun Hty' Hdec' =>
    let Ht1 : term_has_type sigma tm1 (snd v1) :=
      proj1 (ty_let_inv Hty') in
    let Ht2 : term_has_type sigma tm2 ty :=
      proj2 (ty_let_inv Hty') in 
    let Hdec1 : decrease_fun fs nil small y m vs tm1 := 
      proj1 (dec_inv_tlet Hdec') in
    let Hdec2 : decrease_fun fs nil (remove vsymbol_eq_dec v1 small) y m vs tm2 := 
      proj2 (dec_inv_tlet Hdec') in

    exist _ (proj1_sig (term_rep_aux (substi pd vt v v1 
      (proj1_sig (term_rep_aux v tm1 (snd v1) small Ht1 Hdec1 Hsmall))) 
    tm2 ty (remove vsymbol_eq_dec v1 small) Ht2 Hdec2 
    (small_remove_lemma v v1 (proj1_sig (term_rep_aux v tm1 (snd v1) small Ht1 Hdec1 Hsmall)) 
      Hsmall))) (fun x Heqx => False_rect _ (tlet_not_var Heqx))
  (*fun _ _ => match domain_ne pd (val ty) with
  | DE x =>  exist _ x (fun x Heqx => False_rect _ (tlet_not_var Heqx))
  end *)
(*TODO: after, don't want mutual recursion yet*)
| Tif f1 t2 t3 =>
  fun _ _ => match domain_ne pd (val ty) with
  | DE x =>  exist _ x (fun x Heqx => False_rect _ (tif_not_var Heqx))
  end 
| Tmatch t ty1 ps => fun Hty' Hdec' =>
    let Ht1 : term_has_type sigma t ty1 :=
      proj1 (ty_match_inv Hty') in
    let Hall : Forall (fun x => term_has_type sigma (snd x) ty) ps :=
      proj2 (ty_match_inv Hty') in
    let Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) ps :=
      ty_match_inv_pats Hty' in

    let Hdec1 : decrease_fun fs [] small y m vs t := 
      dec_inv_tmatch_fst Hdec' in

    let Hval : valid_type sigma ty1 :=
      has_type_valid gamma_valid _ _ Ht1 in

    let dom_t := proj1_sig (term_rep_aux v t ty1 small Ht1 Hdec1 Hsmall) in

    (*hmm, we have 2 different cases: we might need to have 2
    different inner recursive functions, 1 for each case*)
    match tmatch_case t y small with
    | Left z =>
      let mvar : vsymbol := proj1_sig z in
      let tm_eq : t = Tvar mvar := proj1' (proj2_sig z) in
      let mvar_small : mvar = y \/ In mvar small :=
        proj2' (proj2_sig z) in

        match domain_ne pd (val ty) with
        | DE x =>  exist _ x (fun x Heqx => False_rect _ (tmatch_not_var Heqx))
        end

      (*TODO: do this, first do easy case*)

    | Right Hnotvar =>
      (*Easier, recursive case*)
      let Hdec2 : 
        Forall (fun x => decrease_fun fs nil 
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
          y m vs (snd x)) ps :=
        dec_inv_tmatch_notvar Hnotvar Hdec' in


      (*Can't make [match_rep] a separate function or else Coq
      cannot tell structurally decreasing. So we inline it*)
      let fix match_rep (ps: list (pattern * term)) 
        (Hall: Forall (fun x => term_has_type sigma (snd x) ty) ps)
        (Hpats: Forall (fun x => pattern_has_type sigma (fst x) ty1) ps)
        (Hdec: Forall (fun x => decrease_fun fs nil 
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
          y m vs (snd x)) ps) :
        domain (val ty) :=
      match ps as l' return 
        Forall (fun x => term_has_type sigma (snd x) ty) l' ->
        Forall (fun x => pattern_has_type sigma (fst x) ty1) l' ->
        Forall (fun x => decrease_fun fs nil 
          (remove_all vsymbol_eq_dec (pat_fv (fst x)) small) 
          y m vs (snd x)) l' ->
        domain (val ty) with
      | (p , dat) :: ptl => fun Hall Hpats Hdec =>
        (*We need info about [match_val_single] to know how the
          valuation changes*)
        match (match_val_single gamma_valid pd all_unif vt ty1 Hval dom_t p) as o
          return (match_val_single gamma_valid pd all_unif vt ty1 Hval dom_t p) = o ->
          domain (val ty) with
        | Some l => fun Hmatch => 
          proj1_sig (term_rep_aux (extend_val_with_list pd vt v l) dat ty
          _ (Forall_inv Hall) (Forall_inv Hdec) 
          (match_val_single_small1 (Forall_inv Hpats) Hmatch Hsmall))
        | None => fun _ => match_rep ptl (Forall_inv_tail Hall)
          (Forall_inv_tail Hpats) (Forall_inv_tail Hdec)
        end eq_refl
      | _ => (*TODO: show we cannot reach this*) fun _ _ _ =>
        match domain_ne pd (val ty) with
        | DE x => x
        end
      end Hall Hpats Hdec in
      (*For some reason, Coq needs the typing annotation here*)
      exist (fun d => forall x Heqx, d = 
      dom_cast (dom_aux pd)
      (f_equal (fun x0 : vty => val x0)
         (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty')))) 
      (var_to_dom pd vt v x)) (match_rep ps Hall Hpats Hdec2)
        (fun x Heqx => False_rect _ (tmatch_not_var Heqx))
    end

  (*fun _ _ => match domain_ne pd (val ty) with
  | DE x =>  exist _ x (fun x Heqx => False_rect _ (tmatch_not_var Heqx))
  end *)
| Teps f1 v =>
  fun _ _ => match domain_ne pd (val ty) with
  | DE x =>  exist _ x (fun x Heqx => False_rect _ (teps_not_var Heqx))
  end 
end Hty Hdec.

(*We give the Fixpoint. Coq does not accept this
  without the horrible inlined function and proofs above*)
Fixpoint term_rep_aux
(v: val_vars pd vt)
(t: term)
(ty: vty)
(small: list vsymbol)
(Hty: term_has_type sigma t ty)
(Hdec: decrease_fun fs nil small y m vs t)
(Hsmall: forall x, In x small ->
  (*TODO: type restriction here?*)
  adt_smaller_trans (hide_ty (v x)) d)
  {struct t}:
{d: domain (val ty) | forall x (Heqx: t = Tvar x),
  d = dom_cast _ (f_equal (fun x => val x) 
    (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
    (var_to_dom _ vt v x)}  :=
term_rep_aux_body term_rep_aux v t ty small Hty Hdec Hsmall.

End TermRepAux.

(*The body of the outer function - calls [term_rep_aux]
  with appropriate arguments*)
Definition funcs_rep_aux_body (input: packed_args2)
(rec:(forall
  y : packed_args2,
  (R_projT1 _ arg_list_smaller) y input ->
  domain (funsym_sigma_ret (fn_name (proj1_sig (projT1 (projT1 y)))) 
    (projT1 (projT2 (projT1 y))))) ):
  domain (funsym_sigma_ret (fn_name (proj1_sig (projT1 (projT1 input))))
   (projT1 (projT2 (projT1 input)))) :=
  let fa := projT1 input in
  let v := fst (projT2 input) in
  let Hsrts := snd (projT2 input) in
  let f1 := proj1_sig (projT1 fa) in
  let a1 := projT2 (projT2 fa) in
  let srts := projT1 (projT2 fa) in
  let srts_len := proj1' Hsrts in
  let vt_eq_srts := proj2' Hsrts in

  (*d is the ADT instance we must be smaller than to recurse*)
  let d := (hide_ty (dom_cast _ 
    (arg_nth_eq srts (fn_name f1) (fn_idx f1) (fn_idx_bound f1)) 
    (hnth (fn_idx f1) a1 s_int (dom_int pd)))) in
  (*y is the vsymbol we must be syntactically decreasing on*)
  let y := nth (fn_idx f1) (fn_args f1) vs_d in
  
  dom_cast _ (fn_ret_cast_eq _ (proj2_sig (projT1 fa)) srts a1
      (proj1' Hsrts) (proj2' Hsrts)) 
      (proj1_sig (term_rep_aux input rec
        (val_with_args v (fn_args f1) a1) (fn_body f1) 
          (s_ret (fn_name (proj1_sig (projT1 fa))))  nil
        (*proofs we need for [term_rep_aux]*)
        (Forall_In fs_typed (proj2_sig (projT1 fa)))
        (Forall_In fs_dec (proj2_sig (projT1 fa)))
        (fun x Hx => match Hx with end) )).

(*Define final function with Fix*)
Definition funcs_rep_aux (fa: packed_args)
(v: val_vars pd vt)
(Hsrts: length (projT1 (projT2 fa)) = length params /\
  vt_eq (projT1 (projT2 fa))) :
  domain (funsym_sigma_ret (fn_name (proj1_sig (projT1 fa))) (projT1 (projT2 fa))).
assert (Hwf: well_founded
(fun
   x
    y : {fa0 : packed_args &
        (val_vars pd vt *
         (Datatypes.length (projT1 (projT2 fa0)) = Datatypes.length params /\
          vt_eq (projT1 (projT2 fa0))))%type} =>
 arg_list_smaller (projT1 x) (projT1 y))). {
  exact (wf_projT1 arg_list_smaller_wf).
}
pose proof (@Fix packed_args2
(R_projT1 _ arg_list_smaller) Hwf
(fun input => domain (funsym_sigma_ret (fn_name (proj1_sig (projT1 (projT1 input))))
(projT1 (projT2 (projT1 input)))) )
funcs_rep_aux_body).
specialize (X (pack_args fa v Hsrts)).
simpl in X. apply X.
Defined.

(*We have it!*)

(*old Equations version - TODO: could use this for
  rewriting, etc
  BUT might be worse performance because have 3 layers
  nested together*)
(*Uses old [get_arg_list_aux]*)
(*
Equations funcs_rep_aux 
  (*The function symbol and arg list*)
  (fa: packed_args)
  (v: val_vars pd vt)
  (Hsrts: length (projT1 (projT2 fa)) = length params /\
    vt_eq (projT1 (projT2 fa))) :
  domain (funsym_sigma_ret (fn_name (proj1_sig (projT1 fa))) (projT1 (projT2 fa))) 
  by wf fa arg_list_smaller :=
  funcs_rep_aux fa v Hsrts := 
  let f1 := proj1_sig (projT1 fa) in
  let a1 := projT2 (projT2 fa) in
  let srts := projT1 (projT2 fa) in
  let srts_len := proj1' Hsrts in
  let vt_eq_srts := proj2' Hsrts in

  (*d is the ADT instance we must be smaller than to recurse*)
  let d := (hide_ty (dom_cast _ 
    (arg_nth_eq srts (fn_name f1) (fn_idx f1) (fn_idx_bound f1)) 
    (hnth (fn_idx f1) a1 s_int (dom_int pd)))) in
  (*y is the vsymbol we must be syntactically decreasing on*)
  let y := nth (fn_idx f1) (fn_args f1) vs_d in
  (*We need to know/obtain m and vs such that *)
  
    let fix term_rep_aux (v: val_vars pd vt) 
      (t: term) (ty: vty) (small: list vsymbol)
      (Hty: term_has_type sigma t ty)
      (Hdec: decrease_fun fs nil small y m vs t)
      (*All variables in small list correspond to
        values in the valuation which are actually smaller than d*)
      (Hsmall: forall x, In x small ->
        (*TODO: type restriction here?*)
        adt_smaller_trans (hide_ty (v x)) d)
        {struct t} :
      (*We need to know that we give [var_to_dom] on a variable
        for the termination proof*)
      {d: domain (val ty) | forall x (Heqx: t = Tvar x),
        d = dom_cast _ (f_equal (fun x => val x) 
          (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty))))
          (var_to_dom _ vt v x)} :=
      match t as tm return forall (Hty': term_has_type sigma tm ty),
        decrease_fun fs nil small y m vs tm -> 
        {d: domain (val ty) | forall x (Heqx: tm = Tvar x),
        d = dom_cast _ (f_equal (fun x => val x) 
          (eq_sym (ty_var_inv (term_has_type_cast Heqx Hty'))))
          (var_to_dom _ vt v x)} with
      (*Some cases are identical to [term_rep]*)
      | Tconst (ConstInt z) => fun Hty' _ =>
        let Htyeq : vty_int = ty :=
          eq_sym (ty_constint_inv Hty') in
    
        exist _ (cast_dom_vty pd Htyeq z) _ 
      | Tvar x => fun Hty' _ =>
        let Heq : ty = snd x := ty_var_inv Hty' in
        (exist _ 
          (dom_cast _ (f_equal (fun x => val x) (eq_sym Heq)) 
          (var_to_dom _ vt v x)) _)
      (*The function case is one of the 2 interesting cases*)
      | Tfun f l ts => fun Hty' Hdec' =>

        (*Some proof we need; we give types for clarity*)
        let Htyeq : ty_subst (s_params f) l (s_ret f) = ty :=
          eq_sym (ty_fun_ind_ret Hty') in
        (*The main typecast: v(sigma(ty_ret)) = sigma'(ty_ret), where
          sigma sends (s_params f)_i -> l_i and 
          sigma' sends (s_params f) _i -> v(l_i)*)
        let Heqret : v_subst (v_typevar vt) (ty_subst (s_params f) l (s_ret f)) =
          ty_subst_s (s_params f) (map (v_subst (v_typevar vt)) l) (s_ret f) :=
            funsym_subst_eq (s_params f) l (v_typevar vt) (s_ret f) (s_params_Nodup f)
            (tfun_params_length Hty') in

        (*We need to inline definition of [get_arg_list_ext]
          here (TODO: is there any way to do this so Coq will
          accept it?)*)
        let fix get_arg_list_ext_aux (*{d}*) (f: funsym)
        {vs': list vty} {ts: list term} (*{ty: vty}*)
        (Hparamslen: length vs' = length (s_params f))
        {struct ts}:
        forall args
        (Hargslen: length ts = length args)
        (Hall: Forall (fun x => term_has_type sigma (fst x) (snd x))
          (combine ts (map (ty_subst (s_params f) vs') args)))
        (*(Hty': ty = ty_subst (s_params f) vs' (s_ret f))*)
        (Hdec: Forall (fun t => decrease_fun fs nil small y m vs t) ts),
        arg_list domain (ty_subst_list_s (s_params f) 
          (map (fun x => val x) vs') args)
         :=
        match ts as ts' return forall args,
          length ts' = length args ->
          Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
            (combine ts' (map (ty_subst (s_params f) vs') args)) ->
          Forall (fun t : term => decrease_fun fs [] small y m vs t) ts' ->
          arg_list domain (ty_subst_list_s (s_params f) 
            (map (fun x : vty => val x) vs') args) with
        | nil => 
          fun args Hlen _ _ =>
            match args as a' return length nil = length a' -> 
            arg_list domain (ty_subst_list_s (s_params f) 
              (map (fun x : vty => val x) vs') a')
            with 
            | nil => fun _ => (@HL_nil _ _)
            | ahd :: atl => fun Heq => False_rect _ (Nat.neq_0_succ (length atl) Heq)
            end Hlen
        | thd :: ttl => 
            fun args Hlen Htys Hdecs =>
            match args as a' return length (thd :: ttl) = length a' ->
              Forall (fun x : term * vty => term_has_type sigma (fst x) (snd x))
                (combine (thd :: ttl) (map (ty_subst (s_params f) vs') a')) ->
              arg_list domain (ty_subst_list_s (s_params f) 
                (map (fun x : vty => val x) vs') a')
            with
            | nil => fun Heq _ => False_rect _ (Nat.neq_succ_0 (length ttl) Heq)
            | ahd :: atl => fun Heq Htys =>
              HL_cons _ _ _ (dom_cast (dom_aux pd)
              (funsym_subst_eq (s_params f) vs' (v_typevar vt) ahd
               (s_params_Nodup _) (eq_sym Hparamslen)) 
                (proj1_sig (term_rep_aux v thd 
                  (ty_subst (s_params f) vs' ahd) small (Forall_inv Htys) (Forall_inv Hdecs) Hsmall))) 
                (get_arg_list_ext_aux f Hparamslen atl 
                  (Nat.succ_inj (length ttl) (length atl) Heq)
                  (Forall_inv_tail Htys) (Forall_inv_tail Hdecs))
            end Hlen Htys
        end in

        let Hinv := fun_ty_inversion _ _ _ _ _ Hty' in 
        let Hargslen := proj1 (proj2 (proj2 Hinv)) in
        let Hparamslen := proj1 (proj2 (proj2 (proj2 Hinv))) in
        let Hall := proj1 (proj2 (proj2 (proj2 (proj2 Hinv)))) in
        let Hdec2 := dec_inv_tfun_rec Hdec' in

        (*Get argument to apply recursively*)
        let args : arg_list domain (funsym_sigma_args f 
          (map (fun x => val x) l))  :=
          get_arg_list_ext_aux f Hparamslen (s_args f) Hargslen
          Hall Hdec2 in


        (*If f is in fs, then we need to make a recursive call*)
        match (find_fn f fs) with
        | Left x =>
          let fn_def : fn := proj1_sig x in
          let fn_in: In fn_def fs := proj1' (proj2_sig x) in
          let f_fn : f = fn_name fn_def := proj2' (proj2_sig x) in

          let l_eq : l = map vty_var (s_params f) :=
            proj1' (dec_inv_tfun_in Hdec' fn_in f_fn) in

          (*With l_eq, we can begin casting*)
          let srts_eq : map (fun x => val x) (map vty_var (s_params f)) =
            srts :=
            eq_trans (f_equal (fun x => map (fun x => val x) (map vty_var (s_params x)))
              f_fn)
              (map_vals_srts' srts fn_def srts_len vt_eq_srts fn_in) in
            (*need eq trans*)
            (*f_equal (fun x => map (fun x => val x) (map vty_var (s_params x))
              fn_def
              map_vals_srts' fn_def fn_in in*)

          let l_eq2: srts = map (fun x => val x) l :=
            eq_trans (eq_sym srts_eq) 
              (f_equal (fun x => map (fun x => val x) x) (eq_sym l_eq)) in
            (*eq_trans (eq_sym (map_vals_srts' fn_def fn_in))
              (f_equal (fun x => map (fun y => val y) x)
                (eq_sym l_eq)) in*)
          (*(eq_trans (f_equal _ l_eq) (map_vals_srts' fn_def fn_in)) in*)

          let args': arg_list domain (funsym_sigma_args f srts) 
            :=
            scast (f_equal (fun x => arg_list domain (funsym_sigma_args f x)) 
              (eq_sym l_eq2)) args in
          let args'' : arg_list domain (funsym_sigma_args (fn_name fn_def) srts) :=
            scast (f_equal (fun x => arg_list domain (funsym_sigma_args x srts))
              f_fn) args' in

          let ind_arg : packed_args
          
          := existT _ (exist _ fn_def fn_in) (existT _ srts args'') in
          (*TODO: not v*)
          (*Here is our recursive call. We have to cast the result*)
          let ret_val : domain (funsym_sigma_ret (fn_name fn_def) srts) :=
            (funcs_rep_aux ind_arg v (conj srts_len vt_eq_srts)) in
          (*Now we have to cast in the reverse direction*)
          (*First, get in terms of f*)
          let ret1 : domain (funsym_sigma_ret f srts) :=
            dom_cast (dom_aux pd) 
              (f_equal (fun x => funsym_sigma_ret x srts) (eq_sym f_fn)) ret_val in

          let ret2 : 
            domain (ty_subst_s (s_params f) 
              (map (v_subst (v_typevar vt)) l) (s_ret f)) :=
            dom_cast (dom_aux pd) 
              (f_equal (fun x => ty_subst_s (s_params f) x (s_ret f))
              l_eq2) ret1 in

              exist _ (cast_dom_vty pd Htyeq 
                (dom_cast (dom_aux pd) (eq_sym Heqret) ret2)) _
          
(*Definition funsym_sigma_ret (f: funsym) (s: list Types.sort) : Types.sort :=
  ty_subst_s (s_params f) s (s_ret f).*)


        | Right Hnotin =>
          (*Otherwise, use funs*)

        (* The final result is to apply [funs] to the [arg_list] created recursively
          from the argument domain values. We need two casts to make the dependent
          types work out*)
      
        (exist _ (cast_dom_vty pd Htyeq (
          dom_cast (dom_aux pd)
            (eq_sym Heqret)
              ((funs gamma_valid pd pf f 
                (map (fun x => val x) l)) args))) _)
        end

      (*TODO: placeholder*)
      | _ => fun _ _ => match domain_ne pd (val ty) with
                        | DE x =>  exist _ x _
                        end
      end Hty Hdec
    in
    dom_cast _ (fn_ret_cast_eq _ (proj2_sig (projT1 fa)) srts a1
      (proj1' Hsrts) (proj2' Hsrts)) (proj1_sig (term_rep_aux 
      (val_with_args v (fn_args f1) a1) (fn_body f1) 
        (s_ret (fn_name (proj1_sig (projT1 fa))))  nil
    (*TODO*) (Forall_In fs_typed (proj2_sig (projT1 fa)))
      (Forall_In fs_dec (proj2_sig (projT1 fa)))
      (fun x Hx => match Hx with end) )).
Next Obligation.
simpl; intros. injection Heqx. intros; subst.
(*First, show var case - TODO: maybe add in, see*)
unfold term_has_type_cast.
f_equal. f_equal. apply dec_uip_diff. apply vty_eq_dec.
Defined.
Next Obligation.
Tactics.program_simplify. simpl.
(*try after removing admitted*)
(*Remove the inlined nested fix*)
(*ok let's try this*)

apply func_decreasing'.
Defined.
Print term.
(*
Next Obligation.
destruct fa as [[f Hinf] [srts args]].
simpl in *.
destruct Hsrts as [Hlen Hty].
apply fn_ret_cast_eq; assumption.
Defined.
Next Obligation.
destruct fa as [[f Hinf] [srts args]].
simpl in *.
rewrite Forall_forall in fs_typed.
apply fs_typed. assumption.
Defined.
Next Obligation.
destruct fa as [[f Hinf] [srts args]].
simpl in *.
rewrite Forall_forall in fs_dec.
apply fs_dec.
assumption.
Defined.
Next Obligation.
destruct H.
Defined.
*)*)
End FunDef.
