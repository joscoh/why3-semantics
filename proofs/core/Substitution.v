Require Import Common.
Require Import Syntax.
Require Import Semantics.
Require Import Types.
Require Import Typing.
Require Import Denotational.

(*Here we define a function to rename bound variables to unique
  values such that terms and formulas have no duplicate bound
  variables and no clashes between free and bound variable names.
  This makes many transformations easier.*)

(*First, some functions we need*)

Definition split {A: Type} (l: list A) (i: nat) : (list A * list A) :=
  (firstn i l, skipn i l).

(*Split a list into pieces of the appropriate lengths if we can*)
Fixpoint split_lens {A: Type} (l: list A) (lens: list nat) :
  list (list A) :=
  match lens with
  | len :: tl =>
    (fst (split l len)) ::
    split_lens (snd (split l len)) tl
  | nil => nil
  end.

Definition sum (l: list nat) : nat :=
  fold_right (fun x y => x + y) 0 l.

Lemma length_concat {A: Type} (l: list (list A)):
  length (concat l) = sum (map (@length A) l).
Proof.
  induction l; simpl; auto.
  rewrite app_length, IHl; auto.
Qed.

Lemma split_lens_length {A: Type} (l: list A) (lens: list nat) :
  length (split_lens l lens) = length lens.
Proof.
  revert l.
  induction lens; simpl; intros; auto.
Qed.

Lemma split_lens_concat {A: Type} (l: list A) (lens: list nat) :
  sum lens = length l ->
  l = concat (split_lens l lens).
Proof.
  revert l. induction lens; simpl; intros; auto.
  destruct l; auto; inversion H.
  rewrite <- IHlens.
  rewrite firstn_skipn; auto.
  rewrite skipn_length, <- H.
  rewrite minus_plus; auto.
Qed.

Lemma split_lens_nodup {A: Type} (l: list A) (lens: list nat) :
  sum lens = length l ->
  NoDup l ->
  forall (i: nat) (d: list A),
    i < length lens ->
    NoDup (nth i (split_lens l lens) d).
Proof.
  revert l. induction lens; simpl; intros; auto; try lia.
  destruct i.
  - apply NoDup_firstn; assumption.
  - apply IHlens; try lia.
    + rewrite skipn_length, <- H.
      rewrite minus_plus; auto.
    + apply NoDup_skipn; assumption.
Qed. 

Lemma split_lens_ith {A: Type} (l: list A) (lens: list nat) (i: nat) :
  sum lens = length l ->
  i < length lens ->
  length (nth i (split_lens l lens) nil) = nth i lens 0.
Proof.
  revert l i. induction lens; simpl; intros; auto; try lia.
  destruct i.
  - rewrite firstn_length.
    apply Nat.min_l. lia.
  - specialize (IHlens (skipn a l) i).
    rewrite IHlens; auto; try lia.
    rewrite skipn_length, <- H.
    rewrite minus_plus; auto.
Qed.

Lemma in_split_lens_ith {A: Type} (l: list A) (lens: list nat) (i: nat) x (d: list A) :
  sum lens = length l ->
  i < length lens ->
  In x (nth i (split_lens l lens) d) ->
  In x l.
Proof.
  revert l i. induction lens; simpl; intros; auto; destruct i; auto; try lia.
  - apply In_firstn in H1; auto.
  - apply IHlens in H1; try lia.
    + apply In_skipn in H1; auto.
    + rewrite skipn_length, <- H. lia.
Qed.

Section Sub.
Context {sigma: sig} {gamma: context} (gamma_valid: valid_context sigma gamma).


(*Alpha substitute for patterns only in the given term/formula*)
(*Here, we need to keep the dependencies between pattern variables
  (as, for instance, an "or" pattern should have the same free
  vars on each side, so we use an association list)*)
  Fixpoint alpha_p_aux {A: Type} (sub: vsymbol -> vsymbol -> A -> A) 
  (p: pattern) (x: A) (l: list (vsymbol * string)) : (pattern * A) :=
  match p with
  | Pvar v => 
    match (get_assoc_list vsymbol_eq_dec l v) with
    | Some str => 
      let v' := (str, snd v) in
      (Pvar v', sub v v' x)
    | None => (p, x)
    end
  | Pwild => (p, x)
  | Por p1 p2 =>
    (*NOTE: must have same free vars*)
    let t1 := alpha_p_aux sub p1 x l in
    let t2 := alpha_p_aux sub p2 x l in
    (Por (fst t1) (fst t2), (snd t2))
  | Pbind p1 v =>
    match (get_assoc_list vsymbol_eq_dec l v) with
    | Some str =>
      let v' := (str, snd v) in
      let t := (alpha_p_aux sub p1 x l) in
      (Pbind (fst t) v', sub v v' (snd t))
    | None => (p, x)
    end
  | Pconstr f tys pats =>
    let t := 
    ((fix alpha_ps_aux (l1: list pattern) (y: A) : list pattern * A :=
      match l1 with
      | ph :: pt =>
        let t1 := alpha_p_aux sub ph y l in
        let t2 := alpha_ps_aux pt (snd t1) in
        ((fst t1) :: (fst t2), (snd t2))
      | nil => (nil, y)
      end) pats x) in
    (Pconstr f tys (fst t), (snd t))
    end.
(*Proving this correct will not be too fun, but let's see*)

Fixpoint alpha_t_aux (t: term) (l: list string) {struct t} : term :=
  (*We only care about the bound variable and inductive cases*)
  match t with
  | Tlet t1 x t2 => 
    match l with
    | str :: tl =>
      let (l1, l2) := split tl (length (bnd_t t1)) in 
      Tlet (alpha_t_aux t1 l1) (str, snd x) (sub_t x (str, snd x) 
      (alpha_t_aux t2 l2))
    | _ => t
    end
  | Tfun fs tys tms =>
    (*Split up the list into pieces of appropriate lengths 
      (size (bnd_t tm))*)
    let lens := map (fun tm => length (bnd_t tm)) tms in
    let l_split := split_lens l lens in
    Tfun fs tys (map2 (fun (tm: term) (l': list string) =>
    alpha_t_aux tm l') tms l_split)
  | Tif f t1 t2 =>
    let f_sz := length (bnd_f f) in
    let t1_sz := length (bnd_t t1) in
    let (l1, lrest) := split l f_sz in
    let (l2, l3) := split lrest t1_sz in
    Tif (alpha_f_aux f l1) 
      (alpha_t_aux t1 l2)
      (alpha_t_aux t2 l3)
  | Tmatch t1 ty ps =>
    (*First do the pattern substitutions, then do the terms
      recursively*)
    let lens := map (fun x => length (pat_fv (fst x)) + 
      length (bnd_t (snd x))) ps in
    let t1_sz := length (bnd_t t1) in
    let (l1, l2) := split l (t1_sz) in
    let l_split := split_lens l2 lens in
    
    Tmatch (alpha_t_aux t1 l1) ty
      (map2 (fun (x: pattern * term) (strs: list string) =>
        let p_sz := length (pat_fv (fst x)) in
        let (l1, l2) := split strs p_sz in
        let t2 := alpha_t_aux (snd x) l2 in
        alpha_p_aux sub_t (fst x) t2  (combine (pat_fv (fst x)) l1)
        ) ps l_split)
  | Teps f v =>
    match l with
    | nil => t
    | str :: tl =>
      let v' := (str, snd v) in
      Teps (sub_f v v' (alpha_f_aux f tl)) v'
    end
  | _ => t (*no other bound variables/recursive cases*)
  end
with alpha_f_aux (f: formula) (l: list string) {struct f} : formula :=
  match f with
  | Fpred ps tys tms =>
    (*Split up the list into pieces of appropriate lengths 
      (size (bnd_t tm))*)
    let lens := map (fun tm => length (bnd_t tm)) tms in
    let l_split := split_lens l lens in
    Fpred ps tys (map2 (fun (t: term) (l': list string) =>
      alpha_t_aux t l') tms l_split)
  | Fquant q v f1 =>
      match l with
      | str :: tl =>
        let v' := (str, snd v) in
        Fquant q v' (sub_f v v' (alpha_f_aux f1 tl))
      | _ => f
      end
  | Feq ty t1 t2 =>
    let t_sz := length (bnd_t t1) in
    let (l1, l2) := split l t_sz in
    Feq ty (alpha_t_aux t1 l1)
      (alpha_t_aux t2 l2)
  | Fbinop b f1 f2 =>
    let f_sz := length (bnd_f f1) in
    let (l1, l2) := split l f_sz in
    Fbinop b (alpha_f_aux f1 l1)
      (alpha_f_aux f2 l2)
  | Fnot f1 =>
    Fnot (alpha_f_aux f1 l)
  | Flet t v f1 =>
    match l with
    | str :: tl =>
      let (l1, l2) := split tl (length (bnd_t t)) in 
      Flet (alpha_t_aux t l1) (str, snd v) (sub_f v (str, snd v) 
      (alpha_f_aux f1 l2))
    | _ => f
    end
  | Fif f1 f2 f3 =>
    let f1_sz := length (bnd_f f1) in
    let f2_sz := length (bnd_f f2) in
    let (l1, lrest) := split l f1_sz in
    let (l2, l3) := split lrest f2_sz in
    Fif (alpha_f_aux f1 l1) 
      (alpha_f_aux f2 l2)
      (alpha_f_aux f3 l3)
  | Fmatch t1 ty ps =>
    (*First do the pattern substitutions, then do the terms
      recursively*)
    let lens := map (fun x => length (pat_fv (fst x)) + 
    length (bnd_f (snd x))) ps in
    let t1_sz := length (bnd_t t1) in
    let (l1, l2) := split l t1_sz in
    let l_split := split_lens l2 lens in
    
    Fmatch (alpha_t_aux t1 l1) ty
      (map2 (fun (x: pattern * formula) (strs: list string) =>
        let p_sz := length (pat_fv (fst x)) in
        let (l1, l2) := split strs p_sz in
        let f2 := alpha_f_aux (snd x) l2 in
        alpha_p_aux sub_f (fst x) f2  (combine (pat_fv (fst x)) l1)
        ) ps l_split)
  | _ => f (*No other bound/recursive cases*)
  end.
(*Prove correctness: 3 lemmas
  1. results in wf term/fmla
  2. preserves interp
  3. has same "shape" (and corollaries: ind form, positive, etc)*)


Lemma NoDup_pat_fv (p: pattern) : NoDup (pat_fv p).
Proof.
  induction p; simpl; try constructor; auto.
  - constructor.
  - apply big_union_nodup.
  - apply union_nodup; auto.
  - apply union_nodup; auto. constructor; auto. constructor.
Qed.

(*TODO: see if we need*)
Lemma alpha_p_aux_wf_aux_gen {A: Type} (p: pattern) 
  (sub: vsymbol -> vsymbol -> A -> A) :
  (forall (l: list (vsymbol * string)),
    (*NoDup (map snd l) ->*)
    (forall v, In v (pat_fv p) -> In v (map fst l)) ->
    (*NoDup (map fst l) ->*)
    (forall x v, In v (pat_fv (fst (alpha_p_aux sub p x l))) ->
      exists v', In (v', (fst v)) l /\
        In v' (pat_fv p))).
Proof.
  intros l (*Hnodups*) Hfvs (*Hnodupf*).
  induction p; simpl; auto; intros.
  - destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha.
    + simpl in H. destruct H as [Heq | []]; subst; simpl.
      apply get_assoc_list_some in Ha.
      exists v. auto.
    + apply get_assoc_list_none in Ha. simpl in H.
      destruct H as [Heq | []]; subst.
      exfalso. apply Ha. apply (Hfvs v0); auto. simpl; auto.
  - generalize dependent x. induction ps; simpl in *; auto; intros. 
    destruct H0.
    inversion H; subst.
    rewrite union_elts in H0. destruct H0.
    + assert (Hv: exists v', In (v', fst v) l /\ In v' (pat_fv a)). {
        apply H3 with(x:=x); auto. intros. apply Hfvs.
        rewrite union_elts. left; auto.
      }
      destruct Hv as [v' [Hinl Hinv']].
      exists v'. split; auto. rewrite union_elts. left; auto.
    + assert (Hv: exists v' : vsymbol,
        In (v', fst v) l /\ In v' (big_union vsymbol_eq_dec pat_fv ps)). {
        apply IHps with (x:=(snd (alpha_p_aux sub a x l))); auto.
        intros. apply Hfvs. rewrite union_elts. right; auto.
      }
      destruct Hv as [v' [Hinl Hinv']]; subst.
      exists v'. split; auto. rewrite union_elts. right; auto.
  - destruct H.
  - rewrite union_elts in H.
    destruct H.
    + assert (Hv: exists v' : vsymbol, In (v', fst v) l /\ In v' (pat_fv p1)). {
        apply IHp1 with(x:=x); auto. intros. apply Hfvs; simpl;
        rewrite union_elts; left; auto.
      }
      destruct Hv as [v' [Hinl Hinv']].
      exists v'. split; auto. rewrite union_elts. left; auto.
    + assert (Hv: exists v' : vsymbol, In (v', fst v) l /\ In v' (pat_fv p2)). {
        apply IHp2 with(x:=x); auto.
        intros; apply Hfvs; simpl; rewrite union_elts; right; auto.
      } destruct Hv as [v' [Hinl Hinv']]; subst.
      exists v'. split; auto. rewrite union_elts; right; auto. 
  - destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha.
    + simpl in H. rewrite union_elts in H.
      destruct H as [Hinv | [Heq | []]]; subst.
      * apply IHp with(x:=x) in Hinv.
        destruct Hinv as [v' [Hl Hv']].
        exists v'; split; auto. rewrite union_elts; left; auto.
        intros. apply Hfvs; simpl; rewrite union_elts; left; auto.
      * apply get_assoc_list_some in Ha.
        exists v. split; auto. rewrite union_elts; right; auto.
        left; auto.
    + simpl in H. apply get_assoc_list_none in Ha.
      exfalso. apply Ha. apply Hfvs. simpl. auto.
      rewrite union_elts. right; left; auto.
Qed. 

(*Other direction*)
Lemma alpha_p_aux_wf_aux_gen' {A: Type} (p: pattern) 
  (sub: vsymbol -> vsymbol -> A -> A) :
  (forall (l: list (vsymbol * string)),
    NoDup (map fst l) ->
    (forall v, In v (pat_fv p) -> In v (map fst l)) ->
    (forall x d, 
      In x (pat_fv (fst (alpha_p_aux sub p d l))) <->
      exists v str, 
        In (v, str) l /\
        In v (pat_fv p) /\
        snd x = snd v /\
        fst x = str)).
Proof.
  intros l Hnodup Hfvs (*Hnodupf*).
  induction p; simpl; auto; intros.
  - destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha; simpl; split; intros.
    + destruct H as [Heq | []]; subst; simpl.
      apply get_assoc_list_some in Ha.
      exists v. exists s. split; auto.
    + destruct H as [v1 [str [Hinl [[Heq | []] [Hsnd Hfst]]]]]; subst.
      left. destruct x; simpl in *; subst.
      f_equal. symmetry.
      apply get_assoc_list_some in Ha. 
      apply (nodup_fst_inj Hnodup Hinl Ha).
    + apply get_assoc_list_none in Ha.
      destruct H as [Heq | []]; subst.
      exfalso. apply Ha. apply Hfvs. left; auto.
    + apply get_assoc_list_none in Ha.
      destruct H as [v1 [str [Hinl [[Heq | []] [Hsnd Hfst]]]]]; subst.
      exfalso. apply Ha. rewrite in_map_iff. exists (v1, fst x); auto.
  - generalize dependent d. induction ps; simpl in *; auto; intros; 
    [split; simpl; intros; auto |].
    + destruct H0.
    + destruct H0 as [v1 [str [Hinl [[] _]]]].
    + assert (Hfvs': (forall v : vsymbol,
      In v (big_union vsymbol_eq_dec pat_fv ps) -> In v (map fst l))).
      {
        intros; apply Hfvs; simpl; rewrite union_elts; right; auto.
      } inversion H; subst. split; simpl; intros; auto.  
      rewrite union_elts in H0. inversion H; subst.
      destruct H0.
      * apply H2 in H0; auto.
        destruct H0 as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst.
        exists v1. exists (fst x). split_all; auto.
        rewrite union_elts; left; auto.
        intros. apply Hfvs. rewrite union_elts. left; auto.
      * specialize (IHps H3 Hfvs' (snd (alpha_p_aux sub a d l))).
        apply IHps in H0; clear IHps.
        destruct H0 as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst.
        exists v1. exists (fst x). split_all; auto.
        rewrite union_elts. right; auto.
      * destruct H0 as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst.
        rewrite union_elts in Hinv.
        rewrite union_elts.
        destruct Hinv as [Hinv1 | Hinv1]; [left | right].
        -- apply H2; auto. intros; apply Hfvs; simpl; rewrite union_elts;
          left; auto.
          exists v1. exists (fst x). auto.
        -- apply IHps; auto.
          exists v1. exists (fst x). auto.
  - split; intros; auto. destruct H. 
    destruct H as [_ [_ [_ [[] _]]]].
  - rewrite union_elts. split; intros.
    + destruct H; [apply IHp1 in H | apply IHp2 in H];
      try (intros; apply Hfvs; simpl; rewrite union_elts;
        try(solve[left; auto]); right; auto);
      destruct H as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst;
      exists v1; exists (fst x); split_all; auto;
      rewrite union_elts; [left | right]; auto.
    + destruct H as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst.
      rewrite union_elts in Hinv. destruct Hinv; 
      [left; apply IHp1 | right; apply IHp2]; try (intros; apply Hfvs;
      simpl; rewrite union_elts; try(solve[left; auto]); right; auto);
      exists v1; exists (fst x); split_all; auto.
  - destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha; simpl;
    rewrite union_elts; [split; intros|].
    + destruct H as [Hinx | [Heq | []]]; subst.
      * apply IHp in Hinx.
        destruct Hinx as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst.
        exists v1. exists (fst x). split_all; auto.
        rewrite union_elts; left; auto.
        intros; apply Hfvs; simpl; rewrite union_elts; left; auto.
      * apply get_assoc_list_some in Ha.
        exists v. exists s. split_all; auto. rewrite union_elts.
        right; left;auto.
    + destruct H as [v1 [str [Hinl [Hinv [Hsnd Hfst]]]]]; subst.
      rewrite union_elts in Hinv. destruct Hinv as [Hinv | [Heq | []]]; subst;
      [left | right; left]; auto.
      * apply IHp. intros. apply Hfvs; simpl; rewrite union_elts; left; auto.
        exists v1. exists (fst x). split_all; auto.
      * apply get_assoc_list_some in Ha.
        destruct x; simpl in *; subst. f_equal.
        apply (nodup_fst_inj Hnodup Ha Hinl).
    + apply get_assoc_list_none in Ha.
      exfalso. apply Ha. apply Hfvs. simpl. rewrite union_elts; right; left;
      auto.
Qed.

Lemma alpha_p_aux_wf_aux {A: Type} (p: pattern) 
  (sub: vsymbol -> vsymbol -> A -> A) :
  (forall (l: list (vsymbol * string)),
    NoDup (map fst l) ->
    (forall v, In v (pat_fv p) -> In v (map fst l)) ->
    (forall x v, In v (pat_fv (fst (alpha_p_aux sub p x l))) ->
      In (fst v) (map snd l))).
Proof.
  intros. pose proof (alpha_p_aux_wf_aux_gen' p sub l H H0 v x).
  apply H2 in H1. destruct H1 as [v1 [str [Hinl [Hinv1 [Hsnd Hfst]]]]]; subst.
  rewrite in_map_iff. exists (v1, fst v). split; auto.
Qed.

(*Second: need to know that [alpha_p_aux] does not change any bound
  variables in t/f*)

Lemma alpha_p_aux_bnd_t_eq  (p: pattern) (t: term) (l: list (vsymbol * string)) :
  bnd_t (snd (alpha_p_aux sub_t p t l)) =
  bnd_t t.
Proof.
  revert t.
  induction p; simpl; intros; auto.
  - destruct (get_assoc_list vsymbol_eq_dec l v); simpl; auto.
    rewrite bnd_sub_t; auto.
  - generalize dependent t. induction ps; simpl; intros; auto. 
    inversion H; subst.
    rewrite IHps; auto.
  - destruct (get_assoc_list vsymbol_eq_dec l v); simpl; auto.
    rewrite bnd_sub_t; auto.
Qed.

Lemma alpha_p_aux_bnd_f_eq (p: pattern) (f: formula) (l: list (vsymbol * string)) :
  bnd_f (snd (alpha_p_aux sub_f p f l)) =
  bnd_f f.
Proof.
  revert f.
  induction p; simpl; intros; auto.
  - destruct (get_assoc_list vsymbol_eq_dec l v); simpl; auto.
    rewrite bnd_sub_f; auto.
  - generalize dependent f0. induction ps; simpl; intros; auto. 
    inversion H; subst.
    rewrite IHps; auto.
  - destruct (get_assoc_list vsymbol_eq_dec l v); simpl; auto.
    rewrite bnd_sub_f; auto.
Qed.

(*TODO: add to this*)
(*Solve trivial/repeated goals and simplify*)
Ltac len_tac :=
repeat match goal with
| |- context [length (firstn ?n ?l)] => rewrite firstn_length
| |- context [length (skipn ?n ?l)] => rewrite skipn_length
| H: length ?l = ?x |- context [length ?l] => rewrite H
| |- context [length (?x ++ ?y)] => rewrite app_length
end; try lia.

Ltac wf_tac :=
  repeat(
  assumption +
  solve[len_tac] +
  solve[lia] +
  match goal with
  | |- context [map snd (combine ?l1 ?l2)] =>
    rewrite map_snd_combine
  | |- context [map fst (combine ?l1 ?l2)] =>
    rewrite map_fst_combine
  | |- NoDup (firstn ?n ?l) => apply NoDup_firstn
  | |- NoDup (skipn ?n ?l) => apply NoDup_skipn
  | |- NoDup (nth ?i (split_lens ?a ?b) ?d) =>
    apply split_lens_nodup
  | |- context [length (map ?f ?x)] => rewrite map_length
  | |- context [length (split_lens ?l1 ?l2)] =>
    rewrite split_lens_length
  | |- context [length (firstn ?n ?l)] => rewrite firstn_length
  | |- context [length (skipn ?n ?l)] => rewrite skipn_length
  | |- In (nth ?i ?l ?x) ?l =>
    apply nth_In
  | |- context [length (nth ?l (split_lens ?a ?b) ?d)] =>
    rewrite split_lens_ith
  | |- context [length (map2 ?f ?l1 ?l2)] =>
    rewrite map2_length
  | |- ?i < length ?l -> ?P => intros
  | |- context [Nat.min ?x ?x] =>
    rewrite Nat.min_id
  (*TODO: this is hacky*)
  | |- context [nth ?i (map ?f ?l) ?d] =>
    (rewrite map_nth_inbound with(d2:=tm_d)) ||
    (rewrite map_nth_inbound with (d2:=(Pwild, tm_d))) ||
    (rewrite map_nth_inbound with (d2:=(Pwild, Ftrue)))
  (*Deal with some "In" goals - TODO improve*)
  | H: In ?x (firstn ?n ?l) |- In ?x ?l => apply In_firstn in H
  | H: In ?x (skipn ?n ?l) |- In ?x ?l => apply In_skipn in H
  (*A special case*)
  | |- NoDup (pat_fv ?p) => apply NoDup_pat_fv
  | |- context [concat (split_lens ?l1 ?l2)] =>
    rewrite <- split_lens_concat
  | |- In ?x (map ?g ?l) => rewrite in_map_iff
  | |- exists y, ?f y = ?f ?x /\ ?P => exists x; split
  (*Solve the sum length goal*)
  | H: length ?l = length (concat (map ?f ?l1)) |-
    sum (map ?g ?l1) = length ?l => rewrite length_concat in H;
    rewrite H; f_equal; rewrite map_map; apply map_ext
  | H: length (?x :: ?l) = ?n |- _ => simpl in H
  | H: ?x = length (?l1 ++ ?l2) |- _ => rewrite app_length in H
  end); auto; try lia. 

Lemma alpha_aux_wf_aux (t: term) (f: formula) :
  (forall (l: list string),
    NoDup l ->
    length l = length (bnd_t t) ->
    NoDup (bnd_t (alpha_t_aux t l)) /\
    (forall x, In x (bnd_t (alpha_t_aux t l)) -> In (fst x) l)) /\
  (forall (l: list string),
    NoDup l ->
    length l = length (bnd_f f) ->
    NoDup (bnd_f (alpha_f_aux f l)) /\
    (forall x, In x (bnd_f (alpha_f_aux f l)) -> In (fst x) l)).
Proof.
  revert t f.
  apply term_formula_ind; simpl; intros; auto.
  - split; [constructor | intros x []]. 
  - split; [constructor | intros x []].
  - (*Tfun case*) 
    split.
    + rewrite NoDup_concat_iff. split.
      * intros x. rewrite in_map_iff.
        intros [t1 [Hbndt1 Hint1]]. subst.
        rewrite in_map2_iff with(d1:=tm_d)(d2:=nil) in Hint1;
        wf_tac.
        destruct Hint1 as [i [Hi Ht1]]; subst.
        rewrite Forall_forall in H.
        apply H; simpl; wf_tac.
      * intros i1 i2 d x. wf_tac.
        intros [Hin1 Hin2].
        (*Idea: suppose in both, then by IH (twice), in 2 different
          parts of l - contradicts NoDup l*)
        rewrite Forall_forall in H.
        rewrite (map2_nth _ _ _ tm_d nil) in Hin1, Hin2; wf_tac.
        apply H in Hin1, Hin2; auto; wf_tac.
        assert (NoDup (concat (split_lens l0 (map (fun t => length (bnd_t t)) l1)))) by
          (rewrite <- split_lens_concat; wf_tac).
          rewrite NoDup_concat_iff in H5.
        split_all. apply (H6 i1 i2 nil (fst x)); wf_tac.
    + intros x. rewrite in_concat. intros [bl [Hinbl Hinx]].
      rewrite in_map_iff in Hinbl.
      destruct Hinbl as [t1 [Ht1 Hint1]]; subst.
      rewrite (in_map2_iff _ _ _ tm_d nil) in Hint1; wf_tac.
      destruct Hint1 as [i [Hi Ht1]]; subst.
      rewrite Forall_forall in H.
      apply H in Hinx; auto; wf_tac.
      rewrite (split_lens_concat l0 (map (fun t => length (bnd_t t)) l1));
      [|wf_tac]. rewrite in_concat. eexists. split; [| apply Hinx]. wf_tac.
  - (*Tlet case*)
    destruct l; inversion H2; simpl.
    inversion H1; subst.
    split.
    + constructor.
      * (*TODO: automate the "In" part*) 
        intro Hin.
        apply in_app_or in Hin.
        destruct Hin.
        -- apply H in H3; wf_tac.
          apply In_firstn in H3. contradiction.
        -- rewrite bnd_sub_t in H3.
          apply H0 in H3; wf_tac. apply In_skipn in H3.
          contradiction.
      * rewrite NoDup_app_iff'.
        split_all.
        -- apply H; wf_tac.
        -- rewrite bnd_sub_t. apply H0; wf_tac.
        -- intros x.
          rewrite bnd_sub_t.
          intros [Hinx1 Hinx2].
          apply H in Hinx1; wf_tac.
          apply H0 in Hinx2; wf_tac.
          apply (nodup_firstn_skipn Hinx1 Hinx2); auto.
    + intros x [Hx | Hinx]; subst;[left; auto|].
      apply in_app_or in Hinx.
      destruct Hinx as [Hinx | Hinx].
      * apply H in Hinx; wf_tac.
        right. apply In_firstn in Hinx; auto.
      * rewrite bnd_sub_t in Hinx. apply H0 in Hinx; wf_tac.
        right. apply In_skipn in Hinx; auto.
  - (*Tif case*)
    split.
    + rewrite !NoDup_app_iff'.
      split_all.
      * apply H; wf_tac.
      * apply H0; wf_tac.
      * apply H1; wf_tac.
      * intros x [Hinx1 Hinx2].
        apply H0 in Hinx1; wf_tac.
        apply H1 in Hinx2; wf_tac.
        apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac. 
      * intros x [Hinx1 Hinx2].
        apply H in Hinx1; wf_tac.
        apply in_app_or in Hinx2. destruct Hinx2.
        -- apply H0 in H4; wf_tac.
          apply (nodup_firstn_skipn Hinx1); wf_tac. 
        -- apply H1 in H4; wf_tac.
          apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x Hinx.
      repeat (apply in_app_or in Hinx; destruct Hinx as [Hinx | Hinx]).
      * apply H in Hinx; wf_tac.
      * apply H0 in Hinx; wf_tac. apply In_firstn in Hinx.
        apply In_skipn in Hinx; auto.
      * apply H1 in Hinx; wf_tac. apply In_skipn in Hinx.
        apply In_skipn in Hinx; auto.
  - (*Tmatch case*)
    assert (Hsum: sum (map
        (fun x : pattern * term =>
        Datatypes.length (pat_fv (fst x)) + Datatypes.length (bnd_t (snd x)))
        ps) = Datatypes.length (skipn (Datatypes.length (bnd_t tm)) l)). {
          wf_tac. rewrite H2,length_concat, 
        map_map, minus_plus. f_equal. apply map_ext_in_iff; intros.
        rewrite app_length; auto.
    }
    split.
    + rewrite NoDup_app_iff'; split_all.
      * apply H; wf_tac.
      * rewrite NoDup_concat_iff; split_all.
        -- intros x. rewrite in_map_iff.
          intros [pt1 [Hx Hinx]]; subst.
          rewrite (in_map2_iff _ _ _ (Pwild, tm_d) nil) in Hinx; wf_tac.
          destruct Hinx as [i [Hi Hpt1]].
          rewrite NoDup_app_iff'.
          split_all; subst; wf_tac.
          ++ rewrite alpha_p_aux_bnd_t_eq.
            rewrite Forall_forall in H0.
            apply H0; auto; wf_tac.
          ++ intros x.
            rewrite alpha_p_aux_bnd_t_eq.
            intros [Hinx1 Hinx2].
            (*Need this a lot even though it's ugly*)
            apply alpha_p_aux_wf_aux in Hinx1; wf_tac.
            rewrite map_snd_combine in Hinx1; wf_tac.
            rewrite Forall_forall in H0.
            apply H0 in Hinx2; wf_tac.
            apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
        -- intros i1 i2 d x. wf_tac.
          rewrite !map2_nth with(d1:=(Pwild, tm_d)) (d2:=nil); wf_tac.
          intros [Hini1 Hini2].
          apply in_app_or in Hini1, Hini2.
          (*Now we get 4 cases need to show each is impossible*)
          destruct Hini1 as [Hini1 | Hini1].
          ++ apply alpha_p_aux_wf_aux in Hini1; wf_tac.
            revert Hini1. wf_tac. intros Hini1.
            apply In_firstn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** apply alpha_p_aux_wf_aux in Hini2; wf_tac.
              revert Hini2. wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** rewrite alpha_p_aux_bnd_t_eq in Hini2.
              rewrite Forall_forall in H0.
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
          ++ rewrite alpha_p_aux_bnd_t_eq in Hini1.
            rewrite Forall_forall in H0.
            apply H0 in Hini1; wf_tac.
            apply In_skipn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** apply alpha_p_aux_wf_aux in Hini2; wf_tac.
              revert Hini2; wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** rewrite alpha_p_aux_bnd_t_eq in Hini2.
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
      * intros x.
        rewrite in_concat. intros [Hinx1 [l1 [Hinl1 Hinxl1]]].
        apply H in Hinx1; wf_tac.
        rewrite in_map_iff in Hinl1. destruct Hinl1 as [p1 [Hl1 Hinp1]].
        subst.
        rewrite in_map2_iff with(d1:=(Pwild, tm_d))(d2:=nil) in Hinp1; wf_tac.
        destruct Hinp1 as [i [Hi Hp1]]; subst.
        (*And now we have to show these are distinct, will be similar*)
        apply in_app_or in Hinxl1.
        destruct Hinxl1 as [Hinx2 | Hinx2].
        -- apply alpha_p_aux_wf_aux in Hinx2; wf_tac.
          revert Hinx2; wf_tac; intros.
          apply In_firstn in Hinx2.
          apply in_split_lens_ith in Hinx2; wf_tac.
          apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
        -- rewrite alpha_p_aux_bnd_t_eq in Hinx2.
          rewrite Forall_forall in H0; apply H0 in Hinx2; wf_tac.
          apply In_skipn in Hinx2.
          apply in_split_lens_ith in Hinx2; wf_tac.
          apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
    + (*Second part - TODO very similar to previous*)
      intros x Hinx.
      apply in_app_or in Hinx.
      destruct Hinx as [Hinx | Hinx].
      * apply H in Hinx; wf_tac.
      * rewrite in_concat in Hinx.
        destruct Hinx as [l1 [Hinl1 Hinxl1]].
        rewrite in_map_iff in Hinl1.
        destruct Hinl1 as [p1 [Hl1 Hinp1]].
        subst.
        rewrite in_map2_iff with (d1:=(Pwild, tm_d))(d2:=nil) in Hinp1; wf_tac.
        destruct Hinp1 as [i [Hi Hp1]]; subst.
        apply in_app_or in Hinxl1.
        destruct Hinxl1 as [Hinx | Hinx].
        -- apply alpha_p_aux_wf_aux in Hinx; wf_tac.
          revert Hinx; wf_tac; intros.
          apply In_firstn in Hinx.
          apply in_split_lens_ith in Hinx; wf_tac.
        -- rewrite alpha_p_aux_bnd_t_eq in Hinx.
          rewrite Forall_forall in H0; apply H0 in Hinx; wf_tac.
          apply In_skipn in Hinx.
          apply in_split_lens_ith in Hinx; wf_tac.
  - (*Epsilon case*)
    destruct l; inversion H1; subst; simpl.
    inversion H0; subst.
    rewrite bnd_sub_f.
    split.
    + constructor; [|apply H; wf_tac].
      intro Hin. apply H in Hin; wf_tac.
    + intros. destruct H2; subst; [left; auto | right].
      apply H in H2; wf_tac.
  - (*Fpred case - same as Tfun*)
    split.
    + rewrite NoDup_concat_iff. split.
      * intros x. rewrite in_map_iff.
        intros [t1 [Hbndt1 Hint1]]. subst.
        rewrite in_map2_iff with(d1:=tm_d)(d2:=nil) in Hint1;
        wf_tac.
        destruct Hint1 as [i [Hi Ht1]]; subst.
        rewrite Forall_forall in H.
        apply H; simpl; wf_tac.
      * intros i1 i2 d x. wf_tac.
        intros [Hin1 Hin2].
        (*Idea: suppose in both, then by IH (twice), in 2 different
          parts of l - contradicts NoDup l*)
        rewrite Forall_forall in H.
        rewrite (map2_nth _ _ _ tm_d nil) in Hin1, Hin2; wf_tac.
        apply H in Hin1, Hin2; auto; wf_tac.
        assert (NoDup (concat (split_lens l (map (fun t => length (bnd_t t)) tms)))) by
          (rewrite <- split_lens_concat; wf_tac).
          rewrite NoDup_concat_iff in H5.
        split_all. apply (H6 i1 i2 nil (fst x)); wf_tac.
    + intros x. rewrite in_concat. intros [bl [Hinbl Hinx]].
      rewrite in_map_iff in Hinbl.
      destruct Hinbl as [t1 [Ht1 Hint1]]; subst.
      rewrite (in_map2_iff _ _ _ tm_d nil) in Hint1; wf_tac.
      destruct Hint1 as [i [Hi Ht1]]; subst.
      rewrite Forall_forall in H.
      apply H in Hinx; auto; wf_tac.
      rewrite (split_lens_concat l (map (fun t => length (bnd_t t)) tms));
        [|wf_tac]. rewrite in_concat. eexists. split; [| apply Hinx]. wf_tac.
  - (*Fquant*)
    destruct l; inversion H1; subst; simpl.
    inversion H0; subst.
    rewrite bnd_sub_f.
    split.
    + constructor; [intro C; apply H in C |apply H]; wf_tac.
    + intros. destruct H2; subst;[left | right]; auto.
      apply H in H2; wf_tac.
  - (*Feq*)
    split.
    + rewrite NoDup_app_iff'; split_all;[apply H | apply H0 |]; wf_tac.
      intros x [Hinx1 Hinx2].
      apply H in Hinx1; wf_tac; apply H0 in Hinx2; wf_tac.
      apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x Hinx.
      apply in_app_or in Hinx. destruct Hinx as [Hinx | Hinx]; 
      [apply H in Hinx | apply H0 in Hinx];wf_tac.
  - (*Fbinop*)
    split.
    + rewrite NoDup_app_iff'; split_all;[apply H|apply H0|]; wf_tac.
      intros x [Hinx1 Hinx2].
      apply H in Hinx1; wf_tac; apply H0 in Hinx2; wf_tac.
      apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x Hinx.
      apply in_app_or in Hinx; destruct Hinx as [Hinx | Hinx];
      [apply H in Hinx | apply H0 in Hinx];wf_tac.
  - (*trivial*)
    split;[constructor | intros x []].
  - split;[constructor | intros x []].
  - (*Flet*)
    destruct l; inversion H2; subst.
    inversion H1; subst; simpl; rewrite bnd_sub_f.
    split.
    + constructor.
      * intro C. apply in_app_or in C.
        destruct C as [Hins | Hins];
        [apply H in Hins | apply H0 in Hins]; wf_tac;
        [apply In_firstn in Hins | apply In_skipn in Hins];
        contradiction.
      * rewrite NoDup_app_iff'; split_all; [apply H | apply H0 |];wf_tac.
        intros x [Hinx1 Hinx2]; apply H in Hinx1; apply H0 in Hinx2; wf_tac.
        apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x [Hx | Hinx]; subst;[left | right]; auto.
      apply in_app_or in Hinx; destruct Hinx as [Hinx | Hinx];
      [apply H in Hinx | apply H0 in Hinx]; wf_tac.
  - (*Fif*)
    split.
    + rewrite !NoDup_app_iff'; split_all;
      [apply H | apply H0 | apply H1 | |]; wf_tac;
      intros x; [| rewrite in_app_iff];
      intros [Hinx1 Hinx2];[|destruct Hinx2 as [Hinx2 | Hinx2]];
      [apply H0 in Hinx1; apply H1 in Hinx2 | apply H in Hinx1; 
        apply H0 in Hinx2 | apply H in Hinx1; apply H1 in Hinx2]; wf_tac;
      apply (nodup_firstn_skipn Hinx1); wf_tac.
    + intros x.
      rewrite ! in_app_iff; intros [Hinx | [Hinx | Hinx]];
      [apply H in Hinx | apply H0 in Hinx | apply H1 in Hinx]; wf_tac.
      * apply In_firstn in Hinx. wf_tac.
      * apply In_skipn in Hinx. wf_tac.
  - (*Fmatch case - very similar to Tmatch*)
    assert (Hsum: sum (map
      (fun x : pattern * formula =>
      Datatypes.length (pat_fv (fst x)) + Datatypes.length (bnd_f (snd x)))
      ps) = Datatypes.length (skipn (Datatypes.length (bnd_t tm)) l)). {
        wf_tac. rewrite H2,length_concat, 
      map_map, minus_plus. f_equal. apply map_ext_in_iff; intros.
      rewrite app_length; auto.
    }
    split.
    + rewrite NoDup_app_iff'; split_all.
      * apply H; wf_tac.
      * rewrite NoDup_concat_iff; split_all.
        -- intros x. rewrite in_map_iff.
          intros [pt1 [Hx Hinx]]; subst.
          rewrite (in_map2_iff _ _ _ (Pwild, Ftrue) nil) in Hinx; wf_tac.
          destruct Hinx as [i [Hi Hpt1]].
          rewrite NoDup_app_iff'.
          split_all; subst; wf_tac.
          ++ rewrite alpha_p_aux_bnd_f_eq.
            rewrite Forall_forall in H0.
            apply H0; auto; wf_tac.
          ++ intros x.
            rewrite alpha_p_aux_bnd_f_eq.
            intros [Hinx1 Hinx2].
            (*Need this a lot even though it's ugly*)
            apply alpha_p_aux_wf_aux in Hinx1; wf_tac.
            rewrite map_snd_combine in Hinx1; wf_tac.
            rewrite Forall_forall in H0.
            apply H0 in Hinx2; wf_tac.
            apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
        -- intros i1 i2 d x. wf_tac.
          rewrite !map2_nth with(d1:=(Pwild, Ftrue)) (d2:=nil); wf_tac.
          intros [Hini1 Hini2].
          apply in_app_or in Hini1, Hini2.
          (*Now we get 4 cases need to show each is impossible*)
          destruct Hini1 as [Hini1 | Hini1].
          ++ apply alpha_p_aux_wf_aux in Hini1; wf_tac.
            revert Hini1. wf_tac. intros Hini1.
            apply In_firstn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** apply alpha_p_aux_wf_aux in Hini2; wf_tac.
              revert Hini2. wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** rewrite alpha_p_aux_bnd_f_eq in Hini2.
              rewrite Forall_forall in H0.
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
          ++ rewrite alpha_p_aux_bnd_f_eq in Hini1.
            rewrite Forall_forall in H0.
            apply H0 in Hini1; wf_tac.
            apply In_skipn in Hini1.
            destruct Hini2 as [Hini2 | Hini2].
            ** apply alpha_p_aux_wf_aux in Hini2; wf_tac.
              revert Hini2; wf_tac. intros Hini2.
              apply In_firstn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
            ** rewrite alpha_p_aux_bnd_f_eq in Hini2.
              apply H0 in Hini2; wf_tac.
              apply In_skipn in Hini2.
              apply H5.
              apply (in_nth_concat_nodup Hini1 Hini2); wf_tac.
    * intros x.
      rewrite in_concat. intros [Hinx1 [l1 [Hinl1 Hinxl1]]].
      apply H in Hinx1; wf_tac.
      rewrite in_map_iff in Hinl1. destruct Hinl1 as [p1 [Hl1 Hinp1]].
      subst.
      rewrite in_map2_iff with(d1:=(Pwild, Ftrue))(d2:=nil) in Hinp1; wf_tac.
      destruct Hinp1 as [i [Hi Hp1]]; subst.
      (*And now we have to show these are distinct, will be similar*)
      apply in_app_or in Hinxl1.
      destruct Hinxl1 as [Hinx2 | Hinx2].
      -- apply alpha_p_aux_wf_aux in Hinx2; wf_tac.
        revert Hinx2; wf_tac; intros.
        apply In_firstn in Hinx2.
        apply in_split_lens_ith in Hinx2; wf_tac.
        apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
      -- rewrite alpha_p_aux_bnd_f_eq in Hinx2.
        rewrite Forall_forall in H0; apply H0 in Hinx2; wf_tac.
        apply In_skipn in Hinx2.
        apply in_split_lens_ith in Hinx2; wf_tac.
        apply (nodup_firstn_skipn Hinx1 Hinx2); wf_tac.
    + (*Second part - TODO very similar to previous*)
    intros x Hinx.
    apply in_app_or in Hinx.
    destruct Hinx as [Hinx | Hinx].
    * apply H in Hinx; wf_tac.
    * rewrite in_concat in Hinx.
      destruct Hinx as [l1 [Hinl1 Hinxl1]].
      rewrite in_map_iff in Hinl1.
      destruct Hinl1 as [p1 [Hl1 Hinp1]].
      subst.
      rewrite in_map2_iff with (d1:=(Pwild, Ftrue))(d2:=nil) in Hinp1; wf_tac.
      destruct Hinp1 as [i [Hi Hp1]]; subst.
      apply in_app_or in Hinxl1.
      destruct Hinxl1 as [Hinx | Hinx].
      -- apply alpha_p_aux_wf_aux in Hinx; wf_tac.
        revert Hinx; wf_tac; intros.
        apply In_firstn in Hinx.
        apply in_split_lens_ith in Hinx; wf_tac.
      -- rewrite alpha_p_aux_bnd_f_eq in Hinx.
        rewrite Forall_forall in H0; apply H0 in Hinx; wf_tac.
        apply In_skipn in Hinx.
        apply in_split_lens_ith in Hinx; wf_tac.
Qed.

Corollary alpha_t_aux_wf (t: term):
  (forall (l: list string),
    NoDup l ->
    length l = length (bnd_t t) ->
    NoDup (bnd_t (alpha_t_aux t l)) /\
    (forall x, In x (bnd_t (alpha_t_aux t l)) -> In (fst x) l)).
Proof.
  apply alpha_aux_wf_aux. apply Ftrue.
Qed.

Corollary alpha_f_aux_wf (f: formula):
  (forall (l: list string),
    NoDup l ->
    length l = length (bnd_f f) ->
    NoDup (bnd_f (alpha_f_aux f l)) /\
    (forall x, In x (bnd_f (alpha_f_aux f l)) -> In (fst x) l)).
Proof.
  apply alpha_aux_wf_aux. apply tm_d.
Qed.


(*Need to know that all patterns in constrs are valid*)

(*Generalized so it works for terms and formulas*)
Lemma alpha_p_aux_valid {A B: Type} (sub: vsymbol -> vsymbol -> A -> A)
  (valid: A -> B -> Prop)(p: pattern) (a: A)
  (l: list (vsymbol * string))
  (Hnodup1: NoDup (map fst l))
  (Hnodup2: NoDup (map snd l))
  (sub_valid: forall a x y b,
    valid a b ->
    snd x = snd y ->
    valid (sub x y a) b):
  (forall v : vsymbol, In v (pat_fv p) -> In v (map fst l)) ->
  (forall ty, pattern_has_type sigma p ty ->
    pattern_has_type sigma (fst (alpha_p_aux sub p a l)) ty) /\
  (forall b, valid a b ->
    valid (snd (alpha_p_aux sub p a l)) b).
Proof.
  revert a.
  (*revert l t Hnodup1 Hnodup2.*) induction p; simpl; auto; intros.
  - (*Pvar*) 
    destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha; 
    simpl; split; intros; auto.
    inversion H0; subst.
    replace (snd v) with (snd ((s, snd v))) at 2 by auto.
    constructor; auto.
  - (*Pconstr*)
    split; intros.
    + inversion H1; subst. subst sigma0.
      assert (Hlen: 
      Datatypes.length
      (fst
         ((fix alpha_ps_aux (l1 : list pattern) (y : A) {struct l1} :
               list pattern * A :=
             match l1 with
             | [] => ([], y)
             | ph :: pt =>
                 (fst (alpha_p_aux sub ph y l)
                  :: fst (alpha_ps_aux pt (snd (alpha_p_aux sub ph y l))),
                 snd (alpha_ps_aux pt (snd (alpha_p_aux sub ph y l))))
             end) ps a)) = Datatypes.length (s_args f)). {
        rewrite <- H7. clear. revert a. induction ps; simpl; auto.
      }
      constructor; auto.
      * revert H11. rewrite !Forall_forall.
        assert (length (map (ty_subst (s_params f) vs) (s_args f)) = length ps) by wf_tac.
        generalize dependent (map (ty_subst (s_params f) vs) (s_args f)).
        clear -H H0.
        revert a. induction ps; simpl; auto ; intros; destruct l0.
        -- inversion H1.
        -- inversion H; subst. simpl in H1. destruct H1; subst; simpl.
          ++ apply H5; auto.
            intros. apply H0. simpl. rewrite union_elts. left; auto.
            specialize (H11 (a, v)); simpl in H11.
            apply H11; left; auto.
          ++ apply (IHps H6) with (a:=(snd (alpha_p_aux sub a a0 l))) (l:=l0); auto.
            intros. apply H0. simpl. rewrite union_elts. right; auto.
            intros.
            apply H11; right; auto.
      * rewrite Hlen, <- H7.
        clear Hlen. clear -H12 H0 H Hnodup2. revert a.
        (*We need a separate inductive lemma:*)
        assert (Hinnth: forall (ps: list pattern) (j : nat) (x : vsymbol) (d : pattern) (a : A),
        j < Datatypes.length ps ->
        (forall v : vsymbol,
         In v (big_union vsymbol_eq_dec pat_fv ps) -> In v (map fst l)) ->
        In x
          (pat_fv
             (nth j
                (fst
                   ((fix alpha_ps_aux (l1 : list pattern) (y : A) {struct l1} :
                         list pattern * A :=
                       match l1 with
                       | [] => ([], y)
                       | ph :: pt =>
                           (fst (alpha_p_aux sub ph y l)
                            :: fst (alpha_ps_aux pt (snd (alpha_p_aux sub ph y l))),
                           snd (alpha_ps_aux pt (snd (alpha_p_aux sub ph y l))))
                       end) ps a)) d)) ->
        exists v' : vsymbol, In (v', fst x) l /\ In v' (pat_fv (nth j ps Pwild))). {
          clear.
          induction ps; simpl; auto; intros; try lia.
            destruct j.
            - apply alpha_p_aux_wf_aux_gen in H1; auto.
              intros. apply H0. rewrite union_elts. left; auto.
            - eapply IHps; try lia; auto. 2: apply H1.
              intros. apply H0. rewrite union_elts. right; auto.
        }
        intros t i j d x Hi Hj Hij [Hinx1 Hinx2].
        apply Hinnth in Hinx1; auto.
        apply Hinnth in Hinx2; auto.
        destruct Hinx1 as [v1 [Hinl1 Hinv1]].
        destruct Hinx2 as [v2 [Hinl2 Hinv2]].
        assert (v1 = v2) by apply (nodup_snd_inj Hnodup2 Hinl1 Hinl2). 
        subst.
        (*This contradicts the disjointness of free vars*)
        apply (H12 i j Pwild v2); try lia; auto.
    + (*term goal*)
      generalize dependent a.
      revert H. clear - H0.
      induction ps; simpl; auto; intros.
      inversion H; subst.
      apply IHps; auto.
      * intros. apply H0. simpl. rewrite union_elts. right; auto.
      * apply H4; auto. intros. apply H0. simpl. rewrite union_elts.
        left; auto.
  - (*Por case*)
    split; intros.
    + inversion H0; subst.
      constructor; auto.
      * apply IHp1; auto.
        intros. apply H. rewrite union_elts; left; auto.
      * apply IHp2; auto.
        intros; apply H; rewrite union_elts; right; auto.
      * intros x. rewrite !alpha_p_aux_wf_aux_gen'; auto;
        try (intros; apply H; simpl; rewrite union_elts;
          try(solve[left; auto]); right; auto).
        setoid_rewrite H7. reflexivity.
    + apply IHp2; auto.
      intros. apply H. rewrite union_elts; right; auto.
  - (*Pbind case*)
    split; intros.
    + inversion H0; subst. 
      destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha;
      simpl; auto.
      replace (snd v) with (snd ((s, snd v))) at 2 by auto.
      constructor; simpl.
      * intro. 
        rewrite alpha_p_aux_wf_aux_gen' in H1; auto.
        destruct H1 as [v1 [str [Hinl [Hinv1 [Hsnd Hfst]]]]];
        simpl in *; subst.
        apply get_assoc_list_some in Ha.
        assert (v = v1) by apply (nodup_snd_inj Hnodup2 Ha Hinl); subst.
        apply H4. wf_tac.
        intros. apply H. rewrite union_elts; left; auto.
      * apply IHp; auto. intros.
        apply H; rewrite union_elts; left; auto.
    + destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha; simpl; auto.
      apply sub_valid; auto.
      apply IHp; auto.
      intros. apply H. rewrite union_elts; left; auto.
Qed.


Lemma alpha_p_aux_valid_t (p: pattern) (t: term)
  (l: list (vsymbol * string))
  (Hnodup1: NoDup (map fst l))
  (Hnodup2: NoDup (map snd l)):
  (forall v : vsymbol, In v (pat_fv p) -> In v (map fst l)) ->
  (forall ty, pattern_has_type sigma p ty ->
    pattern_has_type sigma (fst (alpha_p_aux sub_t p t l)) ty) /\
  (forall ty, term_has_type sigma t ty ->
    term_has_type sigma (snd (alpha_p_aux sub_t p t l)) ty).
Proof.
  apply alpha_p_aux_valid; auto.
  apply sub_t_valid.
Qed.

Lemma alpha_p_aux_valid_f (p: pattern) (f: formula)
  (l: list (vsymbol * string))
  (Hnodup1: NoDup (map fst l))
  (Hnodup2: NoDup (map snd l)):
  (forall v : vsymbol, In v (pat_fv p) -> In v (map fst l)) ->
  (forall ty, pattern_has_type sigma p ty ->
    pattern_has_type sigma (fst (alpha_p_aux sub_f p f l)) ty) /\
  (valid_formula sigma f ->
    valid_formula sigma (snd (alpha_p_aux sub_f p f l))).
Proof.
  intros Hinfv.
  pose proof (alpha_p_aux_valid sub_f 
    (fun f' (u: unit) => valid_formula sigma f') 
      p f l Hnodup1 Hnodup2);
  split; apply H; auto; try(intros; apply sub_f_valid; auto).
  exact tt.
Qed.

(*Part 2: [alpha_t_aux] and [alpha_f_aux] form well-typed
  terms and formulas*)
Lemma alpha_aux_valid (t: term) (f: formula):
  (forall (l: list string) (ty: vty)
    (Hnodup: NoDup l)
    (Hlenl: length l = length (bnd_t t)),
    term_has_type sigma t ty ->
    term_has_type sigma (alpha_t_aux t l) ty) /\
  (forall (l: list string)
    (Hnodup: NoDup l)
    (Hlenl: length l = length (bnd_f f)),
    valid_formula sigma f ->
    valid_formula sigma (alpha_f_aux f l)).
Proof.
  revert t f.
  apply term_formula_ind; simpl; auto; simpl; intros.
  - (*Tfun*)
    inversion H0; subst. constructor; auto.
    wf_tac. revert H11 H.
    rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H1; wf_tac.
    destruct H1 as [i [Hi Hx]].
    revert Hi; wf_tac.
    specialize (Hx tm_d vty_int); subst; simpl.
    rewrite map2_nth with(d1:=tm_d) (d2:=nil); wf_tac.
    apply H; wf_tac.
    rewrite map_nth_inbound with(d2:=vty_int); try lia.
    apply (H11 (nth i l1 tm_d, 
      (ty_subst (s_params f1) l (nth i (s_args f1) vty_int)))).
    rewrite in_combine_iff; wf_tac.
    exists i. split; auto. intros.
    f_equal.
    + apply nth_indep; auto.
    + rewrite map_nth_inbound with (d2:=vty_int); auto. lia.
  - (*Tlet*) destruct l; auto; simpl.
    inversion H1; subst.
    inversion Hnodup; subst.
    wf_tac. inversion Hlenl.
    constructor.
    + apply H; wf_tac.
    + apply sub_t_valid; auto. apply H0; wf_tac.
  - (*Tif*) inversion H2; subst.
    constructor; auto.
    apply H; wf_tac.
    apply H0; wf_tac.
    apply H1; wf_tac.
  - (*Tmatch*)
    assert (Hsum: sum (map
      (fun x : pattern * term =>
      Datatypes.length (pat_fv (fst x)) + Datatypes.length (bnd_t (snd x)))
      ps) = Datatypes.length (skipn (Datatypes.length (bnd_t tm)) l)). {
        wf_tac. rewrite Hlenl,length_concat, 
      map_map, minus_plus. f_equal. apply map_ext_in_iff; intros.
      rewrite app_length; auto.
    }
    inversion H1; subst.
    constructor.
    + apply H; auto; wf_tac.
    + intros x.
      rewrite in_map2_iff with(d1:=(Pwild, tm_d))(d2:=nil); wf_tac.
      intros [i [Hi Hx]]; subst.
      apply alpha_p_aux_valid_t; wf_tac.
      apply H7; wf_tac.
    + intros x.
      rewrite in_map2_iff with(d1:=(Pwild, tm_d))(d2:=nil); wf_tac.
      intros [i [Hi Hx]]; subst.
      apply alpha_p_aux_valid_t; wf_tac.
      rewrite Forall_forall in H0. apply H0; wf_tac.
      apply H9; wf_tac.
    + rewrite null_map2; auto; wf_tac.
  - (*Teps*)
    destruct l; inversion Hlenl.
    inversion H0; subst.
    replace (snd v) with (snd (s, snd v)) at 3 by auto.
    constructor; auto.
    apply sub_f_valid; auto. inversion Hnodup. apply H; wf_tac.
  - (*Fpred*)
    inversion H0; subst.
    constructor; auto; wf_tac.
    revert H9 H.
    rewrite !Forall_forall; intros.
    rewrite in_combine_iff in H1; wf_tac.
    destruct H1 as [i [Hi Hx]].
    revert Hi; wf_tac.
    specialize (Hx tm_d vty_int); subst; simpl.
    rewrite map2_nth with(d1:=tm_d) (d2:=nil); wf_tac.
    apply H; wf_tac.
    rewrite map_nth_inbound with(d2:=vty_int); try lia.
    apply (H9 (nth i tms tm_d, 
      (ty_subst (p_params p) tys (nth i (p_args p) vty_int)))).
    rewrite in_combine_iff; wf_tac.
    exists i. split; auto. intros.
    f_equal.
    + apply nth_indep; auto.
    + rewrite map_nth_inbound with (d2:=vty_int); auto. lia.
  - (*Fquant*)
    destruct l; inversion Hlenl.
    inversion H0; subst.
    constructor; auto.
    apply sub_f_valid; auto.
    apply H; auto. inversion Hnodup; auto.
  - (*Feq*)
    inversion H1; subst.
    constructor; [apply H | apply H0]; wf_tac.
  - (*Fbinop*)
    inversion H1; subst.
    constructor; [apply H | apply H0]; wf_tac.
  - (*Fnot*)
    inversion H0; subst.
    constructor. apply H; wf_tac.
  - (*Flet*)
    destruct l; inversion Hlenl; simpl.
    inversion H1; subst.
    inversion Hnodup; subst.
    constructor; [apply H | apply sub_f_valid]; wf_tac.
    apply H0; wf_tac.
  - (*Fif*)
    inversion H2; subst.
    constructor; [apply H | apply H0 | apply H1]; wf_tac.
  - (*Fmatch*)
    assert (Hsum: sum (map
      (fun x : pattern * formula =>
      Datatypes.length (pat_fv (fst x)) + Datatypes.length (bnd_f (snd x)))
      ps) = Datatypes.length (skipn (Datatypes.length (bnd_t tm)) l)). {
        wf_tac. rewrite Hlenl,length_concat, 
      map_map, minus_plus. f_equal. apply map_ext_in_iff; intros.
      rewrite app_length; auto.
    }
    inversion H1; subst.
    constructor.
    + apply H; auto; wf_tac.
    + rewrite Forall_forall; intros x.
      rewrite in_map2_iff with(d1:=(Pwild, Ftrue))(d2:=nil); wf_tac.
      intros [i [Hi Hx]]; subst.
      apply alpha_p_aux_valid_f; wf_tac.
      rewrite Forall_forall in H7;
      apply H7; wf_tac.
    + rewrite Forall_forall; intros x.
      rewrite in_map2_iff with(d1:=(Pwild, Ftrue))(d2:=nil); wf_tac.
      intros [i [Hi Hx]]; subst.
      apply alpha_p_aux_valid_f; wf_tac.
      rewrite Forall_forall in H0. apply H0; wf_tac.
      rewrite Forall_forall in H8; apply H8; wf_tac.
    + rewrite null_map2; auto; wf_tac.
Qed.

Corollary alpha_t_aux_type (t: term) :
  (forall (l: list string) (ty: vty)
    (Hnodup: NoDup l)
    (Hlenl: length l = length (bnd_t t)),
    term_has_type sigma t ty ->
    term_has_type sigma (alpha_t_aux t l) ty).
Proof.
  apply alpha_aux_valid. apply Ftrue.
Qed.

Lemma alpha_f_aux_type (f: formula):
  (forall (l: list string)
    (Hnodup: NoDup l)
    (Hlenl: length l = length (bnd_f f)),
    valid_formula sigma f ->
    valid_formula sigma (alpha_f_aux f l)).
Proof.
  apply alpha_aux_valid. apply tm_d.
Qed.

Set Bullet Behavior "Strict Subproofs".
Search sub_t term_fv.

(*Part 2.5: We need to know that this substitution does not
  change the free variables. This is very hard to show, particularly
  due to the patterns and their dependencies*)

(*Some tactics that will be useful:*)

Ltac simpl_set_goal :=
  repeat match goal with
  (*remove*)
  | H: In ?x (remove ?e ?y ?l) |- _ => rewrite in_remove_iff in H
  | |- context [ In ?x (remove ?e ?y ?l)] => rewrite in_remove_iff
  (*big_union*)
  | H: In ?x (big_union ?e ?f ?l) |- _ => rewrite <- big_union_elts in H
  | |- context [ In ?x (big_union ?e ?f ?l)] => rewrite <- big_union_elts
  (*union*)
  | H: In ?x (union ?e ?l1 ?l2) |- _ => rewrite union_elts in H
  | |- context [ In ?x (union ?e ?l1 ?l2)] => rewrite union_elts
  (*cons - TODO do without simpl*)
  | H: In ?x (?y :: ?t) |-_ => simpl in H
  | |- context [In ?x (?y :: ?t)] => simpl
  (*remove \/ False from In goals*)
  | H: ?P \/ False |- _ => rewrite or_false_r in H
  | |- context [ ?P \/ False] => rewrite or_false_r
  (*remove_all*)
  | H: In ?x (remove_all ?e ?l1 ?l2) |- _ => rewrite <- remove_all_elts in H
  | |- context [In ?x (remove_all ?e ?l1 ?l2)] => rewrite <- remove_all_elts
  end.

Ltac simpl_set :=
  simpl_set_goal;
  repeat match goal with
  | H: ~ In ?x (remove_all ?e ?l1 ?l2) |- _ => revert H; simpl_set_goal; intros
  | H: ~ In ?x (union ?e ?l1 ?l2) |- _ => revert H; simpl_set_goal; intros
  | H: ~ In ?x (big_union ?e ?f ?l) |- _ => revert H; simpl_set_goal; intros
  | H: ~ In ?x (remove ?e ?y ?l) |- _ => revert H; simpl_set_goal; intros
  end.

Ltac destruct_all :=
  repeat match goal with
  | H: ?P /\ ?Q |- _ => destruct H
  | H: exists x, ?P |- _ => destruct H
  | H: ?P \/ ?Q |- _ => destruct H
  end; subst.

Ltac simpl_destruct_set :=
  repeat (progress (simpl_set; destruct_all)).

Ltac triv :=
  let inner := split_all; auto; 
  match goal with
  | |- ~ ?P => let C := fresh in intro C; subst; contradiction
  end
  in
  try solve[inner];
  match goal with
  | |- ?P \/ ?Q => solve[left; inner] + solve[right; inner]
  end.

Ltac not_or name :=
  repeat match goal with 
  | H: ~(?P \/ ?Q) |- _ => let N1 := fresh name in
    let N2 := fresh name in
    apply Decidable.not_or in H;
    
    destruct H as [N1 N2]
  end.

Ltac case_in :=
  repeat match goal with
  | |- context [if in_bool ?e ?x ?l then ?y else ?z] => 
    destruct (in_bool_spec e x l)
  end.

(*A few easy results about sub_t/f and free vars:*)

(*If the free var to sub is not in the term, substitution does nothing*)
Lemma sub_notin (t: term) (f: formula) :
  (forall (x y: vsymbol),
    ~ In x (term_fv t) ->
    sub_t x y t = t) /\
    (forall (x y: vsymbol),
    ~ In x (form_fv f) ->
    sub_f x y f = f).
Proof.
  revert t f. apply term_formula_ind; simpl; auto; intros; simpl_set; not_or Hinx.
  - destruct (vsymbol_eq_dec x v); subst; auto; contradiction.
  - f_equal. apply list_eq_ext';
    rewrite map_length; auto.
    intros.
    rewrite (map_nth_inbound) with(d2:=d); auto.
    rewrite Forall_forall in H. apply H; wf_tac.
    intro C. apply H0. simpl_set.  exists (nth n l1 d); split; wf_tac.
  - rewrite H; auto.
    destruct (vsymbol_eq_dec x v); subst; auto.
    rewrite H0; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H; auto. f_equal.
    apply list_eq_ext'; rewrite map_length; auto; intros.
    rewrite map_nth_inbound with (d2:=d); auto.
    case_in; auto.
    rewrite Forall_forall in H0. rewrite H0; wf_tac.
    destruct (nth n ps d); auto.
    intro Hinx'. apply Hinx0. exists (nth n ps d).
    split; wf_tac. simpl_set. split; auto.
  - destruct (vsymbol_eq_dec x v); subst; auto.
    rewrite H; auto.
  - f_equal. apply list_eq_ext';
    rewrite map_length; auto.
    intros.
    rewrite (map_nth_inbound) with(d2:=d); auto.
    rewrite Forall_forall in H. apply H; wf_tac.
    intro C. apply H0.  exists (nth n tms d); split; wf_tac.
  - destruct (vsymbol_eq_dec x v); subst; auto.
    rewrite H; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0; auto.
  - rewrite H; auto.
  - rewrite H; auto.
    destruct (vsymbol_eq_dec x v); subst; auto.
    rewrite H0; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H; auto.
    f_equal.
    apply list_eq_ext'; rewrite map_length; auto; intros.
    rewrite map_nth_inbound with (d2:=d); auto.
    case_in; auto.
    rewrite Forall_forall in H0. rewrite H0; wf_tac.
    destruct (nth n ps d); auto.
    intro Hinx'. apply Hinx0. exists (nth n ps d).
    split; wf_tac. simpl_set. split; auto.
Qed.

Corollary sub_t_notin (t: term):
  (forall (x y: vsymbol),
    ~ In x (term_fv t) ->
    sub_t x y t = t).
Proof. apply sub_notin. apply Ftrue. Qed.

Corollary sub_f_notin (f: formula):
    (forall (x y: vsymbol),
    ~ In x (form_fv f) ->
    sub_f x y f = f).
Proof. apply sub_notin. apply tm_d. Qed.

(*If we substitute x with itself, then nothing changes*)
Lemma sub_eq (t: term) (f: formula) :
  (forall (x: vsymbol),
    sub_t x x t = t) /\
    (forall (x: vsymbol),
    sub_f x x f = f).
Proof.
  revert t f; apply term_formula_ind; simpl; auto; intros.
  - destruct (vsymbol_eq_dec x v); subst; auto.
  - f_equal. apply list_eq_ext'; rewrite map_length; auto; intros.
    rewrite map_nth_inbound with(d2:=d); auto.
    rewrite Forall_forall in H; apply H; wf_tac.
  - rewrite H. destruct (vsymbol_eq_dec x v); subst; auto.
    rewrite H0; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H. f_equal. apply list_eq_ext'; rewrite map_length; auto;
    intros. rewrite map_nth_inbound with(d2:=d); auto.
    rewrite Forall_forall in H0; rewrite H0; wf_tac.
    case_in; auto. destruct (nth n ps d); auto.
  - destruct (vsymbol_eq_dec x v); subst; auto. rewrite H; auto.
  - f_equal. apply list_eq_ext'; rewrite map_length; auto; intros.
    rewrite map_nth_inbound with(d2:=d); auto.
    rewrite Forall_forall in H; apply H; wf_tac.
  - destruct (vsymbol_eq_dec x v); subst; auto. rewrite H; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0; auto.
  - rewrite H; auto.
  - rewrite H, H0. destruct (vsymbol_eq_dec x v); auto.
  - rewrite H, H0, H1; auto.
  - rewrite H. f_equal. apply list_eq_ext'; rewrite map_length; auto;
    intros. rewrite map_nth_inbound with(d2:=d); auto.
    rewrite Forall_forall in H0; rewrite H0; wf_tac.
    case_in; auto. destruct (nth n ps d); auto.
Qed.

Corollary sub_t_eq (t: term):
  (forall (x: vsymbol),
    sub_t x x t = t).
Proof. apply sub_eq. apply Ftrue. Qed.

Corollary sub_f_eq (f: formula):
    (forall (x: vsymbol),
    sub_f x x f = f).
Proof. apply sub_eq. apply tm_d. Qed.

(*It is easier to prove some of the lemmas with an alternate
  approach: define when a variable is free rather than show
  the sets of free vars are equal:*)
Fixpoint free_in_t (x: vsymbol) (t: term) {struct t} : bool :=
  match t with
  | Tconst _ => false
  | Tvar v => vsymbol_eq_dec x v
  | Tfun f tys tms => existsb (fun t => free_in_t x t) tms
  | Tlet t1 v t2 =>
    free_in_t x t1 || (negb (vsymbol_eq_dec x v) && free_in_t x t2)
  | Tif f t1 t2 =>
    free_in_f x f || free_in_t x t1 || free_in_t x t2
  | Tmatch tm ty ps =>
    free_in_t x tm ||
    existsb (fun p => negb (in_bool vsymbol_eq_dec x (pat_fv (fst p))) &&
      free_in_t x (snd p)) ps
  | Teps f v => negb (vsymbol_eq_dec x v) && free_in_f x f
  end
with free_in_f (x: vsymbol) (f: formula) {struct f} : bool :=
  match f with
  | Fpred p tys tms => existsb (fun t => free_in_t x t) tms
  | Fquant q v f1 => negb (vsymbol_eq_dec x v) && free_in_f x f1
  | Feq ty t1 t2 => free_in_t x t1 || free_in_t x t2
  | Fbinop b f1 f2 => free_in_f x f1 || free_in_f x f2
  | Fnot f1 => free_in_f x f1
  | Flet tm v f1 => free_in_t x tm || (negb (vsymbol_eq_dec x v) &&
   free_in_f x f1)
  | Fif f1 f2 f3 => free_in_f x f1 || free_in_f x f2 ||
    free_in_f x f3
  | Fmatch tm ty ps =>
    free_in_t x tm ||
    (existsb (fun p => negb (in_bool vsymbol_eq_dec x (pat_fv (fst p)))
      && free_in_f x (snd p)) ps)
  | _ => false
  end.

Ltac bool_to_prop :=
  repeat (progress (
  unfold is_true;
  (*First, convert bools to props*)
  repeat match goal with
  | |- context [(?b && ?b1) = true] =>
    rewrite andb_true_iff
  | |- context [(?b1 || ?b2) = true] =>
    rewrite orb_true_iff
  | |- context [existsb ?f ?l = true] =>
    rewrite existsb_exists
  (*| |- context [negb ?b = true] =>
    rewrite negb_true_iff*)
  end;
  (*Try to simplify*)
  repeat(
    apply or_iff_compat_l ||
    apply and_iff_compat_l
  );
  (*Put the goal in a nicer form*)
  repeat lazymatch goal with
  | |- ?P /\ ?Q <-> ?Q /\ ?R => rewrite (and_comm P Q)
  | |- ?P \/ ?Q <-> ?Q \/ ?R => rewrite (or_comm P Q)
  | |- ?P /\ ?Q <-> ?R /\ ?P => rewrite (and_comm R P)
  | |- ?P \/ ?Q <-> ?R /\ ?P => rewrite (or_comm R P)
  | |- context [ (?P \/ ?Q) \/ ?R] => rewrite or_assoc
  | |- ?P <-> ?P => reflexivity
  end)).

Lemma ex_in_eq {A: Type} (l: list A) (P1 P2: A -> Prop) :
  Forall (fun x => P1 x <-> P2 x) l ->
  (exists x, In x l /\ P1 x) <->
  (exists x, In x l /\ P2 x).
Proof.
  intros. rewrite Forall_forall in H. 
  split; intros [x [Hinx Hpx]]; exists x; split; auto;
  apply H; auto.
Qed.

Lemma eq_sym_iff {A: Type} (x y: A):
  x = y <-> y = x.
Proof.
  split; intros; subst; auto.
Qed.

Lemma dec_iff {P: Prop} {dec: {P} + { ~ P}}:
  dec <-> P.
Proof.
  destruct dec; simpl; split; intros; auto. inversion H.
Qed.

Lemma dec_negb_iff {P: Prop} {dec: {P} + {~ P}}:
  negb dec <-> ~ P.
Proof.
  destruct dec; simpl; split; intros; auto.
Qed.

(*This is equivalent to the other formulation*)
(*TODO: would be easier with ssreflect*)
Lemma free_in_spec (t: term) (f: formula) :
  (forall x, free_in_t x t <-> In x (term_fv t)) /\
  (forall x, free_in_f x f <-> In x (form_fv f)).
Proof.
  revert t f.
  apply term_formula_ind; simpl; intros; auto; simpl_set; auto;
  try solve[split; auto].
  - rewrite (eq_sym_iff v x), dec_iff; reflexivity. 
  - bool_to_prop. apply ex_in_eq.
    eapply Forall_impl. 2: apply H. simpl; intros; auto. apply H0; auto.
  - rewrite <- H, <- H0. bool_to_prop.
    apply dec_negb_iff.
  - rewrite<- H, <- H0, <- H1.
    bool_to_prop.
  - rewrite <- H. bool_to_prop.
    apply ex_in_eq.
    revert H0. rewrite !Forall_forall; intros. simpl_set.
    bool_to_prop.
    rewrite <- H0; wf_tac. bool_to_prop.
    rewrite <- in_bool_dec.
    apply dec_negb_iff.
  - rewrite <- H; bool_to_prop.
    apply dec_negb_iff.
  - bool_to_prop. apply ex_in_eq.
    eapply Forall_impl. 2: apply H. simpl; intros; auto. apply H0; auto.
  - rewrite <- H; bool_to_prop. apply dec_negb_iff.
  - rewrite <- H, <- H0. bool_to_prop.
  - rewrite <- H, <- H0; bool_to_prop.
  - rewrite <- H, <- H0; bool_to_prop.
    apply dec_negb_iff.
  - rewrite <- H, <- H0, <- H1; bool_to_prop.
  - rewrite <- H. bool_to_prop.
    apply ex_in_eq.
    revert H0. rewrite !Forall_forall; intros. simpl_set.
    bool_to_prop.
    rewrite <- H0; wf_tac. bool_to_prop.
    rewrite <- in_bool_dec.
    apply dec_negb_iff.
Qed.

Corollary free_in_t_spec (t: term):
(forall x, free_in_t x t <-> In x (term_fv t)).
Proof. apply free_in_spec. apply Ftrue. Qed.

Lemma free_in_t_negb (t: term):
forall x, free_in_t x t = false <-> ~In x (term_fv t).
Proof.
  intros. destruct (free_in_t x t) eqn : Hfree; split; intros; auto.
  assert (is_true (free_in_t x t)) by auto.
  apply free_in_t_spec in H0. contradiction.
  intro Hin. apply free_in_t_spec in Hin.
  rewrite Hfree in Hin. inversion Hin.
Qed.

Corollary free_in_f_spec (f: formula):
(forall x, free_in_f x f <-> In x (form_fv f)).
Proof. apply free_in_spec. apply tm_d. Qed.

Lemma free_in_f_negb (f: formula):
forall x, free_in_f x f = false <-> ~In x (form_fv f).
Proof.
  intros. destruct (free_in_f x f) eqn : Hfree; split; intros; auto.
  assert (is_true (free_in_f x f)) by auto.
  apply free_in_f_spec in H0. contradiction.
  intro Hin. apply free_in_f_spec in Hin.
  rewrite Hfree in Hin. inversion Hin.
Qed.

(*Now we can reason about [free_in]*)

(*3 lemmas about free vars and [sub_t]*)

Ltac vsym_eq x y :=
  destruct (vsymbol_eq_dec x y); subst; auto; try contradiction.

Lemma existsb_eq {A: Type} {f1 f2: A -> bool} (l1 l2: list A):
  length l1 = length l2 ->
  Forall (fun x => f1 (fst x) = f2 (snd x)) (combine l1 l2) ->
  existsb f1 l1 = existsb f2 l2.
Proof.
  revert l2. induction l1; simpl; intros; destruct l2; inversion H; simpl; auto.
  inversion H0; subst.
  simpl in H4. rewrite H4, (IHl1 l2); auto.
Qed. 
  

(*1. For any variables which are not x or y, sub_t doesn't change anything*)
Lemma sub_fv_diff (t: term) (f: formula):
  (forall (x y z: vsymbol),
    z <> x -> z <> y ->
    free_in_t z (sub_t x y t) = free_in_t z t) /\
  (forall (x y z: vsymbol),
    z <> x -> z <> y ->
    free_in_f z (sub_f x y f) = free_in_f z f).
Proof.
  revert t f.
  apply term_formula_ind; simpl; auto; intros.
  - vsym_eq x v. vsym_eq z y. vsym_eq z v.
  - apply existsb_eq; wf_tac.
    revert H. rewrite !Forall_forall; intros.
    revert H2. 
    rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d); subst; simpl.
    wf_tac.
    apply H; wf_tac.
  - rewrite H; auto. f_equal. f_equal.
    vsym_eq x v.
  - rewrite H, H0, H1; auto.
  - rewrite H; auto. f_equal.
    apply existsb_eq; wf_tac.
    revert H0.
    rewrite !Forall_forall; intros.
    revert H3.
    rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]; specialize (Hx (Pwild, tm_d) (Pwild, tm_d)); subst; simpl.
    wf_tac. case_in; auto.
    simpl; rewrite H0; wf_tac.
  - vsym_eq x v. simpl. rewrite H; auto.
  - apply existsb_eq; wf_tac.
    revert H. rewrite !Forall_forall; intros.
    revert H2. 
    rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d); subst; simpl.
    wf_tac.
    apply H; wf_tac.
  - vsym_eq x v; simpl; rewrite H; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0; auto.
  - rewrite H; auto. f_equal. f_equal.
    vsym_eq x v.
  - rewrite H, H0, H1; auto.
  - rewrite H; auto. f_equal.
    apply existsb_eq; wf_tac.
    revert H0.
    rewrite !Forall_forall; intros.
    revert H3.
    rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]; specialize (Hx (Pwild, Ftrue) (Pwild, Ftrue)); subst; simpl.
    wf_tac. case_in; auto.
    simpl; rewrite H0; wf_tac.
Qed.

Corollary sub_t_fv_diff (t: term):
  (forall (x y z: vsymbol),
    z <> x -> z <> y ->
    free_in_t z (sub_t x y t) = free_in_t z t).
Proof. apply sub_fv_diff. apply Ftrue. Qed.

Corollary sub_f_fv_diff (f:formula):
  (forall (x y z: vsymbol),
    z <> x -> z <> y ->
    free_in_f z (sub_f x y f) = free_in_f z f).
Proof. apply sub_fv_diff. apply tm_d. Qed.

Lemma existsb_false {A: Type} (f: A -> bool) (l: list A):
  (existsb f l = false) <-> Forall (fun x => f x = false) l.
Proof.
  induction l; simpl; split; intros; auto.
  - rewrite orb_false_iff in H.
    destruct_all; subst; constructor; auto.
    apply IHl; auto.
  - rewrite orb_false_iff. inversion H; subst.
    split; auto. apply IHl; auto.
Qed.

(*2: If we replace x with y, x is NOT in the resulting free variables*)
Lemma sub_fv_notin (t: term) (f: formula):
  (forall (x y: vsymbol),
    x <> y ->
    free_in_t x (sub_t x y t) = false) /\
  (forall (x y: vsymbol),
    x <> y ->
    free_in_f x (sub_f x y f) = false).
Proof.
  revert t f. apply term_formula_ind; simpl; auto; intros.
  - vsym_eq x v. vsym_eq v y. vsym_eq x v.
  - apply existsb_false.
    revert H. rewrite !Forall_forall; intros.
    revert H1. rewrite in_map_iff; intros [t [Ht Hint]]; subst.
    apply H; auto.
  - rewrite !orb_false_iff. split; [apply H; auto|].
    vsym_eq x v. simpl. apply H0; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H; simpl; auto.
    apply existsb_false. revert H0. rewrite !Forall_forall; intros.
    revert H2. rewrite in_map_iff; intros [p1 [Hp1 Hinp1]]; subst.
    case_in; simpl; destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst p1))); simpl; auto;
    try contradiction.
    apply H0; wf_tac.
  - vsym_eq x v; simpl; auto. vsym_eq v v.
    vsym_eq x v; simpl. apply H; auto.
  - apply existsb_false.
    revert H. rewrite !Forall_forall; intros.
    revert H1. rewrite in_map_iff; intros [t [Ht Hint]]; subst.
    apply H; auto.
  - vsym_eq x v; simpl. vsym_eq v v. vsym_eq x v; simpl.
    apply H; auto.
  - rewrite H, H0; auto.
  - rewrite H, H0; auto.
  - rewrite H; auto; simpl. vsym_eq x v; simpl.
    apply H0; auto.
  - rewrite H, H0, H1; auto.
  - rewrite H; simpl; auto.
    apply existsb_false. revert H0. rewrite !Forall_forall; intros.
    revert H2. rewrite in_map_iff; intros [p1 [Hp1 Hinp1]]; subst.
    case_in; simpl; destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst p1))); simpl; auto;
    try contradiction.
    apply H0; wf_tac.
Qed.

Corollary sub_t_fv_notin (t: term):
  (forall (x y: vsymbol),
    x <> y ->
    free_in_t x (sub_t x y t) = false).
Proof. apply sub_fv_notin. apply Ftrue. Qed.

Corollary sub_f_fv_notin (f: formula):
  (forall (x y: vsymbol),
    x <> y ->
    free_in_f x (sub_f x y f) = false).
Proof. apply sub_fv_notin. apply tm_d. Qed.

Lemma existsb_orb {A: Type} (f1 f2: A -> bool) (l: list A):
  existsb f1 l || existsb f2 l =
  existsb (fun x => f1 x || f2 x) l.
Proof.
  induction l; simpl; auto.
  rewrite <- !orb_assoc. f_equal.
  rewrite orb_comm, <- orb_assoc. f_equal.
  rewrite orb_comm; apply IHl.
Qed.

Ltac simpl_bool :=
  repeat (progress (simpl;
  try rewrite !orb_assoc;
  try rewrite !andb_assoc;
  repeat match goal with
  | |- context [ ?b && true] => rewrite andb_true_r
  | |- context [?b || true] => rewrite orb_true_r
  | |- context [?b && false] => rewrite andb_false_r
  | |- context [?b || false] => rewrite orb_false_r
  end)).

Ltac solve_bool :=
  simpl_bool;
  (*Then brute force the solution*)
  repeat 
  (match goal with
  | |- ?b1 && ?b2 = ?z => destruct b2
  | |- ?b1 || ?b2 = ?z => destruct b2
  | |- ?z = ?b1 && ?b2 => destruct b2
  | |- ?z = ?b1 || ?b2 => destruct b2
  end; simpl_bool; try reflexivity).


(*3. When we substitute x with y, y is in the free variables
  iff either y was before or x was before*)
(*Need the Hbnd assumption for the following: in let t1 = v in t2,
  if y =v, then y will not be in the free variables of
  the substituted term even if x is a free variable in t2*)
Lemma sub_fv_in (t: term) (f: formula):
  (forall (x y: vsymbol)
    (Hbnd: ~ In y (bnd_t t)),
    x <> y ->
    free_in_t y (sub_t x y t) = (free_in_t x t) || (free_in_t y t)) /\
  (forall (x y: vsymbol)
    (Hbnd: ~ In y (bnd_f f)),
    x <> y ->
    free_in_f y (sub_f x y f) = (free_in_f x f) || (free_in_f y f)).
Proof.
  revert t f. apply term_formula_ind; simpl; auto; intros.
  - vsym_eq x v; simpl.
    vsym_eq y y.
  - rewrite existsb_orb.
    apply existsb_eq; wf_tac.
    revert H. rewrite !Forall_forall; intros.
    revert H1. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d); subst; simpl.
    wf_tac. apply H; wf_tac. intro C.
    apply Hbnd. rewrite in_concat. exists (bnd_t (nth i l1 tm_d)); 
    split; wf_tac.
  - rewrite H; auto; [|intro C; apply Hbnd; right; apply in_or_app; triv]. 
    rewrite <- !orb_assoc. f_equal.
    rewrite !orb_andb_distrib_r.
    vsym_eq x v.
    rewrite H0; auto; [|intro C; apply Hbnd; right; apply in_or_app; triv].
    vsym_eq y v. exfalso. apply Hbnd; triv.
    simpl. solve_bool.
  - rewrite H, H0, H1; auto;[solve_bool| | |]; intro C; apply Hbnd;
    rewrite !in_app_iff; triv.
  - (*match is hard case not surprisingly*)
    rewrite H; auto; [|intro C; apply Hbnd; rewrite in_app_iff; triv].
    simpl_bool. rewrite (orb_comm (_ || _) (free_in_t y tm)).
    rewrite orb_assoc, (orb_comm (free_in_t y tm)).
    rewrite <- !orb_assoc. f_equal. f_equal.
    (*Now just have the exists goal*)
    rewrite existsb_orb.
    apply existsb_eq; wf_tac.
    revert H0. rewrite !Forall_forall; intros.
    revert H2. rewrite in_combine_iff; wf_tac; intros [i [Hi Hx]].
    specialize (Hx (Pwild, tm_d) (Pwild, tm_d)); subst; simpl.
    wf_tac. case_in; simpl; auto.
    destruct (in_bool_spec vsymbol_eq_dec y (pat_fv (fst (nth i ps (Pwild, tm_d))))); simpl.
    + (*contradiction: y not in bound vars*)
      exfalso. apply Hbnd. rewrite in_app_iff. right.
      rewrite in_concat. exists ((pat_fv (fst (nth i ps (Pwild, tm_d))))
      ++ (bnd_t (snd (nth i ps (Pwild, tm_d))))).
      split; wf_tac. exists (nth i ps (Pwild, tm_d)). split; wf_tac.
      rewrite in_app_iff; triv.
    + rewrite H0; wf_tac. intro C.
      apply Hbnd. rewrite in_app_iff. right. 
      rewrite in_concat. exists ((pat_fv (fst (nth i ps (Pwild, tm_d))))
      ++ (bnd_t (snd (nth i ps (Pwild, tm_d))))).
      split; wf_tac. exists (nth i ps (Pwild, tm_d)). split; wf_tac.
      rewrite in_app_iff; triv.
  - vsym_eq x v; simpl.
    vsym_eq y v; simpl.
    + exfalso; apply Hbnd; triv.
    + rewrite H; auto.
  - rewrite existsb_orb.
    apply existsb_eq; wf_tac.
    revert H. rewrite !Forall_forall; intros.
    revert H1. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d); subst; simpl.
    wf_tac. apply H; wf_tac. intro C.
    apply Hbnd. rewrite in_concat. exists (bnd_t (nth i tms tm_d)); 
    split; wf_tac.
  - vsym_eq x v; simpl.
    vsym_eq y v; simpl.
    + exfalso; apply Hbnd; triv.
    + rewrite H; auto.
  - rewrite H, H0; auto; [solve_bool | |]; intro C; apply Hbnd;
    rewrite in_app_iff; triv.
  - rewrite H, H0; auto; [solve_bool | |]; intro C; apply Hbnd;
    rewrite in_app_iff; triv.
  - rewrite H; auto; [|intro C; apply Hbnd; right; apply in_or_app; triv]. 
    rewrite <- !orb_assoc. f_equal.
    rewrite !orb_andb_distrib_r.
    vsym_eq x v.
    rewrite H0; auto; [|intro C; apply Hbnd; right; apply in_or_app; triv].
    vsym_eq y v. exfalso. apply Hbnd; triv.
    simpl. solve_bool.
  - rewrite H, H0, H1; auto;[solve_bool | | |]; intro C;
    apply Hbnd; rewrite !in_app_iff; triv.
  - rewrite H; auto; [|intro C; apply Hbnd; rewrite in_app_iff; triv].
    simpl_bool. rewrite (orb_comm (_ || _) (free_in_t y tm)).
    rewrite orb_assoc, (orb_comm (free_in_t y tm)).
    rewrite <- !orb_assoc. f_equal. f_equal.
    (*Now just have the exists goal*)
    rewrite existsb_orb.
    apply existsb_eq; wf_tac.
    revert H0. rewrite !Forall_forall; intros.
    revert H2. rewrite in_combine_iff; wf_tac; intros [i [Hi Hx]].
    specialize (Hx (Pwild, Ftrue) (Pwild, Ftrue)); subst; simpl.
    wf_tac. case_in; simpl; auto.
    destruct (in_bool_spec vsymbol_eq_dec y (pat_fv (fst (nth i ps (Pwild, Ftrue))))); simpl.
    + (*contradiction: y not in bound vars*)
      exfalso. apply Hbnd. rewrite in_app_iff. right.
      rewrite in_concat. exists ((pat_fv (fst (nth i ps (Pwild, Ftrue))))
      ++ (bnd_f (snd (nth i ps (Pwild, Ftrue))))).
      split; wf_tac. exists (nth i ps (Pwild, Ftrue)). split; wf_tac.
      rewrite in_app_iff; triv.
    + rewrite H0; wf_tac. intro C.
      apply Hbnd. rewrite in_app_iff. right. 
      rewrite in_concat. exists ((pat_fv (fst (nth i ps (Pwild, Ftrue))))
      ++ (bnd_f (snd (nth i ps (Pwild, Ftrue))))).
      split; wf_tac. exists (nth i ps (Pwild, Ftrue)). split; wf_tac.
      rewrite in_app_iff; triv.
Qed. 

Corollary sub_t_fv_in (t: term):
  (forall (x y: vsymbol)
    (Hbnd: ~ In y (bnd_t t)),
    x <> y ->
    free_in_t y (sub_t x y t) = (free_in_t x t) || (free_in_t y t)). 
Proof. apply sub_fv_in. apply Ftrue. Qed.

Corollary sub_f_fv_in (f: formula):
  (forall (x y: vsymbol)
    (Hbnd: ~ In y (bnd_f f)),
    x <> y ->
    free_in_f y (sub_f x y f) = (free_in_f x f) || (free_in_f y f)).
Proof. apply sub_fv_in. apply tm_d. Qed.

(*Analagous lemmas for term/formula in [alpha_p_aux]. These 
  are much harder*)

(*1. For any vsymbol not in the free vars of p and not in
  the free vars of the resulting pattern,  
  [alpha_p_aux] does not change the result*)

Lemma alpha_p_aux_diff {A: Type} (sub: vsymbol -> vsymbol -> A -> A)
(p: pattern) (t: A) (l: list (vsymbol * string))
(free_in: vsymbol -> A -> bool)
(Hsub: forall a x y z, z <> x -> z <> y -> 
  free_in z (sub x y a) = free_in z a)
(Hnodup: NoDup(map fst l))
(Hallin: forall v, In v (pat_fv p) -> In v (map fst l)):
forall x, ~In x (pat_fv p) ->
  ~ In x (pat_fv (fst (alpha_p_aux sub p t l))) ->
   free_in x (snd (alpha_p_aux sub p t l)) = free_in x t.
Proof.
  intros x.
  (*This makes it usable with our IH for constr case*)
  rewrite alpha_p_aux_wf_aux_gen'; auto.
  generalize dependent t.
  induction p; simpl in *; intros; auto.
  - destruct (get_assoc_list vsymbol_eq_dec l v) eqn : ha; auto.
    simpl. rewrite Hsub; auto.
    intro Heq; subst.
    apply get_assoc_list_some in ha.
    apply H0. simpl. exists v. exists s. split_all; auto.
  - generalize dependent t. induction ps; simpl; intros; auto.
    inversion H; subst.
    rewrite IHps; auto.
    + simpl in H0. simpl_set. rewrite H4; auto.
      * intros. apply Hallin. simpl; simpl_set; triv.
      * intros [v [str [Hinvst [Hinv [Hsnd Hfst]]]]]; subst.
        apply H1. exists v. exists (fst x). split_all; auto.
        simpl; simpl_set; triv.
    + intros. apply Hallin. simpl; simpl_set; triv.
    + simpl in H0. rewrite union_elts in H0.
      intro C. apply H0. triv.
    + intros [v [str [Hinvstr [Hinv [Hsnd Hfst]]]]]; subst.
      apply H1. exists v. exists (fst x). split_all; auto.
      simpl. simpl_set; triv.
  - rewrite IHp2; auto.
    + intros. apply Hallin. simpl_set; triv.
    + intro C. apply H. simpl_set; triv.
    + intros [v [str [Hinv1 [Hinv2 [Hfst Hsnd]]]]]; subst.
      apply H0. exists v. exists (fst x). split_all; auto.
      simpl_set; triv.
  - destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha; auto.
    simpl. rewrite Hsub; auto.
    + apply IHp.
      * intros; apply Hallin; simpl_set; triv.
      * intro C. apply H. simpl_set; triv.
      * intros [v' [str [Hinv1 [Hinv2 [Hfst Hsnd]]]]]; subst.
        apply H0. exists v'. exists (fst x). split_all; auto.
        simpl_set; triv.
    + intro Heq; subst. apply H. simpl_set; triv.
    + intro Heq; subst. apply H0. simpl.
      apply get_assoc_list_some in Ha.
      exists v. exists s. split_all; auto. simpl_set; triv.
Qed.

(*TODO: move these*)
Lemma sub_t_in_implies (t: term): forall z x y,
  free_in_t z (sub_t x y t) ->
  (free_in_t z t /\ z <> x) \/ z = y.
Proof.
  intros. vsym_eq x y.
  - rewrite sub_t_eq in H. vsym_eq z y.
  - vsym_eq z x.
    + rewrite (sub_t_fv_notin _ _ _ n) in H. inversion H.
    + vsym_eq z y.
      rewrite sub_t_fv_diff in H; auto.
Qed.

Lemma sub_f_in_implies (f: formula): forall z x y,
  free_in_f z (sub_f x y f) ->
  (free_in_f z f /\ z <> x) \/ z = y.
Proof.
  intros. vsym_eq x y.
  - rewrite sub_f_eq in H. vsym_eq z y.
  - vsym_eq z x.
    + rewrite (sub_f_fv_notin _ _ _ n) in H. inversion H.
    + vsym_eq z y.
      rewrite sub_f_fv_diff in H; auto.
Qed.

(*1.5: Every variable free in the result is free in the term or
  is free in the new pattern*)
Lemma alpha_p_aux_in_implies {A: Type} (sub: vsymbol -> vsymbol -> A -> A)
  (p: pattern) (t: A) (l: list (vsymbol * string))
  (free_in: vsymbol -> A -> bool) (ty: vty)
  (Hty: pattern_has_type sigma p ty)
  (Hsub: forall z x y a, free_in z (sub x y a) ->
    (free_in z a /\ z <> x) \/ z = y)
  (Hallin: forall x, In x (pat_fv p) -> In x (map fst l))
  (Hnodup: NoDup (map fst l)) :
  forall x, free_in x (snd (alpha_p_aux sub p t l)) ->
    (free_in x t /\ ~In x (pat_fv p)) \/ 
      In x (pat_fv(fst (alpha_p_aux sub p t l))).
Proof.
  intros.
  rewrite alpha_p_aux_wf_aux_gen'; auto.
  intros; generalize dependent ty; generalize dependent t; induction p; simpl in *; intros.
  - destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha;
    simpl in H.
    + apply Hsub in H. destruct H as [[Hfree Hneq] | Heq]; subst; try triv.
      * left. split; auto. intro C; destruct_all; subst; auto; try contradiction.
      * right. simpl. exists v. exists s. split_all; auto.
        apply get_assoc_list_some in Ha; auto.
    + apply get_assoc_list_none in Ha. exfalso. apply Ha. apply Hallin.
      triv. 
  - generalize dependent t.
    inversion Hty; subst.
    revert H9. clear H3 H4 H7 H10 Hty.
    assert (length ps = length (map sigma0 (s_args f))) by (rewrite map_length; auto).
    revert H0; clear H5.
    generalize dependent (map sigma0 (s_args f)).
    induction ps; simpl; intros; auto.
    inversion H; subst.
    destruct l0; inversion H0.
    inversion H9; subst. simpl in H7.
    eapply IHps in H1; auto. 3: apply H3.
    + destruct H1.
      * destruct H1. eapply H4 in H1. 3: apply H7.
        -- destruct H1.
          ++ destruct H1. left. split; auto.
            simpl_set. intro C. destruct C; contradiction.
          ++ right. destruct H1 as [v' [str[Hinv1 [Hinv2 [Hfst Hsnd]]]]]; subst.
            exists v'. exists (fst x). split_all; auto.
            simpl_set; triv.
        -- intros; apply Hallin; simpl; simpl_set; triv.
      * right. destruct H1 as [v' [str[Hinv1 [Hinv2 [Hfst Hsnd]]]]]; subst.
        exists v'. exists (fst x). split_all; auto. simpl_set; triv.
    + intros; apply Hallin; simpl; simpl_set; triv.
    + auto. 
  - triv. 
  - inversion Hty; subst. 
    eapply IHp2 in H. 3: apply H4.
    + destruct H; try triv.
      * destruct H. left. split; auto. simpl_set.
        intros [Hinx | Hinx]; try contradiction.
        (*Need typing to know that free vars the same*)
        rewrite H6 in Hinx. contradiction.
      * right. destruct H as [v' [str[Hinv1 [Hinv2 [Hfst Hsnd]]]]]; subst.
        exists v'; exists (fst x); split_all; auto; simpl_set; triv.
    + intros; apply Hallin; simpl; simpl_set; triv.
  - inversion Hty; subst. 
    destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha;
    simpl in H.
    + apply Hsub in H. destruct H; subst; simpl; try triv.
      * destruct H. eapply IHp in H. 3: apply H5.
        -- destruct_all; try triv.
          ++ left.
            split; auto; simpl_set. intros [C | C]; subst; auto.
          ++ right. exists x0. exists (fst x). split_all; auto. simpl_set; triv. 
        -- intros; apply Hallin; simpl; simpl_set; triv.
      * right. apply get_assoc_list_some in Ha.
        exists v. exists s. split_all; auto. simpl_set. triv.
    + apply get_assoc_list_none in Ha.
      exfalso. apply Ha. apply Hallin. simpl_set. triv.
Qed.

(*2. For any vsymbol in the free vars of p, and the free vars
  of the new pattern. it is not free in the result. This is quite
  hard to show*)
Lemma alpha_p_aux_notin {A: Type} (sub: vsymbol -> vsymbol -> A -> A)
  (p: pattern) (t: A) (l: list (vsymbol * string))
  (free_in: vsymbol -> A -> bool) ty
  (Hty: pattern_has_type sigma p ty)
  (Hsub1: forall x y a, x <> y -> free_in x (sub x y a) = false)
  (Hsub2: forall z x y a, free_in z (sub x y a) ->
    (free_in z a /\ z <> x) \/ z = y)
  (Hfree: forall x, In (fst x) (map snd l) -> ~ In x (pat_fv p))
  (Hallin: forall x, In x (pat_fv p) -> In x (map fst l))
  (Hnodup: NoDup (map fst l)):
  forall x, In x (pat_fv p) ->
  ~In x (pat_fv (fst (alpha_p_aux sub p t l))) ->
  free_in x (snd (alpha_p_aux sub p t l)) = false.
Proof.
  intros. rewrite alpha_p_aux_wf_aux_gen' in H0; auto.
  generalize dependent ty. 
  generalize dependent t.
  induction p; intros; simpl in H; simpl.
  - destruct H as [Heq | []]; subst.
    destruct (get_assoc_list vsymbol_eq_dec l x) eqn : Ha.
    + simpl. apply Hsub1. intro Hx.
      apply (Hfree x); simpl; try triv.
      rewrite Hx. simpl.
      apply get_assoc_list_some in Ha.
      rewrite in_map_iff. exists (x, s); auto.
    + apply get_assoc_list_none in Ha.
      exfalso. apply Ha. apply Hallin; simpl; triv.
  - assert (In x (big_union vsymbol_eq_dec pat_fv ps) \/ free_in x t = false) by triv.
    clear H. (*Need weaker statement for IH*)
    inversion Hty; subst.
    revert H11. clear H5 H6 H9 H12 Hty.
    assert (length ps = length (map sigma0 (s_args f))) by (rewrite map_length; auto).
    revert H; clear H7.
    generalize dependent (map sigma0 (s_args f)). clear sigma0.
    generalize dependent t.  induction ps; simpl; intros; auto.
    + destruct H2 as [[] |]; auto.
    + simpl in *.
      destruct l0; inversion H.
      inversion H11; subst. simpl in H6.
    (*TODO: think need separate lemma for base case see*)
      destruct H2.
      * inversion H1; subst. eapply IHps; [| | | | |apply H4 |]; auto.
        -- intros y Hiny C.
          apply (Hfree y); auto. simpl_set; triv.
        -- intros. apply Hallin. simpl_set; triv.
        -- intros [v' [str [Hinv1 [Hinv2 [Hsnd Hfst]]]]]; subst.
          apply H0. exists v'. exists (fst x). split_all; auto.
          simpl_set; triv.
        -- rewrite union_elts in H2.
          destruct H2.
          (*Why we need weaker IH*)
          ++ right. eapply H8; [| | | | apply H6]; auto.
            ** intros y Hiny C.
              apply (Hfree y); auto. simpl_set; triv.
            ** intros; apply Hallin; simpl_set; triv.
            ** intros [v' [str [Hinv1 [Hinv2 [Hsnd Hfst]]]]]; subst.
              apply H0. exists v'. exists (fst x). split_all; auto.
              simpl_set; triv.
          ++ left; auto.
      * (*Prove this by separate inductive lemma - this is annoying*)
        (*We need to prove this part twice - can we improve?*)
        destruct (free_in x (snd (alpha_p_aux sub a t l))) eqn : Hfreext.
        {
          eapply alpha_p_aux_in_implies in Hfreext; [| apply H6 | | |]; auto.
          - exfalso. destruct Hfreext.
            + destruct H3; rewrite H3 in H2; inversion H2.
            + rewrite alpha_p_aux_wf_aux_gen' in H3; auto.
              apply H0. destruct H3 as [v' [str [Hinv1 [Hinv2 [Hsnd Hfst]]]]]; subst.
              exists v'. exists (fst x). split_all; auto. 
              simpl_set; triv.
              intros; apply Hallin. simpl_set; triv.
          - intros. apply Hallin. simpl_set; triv.
          }
        (*Also need to know type*)
        generalize dependent (snd (alpha_p_aux sub a t l)).
        revert H7. revert H4. 
        assert (~
        (exists (v : vsymbol) (str : string),
           In (v, str) l /\
           In v
                (big_union vsymbol_eq_dec pat_fv ps) /\
           snd x = snd v /\ fst x = str)). {
            intros [v' [str [Hinv1 [Hinv2 [Hfst Hsnd]]]]]; subst.
            apply H0. exists v'. exists (fst x). split_all; auto.
            simpl_set; triv.
           }
          revert H3.
          clear -sigma Hnodup Hallin Hsub2. (*TODO: see if we need anything*)
          revert l0.
          induction ps; simpl; intros; auto.
          destruct l0; inversion H4.
          inversion H7; subst.
          eapply IHps; [| | apply H0 | |]; auto.
          -- intros. apply Hallin. simpl. simpl_set. 
            destruct H; try triv. simpl_set. triv.
          -- intros [v' [str [Hinv1 [Hinv2 [Hsnd Hfst]]]]]; subst.
            apply H3. exists v'. exists (fst x). split_all; auto.
            simpl_set; triv.
          -- (*TODO: prev lemma - can we avoid repeating?*)
            destruct (free_in x (snd (alpha_p_aux sub a0 a1 l))) eqn : Hfree; auto.
            eapply alpha_p_aux_in_implies in Hfree; [| apply H2 | | |]; auto.
            ++ exfalso. destruct Hfree.
              ** destruct H; rewrite Hfreext in H; auto.
              ** rewrite alpha_p_aux_wf_aux_gen' in H; auto.
                apply H3. destruct H as [v' [str [Hinv1 [Hinv2 [Hsnd Hfst]]]]]; subst.
                exists v'. exists (fst x). split_all; auto. 
                simpl_set; triv.
                intros; apply Hallin. simpl; simpl_set; triv.
            ++ intros. apply Hallin. simpl; simpl_set; triv.
  - destruct H.
  - inversion Hty; subst.
    simpl_set.
    eapply IHp2; [| | | | apply H5]; auto.
    + intros y Hiny C; apply (Hfree y); auto; simpl; simpl_set; triv.
    + intros; apply Hallin; simpl; simpl_set; triv.
    + destruct H; auto. apply H7; auto.
    + intros [v [str [Hinv1 [Hinv2 [Hsnd Hfst]]]]]; subst.
      apply H0. exists v. exists (fst x). split_all; auto.
      simpl. simpl_set; triv.
  - inversion Hty; subst. 
    destruct (get_assoc_list vsymbol_eq_dec l v) eqn : Ha.
    + simpl.
      simpl_set. destruct H as [Hinx | [Hxv | []]]; subst.
      * destruct (free_in x (sub v (s, snd v) (snd (alpha_p_aux sub p t l)))) eqn : Hfreex; auto.
        apply Hsub2 in Hfreex. destruct Hfreex.
        -- destruct H.
          eapply alpha_p_aux_in_implies in H; [| apply H6 | | |]; auto.
          destruct H.
          ++ destruct H; contradiction.
          ++ rewrite alpha_p_aux_wf_aux_gen' in H; auto.
            ** destruct H as [v1 [str [Hinv1 [Hinv2 [Hsnd Hfst]]]]]; subst.
              exfalso. apply H0. exists v1. exists (fst x).
              split_all; auto. simpl. simpl_set; triv.
            ** intros; apply Hallin; simpl; simpl_set; triv.
          ++ intros; apply Hallin; simpl; simpl_set; triv.
        -- subst. apply get_assoc_list_some in Ha.
          exfalso. apply H0. exists v. exists s. split_all; auto.
          simpl; simpl_set; triv.
      * rewrite Hsub1; auto. intro; subst.
        apply H0.
        apply get_assoc_list_some in Ha.
        exists x. exists s. split_all; auto. simpl; simpl_set; triv.
        rewrite H; auto.
    + simpl. apply get_assoc_list_none in Ha.
      exfalso. apply Ha. apply Hallin; simpl; simpl_set; triv.
Qed.

Ltac prove_hyp H :=
  match goal with
  | H: ?P -> ?Q |- _ => let N := fresh in assert (N: P); [|specialize (H N); clear N]
  end.

Ltac prove_hyps n H :=
  match constr:(n) with
  | O => idtac
  | (S ?m) => prove_hyp H; [|prove_hyps m H]
  end.

Ltac vsym_eq2 x y z :=
  let H := fresh in
  assert (H: x = y \/ (x <> y /\ x = z) \/ (x <> y /\ x <> z)) by
  (vsym_eq x y; right; vsym_eq x z);
  destruct H as [? | [[? ?]|[? ?]]].

(*The big lemma we want: the free vars of [alpha_t_aux] and
  [alpha_f_aux] are the same as those of the original terms.
  This is very hard to prove, though very intuitive*)
Lemma alpha_aux_fv (t: term) (f: formula) :
  (forall (ty: vty)
    (Hty: term_has_type sigma t ty)
    (l: list string)
    (Hnodupl: NoDup l)
    (Hlen: length l = length (bnd_t t))
    (Hfree: forall x, In (fst x) l -> ~ In x (term_fv t))
    (Hbnd: forall x, In (fst x) l -> ~ In x (bnd_t t)),
    forall x,
    free_in_t x (alpha_t_aux t l) = free_in_t x t) /\
  (forall 
    (Hval: valid_formula sigma f)
    (l: list string)  
    (Hnodupl: NoDup l)
    (Hlen: length l = length (bnd_f f))
    (Hfree: forall x, In (fst x) l -> ~ In x (form_fv f))
    (Hbnd: forall x, In (fst x) l -> ~ In x (bnd_f f)),
    forall x,
    free_in_f x (alpha_f_aux f l) = free_in_f x f).
Proof.
  revert t f. apply term_formula_ind; simpl; auto; intros; try reflexivity.
  - apply existsb_eq; wf_tac.
    revert H. rewrite !Forall_forall; intros.
    revert H0. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d).
    subst; simpl. rewrite map2_nth with(d1:=tm_d)(d2:=nil); wf_tac.
    assert (term_has_type sigma (nth i l1 tm_d) (nth i (map (ty_subst (s_params f1) l) (s_args f1)) vty_int)).
    {
      inversion Hty; subst. rewrite Forall_forall in H10.

      specialize (H10 (nth i l1 tm_d, (nth i (map (ty_subst (s_params f1) l) (s_args f1)) vty_int))).
      apply H10. rewrite in_combine_iff; wf_tac.
      exists i. split; auto; intros; f_equal; apply nth_indep; wf_tac. 
    }
    eapply H; [| apply H0 | | | |]; wf_tac; intros y Hiny C; apply in_split_lens_ith in Hiny; wf_tac.
    + apply (Hfree y); simpl_set; auto.
      exists (nth i l1 tm_d). split; wf_tac.
    + apply (Hbnd y); auto. rewrite in_concat.
      exists (bnd_t (nth i l1 tm_d)). split; wf_tac.
  - (*Let - this case is complicated because we are binding variables*) 
    destruct l; inversion Hlen.
    simpl. inversion Hnodupl; subst.
    inversion Hty; subst.
    erewrite H; [| apply H9 | | | |]; wf_tac; try(intros y Hiny C); [|apply (Hfree y) | apply (Hbnd y)];
    try(simpl; right; wf_tac); [|simpl_set; triv|rewrite in_app_iff; triv].
    f_equal.
    assert (v <> (s, snd v)). {
      intro C; subst. apply (Hbnd v); try triv. 
      left; rewrite C; auto.
    }
    specialize (H0 ty H10 (skipn (Datatypes.length (bnd_t tm1)) l)).
    prove_hyps 4 H0; wf_tac;
    try(intros y Hiny C); [apply (Hfree y) | apply (Hbnd y)|];
    try solve[simpl; right; wf_tac];
    [simpl_set; right; split; auto; intro Heq; subst;
      apply (Hbnd v); [right; wf_tac | left; auto]
    | rewrite in_app_iff; triv |].
    (*Now we proceed by cases depending on whether x = v,
      x = (s, snd v), or none of the above*)
    vsym_eq2 x v (s, snd v).
    + subst. rewrite sub_t_fv_notin; auto. simpl_bool.
      vsym_eq v v.
    + (*If x = (s, snd v)*)
      subst. vsym_eq (s, snd v) (s, snd v).
      rewrite sub_t_fv_in; auto.
      * rewrite !H0.
        vsym_eq (s, snd v) v. simpl.
        (*TODO: change Hfree to use [free_in_t]?*)
        symmetry. apply free_in_t_negb. intro Hin.
        apply (Hfree (s, snd v)). left; auto. 
        simpl_set. triv.
      * intro Hin. apply alpha_t_aux_wf in Hin; wf_tac.
        apply In_skipn in Hin.
        simpl in Hin. contradiction. (*contradicts NoDup*)
    + (*The last case is quite easy, nothing changes*) 
      rewrite sub_t_fv_diff; auto.
      vsym_eq x (s, snd v); simpl.
      vsym_eq x v; simpl.
      apply H0.
  - (*If case - hypotheses for IH's are annoying *)
    inversion Hty; subst.
    rewrite H, (H0 _ H8), (H1 _ H9); wf_tac; intros y Hiny C;
    [apply (Hfree y) | apply (Hbnd y) | apply (Hfree y) | apply (Hbnd y) |
    apply (Hfree y) | apply (Hbnd y)];
    try(apply (Hfree y)); try(apply (Hbnd y));
    try (apply In_skipn in Hiny); try (apply In_firstn in Hiny);
    wf_tac; simpl_set; try (rewrite !in_app_iff); triv.
  - (*Match case - let's see*)
    inversion Hty; subst.
    specialize (H _ H4 (firstn (Datatypes.length (bnd_t tm)) l)).
    prove_hyps 4 H; wf_tac; try(intros y Hiny C);
    [apply (Hfree y) | apply (Hbnd y) |]; wf_tac;
    [simpl_set; triv | rewrite in_app_iff; triv |].
    rewrite H. f_equal.
    apply existsb_eq; wf_tac.
    revert H0. rewrite !Forall_forall; intros.
    revert H1. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx (Pwild, tm_d) (Pwild, tm_d)).
    subst; simpl.
    rewrite map2_nth with(d1:=(Pwild, tm_d))(d2:=nil); wf_tac.
    assert (Hsum: sum
    (map
       (fun x0 : pattern * term =>
        Datatypes.length (pat_fv (fst x0)) + Datatypes.length (bnd_t (snd x0)))
       ps) = Datatypes.length l - Datatypes.length (bnd_t tm)). {
      rewrite Hlen, length_concat, map_map, minus_plus.
      f_equal. apply map_ext_in_iff; intros.
        rewrite app_length; auto.
    }
    (*Ok, so we are back where we were before*)
    match goal with
    | |- context [in_bool ?e ?x ?l] => destruct (in_bool_spec e x l)
    end; simpl.
    + (*If x is in the pattern free vars, then it is in l*)
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst (nth i ps (Pwild, tm_d))))); simpl; auto.
      symmetry. apply free_in_t_negb. intro Hinfree.
      apply alpha_p_aux_wf_aux in i0.
      * rewrite map_snd_combine in i0; wf_tac.
        apply In_firstn in i0.
        apply in_split_lens_ith in i0; wf_tac.
        apply (Hfree x); wf_tac. simpl_set.
        right. exists (nth i ps (Pwild, tm_d)).
        split; wf_tac.
        simpl_set. split; auto.
      * rewrite map_fst_combine; wf_tac.
      * intros. rewrite map_fst_combine; wf_tac.
    + (*Otherwise, x not in pattern free vars*)
      (*Need this result in 2 places*)
      assert (Hnotfree: forall x0 : string * vty,
      In (fst x0)
           (nth i
              (split_lens (skipn (Datatypes.length (bnd_t tm)) l)
                 (map
                    (fun x1 : pattern * term =>
                     Datatypes.length (pat_fv (fst x1)) +
                     Datatypes.length (bnd_t (snd x1))) ps)) []) ->
      ~ (In x0 (term_fv (snd (nth i ps (Pwild, tm_d)))) \/
        In x0 (pat_fv (fst (nth i ps (Pwild, tm_d)))))). {
        intros y Hy C.
        apply in_split_lens_ith in Hy; wf_tac.
        (*Do [pat_fv] first*)
        assert (~In y (pat_fv (fst (nth i ps (Pwild, tm_d))))). {
          (*Contradiction: y in l, so not bound in pattern,
            which is same as pattern free var*)
          intro Hnot.
          apply (Hbnd y); wf_tac.
          rewrite in_app_iff. right.
          rewrite in_concat. exists (pat_fv (fst (nth i ps (Pwild, tm_d))) ++
            bnd_t (snd (nth i ps (Pwild, tm_d)))). split; wf_tac.
          exists (nth i ps (Pwild, tm_d)); split; wf_tac.
          rewrite in_app_iff; triv.
        }
        destruct C; try contradiction.
        (*Here, contradicts [Hfree], need [pat_fv result]*)
        apply (Hfree y); simpl_set; wf_tac.
        right. exists (nth i ps (Pwild, tm_d)). split;
        auto; simpl_set; wf_tac. 
      }
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst (nth i ps (Pwild, tm_d))))); simpl.
      * (*If x in orig pattern free vars, need to show false*)
        assert (Hty': pattern_has_type sigma (fst (nth i ps (Pwild, tm_d))) v). {
          apply H6. wf_tac.
        }
        eapply alpha_p_aux_notin; [apply Hty' | | | | | | |]; wf_tac.
        -- intros; apply sub_t_fv_notin; auto.
        -- intros; apply sub_t_in_implies; auto.
        -- intros. apply In_firstn in H1. apply Hnotfree in H1.
          intro C; apply H1; triv.
      * rewrite alpha_p_aux_diff; wf_tac.
        assert (Hty': term_has_type sigma (snd (nth i ps (Pwild, tm_d))) ty). {
          apply H8; wf_tac.
        }
        -- erewrite H0; [| | apply Hty' | | | |]; wf_tac.
          ++ intros y Hy C.
            apply In_skipn in Hy.
            apply Hnotfree in Hy. apply Hy; triv.
          ++ intros y Hy C.
            apply In_skipn in Hy.
            apply in_split_lens_ith in Hy; wf_tac.
            apply (Hbnd y); wf_tac.
            rewrite in_app_iff; right.
            rewrite in_concat. exists (pat_fv (fst (nth i ps (Pwild, tm_d))) ++
              bnd_t (snd (nth i ps (Pwild, tm_d)))). split; wf_tac.
            exists (nth i ps (Pwild, tm_d)); split; wf_tac.
            rewrite in_app_iff; triv.
        -- apply sub_t_fv_diff.
  - (*Teps - basically same as let*) 
    destruct l; inversion Hlen. inversion Hty; subst. simpl.
    assert (v <> (s, snd v)). {
      intro C; subst. apply (Hbnd v); try triv. 
      left; rewrite C; auto.
    }
    inversion Hnodupl; subst.
    specialize (H H4 l).
    prove_hyps 4 H; wf_tac;
    try(intros y Hiny C); [apply (Hfree y) | apply (Hbnd y)|];
    try solve[simpl; right; wf_tac];
    simpl_set; auto.
    split; auto; intro Heq; subst.
    apply (Hbnd v); [right; wf_tac | left; auto].
    (*Now we proceed by cases depending on whether x = v,
      x = (s, snd v), or none of the above*)
    vsym_eq2 x v (s, snd v).
    + subst. rewrite sub_f_fv_notin; auto. simpl_bool.
      vsym_eq v v.
    + (*If x = (s, snd v)*)
      subst. vsym_eq (s, snd v) (s, snd v).
      rewrite sub_f_fv_in; auto.
      * rewrite !H.
        vsym_eq (s, snd v) v. simpl.
        (*TODO: change Hfree to use [free_in_t]?*)
        symmetry. apply free_in_f_negb. intro Hin.
        apply (Hfree (s, snd v)). left; auto. 
        simpl_set. triv.
      * intro Hin. apply alpha_f_aux_wf in Hin; wf_tac.
    + (*The last case is quite easy, nothing changes*) 
      rewrite sub_f_fv_diff; auto.
      vsym_eq x (s, snd v); simpl.
      vsym_eq x v; simpl.
      apply H.
  - (*Fpred*)
    apply existsb_eq; wf_tac.
    revert H. rewrite !Forall_forall; intros.
    revert H0. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx tm_d tm_d).
    subst; simpl. rewrite map2_nth with(d1:=tm_d)(d2:=nil); wf_tac.
    assert (term_has_type sigma (nth i tms tm_d) (nth i (map (ty_subst (p_params p) tys) (p_args p)) vty_int)).
    {
      inversion Hval; subst. rewrite Forall_forall in H8.

      specialize (H8 (nth i tms tm_d, (nth i (map (ty_subst (p_params p) tys) (p_args p)) vty_int))).
      apply H8. rewrite in_combine_iff; wf_tac.
      exists i. split; auto; intros; f_equal; apply nth_indep; wf_tac. 
    }
    eapply H; [| apply H0 | | | |]; wf_tac; intros y Hiny C; apply in_split_lens_ith in Hiny; wf_tac.
    + apply (Hfree y); simpl_set; auto.
      exists (nth i tms tm_d). split; wf_tac.
    + apply (Hbnd y); auto. rewrite in_concat.
      exists (bnd_t (nth i tms tm_d)). split; wf_tac.
  - (*Fquant -similar to let/eps*)
    destruct l; inversion Hlen.
    inversion Hnodupl;subst.
    inversion Hval; subst.
    simpl.
    assert (v <> (s, snd v)). {
      intro C; subst. apply (Hbnd v); try triv. 
      left; rewrite C; auto.
    }
    specialize (H H8 l).
    prove_hyps 4 H; wf_tac;
    try(intros y Hiny C); [apply (Hfree y) | apply (Hbnd y)|];
    try solve[simpl; right; wf_tac];
    simpl_set; auto.
    split; auto; intro Heq; subst.
    apply (Hbnd v); [right; wf_tac | left; auto].
    (*Now we proceed by cases depending on whether x = v,
      x = (s, snd v), or none of the above*)
    vsym_eq2 x v (s, snd v).
    + subst. rewrite sub_f_fv_notin; auto. simpl_bool.
      vsym_eq v v.
    + (*If x = (s, snd v)*)
      subst. vsym_eq (s, snd v) (s, snd v).
      rewrite sub_f_fv_in; auto.
      * rewrite !H.
        vsym_eq (s, snd v) v. simpl.
        (*TODO: change Hfree to use [free_in_t]?*)
        symmetry. apply free_in_f_negb. intro Hin.
        apply (Hfree (s, snd v)). left; auto. 
        simpl_set. triv.
      * intro Hin. apply alpha_f_aux_wf in Hin; wf_tac.
    + (*The last case is quite easy, nothing changes*) 
      rewrite sub_f_fv_diff; auto.
      vsym_eq x (s, snd v); simpl.
      vsym_eq x v; simpl.
      apply H.
  - (*Feq*)
    inversion Hval; subst.
    rewrite (H _ H4), (H0 _ H6); wf_tac; intros y Hiny C;
    try solve[(apply (Hfree y); wf_tac; simpl_set; triv)];
    apply (Hbnd y); wf_tac; rewrite in_app_iff; triv.
  - (*Fbinop*)
    inversion Hval; subst.
    rewrite (H  H4), (H0 H6); wf_tac; intros y Hiny C;
    try solve[(apply (Hfree y); wf_tac; simpl_set; triv)];
    apply (Hbnd y); wf_tac; rewrite in_app_iff; triv.
  - apply H; wf_tac. inversion Hval; subst; auto.
  - (*Flet*)
    destruct l; inversion Hlen.
    simpl. inversion Hnodupl; subst.
    inversion Hval; subst.
    erewrite H; [| apply H7 | | | |]; wf_tac; try(intros y Hiny C); [|apply (Hfree y) | apply (Hbnd y)];
    try(simpl; right; wf_tac); [|simpl_set; triv|rewrite in_app_iff; triv].
    f_equal.
    assert (v <> (s, snd v)). {
      intro C; subst. apply (Hbnd v); try triv. 
      left; rewrite C; auto.
    }
    specialize (H0 H9 (skipn (Datatypes.length (bnd_t tm)) l)).
    prove_hyps 4 H0; wf_tac;
    try(intros y Hiny C); [apply (Hfree y) | apply (Hbnd y)|];
    try solve[simpl; right; wf_tac];
    [simpl_set; right; split; auto; intro Heq; subst;
      apply (Hbnd v); [right; wf_tac | left; auto]
    | rewrite in_app_iff; triv |].
    (*Now we proceed by cases depending on whether x = v,
      x = (s, snd v), or none of the above*)
    vsym_eq2 x v (s, snd v).
    + subst. rewrite sub_f_fv_notin; auto. simpl_bool.
      vsym_eq v v.
    + (*If x = (s, snd v)*)
      subst. vsym_eq (s, snd v) (s, snd v).
      rewrite sub_f_fv_in; auto.
      * rewrite !H0.
        vsym_eq (s, snd v) v. simpl.
        (*TODO: change Hfree to use [free_in_t]?*)
        symmetry. apply free_in_f_negb. intro Hin.
        apply (Hfree (s, snd v)). left; auto. 
        simpl_set. triv.
      * intro Hin. apply alpha_f_aux_wf in Hin; wf_tac.
        apply In_skipn in Hin.
        simpl in Hin. contradiction. (*contradicts NoDup*)
    + (*The last case is quite easy, nothing changes*) 
      rewrite sub_f_fv_diff; auto.
      vsym_eq x (s, snd v); simpl.
      vsym_eq x v; simpl.
      apply H0.
  - (*Fif*)
    inversion Hval; subst.
    rewrite H, H0, H1; wf_tac; intros y Hiny C;
    [apply (Hfree y) | apply (Hbnd y) | apply (Hfree y) | apply (Hbnd y) |
    apply (Hfree y) | apply (Hbnd y)];
    try(apply (Hfree y)); try(apply (Hbnd y));
    try (apply In_skipn in Hiny); try (apply In_firstn in Hiny);
    wf_tac; simpl_set; try (rewrite !in_app_iff); triv.
  - (*Fmatch - copied and pasted*)
    inversion Hval; subst.
    specialize (H _ H4 (firstn (Datatypes.length (bnd_t tm)) l)).
    prove_hyps 4 H; wf_tac; try(intros y Hiny C);
    [apply (Hfree y) | apply (Hbnd y) |]; wf_tac;
    [simpl_set; triv | rewrite in_app_iff; triv |].
    rewrite H. f_equal.
    apply existsb_eq; wf_tac.
    revert H0. rewrite !Forall_forall; intros.
    revert H1. rewrite in_combine_iff; wf_tac.
    intros [i [Hi Hx]]. specialize (Hx (Pwild, Ftrue) (Pwild, Ftrue)).
    subst; simpl.
    rewrite map2_nth with(d1:=(Pwild, Ftrue))(d2:=nil); wf_tac.
    assert (Hsum: sum
    (map
      (fun x0 : pattern * formula =>
        Datatypes.length (pat_fv (fst x0)) + Datatypes.length (bnd_f (snd x0)))
      ps) = Datatypes.length l - Datatypes.length (bnd_t tm)). {
      rewrite Hlen, length_concat, map_map, minus_plus.
      f_equal. apply map_ext_in_iff; intros.
        rewrite app_length; auto.
    }
    (*Ok, so we are back where we were before*)
    match goal with
    | |- context [in_bool ?e ?x ?l] => destruct (in_bool_spec e x l)
    end; simpl.
    + (*If x is in the pattern free vars, then it is in l*)
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst (nth i ps (Pwild, Ftrue))))); simpl; auto.
      symmetry. apply free_in_f_negb. intro Hinfree.
      apply alpha_p_aux_wf_aux in i0.
      * rewrite map_snd_combine in i0; wf_tac.
        apply In_firstn in i0.
        apply in_split_lens_ith in i0; wf_tac.
        apply (Hfree x); wf_tac. simpl_set.
        right. exists (nth i ps (Pwild, Ftrue)).
        split; wf_tac.
        simpl_set. split; auto.
      * rewrite map_fst_combine; wf_tac.
      * intros. rewrite map_fst_combine; wf_tac.
    + (*Otherwise, x not in pattern free vars*)
      (*Need this result in 2 places*)
      assert (Hnotfree: forall x0 : string * vty,
      In (fst x0)
          (nth i
              (split_lens (skipn (Datatypes.length (bnd_t tm)) l)
                (map
                    (fun x1 : pattern * formula =>
                    Datatypes.length (pat_fv (fst x1)) +
                    Datatypes.length (bnd_f (snd x1))) ps)) []) ->
      ~ (In x0 (form_fv (snd (nth i ps (Pwild, Ftrue)))) \/
        In x0 (pat_fv (fst (nth i ps (Pwild, Ftrue)))))). {
        intros y Hy C.
        apply in_split_lens_ith in Hy; wf_tac.
        (*Do [pat_fv] first*)
        assert (~In y (pat_fv (fst (nth i ps (Pwild, Ftrue))))). {
          (*Contradiction: y in l, so not bound in pattern,
            which is same as pattern free var*)
          intro Hnot.
          apply (Hbnd y); wf_tac.
          rewrite in_app_iff. right.
          rewrite in_concat. exists (pat_fv (fst (nth i ps (Pwild, Ftrue))) ++
            bnd_f (snd (nth i ps (Pwild, Ftrue)))). split; wf_tac.
          exists (nth i ps (Pwild, Ftrue)); split; wf_tac.
          rewrite in_app_iff; triv.
        }
        destruct C; try contradiction.
        (*Here, contradicts [Hfree], need [pat_fv result]*)
        apply (Hfree y); simpl_set; wf_tac.
        right. exists (nth i ps (Pwild, Ftrue)). split;
        auto; simpl_set; wf_tac. 
      }
      destruct (in_bool_spec vsymbol_eq_dec x (pat_fv (fst (nth i ps (Pwild, Ftrue))))); simpl.
      * (*If x in orig pattern free vars, need to show false*)
        assert (Hty': pattern_has_type sigma (fst (nth i ps (Pwild, Ftrue))) v). {
          rewrite Forall_forall in H6; apply H6. wf_tac.
        }
        eapply alpha_p_aux_notin; [apply Hty' | | | | | | |]; wf_tac.
        -- intros; apply sub_f_fv_notin; auto.
        -- intros; apply sub_f_in_implies; auto.
        -- intros. apply In_firstn in H1. apply Hnotfree in H1.
          intro C; apply H1; triv.
      * rewrite alpha_p_aux_diff; wf_tac.
        assert (Hty': valid_formula sigma (snd (nth i ps (Pwild, Ftrue)))). {
          rewrite Forall_forall in H7; apply H7; wf_tac.
        }
        -- erewrite H0; [| | apply Hty' | | | |]; wf_tac.
          ++ intros y Hy C.
            apply In_skipn in Hy.
            apply Hnotfree in Hy. apply Hy; triv.
          ++ intros y Hy C.
            apply In_skipn in Hy.
            apply in_split_lens_ith in Hy; wf_tac.
            apply (Hbnd y); wf_tac.
            rewrite in_app_iff; right.
            rewrite in_concat. exists (pat_fv (fst (nth i ps (Pwild, Ftrue))) ++
              bnd_f (snd (nth i ps (Pwild, Ftrue)))). split; wf_tac.
            exists (nth i ps (Pwild, Ftrue)); split; wf_tac.
            rewrite in_app_iff; triv.
        -- apply sub_f_fv_diff.
Qed.

(*Finally, we need to prove that the [alpha] functions
  do not change the meaning of the term/formula (since we
  only rename bound variables)*)

Context {pd: pi_dom} (all_unif: forall m, mut_in_ctx m gamma -> IndTypes.uniform m)
  {vt: @val_typevar sigma} {pf: pi_funpred gamma_valid pd}.

Notation term_rep := (term_rep gamma_valid pd all_unif vt pf).
Notation formula_rep := (formula_rep gamma_valid pd all_unif vt pf).


Require Import Coq.Logic.Eqdep_dec.

Lemma alpha_aux_rep (t: term) (f: formula) :
  (forall (vv: val_vars pd vt) (l: list string) (ty: vty)
  (Hty: term_has_type sigma t ty)
  (Hty2: term_has_type sigma (alpha_t_aux t l) ty),
  NoDup l ->
  length l = length (bnd_t t) ->
  term_rep vv t ty Hty =
  term_rep vv (alpha_t_aux t l) ty Hty2) /\
  (forall (vv: val_vars pd vt) (l: list string)
  (Hval: valid_formula sigma f)
  (Hval2: valid_formula sigma (alpha_f_aux f l)),
  NoDup l ->
  length l = length (bnd_f f) ->
  formula_rep vv f Hval =
  formula_rep vv (alpha_f_aux f l) Hval2).
Proof.
  revert t f; apply term_formula_ind; simpl; intros; auto;
  try solve[apply term_rep_irrel].
  - rewrite !tfun_rep.
    f_equal.
    apply UIP_dec. apply vty_eq_dec.
    f_equal. apply UIP_dec. apply sort_eq_dec.
    (*casting is done*)
    f_equal.
    apply get_arg_list_ext; wf_tac.
    intros i Hi ty' Htya Htyb.
    revert Htyb.
    rewrite map2_nth with(d1:=tm_d)(d2:=nil); simpl; intros; wf_tac.
    rewrite Forall_forall in H; apply H; wf_tac.
  - destruct l; [apply term_rep_irrel|].
    inversion H2; subst.
    inversion H1; subst.
    assert (Hty3: term_has_type sigma
    (Tlet (alpha_t_aux tm1 (firstn (Datatypes.length (bnd_t tm1)) l)) v
       (alpha_t_aux tm2 (skipn (Datatypes.length (bnd_t tm1)) l))) ty). {
        inversion Hty; subst.
        constructor; apply alpha_t_aux_type; wf_tac.
    }
    rewrite <- alpha_convert_tlet with(Hty1:=Hty3); wf_tac.
    + rewrite !tlet_rep.
      rewrite (H vv (firstn (length (bnd_t tm1)) l) (snd v)
      (proj1 (ty_let_inv (has_type_eq eq_refl Hty)))
      (proj1 (ty_let_inv (has_type_eq eq_refl Hty2)))); wf_tac.
      erewrite H0 with(Hty2:=(proj2 (ty_let_inv (has_type_eq eq_refl Hty3)))); wf_tac.
      erewrite (term_rep_irrel _ _ _ _ _ _ (alpha_t_aux tm1 _)).
      reflexivity.
    + intro C. apply alpha_t_aux_wf in C; wf_tac.
      simpl in C. apply In_skipn in C. contradiction.
    + intro C.
      (*TODO: prove that [alpha_t_aux] does not change free variables*)