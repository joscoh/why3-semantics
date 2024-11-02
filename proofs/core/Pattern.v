(*Compilation of pattern matches*)
Require Import Syntax Vars AssocList GenElts.
Set Bullet Behavior "Strict Subproofs".
From Equations Require Import Equations.
Require Import Coq.Sorting.Permutation.
Require Import Init.Wf.


Definition rev_map {B C: Type} (f: B -> C) (l: list B) : list C :=
  rev (map f l).

Section Compile.
Context {A: Type} (get_constructors: typesym -> list funsym) 
  (mk_case: term -> vty -> list (pattern * A) -> A) (mk_let: vsymbol -> term -> A -> A).

(*Part 1: Define parts of compile function. We separate out helper functions to make proofs easier*)

Definition add_case (fs: funsym) (pl: list pattern) (a: A) (cases : amap funsym (list (list pattern * A))) :=
    amap_change funsym_eq_dec (fun o =>
      match o with
      | None => [(pl, a)]
      | Some rl => (pl, a) :: rl
      end
    ) fs cases.

Definition union_cases (pl: list pattern) (a: A) (types: amap funsym (list pattern)) 
    (cases: amap funsym (list (list pattern * A))) : amap funsym (list (list pattern * A)) :=
    let add pl _ := Pwild :: pl in
    let wild (c: funsym) ql  := [(fold_left add ql pl, a)] in
    let join _ wl rl := Some (wl ++ rl) in
    amap_union funsym_eq_dec join (amap_map_key wild types) cases . 

(*Part 1: The dispatch function they implement in OCaml
  This is more efficient (1 pass) but harder to directly reason about*)

(*The induction is non-trivial - we recurse inside the pattern.
  We will need a version of this later for terms as well*)
Fixpoint pat_size (p: pattern) : nat :=
  match p with
  | Por p1 p2 => 1 + pat_size p1 + pat_size p2
  | Pbind p _ => 1 + pat_size p
  | Pconstr _ _ ps => 1 + sum (map pat_size ps)
  | _ => 1
  end.
Definition pat_list_size (l: list pattern) : nat :=
  sum (map pat_size l).
Lemma pat_list_size_cons p l :
  pat_list_size (p :: l) = pat_size p + pat_list_size l.
Proof.
  reflexivity.
Qed.

Section Dispatch.
Variable (t: term) (types: amap funsym (list pattern)) .
Equations dispatch (x: list pattern * A) 
  (y:  (amap funsym (list (list pattern * A))) * list (list pattern * A) ) : 
  (amap funsym (list (list pattern * A))) * list (list pattern * A) 
  by wf (pat_list_size (fst x)) lt  :=
  dispatch (nil, _) y := (*impossible*) y;
  dispatch (Pvar x :: pl, a) (cases, wilds) := 
    let a := mk_let x t a in
    (union_cases pl a types cases, (pl, a) :: wilds);
  dispatch (Pconstr fs _ pl' :: pl, a) (cases, wilds) :=
    (add_case fs (rev pl' ++ pl) a cases, wilds);
  dispatch (Pwild :: pl, a) (cases, wilds) :=
    (union_cases pl a types cases, (pl, a) :: wilds);
  dispatch (Por p q :: pl, a) (cases, wilds) :=
    dispatch (p :: pl, a) (dispatch (q :: pl, a) (cases, wilds));
  dispatch (Pbind p x :: pl, a) (cases, wilds) :=
    dispatch (p :: pl, mk_let x t a) (cases, wilds).
Next Obligation.
  rewrite !pat_list_size_cons. simpl. lia.
Defined.
Next Obligation.
  rewrite !pat_list_size_cons. simpl. lia.
Defined.

Definition dispatch1 rl := fold_right dispatch (amap_empty, nil) rl.

(*Part 2: An alternative that takes 2 stages: remove all var/bind/or patterns, 
  and then build map. This is structurally recursive and easier to reason about*)
Fixpoint simplify_aux (a: A) (p: pattern) : list (pattern * A) :=
  match p with
  | Pbind p1 x => (*map (fun '(p2, y) => (p2, mk_let x t y))*) (simplify_aux (mk_let x t a) p1)
  | Por p1 p2 => simplify_aux a p1 ++ simplify_aux a p2
  | Pvar x => [(Pwild, mk_let x t a)]
  | _ => [(p, a)]
  end.

Definition simplify_single (x: list pattern * A) : list (list pattern * A) :=
    let (ps, a) := x in
    match ps with
    | p :: ptl => 
      map (fun x => (fst x :: ptl, snd x)) (simplify_aux a p)
    | nil => [x]
    end.

Definition simplify (rl: list (list pattern * A)) : list (list pattern * A) :=
  concat (map simplify_single rl).

Definition dispatch2_aux (x: list pattern * A) 
  (y:  (amap funsym (list (list pattern * A))) * list (list pattern * A) ) : 
  (amap funsym (list (list pattern * A))) * list (list pattern * A) :=
  let (pl, a) := x in
  let (cases, wilds) := y in
  match pl with
  | p :: pl =>  
    match p with
    | Pconstr fs _ pl' => (add_case fs (rev pl' ++ pl) a cases, wilds)
    | Pwild => (union_cases pl a types cases, (pl, a) :: wilds)
    | _ => (*impossible*) (cases, wilds)
    end
  | nil => (cases, wilds) (*impossible if well-typed*)
  end.

Definition dispatch2_gen (rl: list (list pattern * A)) :
  amap funsym (list (list pattern * A)) * list (list pattern * A) :=
  fold_right dispatch2_aux (amap_empty, nil) rl.

Definition dispatch2 (rl: list (list pattern * A)) :=
  dispatch2_gen (simplify rl).

(*Prove equivalence between the two versions:*)

(*We need this for the odd induction principle*)
Lemma dispatch_equiv_aux x base :
  dispatch x base =
  fold_right dispatch2_aux base (simplify_single x).
Proof.
  apply dispatch_elim; auto.
  - intros. simpl. destruct y; auto.
  - intros p q pl a cases wilds IH1 IH2. simpl in *.
    rewrite map_app, fold_right_app.
    rewrite <- IH1; auto.
Qed.
 
(*Now we prove equivalence*)
Lemma dispatch_equiv rl:
  dispatch1 rl = dispatch2 rl.
Proof.
  unfold dispatch2, dispatch2_gen, dispatch1.
  induction rl as [|[pl a] ps IH]; simpl; auto.
  unfold simplify in *. simpl.
  rewrite fold_right_app.
  destruct pl as [| phd ptl]; simpl in *; try discriminate.
  - rewrite dispatch_equation_1. rewrite <- IH. destruct (fold_right dispatch (amap_empty, []) ps); auto. 
  - rewrite <- IH; auto. 
    destruct (fold_right dispatch (amap_empty, []) ps) as [cases1 wilds1] eqn : Hd2; auto.
    apply dispatch_equiv_aux.
Qed.


(*In why3, throw error if list is empty. We give an option version for this, then prove
  that it is equivalent to the existing version (which is simpler to reason about*)
Equations dispatch_opt (x: list pattern * A) 
  (y:  (amap funsym (list (list pattern * A))) * list (list pattern * A) ) : 
  option ((amap funsym (list (list pattern * A))) * list (list pattern * A))
  by wf (pat_list_size (fst x)) lt  :=
  dispatch_opt (nil, _) y := (*impossible*) None;
  dispatch_opt (Pvar x :: pl, a) (cases, wilds) := 
    let a := mk_let x t a in
    Some (union_cases pl a types cases, (pl, a) :: wilds);
  dispatch_opt (Pconstr fs _ pl' :: pl, a) (cases, wilds) :=
    Some (add_case fs (rev pl' ++ pl) a cases, wilds);
  dispatch_opt (Pwild :: pl, a) (cases, wilds) :=
    Some (union_cases pl a types cases, (pl, a) :: wilds);
  dispatch_opt (Por p q :: pl, a) (cases, wilds) :=
    option_bind (dispatch_opt (q :: pl, a) (cases, wilds)) (fun o =>
    dispatch_opt (p :: pl, a) o) ;
  dispatch_opt (Pbind p x :: pl, a) (cases, wilds) :=
    dispatch_opt (p :: pl, mk_let x t a) (cases, wilds).
Next Obligation.
  rewrite !pat_list_size_cons. simpl. lia.
Defined.
Next Obligation.
  rewrite !pat_list_size_cons. simpl. lia.
Defined.

Definition dispatch1_opt (rl: list (list pattern * A)) :
  option (amap funsym (list (list pattern * A)) * list (list pattern * A)) :=
  fold_right (fun x acc => option_bind acc (fun o => dispatch_opt x o)) (Some (amap_empty, nil)) rl.

Lemma dispatch_opt_none x acc:
  dispatch_opt x acc = None <-> null (fst x).
Proof.
  apply dispatch_opt_elim; intros; simpl in *; try solve[auto;split; auto; discriminate].
  destruct (dispatch_opt (q :: pl, a) (cases, wilds)); simpl; auto.
Qed.

Lemma dispatch_opt_some x acc l:
  dispatch_opt x acc = Some l <-> negb (null (fst x)) /\ l = dispatch x acc.
Proof.
  revert l. apply dispatch_opt_elim; intros; simpl;
  try solve [split; [intros Hsome; inversion Hsome; subst| intros [_ Hl]; subst]; auto].
  - split; intros; destruct_all; discriminate.
  - simpl in *. rewrite dispatch_equation_5. destruct (dispatch_opt (q :: pl, a) (cases, wilds)) as [l1 |] eqn : Hq; simpl.
    + rewrite H0. specialize (H l1). destruct H as [Hl1 _].
      specialize (Hl1 eq_refl). destruct Hl1; subst; auto. reflexivity.
    + split; try discriminate. apply dispatch_opt_none in Hq. discriminate.
  - rewrite dispatch_equation_6. apply H.
Qed. 

Lemma dispatch1_opt_none rl:
  dispatch1_opt rl = None <-> existsb (fun x => (null (fst x))) rl.
Proof.
  induction rl as [| rhd rtl IH]; simpl.
  - split; discriminate.
  - destruct (dispatch1_opt rtl) as [l1|] eqn : Htl.
    + simpl. rewrite dispatch_opt_none.
      unfold is_true.
      rewrite orb_true_iff, <- IH. split; intros; auto; destruct_all; auto; discriminate.
    + simpl. split; auto. intros _. destruct (null (fst rhd)); auto. simpl. apply IH. auto.
Qed. 

Lemma dispatch1_opt_some rl l:
  dispatch1_opt rl = Some l <->
  forallb (fun x => negb (null (fst x))) rl /\ l = dispatch1 rl.
Proof.
  revert l.
  induction rl as [|rhd rtl IH]; simpl; intros l.
  - split.
    + intros Hsome; inversion Hsome; subst; auto.
    + intros [_ Hl]; subst; auto.
  - destruct (dispatch1_opt rtl) as [ l1|] eqn : Htl .
    2: { simpl. apply dispatch1_opt_none in Htl.
      split; try discriminate. unfold is_true. rewrite andb_true_iff.
      intros [[Hnull Hall] Hl].
      exfalso.
      apply existsb_exists in Htl.
      rewrite forallb_forall in Hall.
      destruct Htl as [x [Hinx Hnullx]].
      specialize (Hall x Hinx). rewrite Hnullx in Hall. discriminate.
    }
    simpl.
    rewrite dispatch_opt_some.
    specialize (IH l1). destruct IH as [IH _]. specialize (IH eq_refl).
    destruct IH as [Hall Hl1]; subst. rewrite Hall. rewrite andb_true_r. reflexivity.
Qed.
End Dispatch.

(*More intermediate functions:*)

(*Populate: get first ocurrences of each constructor with the corresponding arguments, both as map
  and as list*)
Section Populate.
Variable (is_constr : funsym -> bool).
(*NOTE: populate will give option - want to ensure everything in pattern is constructor*)
Fixpoint populate  (acc : (amap funsym (list pattern) * list (funsym * list vty * list pattern))) 
        (p: pattern) : option (amap funsym (list pattern) * list (funsym * list vty * list pattern)) :=
        match p with
        | Pwild => Some acc
        | Pvar _ => Some acc
        | Pconstr fs params ps =>
            let (css, csl) := acc in
            if is_constr fs then
              if amap_mem funsym_eq_dec fs css then Some acc else
              Some (amap_set funsym_eq_dec css fs ps, (fs, params, ps) :: csl)
            else None (*exception - impossible by typing*)
        | Por p1 p2 => option_bind (populate acc p1) (fun x => populate x p2)
        | Pbind p _ => populate acc p
        end.
End Populate.

(*Avoid using List.hd*)
Definition get_heads (rl: list (list pattern * A)) : option (list pattern) :=
  (fold_right (fun x acc => match (fst x) with | nil => None | y :: _ => option_bind acc (fun acc => Some (y :: acc)) end)
     (Some []) rl).
Definition populate_all (is_constr: funsym -> bool) (rl: list (list pattern * A)) :=
  (*Get list*)
  match get_heads rl with
  | None => None
  | Some l =>
  fold_left_opt (populate is_constr) l
    (amap_empty, nil)
  end.

(*Part 2: The Matrices S and D*)

(*We now have all of the intermediate functions we need.
  Proving termination is very complicated.
  The first step is to give nicer declarative specifications for the results of [dispatch].
  [dispatch] populates all maps at once, which is efficient but difficult to reason about.
  Here we prove that, specialized to a given constructor, this function produces the
  matrices S and D from the paper*)

Definition pat_at_head (p: pattern) (r: list pattern * A) : bool :=
  match (fst r) with | p1 :: _ => pattern_eqb p p1 | _ => false end.
Definition constr_at_head (c: funsym) (r: list pattern * A) : bool :=
  match (fst r) with | Pconstr f _ _ :: _ => funsym_eqb f c | _ => false end.
Definition constr_at_head_ex cs rl := existsb (constr_at_head cs) rl.
Definition wild_at_head_ex rl := existsb (pat_at_head Pwild) rl.

(*Structural Lemmas*)
(*Here we relate the output of [dispatch2] to the matrices S and D from the paper, giving a nice
  functional specification. This is useful both in correctness and termination proofs*)

(*First structural lemma: if neither a constructor nor Pwild appears in the first column, 
  S is empty*)
Lemma dispatch2_gen_fst_notin (types: amap funsym (list pattern)) rl cs:
  amap_mem funsym_eq_dec cs types ->
  (constr_at_head_ex cs rl || wild_at_head_ex rl) = false <->
  amap_get funsym_eq_dec (fst (dispatch2_gen types rl)) cs = None.
Proof.
  intros Htypes. induction rl as [| [ps a] rtl IH]; simpl; [split; auto|].
  destruct (dispatch2_gen types rtl) as [cases wilds] eqn : Hd; simpl in *.
  unfold constr_at_head, pat_at_head;simpl.
  destruct ps as [| phd ptl]; simpl in *; auto.
  destruct phd; simpl; auto.
  - unfold add_case, amap_change. destruct (funsym_eqb_spec f cs); subst; simpl.
    + split; try discriminate.
      destruct (amap_get funsym_eq_dec cases cs) eqn : Hget.
      * erewrite amap_replace_get_same1. discriminate. apply Hget.
      * rewrite amap_replace_get_same2; auto. discriminate.
    + rewrite amap_replace_get_diff; auto.
  - rewrite orb_true_r. split; try discriminate.
    unfold union_cases.
    rewrite amap_mem_spec in Htypes.
    destruct (amap_get funsym_eq_dec types cs) eqn : Hget1; try discriminate.
    destruct (amap_get funsym_eq_dec cases cs) eqn : Hget2. 
    + erewrite amap_union_inboth. discriminate. erewrite amap_map_key_get_some. reflexivity. apply Hget1. apply Hget2.
    + erewrite amap_union_inl. discriminate. erewrite amap_map_key_get_some. reflexivity. apply Hget1. auto.
Qed.

Lemma omap_nil_pat_false rl cs m:
  (constr_at_head_ex cs rl || wild_at_head_ex rl) = false ->
  omap (fun x : list pattern * A =>
         match fst x with (*these functions can be arbitrary but whatever*)
         | Pconstr fs _ pats :: ps => if funsym_eqb fs cs then Some (rev pats ++ ps, snd x) else None
         | Pwild :: ps => Some (repeat Pwild m ++ ps, snd x)
         | _ => None
         end) rl = nil.
Proof.
  induction rl as [| [ps a] ptl IH]; simpl; simpl; auto.
  intros Hhead; unfold constr_at_head, pat_at_head in Hhead; simpl in *.
  destruct ps as [| phd ps]; auto.
  destruct phd; simpl in *; auto.
  - destruct (funsym_eqb_spec f cs); subst; auto; discriminate.
  - rewrite orb_true_r in Hhead. discriminate.
Qed.
  
(*2nd (main) structural lemma: if either cs or a Pwild appears in the first column, then S is the
  result of filtering all of the other constructors out, appending the arguments of the matching
  constructors and the correct number of wildcards for a Pwild*)
Lemma dispatch2_gen_fst_in (types: amap funsym (list pattern)) ys rl cs:
  amap_get funsym_eq_dec types cs = Some ys ->
  (constr_at_head_ex cs rl || wild_at_head_ex rl) ->
  amap_get funsym_eq_dec (fst (dispatch2_gen types rl)) cs = Some
    (omap (fun x =>
      let ps := fst x in
      let a := snd x in
      match ps with
      | p :: ps =>
        match p with
        | Pwild => Some (repeat Pwild (length ys) ++ ps, a)
        | Pconstr fs tys pats => (*trivial here*)
            if funsym_eqb fs cs then Some (rev pats ++ ps, a) else None
        | _ => None
        end
      | _ => None
      end
) rl).
Proof.
  revert ys.
  induction rl as [| [ps a] rtl IH]; simpl; try discriminate; intros ys Htypes Hhead;
  try contradiction.
  destruct (dispatch2_gen types rtl) as [cases wilds] eqn : Hd; simpl in *.
  unfold constr_at_head, pat_at_head in Hhead; simpl in Hhead.
  destruct ps as [| phd ptl]; simpl in *; auto.
  assert (Hmem: amap_mem funsym_eq_dec cs types). {
    rewrite amap_mem_spec, Htypes; auto. }
  destruct phd; auto.
  - unfold add_case, amap_change; simpl.
    destruct (funsym_eqb_spec f cs); subst.
    + simpl in Hhead. 
      (*Need to see what recursive case is: preveious lemma gives more info*)
      destruct (constr_at_head_ex cs rtl || wild_at_head_ex rtl) eqn : Hhd2.
      * simpl in IH. erewrite amap_replace_get_same1.
        2: apply IH; auto. reflexivity. auto.
      * rewrite amap_replace_get_same2. 
        -- rewrite omap_nil_pat_false. reflexivity. auto.
        -- pose proof (dispatch2_gen_fst_notin types rtl cs Hmem) as Hnone.
           rewrite Hd in Hnone; apply Hnone. auto.
    + simpl in Hhead. rewrite amap_replace_get_diff; auto.
  - unfold union_cases; simpl.
    assert (Hrepeat: forall (ql: list pattern), fold_left (fun (pl : list pattern) (_ : pattern) => Pwild :: pl) ql ptl =
      repeat Pwild (Datatypes.length ql) ++ ptl).
    {
      clear. intros ql.
      revert ptl. induction ql; intros; auto.
      simpl fold_left. rewrite IHql.
      assert (Hassoc: forall {A: Type} (l1: list A) l2 l3, l1 ++ l2 :: l3 = (l1 ++ [l2]) ++ l3).
      { intros. rewrite <- app_assoc. reflexivity. }
      rewrite Hassoc.  f_equal.
      assert (Hwild: [Pwild] = repeat Pwild 1) by reflexivity.
      rewrite Hwild, <- repeat_app, Nat.add_comm. reflexivity.
    }
    destruct (constr_at_head_ex cs rtl || wild_at_head_ex rtl) eqn : Hhead2.
    + erewrite amap_union_inboth. 3: { apply IH. apply Htypes. auto. }
      2: { apply amap_map_key_get_some. apply Htypes. } simpl. f_equal.
      f_equal. f_equal. auto. 
    + (*here, recursive get is false and list is nil*)
      rewrite omap_nil_pat_false; auto.
      erewrite amap_union_inl. reflexivity. erewrite amap_map_key_get_some.
      f_equal. f_equal. f_equal. apply Hrepeat.
      apply Htypes. pose proof (dispatch2_gen_fst_notin types rtl cs Hmem) as Hnone.
      rewrite Hd in Hnone; apply Hnone. auto.
Qed.

(*Second main structural lemma: the matrix D*)

Definition default {A: Type} (rl : list (list pattern * A)) := 
  omap (fun x =>
    match (fst x) with
    | Pwild :: ps => Some (ps, snd x)
    | _ => None
    end ) rl.

Lemma dispatch2_gen_snd (types: amap funsym (list pattern)) rl:
  snd (dispatch2_gen types rl) = default rl.
Proof.
  induction rl as [| [pl a] rtl IH]; simpl; auto.
  unfold dispatch2_aux; simpl.
  destruct (dispatch2_gen types rtl ) as [cases wilds]; simpl in *.
  destruct pl as [| p ps]; auto.
  destruct p; auto; simpl.
  f_equal; auto.
Qed.

(*Part 3: Termination*)


(*Termination Metric*)

(*The termination metric is complicated. The compile function is not structurally recursive.
  The natural choice for the termination metric is the sum of the sizes of the patterns in the input list,
  since for a constructor c(ps) :: pl, it becomes ps :: pl, decreasing the size.
  However, this does not work: the size gets bigger when we simplify to remove "or" patterns.
  An alternative is then to make the metric the sum of the products of 2^(size p) for each p in each list.
  This ensures that Por p q :: pl is bigger than p :: pl + q :: pl
  But this also doesn't work: when we add the extra (length (s_args c)) Pwilds in the matrix S, we end up
  with a bigger matrix.
  One could imagine a metric that adds the size of a Pwild, but multiplies the others, so that 
  the extra Pwilds we add are bounded in size (and thus we can make the decrease from the constructor bigger).
  But this is not commutative and it is very difficult to work with.

  Instead, we argue that the function clearly terminates if there are no "or" patterns - then we can just
  use a regular size metric with a large enough addition for the constructor case to offset the increase from
  the wilds.
  Conceptually, we can view the algorithm as first expanding all "or" patterns (recursively), and then
  proceeding with a clearly-terminating computation. But of course this is very inefficient, so the algorithm
  only expands "or"s as needed. To solve this, our termination metric is: first expand the pattern list fully,
  then caculate the size (with a suitable value for constructors). This gives an appropriate upper bound on
  the number of steps the algorithm will take. But we now have to reason about how every intermediate
  computation effects the full expansion of the patterns, which is very tricky.*)

(*The Termination Metric*)
Section TerminationMetric.

(*Part 1: [expand_size]*)
(*This is the length of the expanded pattern list, which we later prove.
  But we need a number of properties of the size independent of reasoning about expansion itself
  (this size will be part of our final bound, separate from expansion)*)

Definition iter_mult (l: list nat) : nat := fold_right Nat.mul 1 l.

Fixpoint expand_size_pat (p: pattern) : nat :=
  match p with
  | Por p1 p2 => (expand_size_pat p1) + (expand_size_pat p2)
  | Pbind p x => expand_size_pat p
  | Pconstr f _ ps => iter_mult (map expand_size_pat ps)
  | _ => 1
  end.
Definition expand_size_pat_list (l: list pattern) : nat :=
  iter_mult (map expand_size_pat l).
Definition expand_size (l: list (list pattern * A)) : nat :=
  sum (map (fun x => expand_size_pat_list (fst x)) l).

(*Lemmas*)

Lemma expand_size_nil: expand_size nil = 0.
Proof. reflexivity. Qed.

Lemma expand_size_cons x l:
  expand_size (x :: l) = expand_size_pat_list (fst x) + expand_size l.
Proof. reflexivity. Qed.

Lemma expand_size_app l1 l2 :
  expand_size (l1 ++ l2) = expand_size l1 + expand_size l2.
Proof.
  induction l1; simpl; auto; try lia.
  rewrite !expand_size_cons. lia.
Qed.

Lemma expand_size_pat_list_nil: expand_size_pat_list nil = 1. Proof. reflexivity. Qed.

Lemma expand_size_pat_list_cons x l:
  expand_size_pat_list (x :: l) = expand_size_pat x * expand_size_pat_list l.
Proof. reflexivity. Qed.

Lemma expand_size_pat_list_app l1 l2:
  expand_size_pat_list (l1 ++ l2) = expand_size_pat_list l1 * expand_size_pat_list l2.
Proof. induction l1; simpl; auto. lia. rewrite !expand_size_pat_list_cons. lia.
Qed.

Lemma expand_size_pat_list_rev l:
  expand_size_pat_list (rev l) = expand_size_pat_list l.
Proof.
  induction l; simpl; auto. 
  rewrite expand_size_pat_list_app, !expand_size_pat_list_cons, !expand_size_pat_list_nil. lia.
Qed.


(*Part 2: Expansion*)

(*The crucial subroutine in expansion concerns lists - for a list of pattern ps,
  we need to generate lists containing all possible combinations of elements from each of the
  expansions of the elements of ps. Here we give the function to do this and prove lemmas about it*)

Definition combinewith {A B C: Type} (f: A -> B -> C) (l1: list A) (l2: list B) : list C :=
  concat (map (fun x => map (fun y => f x y) l2 ) l1).
Definition choose_all {B: Type} (l: list (list B)) :=
  fold_right (fun l1 acc => combinewith cons l1 acc) [nil] l.

(*Theorems about [combinewith] and [choose_all]*)
Lemma combinewith_cons1 {B C D: Type} (f: B -> C -> D) (x: B) (l1: list B) (l2: list C) :
  combinewith f (x :: l1) l2 =
  (map (fun y => f x y) l2) ++ combinewith f l1 l2.
Proof.
  reflexivity.
Qed.

Lemma combinewith_app1 {B C D: Type} (f: B -> C -> D) (l1 l2: list B) (l3: list C) :
  combinewith f (l1 ++ l2) l3 =
  combinewith f l1 l3 ++ combinewith f l2 l3.
Proof.
  induction l1; simpl; auto.
  rewrite !combinewith_cons1, IHl1.
  rewrite app_assoc. reflexivity.
Qed.

Lemma combinewith_comp {B C: Type} (l1 : list B) (l2 l3: list C) f g
  (Hcomp: forall x y z, f x (g y z) = g (f x y) z):
  combinewith f l1 (combinewith g l2 l3) =
  combinewith g (combinewith f l1 l2) l3.
Proof.
  induction l1; [reflexivity|].
  unfold combinewith at 1. simpl.
  fold (@combinewith _ _ _ f l1 (combinewith g l2 l3)).
  rewrite IHl1.
  unfold combinewith at 5. simpl.
  rewrite combinewith_app1.
  fold (@combinewith _ _ _ f l1 l2). f_equal.
  clear -Hcomp.
  induction l2; simpl; [reflexivity|].
  rewrite !combinewith_cons1.
  rewrite !map_app, !map_map.
  rewrite IHl2. f_equal.
  apply map_ext.
  auto.
Qed.

Lemma combinewith_cons_app {B: Type} (l1: list B) l2:
  combinewith cons l1 l2 = combinewith (fun x y => x ++ y) (map (fun x => [x]) l1) l2.
Proof.
  unfold combinewith.
  rewrite !map_map. reflexivity.
Qed. 

Lemma choose_all_app {B: Type} (l1 l2: list (list B)) :
  choose_all (l1 ++ l2) = combinewith (fun x y => x ++ y) (choose_all l1) (choose_all l2).
Proof.
  induction l1; simpl; auto.
  - unfold combinewith; simpl; rewrite app_nil_r, map_id; reflexivity.
  - rewrite IHl1. apply combinewith_comp.
    intros. reflexivity.
Qed.

Lemma choose_all_length {B: Type} (l: list (list B)):
  length (choose_all l) = iter_mult (map (fun x => length x) l).
Proof.
  induction l as [| h t IH]; auto.
  simpl.
  apply length_concat_mult.
  - rewrite !map_length. auto.
  - rewrite Forall_forall. intros x.
    rewrite in_map_iff. intros [b [Hx Hinb]]; subst.
    rewrite map_length. auto.
Qed.

Lemma choose_all_null {B: Type} (l: list (list B)):
  null (choose_all l) = existsb null l.
Proof.
  induction l; simpl; auto.
  unfold combinewith.
  rewrite null_concat, forallb_map.
  destruct (choose_all l) as [|c1 ctl]; simpl in *.
  - rewrite forallb_t, <- IHl, orb_true_r. auto.
  - rewrite forallb_f, <- IHl, orb_false_r. auto.
Qed. 

(*And now we can define expansion*)

(*Note: ignore variables here, only care about size*)
Fixpoint expand_pat (p: pattern) : list pattern :=
  match p with
  | Por p1 p2 => (expand_pat p1) ++ (expand_pat p2)
  | Pbind p x => (expand_pat p) (*OK even though lose size info bc we dont ever recurse here*)
  | Pconstr c tys pats => map (fun y => Pconstr c tys y) (choose_all (map expand_pat pats))
  | _ => [Pwild]
  end.

Definition expand_pat_list (ls: list pattern) : list (list pattern) :=
  choose_all (map expand_pat ls).

Definition expand_full (ls: list (list pattern * A)) : list (list pattern) :=
  concat (map (fun x => expand_pat_list (fst x)) ls).


(*Lemmas*)

Lemma expand_pat_list_cons x t: expand_pat_list (x :: t) =
  combinewith cons (expand_pat x) (expand_pat_list t).
Proof.
  reflexivity.
Qed.

Lemma expand_pat_list_nil: expand_pat_list nil = [nil].
Proof. reflexivity. Qed.

Lemma expand_full_cons x t: expand_full (x :: t) = 
  expand_pat_list (fst x) ++ expand_full t.
Proof. reflexivity. Qed.

Lemma expand_full_nil: expand_full nil = nil.
Proof. reflexivity. Qed.

Lemma expand_full_app l1 l2: expand_full (l1 ++ l2) = expand_full l1 ++ expand_full l2.
Proof.
  unfold expand_full. rewrite map_app, concat_app. reflexivity.
Qed.

Lemma expand_pat_null p:
  null (expand_pat p) = false.
Proof.
  induction p; simpl; auto.
  - rewrite null_map, choose_all_null.
    apply existsb_false. rewrite Forall_map. auto.
  - rewrite null_app, IHp1, IHp2. auto.
Qed.

Lemma expand_pat_list_null l:
  null (expand_pat_list l) = false.
Proof.
  induction l as [| p t IH]; simpl; auto.
  unfold expand_pat_list in *; rewrite choose_all_null. simpl.
  rewrite expand_pat_null. simpl. rewrite choose_all_null in IH. auto.
Qed.

Lemma expand_pat_list_all_null l:
  negb (null l) ->
  forallb (fun x => negb (null x)) (expand_pat_list l).
Proof.
  induction l as [| p t IH]; simpl; auto.
  intros _.
  destruct t as [|t1 t2]; simpl in IH.
  - unfold expand_pat_list; simpl. unfold combinewith. rewrite forallb_concat.
    apply forallb_forall. intros x. rewrite in_map_iff. intros [y [Hy Hiny]]; subst. auto.
  - rewrite expand_pat_list_cons. unfold combinewith. rewrite forallb_concat.
    apply forallb_forall. intros x. rewrite in_map_iff.
    intros [p1 [Hp1 Hinp1]]. subst. rewrite forallb_map. simpl.
    apply forallb_t.
Qed.

Lemma expand_pat_list_app l1 l2:
  expand_pat_list (l1 ++ l2) =
  (*Idea: get all in l1, get all in l2, combine all*)
  combinewith (fun x y => x ++ y) (expand_pat_list l1) (expand_pat_list l2).
Proof.
  unfold expand_pat_list.
  rewrite map_app, choose_all_app. reflexivity.
Qed.


(*Our termination metric will be [pat_size n (expand_full ls)], where n > length (expand_full ls) * max (length ps)
  (or (expand_size ls) * max (length ps), for all ps, constr lists that appear in ls*)

(*Now we want to show the following:*)

(*1. expand_full (simplify t ls) = expand_full ls*)

(*2. pat_size n (expand_full D(ls)) < pat_size n (expand_full ls)*)

(*3. pat_size n (expand_full S(cs, ls)) + n <= expand_size ls * (s_args c)*)
  

(*Part 1: simplify*)
Lemma expand_full_simplify_single t rhd:
  expand_full (simplify_single t rhd) = expand_pat_list (fst rhd).
Proof.
  destruct rhd as [ps a]. simpl.
  destruct ps as [| p ptl]; auto.
  rewrite expand_pat_list_cons.
  revert a.
  induction p; simpl; intros a; try rewrite !expand_full_cons; try rewrite !expand_full_nil; simpl;
  try rewrite !expand_pat_list_cons; simpl; try rewrite !app_nil_r; auto.
  unfold combinewith.
  rewrite !map_app, !concat_app, !expand_full_app, IHp1, IHp2. reflexivity.
Qed.

Lemma expand_full_simplify t rl:
  expand_full (simplify t rl) = expand_full rl.
Proof.
  induction rl as [| rhd rtl IH]; auto.
  unfold simplify in *; simpl.
  rewrite expand_full_app, IH, expand_full_cons. f_equal.
  apply expand_full_simplify_single.
Qed.

(*Step 1.5: Prove length (expand_full) = expand_length*)

Lemma expand_pat_length p:
  length (expand_pat p) = expand_size_pat p.
Proof.
  induction p; simpl; auto.
  - rewrite map_length, choose_all_length.
    f_equal. rewrite !map_map. apply map_ext_Forall; auto.
  - rewrite app_length; lia.
Qed.

Lemma expand_pat_list_length l:
  length (expand_pat_list l) = expand_size_pat_list l.
Proof.
  induction l as [| p ps IH]; auto.
  rewrite expand_pat_list_cons, expand_size_pat_list_cons.
  apply length_concat_mult.
  - rewrite map_length, expand_pat_length. reflexivity.
  - rewrite Forall_forall. intros x.
    rewrite in_map_iff. intros [p1 [Hx Hinp1]]; subst.
    rewrite map_length. auto.
Qed.

Lemma expand_full_length rl:
  length (expand_full rl) = expand_size rl.
Proof.
  induction rl as [| rhd rtl IH]; auto.
  rewrite expand_full_cons, expand_size_cons, app_length, IH. f_equal.
  apply expand_pat_list_length.
Qed.


(*Part 3: Theorems about [expand_size]*)
(*We do this here to avoid repeating proofs about [simplify]*)

(*1. expand_size (simplify rl) = expand_size rl*)
Lemma expand_size_simplify t rl:
  expand_size (simplify t rl) = expand_size rl.
Proof.
  rewrite <- expand_full_length, expand_full_simplify.
  apply expand_full_length.
Qed.

(*2. The matrix D only decreases[expand_size]*)
Lemma expand_size_dispatch2_gen_snd types rl:
  expand_size (snd (dispatch2_gen types rl)) <= expand_size rl.
Proof.
  rewrite dispatch2_gen_snd.
  induction rl as [|[pl a] ptl IH]; simpl; auto.
  destruct pl as [| p tl].
  - rewrite expand_size_cons. simpl. lia.
  - destruct p; rewrite !expand_size_cons; simpl; try lia.
    rewrite expand_size_pat_list_cons; simpl. lia.
Qed.

Lemma expand_size_d t types rl:
  expand_size (snd (dispatch1 t types rl)) <= expand_size rl.
Proof.
  rewrite dispatch_equiv.
  eapply Nat.le_trans.
  apply expand_size_dispatch2_gen_snd.
  rewrite expand_size_simplify. auto.
Qed.

(*3. expand_size (S(cs, rl)) <= expand_size rl*)
Lemma expand_size_dispatch2_gen_fst types cs rl l:
  amap_mem funsym_eq_dec cs types ->
  amap_get funsym_eq_dec (fst (dispatch2_gen types rl)) cs = Some l ->
  expand_size l <= expand_size rl.
Proof.
  intros Htypes.
  destruct (constr_at_head_ex cs rl || wild_at_head_ex rl) eqn : Hin.
  2: { rewrite dispatch2_gen_fst_notin in Hin. 2: apply Htypes. rewrite Hin. discriminate. }
  rewrite amap_mem_spec in Htypes.
  destruct (amap_get funsym_eq_dec types cs) as [ys |] eqn : Hget; try discriminate.
  rewrite dispatch2_gen_fst_in with (ys:=ys); auto.
  clear Htypes Hget Hin.
  revert ys l.
  induction rl as [| [ps a] ptl IH]; simpl; intros ys l; auto; [intros Hsome; inversion Hsome; subst; auto|].
  destruct ps as [|p ps]; auto.
  - rewrite expand_size_cons; simpl. intros Hsome. apply IH in Hsome. lia.
  - destruct p; rewrite !expand_size_cons; simpl; try solve[intros Hsome; apply IH in Hsome; lia].
    + destruct (funsym_eqb_spec f cs); subst; [| intros Hsome; apply IH in Hsome; lia].
      intros Hsome. injection Hsome.
      intros Hl; subst; clear Hsome. rewrite expand_size_cons. simpl.
      rewrite expand_size_pat_list_cons. simpl.
      rewrite expand_size_pat_list_app, expand_size_pat_list_rev.
      specialize (IH ys _ eq_refl). unfold expand_size_pat_list at 1.
      apply Nat.add_le_mono; auto.
    + intros Hl; inversion Hl; subst; clear Hl.
      rewrite expand_size_cons. simpl.
      rewrite expand_size_pat_list_cons, expand_size_pat_list_app.
      replace (expand_size_pat_list (repeat Pwild (Datatypes.length ys))) with 1.
      -- specialize (IH ys _ eq_refl). simpl. rewrite !Nat.add_0_r. apply Nat.add_le_mono; auto.
      -- (*Crucial: adding lots of wilds does not increase this measure*) 
        clear. induction (length ys); simpl; auto. 
        rewrite expand_size_pat_list_cons. simpl. lia.
Qed.

Lemma expand_size_s t types rl cs l:
  amap_mem funsym_eq_dec cs types ->
  amap_get funsym_eq_dec (fst (dispatch1 t types rl)) cs = Some l ->
  expand_size l <= expand_size rl.
Proof.
  intros Htypes.
  rewrite dispatch_equiv.
  unfold dispatch2.
  intros Hl.
  eapply Nat.le_trans.
  - apply (expand_size_dispatch2_gen_fst _ _ _ _ Htypes Hl).
  - rewrite expand_size_simplify. auto.
Qed.


(*4. Now we reason about why we used this particular metric: the length of the simplified list is
  smaller than [expand_size]*)


(*Finish defining termination metric*)

Section PatSize.
Variable (n: nat).
Fixpoint pat_size_n (p: pattern) : nat :=
  match p with
  | Por p1 p2 => 1 + pat_size_n p1 + pat_size_n p2
  | Pconstr f tys ps => 1 + n + sum (map pat_size_n ps)
  | Pbind p x => 1 + pat_size_n p
  | _ => 1
  end.
Definition pat_list_size_n (l: list pattern) : nat :=
  sum (map pat_size_n l).
Definition pat_list_list_size (l: list (list pattern)) : nat :=
  sum (map pat_list_size_n l).
Definition compile_size (rl: list (list pattern * A)) : nat :=
  pat_list_list_size (expand_full rl).

(*Lemmas*)


Lemma pat_list_list_size_app l1 l2:
  pat_list_list_size (l1 ++ l2) = pat_list_list_size l1 + pat_list_list_size l2.
Proof.
  unfold pat_list_list_size. rewrite map_app.
  apply sum_app.
Qed.

(*Not as nice a definition for cons*)

Lemma compile_size_cons x l:
  compile_size (x :: l) = 
  pat_list_list_size (expand_pat_list (fst x)) + compile_size l.
Proof. 
  unfold compile_size. rewrite expand_full_cons, pat_list_list_size_app. reflexivity. 
Qed.

Lemma compile_size_nil:
  compile_size nil = 0.
Proof. reflexivity. Qed.

Lemma compile_size_cons_le x l:
  compile_size l <= compile_size (x :: l).
Proof.
  rewrite compile_size_cons. lia.
Qed.

Lemma pat_list_list_size_nil:
  pat_list_list_size nil = 0.
Proof. reflexivity. Qed.

Lemma pat_list_list_size_cons x l:
  pat_list_list_size (x :: l) = pat_list_size_n x + pat_list_list_size l.
Proof. reflexivity. Qed.

Lemma pat_list_size_n_cons x l:
  pat_list_size_n (x :: l) = pat_size_n x + pat_list_size_n l.
Proof. reflexivity. Qed.

Lemma pat_list_size_n_app l1 l2:
  pat_list_size_n (l1 ++ l2) = pat_list_size_n l1 + pat_list_size_n l2.
Proof.
  induction l1; simpl; auto. rewrite !pat_list_size_n_cons, IHl1. lia.
Qed. 

Lemma pat_size_n_pos p:
  0 < pat_size_n p.
Proof.
  destruct p; simpl; lia.
Qed.

Lemma pat_list_size_n_pos l:
  negb (null l) ->
  0 < pat_list_size_n l.
Proof.
  induction l as [| h t IH]; simpl; try discriminate.
  intros _. rewrite pat_list_size_n_cons.
  pose proof (pat_size_n_pos h); lia.
Qed.

Lemma pat_list_list_size_pos l:
  negb (null l) ->
  forallb (fun x => negb (null x)) l ->
  0 < pat_list_list_size l.
Proof.
  induction l; simpl; auto; try discriminate.
  intros _. intros Hnull.
  rewrite pat_list_list_size_cons.
  apply andb_true_iff in Hnull. destruct Hnull as [Hnull _].
  pose proof (pat_list_size_n_pos a Hnull). lia.
Qed.

(*Very important: remove element gives smaller size. This and the following
  lemma are crucial for proving that the D matrix gets smaller*)
Lemma compile_size_cons_lt x l:
  negb (null (fst x)) ->
  compile_size l < compile_size (x :: l).
Proof.
  intros Hnull. rewrite compile_size_cons.
  assert (0 <pat_list_list_size (expand_pat_list (fst x))); try lia.
  apply pat_list_list_size_pos.
  - rewrite expand_pat_list_null. auto.
  - apply expand_pat_list_all_null. auto.
Qed.  

Lemma pat_list_list_expand_cons_lt x l:
  pat_list_list_size (expand_pat_list l) < pat_list_list_size (expand_pat_list (x :: l)).
Proof.
  rewrite expand_pat_list_cons. unfold combinewith.
  pose proof (expand_pat_list_null l) as Hnull.
  induction (expand_pat_list l) as [|e1 e2 IH]; simpl; try discriminate.
  destruct e2 as [| e2 e3]; simpl in *.
  - pose proof (expand_pat_null x). destruct (expand_pat x); try discriminate.
    simpl. rewrite !pat_list_list_size_cons.
    rewrite !pat_list_size_n_cons. rewrite pat_list_list_size_nil. 
    pose proof (pat_size_n_pos p); lia.
  - rewrite pat_list_list_size_cons.
    unfold pat_list_list_size at 2.
    rewrite sum_concat. rewrite !map_map. simpl.
    specialize (IH eq_refl).
    unfold pat_list_list_size at 2 in IH.
    rewrite sum_concat in IH. rewrite !map_map in IH; simpl in IH.
    rewrite sum_map_sum.
    apply Nat.add_lt_mono; auto.
    pose proof (expand_pat_null x). destruct (expand_pat x); try discriminate.
    simpl. rewrite pat_list_size_n_cons. pose proof (pat_size_n_pos p). lia.
Qed.

End PatSize.

Lemma pat_size_n_mono_le n1 n2 p:
  n1 <= n2 ->
  pat_size_n n1 p <= pat_size_n n2 p.
Proof.
  intros Hn. induction p; simpl; auto; try lia.
  assert (sum (map (pat_size_n n1) ps) <= sum (map (pat_size_n n2) ps)).
  { apply sum_lt. rewrite <- Forall_forall. assumption. }
  lia.
Qed.

Lemma compile_size_mono_le n1 n2 rl:
  n1 <= n2 ->
  compile_size n1 rl <= compile_size n2 rl.
Proof.
  intros Hn.
  repeat (apply sum_lt; intros).
  apply pat_size_n_mono_le; assumption.
Qed.

End TerminationMetric.

(*Part 4: D matrix is smaller*)

(*This is trivial using a standard termination metric, but difficult for us because
  we have to reason about simplification and expansion*)

(*A weaker lemma that holds unconditionally*)
Lemma dispatch2_gen_snd_leq n types rl:
  compile_size n (snd (dispatch2_gen types rl)) <= compile_size n rl.
Proof.
  rewrite dispatch2_gen_snd. induction rl as [|[ps a] rtl IH]; auto.
  simpl. destruct ps as [| phd ptl]; simpl; auto.
  destruct phd; simpl; auto; try solve[eapply Nat.le_trans; [apply IH| apply compile_size_cons_le]].
  rewrite !compile_size_cons. simpl.
  apply Nat.add_le_mono; auto.
  rewrite expand_pat_list_cons. unfold combinewith. simpl. rewrite app_nil_r.
  unfold pat_list_list_size. rewrite map_map. unfold pat_list_size_n. simpl.
  apply sum_lt. intros x Hinx. lia.
Qed.

(*The main lemma: assuming nonempty rl lists, the D matrix is actually smaller*)
Lemma dispatch2_gen_snd_smaller n types rl:
  negb (null rl) ->
  forallb (fun x => negb (null (fst x))) rl ->
  compile_size n (snd (dispatch2_gen types rl)) < compile_size n rl.
Proof.
  rewrite dispatch2_gen_snd. induction rl as [|[ps a] rtl IH]; try discriminate.
  simpl. intros _ Hnull. destruct ps as [| phd ptl]; simpl; try discriminate.
  destruct phd; simpl; auto; try solve[
  eapply Nat.le_lt_trans; [rewrite <- dispatch2_gen_snd with (types:=types); apply dispatch2_gen_snd_leq |
    apply compile_size_cons_lt; auto]].
  (*Only 1 nontrivial case*)
  simpl in *.
  rewrite !compile_size_cons.
  simpl.
  apply Nat.add_lt_le_mono.
  - apply pat_list_list_expand_cons_lt.
  - rewrite <- (dispatch2_gen_snd types). apply dispatch2_gen_snd_leq.
Qed.

(*Before we can get the full result, we need a bunch of annoying results
  about the nonemptiness of simplification. Not sure where to put these*)
Lemma null_simplify_aux t a p:
  negb (null (simplify_aux t a p)).
Proof.
  revert a.
  induction p; simpl; intros; auto.
  rewrite null_app, negb_andb, IHp1, IHp2. auto.
Qed.

Lemma null_simplify_single t rl:
  negb (null (simplify_single t rl)).
Proof.
  destruct rl as [ps a]. simpl.
  destruct ps; simpl; auto.
  rewrite null_map, null_simplify_aux.
  auto.
Qed.

Lemma null_simplify t rl:
  null (simplify t rl) = null rl.
Proof.
  unfold simplify. rewrite null_concat.
  destruct rl; simpl; auto.
  pose proof (null_simplify_single t p) as Hnull.
  apply negb_true_iff in Hnull.
  rewrite Hnull; auto.
Qed.

Lemma simplify_single_all_null t x:
  negb (null (fst x)) =
  forallb (fun x => negb (null (fst x))) (simplify_single t x).
Proof.
  destruct x as [ps a]. simpl.
  destruct ps as [| p ptl]; simpl; auto.
  rewrite forallb_map. simpl. rewrite forallb_t. reflexivity.
Qed.

Lemma simplify_all_null t rl:
  forallb (fun x => negb (null (fst x))) rl =
  forallb (fun x => negb (null (fst x))) (simplify t rl).
Proof.
  unfold simplify.
  rewrite forallb_concat, forallb_map.
  apply forallb_ext. apply simplify_single_all_null.
Qed.

(*And the full result*)
Lemma d_matrix_smaller n t types rl:
  negb (null rl) ->
  forallb (fun x => negb (null (fst x))) rl ->
  compile_size n (snd (dispatch1 t types rl)) < compile_size n rl.
Proof.
  rewrite dispatch_equiv.
  unfold dispatch2.
  intros Hnull Hallnull.
  eapply Nat.lt_le_trans.
  - apply dispatch2_gen_snd_smaller.
    + rewrite null_simplify; auto.
    + rewrite <- simplify_all_null; auto.
  - unfold compile_size. rewrite expand_full_simplify. auto.
Qed.

(*Part 5: S matrix is smaller (for large enough n)*)

(*We first need several intermediate lemmas:*)
Lemma pat_list_list_size_combinewith_app n l1 l2:
  pat_list_list_size n (combinewith (fun x y => x ++ y) l1 l2) =
  (length l2) * (pat_list_list_size n l1) + (length l1) * (pat_list_list_size n l2).
Proof.
  unfold combinewith, pat_list_list_size.
  rewrite sum_concat. rewrite !map_map.
  erewrite map_ext.
  2: {
    intros. rewrite map_map. reflexivity. }
  revert l2. induction l1; simpl; intros l2; try nia.
  specialize (IHl1 l2). rewrite IHl1.
  rewrite Nat.mul_add_distr_l.
  assert (sum (map (fun x : list pattern => pat_list_size_n n (a ++ x)) l2) =

    Datatypes.length l2 * pat_list_size_n n a + (sum (map (pat_list_size_n n) l2))); try lia.
  {
    clear. induction l2; simpl; intros; auto.
    rewrite pat_list_size_n_app.
    rewrite IHl2. lia.
  }
Qed.

(*Need to know that size of expansion invariant under reversal (NOTE: this is a 
  big reason why the Pwild+/else* version doesn't work). This takes several steps*)

Lemma combinewith_cons_length {B: Type} (x: list B) (l: list (list B)):
  length (combinewith cons x l) =  (length x) * (length l).
Proof.
  unfold combinewith. rewrite length_concat. rewrite !map_map.
  erewrite map_ext.
  2: { intros. rewrite map_length. reflexivity. }
  rewrite map_const.
  apply sum_repeat.
Qed. 

Lemma choose_all_perm_length {B: Type} (l1 l2: list (list B)):
  Permutation l1 l2 ->
  length (choose_all l1) = length (choose_all l2).
Proof.
  intros Hperm.
  induction Hperm; simpl; auto.
  - rewrite !combinewith_cons_length. lia.
  - rewrite !combinewith_cons_length. lia.
  - lia.
Qed. 

Lemma expand_pat_list_length_perm (l1 l2: list pattern) :
  Permutation l1 l2 ->
  length (expand_pat_list l1) = length (expand_pat_list l2).
Proof.
  intros Hperm.
  apply choose_all_perm_length.
  apply Permutation_map. auto.
Qed.

Lemma expand_pat_list_rev_length (l: list pattern) :
  length (expand_pat_list (rev l)) = length (expand_pat_list l).
Proof.
  apply expand_pat_list_length_perm. apply Permutation_sym. apply Permutation_rev.
Qed. 

Lemma pat_list_list_size_rev n l:
  pat_list_list_size n (expand_pat_list (rev l)) =
  pat_list_list_size n (expand_pat_list l).
Proof.
  induction l; simpl; auto.
  rewrite expand_pat_list_cons, expand_pat_list_app, combinewith_cons_app,
    !pat_list_list_size_combinewith_app, !map_length, <- IHl, !expand_pat_list_cons, expand_pat_list_nil.
  unfold combinewith; simpl.
  rewrite concat_map_singleton, !map_length, expand_pat_list_rev_length.
  lia.
Qed.

(*We prove the bound in several stages. First, prove the constructor part
  assuming an unconditional bound on the tail*)
Lemma dispatch2_gen_bound_constr rtl cs n l0 ptl a l (m: nat) :
compile_size n
       (omap
          (fun x : list pattern * A =>
           match fst x with
           | Pconstr fs _ pats :: ps => if funsym_eqb fs cs then Some (rev pats ++ ps, snd x) else None
           | Pwild :: ps => Some (repeat Pwild m++ ps, snd x)
           | _ => None
           end) rtl) <= compile_size n rtl + expand_size rtl * m ->
compile_size n
  ((rev l0 ++ ptl, a)
   :: omap
        (fun x : list pattern * A =>
         match fst x with
         | Pconstr fs _ pats :: ps => if funsym_eqb fs cs then Some (rev pats ++ ps, snd x) else None
         | Pwild :: ps => Some (repeat Pwild m ++ ps, snd x)
         | _ => None
         end) rtl) + n <=
compile_size n ((Pconstr cs l l0 :: ptl, a) :: rtl) +
expand_size ((Pconstr cs l l0 :: ptl, a) :: rtl) * m.
Proof.
  intros IH.
  rewrite expand_size_cons. simpl.
  rewrite expand_size_pat_list_cons, !compile_size_cons. simpl.
  rewrite expand_pat_list_cons, expand_pat_list_app, pat_list_list_size_combinewith_app, 
    combinewith_cons_app. simpl.
  rewrite !map_map, pat_list_list_size_combinewith_app, map_length.
  fold (expand_pat_list l0).
  (*Main result we need)*)
  assert (Hconstrbound: Datatypes.length (expand_pat_list ptl) * pat_list_list_size n (expand_pat_list ( l0)) + n <=
     Datatypes.length (expand_pat_list ptl) *
      pat_list_list_size n (map (fun x : list pattern => [Pconstr cs l x]) (expand_pat_list l0))).
  {
    assert (pat_list_list_size n (expand_pat_list l0) + n <= 
      pat_list_list_size n (map (fun x : list pattern => [Pconstr cs l x]) (expand_pat_list l0))).
    {

      (*The less interesting part:*)
      assert (Hweak: forall l1, 
        pat_list_list_size n l1 <= pat_list_list_size n (map (fun x : list pattern => [Pconstr cs l x]) l1)).
      { 
        intros l1. induction l1; simpl; auto.
        rewrite !pat_list_list_size_cons. simpl. unfold pat_list_size_n. lia.
      }
      (*The important part*)
      (*Idea: [expand_pat_list] has something, that something already increases potential by n, 
        rest only increases*)
      pose proof (expand_pat_list_null l0) as Hnull.
      destruct (expand_pat_list l0) as [| e1 e2]; try discriminate.
      simpl map. rewrite !pat_list_list_size_cons.
      simpl. specialize (Hweak e2). unfold pat_list_size_n. lia.
    }
    (*And now we deal with the multiplication - can only increase the difference*)
    assert (length (expand_pat_list ptl) >= 1); [|nia].
    pose proof (expand_pat_list_null ptl); destruct (expand_pat_list ptl); simpl; [discriminate | lia].
  }
  rewrite expand_pat_list_rev_length, pat_list_list_size_rev.
  lia.
Qed.

(*Lemma we need for Pwild case*)
Lemma dispatch2_gen_bound_wild: forall n m ptl, pat_list_list_size n (expand_pat_list (repeat Pwild m ++ ptl)) =
        m * length (expand_pat_list ptl) + pat_list_list_size n (expand_pat_list ptl).
Proof.
  intros.
  rewrite expand_pat_list_app.
  replace (expand_pat_list (repeat Pwild m)) with [(repeat Pwild m)]. 
  2: {
    unfold expand_pat_list. unfold choose_all.
    replace (map expand_pat (repeat Pwild m)) with ((map (fun x => [x])) (repeat Pwild m)).
    2: {
      induction m; simpl; auto. f_equal; auto.
    }
    induction m; simpl; auto.
    rewrite <- IHm. unfold combinewith. simpl. reflexivity.
  }
  rewrite pat_list_list_size_combinewith_app. simpl.
  replace (pat_list_list_size n [repeat Pwild m]) with m; [lia|].
  induction m; simpl; auto. revert IHm.
  rewrite !pat_list_list_size_cons, pat_list_list_size_nil.
  rewrite pat_list_size_n_cons. simpl. lia.
Qed.

(*The first bound we need: weaker, but unconditional*)
Lemma dispatch2_gen_bound_gen rl cs n (m: nat):
  compile_size n
   (omap
      (fun x : list pattern * A =>
       match fst x with
       | Pconstr fs _ pats :: ps => if funsym_eqb fs cs then Some (rev pats ++ ps, snd x) else None
       | Pwild :: ps => Some (repeat Pwild m ++ ps, snd x)
       | _ => None
       end) rl) <= compile_size n rl + expand_size rl * m.
Proof.
  induction rl as [| [ps a] rtl IH]; auto.
  simpl.
  destruct ps as [| p ptl].
  - rewrite expand_size_cons. simpl. rewrite compile_size_cons. simpl. lia.
  - destruct p; try solve[rewrite expand_size_cons, compile_size_cons; simpl; lia].
    + destruct (funsym_eqb_spec f cs); subst.
      * (*hard case: proved*) pose proof (dispatch2_gen_bound_constr rtl cs n l0 ptl a l m) ; lia.
      * rewrite expand_size_cons, compile_size_cons; simpl. lia.
    + (*Pwild case*)
      rewrite !compile_size_cons. simpl.
      rewrite expand_size_cons. simpl.
      rewrite expand_size_pat_list_cons. simpl. rewrite Nat.add_0_r.
      replace (Pwild :: ptl) with (repeat Pwild 1 ++ ptl) by reflexivity.
      rewrite !dispatch2_gen_bound_wild; simpl.
      rewrite expand_pat_list_length. lia.
Qed.

(*And the real bound we need:
  We add at most (length ys) wilds per each row of the expanded matrix, but
  we reduce by n. This allows us to set n large enough*)
Theorem dispatch2_gen_bound_in n types rl cs l (ys: list pattern):
  amap_get funsym_eq_dec types cs = Some ys ->
  constr_at_head_ex cs rl ->
  amap_get funsym_eq_dec (fst (dispatch2_gen types rl)) cs = Some l ->
  compile_size n l + n <= compile_size n rl + (expand_size rl) * (length ys).
Proof.
  intros Hget Hconstr.
  rewrite dispatch2_gen_fst_in with (ys:=ys); auto; [| rewrite Hconstr; auto].
  intros Hsome; inversion Hsome; subst; clear Hsome.
  induction rl as [| [ps a] rtl IH]; auto; [discriminate|].
  simpl. simpl in Hconstr.
  unfold constr_at_head in Hconstr. simpl in Hconstr.
  destruct ps as [| p ptl].
  - rewrite expand_size_cons. simpl. rewrite compile_size_cons. simpl.
    eapply Nat.le_trans. apply IH; auto. lia.
  - destruct p; simpl in Hconstr; try solve[rewrite expand_size_cons, compile_size_cons; simpl;
      eapply Nat.le_trans; [apply IH; auto| lia]].
    + (*Interesting case: add constr*)
      destruct (funsym_eqb_spec f cs); subst.
      * apply (dispatch2_gen_bound_constr rtl cs n l0 ptl a l).
        apply dispatch2_gen_bound_gen.
      * rewrite expand_size_cons, compile_size_cons; simpl;
        eapply Nat.le_trans; [apply IH; auto| lia].
    + (*Pwild case*)
      rewrite !compile_size_cons. simpl.
      rewrite expand_size_cons. simpl.
      rewrite expand_size_pat_list_cons. simpl. rewrite Nat.add_0_r.
      replace (Pwild :: ptl) with (repeat Pwild 1 ++ ptl) by reflexivity.
      rewrite !dispatch2_gen_bound_wild; simpl.
      rewrite expand_pat_list_length. specialize (IH Hconstr). lia.
Qed.

(*And the corollary for the full S matrix*)
Lemma s_matrix_bound_in n t types rl cs l (ys: list pattern):
  amap_get funsym_eq_dec types cs = Some ys ->
  constr_at_head_ex cs (simplify t rl) ->
  amap_get funsym_eq_dec (fst (dispatch1 t types rl)) cs = Some l ->
  compile_size n l + n <= compile_size n rl + (expand_size rl) * (length ys).
Proof.
  intros Htypes. rewrite dispatch_equiv. unfold dispatch2.
  intros Hhead Hget.
  eapply Nat.le_trans.
  - apply (dispatch2_gen_bound_in _ _ _ _ _ _ Htypes Hhead Hget).
  - apply Nat.add_le_mono. 
    + unfold compile_size. rewrite expand_full_simplify. lia.
    + apply Nat.mul_le_mono; auto. rewrite expand_size_simplify; auto.
Qed.

(*Part 6: Proofs about [populate_all]*)

(*Essentially, we need to know how the keys of the map from [populate_all] correspond to the
  keys of the map in [dispatch]. This is annoyingly complicated, in part because
  they fold over the list in reverse order*)

(*Populate is the same as first simplifying, then running simpler populate*)

(*We need this because in our proofs, we can't forget about a until the end*)
Definition get_full (rl: list (list pattern * A)) : option (list (pattern * A)) :=
  fold_right (fun x acc => match fst x with | nil => None | y :: _ => 
    option_bind acc (fun acc => Some ((y, (snd x)) :: acc)) end)
  (Some nil) rl.

Lemma get_full_heads rl:
  option_map (fun l => map fst l) (get_full rl) = get_heads rl.
Proof.
  induction rl as [| [l a] t IH]; simpl; auto.
  destruct l; auto.
  rewrite <- IH.
  destruct (get_full t); auto.
Qed.

Lemma get_full_app l1 l2:
  get_full (l1 ++ l2) =
  option_bind (get_full l1) (fun x1 => option_bind (get_full l2) (fun x2 => Some (x1 ++ x2))).
Proof.
  induction l1 as [| [ps a] t IH]; simpl; auto.
  - rewrite option_bind_id. auto.
  - destruct ps; auto.
    rewrite IH. destruct (get_full t); auto. simpl.
    destruct (get_full l2); auto.
Qed.

Lemma get_full_simplify t rl:
  get_full (simplify t rl) = option_map (fun l => concat (map (fun x => simplify_aux t (snd x) (fst x)) l)) (get_full rl).
Proof.
  induction rl as [| [ps a] rtl IH]; simpl; auto.
  unfold simplify in *. simpl.
  rewrite get_full_app, IH.
  destruct ps as [| phd ptl]; simpl; auto.
  destruct (get_full rtl); simpl; auto.
  - assert (Hfull: get_full (map (fun x : pattern * A => (fst x :: ptl, snd x)) (simplify_aux t a phd)) = Some (simplify_aux t a phd)).
    { clear. generalize dependent (simplify_aux t a phd). induction l as [| h tl IH]; simpl; auto.
      rewrite IH. simpl. destruct h; auto. }
    rewrite Hfull. reflexivity.
  - rewrite option_bind_none. reflexivity.
Qed. 

Lemma populate_simplify_aux is_constr acc p t a:
  populate is_constr acc p =
  fold_left_opt (populate is_constr) (map fst (simplify_aux t a p)) acc.
Proof.
  revert a acc.
  induction p; simpl; auto; intros a acc.
  - destruct acc as [css csl]; simpl.
    destruct (is_constr f); auto.
    destruct (amap_mem funsym_eq_dec f css); auto.
  - rewrite map_app, fold_left_opt_app, (IHp1 a).
    apply option_bind_ext. auto.
Qed.

(*This is useful because we can just ignore simplification entirely*)
Lemma populate_all_simplify is_constr t rl:
  populate_all is_constr rl = populate_all is_constr (simplify t rl).
Proof.
  unfold populate_all. rewrite <- !get_full_heads.
  rewrite get_full_simplify, option_map_comp.
  destruct (get_full rl) eqn : Hfull; simpl; auto.
  generalize dependent (@amap_empty funsym (list pattern), (@nil (funsym * list vty * list pattern))).
  clear Hfull.
  induction l as [| h tl IH]; simpl; auto.
  intros p.
  rewrite map_app, fold_left_opt_app.
  unfold option_bind.
  rewrite <- populate_simplify_aux.
  destruct (populate is_constr p (fst h)); auto.
Qed.

(*A detour: we will need to know that there are only constructors and wilds in the
  simplified list. We give a separate predicate:*)

Definition simplified_aux (p: pattern) : bool :=
  match p with
  | Pconstr _ _ _ => true
  | Pwild => true
  | _ => false
  end.

Lemma simplify_aux_simplified t a p:
  forallb simplified_aux (map fst (simplify_aux t a p)).
Proof.
  revert a.
  induction p; simpl; intros; auto.
  rewrite map_app, forallb_app; auto. rewrite IHp1, IHp2; auto.
Qed.

Definition simplified (p: list (list pattern * A)) : bool :=
  (*The first patterns of each are simplified*)
  forallb (fun l => match fst l with | nil => true | p :: _ => simplified_aux p end) p.

Lemma simplify_simplified t rl :
  simplified (simplify t rl).
Proof.
  unfold simplify, simplified.
  rewrite forallb_concat.
  apply forallb_map_true.
  intros x Hinx.
  apply forallb_forall.
  intros y Hiny; simpl in *.
  unfold simplify_single in Hiny.
  destruct x as [ps a]; simpl in *.
  destruct ps as [| p ptl]; simpl in *; auto.
  - destruct Hiny; subst; auto; try contradiction.
  - rewrite in_map_iff in Hiny.
    destruct Hiny as [[p2 z] [Hz Hinx']].
    subst. simpl in *.
    pose proof (simplify_aux_simplified t a p) as Hsimpl.
    unfold is_true in Hsimpl.
    rewrite forallb_forall in Hsimpl.
    apply Hsimpl. rewrite in_map_iff. exists (p2, z); auto.
Qed.

Lemma simplified_tl(p: list pattern * A) ps:
  simplified (p :: ps) ->
  simplified ps.
Proof.
  unfold simplified. simpl. intros. bool_hyps. auto.
Qed.

Lemma get_heads_rev rl:
  get_heads (rev rl) = option_map (fun x => rev x) (get_heads rl).
Proof.
  induction rl as [| h t IH]; simpl; auto.
  rewrite <- get_full_heads in IH |- *.
  rewrite get_full_app.
  simpl. destruct h as [ps a]; simpl.
  destruct ps; simpl; auto.
  - rewrite option_bind_none. reflexivity.
  - rewrite !option_map_bind. simpl.
    rewrite !option_bind_map.
    destruct (get_full (rev t)); simpl in *; auto.
    + rewrite map_app. simpl. destruct (get_heads t); simpl in *; auto; try discriminate.
      inversion IH; subst; auto.
    + destruct (get_heads t); simpl in *; auto. discriminate.
Qed.

Lemma simplified_rev l:
  simplified (rev l) = simplified l.
Proof.
  apply forallb_rev.
Qed.

(*The result we want: much easier to work with than [populate_all]*)
Lemma populate_all_in is_constr rl o cs:
  simplified rl ->
  populate_all is_constr rl = Some o ->
  amap_mem funsym_eq_dec cs (fst o) <-> constr_at_head_ex cs rl.
Proof.
  intros Hsimpl. unfold populate_all.
  destruct (get_heads rl) as[heads|] eqn : Hhead; [|discriminate].
  rewrite fold_left_right_opt.
  unfold constr_at_head_ex.
  rewrite <- (rev_involutive rl) at 1.
  rewrite existsb_rev. 
  assert (Hhead1: get_heads (rev rl) = Some (rev heads)). {
    rewrite get_heads_rev, Hhead. reflexivity.
  }
  clear Hhead.
  rewrite <- simplified_rev in Hsimpl.
  (*Now, same direction*)
  generalize dependent (rev heads).
  revert o.
  revert cs.
  induction (rev rl) as [| [ps a] t IH]; simpl; auto; intros o cs.
  - intros l. inv Hsome. simpl.
    inv Hsome. simpl. rewrite amap_mem_spec, amap_empty_get. reflexivity. 
  - intros head. destruct ps as [| phd ptl]; try discriminate.
    destruct (get_heads t) as [heads1|] eqn : Hheads2; simpl; try discriminate.
    inv Hsome. simpl.
    match goal with 
    | |- context [option_bind ?o ?f] => destruct o as [p|] eqn : Hfold; simpl; try discriminate end.
    unfold simplified in Hsimpl.
    unfold constr_at_head at 1; simpl.
    (*simplified assumption means we only care about constr and wildcard*)
    destruct phd; simpl in *; auto; try discriminate.
    + destruct p as [css csl]; simpl in *.
      destruct (is_constr f); try discriminate.
      destruct (amap_mem funsym_eq_dec f css) eqn : Hmem.
      * inv Hsome. simpl. 
        destruct (funsym_eqb_spec f o); simpl; subst; auto.
        -- split; auto.
        -- rewrite <- (IH Hsimpl _ _ _ eq_refl Hfold). simpl.
          split; intros; destruct_all; subst; auto.
      * inv Hsome. 
        simpl.
        destruct (funsym_eqb_spec f o); simpl; subst.
        2: { rewrite amap_mem_spec, amap_set_get_diff; auto.
          rewrite <- (IH Hsimpl _ _ _ eq_refl Hfold); auto.
          simpl. rewrite amap_mem_spec. destruct (amap_get funsym_eq_dec css o); split; auto.
        }
        rewrite amap_mem_spec, amap_set_get_same. split; auto.
    + inv Hsome. eapply IH. assumption. reflexivity. auto.
Qed.

(*And now we prove the same for [dispatch1]*)

(*Not most general but oh well*)
Lemma amap_mem_union_some {B C: Type} (eq_dec: forall x y, {x = y} + {x <> y})
  (f: B -> C -> C -> option C) (m1 m2: amap B C) x
  (Hsome: forall b c1 c2, isSome (f b c1 c2)):
  amap_mem eq_dec x (amap_union eq_dec f m1 m2) = amap_mem eq_dec x m1 || amap_mem eq_dec x m2.
Proof.
  rewrite !amap_mem_spec.
  destruct (amap_get eq_dec m1 x) eqn : Hget1; destruct (amap_get eq_dec m2 x) eqn : Hget2.
  - erewrite amap_union_inboth. 2: apply Hget1. 2: apply Hget2.
    specialize (Hsome x c c0). destruct (f x c c0); auto.
  - erewrite amap_union_inl; eauto.
  - erewrite amap_union_inr; eauto.
  - erewrite amap_union_notin; auto.
Qed. 

Lemma dispatch1_in_types rl t types cs:
  amap_mem funsym_eq_dec cs (fst (dispatch1 t types rl)) ->
  constr_at_head_ex cs (simplify t rl) \/
  amap_mem funsym_eq_dec cs types.
Proof.
  rewrite dispatch_equiv.
  unfold dispatch2.
  induction (simplify t rl) as [|[pl a] rtl IH]; simpl.
  - rewrite amap_mem_spec, amap_empty_get. discriminate.
  - destruct (dispatch2_gen types rtl) as [cases wilds]; simpl in *.
    destruct pl as [| phd ptl]; simpl in *; auto.
    unfold constr_at_head; simpl.
    destruct phd; simpl; auto.
    + unfold add_case, amap_change.
      rewrite amap_mem_spec.
      destruct (funsym_eqb_spec f cs); subst; auto.
      rewrite amap_replace_get_diff; auto.
    + unfold union_cases.
      rewrite amap_mem_union_some; auto.
      rewrite amap_mem_spec.
      destruct (amap_get funsym_eq_dec types cs) eqn : Hget; auto.
      * intros _. right. rewrite amap_mem_spec. rewrite Hget; auto.
      * rewrite amap_map_key_get_none; auto.
Qed.

(*The main lemma we need, a corollary of the above:*)
Lemma constrs_in_types t rl cs l is_constr o:
  amap_get funsym_eq_dec (fst (dispatch1 t (fst o) rl)) cs = Some l ->
  populate_all is_constr rl = Some o ->
  amap_mem funsym_eq_dec cs (fst o).
Proof.
  intros Hget Hpop.
  (*First, see if we are already good*)
  destruct (amap_mem funsym_eq_dec cs (fst o)) eqn : Htypes; auto.
  (*Cannot use any lemmas because we always assumed in types*)
  rewrite populate_all_simplify with (t:=t) in Hpop.
  assert (Hin: constr_at_head_ex cs (simplify t rl)). {
    pose proof (dispatch1_in_types rl t (fst o) cs) as Hdis.
    rewrite amap_mem_spec in Hdis. rewrite Hget in Hdis.
    specialize (Hdis eq_refl). destruct Hdis as [Hdis | Hdis]; auto.
    rewrite Htypes in Hdis. discriminate.
  }
  rewrite <- populate_all_in in Hin.
  - rewrite Htypes in Hin. discriminate.
  - apply simplify_simplified.
  - apply Hpop.
Qed.

(*Part 7: Define full bound*)

(*The bound we give: (length rl) * (max size of ps in rl)*)
(*We actually do need to get every single constructor in the patterns, because when simplifying,
  we may introduce a constructor that was was not at the head before*)
(*We don't care about duplicates or efficiency; we never run this*)

Fixpoint get_constrs_pat (p: pattern) : list (funsym * nat) :=
  match p with
  | Pconstr f _ ps => (f, length ps) :: concat (map get_constrs_pat ps)
  | Por p1 p2 => (get_constrs_pat p1) ++ (get_constrs_pat p2)
  | Pbind p _ => get_constrs_pat p
  | _ => nil
  end.
Definition get_constrs_pat_list (l: list pattern) : list (funsym * nat) :=
  concat (map get_constrs_pat l).
Definition get_constrs_pat_list_list (l: list (list pattern)) : list (funsym * nat) :=
  concat (map get_constrs_pat_list l).
Definition get_constrs_in (rl: list (list pattern * A)) : list (funsym * nat) :=
  concat (map (fun x => get_constrs_pat_list (fst x)) rl).

(*Lemmas*)
Lemma get_constrs_in_cons x l:
  get_constrs_in (x :: l) = get_constrs_pat_list (fst x) ++ get_constrs_in l.
Proof. reflexivity. Qed.
Lemma get_constrs_pat_list_cons x l:
  get_constrs_pat_list (x :: l) = get_constrs_pat x ++ get_constrs_pat_list l.
Proof. reflexivity. Qed.
Lemma get_constrs_in_app l1 l2:
  get_constrs_in (l1 ++ l2) = get_constrs_in l1 ++ get_constrs_in l2.
Proof.
  induction l1; simpl; auto. rewrite !get_constrs_in_cons; auto. rewrite IHl1.
  rewrite app_assoc.
  auto.
Qed. 
Lemma get_constrs_pat_list_app l1 l2:
  get_constrs_pat_list (l1 ++ l2) = get_constrs_pat_list l1 ++ get_constrs_pat_list l2.
Proof.
  induction l1; simpl; auto. rewrite !get_constrs_pat_list_cons, IHl1, app_assoc.
  reflexivity.
Qed.


Definition constr_args_at_head (c: funsym) (ps: list pattern) (r: list pattern * A) : bool :=
  match fst r with
  | Pconstr f _ pats :: _ => funsym_eqb f c && list_eqb pattern_eqb ps pats
  | _ => false
  end.

Lemma constr_args_at_head_pat_list c pats h:
  constr_args_at_head c pats h -> In (c, length pats) (get_constrs_pat_list (fst h)).
Proof.
  destruct h as [ps a]. simpl.
  unfold constr_args_at_head. simpl.
  destruct ps as [| p tl]; simpl; auto.
  destruct p; simpl; auto; try discriminate.
  destruct (funsym_eqb_spec f c); subst; simpl; try discriminate.
  destruct (list_eqb_spec _ pattern_eqb_spec pats l0); subst; simpl; auto.
  discriminate.
Qed.

Lemma constr_args_at_head_ex_in (rl: list (list pattern * A)) (c: funsym) ps:
  existsb (constr_args_at_head c ps) rl ->
  In (c, length ps) (get_constrs_in rl).
Proof.
  induction rl as [| h t IH]; simpl; auto.
  rewrite get_constrs_in_cons, in_app_iff. unfold is_true.
  rewrite orb_true_iff.
  intros Hin.
  pose proof (constr_args_at_head_pat_list c ps h). destruct_all; auto.
Qed.


(*Simplifying does not change constructors*)
Lemma get_constrs_in_simplify_single c t h:
In c (get_constrs_in (simplify_single t h))  <-> In c (get_constrs_pat_list (fst h)).
Proof.
  unfold simplify_single.
  destruct h as [ps a].
  destruct ps as [| p ptl]; simpl; auto; [reflexivity|].
  rewrite get_constrs_pat_list_cons.
  unfold get_constrs_in. rewrite !map_map. simpl.
  revert a.
  induction p; simpl; intros a; auto; try rewrite app_nil_r; auto; try reflexivity.
  rewrite map_app, concat_app, !in_app_iff, IHp1, IHp2.
  rewrite !in_app_iff; split; intros; destruct_all; auto.
Qed.

Lemma get_constrs_in_simplify (rl: list (list pattern * A)) t (c: funsym * nat):
  In c (get_constrs_in (simplify t rl)) <-> In c (get_constrs_in rl).
Proof.
  induction rl as [| rhd rtl IH]; simpl; auto; [reflexivity|].
  unfold simplify in *; simpl in *. rewrite get_constrs_in_app, get_constrs_in_cons, !in_app_iff.
  rewrite IH. rewrite get_constrs_in_simplify_single. reflexivity.
Qed.

(*Iterated max*)
Definition iter_max (l: list nat) : nat :=
  fold_right max 0 l.
Lemma iter_max_in (n: nat) (l: list nat):
  In n l -> n <= iter_max l.
Proof.
  induction l; simpl; auto; [contradiction|].
  intros [Han| Hin]; subst; auto; try lia.
  specialize (IHl Hin); lia.
Qed.
Lemma iter_max_leq (l1 l2: list nat):
  (forall x, In x l1 -> In x l2) ->
  iter_max l1 <= iter_max l2.
Proof.
  induction l1 as [| h t IH]; simpl; intros Hin; [lia|].
  assert (h <= iter_max l2) by (apply iter_max_in; auto).
  assert (iter_max t <= iter_max l2) by auto.
  lia.
Qed.


(*Prove that for every cs(ps) in [populate_all], (cs, length ps) is in [get_constrs_in]*)

(*Previous lemma iff but not strong enough*)
Lemma populate_all_in_strong is_constr rl o cs pats:
  simplified rl ->
  populate_all is_constr rl = Some o ->
  amap_get funsym_eq_dec (fst o) cs = Some pats -> 
    existsb (constr_args_at_head cs pats) rl.
Proof.
  intros Hsimpl. unfold populate_all.
  destruct (get_heads rl) as[heads|] eqn : Hhead; [|discriminate].
  rewrite fold_left_right_opt.
  unfold constr_at_head_ex.
  rewrite <- (rev_involutive rl) at 1.
  rewrite existsb_rev. 
  assert (Hhead1: get_heads (rev rl) = Some (rev heads)). {
    rewrite get_heads_rev, Hhead. reflexivity.
  }
  clear Hhead.
  rewrite <- simplified_rev in Hsimpl.
  (*Now, same direction*)
  generalize dependent (rev heads).
  revert o.
  revert cs.
  revert pats.
  induction (rev rl) as [| [ps a] t IH]; simpl; auto; intros o cs pats.
  - intros l. inv Hsome. simpl.
    inv Hsome. simpl. rewrite amap_empty_get. discriminate. 
  - intros head. destruct ps as [| phd ptl]; try discriminate.
    destruct (get_heads t) as [heads1|] eqn : Hheads2; simpl; try discriminate.
    inv Hsome. simpl.
    match goal with 
    | |- context [option_bind ?o ?f] => destruct o as [p|] eqn : Hfold; simpl; try discriminate end.
    unfold simplified in Hsimpl.
    unfold constr_args_at_head at 1; simpl.
    (*simplified assumption means we only care about constr and wildcard*)
    destruct phd; simpl in *; auto; try discriminate.
    + destruct p as [css csl]; simpl in *.
      destruct (is_constr f); try discriminate.
      rewrite amap_mem_spec.
      destruct (amap_get funsym_eq_dec css f) as [fy|] eqn : Hmem.
      * inv Hsome. simpl in *. 
        destruct (funsym_eqb_spec f cs); simpl; subst; auto.
        -- destruct (list_eqb_spec _ pattern_eqb_spec o l0); subst; auto.
          intros Hget. rewrite Hget in Hmem. inversion Hmem; subst. simpl.
          eapply IH; eauto.
        -- intros Hget. apply (IH Hsimpl _ _ _  _ eq_refl Hfold). auto. 
      * inv Hsome. 
        simpl.
        destruct (funsym_eqb_spec f cs); simpl; subst.
        2: { rewrite amap_set_get_diff; auto. intros; eapply IH; eauto.
        }
        rewrite amap_set_get_same. inv Hsome.
        destruct (list_eqb_spec _ pattern_eqb_spec o o); subst; auto.
    + inv Hsome. eapply IH. assumption. reflexivity. auto.
Qed.

Lemma populate_all_get_constrs_in is_constr rl o cs ps:
  populate_all is_constr rl = Some o ->
  amap_get funsym_eq_dec (fst o) cs = Some ps ->
  In (cs, length ps) (get_constrs_in rl).
Proof.
  rewrite populate_all_simplify with (t:=tm_d).
  intros Hpop Hget.
  apply (populate_all_in_strong is_constr (simplify tm_d rl) o cs) in Hget; auto.
  2: apply simplify_simplified.
  rewrite <- get_constrs_in_simplify.
  apply constr_args_at_head_ex_in. apply Hget.
Qed.

(*The bound*)
Definition compile_size_bound (rl: list (list pattern * A)) : nat :=
  expand_size rl * (iter_max (map snd (get_constrs_in rl))).

(*And now, If n is above our bound, S matrix size decreases*)
Lemma s_matrix_bound_large_n is_constr n t rl cs l o:
  populate_all is_constr rl = Some o ->
  amap_mem funsym_eq_dec cs (fst o) ->
  constr_at_head_ex cs (simplify t rl) ->
  amap_get funsym_eq_dec (fst (dispatch1 t (fst o) rl)) cs = Some l ->
  n > compile_size_bound rl ->
  compile_size n l < compile_size n rl.
Proof.
  intros Hpop Htypes Hconstr Hget Hn.
  rewrite amap_mem_spec in Htypes.
  destruct (amap_get funsym_eq_dec (fst o) cs) as [ys |] eqn : Htypes'; try discriminate.
  pose proof (s_matrix_bound_in n _ _ _ _ _ _ Htypes' Hconstr Hget).
  revert Hn. unfold compile_size_bound.
  assert (length ys <= iter_max (map snd (get_constrs_in rl)));[| nia].
  apply iter_max_in. rewrite in_map_iff.
  exists (cs, length ys). split; auto.
  eapply populate_all_get_constrs_in. apply Hpop. auto.
Qed.
 
(*Part 7: [compile_size] only decreases as we recurse*)
(*Since [compile_size] is not constant, we show that it only decreaess, so our initial bound is always
  large enough*)

(*D matrix*)
Lemma dispatch2_gen_snd_constrs c types rl:
  In c (get_constrs_in (snd (dispatch2_gen types rl))) -> In c (get_constrs_in rl).
Proof.
  rewrite dispatch2_gen_snd.
  induction rl as [| [ps a] rtl IH]; simpl; auto.
  rewrite get_constrs_in_cons, in_app_iff. simpl.
  destruct ps as [| phd ptl]; simpl; auto.
  simpl.
  rewrite get_constrs_pat_list_cons, in_app_iff.
  destruct phd; simpl; auto.
  rewrite get_constrs_in_cons, in_app_iff. simpl.
  intros; destruct_all; auto.
Qed.

(*Simplification does not add constructors (there is an iff version provable but it is more compicated)*)
(* Lemma simplify_aux_constrs t a phd x c:
  In x (simplify_aux t a phd) ->
  In c (get_constrs_pat (fst x)) ->
  In c (get_constrs_pat phd).
Proof.
  revert a.
  induction phd; simpl; intros a; eauto; try (intros [Hx | []]; subst; simpl; auto).
  rewrite !in_app_iff. intros [Hs1 | Hs2] Hinc; [left | right]; eauto.
Qed.

Lemma simplify_constrs c t rl:
  In c (get_constrs_in (simplify t rl)) -> In c (get_constrs_in rl).
Proof.
  induction rl as [| [ps a] rtl IH]; simpl; auto.
  unfold simplify in *; simpl in *.
  destruct ps as [| phd ptl]; simpl; auto.
  rewrite get_constrs_in_app, get_constrs_in_cons, !in_app_iff; simpl.
  assert (In c (get_constrs_in (map (fun x : pattern * A => (fst x :: ptl, snd x)) (simplify_aux t a phd))) ->
    In c (get_constrs_pat_list (phd :: ptl))); [| intros; destruct_all; auto].
  unfold get_constrs_in. rewrite !map_map. simpl.
  rewrite get_constrs_pat_list_cons, in_app_iff.
  erewrite map_ext. 2: { intros. rewrite get_constrs_pat_list_cons. reflexivity. }
  rewrite (perm_in_iff c (perm_concat_map_app _ _ _)), in_app_iff.
  rewrite map_const, in_concat_repeat.
  2: { pose proof (null_simplify_aux t a phd). destruct (simplify_aux t a phd); simpl in *; try lia. discriminate. }
  rewrite in_concat.  intros [[fs [Hinfs Hinc]] | ?]; auto.
  rewrite in_map_iff in Hinfs.
  destruct Hinfs as [[p a1] [Hfs Hinpa]]; subst; simpl in *. left.
  eapply simplify_aux_constrs. apply Hinpa. assumption.
Qed. *)

Lemma d_matrix_constrs c t types rl:
  In c (get_constrs_in (snd (dispatch1 t types rl))) -> In c (get_constrs_in rl).
Proof.
  rewrite dispatch_equiv.
  unfold dispatch2.
  intros Hin1.
  apply dispatch2_gen_snd_constrs in Hin1.
  apply get_constrs_in_simplify in Hin1.
  assumption.
Qed.

Lemma d_matrix_compile_bound_gets_smaller t types (rl: list (list pattern * A)):
  compile_size_bound (snd (dispatch1 t types rl)) <= (compile_size_bound rl).
Proof.
  unfold compile_size_bound.
  apply Nat.mul_le_mono.
  - apply expand_size_d.
  - apply iter_max_leq.
    intros x. rewrite !in_map_iff.
    intros [c [Hx Hinc]]; subst.
    exists c. split; auto.
    apply d_matrix_constrs in Hinc; exact Hinc.
Qed.


(*And the same for the S matrix*)

Lemma get_constrs_pat_list_rev_in c l:
  In c (get_constrs_pat_list (rev l)) <-> In c (get_constrs_pat_list l).
Proof.
  apply perm_in_iff. unfold get_constrs_pat_list. rewrite map_rev. apply perm_concat_rev.
Qed.

Lemma dispatch2_gen_fst_constrs c cs types rl l:
  amap_mem funsym_eq_dec cs types ->
  amap_get funsym_eq_dec (fst (dispatch2_gen types rl)) cs = Some l ->
  In c (get_constrs_in l) -> In c (get_constrs_in rl).
Proof.
  intros Htypes.
  destruct (constr_at_head_ex cs rl || wild_at_head_ex rl) eqn : Hconstr.
  2: { rewrite dispatch2_gen_fst_notin in Hconstr; eauto. rewrite Hconstr; auto. discriminate. }
  rewrite amap_mem_spec in Htypes. 
  destruct (amap_get funsym_eq_dec types cs) as [ys|] eqn : Htypes'; try discriminate.
  rewrite dispatch2_gen_fst_in with (ys:=ys); auto.
  clear Hconstr.
  intros Hsome; inversion Hsome; subst; clear Hsome.
  induction rl as [| [ps a] rtl IH]; simpl; auto.
  rewrite get_constrs_in_cons, in_app_iff; simpl.
  destruct ps as [| phd ptl]; simpl; auto.
  rewrite get_constrs_pat_list_cons, in_app_iff; simpl.
  destruct phd; auto.
  - (*constr case*)
    destruct (funsym_eqb_spec f cs); subst; simpl; auto.
    rewrite get_constrs_in_cons; simpl.
    rewrite get_constrs_pat_list_app, !in_app_iff.
    rewrite get_constrs_pat_list_rev_in.
    unfold get_constrs_pat_list at 1.
    intros; destruct_all; auto.
  - (*Wild case*)
    simpl. rewrite get_constrs_in_cons, in_app_iff.
    simpl. rewrite get_constrs_pat_list_app, in_app_iff.
    assert (In c (get_constrs_pat_list (repeat Pwild (Datatypes.length ys))) -> False).
    { clear. induction (length ys); simpl; auto. }
    intros; destruct_all; auto.
Qed.

Lemma s_matrix_constrs cs c t types rl l:
  amap_mem funsym_eq_dec cs types ->
  amap_get funsym_eq_dec (fst (dispatch1 t types rl)) cs = Some l ->
  In c (get_constrs_in l) -> In c (get_constrs_in rl).
Proof.
  intros Htypes Hget Hinc.
  revert Hget.
  rewrite dispatch_equiv.
  unfold dispatch2.
  intros Hin1.
  apply dispatch2_gen_fst_constrs with (c:=c) in Hin1; auto.
  apply get_constrs_in_simplify in Hin1.
  assumption.
Qed.

Lemma s_matrix_compile_bound_get_smaller t types rl cs l:
  amap_mem funsym_eq_dec cs types ->
  amap_get funsym_eq_dec (fst (dispatch1 t types rl)) cs = Some l ->
  compile_size_bound l <= (compile_size_bound rl).
Proof.
  intros Htypes Hget.
  unfold compile_size_bound.
  apply Nat.mul_le_mono.
  - eapply expand_size_s; eauto.
  - apply iter_max_leq.
    intros x. rewrite !in_map_iff.
    intros [c [Hx Hinc]]. subst.
    exists c. split; auto.
    eapply s_matrix_constrs; eauto.
Qed.

(*It is important that the variables we add do not overlap with the other variables
  present in the matrix*)
Definition row_fv (row: list pattern * A) : list vsymbol :=
  big_union vsymbol_eq_dec pat_fv (fst row).
Definition pat_mx_fv (P: list (list pattern * A)) : list vsymbol :=
  big_union vsymbol_eq_dec row_fv P.

(*Variables in pattern actions*)
Variable (a_vars: A -> list vsymbol).
(*NOTE: include both bound and fv, not sure if we need all*)
Variable (a_let_vars: forall (v: vsymbol) (tm: term) (a: A),
  forall x, In x (a_vars (mk_let v tm a)) <-> v = x \/ In x (tm_bnd tm) \/ In x (tm_fv tm) \/
    In x (a_vars a)).

Definition pat_mx_act_vars (P: list (list pattern * A)) : list vsymbol :=
  big_union vsymbol_eq_dec (fun x => a_vars (snd x)) P.

Definition tmlist_vars (tl: list (term * vty)) : list vsymbol :=
  concat (map (fun x => tm_fv (fst x) ++ tm_bnd (fst x)) tl) .

(*Get all variables in the input*)
(*Problem is that this is very slow, don't want to precompute, should be OK for our purposes now*)
Definition compile_fvs (tl: list (term * vty)) (rl: list (list pattern * A)) :=
  tmlist_vars tl ++ pat_mx_fv rl ++ pat_mx_act_vars rl.

(*Part 9: Define the function*)

Obligation Tactic := idtac.

Definition compile_measure (rl: list (list pattern * A)) : nat :=
  compile_size (S (compile_size_bound rl)) rl.

(*Some more intermediate functions, for proofs:*)
Definition comp_cases (compile: list (term * vty) -> list (list pattern * A) -> option A) cases (tl: list (term * vty)) 
  := fun
  cs (al : list (term * vty)) =>
   match (amap_get funsym_eq_dec cases cs ) as o return amap_get funsym_eq_dec cases cs = o -> _ with
    | None => fun _ => None (*impossible*)
    | Some l => fun Hget => compile (rev al ++ tl) l
    end eq_refl
        .

Definition add (comp_cases: funsym -> list (term * vty) -> option A) 
  (t: term) (ty: vty) (rl: list (list pattern * A)) (tl: list (term * vty)) := fun

acc (x: funsym * list vty * list pattern) =>
  let '(cs, params, ql) := x in
  (*create variables*)
  let pat_tys :=  (map (ty_subst (s_params cs) params) (s_args cs)) in
  let new_var_names := gen_strs (length ql) (compile_fvs ((t, ty) :: tl) rl) in
  let typed_vars := (combine new_var_names pat_tys) in
  let vl := rev typed_vars in 
  let pl := rev_map Pvar vl in
  let al := rev_map Tvar vl in
  match (comp_cases cs (combine al (rev (map snd vl)))) with
  | None => None
  | Some v => Some ((Pconstr cs params pl, v) :: acc)
  end.

(*Instead of matching on t, which gives us lots of different cases,
  have this result:*)
Definition is_fun (t: term) : Either ({x : funsym * list vty * list term | t = Tfun (fst (fst x)) (snd (fst x)) (snd x)})
  { x: unit | forall cs tys tms, t <> Tfun cs tys tms}.
Proof.
  destruct t; try solve[apply Right; apply (exist _ tt); discriminate].
  apply Left. apply (exist _ (f, l, l0)). reflexivity.
Defined.

Definition comp_full (is_bare: bool) (comp_wilds : unit -> option A) comp_cases 
  (types: amap funsym (list pattern))
  (cslist: list (funsym * list vty * list pattern)) css t ty tl rl (_: unit) :=
    let no_wilds := 
      if is_bare then (*not using choose - we need to know it is the first one*)
        option_bind (option_map (fun x => match x with | (cs, _, _) => cs end)
          (List.head cslist)) (fun x =>
          Some (Nat.eqb (amap_size types) (f_num_constrs x))) 
      else Some (forallb (fun f => amap_mem funsym_eq_dec f types) css) in
    let base : option (list (pattern * A)) :=
      option_bind no_wilds (fun b => if b then Some nil else
    option_map (fun x => [(Pwild, x)]) (comp_wilds tt))
    in
    option_bind base (fun b =>
      option_map (fun b1 => mk_case t ty b1)  (fold_left_opt (add comp_cases t ty rl tl) cslist b)). 

Section Comp.
Variable bare: bool.
Variable simpl_constr : bool. (*Do we simplify
  match (Tfun f ts) with | ... end to 
  compile (ts) (S(P, f))?
  If yes, interacts poorly with rewriting, so we cannot
  use for exhaustiveness. But other parts of Why3 rely
  on this being done (e.g. for tuples). So we include
  both, prove all the specs for all except rewriting, 
  and prove that the (simpl_constr = false) case
  implies the (simpl_constr = true) case - it is only more restrictive
  Then we use the false case for exhaustivenss and true for
  compilation*)

Equations compile (tl: list (term * vty)) (rl: list (list pattern * A))
  : option A  by wf (compile_measure rl) lt :=
  compile _ [] := None;
  compile [] ((_, a) :: _) => Some a;
  compile ((t, ty) :: tl) rl =>
    (*No bare*)
    (*extract the set of constructors*)
    let is_bare_css :=
    match ty with
    | vty_cons ts _ => if bare then (true, nil) else (false, get_constructors ts)
    | _ => (false, nil)
    end in
    let is_bare := fst is_bare_css in
    let css := snd is_bare_css in
    let is_constr fs := 
    (*Need to check that f_is_constr because we need to check for
      constr in cases later (not true by typing)*)
      (f_is_constr fs) && (is_bare || in_bool funsym_eq_dec fs css) in

    (*Here, we do the simplify/dispatch*)

    (*Map every constructor ocurring at the head of the pattern list to the
      list of its args*)
    let types_cslist := populate_all is_constr rl in
    match types_cslist as o return o = types_cslist -> _ with
    | None => fun _ => None
    | Some types_cslist => fun Htypes => 
      (*NOTE: we don't have maps, not ideal*)
    let types := fst types_cslist in
    let cslist := snd types_cslist in
    
    (*dispatch part*)
    match dispatch1_opt t types rl as o return dispatch1_opt t types rl = o -> _ with
    | None => fun _ => None
    | Some casewild => fun Hdispatch1 =>
    let cases := fst casewild in
    let wilds := snd casewild in

    let comp_wilds (_: unit) := compile tl wilds in


    let comp_cases cs (al : list (term * vty)) :=
         match (amap_get funsym_eq_dec cases cs ) as o return amap_get funsym_eq_dec cases cs = o -> _ with
          | None => fun _ => None (*impossible*)
          | Some l => fun Hget => compile (rev al ++ tl) l
          end eq_refl
        in

    let comp_full := comp_full is_bare comp_wilds comp_cases types cslist css t ty tl rl in
    
    if amap_is_empty types then comp_wilds tt
    else

    if simpl_constr then
      match (is_fun t) with
      | Left Hconstr =>
        let '(cs, params, al) := proj1_sig Hconstr in
          if is_constr cs then
          if amap_mem funsym_eq_dec cs types then comp_cases cs (combine al
            (map (ty_subst (s_params cs) params) (s_args cs))) else comp_wilds tt
          else comp_full tt
      | Right Hnotconstr =>
        comp_full tt
      end
    else comp_full tt


    (*NOTE: remove Tfun case - interacts poorly with rewriting*)

    (* comp_full tt *)

    (* match (is_fun t) with
    | Left Hconstr =>
      let '(cs, params, al) := proj1_sig Hconstr in
        if is_constr cs then
        if amap_mem funsym_eq_dec cs types then comp_cases cs (combine al
          (map (ty_subst (s_params cs) params) (s_args cs))) else comp_wilds tt
        else comp_full tt
    | Right Hnotconstr =>
      comp_full tt
    end *)
    
end eq_refl
end eq_refl.
Next Obligation.
intros t ty tl phd ptl compile rl is_bare_css is_bare css is_constr types_cslist t2 Heqt2 types cslist casewild Hdispatch cases wilds _.
fold rl.
unfold compile_measure.
unfold wilds.  apply dispatch1_opt_some in Hdispatch.
destruct Hdispatch as [Hnotnull Hcasewild]. rewrite Hcasewild.
eapply Nat.le_lt_trans.
- apply compile_size_mono_le, le_n_S, (d_matrix_compile_bound_gets_smaller t types rl).
- apply d_matrix_smaller; auto.
Defined.
Next Obligation.
intros t ty tl p ptl compile rl is_bare_css is_bare css is_constr types_cslist t2 Heqt2 types cslist casewild Hdispatch cases wilds _ cs _ l Hget.
apply dispatch1_opt_some in Hdispatch.
destruct Hdispatch as [Hnotnull Hcasewild]. 
fold rl.
unfold compile_measure.
pose proof (s_matrix_compile_bound_get_smaller t types rl cs l) as Hsmall.
revert Hget. unfold cases. rewrite Hcasewild. intros Hget.
assert (Htypes: amap_mem funsym_eq_dec cs types) by (eapply constrs_in_types; eauto).
specialize (Hsmall Htypes Hget).
eapply Nat.le_lt_trans.
- apply compile_size_mono_le, le_n_S. apply Hsmall.
- eapply (s_matrix_bound_large_n _ _ t rl cs l); auto. apply (eq_sym Heqt2). all: auto.
  pose proof (dispatch1_in_types rl t types cs) as Hdisj.
  rewrite amap_mem_spec in Hdisj.
  rewrite Hget in Hdisj. specialize (Hdisj eq_refl).
  destruct Hdisj as [Hincs | Hintypes]; auto.
  rewrite <- populate_all_in. apply Hintypes.
  apply simplify_simplified. rewrite <- populate_all_simplify. apply (eq_sym Heqt2).
Defined.

(*It is much simpler to work with simplified pattern matrices. We show that (in the interesting case),
  we are free to assume that our matrix is simplified for [compile]. First, some lemmas*)

(*Simplifying twice does nothing*)

Lemma simplified_simplify_aux 
  t a p:
  simplified_aux p ->
  simplify_aux t a p = [(p, a)].
Proof.
  induction p; simpl; try discriminate; auto.
Qed.

Lemma simplified_simplify (t : term) (rl : list (list pattern * A)):
  simplified rl ->
  simplify t rl = rl.
Proof.
  induction rl as [| [ps a] rtl IH]; simpl.
  - intros _. reflexivity.
  - destruct ps as [| phd ptl]; simpl; auto.
    + intros Htl. unfold simplify in *. simpl. f_equal. auto.
    + intros Hsimp. apply andb_prop in Hsimp.
      destruct Hsimp as [Hhd Htl].
      unfold simplify in *. simpl. rewrite IH; auto.
      rewrite simplified_simplify_aux; auto.
Qed.

Lemma simplify_twice (t : term) (rl : list (list pattern * A)):
  simplify t (simplify t rl) = simplify t rl.
Proof.
  apply simplified_simplify, simplify_simplified.
Qed.

Lemma dispatch1_simplify t types P:
  dispatch1 t types (simplify t P) = dispatch1 t types P.
Proof.
  rewrite !dispatch_equiv.
  unfold dispatch2.
  rewrite simplify_twice.
  reflexivity.
Qed.

Lemma dispatch1_opt_simplify t types P : 
  dispatch1_opt t types (simplify t P) = dispatch1_opt t types P.
Proof.
  destruct (dispatch1_opt _ _ P) as [l1|] eqn : Hd1.
  - apply dispatch1_opt_some in Hd1.
    destruct Hd1 as [Hall Hl1].
    apply dispatch1_opt_some.
    split.
    + rewrite <- simplify_all_null. auto.
    + rewrite dispatch1_simplify; assumption.
  - apply dispatch1_opt_none in Hd1.
    apply dispatch1_opt_none.
    rewrite existsb_forallb_negb in Hd1 |- *.
    rewrite <- simplify_all_null. auto.
Qed.

(*[compile_fv] is invariant under simplifying*)

Lemma tmlist_vars_cons t tms: tmlist_vars (t :: tms) =
  tm_fv (fst t) ++ tm_bnd (fst t) ++ tmlist_vars tms.
Proof. unfold tmlist_vars; simpl. rewrite app_assoc; auto.
Qed.

Lemma pat_mx_fv_app x p1 p2:
  In x (pat_mx_fv (p1 ++ p2)) <-> In x (pat_mx_fv p1) \/ In x (pat_mx_fv p2).
Proof.
  unfold pat_mx_fv. rewrite big_union_app. simpl_set_small. reflexivity.
Qed.

Lemma pat_mx_act_vars_app x p1 p2:
  In x (pat_mx_act_vars (p1 ++ p2)) <-> In x (pat_mx_act_vars p1) \/ In x (pat_mx_act_vars p2).
Proof.
  unfold pat_mx_act_vars. rewrite big_union_app. simpl_set_small. reflexivity.
Qed. 

Lemma compile_fv_simplify (tms: list (term * vty)) (P: list (list pattern * A)) t ty:
  forall x, 
    In x (compile_fvs ((t, ty) :: tms) P) <->
    In x (compile_fvs ((t, ty) :: tms) (simplify t P)).
Proof.
  unfold simplify. unfold compile_fvs.
  intros x.
  rewrite !in_app_iff.
  rewrite !tmlist_vars_cons. simpl. 
  rewrite !in_app_iff.
  induction P as [| rhd rtl IH]; [reflexivity|simpl].
  simpl_set_small.
  rewrite !pat_mx_fv_app, ! pat_mx_act_vars_app.
  (*We need 2 directions: if in [simplify_single] vars, then in original
    and if in original, then in [simplify_single] vars or in term*)
  assert (Hsingle1: 
    In x (pat_mx_fv (simplify_single t rhd)) \/
    In x (pat_mx_act_vars (simplify_single t rhd)) ->
    In x (row_fv rhd) \/ In x (a_vars (snd rhd)) \/ In x (tm_fv t) \/ In x (tm_bnd t)
  ).
  {
    clear -a_let_vars. destruct rhd as [ps a]. simpl.
    destruct ps as [| phd ptl]; simpl. 
    { simpl_set_small; simpl. intros; destruct_all; auto. }
    unfold row_fv; simpl. simpl_set_small.
    generalize dependent a.
    induction phd; simpl; intros a; try solve[
      unfold row_fv; simpl; simpl_set_small; simpl;
      try(rewrite a_let_vars); intros; destruct_all; auto; contradiction 
    ].
    - (*Por*)
      unfold pat_mx_fv in *. 
      rewrite !map_app, !big_union_app; simpl_set_small.
      rewrite pat_mx_act_vars_app.
      intros [[Hin1 | Hin2] | [Hin1 | Hin2]];
      [specialize (IHphd1 _ (or_introl Hin1)) | 
       specialize (IHphd2 _ (or_introl Hin2)) |
       specialize (IHphd1 _ (or_intror Hin1)) |
       specialize (IHphd2 _ (or_intror Hin2))];
      destruct_all; auto.
    - (*Pbind*)
      intros Hin. apply IHphd in Hin.
      rewrite a_let_vars in Hin. simpl_set_small.
      destruct_all; auto.
  }
  (*And the other direction*)
  assert (Hsingle2: 
    In x (row_fv rhd) \/ In x (a_vars (snd rhd)) ->
    In x (pat_mx_fv (simplify_single t rhd)) \/
    In x (pat_mx_act_vars (simplify_single t rhd))).
  {
    clear -a_let_vars. destruct rhd as [ps a]. simpl.
    destruct ps as [| phd ptl]; simpl. 
    { simpl_set_small; simpl. intros; destruct_all; auto. }
    unfold row_fv; simpl. simpl_set_small.
    generalize dependent a.
    induction phd; simpl; intros a; try solve[
      unfold row_fv; simpl; simpl_set_small; simpl;
      try(rewrite a_let_vars); intros; destruct_all; auto 10; contradiction 
    ].
    -  (*Por*)
      unfold pat_mx_fv in *. 
      rewrite !map_app, !big_union_app; simpl_set_small.
      rewrite pat_mx_act_vars_app.
      intros [[[Hin | Hin] | Hin] | Hin];
      [specialize (IHphd1 a (or_introl (or_introl Hin))) |
       specialize (IHphd2 a (or_introl (or_introl Hin))) |
       specialize (IHphd1 a (or_introl (or_intror Hin))) |
       specialize (IHphd1 a (or_intror Hin))];
      destruct_all; auto.
    - (*Pbind*)
      simpl_set_small.
      intros Hin. apply IHphd. rewrite a_let_vars. destruct_all; auto.
  }
  (*Now we can solve this (by lots of cases)*)
  destruct IH as [IH1 IH2]; split.
  -
  intros; destruct_all; auto;
    (forward Hsingle2; [solve[auto]|]) +
    (forward IH1; [solve[auto]|]);
    destruct_all; auto.
  - intros; destruct_all; auto;
    (forward Hsingle1; [solve[auto]|]) +
    (forward IH2; [solve[auto]|]);
    destruct_all; auto.
Qed.

(*And therefore, [gen_strs] are equivalent*)
Lemma compile_gen_strs_simplify (tms: list (term * vty)) (P: list (list pattern * A)) t ty n:
  gen_strs n (compile_fvs ((t, ty) :: tms) (simplify t P)) =
  gen_strs n (compile_fvs ((t, ty) :: tms) P).
Proof.
apply gen_strs_ext. intros; rewrite <- compile_fv_simplify. reflexivity.
Qed.

Lemma fold_left_opt_change_f {B C: Type} (f1 f2: B -> C -> option B) (l: list C) (x: B):
  (forall b c, f1 b c = f2 b c) ->
  fold_left_opt f1 l x = fold_left_opt f2 l x.
Proof.
  intros Hext.
  revert x. induction l; simpl; auto.
  intros x. rewrite Hext. destruct (f2 x a); auto.
Qed.
 
Ltac case_match_goal :=
  repeat match goal with 
        |- (match ?p with |Some l => ?x | None => ?y end) = ?z =>
          let Hp := fresh "Hmatch" in 
          destruct p eqn: Hp end; auto.

Lemma add_simplify_eq: forall comp_cases t ty P ts acc x,
  add comp_cases t ty P ts acc x = add comp_cases t ty (simplify t P) ts acc x.
Proof.
intros comp_cases t ty P ts acc [[f1 tys1] ps1]; simpl.
rewrite compile_gen_strs_simplify.
reflexivity.
Qed.

Lemma fold_left_opt_simplify_eq comp_cases t ty P ts x y:
  fold_left_opt (add comp_cases t ty (simplify t P) ts) x y =
  fold_left_opt (add comp_cases t ty P ts) x y.
Proof.
  apply fold_left_opt_change_f.
  intros. symmetry. apply add_simplify_eq.
Qed.

Lemma comp_full_simplify_eq is_bare comp_wilds comp_cases types cslist css t ty tl P x:
  comp_full is_bare comp_wilds comp_cases types cslist css t ty tl (simplify t P) x =
  comp_full is_bare comp_wilds comp_cases types cslist css t ty tl P x.
Proof.
  unfold comp_full.
  destruct is_bare.
  -destruct (hd_error _); simpl; auto.
    destruct (Nat.eqb _ _); simpl; auto.
    + rewrite fold_left_opt_simplify_eq. reflexivity.
    + destruct (comp_wilds tt); simpl; auto. 
      rewrite fold_left_opt_simplify_eq. reflexivity.
  - destruct (forallb _ _); simpl; auto.
    + rewrite fold_left_opt_simplify_eq. reflexivity.
    + destruct (comp_wilds tt); simpl; auto.  
      rewrite fold_left_opt_simplify_eq. reflexivity.
Qed.

Lemma compile_simplify (tms: list (term * vty)) (P: list (list pattern * A))  t ty:
  compile ((t, ty) :: tms) P =
  compile ((t, ty) :: tms) (simplify t P).
Proof.
  destruct P as [| row P']; simp compile; auto.
  destruct ((simplify t (row :: P'))) as [| s1 stl] eqn : Hsimp.
  {
    exfalso. revert Hsimp. rewrite <- null_nil, null_simplify. simpl. auto.
  }
  simp compile.
  set (bare_css := match ty with
    | vty_cons ts _ =>
        if bare then (true, []) else (false, get_constructors ts)
    | _ => (false, [])
    end) in *.
  set (P := row :: P') in *.
  rewrite <- Hsimp.
  Opaque dispatch1_opt.
  simpl.
  set (is_constr := fun fs => (f_is_constr fs) && (fst bare_css || in_bool funsym_eq_dec fs (snd bare_css))) in *.
  rewrite <- populate_all_simplify.
  destruct (populate_all is_constr P) as [types_cslist|] eqn : Hpop; [| reflexivity].
  rewrite dispatch1_opt_simplify.
  destruct (dispatch1_opt t (fst types_cslist) P) as [casewild|] eqn : Hdispatch; try reflexivity.
  destruct (amap_is_empty (fst types_cslist)); auto.
  rewrite comp_full_simplify_eq; reflexivity.
Qed.

Lemma iter_max_eq l1 l2:
  (forall x, In x l1 <-> In x l2) ->
  iter_max l1 = iter_max l2.
Proof.
  intros Hallin.
  apply Nat.le_antisymm; apply iter_max_leq; intros; apply Hallin; auto.
Qed.

Lemma compile_measure_simplify t rl:
  compile_measure (simplify t rl) = compile_measure rl.
Proof.
  unfold compile_measure, compile_size.
  rewrite expand_full_simplify.
  unfold compile_size_bound.
  rewrite expand_size_simplify.
  f_equal. f_equal. f_equal. apply iter_max_eq.
  intros x. 
  rewrite !in_map_iff.
  split; intros [y [Hx Hinx]]; subst; exists y; split; auto; revert Hinx;
  rewrite get_constrs_in_simplify; auto.
Qed.

(*Now we can prove an induction principle for [compile]. In the interesting cases,
  we can assume our pattern matrix is simplified thanks to the above*)

Lemma compile_ind (P: list (term * vty) -> list (list pattern * A) -> option A -> Prop)
  (P_simp: forall t ty tms rl,
    P ((t, ty) :: tms) (simplify t rl) (compile ((t, ty) :: tms) (simplify t rl)) ->
    P ((t, ty) :: tms) rl (compile ((t, ty) :: tms) rl))
  (Hnone: forall tl, P tl nil None)
  (Hemp: forall ps a l, P nil ((ps, a) :: l) (Some a))
  (Hilltyped: forall t ty tl rl,
    let is_bare_css :=
    match ty with
    | vty_cons ts _ => if bare then (true, nil) else (false, get_constructors ts)
    | _ => (false, nil)
    end in
    let is_bare := fst is_bare_css in
    let css := snd is_bare_css in
    let is_constr fs := 
      f_is_constr fs && (is_bare || in_bool funsym_eq_dec fs css) in
    simplified rl ->
    (populate_all is_constr rl = None \/
      exists types_cslist,
        (populate_all is_constr rl) = Some types_cslist /\
        let types := fst types_cslist in
        let cslist := snd types_cslist in
        dispatch1_opt t types rl = None 
    ) ->
    P ((t, ty) :: tl) rl None
  )
  (Hconstr: forall t ty tl rl rhd rtl,
    let is_bare_css :=
    match ty with
    | vty_cons ts _ => if bare then (true, nil) else (false, get_constructors ts)
    | _ => (false, nil)
    end in
    let is_bare := fst is_bare_css in
    let css := snd is_bare_css in
    let is_constr fs := 
      f_is_constr fs && (is_bare || in_bool funsym_eq_dec fs css) in
    simplified rl ->
    rl = rhd :: rtl ->
    (* let types_cslist := populate_all is_constr rl in *)
    forall types_cslist (Htypes: (populate_all is_constr rl) = Some types_cslist),
      (*NOTE: we don't have maps, not ideal*)
      let types := fst types_cslist in
      let cslist := snd types_cslist in
      forall casewild (Hdispatch1 : dispatch1_opt t types rl = Some casewild),
        let cases := fst casewild in
        let wilds := snd casewild in
        (*wilds*)
        P tl wilds (compile tl wilds) /\
        (forall cs al l (Hget: amap_get funsym_eq_dec cases cs = Some l),
          P (rev al ++ tl) l (compile (rev al ++ tl) l)) ->
    P ((t, ty) :: tl) rl (
      let comp_wilds (_: unit) := compile tl wilds in

      let comp_cases cs (al : list (term * vty)) :=
        comp_cases compile cases tl cs al in

      let comp_full := comp_full is_bare comp_wilds comp_cases types cslist css t ty tl rl in
      
      if amap_is_empty types then comp_wilds tt
      else
        if simpl_constr then
        match (is_fun t) with
        | Left Hconstr =>
          let '(cs, params, al) := proj1_sig Hconstr in
            if is_constr cs then
            if amap_mem funsym_eq_dec cs types then comp_cases cs (combine al
              (map (ty_subst (s_params cs) params) (s_args cs))) else comp_wilds tt
            else comp_full tt
        | Right Hnotconstr =>
          comp_full tt
        end
      else comp_full tt)):
      (* match (is_fun t) with
          | Left Hconstr =>
            let '(cs, params, al) := proj1_sig Hconstr in
              if is_constr cs then
              if amap_mem funsym_eq_dec cs types then comp_cases cs (combine al
                (map (ty_subst (s_params cs) params) (s_args cs))) else comp_wilds tt
              else comp_full tt
          | Right Hnotconstr =>
            comp_full tt
          end)): *)

  forall ts p, P ts p (compile ts p).
Proof.
  intros ts rl.
  (*Prove by strong induction on size*)
  remember (compile_measure rl) as n eqn : Hsize.
  generalize dependent rl.
  revert ts.
  induction n as [ n IHn ] using (well_founded_induction lt_wf).
  intros [| [t ty] ts] [| [phd a] rtl] Hn; subst; try solve[simp compile].
  rewrite compile_simplify.
  set (rl := ((phd, a) :: rtl)) in *.
  set (simplify t rl) as rl' in *.
  specialize (P_simp t ty ts rl); revert P_simp. fold rl'.
  destruct rl' as [|[phd1 a1] rtl1] eqn : Hsimpeq.
  {
    exfalso. assert (Hnull: null (simplify t rl)). {
      fold rl'. rewrite Hsimpeq. reflexivity.
    }
    rewrite null_simplify in Hnull. discriminate.
  }
  unfold rl at 2.
  simp compile.
  rewrite <- Hsimpeq.
  fold rl.
  assert (Hsimp: simplified rl') by (apply simplify_simplified). 
  specialize (Hconstr t ty ts rl'); revert Hconstr.
  (*Simplify goal*)
  set (bare_css := match ty with
  | vty_cons ts _ =>
      if bare then (true, []) else (false, get_constructors ts)
  | _ => (false, [])
  end) in *.
  Opaque dispatch1_opt.
  simpl.
  set (is_constr := fun fs => f_is_constr fs && ((fst bare_css) || in_bool funsym_eq_dec fs (snd bare_css))) in *.
  intros Hconstr.
  replace (populate_all is_constr rl) with (populate_all is_constr rl') by (symmetry; apply populate_all_simplify).
  destruct (populate_all is_constr rl') as [types_cslist|] eqn : Hpop.
  2: {
    intros P_ext. apply P_ext. apply Hilltyped; auto.
  }
  replace (dispatch1_opt t (fst types_cslist) rl) with
    (dispatch1_opt t (fst types_cslist) rl') by (apply dispatch1_opt_simplify).
  destruct ((dispatch1_opt t (fst types_cslist) rl')) as [casewild|] eqn : Hdispatch1.
  2: {
    intros P_ext; apply P_ext.
    apply Hilltyped; auto. right. exists types_cslist. split; auto. 
  }
  specialize (Hconstr (phd1, a1) rtl1 Hsimp Hsimpeq types_cslist eq_refl casewild Hdispatch1).
  revert Hconstr.
  rewrite Hsimpeq at 2.
  simp compile.
  (*One more round of simplifying, then we just have to prove the IH*)
  subst bare_css.
  set (bare_css := match ty with
  | vty_cons ts _ =>
      if bare then (true, []) else (false, get_constructors ts)
  | _ => (false, [])
  end) in *.
  simpl.
  subst is_constr.
  set (is_constr := fun fs => f_is_constr fs && ((fst bare_css) || in_bool funsym_eq_dec fs (snd bare_css))) in *.
  rewrite <- Hsimpeq.
  intros Hconstr P_ext.
  unfold rl'. rewrite comp_full_simplify_eq. fold rl'.
  apply P_ext.
  apply Hconstr.
  (*All that is left is proving the IH from our strong induction IH*)
  split.
  - eapply IHn. 2: reflexivity.
    (*First case, repeat proof from Equations*)
    unfold compile_measure.
    apply dispatch1_opt_some in Hdispatch1.
    destruct Hdispatch1 as [Hnotnull Hcasewild]. rewrite Hcasewild.
    unfold rl'. rewrite dispatch1_simplify.
    eapply Nat.le_lt_trans.
    + apply compile_size_mono_le, le_n_S, (d_matrix_compile_bound_gets_smaller t (fst types_cslist) rl).
    + apply d_matrix_smaller; auto.
      unfold rl' in Hnotnull.
      rewrite <- simplify_all_null in Hnotnull.
      apply Hnotnull.
  - intros cs al l Hget. eapply IHn.   2: reflexivity.
    replace (compile_measure rl) with (compile_measure rl') by (apply compile_measure_simplify).
    apply dispatch1_opt_some in Hdispatch1.
    destruct Hdispatch1 as [Hnotnull Hcasewild]. 
    unfold compile_measure.
    pose proof (s_matrix_compile_bound_get_smaller t (fst types_cslist) rl' cs l) as Hsmall.
    revert Hget. rewrite Hcasewild. intros Hget.
    assert (Htypes: amap_mem funsym_eq_dec cs (fst types_cslist)) by (eapply constrs_in_types; eauto).
    specialize (Hsmall Htypes Hget).
    eapply Nat.le_lt_trans.
    + apply compile_size_mono_le, le_n_S. apply Hsmall.
    + eapply (s_matrix_bound_large_n _ _ t rl' cs l); auto. apply Hpop.  all: auto.
      pose proof (dispatch1_in_types rl' t (fst types_cslist) cs) as Hdisj.
      rewrite amap_mem_spec in Hdisj.
      rewrite Hget in Hdisj. specialize (Hdisj eq_refl).
      destruct Hdisj as [Hincs | Hintypes]; auto.
      rewrite <- populate_all_in. apply Hintypes.
      apply simplify_simplified. rewrite <- populate_all_simplify. apply Hpop.
Qed.

(*Another form, where each case is separated*)

Lemma dispatch1_equiv_default t types 
  (rl: list (list pattern * A)):
  simplified rl -> (*Makes things easier*)
  snd (dispatch1 t types rl) = default rl.
Proof.
  intros Hsimp.
  rewrite dispatch_equiv.
  unfold dispatch2.
  rewrite simplified_simplify; auto.
  rewrite dispatch2_gen_snd.
  reflexivity.
Qed.

Lemma compile_ind' (P: list (term * vty) -> list (list pattern * A) -> option A -> Prop)
  (P_simp: forall t ty tms rl,
    P ((t, ty) :: tms) (simplify t rl) (compile ((t, ty) :: tms) rl) ->
    P ((t, ty) :: tms) rl (compile ((t, ty) :: tms) rl))
  (Hnone: forall tl, P tl nil None)
  (Hemp: forall ps a l, P nil ((ps, a) :: l) (Some a))
  (Hilltyped: forall t ty tl rl,
    let is_bare_css :=
    match ty with
    | vty_cons ts _ => if bare then (true, nil) else (false, get_constructors ts)
    | _ => (false, nil)
    end in
    let is_bare := fst is_bare_css in
    let css := snd is_bare_css in
    let is_constr fs := 
      f_is_constr fs && (is_bare || in_bool funsym_eq_dec fs css) in
    simplified rl ->
    (populate_all is_constr rl = None \/
      exists types_cslist,
        (populate_all is_constr rl) = Some types_cslist /\
        let types := fst types_cslist in
        let cslist := snd types_cslist in
        dispatch1_opt t types rl = None 
    ) ->
    P ((t, ty) :: tl) rl None
  )
  (*Separate out cases*)
  (Hwildscase: forall t ty tl rl rhd rtl,
    let is_bare_css :=
    match ty with
    | vty_cons ts _ => if bare then (true, nil) else (false, get_constructors ts)
    | _ => (false, nil)
    end in
    let is_bare := fst is_bare_css in
    let css := snd is_bare_css in
    let is_constr fs := 
      f_is_constr fs && (is_bare || in_bool funsym_eq_dec fs css) in
    forall (Hsimpl: simplified rl) (Hrl: rl = rhd :: rtl) 
      types_cslist (Htypes: (populate_all is_constr rl) = Some types_cslist),
    let types := fst types_cslist in
    let cslist := snd types_cslist in
    forall casewild (Hcasewild : casewild = dispatch1 t types rl) (Hnotnull: forallb (fun x => negb (null (fst x))) rl),
    let cases := fst casewild in
    let wilds := snd casewild in
    forall (Hwild: wilds = default rl) (IHwilds: P tl (default rl) (compile tl wilds))
    (Hwildcases: amap_is_empty types \/ 
      if simpl_constr then 
      match (is_fun t) with
      | Left Hconstr =>
        let '(cs, params, al) := proj1_sig Hconstr in
          is_constr cs && amap_mem funsym_eq_dec cs types = false
      | _ => False
      end
      else False),
    P ((t, ty) :: tl) rl (compile tl wilds))
  (Hfullcase: forall t ty tl rl rhd rtl,
    let is_bare_css :=
    match ty with
    | vty_cons ts _ => if bare then (true, nil) else (false, get_constructors ts)
    | _ => (false, nil)
    end in
    let is_bare := fst is_bare_css in
    let css := snd is_bare_css in
    let is_constr fs := 
      f_is_constr fs && (is_bare || in_bool funsym_eq_dec fs css) in
    forall (Hsimpl: simplified rl) (Hrl: rl = rhd :: rtl) 
      types_cslist (Htypes: (populate_all is_constr rl) = Some types_cslist),
    let types := fst types_cslist in
    let cslist := snd types_cslist in
    forall casewild (Hcasewild : casewild = dispatch1 t types rl) (Hnotnull: forallb (fun x => negb (null (fst x))) rl),
      let cases := fst casewild in
      let wilds := snd casewild in
      forall
      (IHwilds: P tl (default rl) (compile tl wilds))
      (IHconstrs: forall cs al l (Hget: amap_get funsym_eq_dec cases cs = Some l),
        P (rev al ++ tl) l (compile (rev al ++ tl) l))
      (Hisemp: amap_is_empty types = false),
    P ((t, ty) :: tl) rl (
      let comp_wilds (_: unit) := compile tl wilds in

      let comp_cases cs (al : list (term * vty)) :=
        comp_cases compile cases tl cs al in

      let comp_full := comp_full is_bare comp_wilds comp_cases types cslist css t ty tl rl in
      comp_full tt))
  (Hconstrcase: forall t ty tl rl rhd rtl cs params tms,
    let is_bare_css :=
    match ty with
    | vty_cons ts _ => if bare then (true, nil) else (false, get_constructors ts)
    | _ => (false, nil)
    end in
    let is_bare := fst is_bare_css in
    let css := snd is_bare_css in
    let is_constr fs := 
      f_is_constr fs && (is_bare || in_bool funsym_eq_dec fs css) in
    forall (Hsimpl: simplified rl) (Hrl: rl = rhd :: rtl) 
      types_cslist (Htypes: (populate_all is_constr rl) = Some types_cslist),
      (*NOTE: we don't have maps, not ideal*)
      let types := fst types_cslist in
      let cslist := snd types_cslist in
      forall casewild (Hcasewild : casewild = dispatch1 t types rl) (Hnotnull: forallb (fun x => negb (null (fst x))) rl),
        let cases := fst casewild in
        let wilds := snd casewild in
      forall (IHwilds: P tl (default rl) (compile tl wilds))
        (IHconstrs: forall cs al l (Hget: amap_get funsym_eq_dec cases cs = Some l),
          P (rev al ++ tl) l (compile (rev al ++ tl) l))
        (Hisemp: amap_is_empty types = false)
        (Hsimplconstr: simpl_constr = true)
        (Ht: t = Tfun cs params tms)
        (Hisconstr: is_constr cs)
        (Hmem: amap_mem funsym_eq_dec cs types),
    
    P ((t, ty) :: tl) rl (
       comp_cases compile cases tl cs (combine tms
              (map (ty_subst (s_params cs) params) (s_args cs))))):

    forall ts p, P ts p (compile ts p).
Proof.
  apply compile_ind; auto.
  - setoid_rewrite <- compile_simplify. auto.
  - intros. destruct H1 as [IHwilds IHconstrs]. simpl.
    apply dispatch1_opt_some in Hdispatch1.
    destruct Hdispatch1 as [Hnotnull Hcasewild]; subst casewild.
    (*prove wilds equiv*)
    assert (Hwilds: wilds = default rl). {
      unfold wilds.
      rewrite dispatch1_equiv_default; auto.
    }
    destruct (amap_is_empty types) eqn : Hisemp; eauto.
    { eapply Hwildscase; eauto. rewrite <- Hwilds; auto. }
    destruct simpl_constr; eauto; [| eapply Hfullcase; eauto; rewrite <- Hwilds; auto].
    specialize (Hwildscase t ty tl rl rhd rtl).
    destruct (is_fun t) as [[[ [cs params] tms] Ht]|]; [| eapply Hfullcase; eauto; rewrite <- Hwilds; auto].
    simpl in Ht |- *.  destruct (is_constr cs) eqn : Hconstr; [| eapply Hfullcase; eauto; rewrite <- Hwilds; auto].
    destruct (amap_mem funsym_eq_dec cs types) eqn : Hmem; [eapply Hconstrcase; eauto; rewrite <- Hwilds; auto|].
    eapply Hwildscase; eauto. rewrite <- Hwilds; auto. right. simpl.
    apply andb_false_iff. right; auto.
Qed.

(*And now a version to prove goals of the form [compile tms rl = Some t1 -> P t1]*)


(*A "map" version of "add" (asusming all options are Some) that is more pleasant to work with*)
Definition add_map
(comp_cases : funsym -> list (term * vty) -> option A) (t: term) 
ty tl rl :=
(fun (x: funsym * list vty * list pattern) =>
          let '(cs, params, ql) := x in 
          let pat_tys := map (ty_subst (s_params cs) params) (s_args cs) in 
          let new_var_names := gen_strs (Datatypes.length ql) (compile_fvs ((t, ty) :: tl) rl) in
          let typed_vars := (combine new_var_names pat_tys) in
          let vl := rev typed_vars in 
          let pl := rev_map Pvar vl in 
          let al := rev_map Tvar vl in
          (Pconstr cs params pl, comp_cases cs (combine al (rev (map snd vl))))).

(*And the spec*)
Lemma fold_right_opt_add_map 
  comp_cases t ty rl tl cslist bse pats:
  fold_left_opt (add comp_cases t ty rl tl) cslist bse = Some pats ->
  (* map Some l = bse -> *)
  rev (map (add_map comp_cases t ty tl rl) cslist) ++ (map (fun x => (fst x, Some (snd x))) bse) =
  map (fun x => (fst x, Some (snd x))) pats.
Proof.
  intros Hadd.
  unfold add in Hadd.
  erewrite fold_left_opt_change_f in Hadd.
  apply (fold_left_opt_cons (fun (x: funsym * list vty * list pattern) =>
    let cs := fst (fst x) in
    let params := snd (fst x) in
    let ql := snd x in
    let pat_tys := map (ty_subst (s_params cs) params) (s_args cs) in 
    let new_var_names := gen_strs (Datatypes.length ql) (compile_fvs ((t, ty) :: tl) rl) in
    let typed_vars := (combine new_var_names pat_tys) in
    let vl := rev typed_vars in 
    let pl := rev_map Pvar vl in 
    let al := rev_map Tvar vl in
    comp_cases cs (combine al (rev (map snd vl))))
    (fun (x: funsym * list vty * list pattern) =>
      let cs := fst (fst x) in
      let params := snd (fst x) in
      let ql := snd x in
      let pat_tys := map (ty_subst (s_params cs) params) (s_args cs) in 
      let new_var_names := gen_strs (Datatypes.length ql) (compile_fvs ((t, ty) :: tl) rl) in
      let typed_vars :=(combine new_var_names pat_tys) in
      let vl := rev typed_vars in 
      let pl := rev_map Pvar vl in 
      Pconstr cs params pl
      )
  ) in Hadd.
  2: { simpl. intros. destruct c as [[f vs] ps]; simpl; reflexivity. }
  erewrite (map_ext (fun x => (fst x, Some (snd x)))). rewrite <- Hadd.
  simpl. f_equal.
  2: simpl; intros [x1 y1]; auto.
  f_equal.
  apply map_ext. intros [[f vs] ps]; simpl; auto.
Qed.

(*TODO: maybe simplify dispatch1*)
Lemma compile_prove_some (P_hyps: list (term * vty) -> list (list pattern * A) -> Prop) 
  (P_goal: list (term * vty) -> list (list pattern * A) -> A -> Prop)
  (P_simp: forall t ty tms rl
    (Hsimpl: forall tm1, P_hyps ((t, ty) :: tms) (simplify t rl) -> compile ((t, ty) :: tms) rl = Some tm1 ->
      P_goal ((t, ty) :: tms) (simplify t rl) tm1)
    tm1
    (Hcomp: (compile ((t, ty) :: tms) rl) = Some tm1)
    (Hhyps: P_hyps ((t, ty) :: tms) rl),
    P_goal ((t, ty) :: tms) rl tm1)
  (Hemp: forall ps a l (Hhyps: P_hyps nil ((ps, a) :: l)), P_goal nil ((ps, a) :: l) a)
  (*Separate out cases*)
  (Hwildscase: forall t ty tl rl rhd rtl,
    let is_bare_css :=
    match ty with
    | vty_cons ts _ => if bare then (true, nil) else (false, get_constructors ts)
    | _ => (false, nil)
    end in
    let is_bare := fst is_bare_css in
    let css := snd is_bare_css in
    let is_constr fs := 
      f_is_constr fs && (is_bare || in_bool funsym_eq_dec fs css) in
    forall (Hsimpl: simplified rl) (Hrl: rl = rhd :: rtl) 
      types_cslist (Hpop: (populate_all is_constr rl) = Some types_cslist),
    let types := fst types_cslist in
    let cslist := snd types_cslist in
    forall casewild (Hcasewild : casewild = dispatch1 t types rl) (Hnotnull: forallb (fun x => negb (null (fst x))) rl),
    let cases := fst casewild in
    let wilds := snd casewild in
    forall (Hwilds: wilds = default rl) (IHwilds: forall tm1, P_hyps tl (default rl) -> 
      compile tl wilds = Some tm1 -> P_goal tl (default rl) tm1)
    (Hwildcases: amap_is_empty types \/ 
      if simpl_constr then 
      match (is_fun t) with
      | Left Hconstr =>
        let '(cs, params, al) := proj1_sig Hconstr in
          is_constr cs && amap_mem funsym_eq_dec cs types = false
      | _ => False
      end
      else False) tm1
    (Hmt1: compile tl wilds = Some tm1)
    (Hhyps: P_hyps ((t, ty) :: tl) rl),
    P_goal ((t, ty) :: tl) rl tm1)
  (Hfullcase: forall t ty tl rl rhd rtl,
    let is_bare_css :=
    match ty with
    | vty_cons ts _ => if bare then (true, nil) else (false, get_constructors ts)
    | _ => (false, nil)
    end in
    let is_bare := fst is_bare_css in
    let css := snd is_bare_css in
    let is_constr fs := 
      f_is_constr fs && (is_bare || in_bool funsym_eq_dec fs css) in
    forall (Hsimpl: simplified rl) (Hrl: rl = rhd :: rtl) 
      types_cslist (Hpop: (populate_all is_constr rl) = Some types_cslist),
    let types := fst types_cslist in
    let cslist := snd types_cslist in
    forall casewild (Hcasewild : casewild = dispatch1 t types rl) (Hnotnull: forallb (fun x => negb (null (fst x))) rl),
      let cases := fst casewild in
      let wilds := snd casewild in
      forall
      (IHwilds: forall tm1, P_hyps tl (default rl) -> 
        compile tl wilds = Some tm1 -> P_goal tl (default rl) tm1)
      (IHconstrs: forall cs al l (Hget: amap_get funsym_eq_dec cases cs = Some l) tm1,
        P_hyps (rev al ++ tl) l ->
        compile (rev al ++ tl) l = Some tm1 ->
        P_goal (rev al ++ tl) l tm1)
      (Hisemp: amap_is_empty types = false)
      (ps ps1 : list (pattern * A))
      (Hopt : rev
         (map
            (add_map
               (fun (cs0 : funsym) (al0 : list (term * vty)) =>
                comp_cases compile
                  cases tl cs0 al0) t ty tl rl) cslist) ++
       map (fun x : pattern * A => (fst x, Some (snd x))) ps1 =
       map (fun x : pattern * A => (fst x, Some (snd x))) ps)
      (*Much more useful than destructing and simplifying each time*)
      (Hps1' : ps1 = [] \/
              (exists t2 : A,
                 compile tl wilds = Some t2 /\
                 ps1 = [(Pwild, t2)]))
      (Hhyps: P_hyps ((t, ty) :: tl) rl),
      (*NOTE: here we simplify [comp_full] to avoid duplication every time (TODO)*)
      (* let comp_wilds (_: unit) := compile tl wilds in

      let comp_cases cs (al : list (term * vty)) :=
        comp_cases compile cases tl cs al in

      let comp_full := comp_full is_bare comp_wilds comp_cases types cslist css t ty tl rl in
      forall tm1 (Hcomp: comp_full tt = Some tm1), *)
    P_goal ((t, ty) :: tl) rl (mk_case t ty ps))
  (Hconstrcase: forall t ty tl rl rhd rtl cs params tms,
    let is_bare_css :=
    match ty with
    | vty_cons ts _ => if bare then (true, nil) else (false, get_constructors ts)
    | _ => (false, nil)
    end in
    let is_bare := fst is_bare_css in
    let css := snd is_bare_css in
    let is_constr fs := 
      f_is_constr fs && (is_bare || in_bool funsym_eq_dec fs css) in
    forall (Hsimpl: simplified rl) (Hrl: rl = rhd :: rtl) 
      types_cslist (Hpop: (populate_all is_constr rl) = Some types_cslist),
      (*NOTE: we don't have maps, not ideal*)
      let types := fst types_cslist in
      let cslist := snd types_cslist in
      forall casewild (Hcasewild : casewild = dispatch1 t types rl) (Hnotnull: forallb (fun x => negb (null (fst x))) rl),
        let cases := fst casewild in
        let wilds := snd casewild in
      forall (IHwilds: forall tm1, P_hyps tl (default rl) -> 
        compile tl wilds = Some tm1 -> P_goal tl (default rl) tm1)
      (IHconstrs: forall cs al l (Hget: amap_get funsym_eq_dec cases cs = Some l) tm1,
        P_hyps (rev al ++ tl) l ->
        compile (rev al ++ tl) l = Some tm1 ->
        P_goal (rev al ++ tl) l tm1)
      (Hisemp: amap_is_empty types = false)
      (Hsimplconstr: simpl_constr = true)
      (Ht: t = Tfun cs params tms)
      (Hisconstr: is_constr cs)
      (Hmem: amap_mem funsym_eq_dec cs types) tm1
      (Hcomp: comp_cases compile cases tl cs (combine tms
            (map (ty_subst (s_params cs) params) (s_args cs))) = Some tm1)
      (Hhyps: P_hyps ((t, ty) :: tl) rl), 
     P_goal ((t, ty) :: tl) rl tm1):

    forall ts p tm1, P_hyps ts p -> (compile ts p) = Some tm1 -> P_goal ts p tm1.
Proof.
  intros ts rl tm1 Hhyps. revert ts rl Hhyps tm1.
  apply (compile_ind' (fun tms rl o => P_hyps tms rl -> forall tm1, o = Some tm1 -> P_goal tms rl tm1)); auto; try discriminate.
  - intros ps a p Hhyps tm1 Hsome; inversion Hsome; subst; auto.
  - intros. eapply Hwildscase; eauto.
  - (*[comp_full] simplify*)
    intros t ty tl rl rhd rtl is_bare_css is_bare css is_constr Hsimpl Hrl types_cslist Hpop types
      cslist casewild Hcasewild Hnotnull cases wilds IHwilds IHconstrs Hisemp Hhyps tm1.
    simpl.
    unfold comp_full.
    rewrite <- option_map_bind.
    intros Hopt. apply option_map_some in Hopt.
    destruct Hopt as [ps [Hps Ht1]]; subst tm1.
    apply option_bind_some in Hps.
    destruct Hps as [ps1 [Hps1 Hopt]].
    (*This way we can deal with [fold_left_opt] before destructing 'forallb'*)
    apply fold_right_opt_add_map in Hopt.
    (*Much more useful than destructing and simplifying each time*)
    assert (Hps1': ps1 = nil \/ 
      exists t2, compile tl wilds = Some t2 /\
        ps1 = [(Pwild, t2)]).
    {
      apply option_bind_some in Hps1.
      destruct Hps1 as [z [Hsome Hifz]].
      destruct z; [inversion Hifz; auto|].
      apply option_map_some in Hifz. destruct Hifz as [t1 [Hwilds Hps1]]; subst. right.
      exists t1. auto.
    }
    eapply Hfullcase; eauto.
  - intros. eapply Hconstrcase; eauto.
Qed.

End Comp.

End Compile.

(*The version of [compile] for [gen_term]*)
Definition compile_term (b: bool) (simpl_constr: bool) 
  get_constructors bare tms P :=
  compile get_constructors (@gen_match b) (@gen_let b) 
    (@gen_getvars b) bare simpl_constr tms P.
Definition compile_bare (b: bool) (simpl_constr: bool) tms P :=
  compile (fun _ => nil) (@gen_match b) (@gen_let b) (@gen_getvars b) 
  true simpl_constr tms P.

(*single version*)
Definition compile_bare_single (b: bool) (simpl_constr: bool) (t: term) (ty: vty)
  (pats: list (pattern * (gen_term b))) :=
  compile_bare b simpl_constr [(t, ty)] (map (fun x => ([(fst x)], (snd x))) pats).