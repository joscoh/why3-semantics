(*Compilation of pattern matches*)
Require Import Syntax Denotational.
Set Bullet Behavior "Strict Subproofs".
From Equations Require Import Equations.

(*TODO: don't really need but matches interface*)
Definition amap_change {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (f: option B -> B) (x: A) (m: amap A B) : amap A B :=
  amap_replace eq_dec m x (fun _ b => f (Some b)) (f None).

Section Compile.
Context {A: Type} (get_constructors: typesym -> list funsym) 
  (mk_case: term -> list (pattern * A) -> A) (mk_let: vsymbol -> term -> A -> A).

(*We separate out some helper functions*)
Definition add_case (fs: funsym) (pl: list pattern) (a: A) (cases : amap funsym (list (list pattern * A))) :=
    amap_change funsym_eq_dec (fun o =>
      match o with
      | None => [(pl, a)]
      | Some rl => (pl, a) :: rl
      end
    ) fs cases.

(*NOTE: we use length (s_args c) instead of the list, so we don't need to reference types later*)
Definition union_cases (pl: list pattern) (a: A) (types: amap funsym (list pattern)) 
    (cases: amap funsym (list (list pattern * A))) : amap funsym (list (list pattern * A)) :=
    let add pl _ := Pwild :: pl in
    let wild (c: funsym) _  := [(fold_left add (s_args c) pl, a)] in
    let join _ wl rl := Some (wl ++ rl) in
    amap_union funsym_eq_dec join (amap_map_key wild types) cases . 
(* Definition union_cases (pl: list pattern) (a: A) (types: amap funsym (list pattern)) 
    (cases: amap funsym (list (list pattern * A))) : amap funsym (list (list pattern * A)) :=
    let add pl _ := Pwild :: pl in
    let wild ql := [(fold_left add ql pl, a)] in
    let join _ wl rl := Some (wl ++ rl) in
    amap_union funsym_eq_dec join (amap_map wild types) cases . *)

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
End Dispatch.

(*Now define full compilation*)
Require Import GenElts.
Check gen_vars.

Definition rev_map {B C: Type} (f: B -> C) (l: list B) : list C :=
  rev (map f l).


Fixpoint fold_left_opt {B C: Type} (f: B -> C -> option B) (l: list C) (base: B) : option B :=
  match l with
  | nil => Some base
  | x :: xs =>
    match (f base x) with
    | None => None
    | Some y => fold_left_opt f xs y
    end
  end.
  
(*Measure: total term size*)
(* We can be very permissive here*)
Fixpoint term_size (t: term) : nat :=
  match t with
  | Tfun _ _ ts => 1 + sum (map term_size ts)
  | _ => 1
  end.

Definition term_list_size (l: list term) : nat :=
  sum (map term_size l).

(*None = NonExhaustive*)

(* Definition compile_size (l: list (list pattern * A)) : nat :=
  sum (map pat_list_size (map fst l)). *)

(*TODO: move*)
Search "bind".
Definition option_bind {A B: Type} (o: option A) (f: A -> option B) : option B :=
  match o with
  | Some x => f x
  | None => None
  end.

Section Populate.
Variable (is_constr : funsym -> bool).
(*NOTE: populate will give option - want to ensure everything in pattern is constructor*)
Fixpoint populate  (acc : option (amap funsym (list pattern) * list (funsym * list vty * list pattern))) 
        (p: pattern) : option (amap funsym (list pattern) * list (funsym * list vty * list pattern)) :=
        match p with
        | Pwild => acc
        | Pvar _ => acc
        | Pconstr fs params ps =>
          option_bind acc
          (fun acc => 
            let (css, csl) := acc in
            if is_constr fs then
              if amap_mem funsym_eq_dec fs css then Some acc else
              Some (amap_set funsym_eq_dec css fs ps, (fs, params, ps) :: csl)
            else None (*exception - impossible by typing*))
        | Por p1 p2 => populate (populate acc p1) p2
        | Pbind p _ => populate acc p
        end.
End Populate.

(*Before we can define the full function, we need proofs for termination.
  These proofs will be very useful for correctness later on.
  First, the key property characterizing the results of dispatch in a clear, functional way*)
Check dispatch1.
Check amap_mem.

Definition is_pat_constr (cs: funsym) (p: pattern) : option (list vty * list pattern) :=
  match p with
  | Pconstr f tys ps => if funsym_eqb cs f then Some (tys, ps) else None
  | _ => None
end.
Check repeat.
(*assume that we have already simplified the pattern match, so it only has constructors and wilds*)
(*NOTE: need to know that all instances of Pconstr f ps for same f has ps with same length (implied by typing)*)
Check dispatch2.
(*TODO: define map_filter operation: filter, then map*)
Definition filter_map {A B: Type} (f: A -> option B) (l: list A): list B :=
  fold_right (fun x acc => match (f x) with | None => acc | Some y => y :: acc end) nil l.
Check amap_get.

Definition populate_all (is_constr: funsym -> bool) (rl: list (list pattern * A)) :=
  fold_left (populate is_constr) (map (fun x => List.hd Pwild (fst x)) rl) (Some (amap_empty, nil)).
Check populate_all.

Definition pat_at_head (p: pattern) (r: list pattern * A) : bool :=
  match (fst r) with | p1 :: _ => pattern_eqb p p1 | _ => false end.
Definition constr_at_head (c: funsym) (r: list pattern * A) : bool :=
  match (fst r) with | Pconstr f _ _ :: _ => funsym_eqb f c | _ => false end.

(*list has every (cs, tys, ps) tuple that is the first ocurrence of cs*)
(*An easier, but much less efficient definition*)
Definition find_last {A: Type} (p: A -> bool) (l: list A) : option A :=
  fold_right (fun x acc => match acc with | Some y => Some y | None => if p x then Some x else None end) None l.

Lemma find_app1 {B: Type} (p: B -> bool) (l1 l2: list B) x:
  find p l1 = Some x ->
  find p (l1 ++ l2) = Some x.
Proof.
  induction l1 as [|h t IH]; simpl; try discriminate.
  destruct (p h); auto.
Qed.

Lemma find_app2 {B: Type} (p: B -> bool) (l1 l2: list B):
  find p l1 = None ->
  find p (l1 ++ l2) = find p l2.
Proof.
  induction l1 as [|h t IH]; simpl; auto.
  destruct (p h); auto. discriminate.
Qed.

Lemma find_app3 {B: Type} (p: B -> bool) (l1 l2: list B):
  find p l2 = None ->
  find p (l1 ++ l2) = find p l1.
Proof.
  induction l1 as [|h t IH]; simpl; auto.
  destruct (p h); auto.
Qed.

Lemma find_rev {B: Type} (p: B -> bool) (l: list B):
  find p (rev l) = find_last p l.
Proof.
  induction l; simpl; auto.
  destruct (find_last p l).
  - apply find_app1. auto.
  - rewrite find_app2; auto.
Qed. 

(*Prove map, prove list has same things as map, don't care about order here I think? - maybe just
  prove bindings*)
(*NOTE: we can assume that rl is simplified (TODO change in compile)*)
(*Incorrect: store funsym + list pattern in that pattern*)

(*TODO: maybe prove after, almost proved, first focus on termination, which must be unconditional*)
(*
Lemma populate_all_types_constr (is_constr: funsym -> bool) rl cs (Hconstr: is_constr cs)
  (Hrl: Forall (fun x => negb (null (fst x))) rl):
  amap_get funsym_eq_dec (fst (populate_all is_constr rl)) cs =
  option_map fst (find (constr_at_head cs) rl).
Proof.
  unfold populate_all.
  rewrite <- fold_left_rev_right, <- map_rev.
  rewrite <- (rev_involutive rl) at 2. (*TODO: maybe don't need [find_rev]*)
  apply Forall_rev in Hrl.
  induction (rev rl) as [| [ps a] t IH]; simpl.
  - rewrite amap_empty_get. reflexivity.
  - inversion Hrl as [|? ? Hnull Hrl']; subst; simpl in *. 
    destruct ps as [|phd ptl]; try discriminate.
    simpl. destruct phd as [v|f tys pats| | | ]; simpl; try solve[rewrite IH; auto; rewrite find_app3; auto].
    + (*Pconstr*)
      destruct (fold_right
          (fun (y : pattern) (x : amap funsym (list pattern) * list (funsym * list vty * list pattern))
           => populate is_constr x y) (amap_empty, [])
          (map (fun x : list pattern * A => hd Pwild (fst x)) t)) as [css csl].
      simpl in IH. specialize (IH Hrl').
      destruct (funsym_eqb_spec f cs).
      * subst. rewrite Hconstr.
        rewrite amap_mem_spec, IH.
        destruct (find (constr_at_head cs) (rev t)) as [x|] eqn : Hfind; simpl.
        -- rewrite find_app1 with (x:=x); auto.
        -- rewrite find_app2; auto. simpl.
           unfold constr_at_head. simpl. destruct (funsym_eqb_spec cs cs); auto; try contradiction.
           simpl. rewrite amap_set_get_same. Search amap_get amap_set.
        *)
  
(*TODO: defined elsewhere, see*)
Definition constr_at_head_ex cs rl :=
  existsb (constr_at_head cs) rl.
(*Structural Lemmas*)
(*Here we relate the output of [dispatch2] to the matrices S and D from the paper, giving a nice
  functional specification. This is useful both in correctness and termination proofs*)

(*Basically, we need to know something about types and rl - some things we could say:
  1. constr_at_head_ex cs rl = amap_mem funsym_eq_dec cs types
  2. forall cs in types, constr_at_head_ex cs rl (cannot prove inductively)
  3. forall constr_at_head_ex cs rl, cs in types (can prove inductively - but isn't true depending on is_constr)
  I think we actually need the first one
  unless we inline definition of types
  
  Why is this so difficult? It really shouldn't be



Lemma dispatch2_gen_fst_nil (types: amap funsym (list pattern)) rl cs:
  amap_mem funsym_eq_dec cs types ->
  constr_at_head_ex cs rl = false ->
  amap_get funsym_eq_dec (fst (dispatch2_gen types rl)) cs = None.
Proof.
  intros Htyps.
   induction rl as [| [ps a] rtl IH]; simpl.
  - intros _. apply amap_empty_get.
  - intros Hfalse. apply orb_false_elim in Hfalse. destruct Hfalse as [Hhd Hfalse].
    destruct (dispatch2_gen types rtl ) as [cases wilds]; simpl in *.
    unfold constr_at_head in Hhd; simpl in Hhd.
    destruct ps as [|phd ptl]; auto.
    destruct phd; auto.
    + unfold add_case, amap_change. simpl.
      destruct (funsym_eqb_spec f cs); try discriminate.
      rewrite amap_replace_get_diff; auto.
    + unfold union_cases; simpl. 
      destruct (amap_get funsym_eq_dec (amap_map_key
        (fun (c : funsym) (_ : list pattern) =>
         [(fold_left (fun (pl : list pattern) (_ : vty) => Pwild :: pl) (s_args c) ptl, a)]) types) cs) as [y|] eqn : Hget2.
      * erewrite amap_union_inl.  Search amap_get amap_union.

      Search amap_get amap_replace. 

 Search (?x || ?y = false).

 Search amap_empty.*)

(*START HERE*)

(*Basic problem: I cannot get strong enough IH
  We need (for base case) to assume that cs in rl - but we need (in IH) to know something about
  case like: cs :: Pwild - Pwild still induces something (bc of types) but IH gives no info

  really need to know that everything in types is in rl - but this does NOT hold inductively
  problem is really that this is NOT defined via structural recursion on rl
  so somehow we need to say something useful:

  in inductive case, want to say we have foo :: filter ...., but constructor may not appear
  what if we have
  1. If cs appears in types but NOT as constr, get this result (though constr case is trivial)
  2. Then case as whether as constr

Let's try*)
(*NOTE: assume simplified*)


Definition wild_at_head_ex rl := existsb (pat_at_head Pwild) rl.

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

Lemma filter_map_nil rl cs:
  (constr_at_head_ex cs rl || wild_at_head_ex rl) = false ->
  filter_map (fun x : list pattern * A =>
         match fst x with (*these functions can be arbitrary but whatever*)
         | Pconstr fs _ pats :: ps => if funsym_eqb fs cs then Some (rev pats ++ ps, snd x) else None
         | Pwild :: ps => Some (repeat Pwild (Datatypes.length (s_args cs)) ++ ps, snd x)
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
Lemma dispatch2_gen_fst_in (types: amap funsym (list pattern)) rl cs:
  amap_mem funsym_eq_dec cs types ->
  (constr_at_head_ex cs rl || wild_at_head_ex rl) ->
  amap_get funsym_eq_dec (fst (dispatch2_gen types rl)) cs = Some
    (filter_map (fun x =>
      let ps := fst x in
      let a := snd x in
      match ps with
      | p :: ps =>
        match p with
        | Pwild => Some (repeat Pwild (length (s_args cs)) ++ ps, a)
        | Pconstr fs tys pats => (*trivial here*)
            if funsym_eqb fs cs then Some (rev pats ++ ps, a) else None
        | _ => None
        end
      | _ => None
      end
) rl).
Proof.
  intros Htypes. induction rl as [| [ps a] rtl IH]; simpl; try discriminate; intros Hhead;
  try contradiction.
  destruct (dispatch2_gen types rtl) as [cases wilds] eqn : Hd; simpl in *.
  unfold constr_at_head, pat_at_head in Hhead; simpl in Hhead.
  destruct ps as [| phd ptl]; simpl in *; auto.
  destruct phd; auto.
  - unfold add_case, amap_change; simpl.
    destruct (funsym_eqb_spec f cs); subst.
    + simpl in Hhead. 
      (*Need to see what recursive case is: preveious lemma gives more info*)
      destruct (constr_at_head_ex cs rtl || wild_at_head_ex rtl) eqn : Hhd2.
      * simpl in IH. erewrite amap_replace_get_same1.
        2: apply IH; auto. reflexivity.
      * rewrite amap_replace_get_same2. 
        -- rewrite filter_map_nil. reflexivity. auto.
        -- pose proof (dispatch2_gen_fst_notin types rtl cs Htypes) as Hnone.
           rewrite Hd in Hnone; apply Hnone. auto.
    + simpl in Hhead. rewrite amap_replace_get_diff; auto.
  - unfold union_cases; simpl.
    (*Need to prove list*)
    assert (Hrepeat: fold_left (fun (pl : list pattern) (_ : vty) => Pwild :: pl) (s_args cs) ptl =
      repeat Pwild (Datatypes.length (s_args cs)) ++ ptl).
    {
      clear.
      revert ptl. induction (s_args cs); intros; auto.
      simpl fold_left. rewrite IHl.
      assert (Hassoc: forall {A: Type} (l1: list A) l2 l3, l1 ++ l2 :: l3 = (l1 ++ [l2]) ++ l3).
      { intros. rewrite <- app_assoc. reflexivity. }
      rewrite Hassoc.  f_equal.
      assert (Hwild: [Pwild] = repeat Pwild 1) by reflexivity.
      rewrite Hwild, <- repeat_app, Nat.add_comm. reflexivity.
    }
    assert (Htypes':=Htypes).
    rewrite amap_mem_spec in Htypes'.
    destruct (amap_get funsym_eq_dec types cs) eqn : Hget1; try discriminate.
    destruct (constr_at_head_ex cs rtl || wild_at_head_ex rtl) eqn : Hhead2.
    + erewrite amap_union_inboth. 3: { apply IH. auto. }
      2: { apply amap_map_key_get_some. apply Hget1. } simpl. f_equal.
      f_equal. f_equal. auto. 
    + (*here, recursive get is false and list is nil*)
      rewrite filter_map_nil; auto.
      erewrite amap_union_inl. reflexivity. erewrite amap_map_key_get_some.
      f_equal. f_equal. f_equal. apply Hrepeat.
      apply Hget1. pose proof (dispatch2_gen_fst_notin types rtl cs Htypes) as Hnone.
      rewrite Hd in Hnone; apply Hnone. auto.
Qed.

(*Second main structural lemma: the matrix D*)

Lemma dispatch2_gen_snd (types: amap funsym (list pattern)) rl:
  snd (dispatch2_gen types rl) = filter_map (fun x =>
    match (fst x) with
    | Pwild :: ps => Some (ps, snd x)
    | _ => None
    end ) rl.
Proof.
  induction rl as [| [pl a] rtl IH]; simpl; auto.
  unfold dispatch2_aux; simpl.
  destruct (dispatch2_gen types rtl ) as [cases wilds]; simpl in *.
  destruct pl as [| p ps]; auto.
  destruct p; auto; simpl.
  f_equal; auto.
Qed.

(*Termination Metric*)

(*The termination metric is complicated. The compile function is not structurally recursive.
  The natural choice for the termination metric is the sum of the sizes of the patterns in the input list,
  since for a constructor c(ps) :: pl, it becomes ps :: pl, decreasing the size.
  However, this does not work: the size gets bigger when we simplify to remove "or" patterns.
  An alternative is then to make the metric the sum of the products of 2^(size p) for each p in each list.
  This ensures that Por p q :: pl is bigger than p :: pl + q :: pl
  But this also doesn't work: when we add the extra (length (s_args c)) Pwilds in the matrix S, we end up
  with a bigger matrix.
  A solution is a compbined metric: we add the size of a Pwild, but multiply the others.
  Then we make the Pconstr part big enough to compensate for the (bounded) sum of Pwilds that we add.
  TODO: make sure this works*)

(*A more complicated pattern size metric*)


Definition pat_size_op (f: pattern -> nat) (p1 p2: pattern) : nat :=
  match p1 with
  | Pwild => f p1 + f p2
  | _ => (*TODO: is mult enough or do we need 2^(size p)?*)
      (*2 ^*) (f p1) * (*2 ^*) (f p2)
  end.

Definition pat_iter_op (f: pattern -> nat) :=
  fix pat_iter_op (l: list pattern) : nat :=
    match l with
    | nil => 2
    (*| [Pwild] => 2*) (*does NOT work - then does not decrease*)
    | Pwild :: tl => 1 + pat_iter_op tl
    | p :: tl => (*2 ^*) (f p) * (pat_iter_op tl)
    end.

Fixpoint pat_size_mixed (n: nat) (p: pattern) : nat :=
  match p with
  | Pwild => 1
  | Pvar _ => 2
  | Pbind p x => 1 + pat_size_mixed n p
  | Por p1 p2 => 1 + pat_size_mixed n p1 + pat_size_mixed n p2 (*TODO?*)
  | Pconstr c _ ps => 1 + n + pat_iter_op (pat_size_mixed n) ps
  end.

Definition pat_list_size_mixed (n: nat) (l: list pattern) : nat :=
  pat_iter_op (pat_size_mixed n) l.

(*And the metrix*)
Definition compile_size (n: nat) (l: list (list pattern * A)) : nat :=
  sum (map (fun x => pat_list_size_mixed n (fst x)) l).

(*TODO: move*)
Lemma sum_app l1 l2:
  sum (l1 ++ l2) = sum l1 + sum l2.
Proof.
  induction l1; simpl; auto. lia.
Qed.

Lemma compile_size_app n l1 l2:
  compile_size n (l1 ++ l2) = compile_size n l1 + compile_size n l2.
Proof.
  unfold compile_size. rewrite map_app.
  apply sum_app.
Qed.

Lemma compile_size_cons n a l:
  compile_size n (a :: l) = pat_list_size_mixed n (fst a) + compile_size n l.
Proof. reflexivity. Qed.
  

(*Termination Proofs*)
(*compile_size (compile_size_bound (snd (dispatch1 t types rl))) (snd (dispatch1 t types rl)) <
compile_size (compile_size_bound (phd :: ptl)) (phd :: ptl)*)
(*Think we will need: take n larger than compile_size_bound (so that n does not change recursively,
  for IH, easy*)

Lemma add_lt_pow n m:
  1 <= m ->
  1 <= n ->
  S n <= 2 ^ m * n.
Proof.
  intros Hm Hn.
  induction m; try lia.
  destruct m.
  - simpl. lia.
  - rewrite Nat.pow_succ_r'. nia.
Qed.

Lemma pat_size_mixed_geq_1 n p:
  1 <= pat_size_mixed n p.
Proof.
  induction p; simpl; lia.
Qed.

Lemma mul_geq_1 n m:
  1 <= m ->
  1 <= n ->
  1 <= (m * n).
Proof.
nia.
Qed.

Lemma pow_geq_1 n m:
  1 <= n ->
  1 <= n ^ m.
Proof.
  induction m; simpl; intros; lia.
Qed.

Lemma pat_list_size_mixed_geq n ps:
  2 <= pat_list_size_mixed n ps.
Proof.
  induction ps; simpl; try lia.
  destruct a; try solve[simpl; lia].
Qed.
(*   - simpl. apply mul_geq_1; auto.
    eapply Nat.le_trans. 2: apply Nat.le_add_r.
    apply pow_geq_1. lia.
  - apply mul_geq_1; auto. apply pow_geq_1. lia.
  - apply mul_geq_1; auto. apply pow_geq_1. lia.
Qed. *)
  
(*We do NOT have equality: this is crucial for adding pwilds, but we do need that it is
  sometimes a strict equality for the "or" case of simplifying*)
Lemma pat_list_size_mixed_cons n p pl:
  pat_list_size_mixed n (p :: pl) <= 1 + pat_size_mixed n p * pat_list_size_mixed n pl.
Proof.
  simpl. destruct p; auto. simpl. lia.
Qed.

Lemma pat_list_size_mixed_app n p1 p2:
  pat_list_size_mixed n (p1 ++ p2) <= pat_list_size_mixed n p1 * pat_list_size_mixed n p2.
Proof.
  induction p1; simpl; auto; try lia.
  destruct a; simpl; auto; try nia.
  pose proof (pat_list_size_mixed_geq n p2). lia.
Qed.

(*NOTE; this is NOT commutative, so we probably can't say too much
  TODO see what we need*)
(*Lemma pat_list_size_mixed_rev n l:
  pat_list_size_mixed n (rev l) <= 2 * pat_list_size_mixed n l.
Proof.
  induction l; auto; simpl. lia.
  eapply Nat.le_trans.
  apply pat_list_size_mixed_app. simpl.
 destruct a; simpl; try nia.
  simpl rev.
  destruct 

 rewrite pat_list_size_mixed_app.

 simpl; auto.
  destruct a; simpl.*)

Lemma lt_le_0_1 n:
  0 < n <-> 1 <= n.
Proof. lia. Qed.

Lemma compile_size_nil n: compile_size n nil = 0.
Proof.
reflexivity.
Qed.


Lemma compile_size_simplify_single n t rhd:
  compile_size n (simplify_single t rhd) <= pat_list_size_mixed n (fst rhd).
Proof.
  destruct rhd as [ps a]; simpl. destruct ps as [| p ptl]; auto.
  revert a. pose proof (pat_list_size_mixed_geq n ptl). 
  induction p; simpl; intros a; try rewrite !compile_size_cons; try rewrite !compile_size_nil; simpl; try lia.
  - rewrite map_app, compile_size_app.
    assert (pat_list_size_mixed n (p1 :: ptl) + pat_list_size_mixed n (p2 :: ptl) <= 
      pat_list_size_mixed n ptl + (pat_size_mixed n p1 + pat_size_mixed n p2) * pat_list_size_mixed n ptl).
    { clear -H. simpl. destruct p1; destruct p2; try (simpl; lia). }
    specialize (IHp1 a). specialize (IHp2 a). lia.
  - eapply Nat.le_trans. apply IHp. simpl.
    destruct p; simpl; lia.
Qed. 

(*A key idea as to why we chose this size: simplifying does not increase the size (though it does
  increase the raw size)*)
Lemma compile_size_simplify n t rl:
  compile_size n (simplify t rl) <= compile_size n rl.
Proof.
  induction rl as [| rhd rtl IH]; simpl; auto.
  unfold simplify in *; simpl.
  rewrite compile_size_app, compile_size_cons.
  pose proof (compile_size_simplify_single n t rhd); lia.
Qed.


 
(*Lemma dispatch_snd_smaller n t types rhd rtl:
  compile_size n (snd (dispatch t types rhd rtl)) <= pat_list_size_mixed n (fst rhd) + compile_size n (snd rtl).
Proof.
  unfold dispatch.
  rewrite dispatch_equiv.
  apply dispatch_elim; intros; auto; try solve[simpl; lia].
  - simpl. rewrite compile_size_cons. simpl. lia. 
    (* pose proof (pat_list_size_mixed_geq n pl). lia. *)
  - simpl. rewrite compile_size_cons. simpl. lia. 
(*rewrite <- (Nat.add_0_l (compile_size n wilds)) at 1. apply Nat.add_lt_mono_r.
    apply lt_le_0_1. apply mul_geq_1.
    + eapply Nat.le_trans. 2: apply Nat.le_add_r. apply pow_geq_1. lia.
    + apply pat_list_size_mixed_geq.*)
  - eapply Nat.le_trans. apply H0.
    eapply Nat.le_trans. apply Nat.add_le_mono_l. apply H. clear H H0.
    rewrite Nat.add_assoc. apply Nat.add_le_mono; auto.
    simpl. destruct p; destruct q; simpl; try lia.
    + (*So clearly not truue*)*)

(*Imagine size:
  size (Por p1 p2) :: ps = (1 + size p1 + size p2) * (size ps)
  size Pwild :: ps = 1 + size ps
  size (Pvar v) :: ps = 2 * (size ps)
  size (Pconstr f p1) :: ps = (1 + (prod size p1)) *(size ps)
  size (Pbind p _) :: ps =(1 + size p) * (size ps)

want to show size (simplify ps) <= size ps
  

    (*Idea: 

    simpl. destruct p; simpl.

 
 simpl.

    destruct p; simpl; try lia.
    (*NOTE problem: with var, need to make size 2*)
    

 simpl  in *. eapply Nat.lt_le_trans 


 eapply Nat.lt_le_trans. apply H0.
    eapply Nat.le_trans. apply Nat.add_le_mono_l. apply Nat.lt_le_incl, H. 
    simpl snd. rewrite !Nat.add_assoc. apply Nat.add_le_mono_r. simpl fst.
    eapply Nat.le_trans. apply Nat.add_le_mono. apply pat_list_size_mixed_cons. apply pat_list_size_mixed_cons.
    rewrite Nat.add_0_r, !Nat.pow_add_r, Nat.mul_add_distr_r.
    apply Nat.add_le_mono.
    + apply Nat.mul_le_mono_r. rewrite <- (Nat.mul_1_r (2 ^ (pat_size_mixed n p))) at 1.
      apply Nat.mul_le_mono; auto. apply pow_geq_1; lia.
    + apply Nat.mul_le_mono_r. rewrite <- (Nat.mul_1_l (2 ^ (pat_size_mixed n q))) at 1.
      apply Nat.mul_le_mono; auto. apply pow_geq_1; lia.
  - eapply Nat.le_trans. apply H. apply Nat.add_le_mono_r.
    simpl fst. eapply Nat.le_trans. apply pat_list_size_mixed_cons.
    simpl. nia.
Qed.*)*)

Lemma dispatch2_gen_snd_smaller n types rl:
  compile_size n (snd (dispatch2_gen types rl)) <= compile_size n rl.
Proof.
  rewrite dispatch2_gen_snd.
  induction rl as [|[pl a] ptl IH]; simpl; auto.
  destruct pl as [| p tl].
  - rewrite compile_size_cons. simpl. lia.
  - destruct p; rewrite !compile_size_cons; simpl;lia.
Qed.
  

Lemma d_matrix_smaller n t types rl:
  compile_size n (snd (dispatch1 t types rl)) <= compile_size n rl.
Proof.
  rewrite dispatch_equiv.
  unfold dispatch2.
  eapply Nat.le_trans. apply dispatch2_gen_snd_smaller. apply compile_size_simplify.
Qed.

(*2nd obligation: all the S matrices are smaller*)

(*TODO: move*)
Lemma constr_at_head_ex_app cs l1 l2:
  constr_at_head_ex cs (l1 ++ l2) = constr_at_head_ex cs l1 || constr_at_head_ex cs l2.
Proof.
  induction l1; simpl; auto. rewrite IHl1, orb_assoc. reflexivity.
Qed.

(*This is NOT true - could be inside "or" pattern, but IF simplify_single holds, then 
  holds for p*)
Lemma constr_at_head_simplify_single cs t p:
  constr_at_head cs p -> constr_at_head_ex cs (simplify_single t p).
Proof.
  unfold simplify_single. destruct p as [ps a]; simpl. destruct ps; auto.
  unfold constr_at_head; simpl. destruct p; simpl; auto.
  unfold constr_at_head. simpl. rewrite orb_false_r. auto.
Qed.
 
Lemma constr_at_head_ex_simplify t cs rl:
  constr_at_head_ex cs rl -> constr_at_head_ex cs (simplify t rl).
Proof.
  induction rl; simpl; auto.
  unfold simplify in *. simpl.
  rewrite constr_at_head_ex_app.
  intros Hconstr. apply orb_true_iff.
  apply orb_true_iff in Hconstr. destruct Hconstr as [Hconstr | Hconstr].
  - left. apply constr_at_head_simplify_single; auto.
  - right. apply IHrl. auto.
Qed. 


(* (*Size of simplify*)
Lemma compile_size_simplify_single n t rh:
  compile_size n (simplify_single t rh) <= pat_list_size_mixed n (fst rh).
Proof.
  destruct rh as [ps a]. simpl. destruct ps as [| p1 ptl]; auto.
  - simpl. rewrite compile_size_nil. lia.
  - pose proof (pat_list_size_mixed_geq n ptl). revert a. induction p1; simpl; intros;
    try rewrite !compile_size_cons, !compile_size_nil; simpl; try lia.
    + rewrite map_app, compile_size_app.
      rewrite Nat.add_0_r, Nat.mul_add_distr_r, !Nat.pow_add_r.
      apply Nat.add_le_mono.
      * eapply Nat.le_trans. apply IHp1_1. 
        eapply Nat.le_trans. apply pat_list_size_mixed_cons.
        apply Nat.mul_le_mono_r.
        rewrite <- (Nat.mul_1_r (2 ^ pat_size_mixed n p1_1)) at 1. 
        apply Nat.mul_le_mono; auto. 
        apply pow_geq_1; lia.
      * eapply Nat.le_trans. apply IHp1_2. 
        eapply Nat.le_trans. apply pat_list_size_mixed_cons.
        apply Nat.mul_le_mono_r.
        rewrite <- Nat.mul_1_l at 1. apply Nat.mul_le_mono; auto. apply pow_geq_1; lia.
    + eapply Nat.le_trans. apply IHp1. 
      eapply Nat.le_trans. apply pat_list_size_mixed_cons.
      rewrite Nat.add_0_r, Nat.mul_add_distr_r.
      lia.
Qed. *)


(* Lemma compile_size_simplify n t rl:
  compile_size n (simplify t rl) <= compile_size n rl.
Proof.
  unfold simplify. 
  induction rl as [| rh rt IH]; simpl; auto.
  rewrite compile_size_app, compile_size_cons.
  pose proof (compile_size_simplify_single n t rh); lia.
Qed. *)

(*The S matrix is quite complicated. The issue is that, while we have at least one constructor
  go from Pconstr c ps -> ps, we add lots of Pwilds - potentially length (s_args c) for every non-constructor
  row of the matrix - i.e. length rl * (length (s_args c)). This is OK: we can just set n to be large enough.
  But the problem is that the length of rl actually increases during the algorithm. We need some value large
  enough that length (rl) <= m for every step of the algorithm.
  We overapproximate this by fully expanding the pattern list (i.e. all or patterns). Then we can set n
  to be this value and show that our size measure actually decreases in this case*)

(*This function finds a multicplicative version of the pattern size. It is equal to (though we do not prove)
  the size of the resulting list if we repeatedly simplify and expand all "or" patterns*)
Definition iter_mult (l: list nat) : nat := fold_right Nat.mul 1 l.

Lemma pat_list_size_app l1 l2:
  pat_list_size (l1 ++ l2) = pat_list_size l1 + pat_list_size l2.
Proof.
  induction l1; simpl; auto. rewrite !pat_list_size_cons. lia.
Qed.

(*Not just straight multiplication: when we see Por p1 p2, need to multiply each size by resulting size*)

(* Equations expand_size_pat_list (l: list pattern) : nat by wf (pat_list_size l) :=
  expand_size_pat_list nil := 1;
  expand_size_pat_list ((Por p1 p2) :: tl) := (expand_size_pat_list (p1 :: tl)) + (expand_size_pat_list (p2 :: tl)) (*mult or plus here?*);
  expand_size_pat_list ((Pconstr c _ ps) :: tl) := expand_size_pat_list (ps ++ tl);
  expand_size_pat_list (p :: tl) := expand_size_pat_list tl.
Next Obligation.
rewrite pat_list_size_app, pat_list_size_cons; simpl.
unfold pat_list_size at 1. lia.
Defined.
Next Obligation.
rewrite !pat_list_size_cons; simpl. lia.
Defined.
Next Obligation.
rewrite !pat_list_size_cons; simpl; lia.
Defined.
Next Obligation.
rewrite !pat_list_size_cons; simpl. lia.
Defined. *)


Fixpoint expand_size_pat (p: pattern) : nat :=
  match p with
  | Por p1 p2 => (expand_size_pat p1) + (expand_size_pat p2)
  | Pbind p x => expand_size_pat p
  | Pconstr f _ ps => iter_mult (map expand_size_pat ps)
  | _ => 1
  end.
Definition expand_size_pat_list (l: list pattern) : nat :=
  iter_mult (map expand_size_pat l).
(*For list of list - do we add or multiply? - should be OK multiplying I think*)
Definition expand_size (l: list (list pattern * A)) : nat :=
  sum (map (fun x => expand_size_pat_list (fst x)) l).
(*   iter_mult (map (fun x => expand_size_pat_list (fst x)) l). *)

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

(*Theorems about [expand_size]*)

(*1. expand_size (simplify rl) <= expand_size rl*)
Lemma expand_size_simplify_single t rhd:
  expand_size (simplify_single t rhd) <= expand_size_pat_list (fst rhd).
Proof.
  destruct rhd as [ps a]; simpl.
  destruct ps as [|phd ptl]; auto.
  rewrite expand_size_pat_list_cons.  
  revert a.
  induction phd; intros a; simpl; try rewrite !expand_size_cons; try rewrite !expand_size_nil;
  simpl; try rewrite !expand_size_pat_list_cons; simpl;  try lia.
  + rewrite map_app, expand_size_app. specialize (IHphd1 a). specialize (IHphd2 a). nia.
  + apply IHphd.
Qed.

Lemma expand_size_simplify t rl:
  expand_size (simplify t rl) <= expand_size rl.
Proof.
  induction rl as [| rhd rtl IH]; auto; simpl.
  unfold simplify; simpl.
  rewrite expand_size_app, expand_size_cons.
  unfold simplify in IH.
  pose proof (expand_size_simplify_single t rhd); lia.
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
  apply expand_size_simplify.
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
  rewrite dispatch2_gen_fst_in; auto.
  clear Htypes Hin.
  revert l.
  induction rl as [| [ps a] ptl IH]; simpl; intros l; auto; [intros Hsome; inversion Hsome; subst; auto|].
  destruct ps as [|p ps]; auto.
  - rewrite expand_size_cons; simpl. intros Hsome. apply IH in Hsome. lia.
  - destruct p; rewrite !expand_size_cons; simpl; try solve[intros Hsome; apply IH in Hsome; lia].
    + destruct (funsym_eqb_spec f cs); subst; [| intros Hsome; apply IH in Hsome; lia].
      intros Hsome. injection Hsome.
      intros Hl; subst; clear Hsome. rewrite expand_size_cons. simpl.
      rewrite expand_size_pat_list_cons. simpl.
      rewrite expand_size_pat_list_app, expand_size_pat_list_rev.
      specialize (IH _ eq_refl). unfold expand_size_pat_list at 1.
      apply Nat.add_le_mono; auto.
    + intros Hl; inversion Hl; subst; clear Hl.
      rewrite expand_size_cons. simpl.
      rewrite expand_size_pat_list_cons, expand_size_pat_list_app.
      replace (expand_size_pat_list (repeat Pwild (Datatypes.length (s_args cs)))) with 1.
      -- specialize (IH _ eq_refl). simpl. rewrite !Nat.add_0_r. apply Nat.add_le_mono; auto.
      -- (*Crucial: adding lots of wilds does not increase this measure*) 
        clear. induction (length (s_args cs)); simpl; auto. 
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
  - apply expand_size_simplify.
Qed.

(*4. Now we reason about why we used this particular metric: the length of the simplified list is
  smaller than [expand_size]*)

Lemma iter_mult_geq l:
  (forall x, In x l -> 1 <= x) ->
  1 <= iter_mult l.
Proof.
  intros Hin. induction l; simpl in *; auto.
  assert (1 <= a) by (apply Hin; auto).
  apply mul_geq_1; auto.
Qed.

Lemma expand_size_pat_geq p:
  1 <= expand_size_pat p.
Proof.
  induction p; simpl; auto; try lia.
  apply iter_mult_geq. rewrite Forall_forall in H.
  intros x. rewrite in_map_iff. intros [p [Hx Hinx]]; subst.
  apply H; auto.
Qed.

Lemma expand_size_pat_list_geq rl:
  1 <= expand_size_pat_list rl.
Proof.
  unfold expand_size_pat_list.
  apply iter_mult_geq.
  intros x. rewrite in_map_iff.
  intros [p [Hin Hinx]]; subst.
  apply expand_size_pat_geq.
Qed.

Lemma expand_size_length rl:
  length rl <= expand_size rl.
Proof.
  induction rl as [| phd ptl IH]; auto; simpl.
  rewrite expand_size_cons.
  pose proof (expand_size_pat_list_geq (fst phd)). lia.
Qed.

Lemma expand_size_simplify_length t rl:
  length (simplify t rl) <= expand_size rl.
Proof.
  eapply Nat.le_trans.
  - apply expand_size_length.
  - apply expand_size_simplify.
Qed.


(*This is the key step for termination:*)
(*Now we prove the [compile_size] bound for the matrix S. In each step, we decrease the size by n,
  because we remove at least 1 constructor. But we add (s_args c) Pwilds for each wild in the matrix -
  potentially (length rl) - 1 (we can upper bound by (length rl). But really this bound does not hold,
  since we first expand the matrix by wimplifying, so we can add potentially (s_args c) * (length (simplify rl))
  size. However, since (length (simplify rl)) increases, we cannot appropriately bound n. So we need a single
  larger, static bound which is larger than everything we use - hence [expand_size] above. Thus, we give
  the following, weak bound, and we set n (statically) to be large enough.
  This is almost a fuel-based argument, but it is not always decreasing - it is basically a potential argument*)


(*NOTE: need to move*)

(*We need to expand everything fully, since the above termination metric is not well-behaved under
  commutativity, and thus we cannot prove anything useful about app/reverse (although if we did not
  have the reverse, it may have actually worked*)

(*Given lists l1, l2, ..., ln, find all lists with x1,...xn such that x_i \in l_i*)
(*TODO: like [get_possible_index_lists]*)
(* Definition choose_all {A: Type} (l: list (list A)) : list (list A) :=
  fold_right (fun l1 acc =>
    concat (map (fun x => map (fun y => x :: y) acc) l1)) [nil] l. *)

(*Theorems about [choose_all]*)

Definition combinewith {A B C: Type} (f: A -> B -> C) (l1: list A) (l2: list B) : list C :=
  concat (map (fun x => map (fun y => f x y) l2 ) l1).

(* Lemma choose_all_equiv {B: Type} (l: list (list B)): choose_all l =
  fold_right (fun l1 acc => combinewith cons l1 acc) [nil] l.
Proof.
  reflexivity.
Qed. *)

Definition choose_all {B: Type} (l: list (list B)) :=
  fold_right (fun l1 acc => combinewith cons l1 acc) [nil] l.

(* Lemma combinewith_id_l {B C: Type} (f: B -> C -> C) (l1: list B) (l2: list C):
  (forall a b, In a l1 -> In b l2 -> f a b = b) ->
  combinewith f l1 l2 = l2.
Proof.
  intros Hall. unfold combinewith.
  
 *)
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
  (*Separate lemma?*) clear -Hcomp.
  (*TODO: how do f and g have to compose?*)
  induction l2; simpl; [reflexivity|].
  rewrite !combinewith_cons1.
  rewrite !map_app, !map_map.
  rewrite IHl2. f_equal.
  apply map_ext.
  auto.
Qed.


Lemma choose_all_app {B: Type} (l1 l2: list (list B)) :
  choose_all (l1 ++ l2) = combinewith (fun x y => x ++ y) (choose_all l1) (choose_all l2).
Proof.
  induction l1; simpl; auto.
  - unfold combinewith; simpl; rewrite app_nil_r, map_id; reflexivity.
  - rewrite IHl1. apply combinewith_comp.
    intros. reflexivity.
Qed.


(*Note: ignore variables here, only care about size*)
Fixpoint expand_pat (p: pattern) : list pattern :=
  match p with
  | Por p1 p2 => (expand_pat p1) ++ (expand_pat p2)
  | Pbind p x => (*map (fun y => Pbind y x)*) (expand_pat p) (*OK even though lose size info bc we dont ever recurse here*)
  | Pconstr c tys pats => map (fun y => Pconstr c tys y) (choose_all (map expand_pat pats))
  | _ => [Pwild]
  end.

Definition expand_pat_list (ls: list pattern) : list (list pattern) :=
  choose_all (map expand_pat ls).

Definition expand_full (ls: list (list pattern * A)) : list (list pattern) :=
  concat (map (fun x => expand_pat_list (fst x)) ls).

(*Lemmas*)
Lemma expand_pat_list_cons x t: expand_pat_list (x :: t) =
  concat (map (fun x => map (fun y => x :: y) (expand_pat_list t)) (expand_pat x)).
Proof.
  reflexivity.
Qed.

Lemma expand_full_cons x t: expand_full (x :: t) = 
  expand_pat_list (fst x) ++ expand_full t.
Proof. reflexivity. Qed.

Lemma expand_full_nil: expand_full nil = nil.
Proof. reflexivity. Qed.

Lemma expand_full_app l1 l2: expand_full (l1 ++ l2) = expand_full l1 ++ expand_full l2.
Proof.
  unfold expand_full. rewrite map_app, concat_app. reflexivity.
Qed. 

(*Our termination metric will be [pat_size n (expand_full ls)], where n > length (expand_full ls) * max (s_args c)
  (or (expand_size ls) * max (s_args c)*)

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
Lemma length_concat_mult {B: Type} n m (l: list (list B)):
  length l = n ->
  Forall (fun x => length x = m) l ->
  length (concat l) = n * m.
Proof.
  revert n m.
  induction l as [| h t]; simpl; auto.
  - intros; subst. auto.
  - intros n m Hn Hall. subst. rewrite app_length.
    rewrite (IHt (length t) m); auto; [| inversion Hall; auto].
    replace (length h) with m by (inversion Hall; auto). lia.
Qed.

Lemma choose_all_length {B: Type} (l: list (list B)):
  (* Forall (fun l => length l = m) l -> *)
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


(*TODO: move*)
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
(*TODO: delete previous*)
Definition compile_size' (rl: list (list pattern * A)) : nat :=
  pat_list_list_size (expand_full rl).

(*Lemmas*)

Lemma pat_list_list_size_app l1 l2:
  pat_list_list_size (l1 ++ l2) = pat_list_list_size l1 + pat_list_list_size l2.
Proof.
  unfold pat_list_list_size. rewrite map_app.
  apply sum_app.
Qed.

(*Not as nice a definition for cons*)

Lemma compile_size_cons' x l:
  compile_size' (x :: l) = 
  pat_list_list_size (expand_pat_list (fst x)) + compile_size' l.
Proof. unfold compile_size'. rewrite expand_full_cons, pat_list_list_size_app. reflexivity. Qed.

End PatSize.
  

(*Step 2: D matrix*)
(*TODO START HERE*)
(*compile_size' n (snd (dispatch2 t types (phd :: ptl))) < compile_size' n (phd :: ptl*)
(*Idea: have <= always (including null) - any empty row makes it <*)
(*Doesn't quite work: need nonempty row. If all rows are null (ie. fst phd = nil), then
  we could have problems - does this cause termination issues?*)
(*Lemma dispatch2_gen_snd_smaller' n types rl:
  negb (null rl) ->
  compile_size' n (snd (dispatch2_gen types rl)) < compile_size' n rl.
Proof.
  rewrite dispatch2_gen_snd. destruct rl as [|[ps a] rtl]; try discriminate.
  intros _. simpl. destruct ps.
Lemma filter_map_cons {A B: Type} (f: A -> option B) x (l: list A) :
  filter_map f (x :: l) = match (f x) with 

Definition filter_map {A B: Type} (f: A -> option B) (l: list A): list B :=
  fold_right (fun x acc => match (f x) with | None => acc | Some y => y :: acc end) nil l.

 Search filter_map. rewrite compile_size_cons'. 
  simpl. destruct ps; simpl.
  - 


 induction rtl as [|r2 rtl IH]; simpl in *.
  - destruct ps; auto. (*problem: every time we get to nil*) simpl.


 destruct 
  simpl. intros _.
  
 intros Hnull.
  induction rl as [|[pl a] ptl IH]; simpl; auto. discriminate.
  destruct pl as [| p tl].
  - rewrite compile_size_cons'. simpl. simpl in *.
    destruct ptl; auto. simpl in *. lia.
  - destruct p; rewrite !compile_size_cons'; simpl; try lia.
    rewrite expand_pat_list_cons.
    (*The interesting case where we remove wilds*) simpl. rewrite app_nil_r.
    unfold expand_pat_list at 1.
    rewrite Nat.add_comm. apply Nat.add_le_mono.  
    + lia.

Qed.*)
  
(*TODO START: we do NOT have the strict inequality here, but we may need to assume that rl is nonempty*)

Print dispatch1.

(*TODO MOVE: in why3, throw error if list is empty. We give an option version for this, then prove
  that it is equivalent to the existing version (which is simpler to reason about*)
Section Dispatch.
Variable (t: term) (types: amap funsym (list pattern)) .
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

Print dispatch1.
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
  dispatch_opt x acc = Some l <-> negb (null (fst x)) /\ l = dispatch t types x acc.
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
  forallb (fun x => negb (null (fst x))) rl /\ l = dispatch1 t types rl.
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
      (*TODO: generalize this*)
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

(*Now, we prove smaller lemmas (move above stuff later TODO*)

Lemma compile_size_nil' n:
  compile_size' n nil = 0.
Proof. reflexivity. Qed.

Lemma compile_size_cons_le n x l:
  compile_size' n l <= compile_size' n (x :: l).
Proof.
  rewrite compile_size_cons'. lia.
Qed.
Print pat_list_list_size.
Lemma pat_list_list_size_cons n x l:
  pat_list_list_size n (x :: l) = pat_list_size_n n x + pat_list_list_size n l.
Proof. reflexivity. Qed.

Print pat_list_size_n.
Lemma pat_list_size_n_cons n x l:
  pat_list_size_n n (x :: l) = pat_size_n n x + pat_list_size_n n l.
Proof. reflexivity. Qed.

Lemma pat_size_n_pos n p:
  0 < pat_size_n n p.
Proof.
  destruct p; simpl; lia.
Qed.

Lemma pat_list_size_n_pos n l:
  negb (null l) ->
  0 < pat_list_size_n n l.
Proof.
  induction l as [| h t IH]; simpl; try discriminate.
  intros _. rewrite pat_list_size_n_cons.
  pose proof (pat_size_n_pos n h); lia.
Qed.
  

Lemma pat_list_list_size_pos n l:
  negb (null l) ->
  forallb (fun x => negb (null x)) l ->
  0 < pat_list_list_size n l.
Proof.
  induction l; simpl; auto; try discriminate.
  intros _. intros Hnull.
  rewrite pat_list_list_size_cons.
  apply andb_true_iff in Hnull. destruct Hnull as [Hnull _].
  pose proof (pat_list_size_n_pos n a Hnull). lia.
Qed.

Lemma null_app {B: Type} (l1 l2: list B):
  null (l1 ++ l2) = null l1 && null l2.
Proof.
  destruct l1; auto.
Qed.

Lemma null_concat {B: Type} (l: list (list B)):
  null (concat l) = forallb null l.
Proof.
  induction l; simpl; auto. rewrite null_app, IHl; auto.
Qed.

Lemma forallb_map {B C: Type} (f: B -> C) (p: C -> bool) (l: list B):
  forallb p (map f l) = forallb (fun x => p (f x)) l.
Proof.
  induction l; simpl; auto. rewrite IHl; auto.
Qed.

Lemma forallb_false {B: Type} (p: B -> bool) (l: list B):
  forallb p l = false <-> exists x, In x l /\ negb (p x).
Proof.
  induction l; simpl.
  - split; try discriminate. intros;destruct_all; contradiction.
  - split.
    + rewrite andb_false_iff. intros [Hpa | Hall].
      * exists a. split; auto. rewrite Hpa; auto.
      * apply IHl in Hall. destruct Hall as [x [Hinx Hx]].
        exists x. auto.
    + intros [x [[Hax | Hinx] Hnegb]]; subst; auto.
      * destruct (p x); auto. discriminate.
      * apply andb_false_iff. right. apply IHl. exists x; auto.
Qed.

Lemma forallb_t {B: Type} (l: list B):
  forallb (fun _ => true) l.
Proof.
  induction l; auto.
Qed.

Lemma forallb_f {B: Type} (l: list B):
  forallb (fun _ => false) l = null l.
Proof.
  induction l; auto.
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

Lemma forallb_concat {B: Type} (p: B -> bool) (l: list (list B)):
  forallb p (concat l) = forallb (fun l1 => forallb p l1) l.
Proof.
  induction l; simpl; auto. rewrite forallb_app, IHl. auto.
Qed. 

Lemma expand_pat_list_all_null l:
  negb (null l) ->
  (* forallb (fun x => negb (null x)) l -> *)
  forallb (fun x => negb (null x)) (expand_pat_list l).
Proof.
  induction l as [| p t IH]; simpl; auto.
  intros _.
  destruct t as [|t1 t2]; simpl in IH.
  - unfold expand_pat_list; simpl. unfold combinewith. rewrite forallb_concat.
    apply forallb_forall. intros x. rewrite in_map_iff. intros [y [Hy Hiny]]; subst. auto.
  - rewrite expand_pat_list_cons, forallb_concat.
    apply forallb_forall. intros x. rewrite in_map_iff.
    intros [p1 [Hp1 Hinp1]]. subst. rewrite forallb_map. simpl.
    apply forallb_t.
Qed.

Lemma compile_size_cons_lt n x l:
  negb (null (fst x)) ->
  compile_size' n l < compile_size' n (x :: l).
Proof.
  intros Hnull. rewrite compile_size_cons'.
  assert (0 <pat_list_list_size n (expand_pat_list (fst x))); try lia.
  apply pat_list_list_size_pos.
  - rewrite expand_pat_list_null. auto.
  - apply expand_pat_list_all_null. auto.
Qed.  

Lemma pat_list_list_size_nil n:
  pat_list_list_size n nil = 0.
Proof. reflexivity. Qed.

Lemma sum_concat {B: Type} (f: B -> nat) (l: list (list B)) :
  sum (map f (concat l)) = sum (map (fun l1 => sum (map f l1)) l).
Proof.
  induction l; simpl; auto.
  rewrite map_app, sum_app, IHl. auto.
Qed.

Lemma sum_map_sum {B: Type} (f g: B -> nat) (l: list B):
  sum (map (fun (x: B) => f x + g x) l) =
  sum (map f l) + sum (map g l).
Proof.
  induction l; simpl; auto.
  rewrite IHl; auto. lia.
Qed.

(*A similar lemma*)
Lemma pat_list_list_expand_cons_lt n x l:
  pat_list_list_size n (expand_pat_list l) < pat_list_list_size n (expand_pat_list (x :: l)).
Proof.
  rewrite expand_pat_list_cons.
  pose proof (expand_pat_list_null l) as Hnull.
  induction (expand_pat_list l) as [|e1 e2 IH]; simpl; try discriminate.
  destruct e2 as [| e2 e3]; simpl in *.
  - pose proof (expand_pat_null x). destruct (expand_pat x); try discriminate.
    simpl. rewrite !pat_list_list_size_cons.
    rewrite !pat_list_size_n_cons. rewrite pat_list_list_size_nil. 
    pose proof (pat_size_n_pos n p); lia.
  - rewrite pat_list_list_size_cons.
    unfold pat_list_list_size at 2.
    rewrite sum_concat. rewrite !map_map. simpl.
    specialize (IH eq_refl).
    unfold pat_list_list_size at 2 in IH.
    rewrite sum_concat in IH. rewrite !map_map in IH; simpl in IH.
    rewrite sum_map_sum.
    apply Nat.add_lt_mono; auto.
    pose proof (expand_pat_null x). destruct (expand_pat x); try discriminate.
    simpl. rewrite pat_list_size_n_cons. pose proof (pat_size_n_pos n p). lia.
Qed.

Lemma sum_lt {B: Type} (f g: B -> nat) (l: list B)
  (Hlt: forall x, In x l -> f x <= g x):
  sum (map f l) <= sum (map g l).
Proof.
  induction l; simpl in *; auto; try lia.
  apply Nat.add_le_mono; auto.
Qed.

(*A weaker lemma that holds unconditionally*)
Lemma dispatch2_gen_snd_leq n types rl:
  compile_size' n (snd (dispatch2_gen types rl)) <= compile_size' n rl.
Proof.
  rewrite dispatch2_gen_snd. induction rl as [|[ps a] rtl IH]; auto.
  simpl. destruct ps as [| phd ptl]; simpl; auto.
  destruct phd; simpl; auto; try solve[eapply Nat.le_trans; [apply IH| apply compile_size_cons_le]].
  rewrite !compile_size_cons'. simpl.
  apply Nat.add_le_mono; auto.
  rewrite expand_pat_list_cons. simpl. rewrite app_nil_r.
  unfold pat_list_list_size. rewrite map_map. unfold pat_list_size_n. simpl.
  apply sum_lt. intros x Hinx. lia.
Qed.

(*The main lemma: assuming nonempty rl lists, the D matrix is actually smaller*)
Lemma dispatch2_gen_snd_smaller' n types rl:
  negb (null rl) ->
  forallb (fun x => negb (null (fst x))) rl ->
  compile_size' n (snd (dispatch2_gen types rl)) < compile_size' n rl.
Proof.
  rewrite dispatch2_gen_snd. induction rl as [|[ps a] rtl IH]; try discriminate.
  simpl. intros _ Hnull. destruct ps as [| phd ptl]; simpl; try discriminate.
  destruct phd; simpl; auto; try solve[
  eapply Nat.le_lt_trans; [rewrite <- dispatch2_gen_snd with (types:=types); apply dispatch2_gen_snd_leq |
    apply compile_size_cons_lt; auto]].
  (*Only 1 nontrivial case*)
  simpl in *.
  rewrite !compile_size_cons'.
  simpl.
  apply Nat.add_lt_le_mono.
  - apply pat_list_list_expand_cons_lt.
  - rewrite <- (dispatch2_gen_snd types). apply dispatch2_gen_snd_leq.
Qed.

(*TODO: move*)
Check simplify_aux.

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
  negb (null (fst x)) ->
  forallb (fun x => negb (null (fst x))) (simplify_single t x).
Proof.
  destruct x as [ps a]. simpl.
  destruct ps as [| p ptl]; simpl; auto. intros _.
  rewrite forallb_map. simpl. apply forallb_t.
Qed.

Lemma simplify_all_null t rl:
  forallb (fun x => negb (null (fst x))) rl ->
  forallb (fun x => negb (null (fst x))) (simplify t rl).
Proof.
  intros Hall.
  unfold simplify.
  rewrite forallb_concat, forallb_map.
  apply forallb_forall. intros x Hinx.
  apply simplify_single_all_null. unfold is_true in Hall. rewrite forallb_forall in Hall.
  apply Hall; auto.
Qed.

(*And the full result*)
Lemma d_matrix_smaller' n t types rl:
  negb (null rl) ->
  forallb (fun x => negb (null (fst x))) rl ->
  compile_size' n (snd (dispatch1 t types rl)) < compile_size' n rl.
Proof.
  rewrite dispatch_equiv.
  unfold dispatch2.
  intros Hnull Hallnull.
  eapply Nat.lt_le_trans.
  - apply dispatch2_gen_snd_smaller'.
    + rewrite null_simplify; auto.
    + apply simplify_all_null; auto.
  - unfold compile_size'. rewrite expand_full_simplify. auto.
Qed.


(*Proving that the S matrix is smaller is done in several steps:*)

(*Step 0: if cs does not appear in rl, then compile_size n l <= compile_size n rl + (expand_size rl) * (s_args c)*)

(*Step 0.5: if cs does appear in rl, then compile_size n l + n <= compile_size n rl + (expand_size rl) * (s_arcs c)*)


Lemma double n: n + n = 2 * n.
Proof. lia. Qed.

(*What we want to show overall: amap_get funsym_eq_dec (fst (dispatch1 t types rl)) cs = Some l
______________________________________(1/1)
compile_size' n l < compile_size' n rl*) 

(*Lemma pat_list_size_mixed_constr n cs tys pats l:
  pat_list_size_mixed n (Pconstr cs tys pats :: l) =
  (*2 * *)1 + pat_list_size_mixed n (pats ++ l).
Proof.
  simpl. 


 Print pat_size_mixed.

Lemma pat_size_mixed_app n l1 p l2:
  pat_list_size_mixed n (l1 ++ p :: l2) =
  match p with
  | Pwild => pat_list_size_mixed n l1 *)


(*Por case: Por p1 p2 :: ps -> (p1 :: ps, p2 :: ps)
  if sum of products:
  say: if (1 + (size p1) + (size p2)) * (size ps)
  vs: (size p1) * (size ps) + (size p2) * (size ps) 
  still smaller - so why not just multiply instead of powers?
  then, for constr - have (1 + prod (size ps)) * (size tail) = size tail + (size ps) * (size tail)
    and for app (ignoring wild), we have (size ps) * (size tail)
    


 Print pat_iter_op. rewrite !Nat.add_0_r, Nat.pow_add_r, <- Nat.mul_add_distr_l, <- !Nat.mul_assoc. f_equal.
  rewrite double.  induction pats; simpl; auto.




 rewrite !Nat.add_0_r, Nat.pow_add_r. rewrite <- Nat.mul_add_distr_l.
  rewrite !double, !Nat.mul_assoc.
  rewrite (Nat.mul_comm (2 ^ n) 2), <- Nat.mul_assoc. f_equal.
  induction pats; simpl; auto.


  Search (?x + ?x) 2.

  
  Search (?x * (?y + ?z)).

  (*TODO: see if this is enough or do we need 2 * 2^n or something*)
  f_equal. induction pats; simpl. (*START!!!!*)

  f_equal. *) (*TODO
  Search (?x * ?y + ?x * ?z).
  Search (?x ^ (?y + ?z)).
  induction pats; simpl.*)

(*Let;s think: not commutative, but what is worst that can happen going l -> rev l
  worst is that we had addition at beginning, turns into mult (ie. 1 + size tl -> (size p) * (size tl) or something*)

(*Lemma pat_list_size_mixed_rev_app n l1 l2:
  pat_list_size_mixed n (rev l1 ++ l2) <= pat_list_size_mixed n l2 + (pat_list_size_mixed n l1) * (pat_list_size_mixed n l2).
Proof.
  revert l2.
  induction l1 as [| h t IH]; simpl; auto; try lia; intros l2.
  - rewrite <- app_assoc.  eapply Nat.le_trans. apply pat_list_size_mixed_app.
    simpl.
    specialize (IH nil). simpl in IH. rewrite app_nil_r in IH.
    destruct h; simpl; try nia.
    rewrite Nat.mul_comm in IH. simpl in IH.
 rewrite pat_list_sized_mixed_nil in IH.
 apply IH.
    simpl.
    destruct h; simpl; try nia. 
    + rewrite !Nat.add_0_r. lia.


 Check pat_list_size_mixed_app.*)
  
Check choose_all.
Print expand_pat_list.

(*Lemma: l \in (choose_all l1) iff forall i, nth i l in nth i l1*)
(*For all: l \in (choose_all (l1 ++ l2)) iff forall i, nth i l in nth i (l1 ++ l2)
  can we see what is equivalent?*)
(* l: list (list pattern)
comprehension: (choose_all l) == {x : list pattern | forall i, i < length x -> In (nth i x) (nth i l)}

append: if we have (all combos of l1) and (all combose of l2), composition should be
  take all elts of first, take all elts of 2nd, append them
  (maybe do with combine with *)


(*Idea: combinewith {A B C: Type} (f: A -> B -> C) (l1: list A) (l2: list B) : list C :=
  (combine all (f x y) for x in l1 and for y in l2)

  then choose_all (l: list (list pattern)) : list (list pattern) :=
  fold_right (fun (x: list pattern) (acc: list (list pattern)) :=
    concat (map (fun (l1: list pattern) => combinewith cons x l1*)


    (*LHD: tae all posssibilitys from (l1 ++ l2), cons x to front, concat
      RHS: take all possible for l1, append a to top, append with all from l2
    should be equal, need to prove

 Search map concat. rewrite <- concat_map. rewrite !concat_map. rewrite !map_map.
    rewrite !concat_map.


    rewrite !concat_map, !map_map.
    
 rewrite concat_concat. simpl.
    f_equal. rewrite !concat_map. rewrite !map_map.

 rewrite !map_map.


 Search map (fun x => x). auto.
*)
Lemma expand_pat_list_app l1 l2:
  expand_pat_list (l1 ++ l2) =
  (*Idea: get all in l1, get all in l2, combine all*)
  combinewith (fun x y => x ++ y) (expand_pat_list l1) (expand_pat_list l2).
Proof.
  unfold expand_pat_list.
  rewrite map_app, choose_all_app. reflexivity.
Qed.

(*TODO: replace*)
Lemma expand_pat_list_cons' x t: expand_pat_list (x :: t) =
  combinewith cons (expand_pat x) (expand_pat_list t).
Proof.
  reflexivity.
Qed.

Lemma expand_pat_list_nil: expand_pat_list nil = [nil].
Proof. reflexivity. Qed.

Lemma combinewith_rev {B C D: Type} (f: B -> C -> D) (l1: list B) (l2: list C):
  combinewith f (rev l1) (rev l2) = rev (combinewith f l1 l2).
Proof.
  induction l1 as [|h t IH]; simpl; auto.
  rewrite combinewith_app1, !combinewith_cons1, IH.
  rewrite rev_app_distr.
  f_equal.
  unfold combinewith. simpl. rewrite app_nil_r.
  rewrite map_rev. reflexivity.
Qed.
(* 
Lemma combinewith_rev' {B C D: Type} (f: B -> C -> list D) (l1: list B) (l2: list C):
  rev (combinewith f l1 l2) = combinewith (fun x y => rev (f x y)) l1 l2.
Proof.
  induction l1 as [| h t IH]; simpl; auto.
  rewrite !combinewith_cons1.
  rewrite rev_app_distr, IH.
  rewrite <- map_rev.

  rewrite <- map_rev.

  combinewith f (rev l1) (rev l2) = .
Proof.
  induction l1 as [|h t IH]; simpl; auto.
  rewrite combinewith_app1, !combinewith_cons1, IH.
  rewrite rev_app_distr.
  f_equal.
  unfold combinewith. simpl. rewrite app_nil_r.
  rewrite map_rev. reflexivity.
Qed.

Check choose_all.
Lemma choose_all_rev {B: Type} (l: list (list B)) : choose_all (rev l) = rev (choose_all l).
Proof.
  induction l as [| h t IH]; auto.
  simpl. rewrite choose_all_app, IH.
  rewrite <- combinewith_rev.
  

  Search choose_all.
  rewrite choose_all_cons'.
  Print choose_all.

Lemma expand_pat_list_rev l: expand_pat_list (rev l) = rev (expand_pat_list l).
Proof.
  Print expand_pat_list.
  induction l as [| h t IH]; auto.
  simpl. rewrite expand_pat_list_app.
  rewrite (expand_pat_list_cons' h t).
  rewrite <- combinewith_rev, <- IH.
  rewrite expand_pat_list_cons'.
  unfold combinewith at 2. simpl.
  replace ((concat (map (fun x : pattern => [[x]]) (expand_pat h)))) with (map (fun x => [x]) (expand_pat h)).
  2: {
    clear. induction (expand_pat h); simpl; auto.
    rewrite IHl; auto.
  }
  
  

  unfold expand_pat.

  rewrite IH.
  replace (expand_pat_list [h]) with (rev (map (fun x => [x]) (expand_pat h))).
  2: {
    clear. rewrite expand_pat_list_cons'.
    unfold expand_pat_list. simpl.
    induction (expand_pat h); simpl; auto.
    rewrite IHl. unfold combinewith; simpl. rewrite combinewith_cons.

 simpl. unfold expand_pat_list.


 rewrite expand_pat_list_nil.
  
  rewrite <- combinewith_rev, <- IH. 
  


IH.
  rewrite !expand_pat_list_cons', expand_pat_list_nil.
  unfold combinewith at 2. simpl.
  assert (Hconcat: (concat (map (fun x : pattern => [[x]]) (expand_pat h))) = (map (fun x => [x]) (expand_pat h))).
  {
    
  }
  rewrite Hconcat; clear Hconcat.
  


  replace (concat (map (fun x : pattern => [[x]]) (expand_pat h))) with (expand_pat h).
  2: {
    induction (expand_pat h); simpl.

 rewrite concat_map.

  Search expand_pat_list.
   simpl.
  simpl. *)
Search pat_list_size_n.
Lemma pat_list_size_n_app n l1 l2:
  pat_list_size_n n (l1 ++ l2) = pat_list_size_n n l1 + pat_list_size_n n l2.
Proof.
  induction l1; simpl; auto. rewrite !pat_list_size_n_cons, IHl1. lia.
Qed. 

(*TODO: not general enough - only works list -> list -> list*)
Lemma pat_list_list_size_combinewith_app n l1 l2:
  (* (forall x y, pat_list_size_n n (f x y) = (pat_list_size_n n x) + (pat_list_size_n n y)) -> *)
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

Lemma combinewith_cons_app {B: Type} (l1: list B) l2:
  combinewith cons l1 l2 = combinewith (fun x y => x ++ y) (map (fun x => [x]) l1) l2.
Proof.
  unfold combinewith.
  rewrite !map_map. reflexivity.
Qed. 

Lemma combinewith_elts {B C D: Type} (f: B -> C -> D) (l1 : list B) (l2: list C) (x: D):
  In x (combinewith f l1 l2) <-> exists y z, In y l1 /\ In z l2 /\ x = f y z.
Proof.
  unfold combinewith.
  rewrite in_concat.
  split.
  - intros [l [Hinl Hinx]]. rewrite in_map_iff in Hinl.
    destruct Hinl as [y [Hl Hiny]]; subst.
    rewrite in_map_iff in Hinx. destruct Hinx as [z [Hx Hz]]; subst.
    exists y. exists z. auto.
  - intros [y [z [Hiny [Hinz Hx]]]]; subst.
    eexists.
    split.
    + rewrite in_map_iff. exists y. split; auto.
    + rewrite in_map_iff. exists z; auto.
Qed.

Lemma choose_all_lengths {B: Type} (l: list (list B)) (l1: list B):
  In l1 (choose_all l) -> length l1 = length l.
Proof.
  revert l1.
  induction l as [| h t]; simpl; auto; intros l1.
  - intros [Hl1 | []]; subst; auto.
  - rewrite combinewith_elts. intros [y [z [Hiny [Hinz Hl1]]]]. subst.
    simpl. f_equal. apply IHt. auto.
Qed.
    

(*TODO: one with default elt after*)
(*TODO: do we actually need this (at least now?*)
Lemma choose_all_elts {B: Type} (l: list (list B)) (l1: list B):
  In l1 (choose_all l) <-> (length l1 = length l /\ forall x, x < length l -> 
    exists b l2, nth_error l1 x = Some b /\ nth_error l x = Some l2 /\ In b l2).
Proof.
  revert l1.
  induction l as [| h t IH]; intros l1.
  - simpl. split. 
    + intros [Hl1 | []]. subst. split; auto. intros; lia.
    + intros [Hlen _]. destruct l1; simpl in *; auto. discriminate.
  - simpl. rewrite combinewith_elts.
    split.
    + intros [y [z [Hiny [Hinz Hl1]]]]. subst. simpl.
      assert (Hz := Hinz). apply IH in Hz.
      destruct Hz as [Hlenz Hz].
      split; auto.
      intros i Hi.
      destruct i as [|i']; simpl; auto.
      * exists y. exists h. auto.
      * apply Hz. lia.
    + intros [Hlen Helts].
      destruct l1 as [| y z]; try discriminate.
      simpl in Hlen.
      exists y. exists z.
      split_all; auto.
      * specialize (Helts 0 (ltac:(lia))). simpl in Helts.
        destruct Helts as [b1 [l2 [Hb [Hl2 Hinb]]]].
        inversion Hb; inversion Hl2; subst; auto.
      * apply IH; split; try lia. intros x Hx.
        apply (Helts (S x)). lia.
Qed. 

(*Can we prove this*)
Require Import Coq.Sorting.Permutation.

Print choose_all.

Lemma map_const {B C: Type} (d: C) (l: list B):
  map (fun _ => d) l = repeat d (length l).
Proof.
  induction l; simpl; auto. rewrite IHl. reflexivity.
Qed.

Lemma perm_concat_map_cons {B C: Type} (l: list B) (f: B -> C) g:
  Permutation (concat (map (fun x => f x :: g x) l))
    (map (fun x => f x) l ++ concat (map (fun x => g x) l)).
Proof.
  induction l as [| h t IH]; simpl; auto.
  constructor. eapply Permutation_trans.
  - apply Permutation_app_head. apply IH.
  - apply Permutation_app_swap_app. 
Qed.


Lemma combinewith_switch {B C D: Type} (f: B -> C -> D) (l1: list B) (l2: list C):
  Permutation (combinewith f l1 l2) (combinewith (fun x y => f y x) l2 l1).
Proof.
  revert l2. induction l1 as [| h t IH]; intros l2.
  - unfold combinewith. simpl. rewrite map_const.
    replace (concat (repeat [] (Datatypes.length l2))) with (@nil D); auto.
    induction (length l2); simpl; auto.
  - rewrite combinewith_cons1. unfold combinewith in *. simpl.
    eapply Permutation_trans.
    + apply Permutation_app_head. apply IH.
    + eapply Permutation_sym.
      apply perm_concat_map_cons.
Qed.

Lemma combinewith_permutation_fst {B C D: Type} (f: B -> C -> list D) (l1 l1': list B) (l2 : list C):
  Permutation l1 l1' ->
  Permutation (combinewith f l1 l2) (combinewith f l1' l2).
Proof.
  intros Hl1.
  induction Hl1.
  - unfold combinewith. simpl. constructor.
  - rewrite !combinewith_cons1.
    apply Permutation_app; auto.
  - rewrite !combinewith_cons1.
    eapply Permutation_trans.
    apply Permutation_app_swap_app. 
    apply Permutation_app; auto.
  - eapply Permutation_trans. apply IHHl1_1.
    eapply Permutation_trans. apply IHHl1_2.
    auto.
Qed.

Lemma combinewith_permutation_snd {B C D: Type} (f: B -> C -> list D) (l1: list B) (l2 l2' : list C):
  Permutation l2 l2' ->
  Permutation (combinewith f l1 l2) (combinewith f l1 l2').
Proof.
  intros Hperm.
  eapply Permutation_trans.
  - apply combinewith_switch.
  - eapply Permutation_trans.
    2: apply Permutation_sym, combinewith_switch.
    apply combinewith_permutation_fst. auto.
Qed.

Lemma combinewith_permutation {B C D: Type} (f: B -> C -> list D) (l1 l1': list B) (l2 l2' : list C):
  Permutation l1 l1' ->
  Permutation l2 l2' ->
  Permutation (combinewith f l1 l2) (combinewith f l1' l2').
Proof.
  intros Hl1 Hl2.
  eapply Permutation_trans.
  - apply combinewith_permutation_fst. apply Hl1.
  - apply combinewith_permutation_snd. apply Hl2.
Qed.

(*Now proofs about elements of [choose_all]*)
Lemma choose_all_permutation {B: Type} (l1 l2: list (list B)) :
  Forall2 (fun x y => Permutation x y) l1 l2 ->
  Permutation (choose_all l1) (choose_all l2).
Proof.
  revert l2.
  induction l1 as [| h1 t1]; intros l2 Hall.
  - simpl. destruct l2; try inversion Hall. auto.
  - destruct l2 as [| h2 t2]; [inversion Hall|].
    simpl. inversion Hall; subst. apply combinewith_permutation; auto.
Qed.

Lemma combinewith_comp' {B C D: Type} (l1 : list B) (l2 : list C) (l3: list D) f g
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
  (*Separate lemma?*) clear -Hcomp.
  (*TODO: how do f and g have to compose?*)
  induction l2; simpl; [reflexivity|].
  rewrite !combinewith_cons1.
  rewrite !map_app, !map_map.
  rewrite IHl2. f_equal.
  apply map_ext.
  auto.
Qed.
(* 
Lemma permutation_map_f {B C: Type} (l: list B) (f1 f2: B -> list C):
  (forall x, In x l -> Permutation (f1 x) (f2 x)) ->
  Permutation (map f1 l) (map f2 l).
Proof.
  induction l as [|h t IH]; simpl; auto.
  intros Hperms. 
  Search Permutation cons.

 constructor.


Permutation (map (fun y : C => f1 h y) l2) (map (fun y : C => f2 h y) l2) *)

(* Lemma combinewith_permutation_f {B C D: Type} (l1: list B) (l2: list C) (f1 f2: B -> C -> list D):
  (forall b c, Permutation (f1 b c) (f2 b c)) ->
  Permutation (combinewith f1 l1 l2) (combinewith f2 l1 l2).
Proof.
  revert l2. induction l1 as [| h t IH]; intros l2 Hperm.
  - unfold combinewith. simpl. auto.
  - rewrite !combinewith_cons1. apply Permutation_app; auto.
    Search Permutation map.
    apply Permutation_map. *)

(*Just prove specific version*)
(* Lemma combinewith_permutation_rev_app {B: Type} (l1 l2: list (list B)):
  Permutation (combinewith (fun x y => x ++ y) l1 l2) (combinewith (fun x y => y ++ x) l1 l2).
Proof.
  induction l1 as [| h t IH]; simpl; auto.
  rewrite !combinewith_cons1.  *)
Search Permutation concat.
(*The converse is clearly not true*)
Lemma perm_concat {B: Type} (l1 l2: list (list B)):
  Permutation l1 l2 ->
  Permutation (concat l1) (concat l2).
Proof.
  intros Hperm. induction Hperm; simpl; auto.
  - apply Permutation_app; auto.
  - apply Permutation_app_swap_app.
  - eapply Permutation_trans; eauto.
Qed. 

(*What we want to say:
  suppose that l1 and l2 are permutations. Then, if we
  aggregate a commutative operation over all elements of the result, it is equal
  (Note: we CANNOT prove that they are permutations - the elements themselves
  may be in a different order and within each list, the elements are in a different order*)

(*TODO: rewerite with these*)
Definition list_sum {B: Type} (f: B -> nat) (l: list B) : nat :=
  sum (map f l).
Definition list_list_sum {B: Type} (f: B -> nat) (l: list (list B)) : nat :=
  list_sum (list_sum f) l.

(*Need concat here - naive Permutation result not true*)
(*NOTE: just do with sum for now*)

Lemma concat_map_singleton {B: Type} (l: list B):
  concat (map (fun x => [[x]]) l) = (map (fun x => [x]) l).
Proof.
  induction l; simpl; auto. rewrite IHl; auto.
Qed.

(*

Lemma choose_all_permutation2 {B: Type} (l1 l2: list (list B)) (f: B -> nat) :
  Permutation l1 l2 ->
  (*NOT TRUE*) list_list_sum f (choose_all l1) = list_list_sum f (choose_all l2).
Proof.
  revert l2.
  induction l1 as [| h1 t1 IH]; intros l2 Hperm.
  - simpl. apply Permutation_nil in Hperm. subst; auto.
  - simpl.  (*TODO: separte lemma?*)
    assert (Hsplit: exists l3 l4, l2 = l3 ++ h1 :: l4 /\ Permutation t1 (l3 ++ l4)).
    {
      assert (Hin: In h1 l2). { eapply Permutation_in. apply Hperm. simpl; auto. }
      apply in_split in Hin.
      destruct Hin as [l3 [l4 Hl2]]; subst.
      apply Permutation_cons_app_inv in Hperm.
      exists l3. exists l4. auto.
    }
    destruct Hsplit as [l3 [l4 [Hl2 Hpermtl]]]. subst.
    rewrite choose_all_app.
    simpl.

Lemma pat_list_list_size_combinewith_app n l1 l2:
  (* (forall x y, pat_list_size_n n (f x y) = (pat_list_size_n n x) + (pat_list_size_n n y)) -> *)
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

    (*TODO: separate lemma*)
    assert (list_list_sum f (combinewith cons h1 (choose_all t1)) = 
      list_list_sum f (choose_all t1)
    rewrite !combinewith_cons_app.
    rewrite !combinewith_comp.
    2: { intros; rewrite app_assoc; auto. }
    apply IH in Hpermtl.
    rewrite choose_all_app in Hpermtl.
    

    eapply Permutation_trans. 
    { apply perm_concat. apply combinewith_permutation. 2: apply Hpermt
    -
    eapply combinewith_permutation. 2: apply Hpermtl. apply Permutation_refl.
    rewrite !combinewith_comp. 2: intros; rewrite app_assoc; auto.
    apply combinewith_permutation; auto.
    eapply Permutation_trans. apply combinewith_switch.
    simpl.

Lemma list_sum_combinewith {B C: Type} (f: B -> C -> list D) (g: D -> nat):
  list_sum g (combinewith f l1 l2) = 

    unfold combinewith at 1. unfold list_list_sum at 1.
    unfold list_sum at 1 2. rewrite !concat_map,!map_map.
    

 simpl.


(*What we want to say:
  suppose that l1 and l2 are permutations:
  for any aggregations over the resulting lists

    (*TODO: separte lemma?*)
    assert (Hsplit: exists l3 l4, l2 = l3 ++ h1 :: l4 /\ Permutation t1 (l3 ++ l4)).
    {
      assert (Hin: In h1 l2). { eapply Permutation_in. apply Hperm. simpl; auto. }
      apply in_split in Hin.
      destruct Hin as [l3 [l4 Hl2]]; subst.
      apply Permutation_cons_app_inv in Hperm.
      exists l3. exists l4. auto.
    }
    destruct Hsplit as [l3 [l4 [Hl2 Hpermtl]]]. subst.
    rewrite choose_all_app.
    simpl.
    rewrite !combinewith_cons_app.
    rewrite !combinewith_comp.
    2: { intros; rewrite app_assoc; auto. }
    apply IH in Hpermtl.
    rewrite choose_all_app in Hpermtl.
    eapply Permutation_trans. 
    { apply perm_concat. apply combinewith_permutation. 2: apply Hpermt
    -
    eapply combinewith_permutation. 2: apply Hpermtl. apply Permutation_refl.
    rewrite !combinewith_comp. 2: intros; rewrite app_assoc; auto.
    apply combinewith_permutation; auto.
    eapply Permutation_trans. apply combinewith_switch.
    simpl.




 eapply Permutation_trans. apply combinewith_permutation.


 apply Permutation_refl.
    eapply combinewith_permutation.



    Search combinewith cons app.
    Check combinewith_comp'.
    Check (combinewith_comp' (choose_all l3) h1 (choose_all l4)).
    epose proof (combinewith_comp (choose_all l3)).
    rewrite <- combinewith_comp.
    Check combinewith_comp.



      
      Search In app. Search Permutation In.

Permutation_cons_app_inv:
  forall [A : Type] [l : list A] (l1 l2 : list A) [a : A],
  Permutation (a :: l) (l1 ++ a :: l2) -> Permutation l (l1 ++ l2)

      clear -Hperm. remember (h1 :: t1) as l1 eqn : Hl1. generalize dependent t1. revert h1. induction Hperm; subst; auto; intros.
      - discriminate.
      - inversion Hl1; subst. exists nil. exists l'. auto.
      - inversion Hl1; subst. exists [x]. exists l. auto.
      - subst. specialize (IHHperm1 _ _ eq_refl).
        destruct IHHperm1 as [l3 [l4 [Hl' Hperm]]]. subst.
        




 apply IHHperm1 in Hperm1.
 Heql1' subst. contradiction. 
      inversion Hperm; subst. exists nil. exists l'. split; auto.
      exists [x]. exists l. split; auto.
      
      eapply Permutation_sym in Hperm.
      apply Permutation_vs_cons_inv in Hperm.

      
      Permutation_vs_cons_inv:
  forall [A : Type] [l l1 : list A] [a : A],
  Permutation l (a :: l1) -> exists l' l'' : list A, l = l' ++ a :: l''

    Search choose_all app.

 Search Permutation cons. 


Permutation_vs_cons_inv:
  forall [A : Type] [l l1 : list A] [a : A],
  Permutation l (a :: l1) -> exists l' l'' : list A, l = l' ++ a :: l''


 Search (Permutation nil ?x). inversion Hperm; subst. auto. 
  induction Hperm; simpl; auto.
  - apply combinewith_permutation; auto.
  - eapply Permutation_trans. apply combinewith_permutation.
    2: apply combinewith_permutation.

 epose proof (combinewith_comp y x).

 eapply Permutation_trans.  rewrite combinewith_comp. Search combinewith. apply combinewith_permutation; auto.
*)
Lemma Forall2_map {B C D1 D2: Type} (P1: B -> C -> Prop) (P2: D1 -> D2 -> Prop) 
  (f1: B -> D1) (f2: C -> D2) (l1: list B) (l2: list C):
  Forall2 P1 l1 l2 ->
  (forall x y, P1 x y -> P2 (f1 x) (f2 y)) ->
  Forall2 P2 (map f1 l1) (map f2 l2).
Proof.
  intros Hall Hps.
  induction Hall; simpl; auto.
Qed.

(* Lemma expand_pat_list_rev l:
  Permutation (expand_pat_list l) (expand_pat_list (rev l)).
Proof.
  apply choose_all_permutation .
  eapply Forall2_map. 
  eapply Forall2_map with (P1 := fun x y => Permutation x y). 
  Search Forall2 map.
  apply Forall2_map. *)
  
  

(*The theorem we want: if l1 and l1' are permutations, and l2 and l2' are permutations,
  and if f produces a list
  then combineWith f l1 l2 and combindwith f l1' l2' are permutations

  then prove: choose_all is permutation
  then prove (for other): if permutation, length is the same

Lemma combinewith_permutation 

Check Permutation.*)
*)
(*First, prove length*)
(*NOTE: I think this is all useless*)
Lemma sum_repeat n m:
  sum (repeat n m) = m * n.
Proof.
  induction m; simpl; lia.
Qed.

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

Lemma pat_list_list_size_concat_eq n l:
  pat_list_list_size n l = pat_list_size_n n (concat l).
Proof.
  induction l; simpl; auto.
  rewrite pat_list_list_size_cons, pat_list_size_n_app. lia.
Qed.

(*In the end, don't need anything about permutations*)
Lemma pat_list_list_size_rev n l:
  pat_list_list_size n (expand_pat_list (rev l)) =
  pat_list_list_size n (expand_pat_list l).
Proof.
  induction l; simpl; auto.
  rewrite expand_pat_list_cons', expand_pat_list_app, combinewith_cons_app,
    !pat_list_list_size_combinewith_app, !map_length, <- IHl, !expand_pat_list_cons', expand_pat_list_nil.
  unfold combinewith; simpl.
  rewrite concat_map_singleton, !map_length, expand_pat_list_rev_length.
  lia.
Qed.

Lemma dispatch2_gen_bound_in n types rl cs l:
  amap_mem funsym_eq_dec cs types ->
  constr_at_head_ex cs rl ->
  amap_get funsym_eq_dec (fst (dispatch2_gen types rl)) cs = Some l ->
  compile_size' n l + n <= compile_size' n rl + (expand_size rl) * (length (s_args cs)).
Proof.
  intros Htypes Hconstr.
  rewrite dispatch2_gen_fst_in; auto; [| rewrite Hconstr; auto].
  intros Hsome; inversion Hsome; subst; clear Hsome.
  induction rl as [| [ps a] rtl IH]; auto; [discriminate|].
  simpl. simpl in Hconstr.
  unfold constr_at_head in Hconstr. simpl in Hconstr.
  destruct ps as [| p ptl].
  - rewrite expand_size_cons. simpl. rewrite compile_size_cons'. simpl.
    eapply Nat.le_trans. apply IH; auto. lia.
  - destruct p; simpl in Hconstr.
    + rewrite expand_size_cons, compile_size_cons'; simpl.
      eapply Nat.le_trans. apply IH; auto. lia.
    + (*Interesting case: add constr*)
      destruct (funsym_eqb_spec f cs); subst.
      2: {
        (*TODO: factor out*)
        rewrite expand_size_cons, compile_size_cons'; simpl.
        eapply Nat.le_trans. apply IH; auto. lia.
      }
      rewrite expand_size_cons. simpl.
      rewrite expand_size_pat_list_cons. simpl.
      rewrite !compile_size_cons'. simpl.
      rewrite expand_pat_list_cons'. simpl.
      rewrite expand_pat_list_app.
      rewrite pat_list_list_size_combinewith_app.
      rewrite combinewith_cons_app.
      rewrite !map_map.
      rewrite pat_list_list_size_combinewith_app.
      rewrite !map_length.
      fold (expand_pat_list l0).
      (*Main result we need (TODO:separate lemma?)*)
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
      rewrite expand_pat_list_rev_length.
      rewrite pat_list_list_size_rev.
      (*Steps TODO:
        1. Prove general unconditional bound (without n)
        2. lia
        3. prove wild case*)
      assert (compile_size' n
  (filter_map
     (fun x : list pattern * A =>
      match fst x with
      | Pconstr fs _ pats :: ps => if funsym_eqb fs cs then Some (rev pats ++ ps, snd x) else None
      | Pwild :: ps => Some (repeat Pwild (Datatypes.length (s_args cs)) ++ ps, snd x)
      | _ => None
      end) rtl) <= compile_size' n rtl + expand_size rtl * Datatypes.length (s_args cs)) by admit.
      lia.
      



      lia.
      



      Print pat_list_list_size.
      

Print expand_pat_list.
Print choose_all.





      

        Search expand_pat_list.

 nia.

          (*TODO: prove: 


        destruct ptl.
        2: { rewrite expand_pat_list_cons'. simpl.
 simpl. rewrite !Nat.add_0_r.
        unfold pat_list_list_size. rewrite !map_map.
        unfold pat_list_size_n at 2. simpl.
        pose proof (expand_pat_list_null l0).
        induction (expand_pat_list l0); simpl; try lia; try discriminate.
        

        Search expand_pat_list.
        destruct l0; simpl; auto. lia.


 simpl.
        destruct l0; simpl.

        destruct l0; simpl.
        




      Print expand_pat_list.

expand_pat_list_app
      


      (*TODO: might redo some of these above, but first app*)
Check expand_pat_list_cons.
Print choose_all.

  


 simpl.
      simpl.
      Print expand_pat_list.
      Print expand_pat.


      rewrite expand_pat_list_app.
      rewrite expand_pat_list_cons. simpl.

      rewrite compile_size_app'.



 rewrite !compile_size_cons, !expand_size_cons. simpl.
      rewrite expand_size_pat_list_cons. simpl. apply IH in Hconstr. nia.
    + destruct (funsym_eqb_spec f cs); subst.
      * (*Interesting case: add constr*)
        rewrite !compile_size_cons, !expand_size_cons. simpl fst.
        (*TODO: prove that pat_list_size_mixed n (Pconstr _ _ ps) :: tl = pat_list_size_mixed (ps ++ tl)
          and prove that pat_list_size_constr is invariant under rev*)
        rewrite expand_size_pat_list_cons. simpl. Print pat_list_size_mixed.
        unfold pat_list_size_mixed at 1.
        (*So we have: size (rev l0 ++ ptl) + (compile_size rtl) + n <= size ptl + (n + size l0) * (size ptl) +
            compile_size n rtl + (size l0 * expand_size ptl + expand_size rtl) * (length args)

          can say:
            compile_size rtl <= compile_size rtl + expans_size rtl * length (args) - we get

          size (rev l0 ++ ptl) + n <= size ptl + (n + size l0) * (size ptl) +
            (size l0 + expand_size ptl) * (length args)

         ==> size (rev l0 ++ ptl) <= size ptl + (size l0) * (size ptl) + (size l0 + expand_size ptl) * (length args)

        so really, we want to prove that
          size (rev l0 ++ ptl) <= size ptl + (size l0) * (size ptl) - can we prove this?
*)

        
        eapply Nat.le_trans.
        { apply Nat.add_le_mono. 



(*Is it possible to do all multiplication or not?
  dont think so - depends on size, could have n itself there so cannot add more
  *)

(*TODO THIS*)
(*Lemma dispatch2_gen_bound_in n types rl cs l:
  amap_mem funsym_eq_dec cs types ->
  constr_at_head_ex cs rl ->
  amap_get funsym_eq_dec (fst (dispatch2_gen types rl)) cs = Some l ->
  compile_size' n l + n <= compile_size' n rl + (expand_size rl) * (length (s_args cs)).*)


        Print pat_list_size_mixed.
Print pat_size_mixed.
Print pat_iter_op.

        Print expand_size_pat.
 simpl.



 simpl expand_size_pat.
        Search pat_list_size_mixed.
        Print pat_size_mixed.
        rewrite !pat_list_size_mixed_cons.
 simpl.
        

 Print compile_size. simpl.
  

  - dicsriminate.

  Search dispatch2_gen.
Admitted. 

Lemma s_matrix_bound_in n t types rl cs l:
  amap_mem funsym_eq_dec cs types ->
  constr_at_head_ex cs rl ->
  amap_get funsym_eq_dec (fst (dispatch1 t types rl)) cs = Some l ->
  compile_size n l + n <= compile_size n rl + (expand_size rl) * (length (s_args cs)).
Proof.
  intros Htypes. rewrite dispatch_equiv. unfold dispatch2.
  intros Hhead Hget.
  eapply Nat.le_trans.
  - apply constr_at_head_ex_simplify with (t:=t) in Hhead. 
    apply (dispatch2_gen_bound_in _ _ _ _ _ Htypes Hhead Hget).
  - apply Nat.add_le_mono. 
    + apply compile_size_simplify.
    + apply Nat.mul_le_mono; auto. apply expand_size_simplify.
Qed.


  (*This lemma is wrong: length increases - need length of expand

Lemma s_matrix_bound_aux_in n types rl cs l:
  amap_mem funsym_eq_dec cs types ->
  constr_at_head_ex cs rl ->
  amap_get funsym_eq_dec (fst (dispatch2_gen types rl)) cs = Some l ->
  compile_size n l + n <= compile_size n rl + (length rl) * (length (s_args cs)).

  

(*Step 1: Prove: compile_size n l + n <= compile_size n rl + (length rl) * (s_arcs c)*)
Lemma s_matrix_bound n t types rl cs l:
  amap_mem funsym_eq_dec cs types ->
  amap_get funsym_eq_dec (fst (dispatch1 t types rl)) cs = Some l ->
  compile_size n l + n < compile_size n rl.






(*For the S matrix, we first prove the results for [dispatch_gen] (where we don't worry about simplifying,
  and then we compose to get the full result*)

(*Step 0: if cs does not appear in rl, then compile_size n l <= compile_size n rl + (length rl) * (s_args c)*)
(* Lemma s_matrix_bound_aux_in n t types rl *)


(*Proving that the S matrix is smaller is done in several steps:*)

(*Step 0: if cs does not appear in rl, then compile_size n l <= compile_size n rl + (length rl) * (s_args c)*)

(*Step 0.5: if cs does appear in rl, then compile_size n l + n <= compile_size n rl + (length rl) * (s_arcs c)*)
Lemma s_matrix_bound_in n t types rl cs l:
  amap_mem funsym_eq_dec cs types ->
  constr_at_head_ex cs rl ->
  amap_get funsym_eq_dec (fst (dispatch1 t types rl)) cs = Some l ->
  compile_size n l + n <= compile_size n rl + (length rl) * (length (s_args cs)).
Proof.
  intros Htypes. rewrite dispatch_equiv. unfold dispatch2.
  (*This lemma is wrong: length increases - need length of expand

Lemma s_matrix_bound_aux_in n types rl cs l:
  amap_mem funsym_eq_dec cs types ->
  constr_at_head_ex cs rl ->
  amap_get funsym_eq_dec (fst (dispatch2_gen types rl)) cs = Some l ->
  compile_size n l + n <= compile_size n rl + (length rl) * (length (s_args cs)).

  

(*Step 1: Prove: compile_size n l + n <= compile_size n rl + (length rl) * (s_arcs c)*)
Lemma s_matrix_bound n t types rl cs l:
  amap_mem funsym_eq_dec cs types ->
  amap_get funsym_eq_dec (fst (dispatch1 t types rl)) cs = Some l ->
  compile_size n l + n < compile_size n rl.



Lemma s_matrix_smaller n t types rl cs l:
  amap_mem funsym_eq_dec cs types ->
  amap_get funsym_eq_dec (fst (dispatch1 t types rl)) cs = Some l ->
  compile_size n l < compile_size n rl.
Proof.
  intros Htypes.
  (*This time, easier to use dispatch2 (I think)*)
  rewrite dispatch_equiv.
  unfold dispatch2.
   
  Search dispatch2_gen.
  (*TODO: prove*)
  destruct (constr_at_head_ex cs (simplify t rl) || wild_at_head_ex (simplify t rl)) eqn : Hhead.
  2: {
    revert Hhead. rewrite dispatch2_gen_fst_notin; auto. 2: apply Htypes. intros Hnone; rewrite Hnone. discriminate. }
  rewrite dispatch2_gen_fst_in; auto.
  intros Hsome. injection Hsome; clear Hsome. intros Hl; subst. 
  (*So this is the lemma we need to prove*)
  (*TODO: can we prove that compile_size (simplify t rl) <= compile_size n rl, and then compose?*)
  (*This argument is going to be tricky - we can bound above by assuming that every one is a wild,
  split into constr we know exists and all others we assume are wild - 
  the lemma should really say something about n - ... bound

(*So should prove 1. compile_size n l <= compile_size n rl + (length rl) * (s_args c) - n
  2. compile_size n (simplify rl) <= compile_size n rl
  3. define full_simplify (just for patterns not terms)
  4. redefine n to be length (full_simplify rl)
  5. prove that simplify (full_simplify rl) = full_simplify rl (or maybe: full_simplify has only pwild and constr
      even nested)
  6. then prove that filter_map functions we have only decrease full_simplify size
  7 put all together to prove termination

effectively, we are doing a fuel argument, but we are proving that the fuel is sufficient while terminating

note that the expand_all function can itself be defined in equations using regular pattern size as measure
(then pconstr ps -> ps ++ pl, etc
*)



 basically will need to prove that full_simplify never increases with each filter_ma

  3. Redefine n to be length (full_simpl



  Search amap_get dispatch2_gen.
    Search dispatch2_gen.
  (*TODO: prove that all elements in rl are in types*)
  

amap_get funsym_eq_dec (fst (dispatch1 t types rl)) cs = Some l -> compile_size n l < compile_size n rl

(*Old, weaker lemma*)
(*
Lemma dispatch_smaller n t types rhd rtl:
  compile_size n (snd (dispatch t types rhd rtl)) <= pat_list_size_mixed n (fst rhd) + compile_size n (snd rtl).
Proof.
  apply dispatch_elim; intros; auto; try solve[simpl; lia].
  - simpl. rewrite compile_size_cons. simpl. lia.
  - simpl. rewrite compile_size_cons. simpl. destruct pl; simpl; lia.
  - simpl. eapply Nat.le_trans. apply H0.
    eapply Nat.le_trans. apply Nat.add_le_mono_l. apply H.
    simpl snd. rewrite !Nat.add_assoc. apply Nat.add_le_mono_r. simpl fst.
    eapply Nat.le_trans. apply Nat.add_le_mono. apply pat_list_size_mixed_cons. apply pat_list_size_mixed_cons.
    rewrite Nat.add_0_r, !Nat.pow_add_r, Nat.mul_add_distr_r.
    apply Nat.add_le_mono.
    + apply Nat.mul_le_mono_r. rewrite <- (Nat.mul_1_r (2 ^ (pat_size_mixed n p))) at 1.
      apply Nat.mul_le_mono; auto. apply pow_geq_1; lia.
    + apply Nat.mul_le_mono_r. rewrite <- (Nat.mul_1_l (2 ^ (pat_size_mixed n q))) at 1.
      apply Nat.mul_le_mono; auto. apply pow_geq_1; lia.
  - eapply Nat.le_trans. apply H. apply Nat.add_le_mono_r.
    simpl fst. eapply Nat.le_trans. apply pat_list_size_mixed_cons.
    simpl. nia.
Qed.*)

*)*)*)*)

(*TODO: do we need to know that only Pwild/Pconstr*)

(*First, let's prove something about [types] and [cslist] - should be easier*)
(*Probably need map equivalence*)

(*Let's try this*)
Definition dep_let (A: Type) (x: A) : {y: A | y = x} := exist _ x eq_refl.
Obligation Tactic := idtac.

(*The bound we give: (length rl) * (max size of s_args in rl)*)
Definition get_constrs_in (rl: list (list pattern * A)) : list funsym :=
  filter_map (fun y =>
    match (fst y) with
    | Pconstr f _ _ :: _ => Some f
    | _ => None
    end) rl.
Definition iter_max (l: list nat) : nat :=
  fold_right max 0 l.
Definition compile_size_bound (rl: list (list pattern * A)) : nat :=
  expand_size rl  * (iter_max (map (fun (c: funsym) => length (s_args c)) (get_constrs_in rl))).

Fixpoint split (l: list nat) : (list nat * list nat) :=
  match l with
  | nil => (nil, nil)
  | [x] => ([x], nil)
  | x :: y :: tl => let s := split tl in (x :: fst s, y :: snd s)
  end.

Definition pluslen (l1 l2: list nat) := length l1 + length l2.

Equations merge (l1 l2: list nat) : list nat by wf (pluslen l1 l2) :=
  merge (x1 :: t1) (x2 :: t2) => if Nat.leb x1 x2 then x1 :: merge t1 (x2 :: t2) else x2 :: merge (x1 :: t1) t2;
  merge nil l1 => l1;
  merge l2 nil => l2.
Next Obligation.
  intros. simpl. unfold pluslen; simpl. lia.
Defined.
Next Obligation.
  intros. unfold pluslen; simpl. lia.
Defined.

Definition compile_size1 (x: nat * list (list pattern * A)) : nat :=
  compile_size' (fst x) (snd x).
Definition rl_wf (x: nat * list (list pattern * A)) : Prop :=
  (fst x) >= compile_size_bound (snd x).

(* Fixpoint merge (l1 l2: list nat) : list nat :=
  match l1, l2 with
  | x1 :: t1, x2 :: t2 => if x1 <= x2 then x1 :: merge t1 l2 else x2 :: merge l1 t2

Equations mergesort (l1 l2: list nat) by wf (length l1 + length l2) : list nat :=
   *)


(*NOTE: will try to do with pattern, I think that is terminating*)
(*TODO: why does equations not support function of multiple params?*)
Equations compile (tl: list (term * vty)) (rl: nat * list (list pattern * A)) (Hrl: rl_wf rl)
  : option A  by wf (compile_size1 rl) lt :=
  compile _ (n, []) Hn := None;
  compile [] (n, (_, a) :: _) Hn => Some a;
  compile ((t, ty) :: tl) (n, rl) Hn =>
    (*No bare*)
    (*extract the set of constructors*)
    let css :=
    match ty with
    | vty_cons ts _ => get_constructors ts
    | _ => nil
    end in
    (*NOTE: no metadata in funsym saying constructor*)
    let is_constr fs := in_bool funsym_eq_dec fs css in

    (*Here, we do the simplify/dispatch*)

    (*Map every constructor ocurring at the head of the pattern list to the
      list of its args*)
    let types_cslist := populate_all is_constr rl in
    match types_cslist as o return o = types_cslist -> _ with
    | None => fun _ => None
    | Some types_cslist => fun Htypes => 
      (*NOTE: we don't have maps, not ideal*)
      (* fold_left (populate is_constr) (map (fun x => List.hd Pwild (fst x)) rl) (amap_empty, nil)  *)
    let types := fst types_cslist in
    let cslist := snd types_cslist in
    
    (*dispatch part*)
    match dispatch1_opt t types rl as o return dispatch1_opt t types rl = o -> _ with
    | None => fun _ => None
    | Some casewild => fun Hdispatch1 =>
    (* let casewild := dispatch1 t types rl in *)
    let cases := fst casewild in
    let wilds := snd casewild in
    (* let (cases, wilds) := proj1_sig casewild in *)

    (*let comp_cases cs (al : list (term * vty)) :=
      let l := match (amap_get funsym_eq_dec cases cs ) with
      | None => nil (*impossible*)
      | Some l => l
      end in
      compile (rev al ++ tl) l in*)

    let comp_wilds (_: unit) := compile tl (n, wilds) _ in

    let comp_cases cs (al : list (term * vty)) :=
         match (amap_get funsym_eq_dec cases cs ) as o return amap_get funsym_eq_dec cases cs = o -> _ with
          | None => fun _ => None (*impossible*)
          | Some l => fun Hget => compile (rev al ++ tl) (n, l) _
          end eq_refl
        in

    (*TODO: default case here*)
    let comp_full (_: unit) :=
      let no_wilds := forallb (fun f => amap_mem funsym_eq_dec f types) css in
      let base : option (list (pattern * A)) := if no_wilds then Some nil else (*TODO: bind*)
       match comp_wilds tt with
        | None => None
        | Some x => Some [(Pwild, x)]
      end in

      let add acc (x: funsym * list vty * list pattern) : option (list (pattern * A)) :=
        let '(cs, params, ql) := x in
        (*create variables*)
        let pat_tys :=  (map (ty_subst (s_params cs) params) (s_args cs)) in
        let new_var_names := gen_vars (length ql) (tm_fv t ++ tm_bnd t) in
        let typed_vars := map (fun '(x, y) => (fst x, y)) (combine new_var_names pat_tys) in
        let vl := rev typed_vars in 
        (*rev_map (fun x => 
          let v := fst x in
          let p := fst (snd x) in
          let ty := snd (snd x) in
          (fst v, ty)) (combine new_var_names ql) in*)
        let pl := rev_map Pvar vl in
        let al := rev_map Tvar vl in
        (* let comp_cases cs (al : list (term * vty)) :=
         match (amap_get funsym_eq_dec cases cs ) as o return amap_get funsym_eq_dec cases cs = o -> _ with
          | None => fun _ => None (*impossible*)
          | Some l => fun Hget => compile (rev al ++ tl) (n, l) _
          end eq_refl
        in *)
        match (comp_cases cs (combine al (map snd vl))) with
        | None => None
        | Some v => Some ((Pconstr cs params pl, v) :: acc)
        end
      in
      (*TODO: bind*)
      match base with
      | None => None
      | Some b =>
        match (fold_left_opt add cslist b) with
        | None => None
        | Some b1 => Some (mk_case t b1)
        end
      end in 
    
    if null (proj1_sig types) (*TODO: abstraction*) then comp_wilds tt
    else
    
    match t with
    | Tfun cs params al =>

      let comp_cases cs (al : list (term * vty)) :=
       match (amap_get funsym_eq_dec cases cs ) with
      | None => None (*impossible*)
      | Some l =>  compile (rev al ++ tl) (n, l) _
      end
      in

      if is_constr cs then
        if amap_mem funsym_eq_dec cs types then comp_cases cs (combine al
          (map (ty_subst (s_params cs) params) (s_args cs))) else comp_wilds tt
      else comp_full tt
    | _ => 
      comp_full tt 
    end 
end eq_refl
end eq_refl.
Next Obligation.
intros t ty tl n phd ptl Hn compile rl css is_constr types_cslist t2 Heqt2 types cslist casewild Hdispatch cases wilds _.
subst wilds. apply dispatch1_opt_some in Hdispatch.
destruct Hdispatch as [Hnotnull Hcasewild]. rewrite Hcasewild.
revert Hn.
unfold rl_wf. rewrite dispatch_equiv. simpl. replace (phd :: ptl) with rl by auto.
unfold compile_size_bound. intros Hn.
(*TODO: prove that constr_in one -> constr_in other (so max is <=)*)
pose proof (expand_size_dispatch2_gen_snd types (simplify t rl)).
unfold dispatch2.
(*Also TODO just combine in termination metric instead of n separately*)


(*Need to prove that compile_size_bound is smaller with dispatch - is that true?
  it is (length) * max (s_args) - it gets bigger
  really, we want to ensure that it is bigger than simplified version*)
Admitted.
(*Prove that D matrix (wilds) is smaller*)
Next Obligation.
intros t ty tl n phd ptl Hn compile rl css is_constr types_cslist t2 Heqt2 types cslist casewild Hdispatch cases wilds _.
subst wilds. apply dispatch1_opt_some in Hdispatch.
destruct Hdispatch as [Hnotnull Hcasewild]. rewrite Hcasewild.
unfold compile_size1. apply d_matrix_smaller'; auto.
Defined.
(*Prove n bound for S case*)
Next Obligation.
admit.
Admitted.
(*Termination for S matrix for all constructors*)
Next Obligation.
(*2nd termination obligation: comp_cases*)
(*NOTE: can we prove unconditionally?*)
(*TODO: ensure we don't need [comp_wilds] here - shouldn't*)
intros t ty tl n p ptl Hn compile rl css is_constr types_cslist t2 Heqt2 types cslist casewild Hdispatch cases wilds _ cs _ l Hget.
unfold compile_size1. simpl.
fold rl.
apply dispatch1_opt_some in Hdispatch.
destruct Hdispatch as [Hnotnull Hcasewild].
unfold cases in Hget. rewrite Hcasewild in Hget.



unfold compile_size'. simpl.
replace (p :: l0) with rl by auto.
revert Hget. unfold cases, casewild.
rewrite <- rl.


intros t ty tl n p l Hn compile rl css is_constr types_cslist t2 Heqt2 tyes cslist casewild cases wilds comp_wilds _ no_wilds.
subst wilds. unfold casewild.
unfold compile_size'. simpl. eapply Nat.lt_le_trans. apply (dispatch_smaller n).
(*In wilds, what is actually strictly smaller?*)
rewrite compile_size_cons.
apply Nat.add_le_mono_l.
apply dispatch1_smaller.
Defined.
Next Obligation.
Admitted.
Next Obligation.
intros. subst l.
unfold compile_size'; simpl.
destruct (amap_get funsym_eq_dec cases cs) eqn : Hget.


 subst l0.
intros t ty tl n p l Hn compile rl css is_constr types_cslist t2 Heqt2 types cslist casewild cases wilds comp_wilds u no_wilds base
  _ _ _. ql cs params pat_tys new_var_ne





Print dispatch1.


Lemma dispatch_smaller n t types rhd rtl:
  compile_size n (snd (dispatch t types rhd rtl)) <= pat_list_size_mixed n (fst rhd) + compile_size n (snd rtl).

unfold dispatch1.

Print dispatch1.
Check dispatch_smaller.
simpl.

 Search compile_size.


intros t ty tl phd ptl compile rl css is_constr types_cslist types cslist casewild cases wilds _.
subst wilds. unfold casewild.
rewrite dispatch_equiv.
fold rl.
Print dispatch2.
Print dispatch2_gen.
Print dispatch2_aux.
(*TODO: prove about dispatch2*)

 (*?*) compile rl css is_constr types_cslist types cslist casewild cases wilds _ no_wilds.
set (css:= match ty with
    | vty_cons ts _ => get_constructors ts
    | _ => nil
    end) in *.
(*Problem: lose information about cases here*)

(*Idea:
  0. Prove that dispatch1/2 equivalent to filter version (will be useful for both)
  1. Prove that everything in cases has compile_size smaller than rl
  2. Prove that wilds has size smaller than rl 
  3. Probably (maybe) need to inline comp_cases/comp_wilds, or make dependently typed
    may need some kind of convoy pattern so that Equations knows where cases comes from*)

  (*          let pat_tys := (map (ty_subst (s_params fs) params) (s_args fs)) in*)