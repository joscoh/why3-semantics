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
    | nil => nil
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
  intros p q pl a cases wilds IH1 IH2. simpl in *.
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
  - rewrite dispatch_equation_1. auto. 
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

Print simplify.

Definition simplified (p: list (list pattern * A)) : bool :=
  (*The first patterns of each are simplified*)
  forallb (fun l => match fst l with | nil => false | p :: _ => simplified_aux p end) p.

Lemma forallb_concat {B: Type} (f: B -> bool) (l: list (list B)):
  forallb f (concat l) = forallb (fun l1 => forallb f l1) l.
Proof.
  induction l; simpl; auto.
  rewrite !forallb_app. rewrite IHl. auto.
Qed.

Lemma forallb_map {B C: Type} (f: B -> C) (p: C -> bool) l:
  (forall x, In x l -> p (f x)) ->
  forallb p (map f l).
Proof.
  induction l; simpl; auto; intros Hin.
  rewrite Hin; auto.
Qed. 

Lemma simplify_simplified t rl :
  simplified (simplify t rl).
Proof.
  unfold simplify, simplified.
  rewrite forallb_concat.
  apply forallb_map.
  intros x Hinx.
  apply forallb_forall.
  intros y Hiny.
  unfold simplify_single in Hiny.
  destruct x as [ps a]; simpl in *.
  destruct ps as [| p ptl]; auto.
  rewrite in_map_iff in Hiny.
  destruct Hiny as [[p2 z] [Hz Hinx']].
  subst. simpl in *.
  pose proof (simplify_aux_simplified t a p) as Hsimpl.
  unfold is_true in Hsimpl.
  rewrite forallb_forall in Hsimpl.
  apply Hsimpl. rewrite in_map_iff. exists (p2, z); auto.
Qed.

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
Print dispatch2_aux.

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
      2 ^ (f p1) * 2 ^ (f p2)
  end.

Definition pat_iter_op (f: pattern -> nat) :=
  fix pat_iter_op (l: list pattern) : nat :=
    match l with
    | nil => 1
    (*| [Pwild] => 2*) (*does NOT work - then does not decrease*)
    | Pwild :: tl => 1 + pat_iter_op tl
    | p :: tl => 2 ^ (f p) * (pat_iter_op tl)
    end.

Fixpoint pat_size_mixed (n: nat) (p: pattern) : nat :=
  match p with
  | Pwild => 1
  | Pvar _ => 1
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
  1 <= pat_list_size_mixed n ps.
Proof.
  induction ps; simpl; try lia.
  destruct a; try solve[simpl; lia].
  - simpl. apply mul_geq_1; auto.
    eapply Nat.le_trans. 2: apply Nat.le_add_r.
    apply pow_geq_1. lia.
  - apply mul_geq_1; auto. apply pow_geq_1. lia.
  - apply mul_geq_1; auto. apply pow_geq_1. lia.
Qed.
  
(*We do NOT have equality: this is crucial for adding pwilds, but we do need that it is
  sometimes a strict equality for the "or" case of simplifying*)
Lemma pat_list_size_mixed_cons n p pl:
  pat_list_size_mixed n (p :: pl) <= 2 ^ pat_size_mixed n p * pat_list_size_mixed n pl.
Proof.
  simpl. destruct p; auto. destruct pl.
  - simpl; lia.
  - set (y:=(pat_list_size_mixed n (p :: pl))). apply add_lt_pow; try lia.
    + apply pat_size_mixed_geq_1.
    + apply pat_list_size_mixed_geq.
Qed.

Lemma lt_le_0_1 n:
  0 < n <-> 1 <= n.
Proof. lia. Qed.
 
Lemma dispatch_smaller n t types rhd rtl:
  compile_size n (snd (dispatch t types rhd rtl)) < pat_list_size_mixed n (fst rhd) + compile_size n (snd rtl).
Proof.
  apply dispatch_elim; intros; auto; try solve[simpl; lia].
  - simpl. rewrite compile_size_cons. simpl. 
    pose proof (pat_list_size_mixed_geq n pl). lia.
  - simpl. rewrite <- (Nat.add_0_l (compile_size n wilds)) at 1. apply Nat.add_lt_mono_r.
    apply lt_le_0_1. apply mul_geq_1.
    + eapply Nat.le_trans. 2: apply Nat.le_add_r. apply pow_geq_1. lia.
    + apply pat_list_size_mixed_geq.
  - simpl. eapply Nat.lt_le_trans. apply H0.
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
Qed.

Lemma dispatch1_smaller n t types rl:
  compile_size n (snd (dispatch1 t types rl)) <= compile_size n rl.
Proof.
  induction rl as [| rhd rtl IH]; auto.
  simpl. eapply Nat.le_trans. apply Nat.lt_le_incl, dispatch_smaller.
  simpl. rewrite compile_size_cons. lia.
Qed.

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
  length (simplify tm_d rl) * (iter_max (map (fun (c: funsym) => length (s_args c)) (get_constrs_in rl))).

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

Definition compile_size' (x: nat * list (list pattern * A)) : nat :=
  compile_size (fst x) (snd x).
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
  : option A  by wf (compile_size' rl) lt :=
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
    let casewild := dispatch1 t types rl in
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

    (*TODO: default case here*)
    let comp_full (_: unit) :=
      let no_wilds := forallb (fun f => amap_mem funsym_eq_dec f types) css in
      let base : option (list (pattern * A)) := if no_wilds then Some nil else (*TODO: bind*)
       match compile tl (n, wilds) _ with
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
        let comp_cases cs (al : list (term * vty)) :=
          let l := match (amap_get funsym_eq_dec cases cs ) with
          | None => nil (*impossible*)
          | Some l => l
          end in
          compile (rev al ++ tl) (n, l) _ in
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
      let l := match (amap_get funsym_eq_dec cases cs ) with
      | None => nil (*impossible*)
      | Some l => l
      end in
      compile (rev al ++ tl) (n, l) _ in

      if is_constr cs then
        if amap_mem funsym_eq_dec cs types then comp_cases cs (combine al
          (map (ty_subst (s_params cs) params) (s_args cs))) else comp_wilds tt
      else comp_full tt
    | _ => 
      comp_full tt 
    end 
end eq_refl.
Next Obligation.
intros t ty tl n phd ptl Hn compile rl css is_constr types_cslist t2 Heqt2 types cslist casewild cases wilds _.
subst wilds. unfold casewild.
unfold rl_wf. simpl.

(*Need to prove that compile_size_bound is smaller with dispatch - is that true?
  it is (length) * max (s_args) - it gets bigger
  really, we want to ensure that it is bigger than simplified version*)
admit.
Admitted.
Next Obligation.
intros t ty tl n phd ptl Hn compile rl css is_constr types_cslist t2 Heqt2 types cslist casewild cases wilds _.
subst wilds. unfold casewild.
unfold compile_size'. simpl. eapply Nat.lt_le_trans. apply (dispatch_smaller n).
(*In wilds, what is actually strictly smaller?*)
rewrite compile_size_cons.
apply Nat.add_le_mono_l.
apply dispatch1_smaller.
Defined.
Next Obligation.


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