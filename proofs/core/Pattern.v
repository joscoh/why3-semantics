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

Definition union_cases (pl: list pattern) (a: A) (types: amap funsym (list pattern)) 
    (cases: amap funsym (list (list pattern * A))) : amap funsym (list (list pattern * A)) :=
    let add pl _ := Pwild :: pl in
    let wild ql := [(fold_left add ql pl, a)] in
    let join _ wl rl := Some (wl ++ rl) in
    amap_union funsym_eq_dec join (amap_map wild types) cases .

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
  dispatch (nil, _) y := (*impossible*) (amap_empty, nil);
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
      map (fun '(p1, y) => (p1 :: ptl, y)) (simplify_aux a p)
    | nil => nil
    end.

Definition simplify (rl: list (list pattern * A)) : list (list pattern * A) :=
  concat (map simplify_single rl).

Definition dispatch2_aux (x: list pattern * A) 
  (y:  (amap funsym (list (list pattern * A))) * list (list pattern * A) ) : 
  (amap funsym (list (list pattern * A))) * list (list pattern * A) :=
  let (pl, a) := x in
  let (cases, wilds) := y in
  let p := List.hd Pwild pl in
  let pl := List.tl pl in
  match p with
  | Pconstr fs _ pl' => (add_case fs (rev pl' ++ pl) a cases, wilds)
  | Pwild => (union_cases pl a types cases, (pl, a) :: wilds)
  | _ => (*impossible*) (cases, wilds)
  end.

Definition dispatch2_gen (rl: list (list pattern * A)) :
  amap funsym (list (list pattern * A)) * list (list pattern * A) :=
  fold_right dispatch2_aux (amap_empty, nil) rl.

Definition dispatch2 (rl: list (list pattern * A)) :=
  dispatch2_gen (simplify rl).

(*We need this for the odd induction principle*)
Lemma dispatch_equiv_aux x base 
  (Hnull: negb (null (fst x))):
  dispatch x base =
  fold_right dispatch2_aux base (simplify_single x).
Proof.
  revert x base Hnull.
  apply (dispatch_elim (fun x base rec => negb (null (fst x)) -> 
    rec = fold_right dispatch2_aux base (simplify_single x))); auto.
  - intros. discriminate.
  - intros p q pl a cases wilds IH1 IH2. simpl in *.
    intros _.
    rewrite map_app, fold_right_app.
    rewrite <- IH1; auto.
Qed.
 
(*Now we prove equivalence*)
Lemma dispatch_equiv rl (Hrl: Forall (fun x => negb (null (fst x))) rl):
  dispatch1 rl = dispatch2 rl.
Proof.
  unfold dispatch2, dispatch2_gen, dispatch1.
  induction rl as [|[pl a] ps IH]; simpl; auto.
  inversion Hrl as [|? ? Hpl Hps]; subst; simpl in *.
  unfold simplify in *. simpl.
  rewrite fold_right_app.
  destruct pl as [| phd ptl]; simpl in *; try discriminate.
  rewrite <- IH; auto.
  destruct (fold_right dispatch (amap_empty, []) ps) as [cases1 wilds1] eqn : Hd2.
  apply dispatch_equiv_aux. reflexivity.
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

Definition compile_size (l: list (list pattern * A)) : nat :=
  sum (map pat_list_size (map fst l)).

Section Populate.
Variable (is_constr : funsym -> bool).
Fixpoint populate  (acc : amap funsym (list pattern) * list (funsym * list vty * list pattern)) 
        (p: pattern) : amap funsym (list pattern) * list (funsym * list vty * list pattern) :=
        match p with
        | Pwild => acc
        | Pvar _ => acc
        | Pconstr fs params ps =>
          let (css, csl) := acc in
            if is_constr fs then
            if amap_mem funsym_eq_dec fs css then acc else
            (amap_set funsym_eq_dec css fs ps, (fs, params, ps) :: csl)
          else acc (*impossible case - Why3 throws exception here*)
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
  fold_left (populate is_constr) (map (fun x => List.hd Pwild (fst x)) rl) (amap_empty, nil).
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
  

(*TODO: do we need to know that only Pwild/Pconstr*)

(*First, let's prove something about [types] and [cslist] - should be easier*)
(*Probably need map equivalence*)



(*Lemma dispatch2_gen_fst (types: amap funsym (list pattern)) rl cs args
  (*Cannot be iff for IH*)
  (*(Htypes: forall cs args, amap_get funsym_eq_dec types cs = Some args ->
    exists ps tys a, In (Pconstr cs tys args :: ps, a) rl)*):
  amap_get funsym_eq_dec types cs = Some args ->
  amap_get funsym_eq_dec (fst (dispatch2_gen types rl)) cs = Some
    (filter_map (fun x =>
    let ps := fst x in
    let a := snd x in
    let p := hd Pwild ps in
    let ps := tl ps in
    match p with
    | Pwild => Some (repeat Pwild (length args) ++ ps, a)
    | Pconstr fs tys pats =>
        if funsym_eqb fs cs then Some (rev pats ++ ps, a) else None
    | _ => None
    end) rl).
Proof.
  intros Htypesget.
  induction rl as [| [ps a] rtl IH]; simpl.
  - apply Htypes in Htypesget. destruct_all; contradiction.
  - simpl in Htypes. rewrite amap_empty_get. in Hget. discriminate.
  - destruct (dispatch2_gen types rtl) as [cases wilds] eqn : Hrec.
    simpl in *. 


  (*(rl_wf: forall c tys1 tys2 ps1 ps2 l1 l2, In (Pconstr c tys1 ps1) (concat (map fst l1)) -> 
    In (Pconstr c tys2 ps2) (concat (map fst l2)) -> length tys1 = length tys2 /\ length ps1 = length ps2):*):
  amap_get funsym_eq_dec (fst (dispatch2_gen types rl)) cs = Some l ->
  l = filter_map (fun x =>
    let ps := fst x in
    let a := snd x in
    let p := hd Pwild ps in
    let ps := tl ps in
    match (amap_get funsym_eq_dec types cs) with
    | None => (*impossible*) None
    | Some args =>
        match p with
        | Pwild => Some (repeat Pwild (length args) ++ ps, a)
        | Pconstr fs tys pats =>
            if funsym_eqb fs cs then Some (rev pats ++ ps, a) else None
        | _ => None
        end 
    end) rl.
Proof.


Lemma dispatch2_gen_fst (types: amap funsym (list pattern)) rl cs l


  (*(rl_wf: forall c tys1 tys2 ps1 ps2 l1 l2, In (Pconstr c tys1 ps1) (concat (map fst l1)) -> 
    In (Pconstr c tys2 ps2) (concat (map fst l2)) -> length tys1 = length tys2 /\ length ps1 = length ps2):*):
  amap_get funsym_eq_dec (fst (dispatch2_gen types rl)) cs = Some l ->
  l = filter_map (fun x =>
    let ps := fst x in
    let a := snd x in
    let p := hd Pwild ps in
    let ps := tl ps in
    match (amap_get funsym_eq_dec types cs) with
    | None => (*impossible*) None
    | Some args =>
        match p with
        | Pwild => Some (repeat Pwild (length args) ++ ps, a)
        | Pconstr fs tys pats =>
            if funsym_eqb fs cs then Some (rev pats ++ ps, a) else None
        | _ => None
        end 
    end) rl.
Proof.
  induction rl as [| [ps a] rtl IH]; simpl.
  - intros Hget. rewrite amap_empty_get in Hget. discriminate.
  - destruct (dispatch2_gen types rtl) as [cases wilds] eqn : Hrec.
    simpl in *. 
 discrimintae. Search amap_empty.

Proof.
  


  
  l = map (filter (fun x =>
    let ps := fst x in
    let a := snd x in
  rl).
  *)
Print compile_size.
Lemma compile_size_cons p l:
  compile_size (p :: l) = pat_list_size (fst p) + compile_size l.
Proof.
  reflexivity.
Qed.

Lemma compile_size_app l1 l2:
  compile_size (l1 ++ l2) = compile_size l1 + compile_size l2.
Proof.
  induction l1; simpl; auto.
  rewrite !compile_size_cons. lia.
Qed.

Lemma compile_size_concat l:
  compile_size (concat l) = sum (map compile_size l).
Proof.
  induction l; simpl; auto.
  rewrite compile_size_app. lia.
Qed.

Print simplify_single.
Print simplify_aux.

Lemma pat_list_size_nil: pat_list_size nil = 0.
Proof. reflexivity. Qed.

(*TODO: unify these*)
Lemma pat_list_size_app l1 l2:
  pat_list_size (l1 ++ l2) = pat_list_size l1 + pat_list_size l2.
Proof.
  induction l1; simpl; auto. rewrite !pat_list_size_cons. lia.
Qed.

Lemma simplify_aux_smaller t a p:
  pat_list_size (map fst (simplify_aux t a p)) <= pat_size p.
Proof.
  revert a.
  induction p; simpl; intros a; try reflexivity.
  - rewrite pat_list_size_cons, pat_list_size_nil; simpl; lia.
  - rewrite map_app, pat_list_size_app. specialize (IHp1 a); specialize (IHp2 a).  lia.
  - specialize (IHp (mk_let v t a)). lia.
Qed.

(*The point is that even when we split, this is all a part of the original
  However, the pattern can indeed get bigger
  example (simple): (Pvar x | Pvar y) :: Pwild becomes (Pvar x :: Pwild), (Pvar y :: Pwild) - 
    the size is clearly larger
  maybe instead we want the maximum? but that doesn't work either
  if we did maximum, let's see
  but by the dispatch, it should work?*)
Print dispatch1.

Lemma compile_size_nil: compile_size nil = 0.
Proof. reflexivity. Qed.

(*Another compile measures*)
Definition iter_mult (l: list nat) : nat :=
  fold_right mult 1 l.
Definition pattern_list_size' (ps: list pattern) : nat :=
  iter_mult (map (fun p => 2 ^ (pat_size p)) ps).
Check compile_size.
Print compile_size.
Definition compile_size' (l: list (list pattern * A)) : nat :=
  sum (map pattern_list_size' (map fst l)).

Lemma compile_size_cons' a l:
  compile_size' (a :: l) = pattern_list_size' (fst a) + compile_size' l.
Proof.
  reflexivity. Qed.
Lemma compile_size_nil': compile_size' nil = 0.
Proof. reflexivity. Qed.

Lemma pattern_list_size_cons' p l:
  pattern_list_size' (p :: l) = 2 ^ (pat_size p) * (pattern_list_size' l).
Proof. reflexivity. Qed.
Search (( ?x + ?y) * ?z).
Search (?x ^ (?y + ?z)).
Search (?x + ?y <= ?w + ?v).
 Search (?x <= ?y * ?x).
Search (?x <= ?y ^ ?z).

Lemma pow_geq_1 n m:
  n <> 0 ->
  1 <= n ^ m.
Proof.
  induction m; simpl; lia.
Qed.

Lemma mul_le n m:
  1 <= m ->
  n <= m * n.
Proof.
pose proof (Arith_prebase.mult_O_le_stt n m). lia.
Qed. 

Lemma dispatch_smaller t types a rl:
  compile_size' (snd (dispatch t types a rl)) <= compile_size' (a :: (snd rl)).
Proof.
  apply dispatch_elim; intros; simpl.
  - rewrite compile_size_nil'; lia.
  - rewrite !compile_size_cons'; simpl. rewrite pattern_list_size_cons'.
    simpl. lia.
  - rewrite compile_size_cons'; simpl. lia.
  - rewrite !compile_size_cons'; simpl. 
    rewrite pattern_list_size_cons'. simpl. lia.
  - simpl in *. revert H H0. rewrite !compile_size_cons'; simpl.
    rewrite !pattern_list_size_cons'; simpl. 
    intros Hlt1 Hlt2. eapply Nat.le_trans. apply Hlt2.
    apply (Nat.add_le_mono_l _ _ (2 ^ pat_size p * pattern_list_size' pl)) in Hlt1.
    eapply Nat.le_trans. apply Hlt1. clear.
    (*Why we needed exponents*)
    rewrite Nat.add_0_r. rewrite !Nat.add_assoc. apply Nat.add_le_mono_r.
    rewrite Nat.mul_add_distr_r, !Nat.pow_add_r.
    apply Nat.add_le_mono.
    + rewrite <- (Nat.mul_comm (2^ (pat_size q))). rewrite <- Nat.mul_assoc. apply mul_le, pow_geq_1. auto.
    + rewrite <- Nat.mul_assoc. apply mul_le, pow_geq_1. auto.
  - rewrite !compile_size_cons' in H |- *. simpl in *. rewrite pattern_list_size_cons' in H |- *; simpl in *.
    eapply Nat.le_trans. apply H. rewrite Nat.add_0_r. nia.
Qed.

(*START: use this metric, prove the full result (maybe use simplify but prob not)*)
      


 assert (1 <= pat_size q) by admit. nia. lia.
    
    
    
    Search "distr". 

 nia.

    Search (?z + ?x <= ?z + ?y).
    assert (Hlt3: 2 ^ pat_size p * pattern_list_size' pl +
      
2 ^ pat_size p * pattern_list_size' pl +

 nia.



 nia. lia.
   lia.
    nia.

 lia. 

 lia.

Lemma dispatch_smaller t types a rl:
  compile_size (snd (dispatch t types a rl)) <= compile_size (a :: (snd rl)).
Proof.
apply dispatch_elim.
- intros. simpl. rewrite compile_size_nil; auto. lia.
- intros. simpl. rewrite !compile_size_cons. simpl. unfold pat_list_size. lia.
- intros. simpl. rewrite compile_size_cons. simpl. lia.
- intros; simpl. rewrite !compile_size_cons. simpl. unfold pat_list_size; lia.
- intros; simpl. rewrite !compile_size_cons; simpl in *.
  rewrite !compile_size_cons in H, H0. simpl in *.
  rewrite !pat_list_size_cons in H, H0; simpl in *.
  (*Doesn't work: "or" becomes larger
    So what is the termination metric? - maybe it is the 

    is it possible to not terminate?

    so if we have (p1 | p2) ; Pwild, end up with
      (p1 :: Pwild), (p2 :: Pwild)

    what if we do exponentially decreasing:
    like sum (2 ^ size p) (or mult?)
    2 ^ (|p1| + |p2| + 1) = 2 * 2^(|p1|) * 2 ^(|p2|)
    which is larger than  2^(|p1|) * 2^(|p2|)

    so this should work
    and same for the terms

    will be more complicated

    like: 2^(length l) * 1 + ...
    would be smaller if this is smaller
    otherwise, Por = |p1| + |p2| + 1, so


 lia.

 lia.
  

 lia. 

 rewrite compile_size_cons. simpl. rewrite compile_size_nil.
Search dispatch.
Admitted.


Lemma dispath1_smaller t types rl:
  compile_size (snd (dispatch1 t types rl)) <= compile_size rl.
Proof.
  induction rl; simpl; auto.


  

  Print dispatch1.

Lemma simplify_single_smaller t ps a:
  compile_size (simplify_single t (ps, a)) <= pat_list_size ps.
Proof.
  unfold simplify_single.
  destruct ps; auto.
  rewrite pat_list_size_cons.
  assert (forall rl, compile_size (map (fun '(p1, y) => (p1 :: ps, y)) rl) =
    pat_list_size (map fst rl) + pat_list_size ps).
  {
    intros rl. induction rl; simpl.


  Print simplify_single.
  revert a.
  induction ps as [|phd ptl IH]; intros a; simpl; auto.
  rewrite pat_list_size_cons.
  destruct phd; simpl.
  - rewrite compile_size_cons; simpl. unfold compile_size; simpl.
  Search pat_list_size.
  Print simplify_single.

Lemma simplify_smaller t rl : compile_size (simplify t rl) <= compile_size rl.
Proof.
  unfold simplify.
  induction rl; simpl; try lia.
  rewrite compile_size_app, compile_size_cons.
  (*TODO: lemma?*)
  assert (hhd: compile_size (simplify_single t a) <= pat_list_size (fst a)).
  {
    destruct a as [ps a]; simpl in *.
    destruct ps as [| phd ptl]; simpl; auto.
    
    unfold simplify_aux.
    simpl.


  unfold simplify_single. destruct a as [ps a]; simpl in *.
  destruct ps as 
  Print simplify_single.
  simpl.


  rewrite compile_size_concat.
  induction rl; simpl; try lia.
  rewrite compile_

Lemma wild_smaller t types rl: compile_size (snd (dispatch2 t types rl)) < compile_size rl.
Proof.
  unfold dispatch2. Check simplify t rl.


(*Let's try this*)
Definition dep_let (A: Type) (x: A) : {y: A | y = x} := exist _ x eq_refl.
Obligation Tactic := idtac.
(*NOTE: will try to do with pattern, I think that is terminating*)
Equations compile (tl: list (term * vty)) (rl: list (list pattern * A)) : option A 
  by wf (compile_size rl) lt :=
  compile _ [] := None;
  compile [] ((_, a) :: _) => Some a;
  compile ((t, ty) :: tl) rl =>
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
    let types_cslist :=
      (*NOTE: we don't have maps, not ideal*)
      fold_left (populate is_constr) (map (fun x => List.hd Pwild (fst x)) rl) (amap_empty, nil) 
    in 
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

    let comp_wilds (_: unit) := compile tl wilds in

    (*TODO: default case here*)
    let comp_full (_: unit) :=
      let no_wilds := forallb (fun f => amap_mem funsym_eq_dec f types) css in
      let base : option (list (pattern * A)) := if no_wilds then Some nil else (*TODO: bind*)
       match compile tl wilds with
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
          compile (rev al ++ tl) l in
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
      compile (rev al ++ tl) l in

      if is_constr cs then
        if amap_mem funsym_eq_dec cs types then comp_cases cs (combine al
          (map (ty_subst (s_params cs) params) (s_args cs))) else comp_wilds tt
      else comp_full tt
    | _ => 
      comp_full tt 
    end.
Next Obligation.
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