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
  let p := List.hd Pwild ps in
    let ptl := List.tl ps in
    map (fun '(p1, y) => (p1 :: ptl, y)) (simplify_aux a p).

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

Definition dispatch2 (rl: list (list pattern * A)) :
  amap funsym (list (list pattern * A)) * list (list pattern * A) :=
  fold_right dispatch2_aux (amap_empty, nil) (simplify rl).

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
  unfold dispatch2, dispatch1.
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

(*NOTE: will try to do with pattern, I think that is terminating*)
Equations compile (tl: list (term * vty)) (rl: list (list pattern * A)) : option A 
  by wf (compile_size rl) lt :=
  compile _ [] := None;
  compile [] ((_, a) :: _) => Some a;
  compile ((t, ty) :: tl) rl =>
  (* match tl, rl with
  | _, [] => None
  | nil, (_, a) :: _ => Some a
  | (t, ty) :: tl, _ => *)
    (*No bare*)
    (*extarct the set of constructors*)
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
    let (types, cslist) :=
      (*NOTE: we don't have maps, not ideal*)
      let fix populate (acc : amap funsym (list pattern) * list (funsym * list vty * list pattern)) 
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
        end
      in
      fold_left populate (map (fun x => List.hd Pwild (fst x)) rl) (amap_empty, nil) 
    in 
    
    (*dispatch part*)
    let (cases, wilds) := dispatch1 t types rl in

    let comp_cases cs (al : list (term * vty)) :=
      let l := match (amap_get funsym_eq_dec cases cs ) with
      | None => nil (*impossible*)
      | Some l => l
      end in
      compile (rev al ++ tl) l in

    let comp_wilds (_: unit) := compile tl wilds in 

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
      if is_constr cs then
        if amap_mem funsym_eq_dec cs types then comp_cases cs (combine al
          (map (ty_subst (s_params cs) params) (s_args cs))) else comp_wilds tt
      else comp_full tt
    | _ => 
      comp_full tt 
    end.
Next Obligation.
(*Problem: lose information about cases here*)

(*Idea:
  1. Prove that everything in cases has compile_size smaller than rl
  2. Prove that wilds has size smaller than rl 
  3. Probably (maybe) need to inline comp_cases/comp_wilds, or make dependently typed
    may need some kind of convoy pattern so that Equations knows where cases comes from*)

  (*          let pat_tys := (map (ty_subst (s_params fs) params) (s_args fs)) in*)