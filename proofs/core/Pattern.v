(*Compilation of pattern matches*)
Require Import Syntax Denotational.

(*TODO: don't really need but matches interface*)
Definition amap_change {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (f: option B -> B) (x: A) (m: amap A B) : amap A B :=
  amap_replace eq_dec m x (fun _ b => f (Some b)) (f None).
Print amap.
Definition amap_map {A B C: Type} (f: B -> C) (m: amap A B) : amap B C :=


Section Compile.
Context {A: Type} (get_constructors: typesym -> list funsym) 
  (mk_case: term -> list (pattern * A)) (mk_let: vsymbol -> term -> A -> A).

(*NOTE: several different notions of simplification/dispatch, prove equivalent*)

(*Not having maps is annoying*)
Check get_assoc_list.
Check amap.
Definition dispatch :=
  let add_case fs pl a (cases : amap funsym (list (list pattern * A))) :=
    amap_change funsym_eq_dec (fun o =>
      match o with
      | None => [(pl, a)]
      | Some rl => (pl, a) :: rl
      end
      ) fs cases
  in
  let union_cases pl a types cases :=
    let add pl _ := Pwild :: pl in
    let wild ql := [(fold_left add ql pl, a)] in
    let join _ wl rl := Some (wl ++ rl) in
    amap_union join (amap_map wild types) cases 
  in





    amap_replace funsym_eq_dec cases fs (fun )




Definition simplify_dispatch

(*None = NonExhaustive*)
Fixpoint compile (tl: list (term * vty)) (rl: list (list pattern * A)) : option A :=
  match tl, rl with
  | _, [] => None
  | nil, (_, a) :: _ => Some a
  | (t, ty) :: tl, _ =>
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
    let types :=
      (*NOTE: we don't have maps, not ideal*)
      let fix populate (acc : list (funsym * list pattern)) 
        (p: pattern) : list (funsym * list pattern) :=
        match p with
        | Pwild => acc
        | Pvar _ => acc
        | Pconstr fs _ ps => if is_constr fs then
            if in_bool funsym_eq_dec fs (map fst acc) then acc else
            (fs, ps) :: acc
          else nil (*impossible case - Why3 throws exception here*)
        | Por p1 p2 => populate (populate acc p1) p2
        | Pbind p _ => populate acc p
        end
      in
      fold_left populate (map (fun x => List.hd Pwild (fst x)) rl) nil 
    in 
    
    (*dispatch part*)

    
    
    
    compile tl rl
    
  end.