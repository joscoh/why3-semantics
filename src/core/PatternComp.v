(*Compile pattern matching*)
Require Import TermDefs TermFuncs Monads.
Require CoqBigInt.
Import MonadNotations.
Require Import PatternAux.

Local Open Scope err_scope.

Definition NonExhaustive (l: list pattern_c) : errtype := 
  mk_errtype "NonExhaustive" l.
Definition ConstructorExpected (x: lsymbol * ty_c) : errtype :=
  mk_errtype "ConstructorExpected" x.


(*TODO: move*)
Definition Failure (msg: string) : errtype :=
  mk_errtype "Failure" msg.

(*Error-throwing hd (TODO move)*)
Definition hd {A: Type} (l: list A) : errorM A :=
  match l with
  | nil => throw (Failure "hd")
  | x :: _ => err_ret x
  end.

Definition tl {A: Type} (l: list A) : errorM (list A) :=
  match l with
  | nil => throw (Failure "tl")
  | _ :: xs => err_ret xs
  end.

(*We split into multiple functions*)
Section Populate.
Variable (is_constr: lsymbol -> bool) (ty: ty_c).
Fixpoint populate 
  (acc: Mls.t (list pattern_c) * list (lsymbol * (list pattern_c)))
  (p: pattern_c) : errorM (Mls.t (list pattern_c) * list (lsymbol * list pattern_c)) :=
  match pat_node_of p with
  | Pwild => err_ret acc
  | Pvar _ => err_ret acc
  | Pas p _ => populate acc p
  | Por p q =>
    p1 <- (populate acc p);; 
    populate p1 q
  | Papp fs pl =>
    if is_constr fs then
      if Mls.mem _ fs (fst acc) then err_ret acc else
      err_ret (Mls.add fs pl (fst acc), ((fs, pl) :: (snd acc)))
    else throw (ConstructorExpected (fs, ty))
  end.

  Definition populate_all {A: Type} (rl : list (list pattern_c * A)) :
    errorM (Mls.t (list pattern_c) * list (lsymbol * list pattern_c))  := 
      let populate acc (x: list pattern_c * A) : 
        errorM (Mls.t (list pattern_c) * list (lsymbol * list pattern_c))  := 
        p <- hd (fst x) ;;
        populate acc p in
      foldl_err populate rl (Mls.empty, nil).
End Populate.

Section Dispatch.
Context {A B: Type} (mk_let: vsymbol -> term_c -> B -> B) (t: term_c) 
  (types: Mls.t (list pattern_c)).

(*For dispatch, we need Equations, since it is not structurally recursive*)
Definition add_case (fs: lsymbol) (pl: list pattern_c) (a: B) cases :=
    Mls.change _ (fun x =>
      match x with
      | None => Some [(pl, a)]
      | Some rl => Some ((pl, a) :: rl)
      end) fs cases.

Definition union_cases pl (a: B) (types : Mls.t (list pattern_c)) cases :
    Mls.t (list (list pattern_c * B)) :=
    let add pl q := pat_wild (pat_ty_of q) :: pl in
    let wild ql := [(fold_left add ql pl, a)] in
    let join _ wl rl := Some (wl ++ rl) in
    Mls.union _ join (Mls.map wild types) cases.

(*Don't use [hd] and [tl], pattern match for struct recursion*)

(*Lemmas for termination*)
Lemma dispatch_aux_or1 {p p1 q1 pl pla} 
  (Hpl: p :: pl = pla) (Heq: pat_node_of p = Por p1 q1):
  list_pattern_c_size (p1 :: pl) < list_pattern_c_size pla.
Proof.
  subst. unfold list_pattern_c_size. simpl.
  rewrite (pattern_c_size_unfold p), Heq. lia.
Qed.

Lemma dispatch_aux_or2 {p p1 q1 pl pla} 
  (Hpl: p :: pl = pla) (Heq: pat_node_of p = Por p1 q1):
  list_pattern_c_size (q1 :: pl) < list_pattern_c_size pla.
Proof.
  subst. unfold list_pattern_c_size. simpl.
  rewrite (pattern_c_size_unfold p), Heq. lia.
Qed.

Lemma dispatch_aux_bind {p p1 x pl pla} 
  (Hpl: p :: pl = pla) (Heq: pat_node_of p = Pas p1 x):
  list_pattern_c_size (p1 :: pl) < list_pattern_c_size pla.
Proof.
  subst. unfold list_pattern_c_size. simpl.
  rewrite (pattern_c_size_unfold p), Heq. lia.
Qed.

(*TODO: move lemmas to aux file*)
(*TODO: really termination metric is just size of first elt of list*)
(*NOTE: [pat_node_of] makes this VERY annoying*)
(*TODO: rewrite with Equations, generates LOTS of unhelpful stuff*)
Fixpoint dispatch_aux (pla: list pattern_c * B) 
  (casewild: (Mls.t (list (list pattern_c * B)) * list (list pattern_c * B)))
  (ACC: Acc lt (list_pattern_c_size (fst pla))) :
    errorM (Mls.t (list (list pattern_c * B)) * list (list pattern_c * B)) :=
    let cases := fst casewild in
    let wilds := snd casewild in
    match (fst pla) as o return o = fst pla -> _ with
    | nil => fun _ => throw (Failure "hd")
    | p :: pl => fun Hpl =>
      let cases := fst casewild in
      let wilds := snd casewild in
      let a := snd pla in
      match (pat_node_of p) as p' return pat_node_of p = p' -> _ with
      | Papp fs pl' => fun Heq =>
        err_ret (add_case fs (rev_append pl' pl) a cases, wilds)
      | Pwild => fun Heq => err_ret (union_cases pl a types cases, (pl, a) :: wilds)
      | Por p1 q1 => fun Heq =>
        d1 <- dispatch_aux (q1 :: pl, a) (cases, wilds) (Acc_inv ACC (dispatch_aux_or2 Hpl Heq)) ;;
        dispatch_aux (p1 :: pl, a) d1 (Acc_inv ACC (dispatch_aux_or1 Hpl Heq))
      | Pas p x => fun Heq =>
        dispatch_aux (p :: pl, mk_let x t a) (cases,wilds) (Acc_inv ACC (dispatch_aux_bind Hpl Heq))
      | Pvar x => fun Heq =>
        let a := mk_let x t a in
        err_ret (union_cases pl a types cases, (pl, a) :: wilds) 
      end eq_refl
    end eq_refl.

Definition dispatch_aux' (pla: list pattern_c * B) 
  (casewild: (Mls.t (list (list pattern_c * B)) * list (list pattern_c * B))) :
    errorM (Mls.t (list (list pattern_c * B)) * list (list pattern_c * B)) :=
  dispatch_aux pla casewild (Wf_nat.lt_wf _).


(* 

Equations dispatch_aux (pla: list pattern_c * B) 
  (casewild: (Mls.t (list (list pattern_c * B)) * list (list pattern_c * B))) :
    errorM (Mls.t (list (list pattern_c * B)) * list (list pattern_c * B))
  by wf (list_pattern_c_size (fst pla)) lt:=
  dispatch_aux (p :: pl, a) (cases, wilds) :=
  (* let cases := fst casewild in
  let wilds := snd casewild in
  let a := snd pla in
  p <- hd (fst pla) ;;
  pl <- tl (fst pla) ;; *)
    match (pat_node_of p) as p' return pat_node_of p = p' -> _ with
    | Papp fs pl' => fun Heq =>
      err_ret (add_case fs (rev_append pl' pl) a cases, wilds)
    | Pwild => fun Heq => err_ret (union_cases pl a types cases, (pl, a) :: wilds)
    | Por p1 q1 => fun Heq =>
      d1 <- dispatch_aux (q1 :: pl, a) (cases, wilds) ;;
      dispatch_aux (p1 :: pl, a) d1
    | Pas p x => fun Heq =>
      dispatch_aux (p :: pl, mk_let x t a) (cases,wilds)
    | Pvar x => fun Heq =>
      let a := mk_let x t a in
      err_ret (union_cases pl a types cases, (pl, a) :: wilds) 
    end eq_refl;
  dispatch_aux (nil, a) (cases, wilds) := throw (Failure "hd").
Next Obligation.
unfold list_pattern_c_size; simpl.
rewrite (pattern_c_size_unfold p), Heq. lia.
Defined.
Next Obligation.
unfold list_pattern_c_size; simpl.
rewrite (pattern_c_size_unfold p), Heq. lia.
Defined.
Next Obligation.
unfold list_pattern_c_size; simpl.
rewrite (pattern_c_size_unfold p0), Heq. lia.
Defined. *)
(*TODO: see how OCaml code is to see if we need Xavier trick*)

Definition dispatch rl := foldr_err (fun x y => dispatch_aux' y x) rl (Mls.empty, nil) .

End Dispatch.

(*Compile intermediate parts*)
Section Compile.

Context {A: Type}. (*the return type*)

(*NOTE: we do everything without exceptions and only use them at the end. 
  Using try/catch in Coq is much more difficult; we implemented a simple
  try/catch mechanism in Monads.v but this does not allow us to
  match on the argument *)
Variant compile_result:=
  | Succ : A -> compile_result
  | NonExh : list pattern_c -> compile_result.

(*The real result will be errorM (compile_result) - we
  need this to keep track of pattern list*)

Definition compile_exn (e: errorM compile_result) : 
  errorM A :=
  x <- e ;;
  match x with
  | Succ y => err_ret y
  | NonExh ps => throw (NonExhaustive ps)
  end.


(*NOTE: We can have a NonExhaustive inside an OtherExn (it's all the same in
the end). We don't want to pattern match on the exception, since that is
hard to extract to OCaml. And we aren't chanining these, so it is OK
to lose the ps info (which is the whole reason we have this type)*)
(* Definition map_nonexh (f: list pattern_c -> errorM (list pattern_c)) (c: compile_result) :
  compile_result :=
  match c with
  | Succ x => Succ x
  | NonExh ps => OtherExn (
      x <- f ps ;;
      err_ret)
  | OtherExn e => OtherExn e
  end. *)

Definition comp_cases {A: Type} (compile: list term_c -> list (list pattern * A) -> errorM compile_result) 
  cases tl ty cs al : errorM compile_result :=
  r <- (Mls.find _ cs cases) ;;
  c <- compile (rev_append al tl) r ;;
  match c with
  | Succ a => err_ret (Succ a)
  | NonExh pl => 
    (*The catch case*)
    (*We don't prove anything about this so it's fine to have a nested fix*)
    (*TODO: see if OK to use non-hashconsing-version since it's just for exception anyway*)
    let fix cont acc vl pl : errorM (list pattern_c) := 
    match vl,pl with
      | (_::vl), (p::pl) => 
        cont (p::acc) vl pl
      | [], pl => 
        p1 <- pat_app_aux cs acc ty ;;
        err_ret (p1 :: pl)
      | _, _ => assert_false "comp_cases failed"
    end
    in
    c <- (cont nil cs.(ls_args) pl) ;;
    throw (NonExhaustive c)
  end.

End Compile.


(*TODO: let's see*)
(*TODO: Equations*)
(*Unlike their exception method, we will use an extra "bare" param*)
(*Section Compile.
Context {A: Type} (get_constructors: tysymbol_c -> list lsymbol) 
  (mk_case: term_c -> list (pattern * A) -> A) 
  (mk_let: vsymbol -> term_c -> A -> A).
Fixpoint compile_aux (bare: bool) 
  (tl: list term_c) (rl: list (list pattern_c * A)): errorM A :=
  match tl, rl with
  | _, nil => 
    pl1 <- errorM_list (map t_type tl) ;;
    let pl := map pat_wild pl1 in
    throw (NonExhaustive pl)
  | nil, (_ , a) :: _ => err_ret a
  | t :: tl, _ =>
    ty <- t_type t ;;
    (*Extract the set of constructors*)
    let (bare, css) := match ty_node_of ty with
      | Tyapp ts _ =>
        if bare then (true, Sls.empty) else
        (false, Sls.of_list (get_constructors ts))
      | Tyvar _ => (false,  Sls.empty)
    end
    in
    (*if bare, only check fs.ls_constr*)
    let is_constr fs :=
      CoqBigInt.lt CoqBigInt.zero (fs.(ls_constr)) &&
        (bare || Sls.mem fs css)
    in
    (*map every constructor ocurring at the head of the pattern list
      to the list of its args*)
    types_cslist <- 
      let fix populate acc p : errorM (Mls.t (list pattern_c) * list (lsymbol * list pattern_c)) :=
        match pat_node_of p with
        | Pwild => err_ret acc
        | Pvar _ => err_ret acc
        | Pas p _ => populate acc p
        | Por p q =>
          p1 <- (populate acc p);; 
          populate p1 q
        | Papp fs pl =>
          if is_constr fs then
            if Mls.mem _ fs (fst acc) then err_ret acc else
            err_ret (Mls.add fs pl (fst acc), ((fs, pl) :: (snd acc)))
          else throw (ConstructorExpected (fs, ty))
        end
        in
      let populate acc (x: list pattern_c * A) : 
        errorM (Mls.t (list pattern_c) * list (lsymbol * list pattern_c))  := 
        p <- hd (fst x) ;;
        populate acc p in
      foldl_err populate rl (Mls.empty, nil)
    ;;
    let types := fst types_cslist in
    let cslist := snd types_cslist in
    (*dispatch every case to a primitive constructor/wild case*)
    let cases_wilds :=
      let add_case fs ls a cases :=
        Mls.change (fun x =>
          match x with
          | None => Some [(pl, a)]
          | Some rl => Some ((pl, a) :: rl)
          end) fs cases
      in
      let union_cases pl a types cases :=
        let add pl q := pat_wild (pat_ty_of q) :: pl in
        let wild ql := [(fold_left add pl ql, a)] in
        let join _ wl rl := Some (wl ++ rl) in
        Mls.union join (Mls.map wild types) cases
      in
      let rec dispatch (pla: list pattern * A) casewild :=
        let cases := fst casewild in
        let wilds := snd casewild in
        p <- hd (fst pla) ;;
        pl <- tl (fst pla) ;;
        match (pat_node_of p) with
        | Papp fs pl' =>
          (add_case fs (rev_append pl' pl) a cases, wilds)
        | Pwild => (union_cases pl a types cases, (pl, a) :: wilds)
        | Por p1 q1 =>
          d1 <- dispatch (q :: pl, a) (cases, wilds) ;;
          dispatch (p :: pl, a) d1
        | Pas p x =>
          dispatch (p :: pl, mk_let x t a) (cases_wilds)
        | Pvar x => 
          let a := mk_let x t a in
          union_cases pl a types cases 

          (*TODO: do in many parts, add each individually*)

     throw (NonExhaustive nil)
  end. *)
