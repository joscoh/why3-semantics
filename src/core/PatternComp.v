(*Compile pattern matching*)
Require Import TermDefs TermFuncs Monads.
Require CoqBigInt.
Import MonadNotations.
Require Import PatternAux.
(* Require Import TaskDefs (*For hashcons full - TODO: move*). *)

Local Open Scope err_scope.

(*TODO: move*)
Fixpoint rev_map_aux {A B: Type} (f: A -> B) accu l:=
  match l with
  | [] => accu
  | a :: l => rev_map_aux f (f a :: accu) l
  end.

Definition rev_map {A B: Type} (f: A -> B) (l: list A) : list B :=
  rev_map_aux f nil l.

Lemma rev_map_aux_eq {C D: Type} (f: C -> D) accu (l: list C):
  rev_map_aux f accu l = (map f (rev l)) ++ accu.
Proof.
  revert accu.
  induction l as [| h t IH]; simpl; auto; intros accu.
  rewrite IH, map_app. simpl. rewrite <- app_assoc. reflexivity.
Qed.

Lemma rev_map_eq {C D: Type} (f: C -> D) (l: list C):
  rev_map f l = map f (rev l).
Proof.
  unfold rev_map. rewrite rev_map_aux_eq, app_nil_r. reflexivity.
Qed.

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

Local Open Scope errst_scope.

(*TODO: move*)
Notation errst_throw e := (errst_lift2 (throw e)).

Section Dispatch.
(*mk_let can be [t_let_close_simp], which uses [t_subst], which is stateful*)
(*TODO: not stateful, change*)
Context {A: Type} (mk_let: vsymbol -> term_c -> A -> errorM A) (t: term_c) 
  (types: Mls.t (list pattern_c)).

(*For dispatch, we need Equations, since it is not structurally recursive*)
Definition add_case (fs: lsymbol) (pl: list pattern_c) (a: A) cases :=
    Mls.change _ (fun x =>
      match x with
      | None => Some [(pl, a)]
      | Some rl => Some ((pl, a) :: rl)
      end) fs cases.

Definition union_cases pl (a: A) (types : Mls.t (list pattern_c)) cases :
    Mls.t (list (list pattern_c * A)) :=
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
Local Open Scope err_scope.

(*TODO: move lemmas to aux file*)
(*TODO: really termination metric is just size of first elt of list*)
(*NOTE: [pat_node_of] makes this VERY annoying*)
(*TODO: rewrite with Equations, generates LOTS of unhelpful stuff*)
Fixpoint dispatch_aux (pla: list pattern_c * A) 
  (casewild: (Mls.t (list (list pattern_c * A)) * list (list pattern_c * A)))
  (ACC: Acc lt (list_pattern_c_size (fst pla))) :
    errorM (Mls.t (list (list pattern_c * A)) * list (list pattern_c * A)) :=
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
        a <- mk_let x t a ;;
        dispatch_aux (p :: pl, a) (cases,wilds) (Acc_inv ACC (dispatch_aux_bind Hpl Heq))
      | Pvar x => fun Heq =>
        a <- mk_let x t a ;;
        err_ret (union_cases pl a types cases, (pl, a) :: wilds) 
      end eq_refl
    end eq_refl.

Definition dispatch_aux' (pla: list pattern_c * A) 
  (casewild: (Mls.t (list (list pattern_c * A)) * list (list pattern_c * A))) :
    errorM  (Mls.t (list (list pattern_c * A)) * list (list pattern_c * A)) :=
  dispatch_aux pla casewild (Wf_nat.lt_wf _).

Definition dispatch rl := foldr_err (fun x y => dispatch_aux' y x) rl (Mls.empty, nil).

End Dispatch.

(*TODO: remove obviously*)
Unset Guard Checking.
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
  (x <- e ;;
  match x with
  | Succ y => err_ret y
  | NonExh ps => throw (NonExhaustive ps)
  end)%err.


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


(*NOTE: CANNOT use hashcons_full because we need in decl*)
Notation comp_res := (errState (CoqBigInt.t * hashcons_ty ty_c) compile_result).



Definition comp_cases {A: Type} (compile: list term_c -> list (list pattern * A) -> comp_res)
  cases tl ty cs al : comp_res :=
  r <- (errst_lift2 (Mls.find _ cs cases)) ;;
  c <- compile (rev_append al tl) r ;;
  match c with
  | Succ a => errst_ret (Succ a)
  | NonExh pl => 
    (*The catch case*)
    (*We don't prove anything about this so it's fine to have a nested fix*)
    (*TODO: see if OK to use non-hashconsing-version since it's just for exception anyway*)
    let fix cont acc vl pl : errState (CoqBigInt.t * hashcons_ty ty_c) (list pattern_c) := 
    match vl,pl with
      | (_::vl), (p::pl) => 
        cont (p::acc) vl pl
      | [], pl => 
        p1 <- (errst_tup2 (pat_app cs acc ty)) ;;
        errst_ret (p1 :: pl)
      | _, _ => errst_lift2 (assert_false "comp_cases failed")
    end
    in
    c <- (cont nil cs.(ls_args) pl);;
    errst_throw (NonExhaustive c)
  end.

Definition opt_get {A: Type} (o: option A) : errorM A :=
  match o with
  | Some x => err_ret x
  | None => throw (Invalid_argument "option is None")
  end.

(*NOTE: like above, this uses unsafe functions, since we don't really care
  about typechecking the terms we are giving back in the error message*)
Definition comp_wilds (compile: list term_c -> list (list pattern * A) -> comp_res) 
  (types : Mls.t (list pattern_c)) (tl : list term_c) wilds css (ty : ty_c) (_: unit) : comp_res :=
  c <- (compile tl wilds) ;;
  errst_tup2 (match c with
  | Succ x => errst_ret (Succ x)
  | NonExh pl =>
    let find_cs cs : errorHashconsT ty_c unit :=
      if Mls.mem _ cs types then errst_ret tt else
      v <- errst_lift2 (opt_get cs.(ls_value)) ;;
      tm <- ty_match Mtv.empty v ty ;;
      let wild ty := pat_wild (ty_inst_unsafe tm ty) in
      pw <- pat_app cs (List.map wild cs.(ls_args)) ty ;;
      errst_throw (NonExhaustive (pw :: pl))
    in
    (*Cannot iter directly because we cannot include errorM in extmap due to universe
      inconsistency*)
    _ <- iter_errst find_cs (Sls.elements css) ;;
    (* _ <- Sls.iter find_cs css;; *)
    errst_throw (NonExhaustive (pat_wild ty :: pl))
  end).


(*And the full function*)
(*NOTE: we don't give the termination metric or *)

Variable (get_constructors: tysymbol_c -> list lsymbol) 
  (mk_case: term_c -> list (pattern_c * A) -> errorM A)
  (mk_let: vsymbol -> term_c -> A -> errorM A)
  (bare: bool) (simpl_constr: bool).

(*[mk_case] does not use state (t_case_close)*)
Definition comp_full 
  (comp_wilds: unit -> comp_res)
  (comp_cases: lsymbol -> list term_c -> comp_res)
  (types: Mls.t (list pattern_c)) (*tl cases wilds*) (css : Sls.t) 
  cslist t ty (_: unit) :
  comp_res :=
  no_wilds <-
    if bare then
      t <- (errst_lift2 (Mls.choose _ types))  ;;
      let cs := fst t in
      errst_ret (CoqBigInt.eqb (Mls.cardinal _ types) (cs.(ls_constr)))
    else
      errst_ret (Mls.set_submap _ _ css types) ;;
  base <- if (no_wilds : bool) then errst_ret []
    else 
      c <- comp_wilds tt ;;
      match c with
      | NonExh pl => errst_throw (NonExhaustive pl)
      | Succ x =>
          errst_ret [(pat_wild ty,x) ]
      end ;;
  let add (acc : list (pattern_c * A)) (x: lsymbol * list pattern_c) :
     errState (CoqBigInt.t * hashcons_ty ty_c) (list (pattern_c * A)):=
    (let (cs,ql) := x in
    let get_vs q := create_vsymbol (id_fresh1 "x") (pat_ty_of q) in
    vl <- errst_tup1 (errst_lift1 (st_list (rev_map get_vs ql))) ;;
    let pl := rev_map pat_var vl in
    let al := rev_map t_var vl in
    c <- comp_cases cs al ;;
    match c with
    | NonExh pl => errst_throw (NonExhaustive pl)
    | Succ x =>
      p <- errst_tup2 (pat_app cs pl ty) ;;
      errst_ret ((p, x) :: acc)
    end)%errst
  in
  l <- (foldl_errst add cslist base) ;;
  c <- errst_lift2 (mk_case t l) ;;
  errst_ret (Succ c).

(*TODO: Equations is awful for extraction, use wf recursion I think*)
(*TODO: this gives terrible OCaml code*)
Fixpoint compile_aux (tl: list term_c) (rl: list (list pattern_c * A)) { struct rl }
  (*(ACC: Acc lt (pat_mx_size rl))*) : comp_res :=
  match tl, rl with
  | _, [] =>  (* no actions *)
      pl <- errst_list (map (fun t =>
        ty <- errst_lift2 (t_type t) ;;
        errst_ret (pat_wild ty)) tl) ;;
      errst_ret (NonExh pl)
  | [], ((_, a) :: _) => errst_ret (Succ a)
  | t :: tl, rl => (* process the leftmost column *)
    ty <- errst_lift2 (t_type t) ;;
    (* extract the set of constructors *)
    let (bare,css) := match ty_node_of ty with
      | Tyapp ts _ => if bare then (true, Sls.empty) else (false, Sls.of_list (get_constructors ts))
          (* begin try false, Sls.of_list (get_constructors ts)
          with Bare -> true, Sls.empty end *)
      | Tyvar _ => (false, Sls.empty)
      end
    in
    (* if bare, only check fs.ls_constr *)
    let is_constr fs :=
      CoqBigInt.pos fs.(ls_constr) && (bare || Sls.mem fs css)
    in
    (* map every constructor occurring at the head
      * of the pattern list to the list of its args *)
    types_cslist <- errst_lift2 (populate_all is_constr ty rl) ;;
    let types := fst types_cslist in
    let cslist := snd types_cslist in
    (* dispatch every case to a primitive constructor/wild case *)
    (*TODO: need dependent version of bind here*)
    casewild <- errst_lift2 (dispatch mk_let t types rl) ;;
    let cases := fst casewild in
    let wilds := snd casewild in

    (*Need to inline intermediate functions for termination*)

    (*Case 1: wilds*)
    let comp_wilds (_: unit) : comp_res :=
      c <- (compile_aux tl wilds (*(Acc_inv ACC (size_small _ _))*)) ;;
      errst_tup2 (match c with
      | Succ x => errst_ret (Succ x)
      | NonExh pl =>
        let find_cs cs : errorHashconsT ty_c unit :=
          if Mls.mem _ cs types then errst_ret tt else
          v <- errst_lift2 (opt_get cs.(ls_value)) ;;
          tm <- ty_match Mtv.empty v ty ;;
          let wild ty := pat_wild (ty_inst_unsafe tm ty) in
          pw <- pat_app cs (List.map wild cs.(ls_args)) ty ;;
          errst_throw (NonExhaustive (pw :: pl))
        in
        (*Cannot iter directly because we cannot include errorM in extmap due to universe
          inconsistency*)
        _ <- iter_errst find_cs (Sls.elements css) ;;
        (* _ <- Sls.iter find_cs css;; *)
        errst_throw (NonExhaustive (pat_wild ty :: pl))
      end)
    in

    (* how to proceed if [t] is [Tapp(cs,al)] and [cs] is in [cases] *)
    let comp_cases cs al : comp_res := 
      r <- (errst_lift2 (Mls.find _ cs cases)) ;;
      c <- compile_aux (rev_append al tl) r (*(Acc_inv ACC (size_small _ _)*) ;;
      match c with
      | Succ a => errst_ret (Succ a)
      | NonExh pl => 
        (*The catch case*)
        (*We don't prove anything about this so it's fine to have a nested fix*)
        (*TODO: see if OK to use non-hashconsing-version since it's just for exception anyway*)
        let fix cont acc vl pl : errState (CoqBigInt.t * hashcons_ty ty_c) (list pattern_c) := 
        match vl,pl with
          | (_::vl), (p::pl) => 
            cont (p::acc) vl pl
          | [], pl => 
            p1 <- (errst_tup2 (pat_app cs acc ty)) ;;
            errst_ret (p1 :: pl)
          | _, _ => errst_lift2 (assert_false "comp_cases failed")
        end
        in
        c <- (cont nil cs.(ls_args) pl);;
        errst_throw (NonExhaustive c)
      end
    in
    
    (* how to proceed if [t] is not covered by [cases] *)
    (*comp_full above*)

    (* assemble the primitive case statement *)
    if Mls.is_empty _ types then
      comp_wilds tt
    else if simpl_constr then
      match t_node_of t with
      (* | _ when Mls.is_empty types ->
          comp_wilds () *)
      | Tapp cs al => if is_constr cs then
          if Mls.mem _ cs types then comp_cases cs al else 
            comp_wilds tt
          else comp_full comp_wilds comp_cases types css cslist t ty tt
      | _ => comp_full comp_wilds comp_cases types css cslist t ty tt
          
        end
      else comp_full comp_wilds comp_cases types css cslist t ty tt
  end.

Definition compile_aux' (tl: list term_c) (rl: list (list pattern_c * A))
  (*(ACC: Acc lt (pat_mx_size rl))*) : errState (CoqBigInt.t * hashcons_ty ty_c) A :=
  x <- compile_aux tl rl ;;
  match x with
  | Succ x => errst_ret x
  | NonExh pl => errst_throw (NonExhaustive pl)
  end.

End Compile.

Set Guard Checking.

(*The derived functions (NOTE: ours are "aux" because we don't have named arguments)*)
Definition compile_bare_aux {A: Type} mk_case mk_let tl (rl : list (list pattern_c * A)) :=
  let get_constructors _ := nil in
  x <- compile_aux get_constructors mk_case mk_let true true tl rl ;;
  match x with
  | Succ x => errst_ret x
  | NonExh pl => errst_throw (NonExhaustive nil) (*NOTE: not exactly the same, since
    we could have thrown an error before*)
  end.

Definition check_compile_aux get_constructors tl (ps: list (list pattern_c)) :
  errState (CoqBigInt.t * hashcons_ty ty_c) unit :=
  match ps with
  | nil => 
    pl <- (errst_list (map (fun t => 
      ty <- errst_lift2 (t_type t) ;;
      errst_ret (pat_wild ty)) tl)) ;;
    errst_throw (NonExhaustive pl)
  | pl :: _ =>
    let mkt p := 
      i <- errst_lift1 (create_vsymbol (id_fresh1 "_") (pat_ty_of p)) ;;
      errst_ret (t_var i) in
    tl <- if null tl then 
      errst_tup1 (errst_list (map mkt pl)) else errst_ret tl ;;
    let rl := map (fun pl => (pl, t_true)) ps in
    let mk_case := t_case_close in
    let mk_let := t_let_close_simp in (*NOTE: cannot use unit because of proofs*)
    (*let mk_case _ _ := tt and mk_let _ _ _ := tt in (*TODO: change this*)*)
    _ <- compile_aux get_constructors mk_case mk_let false false tl rl;;
    errst_ret tt
  end.

