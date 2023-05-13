Require Import Syntax.
Require Import Typechecker.
(*We want a nicer way to represent terms and formulas*)

(*First, utilities to prevent us from having to write the type
  variables in a function/predicate symbol*)

Definition find_args (l: list vty) : list typevar :=
  big_union typevar_eq_dec type_vars l.

Lemma find_args_nodup l:
  nodupb typevar_eq_dec (find_args l).
Proof.
  apply (ssrbool.introT (nodup_NoDup _ _)).
  apply big_union_nodup.
Qed.

Lemma find_args_check_args_l l1 l2:
  (forall x, In x l1 -> In x l2) ->
  check_args (find_args l2) l1.
Proof.
  intros.
  apply (ssrbool.introT (check_args_correct _ _)).
  intros.
  unfold find_args, sublist. intros.
  simpl_set. exists x. split; auto.
Qed.

Lemma find_args_check_args_in x l:
  In x l ->
  check_sublist (type_vars x) (find_args l).
Proof.
  intros. apply (ssrbool.introT (check_sublist_correct _ _)).
  unfold sublist. intros. unfold find_args. simpl_set.
  exists x; auto.
Qed.

(*TODO: want to remove proofs from fun, predsym*)
Definition funsym_noty (name: string) (args: list vty) 
  (ret: vty) : funsym :=
  Build_funsym (Build_fpsym name (find_args (ret :: args)) args
    (find_args_check_args_l _ _ (fun x => in_cons _ x _)) (find_args_nodup _)) 
    ret (find_args_check_args_in _ _ (in_eq _ _)).

Definition predsym_noty (name: string) (args: list vty) : predsym :=
  Build_predsym (Build_fpsym name (find_args args) args
    (find_args_check_args_l _ _ (fun x H => H))
    (find_args_nodup _)).


(*ALT APPROACH*)

(*Represent things using functions - from
  map of string -> typesym, map of string -> fun/predsym,
  map of string -> vsymbol*)

(*TODO: change to a real map data structure later;
  for now, just use functions*)
(*We will give default values - not great, see*)
Definition str_map (A: Type) := string -> A.
Definition get {A: Type} (m: str_map A) (s: string) : A :=
  m s.
Definition set {A: Type} (m: str_map A) (s: string) (val: A) : str_map A :=
  fun x => if string_dec s x then val else m x.

Definition def_map {A: Type} (x: A) : str_map A :=
  fun _ => x.

Definition mk_str_map {A: Type} (d: A) (f: A -> string) (l: list A) :=
  fold_right (fun x acc => set acc (f x) x) (def_map d) l.

Inductive mapval : Set :=
  | F_val : funsym -> mapval
  | P_val : predsym -> mapval
  | T_val : typesym -> mapval
  | V_val : vsymbol -> mapval.

(*We will use a single map: string -> option mapval*)


(*Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.Structures.OrdersAlt.
Module String_as_OT := Update_OT String_as_OT. Module Str := Make String_as_OT.
Module String_as_OT' := Update_OT String_as_OT.
Module TypeSymMap := FMapAVL.Make(Update_OT String_as_OT).
Module *)

(*Part 1: Types*)


Declare Custom Entry tm.
Declare Custom Entry ty.
Declare Custom Entry adt.
Declare Custom Entry adtconstr.
Declare Custom Entry tylist.
Declare Custom Entry mutadt.
Declare Scope tm_scope.
(*Types*)
(*Definition vty_var' : string -> vty := vty_var.
Coercion vty_var' : string >-> vty.*)
Coercion Pvar : vsymbol >-> pattern.

(*Maybe we want to do this in a context*)

Notation "<{ e }>" := e (at level 0, e custom tm at level 99) : tm_scope.
Notation "<{{ e }}>" := e (e custom ty at level 99) : tm_scope.
Notation "<{{{ e }}}>" := e (e custom adt at level 99) : tm_scope.
Notation "( x )" := x (in custom tm, x at level 99).
Notation "( x )" := x (in custom ty, x at level 99).
Notation "( x )" := x (in custom adt, x at level 99).
Notation "( x )" := x (in custom adtconstr, x at level 99).
Notation "( x )" := x (in custom tylist, x at level 99).
Notation "( x )" := x (in custom mutadt, x at level 99).
Notation "x" := x (in custom tm at level 0, x constr at level 0).
Notation "x" := x
  (in custom ty at level 0, x constr at level 0).
Notation "x" := x (in custom adt at level 0, x constr at level 0).
Notation "x" := x (in custom adtconstr at level 0, x constr at level 0).
Notation "x" := x (in custom tylist at level 0, x constr at level 0).
Notation "x" := x (in custom mutadt at level 0, x constr at level 0).

(*Type symbols  (type: str_map typesym -> vty)*)

(*For now, require types to be in angle brackets - or else
  things are ambiguous*)
  String Notation string string_of_list_byte list_byte_of_string : tm_scope.

Notation "ts vs" := (fun (m_ts : str_map typesym) => 
  (vty_cons (get m_ts ts) (map (fun x => x m_ts) vs)))
  (in custom ty at level 0,
    vs custom ty at level 0).
Notation "ts '_'" := (fun (m_ts : str_map typesym) => 
(vty_cons (get m_ts ts) nil))
(in custom ty at level 0).
Notation "' x " := (fun (m_ts: str_map typesym) => vty_var x)
  (in custom ty at level 0).
Notation "'int'" := (fun (m_ts : str_map typesym) => vty_int)
  (in custom ty at level 0).

(*Algebraic Datatypes*)

(*First, an alternate notation for lists as:
  [ x1 | x2 | ... | xn ]*)
(*Notation "[ x | y | .. | z ]" :=
  (cons x (cons y .. (cons z nil) ..))
  (format "[ '[' x | '/' y | '/' .. | '/' z ']' ]") : tm_scope.*)

(*We will represent a single ADT as 
  (typesym, (str_map typesym -> ne_list funsym))*)

(*First, notation for funsyms when we know the return type
  (function ty -> funsym)*)
(*List of tys*)
Notation "[ ]" := (@nil (str_map typesym -> vty)) 
  (in custom ty at level 0). 
Notation "[ x ]" := (cons x nil) (in custom ty at level 0,
  x custom ty at level 0).
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..))
  (in custom ty at level 0,
    x custom ty at level 0,
    y custom ty at level 0,
    z custom ty at level 0,
    format "[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]"
  ).

Notation "fs tys" := (fun (ret: vty) (ts_map: str_map typesym) => 
  funsym_noty fs (map (fun x => x ts_map) tys) ret)
  (in custom adtconstr at level 5,
    tys custom ty at level 5).

Notation "fs '_'" := (fun (ret: vty) (ts_map: str_map typesym) => 
funsym_noty fs nil ret)
(in custom adtconstr at level 5).

(*List of constrs*)
Notation "| x | y | .. | z 'end'":=
  (cons x (cons y .. (cons z nil) ..))
  (in custom adt at level 10,
  x custom adtconstr at level 5,
  y custom adtconstr at level 5,
  z custom adtconstr at level 5).

Notation "'type' a vs = l" :=
  (mk_ts a vs, fun (ts_m: str_map typesym) => list_to_ne_list 
    (map (fun x => x (vty_cons (mk_ts a vs) (map vty_var vs)) ts_m) l) 
    eq_refl)
  (in custom adt at level 10,
    (*a custom tm at level 10,
    vs custom tm at level 10,*)
    l custom adt at level 10).

Notation "'type' a = l" :=
  (mk_ts a nil, fun (ts_m: str_map typesym) => list_to_ne_list 
    (map (fun x => x (vty_cons (mk_ts a nil) nil) ts_m) l) 
    eq_refl)
  (in custom adt at level 10,
    (*a custom tm at level 10,*)
    l custom adt at level 10).


(*Lists of ADTs*)
Notation "x 'endmut'" := (cons x nil)
  (in custom mutadt at level 20,
    x custom adt at level 15).
Notation "x 'with' l" :=
  (cons x l)
  (in custom mutadt at level 25,
    x custom adt at level 15,
    l custom mutadt at level 20).

(*TODO: move*)
Definition ts_d: typesym := mk_ts EmptyString nil.

(*Mutual ADTs*)

(*Make a mutual ADT from a list of adts - does not
  guarantee well-typed*)
(*TODO: maybe remove m_nodup from m, put in typing
  will likely have to change some stuff in IndTypes.v*)
Definition mut_from_adts (l: list alg_datatype) : mut_adt :=
  (*Need params*)
  match l with
  | nil => mk_mut nil nil eq_refl (*bad*)
  | (alg_def (mk_ts name params) fs) :: atl => 
    match (nodupb typevar_eq_dec params) as b' return
    nodupb typevar_eq_dec params = b' -> mut_adt with
    | true => fun H => mk_mut l params H
    | false => fun _ => mk_mut nil nil eq_refl
    end eq_refl
  end.

(*TODO: move*)
(*make a mut adt from a list (typesym, str_map typesym -> ne_list funsym)*)
Definition build_mut (l: list (typesym * (str_map typesym -> ne_list funsym))) :
  mut_adt :=
  let names := map fst l in
  (*Need whole list so we can assign correct typesym to all constrs 
    in all ADTs in mutual type*)
  let m := mk_str_map ts_d ts_name names in
  let adts := map (fun t => alg_def (fst t) ((snd t) m)) l in
  mut_from_adts adts.

(*This is not great, but OK for now - have to tag adt as "adt" or 
  "mut t1 with t2 with ... tn endmut"*)
Notation "'adt' x" := (build_mut [x])
  (in custom tm at level 30,
  x custom adt at level 25).

Notation "'mut' l" := (build_mut l)
  (in custom tm at level 30,
    l custom mutadt at level 25).

(*Some tests*)
Open Scope tm_scope.

(*Part 1: ADTs (no mutual)*)

(*Not the most beautiful syntax (need underscores,
  lots of quotes), but much better than raw AST*)

Definition bool_adt := <{{{
  type "bool" =
  | "true" _
  | "false" _
  end
}}}>.

Definition nat_adt := <{{{
  type "Nat" =
  | "O" _
  | "S" [ "Nat" _ ]
  end
}}}>.

Definition list_adt := <{{{
  type "List" ["a"] =
    | "Nil" _
    | "Cons" [ '"a" ; "List" [ '"a" ]]
    end
}}}>.

Definition tree_adt := <{{{
  type "tree" ["a"] =
    | "Leaf" _
    | "Node" ['"a"; "tree" ['"a"]; "tree" ['"a"]]
  end
}}}>.

Definition lam_adt := <{{{
  type "tm" =
  | "Var" [ int ]
  | "Lam" [ int; "tm" _]
  | "App" ["tm" _; "tm" _]
  end
}}}>.

(*Mutually inductive types*)

(*First, just an ADT embedded*)
Definition natmut := <{
  adt
  (type "nat" =
  | "O" _
  | "S" [ "nat" _ ]
  end)
}>.

Definition rosetree := <{
  mut
    type "Tree" ["a"] =
    | "Leaf" _
    | "Node" ['"a"; "Forest" ['"a"]]
    end
  with
    type "Forest" ["a"] =
    | "Nil" _
    | "Cons" ['"a"; "Tree" ['"a"]]
    end
  endmut
}>.

(*Test bool - why we need to remove proofs*)
Require Import IndTypes.
Set Bullet Behavior "Strict Subproofs".
Lemma bool_adt_eq : bool_adt =
(ts_bool, (fun m => bool_constrs)).
Proof.
  unfold bool_adt. simpl.
  f_equal; try reflexivity.
  apply functional_extensionality_dep; intros.
  unfold bool_constrs. simpl.
  unfold funsym_noty. simpl.
  f_equal.
  - unfold fs_true. simpl.
    (*TODO: remove checks from fun, predsym, put in typing*)
    unfold ts_bool.
    assert (find_args_check_args_l [] [vty_cons {| ts_name := "bool"; ts_args := [] |} []]
    (fun x0 : vty =>
     in_cons (vty_cons {| ts_name := "bool"; ts_args := [] |} []) x0 []) = eq_refl)
    by (apply bool_irrelevance); rewrite H; clear H.
    assert (find_args_nodup [vty_cons {| ts_name := "bool"; ts_args := [] |} []] =
    eq_refl) by (apply bool_irrelevance); rewrite H; clear H.
    f_equal. apply bool_irrelevance.
  - f_equal.
    assert (find_args_check_args_l [] [vty_cons {| ts_name := "bool"; ts_args := [] |} []]
    (fun x0 : vty =>
     in_cons (vty_cons {| ts_name := "bool"; ts_args := [] |} []) x0 []) = eq_refl)
    by (apply bool_irrelevance); rewrite H; clear H.
    assert (find_args_nodup [vty_cons {| ts_name := "bool"; ts_args := [] |} []] = eq_refl)
    by (apply bool_irrelevance); rewrite H; clear H.
    unfold fs_false.
    f_equal. apply bool_irrelevance.
Qed.

(*Tests for mut adt*)
Lemma natmut_eq: natmut = 
  mk_mut [alg_def ts_nat (mk_ne [fs_O; fs_S])] nil eq_refl.
Proof.
  unfold natmut. simpl. unfold build_mut. simpl.
  f_equal. f_equal. f_equal; try reflexivity.
  f_equal.
  - unfold fs_O. simpl.
    unfold funsym_noty. simpl.
    unfold ts_nat.
    (*Yup, same thing - need to fix proofs in fun/predsyms*)
Abort.




(*Old stuff - TODO: see what we need*)
(*
(*Utilities to create datatypes*)
Print datatype_def.
Print mut_adt.
Print alg_datatype.
Print typesym.

Definition mk_adt (name: string) (params: list typevar) 
  (l: ne_list funsym) : 
  alg_datatype :=
  alg_def (mk_ts name params) l.

Definition adt_args (a: alg_datatype) : list typevar :=
  match a with
  | alg_def (mk_ts _ params) _ => params
  end.

(*This is not great - should do better*)
(*Do as notation so we can use [eq_refl] - TODO: should
  have better error messages*)
Notation mk_mut l :=
  (match l with
    | nil => mk_mut nil nil eq_refl
    | a :: tl =>
      mk_mut l (adt_args a) eq_refl
  end).

(*Function and predate symbols - TODO make better*)
(*Lists for args*)
Notation " x : t ')'" := ((x, t) :: nil) 
(in custom tm at level 80).
Notation "x : t , tl" := ((x, t) :: tl)
(in custom tm at level 80, right associativity).

(*TODO: Coq will probably have problems with this*)
Notation "name ( args : ret" := (funsym_noty name args ret)
(in custom tm at level 85).
Notation "name ( args" := (predsym_noty name args)
(in custom tm at level 85).

(*Pattern notations*)
Notation " x : t " := (x, t) (in custom tm at level 0).
Notation " '_' " := Pwild (in custom tm at level 80).
Notation " p1 'or' p2 " := (Por p1 p2) (in custom tm at level 70,
  right associativity).
Notation " p as x : t" := (Pbind p (x, t)) (in custom tm
  at level 80).
(*Lists for constrs - TODO?*)
(*TODO: dont want tys - can we infer?*)
Notation "f tys ( ps )" := (Pconstr f tys ps) (in custom tm
at level 80).

(*Lists of patterns for pattern matching*)
(*TODO: level*)
Notation " p -> x end" := ([(p, x)]) (in custom tm at level 80).
Notation " | p -> x | t" := ((p, x) :: t) (in custom tm at level 80,
  right associativity). 

(*Formula notations*)
Notation "'true'" := Ftrue (in custom tm at level 0).
Notation "'false'" := Ffalse (in custom tm at level 0).
Notation "'forall' v : t , f" := (Fquant Tforall (v, t) f) 
  (in custom tm at level 70, left associativity).
Notation "'exists v : t , f" := (Fquant Texists (v, t) f)
  (in custom tm at level 70, left associativity).
Notation "f1 && f2" := (Fbinop Tand f1 f2)
  (in custom tm at level 80, right associativity).
Notation "f1 || f2" := (Fbinop Tor f1 f2)
  (in custom tm at level 81, right associativity).
Notation "f1 ==> f2" := (Fbinop Timplies f1 f2)
  (in custom tm at level 90, right associativity).
Notation "f1 <==> f2" := (Fbinop Tiff f1 f2)
  (in custom tm at level 90).
Notation "'if' f1 'then' f2 'else' f3" := (Fif f1 f2 f3)
  (in custom tm at level 90).
Notation "'let' t1 = x : ty 'in' f1" := (Flet t1 (x, ty) f1)
  (in custom tm at level 85).
(*TODO: this is kind of ugly*)
Notation "t1 = t2 ( ty )" := (Feq ty t1 t2)
  (in custom tm at level 99).
Notation "'match' t : ty 'with' ps" := (Fmatch t ty ps)
  (in custom tm at level 90).
Notation "p tys tms" := (Fpred p tys tms)
  (in custom tm at level 75).

(*Term notations*)
Definition tm_int (z: Z) : term := Tconst (ConstInt z).
Coercion tm_int : Z >-> term.

Notation "f tys tms" := (Tfun f tys tms)
(in custom tm at level 75).
Notation "'let' t1 = x : ty 'in' t2" := (Tlet t1 (x, ty) t2)
(in custom tm at level 85).
Notation "'if' f1 'then' t1 'else' t2" := (Tif f1 t1 t2)
(in custom tm at level 90).
Notation "'eps' x : ty , f" := (Teps f (x, ty))
(in custom tm at level 80).
Notation "'match' t : ty 'with' ps" := (Tmatch t ty ps)
  (in custom tm at level 90).

(*Definitions*)

(*ADTs*)
(*Lists for type arguments*)
(*NOTE: there is no way this is going to work*)
(*TODO: might have to make things a bit uglier than why3, see*)
Notation " f | tl" := (ne_cons f tl) 
(in custom tm at level 70, right associativity).
Notation "f 'end'" := (ne_hd f)
(in custom tm at level 70).
Notation "'type' name args = constrs" :=
  (mk_adt name args constrs)
  (in custom tm at level 70).
(*TODO: has to be better way to do lists*)
Notation "x 'with' y" := (x :: y)
  (in custom tm at level 75).
(*ugly*)
Notation "`endmut'" := (@nil alg_datatype).
Notation "`mut' l" := (mk_mut l)
  (in custom tm at level 80).

(*TODO: functions, predicates, indpreds*)

Open Scope tm_scope.

Definition x : string := "x"%string.
Check <{ forall x : vty_int, true }>.
*)