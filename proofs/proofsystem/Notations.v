Require Import Syntax.
Require Import Typechecker.
Require Import Util.
(*We want a nicer way to represent terms and formulas*)

(*For now, variables and symbols are not represented very nicely,
  we will rely on ad-hoc definitions. But we can at least have
  nicer notations for terms and formulas*)


(*Part 1: Types*)

(*This is probably not the way to do it - kind of seems
  like we are re-inventing a type system*)
Declare Custom Entry why3.
Declare Custom Entry ty.
Declare Custom Entry tylist.
Declare Custom Entry adt.
Declare Custom Entry adtconstr.
Declare Custom Entry mutadt.
Declare Custom Entry pat.
Declare Custom Entry patlist.
Declare Custom Entry tm.
Declare Custom Entry num.
Declare Custom Entry tmlist.
Declare Custom Entry tmpat.
Declare Custom Entry tmpatlist.
Declare Custom Entry fmla.
Declare Custom Entry fmlapat.
Declare Custom Entry fmlapatlist.
Declare Custom Entry indpredelt.
Declare Custom Entry indpredlist.
Declare Custom Entry funargelt.
Declare Custom Entry funarglist.
Declare Custom Entry mutfunelt.
Declare Custom Entry mutfunlist.
Declare Scope why3_scope.
(*Types*)
(*Definition vty_var' : string -> vty := vty_var.
Coercion vty_var' : string >-> vty.*)
(*Coercion Pvar : vsymbol >-> pattern.*)

(*Maybe we want to do this in a context*)

Notation "<{ e }>" := e (at level 0, e custom why3 at level 99) : why3_scope.
Notation "<{{ e }}>" := e (e custom ty at level 99) : why3_scope.
Notation "<{{{ e }}}>" := e (e custom adt at level 99) : why3_scope.
(*For testing, remove maybe*)
(*Notation "'<p' e 'p>'" := e (e custom pat at level 99) : why3_scope.*)
Notation "'<t' e 't>'" := e (e custom tm at level 99) : why3_scope. 
(*TODO: should we just use <{}> for this?*)
Notation "'<f' e 'f>'" := e (e custom fmla at level 99) : why3_scope. 
Notation "( x )" := x (in custom why3, x at level 99).
Notation "( x )" := x (in custom ty, x at level 99).
Notation "( x )" := x (in custom adt, x at level 99).
Notation "( x )" := x (in custom adtconstr, x at level 99).
Notation "( x )" := x (in custom tylist, x at level 99).
Notation "( x )" := x (in custom mutadt, x at level 99).
Notation "( x )" := x (in custom pat, x at level 99).
(*Notation "( x )" := x (in custom patlist, x at level 99).*)
Notation "( x )" := x (in custom tm, x at level 99).
(*Notation "( x )" := x (in custom num, x at level 99).*)
(*Notation "( x )" := x (in custom tmlist, x at level 99).*)
Notation "( x )" := x (in custom tmpat, x at level 99).
Notation "( x )" := x (in custom tmpatlist, x at level 99).
Notation "( x )" := x (in custom fmla, x at level 99).
Notation "( x )" := x (in custom fmlapat, x at level 99).
Notation "( x )" := x (in custom fmlapatlist, x at level 99).
Notation "( x )" := x (in custom indpredelt, x at level 99).
Notation "( x )" := x (in custom indpredlist, x at level 99).
Notation "( x )" := x (in custom funargelt, x at level 99).
Notation "( x )" := x (in custom mutfunelt, x at level 99).
Notation "( x )" := x (in custom mutfunlist, x at level 99).
Notation "x" := x (in custom why3 at level 0, x constr at level 0).
Notation "x" := x
  (in custom ty at level 0, x constr at level 0).
Notation "x" := x (in custom adt at level 0, x constr at level 0).
Notation "x" := x (in custom adtconstr at level 0, x constr at level 0).
Notation "x" := x (in custom tylist at level 0, x constr at level 0).
Notation "x" := x (in custom mutadt at level 0, x constr at level 0).
Notation "x" := x (in custom pat at level 0, x constr at level 0).
Notation "x" := x (in custom patlist at level 0, x constr at level 0).
Notation "x" := x (in custom tm at level 0, x constr at level 0).
(*Notation "x" := x (in custom num at level 0, x ). at level 0).*)
Notation "x" := x (in custom tmlist at level 0, x constr at level 0).
Notation "x" := x (in custom tmpat at level 0, x constr at level 0).
Notation "x" := x (in custom tmpatlist at level 0, x constr at level 0).
Notation "x" := x (in custom fmla at level 0, x constr at level 0).
Notation "x" := x (in custom fmlapat at level 0, x constr at level 0).
Notation "x" := x (in custom fmlapatlist at level 0, x constr at level 0).
Notation "x" := x (in custom indpredelt at level 0, x constr at level 0).
Notation "x" := x (in custom indpredlist at level 0, x constr at level 0).
Notation "x" := x (in custom funargelt at level 0, x constr at level 0).
Notation "x" := x (in custom funarglist at level 0, x constr at level 0).
Notation "x" := x (in custom mutfunelt at level 0, x constr at level 0).
Notation "x" := x (in custom mutfunlist at level 0, x constr at level 0).

(*Parse strings as strings*)
Number Notation Z Z.of_num_int Z.to_num_int : why3_scope.
String Notation string string_of_list_byte list_byte_of_string : why3_scope.

(*Types*)

(*User should define typesym and vty for ADT/type symbols and function for args
  also variables
  (TODO: make better?)*)
Notation "'int'" := vty_int (in custom ty at level 0).
Notation "'real'" := vty_real (in custom ty at level 0).


(*List of tys*)
Notation "<>" := (@nil vty) 
  (in custom tylist at level 0). 
Notation "< x >" := (cons x nil) (in custom tylist at level 0,
  x custom ty at level 0).
Notation "< x ; y ; .. ; z >" := (cons x (cons y .. (cons z nil) ..))
  (in custom tylist at level 0,
    x custom ty at level 0,
    y custom ty at level 0,
    z custom ty at level 0,
    format "< '[' x ; '/' y ; '/' .. ; '/' z ']' >"
  ).

(*ADTs*)
(*Again, user should define funsyms and functions*)



(*List of constrs*)
Notation "| x | y | .. | z 'end'":=
  (cons x (cons y .. (cons z nil) ..))
  (in custom adt at level 10,
  x custom adtconstr at level 5,
  y custom adtconstr at level 5,
  z custom adtconstr at level 5).

(*Construct ADT *)
Notation "'type' a = l" :=
  (alg_def a (list_to_ne_list l eq_refl))
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

(*Mut from single ADT*)
Notation mut_from_adt a :=
  (mk_mut [a] (ts_args (adt_name a)) eq_refl).



(*This is not great, but OK for now - have to tag adt as "adt" or 
  "mut t1 with t2 with ... tn endmut"*)
(*TODO: do we need?*)
(*
Notation "'adt' x" := (fun (m_t: str_map typesym) =>
  datatype_def (build_mut [x] m_t))
  (in custom why3 at level 30,
  x custom adt at level 25).

Notation "'mut' l" := (fun (m_t: str_map typesym) =>
  datatype_def (build_mut l m_t))
  (in custom why3 at level 30,
    l custom mutadt at level 25).*)

(*Patterns*)


(*Pvar*)
Notation "{ x }" :=
    (Pvar x)(in custom pat at level 0).

(*Pwild*)
Notation " '_' " := Pwild (in custom pat at level 80).
(*Por*)
Notation " p1 | p2 " := (Por p1 p2)
  (in custom pat at level 80,
  p1 custom pat,
  p2 custom pat,
  right associativity).
(*Pbind*)
Notation "p 'as' x" := (Pbind p x)
  (in custom pat at level 80,
  p custom pat).

(*List of patterns (for constr)*)

Notation "[ ]" := nil
  (in custom patlist at level 80). 
Notation "( p )" :=
  (cons p nil)
  (in custom patlist at level 80,
    p custom pat).
Notation "( p1 , p2 , .. , pn )" :=
  (cons p1 (cons p2 .. (cons pn nil) ..))
  (in custom patlist at level 80,
  p1 custom pat,
  p2 custom pat,
  pn custom pat).
(*Pconstr*)
Notation " f tys ps " := (Pconstr f tys ps)
  (in custom pat at level 80,
    tys custom tylist, 
    ps custom patlist).
(*Without type args*)
Notation " f ps " := (Pconstr f nil ps)
  (in custom pat at level 80,
    ps custom patlist).
    

(*Terms*)

(*Term notations*)
Definition tm_int (z: Z) : term := Tconst (ConstInt z).
Coercion tm_int : Z >-> term.
Definition tm_real q : term := Tconst (ConstReal q).
Coercion tm_real : QArith_base.Q >-> term.

(*For funsym, user should manually create functions*)

(*TODO: maybe require definitions for these?*)

(*List of terms (for funsym)*)
Notation "()" := nil
  (in custom tmlist at level 80). 
Notation "( t )" :=
  (cons t nil)
  (in custom tmlist at level 80,
    t custom tm).
Notation "( t1 , t2 , .. , tn )" :=
  (cons t1 (cons t2 .. (cons tn nil) ..))
  (in custom tmlist at level 80,
  t1 custom tm,
  t2 custom tm,
  tn custom tm).

(*Tfun*)
Notation "f tys tms" := (Tfun f tys tms) 
  (in custom tm at level 90,
  tys custom tylist,
  tms custom tmlist).
Notation "f tms" := (Tfun f nil tms) 
  (in custom tm at level 90,
  tms custom tmlist).

(*Tvar*)
Notation "{ x }" :=
    (Tvar x)(in custom tm at level 60).

(*Tlet*)
Notation "'let' x = t1 'in' t2" :=
    (Tlet t1 x t2) (in custom tm at level 90,
    t1 custom tm,
    t2 custom tm,
    right associativity).

(*Tif*)
Notation "'if' f 'then' t1 'else' t2" := (Tif f t1 t2)
  (in custom tm at level 90,
    f custom fmla,
    t1 custom tm,
    t2 custom tm).

(*Teps*)
Notation "'eps' x , f" := (Teps f x)
  (in custom tm at level 90,
  f custom fmla).
(*Single pattern match for terms*)

Notation " p -> t " := (p, t)
  (in custom tmpat at level 90,
  p custom pat,
  t custom tm).
(*Pattern matching list*)
(*Type: list (t -> f -> p -> v -> (pattern * term))*)
Notation " | x 'end'" := (cons x nil)
  (in custom tmpatlist at level 90,
  (*TODO: level for pattern match? - cant be any term*)
  x custom tmpat).
Notation " | x l" := (cons x l)
  (in custom tmpatlist at level 90,
  x custom tmpat,
  l custom tmpatlist,
  right associativity).

(*Tmatch*)
Notation "'match' t : ty 'with' l" :=
    (Tmatch t ty l)(in custom tm at level 90,
  t custom tm,
  ty custom ty,
  l custom tmpatlist).

(** Formulas*)

(*This is very similar to terms*)
(*Ftrue*)
Notation "'true'" := Ftrue 
  (in custom fmla at level 0).
(*Ffalse*)
Notation "'false'" := Ffalse 
  (in custom fmla at level 0).
(*Feq - TODO kind of ugly*)
Notation " [ ty ] t1 = t2 " := (Feq ty t1 t2) 
  (in custom fmla at level 90,
  (*TODO: bad*)
  t1 custom tm,
  t2 custom tm,
  ty custom ty).
Notation " [ ty ] t1 != t2 " := (Fnot(Feq ty t1 t2)) 
(in custom fmla at level 90,
(*TODO: bad*)
t1 custom tm,
t2 custom tm,
ty custom ty).
(*Basic connectives*)
Notation " f1 /\ f2 " := (Fbinop Tand f1 f2) 
  (in custom fmla at level 90, right associativity,
  f1 custom fmla,
  f2 custom fmla).
Notation " f1 \/ f2 " := (Fbinop Tor f1 f2)
  (in custom fmla at level 90, right associativity,
  f1 custom fmla,
  f2 custom fmla).
Notation " f1 -> f2 " := (Fbinop Timplies f1 f2)
  (in custom fmla at level 90, right associativity,
  f1 custom fmla,
  f2 custom fmla).
Notation " f1 <-> f2 " := (Fbinop Tiff f1 f2)
  (in custom fmla at level 90, right associativity,
  f1 custom fmla,
  f2 custom fmla).
Notation " 'not' f" := (Fnot f) 
  (in custom fmla at level 90,
  f custom fmla).
(*Quantifiers*)
Notation "'forall' x , f" := (Fquant Tforall x f) 
  (in custom fmla at level 90, right associativity,
  f custom fmla).
(*Not great*)
Notation "'forall' x y , f" := (fforalls [x; y] f)
  (in custom fmla at level 90, right associativity,
    f custom fmla).
Notation "'forall' x y z , f" := (fforalls [x; y; z] f)
(in custom fmla at level 90, right associativity,
  f custom fmla).

Notation "'exists' x , f" := (Fquant Texists x f)
  (in custom fmla at level 90, right associativity,
  f custom fmla).
Notation "'exists' x y , f" := (fexists [x; y] f)
(in custom fmla at level 90, right associativity,
f custom fmla).
Notation "'exists' x y z , f" := (fexists [x; y; z] f)
(in custom fmla at level 90, right associativity,
f custom fmla).
(*Fif*)
Notation "'if' f1 'then' f2 'else' f3" := (Fif f1 f2 f3) 
  (in custom fmla at level 90,
    f1 custom fmla,
    f2 custom fmla,
    f3 custom fmla).
(*Flet*)
Notation "'let' x = t1 'in' f" := (Flet t1 x f) 
  (in custom fmla at level 90,
  t1 custom tm,
  f custom fmla,
  right associativity).
(*Fpred*)
Notation "f tys tms" := (Fpred f tys tms) 
  (in custom fmla at level 90,
  tys custom tylist,
  tms custom tmlist).
Notation "f tms" := (Fpred f nil tms) 
  (in custom fmla at level 90,
  tms custom tmlist).
(*Notation "f tys tms" := (fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Fpred (get m_p f) (map (fun x => x m_t) tys)
    (map (fun x => x m_t m_f m_p m_v) tms)
  )
  (in custom fmla at level 90,
  tys custom tylist,
  tms custom tmlist).
Notation "f tms" := (fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Fpred (get m_p f) nil
    (map (fun x => x m_t m_f m_p m_v) tms)
  )
  (in custom fmla at level 90,
  tms custom tmlist).*)
(*Fmatch*)

(*Once again, have custom grammar for single match
  and list of matches*)
(*TODO: delete fmlapat and fmlapatlist*)
(*
Notation " p -> f " := (p, f)
  (fun (ty: vty) (m_t: str_map typesym) (m_f: str_map funsym)
    (m_p: str_map predsym) (m_v: str_map vsymbol) =>
    let pat := p ty m_t m_f in
    (*Set all pattern variables*)
    (pat, f m_t m_f m_p (set_all m_v fst (pat_fv pat)))
    )
  (in custom fmlapat at level 75,
  p custom pat,
  f custom fmla).
(*Pattern matching list*)
(*Type: list (t -> f -> p -> v -> (pattern * term))*)
Notation " | x 'end'" := (cons x nil)
  (in custom fmlapatlist at level 75,
  x custom fmlapat).
Notation " | x l" := (cons x l)
  (in custom fmlapatlist at level 75,
  x custom fmlapat,
  l custom fmlapatlist,
  right associativity).*)

(*Fmatch*)
Notation "'match' t : ty 'with' l" := (Fmatch t ty l) 
  (in custom fmla at level 75,
  t custom tm,
  ty custom ty,
  l custom tmpatlist).

(** Top-level Definitions *)

(*Now that we have terms and formulas, we can define top level
  definitions: recursive functions, inductive predicates, etc*)

(*Inductive predicates*)

(*List of (string * formula)*)
Notation "s : f" := (s, f)
  (in custom indpredelt at level 90,
  f custom fmla at level 99).
Notation " | x 'end'" := (cons x nil)
  (in custom indpredlist at level 90,
  x custom indpredelt).
Notation " | x l" := (cons x l)
  (in custom indpredlist at level 90,
  x custom indpredelt,
  l custom indpredlist,
  right associativity).

(*NOTE: for now, our notations do not allow
  mutually inductive predicates. Our semantics handle
  this of course, but it would be very difficult to
  make this reasonably nice, and the stdlib doesn't seem
  to have mutually recursive inductive predicates
  (TODO: maybe add, can do similar to functions)*)
Notation "'inductive' p = l" := (inductive_def [ind_def p l]) 
  (in custom why3 at level 200,
  l custom indpredlist at level 99).

(*Recursive functions and predicates*)

(*NOTE: we break compatibility (loosely defined) with
  why3 here:
  we use "abstract function foo" to define an abstract function
  and "function foo = ..." to define a concrete one.
  Here we allow mutually recursive functions with the syntax
  "mutfun (function foo = ... with function bar = ..., etc) endmutfun"
  And likewise for predicates *)
Notation "'abstract' 'function' foo" :=
  (abs_fun foo)
  (in custom why3 at level 200).

(*Arg list for function/predicate*)
Notation "x : t" := (x, t)
  (in custom funargelt at level 80,
  t custom ty).

Notation "()" := nil
  (in custom funarglist at level 80). 
Notation "( t )" :=
  (cons t nil)
  (in custom funarglist at level 80,
    t custom funargelt).
Notation "( t1 , t2 , .. , tn )" :=
  (cons t1 (cons t2 .. (cons tn nil) ..))
  (in custom funarglist at level 80,
  t1 custom funargelt,
  t2 custom funargelt,
  tn custom funargelt).

Notation "'function' foo args = body" :=
  (recursive_def [fun_def foo args body])
  (in custom why3 at level 200,
  args custom funarglist,
  body custom tm).

(*Predicates*)

Notation "'abstract' 'predicate' foo" :=
  (abs_pred foo)
  (in custom why3 at level 200).

Notation "'predicate' foo args = body" :=
  (recursive_def [pred_def foo args body])
  (in custom why3 at level 200,
  args custom funarglist,
  body custom fmla).

(*Mutually recursive functions and predicates*)
(*Not great because of duplication*)
(*
Notation "x 'endmutfun'" := (cons x nil)
  (in custom mutfunlist at level 25,
    x custom mutfunelt at level 15).
Notation "x 'with' l" :=
  (cons x l)
  (in custom mutfunlist at level 25,
    right associativity,
    x custom mutfunelt at level 15,
    l custom mutfunlist at level 25).

(*Is there a way to not duplicate? Not sure*)
(*funpred_def NOT recursive_def*)
(*We give the function symbol because using the other
  maps, because we will modify these maps using this funsym*)
Notation "'function' foo args : ret = body" :=
  (fun
  (m_t: str_map typesym) =>
  let inputs := map (fun x => x m_t) args in
  let f := (funsym_noty foo (map snd inputs) (ret m_t)) in
  (Left funsym predsym f, fun
  (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
    fun_def f inputs
      (*Need to adjust m_f to bind the new symbol*)
      (body m_t (set m_f foo f) m_p 
        (set_all m_v fst inputs))
    ))
  (in custom mutfunelt at level 15,
  args custom funarglist,
  ret custom ty,
  body custom tm).


Notation "'predicate' foo args = body" :=
  (fun
  (m_t: str_map typesym) =>
  let inputs := map (fun x => x m_t) args in
  let p := (predsym_noty foo (map snd inputs)) in
  (Right funsym predsym p, fun
  (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
    pred_def 
      p
      inputs
      (body m_t m_f (set m_p foo p) 
        (set_all m_v fst inputs))
    ))
  (in custom mutfunelt at level 15,
  args custom funarglist,
  body custom fmla).

(*TODO: move*)
Definition split_either {A B: Set} (l: list (Either A B)) : 
  (list A * list B) :=
  fold_right (fun x acc =>
    let t1 := fst acc in
    let t2 := snd acc in
    match x with
    | Left y => (y :: t1, t2)
    | Right y => (t1, y :: t2)
    end) (nil, nil) l.

Notation "'mutfun' l" := (fun
(m_t: str_map typesym) (m_f: str_map funsym)
(m_p: str_map predsym) (m_v: str_map vsymbol) =>
  (*Get funs and preds*)
  let l': list (Either funsym predsym *
    (str_map funsym -> str_map predsym -> str_map vsymbol ->
    funpred_def))
  := map (fun x => x m_t) l in
  let (funs, preds) :=  split_either (map fst l') in
  (*New fun and pred maps*)
  let m_f' := set_all m_f s_name funs in
  let m_p' := set_all m_p s_name preds in
  recursive_def 
    (map (fun x => x m_f' m_p' m_v) (map snd l'))
  )
  (in custom why3 at level 200,
  l custom mutfunlist).*)

(*Abstract types*)
(*TODO: should unify notation of these lists to be
  in angle brackets (new grammar?)*)
Notation "'abstract' 'type' t" :=
  (abs_type t)
  (in custom why3 at level 200).



(*Some tests*)
(*Sort of hacky - need this for ints, can't parse strings
  and ints at same scope for some reason*)
Open Scope Z_scope.
Open Scope why3_scope.

(*

(*Part 1: ADTs (no mutual)*)

(*Not the most beautiful syntax (need underscores,
  lots of quotes), but much better than raw AST*)
Definition bool_adt := <{{{
  type "bool" =
  | "true"_
  | "false"_
  end
}}}>.

Definition nat_adt := <{{{
  type "Nat" =
  | "O" <>
  | "S" < "Nat" <> >
  end
}}}>.

Definition list_adt := <{{{
  type "List" ["a"] =
    | "Nil" <>
    | "Cons" < '"a" ; "List" <'"a" >>
    end
}}}>.

Definition tree_adt := <{{{
  type "tree" ["a"] =
    | "Leaf" <>
    | "Node" <'"a"; "tree" <'"a">; "tree"<'"a">>
  end
}}}>.

Definition lam_adt := <{{{
  type "tm" =
  | "Var"<int>
  | "Lam"<int; "tm"<>>
  | "App"<"tm"<>; "tm"<>>
  end
}}}>.

(*Mutually inductive types*)

(*First, just an ADT embedded*)
Definition natmut := <{
  adt
  (type "nat" =
  | "O"<>
  | "S" <"nat"<>>
  end)
}>.

Definition rosetree := <{
  mut
    type "Tree" ["a"] =
    | "Leaf" <>
    | "Node" <'"a"; "Forest"<'"a">>
    end
  with
    type "Forest" ["a"] =
    | "Nil" <>
    | "Cons"<'"a"; "Tree"<'"a">>
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
(*
(*Tests for mut adt*)
Lemma natmut_eq: natmut = 
  datatype_def (mk_mut [alg_def ts_nat (mk_ne [fs_O; fs_S])] nil eq_refl).
Proof.
  unfold natmut. simpl. unfold build_mut. simpl.
  f_equal. f_equal. f_equal. f_equal; try reflexivity.
  f_equal.
  - unfold fs_O. simpl.
    unfold funsym_noty. simpl.
    unfold ts_nat.
    (*Yup, same thing - need to fix proofs in fun/predsyms*)
    admit.
  - unfold fs_S, funsym_noty. simpl.
    unfold Notations.get, set.
    simpl.
    unfold ts_nat.
Abort.*)

(*Test terms*)
Definition test_tm_int : term :=
  <t 0 t>.

(*x*)
Definition test_tm_var := 
  <t _"x" t>.

(*x + y*)
Definition test_tm_plus :=
  <t "add" (_"x", _"y") t>.

(*function with no args*)
Definition test_noop :=
  <t "foo"() t>.

(*Function with 1 arg*)
Definition test_negb :=
  <t "negb"(_"b") t>.

(*let x = y in x + x*)
Definition test_let :=
  <t let "x" : int = _"y" in "add"<int> (_"x", {0}) t>.

Definition test_tif  :=
  <t if true then {0} else {1} t>.

Definition test_teps := 
  <t eps "x" : int , true t>.

(*test pattern match - no semantic meaning for now,
  obviously this match makes no sense*)
(*This shows: we can have constructors with and without
  type arguments - dont think we can have without both*)
Definition test_match :=
  <t
  match _"x" : "List" <int> with
  (*Pvar*)
  | {"x"} -> _"z"
  (*Pwild*)
  | _ -> _"w"
  (*Constr with no args*)
  | "Nil" [] -> _"y"
  (*Constr with args, no polymorphism*)
  | "Cons" ({"h"} , {"t"}) -> _"z"
  (*Constr with args and poly*)
  | "Foo" < int > ( {"X"} ) -> _"w"
  (*Pbind*)
  | "Cons" ({"h"}, {"x"}) as "y" -> _"u"
  (*Por*)
  | "Nil" [] | "Foo" < int > [] -> _"x"
  end
  t>. 

(*Test formulas - don't have formal way to write formulas
  yet, so put in trivial if*)

Definition test_true :=
  <t if true then {1} else {0} t>.

Definition test_false :=
  <t if false then {1} else {0} t>.

Definition test_and :=
  <t if true && false then {1} else {0} t>.

Definition test_or :=
  <t if false || true then {4} else _"x" t>.

Definition test_implies :=
  <t if true -> false then {1} else {0} t>.

Definition test_iff :=
  <t if false <-> false then {1} else {0} t>.

Definition test_forall :=
  <t if forall "x" : int , [int] _"x" = {1} then {1} else {0} t>.

Definition test_exists :=
  <t if exists "x" : int, "foo"(_"x") then {1} else {0} t>.

Definition test_feq :=
  <t if [int] {1} = {0} then {1} else {0} t>.

(*TODO: this is a good test case to prove*)
Definition test_flet :=
  <t if let "x" : int = {0} in [int] _"x" = {0} then {1} else {0} t>.

Definition test_fif :=
  <t if (if true then true else false) then {1} else {0} t>.

Definition test_fmatch :=
  <t if
    (match _"x" : "List" <int> with
    (*Pvar*)
    | {"x"} -> true
    (*Pwild*)
    | _ -> false
    (*Constr with no args*)
    | "Nil" [] -> [int] {1} = {0}
    (*Constr with args, no polymorphism*)
    | "Cons" ({"h"} , {"t"}) -> false
    (*Constr with args and poly*)
    | "Foo" < int > ( {"X"} ) -> true && false
    (*Pbind*)
    | "Cons" ({"h"}, {"x"}) as "y" -> 
      [int] (if true then {1} else {0}) = {1}
    (*Por*)
    | "Nil" [] | "Foo" < int > [] -> true
    end) then {1} else {0} t>.

Definition foo : string := "foo".
Definition test_fpred :=
  <t if foo({1}) then {1} else {0} t>.


(*Inductive Predicates*)
Definition distinct : string := "distinct".
Definition Nil : string := "Nil".
Definition Cons : string := "Cons".
Definition List : string := "List".
Definition mem : string := "mem".
Definition a : string := "a".
Definition x : string := "x".
Definition l : string := "l".
(*From why3 list*)
(*This is not horrible. Would be nice to get rid of
  underscores before vars, but otherwise OK*)
Definition test_indpred :=
  <{
    inductive distinct <List<'a>> =
    | "distinct_zero" : distinct(Nil <List<'a>> [])
    | "distinct_one" : forall x : 'a , 
        distinct (Cons(_ x, Nil()))
    | "distinct_many" : forall x: 'a,
      forall l: List<'a>,
      not (mem(_ x, _ l)) ->
      distinct(_ l) ->
      distinct(Cons(_ x, _ l))
    end
  }>.

(*Abstract functions*)
Definition bar : string := "bar".
Definition test_abs_fun :=
  <{
    abstract function bar<'a; int> : int
  }>.

(*Defined functions*)
Definition andb : string := "andb".
Definition y : string := "y".
Definition Bool : string := "Bool".
Definition Ttrue : string := "True".
Definition Ffalse: string := "False".

Definition test_andb := <{
  function andb (x : Bool<>, y : Bool<>) : Bool<> =
  match _ x : Bool<> with
  | Ttrue [] -> _ y
  | Ffalse [] -> Ffalse()
  end
}>.

(*Recursive functions*)
Definition length : string := "length".
Definition r : string := "r".
Definition plus : string := "plus".

Definition test_length := <{
  function length (l: List<'a>) : int =
  match _ l : List<'a> with
  | Nil<'a> [] -> {0}
  | Cons<'a> (_, {r}) -> plus({1}, length(_ r))
  end
}>.

(*Abstract predicate*)
Definition test_abs_pred := <{
  abstract predicate bar<'a; int>
}>.

(*Concrete (non-recursive) predicate*)
Definition is_nil : string := "is_nil".
Definition test_is_nil := <{
  predicate is_nil (l: List<'a>) =
  match _ l : List<'a> with
  | Nil<'a> [] -> Ttrue()
  | Cons<'a>(_, _) -> Ffalse()
  end
}>.

(*Recursive predicate*)
Definition test_mem := <{
  predicate mem (x: 'a, l: List<'a>) =
  match _ l : List<'a> with
  | Nil <'a> [] -> Ffalse()
  | Cons <'a> ({y}, {r}) -> ([ 'a ] _ x = _ y) || mem(_ x, _ r)
  end
}>.

(*Mutually recursive functions and predicates*)
Definition size_forest : string := "size_forest".
Definition size_tree : string := "size_tree".
Definition f : string := "f".
Definition t : string := "t".
Definition Forest : string := "Forest".
Definition Tree : string := "Tree".
Definition Node : string := "Node".
(*From why3 stdlib Tree*)
Definition test_size_forest := <{
  mutfun 
  function size_forest(f : Forest<'a>) : int =
  match _ f : Forest<'a> with
  | Nil <'a> [] -> {0}
  | Cons <'a>({t}, {f}) -> plus (size_tree(_ t), size_forest(_ f))
  end
  with
  function size_tree(t: Tree<'a>) : int =
  match _ t : Tree<'a> with
  | Node<'a>(_, {f}) -> plus ({1}, size_forest(_ f))
  end
  endmutfun
}>.

(*An example that mixes functions and predicates*)
Definition Foo : string := "Foo".
Definition Bar : string := "Bar".

Definition test_mutfunpred := <{
  mutfun
  function Foo (l: List<'a>) : int =
  match _ l: List<'a> with
  | Nil<'a> [] -> {1}
  | Cons<'a>(_, {t}) -> if Bar(_ t) then {1} else (Foo(_ t))
  end
  with
  predicate Bar (l: List<'a>) =
  match _ l: List<'a> with
  | Nil<'a>[] -> Ttrue()
  | Cons<'a>(_, {t}) -> [int] (Foo(_ t)) = {1}
  end
  endmutfun
}>.

(*Abstract type*)
Definition abs_type := <{
  abstract type Foo [a]
}>.

(*TODO: should make syntax more consistent, maybe
  put all vars in curly braces (kind of ugly but better
  than underscores)*)
*)