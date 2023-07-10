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

(*Maybe we want to do this in a context*)

Notation "<{ e }>" := e (at level 0, e custom why3 at level 99) : why3_scope.
Notation "<{{ e }}>" := e (e custom ty at level 99) : why3_scope.
Notation "<{{{ e }}}>" := e (e custom adt at level 99) : why3_scope.
Notation "'<t' e 't>'" := e (e custom tm at level 99) : why3_scope. 
Notation "'<f' e 'f>'" := e (e custom fmla at level 99) : why3_scope. 
Notation "( x )" := x (in custom why3, x at level 99).
Notation "( x )" := x (in custom ty, x at level 99).
Notation "( x )" := x (in custom adt, x at level 99).
Notation "( x )" := x (in custom adtconstr, x at level 99).
Notation "( x )" := x (in custom tylist, x at level 99).
Notation "( x )" := x (in custom mutadt, x at level 99).
Notation "( x )" := x (in custom pat, x at level 99).
Notation "( x )" := x (in custom tm, x at level 99).
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
  also variables*)
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
Definition mut_from_adts (l: list alg_datatype) : mut_adt :=
  (*Need params*)
  match l with
  | nil => mk_mut nil nil eq_refl
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

Notation "()" := nil
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
Notation " | x 'end'" := (cons x nil)
  (in custom tmpatlist at level 90,
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
(*Feq - kind of ugly*)
Notation " [ ty ] t1 = t2 " := (Feq ty t1 t2) 
  (in custom fmla at level 85,
  t1 custom tm,
  t2 custom tm,
  ty custom ty).
Notation " [ ty ] t1 != t2 " := (Fnot(Feq ty t1 t2)) 
(in custom fmla at level 85,
t1 custom tm,
t2 custom tm,
ty custom ty).
(*Basic connectives*)
Notation " f1 /\ f2 " := (Fbinop Tand f1 f2) 
  (in custom fmla at level 85, right associativity,
  f1 custom fmla,
  f2 custom fmla).
Notation " f1 \/ f2 " := (Fbinop Tor f1 f2)
  (in custom fmla at level 85, right associativity,
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
  (in custom fmla at level 80,
  tys custom tylist,
  tms custom tmlist).
Notation "f tms" := (Fpred f nil tms) 
  (in custom fmla at level 80,
  tms custom tmlist).

(*Fmatch*)

(*Once again, have custom grammar for single match
  and list of matches*)
  Notation " p -> t " := (p, t)
  (in custom fmlapat at level 90,
  p custom pat,
  t custom fmla).
(*Pattern matching list*)
Notation " | x 'end'" := (cons x nil)
  (in custom fmlapatlist at level 90,
  x custom fmlapat).
Notation " | x l" := (cons x l)
  (in custom fmlapatlist at level 90,
  x custom fmlapat,
  l custom fmlapatlist,
  right associativity).

(*Fmatch*)
Notation "'match' t : ty 'with' l" := (Fmatch t ty l) 
  (in custom fmla at level 75,
  t custom tm,
  ty custom ty,
  l custom fmlapatlist).

(** Top-level Definitions *)

(*Now that we have terms and formulas, we can define top level
  definitions: recursive functions, inductive predicates, etc*)

(*These are not great - in the examples, we just
  define manually*)

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
  to have mutually recursive inductive predicates*)
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
  And likewise for predicates.
  But again, we don't actually use this *)
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

(*Abstract types*)
Notation "'abstract' 'type' t" :=
  (abs_type t)
  (in custom why3 at level 200).