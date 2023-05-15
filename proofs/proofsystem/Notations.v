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
Declare Scope why3_scope.
(*Types*)
(*Definition vty_var' : string -> vty := vty_var.
Coercion vty_var' : string >-> vty.*)
Coercion Pvar : vsymbol >-> pattern.

(*Maybe we want to do this in a context*)

Notation "<{ e }>" := e (at level 0, e custom why3 at level 99) : why3_scope.
Notation "<{{ e }}>" := e (e custom ty at level 99) : why3_scope.
Notation "<{{{ e }}}>" := e (e custom adt at level 99) : why3_scope.
(*For testing, remove maybe*)
(*Notation "'<p' e 'p>'" := e (e custom pat at level 99) : why3_scope.*)
Notation "'<t' e 't>'" := e (e custom tm at level 99) : why3_scope. 
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

(*Parse strings as strings*)
Number Notation Z Z.of_num_int Z.to_num_int : why3_scope.
String Notation string string_of_list_byte list_byte_of_string : why3_scope.


(*Type symbols  (type: str_map typesym -> vty)*)

Notation "ts vs" := (fun (m_ts : str_map typesym) => 
  (vty_cons (get m_ts ts) (map (fun x => x m_ts) vs)))
  (in custom ty at level 0,
    vs custom tylist at level 0).
(*Notation "ts '_'" := (fun (m_ts : str_map typesym) => 
(vty_cons (get m_ts ts) nil))
(in custom ty at level 0).*)
Notation "' x " := (fun (m_ts: str_map typesym) => vty_var x)
  (in custom ty at level 0).
Notation "'int'" := (fun (m_ts : str_map typesym) => vty_int)
  (in custom ty at level 0).


(*List of tys*)
Notation "<>" := (@nil (str_map typesym -> vty)) 
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

(*Algebraic Datatypes*)

(*We will represent a single ADT as 
  (typesym, (str_map typesym -> ne_list funsym))*)

(*First, notation for funsyms when we know the return type
  (function ty -> funsym)*)
Notation "fs '_'" := (fun (ret: vty) (ts_map: str_map typesym) => 
  funsym_noty fs nil ret)
  (in custom adtconstr at level 5).

Notation "fs tys" := (fun (ret: vty) (ts_map: str_map typesym) => 
  funsym_noty fs (map (fun x => x ts_map) tys) ret)
  (in custom adtconstr at level 5,
    tys custom tylist at level 5).



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
Notation "'adt' x" := (datatype_def (build_mut [x]))
  (in custom why3 at level 30,
  x custom adt at level 25).

Notation "'mut' l" := (datatype_def (build_mut l))
  (in custom why3 at level 30,
    l custom mutadt at level 25).

(** Terms and formulas*)

(*Here, we represent terms and formulas
  as (str_map typesym -> str_map funsym -> str_map predsym ->
    str_map vsymbol -> term/formula)*)

(*First, patterns*)
(*Patterns only use the funsym map (for constrs) 
  and typesym map (for types)
  We also take in a type (of the pattern) so that we don't
  need to annotate variables with a type*)

(*TODO: : and :: reserved I think - see*)
(*Pvar*)
Notation "{ x }" :=
  (fun (ty: vty) 
    (m_t: str_map typesym) (m_f: str_map funsym) =>
    Pvar (x, ty))
  (in custom pat at level 0).
  (*Notation " x ::: t " := 
    (fun (m_t: str_map typesym) (m_f: str_map funsym) =>  
      Pvar (x, t m_t)) 
  (in custom pat at level 0,
  t custom ty at level 0).*)
(*Pwild*)
Notation " '_' " := (fun (ty: vty) (m_t: str_map typesym) (m_f: str_map funsym) =>
  Pwild) (in custom pat at level 80).
(*Por*)
Notation " p1 | p2 " := (fun (ty: vty) (m_t: str_map typesym)
  (m_f: str_map funsym) =>
  Por (p1 ty m_t m_f) (p2 ty m_t m_f))
  (in custom pat at level 80,
  p1 custom pat,
  p2 custom pat,
  right associativity).
(*Pbind*)
Notation "p 'as' x" := (fun (ty: vty) (m_t: str_map typesym)
  (m_f: str_map funsym) => Pbind (p ty m_t m_f) (x, ty))
  (in custom pat at level 80,
  p custom pat).
(*Notation "p as x ::: t" := (fun (m_t: str_map typesym) 
  (m_f: str_map funsym) => Pbind (x, t m_t) (p m_t m_f))
  (in custom pat at level 80,
  p custom pat,
  t custom ty).*)
(*List of patterns (for constr)*)
(*TODO: add nil notation*)
(*START*)
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
(*With type args - TODO: put type args in angle brackets?
  Could do this, but maybe parse problems*)
Notation " f tys ps " :=
  (fun (ty: vty) (m_t: str_map typesym)
    (m_f: str_map funsym) =>
    (*Get list of types of args*)
    let c := get m_f f in
    let tys' := map (fun x => x m_t) tys in
    let argtys := map (ty_subst (s_params c) tys') (s_args c) in
    Pconstr c tys'
      (map (fun x => (fst x) (snd x) m_t m_f) (combine ps argtys)))
  (in custom pat at level 80,
    tys custom tylist, 
    ps custom patlist).
(*Without type args*)
Notation " f ps " :=
  (fun (ty: vty) (m_t: str_map typesym)
    (m_f: str_map funsym) =>
    let c := get m_f f in
    let ps' : list (forall (ty: vty) (m_t: str_map typesym)
      (m_f: str_map funsym), pattern) := ps in
    Pconstr c nil
      (map (fun x => (fst x) (snd x) m_t m_f) (combine ps' (s_args c))))
  (in custom pat at level 80,
    ps custom patlist).
    

(*Terms*)

(*Type is: (str_map typesym -> str_map funsym -> str_map predsym ->
    str_map vsymbol -> term) *)

(*Term notations*)
Definition tm_int (z: Z) : term := Tconst (ConstInt z).
Coercion tm_int : Z >-> term.

(*Notation " x " :=
  (fun (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Tconst (ConstInt x))
  (in custom num at level 80).*)

(*ints*)
Notation " { x }" :=
  (fun (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Tconst (ConstInt x))
  (in custom tm at level 80).

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
Notation "f tys tms" := (fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Tfun (get m_f f) (map (fun x => x m_t) tys)
    (map (fun x => x m_t m_f m_p m_v) tms)
  )
  (in custom tm at level 90,
  tys custom tylist,
  tms custom tmlist).
Notation "f tms" := (fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Tfun (get m_f f) nil
    (map (fun x => x m_t m_f m_p m_v) tms)
  )
  (in custom tm at level 90,
  tms custom tmlist).
(*Tvar - for now, angle brackets*)
Notation "'_' x " := (fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Tvar (m_v x))
  (in custom tm at level 60).
(*Tlet*)
Notation "'let' x : ty = t1 'in' t2" := (fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Tlet (t1 m_t m_f m_p m_v)
    (x, ty m_t)
    (*Need to adjust bound vars*)
    (t2 m_t m_f m_p (set m_v x (x, ty m_t))))
  (in custom tm at level 90,
  t1 custom tm,
  ty custom ty,
  t2 custom tm,
  right associativity).
(*Tif*)
Notation "'if' f 'then' t1 'else' t2" :=(fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Tif (f m_t m_f m_p m_v)
    (t1 m_t m_f m_p m_v)
    (t2 m_t m_f m_p m_v))
  (in custom tm at level 90,
    f custom fmla,
    t1 custom tm,
    t2 custom tm).
(*Teps*)
Notation "'eps' x : ty , f" := (fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  (*Again, adjust bound vars*)
  Teps (f m_t m_f m_p (set m_v x (x, ty m_t))) (x, ty m_t) )
  (in custom tm at level 90,
  f custom fmla,
  ty custom ty).
(*Single pattern match for terms*)

(*TODO: move*)
Definition bind_vars (m: str_map vsymbol) (l: list vsymbol) :=
  fold_right (fun x acc => set acc (fst x) x) m l.

Notation " p -> t " :=
  (fun (ty: vty) (m_t: str_map typesym) (m_f: str_map funsym)
    (m_p: str_map predsym) (m_v: str_map vsymbol) =>
    let pat := p ty m_t m_f in
    (*Set all pattern variables*)
    (pat, t m_t m_f m_p (bind_vars m_v (pat_fv pat)))
    )
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
Notation "'match' t : ty 'with' l" := (fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Tmatch (t m_t m_f m_p m_v) (ty m_t)
    (*Variable binding handled above*)
    (map (fun x => x (ty m_t)  m_t m_f m_p m_v) l))
  (in custom tm at level 90,
  t custom tm,
  ty custom ty,
  l custom tmpatlist).

(** Formulas*)

(*This is very similar to terms*)
(*Ftrue*)
Notation "'true'" := (fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Ftrue)
  (in custom fmla at level 0).
(*Ffalse*)
Notation "'false'" := (fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Ffalse)
  (in custom fmla at level 0).
(*Feq - TODO kind of ugly*)
Notation " [ ty ] t1 = t2 " := (fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Feq (ty m_t) (t1 m_t m_f m_p m_v) (t2 m_t m_f m_p m_v))
  (in custom fmla at level 90,
  t1 custom tm,
  t2 custom tm,
  ty custom ty).
(*Basic connectives*)
Notation " f1 && f2 " := (fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Fbinop Tand (f1 m_t m_f m_p m_v) (f2 m_t m_f m_p m_v))
  (in custom fmla at level 90, right associativity,
  f1 custom fmla,
  f2 custom fmla).
Notation " f1 || f2 " := (fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Fbinop Tor (f1 m_t m_f m_p m_v) (f2 m_t m_f m_p m_v))
  (in custom fmla at level 90, right associativity,
  f1 custom fmla,
  f2 custom fmla).
Notation " f1 ==> f2 " := (fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Fbinop Timplies (f1 m_t m_f m_p m_v) (f2 m_t m_f m_p m_v))
  (in custom fmla at level 90, right associativity,
  f1 custom fmla,
  f2 custom fmla).
Notation " f1 <==> f2 " := (fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Fbinop Tiff (f1 m_t m_f m_p m_v) (f2 m_t m_f m_p m_v))
  (in custom fmla at level 90, right associativity,
  f1 custom fmla,
  f2 custom fmla).
(*Quantifiers*)
Notation "'forall' v : t , f" := (fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Fquant Tforall (v, t m_t) (f m_t m_f m_p m_v))
  (in custom fmla at level 90, right associativity,
  t custom ty,
  f custom fmla).
Notation "'exists' v : t , f" := (fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Fquant Texists (v, t m_t) (f m_t m_f m_p m_v))
  (in custom fmla at level 90, right associativity,
  t custom ty,
  f custom fmla).
(*Fif*)
Notation "'if' f1 'then' f2 'else' f3" :=(fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Fif (f1 m_t m_f m_p m_v)
    (f2 m_t m_f m_p m_v)
    (f3 m_t m_f m_p m_v))
  (in custom fmla at level 90,
    f1 custom fmla,
    f2 custom fmla,
    f3 custom fmla).
(*Flet*)
Notation "'let' x : ty = t1 'in' f" := (fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Flet (t1 m_t m_f m_p m_v)
    (x, ty m_t)
    (*Need to adjust bound vars*)
    (f m_t m_f m_p (set m_v x (x, ty m_t))))
  (in custom fmla at level 90,
  t1 custom tm,
  ty custom ty,
  f custom fmla,
  right associativity).
(*Fpred*)
Notation "f tys tms" := (fun 
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
  tms custom tmlist).
(*Fmatch*)

(*Once again, have custom grammar for single match
  and list of matches*)

Notation " p -> f " :=
  (fun (ty: vty) (m_t: str_map typesym) (m_f: str_map funsym)
    (m_p: str_map predsym) (m_v: str_map vsymbol) =>
    let pat := p ty m_t m_f in
    (*Set all pattern variables*)
    (pat, f m_t m_f m_p (bind_vars m_v (pat_fv pat)))
    )
  (in custom fmlapat at level 75,
  p custom pat,
  f custom fmla).
(*Pattern matching list*)
(*Type: list (t -> f -> p -> v -> (pattern * term))*)
Notation " | x 'end'" := (cons x nil)
  (in custom fmlapatlist at level 75,
  (*TODO: level for pattern match? - cant be any term*)
  x custom fmlapat).
Notation " | x l" := (cons x l)
  (in custom fmlapatlist at level 75,
  x custom fmlapat,
  l custom fmlapatlist,
  right associativity).

(*Fmatch*)
Notation "'match' t : ty 'with' l" := (fun 
  (m_t: str_map typesym) (m_f: str_map funsym)
  (m_p: str_map predsym) (m_v: str_map vsymbol) =>
  Fmatch (t m_t m_f m_p m_v) (ty m_t)
    (*Variable binding handled above*)
    (map (fun x => x (ty m_t)  m_t m_f m_p m_v) l))
  (in custom fmla at level 75,
  t custom tm,
  ty custom ty,
  l custom fmlapatlist).



(*Some tests*)
(*Sort of hacky - need this for ints, can't parse strings
  and ints at same scope for some reason*)
Open Scope Z_scope.
Open Scope why3_scope.

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
Abort.

(*Test terms*)
Definition test_tm_int : term :=
  <t 0 t>.

(*TODO: add ints*)
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
  <t if true ==> false then {1} else {0} t>.

Definition test_iff :=
  <t if false <==> false then {1} else {0} t>.

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