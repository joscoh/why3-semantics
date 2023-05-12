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

Definition funsym_noty (name: string) (args: list vty) 
  (ret: vty) : funsym :=
  Build_funsym (Build_fpsym name (find_args (ret :: args)) args
    (find_args_check_args_l _ _ (fun x => in_cons _ x _)) (find_args_nodup _)) 
    ret (find_args_check_args_in _ _ (in_eq _ _)).

Definition predsym_noty (name: string) (args: list vty) : predsym :=
  Build_predsym (Build_fpsym name (find_args args) args
    (find_args_check_args_l _ _ (fun x H => H))
    (find_args_nodup _)).

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

Declare Custom Entry tm.
Declare Scope tm_scope.
(*Types*)
Coercion vty_var : typevar >-> vty.
Coercion Pvar : vsymbol >-> pattern.

(*Maybe we want to do this in a context*)

Notation "<{ e }>" := e (at level 0, e custom tm at level 99) : tm_scope.
Notation "( x )" := x (in custom tm, x at level 99) : tm_scope.
Notation "x" := x (in custom tm at level 0, x constr at level 0).

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
