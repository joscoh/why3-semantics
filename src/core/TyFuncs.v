Require Import ErrorMonad StateMonad TyDefs.

Definition mk_ty (n: ty_node_c) : ty_c :=
  mk_ty_c n Weakhtbl.dummy_tag.

Definition ty_var (n: tvsymbol) : hashcons_st ty_c :=
  Hsty.hashcons (mk_ty (Tyvar n)).
Definition ty_app1 (s: tysymbol_c) (tl: list ty_c) : hashcons_st ty_c :=
  Hsty.hashcons (mk_ty (Tyapp s tl)).

(*Generic Traversal Functions*)
(*The reason we actually do want hash consing, or else
  the counter grows every time we call one of these functions*)
Definition ty_map (fn: ty_c -> ty_c) (t: ty_c) : hashcons_st ty_c :=
  match ty_node_of t with
  | Tyvar _ => hashcons_ret t
  | Tyapp f tl => ty_app1 f (map fn tl)
  end.

Definition ty_fold {A: Type} (fn: A -> ty_c -> A) (acc: A) (t: ty_c) : A :=
  match ty_node_of t with
  | Tyvar _ => acc
  | Tyapp _ tl => List.fold_left fn tl acc
  end.

Definition ty_all (pr: ty_c -> bool) (t: ty_c) : bool :=
  ty_fold (fun acc x => acc && (pr x)) true t.

Definition ty_any (pr: ty_c -> bool) (t: ty_c) : bool :=
  ty_fold (fun acc x => acc || (pr x)) false t.

Definition type_def_map {A: Type} (fn: A -> A) (x: type_def A) : type_def A :=
  match x with
  | Alias t => Alias (fn t)
  | _ => x
  end.

Definition type_def_fold {A B: Type} (fn: A -> B -> A) (acc: A) 
  (t: type_def B) : A :=
  match t with
  | Alias t => fn acc t
  | _ => acc
  end.

Definition is_alias_type_def {A: Type} (t: type_def A) : bool :=
  match t with
  | Alias _ => true
  | _ => false
  end.

Definition is_range_type_def {A: Type} (t: type_def A) : bool :=
  match t with
  | Range _ => true
  | _ => false
  end.

Definition is_float_type_def {A: Type} (t: type_def A) : bool :=
  match t with
  | Float _ => true
  | _ => false
  end.

(*State monad makes some things more annoying
  TODO: see if this is right way to do it*)

(*Need to do it this way because if l is nil, cannot produce
  state necessarily*)
Definition hashcons_list { K A B: Type} 
  (f: list A -> @hashcons_st K B) 
    (l: list (@hashcons_st K A)) : @hashcons_st K B :=
  match l with
  | nil => f nil
  | x :: xs =>
    let st : @hashcons_st K (list A) :=
      (*NOTE: folding right, not left - order matters for
        stateful things*)
      List.fold_right (fun shd sacc =>
        hashcons_bnd (fun hd => 
          hashcons_bnd (fun tl => hashcons_ret (hd :: tl)) sacc
        ) shd
      ) (hashcons_bnd (fun h => hashcons_ret [h]) x) xs
    in hashcons_bnd (fun z => (f z)) st
  end.

(*Traversal Functions on Type Variables*)
Fixpoint ty_v_map (fn: tvsymbol -> ty_c) (t: ty_c) : hashcons_st ty_c :=
  match ty_node_of t with
  | Tyvar v => hashcons_ret (fn v)
  | Tyapp f tl => hashcons_list (ty_app1 f) (map (ty_v_map fn) tl)
  end.

Fixpoint ty_v_fold {A: Type} (fn: A -> tvsymbol -> A) (acc: A)
  (t: ty_c) : A :=
  match ty_node_of t with
  | Tyvar v => fn acc v
  | Tyapp _ tl => List.fold_left (ty_v_fold fn) tl acc
  end.

Definition ty_v_all (pr: tvsymbol -> bool) (t: ty_c) : bool :=
  ty_v_fold (fun acc v => acc && (pr v)) true t.

Definition ty_v_any (pr: tvsymbol -> bool) (t: ty_c) : bool :=
  ty_v_fold (fun acc v => acc || (pr v)) false t.

Fixpoint errorM_list {A: Type} (l: list (errorM A)) : errorM (list A) :=
  match l with
  | nil => ret nil
  | h :: t => bnd (fun hd => bnd (fun htl => ret (hd :: htl)) (errorM_list t)) h
  end.

Fixpoint ty_v_map_err (fn: tvsymbol -> errorM ty_c) (t: ty_c) : 
  errorM (hashcons_st ty_c) :=
  match ty_node_of t with
  | Tyvar v => bnd (fun x => ret (hashcons_ret x)) (fn v)
  | Tyapp f tl => bnd (fun l => ret (hashcons_list (ty_app1 f) l)) 
      (errorM_list (map (ty_v_map_err fn) tl))
  end.

Definition ty_full_inst (m: Mtv.t ty_c) (t: ty_c) : errorM (hashcons_st ty_c):=
  ty_v_map_err (fun v => Mtv.find _ v m) t.

Definition ty_freevars (s: Stv.t) (t: ty_c) : Stv.t :=
  ty_v_fold Stv.add_left s t.

Definition ty_closed (t: ty_c) : bool :=
  ty_v_all (fun _ => false) t.

(*Smart constructors*)

Definition mk_errtype {A: Type} (x: A) : errtype :=
  {| errargs := A; errdata := x|}.

Definition BadTypeArity (t: tysymbol_c * CoqBigInt.t) : errtype := 
  mk_errtype t.

(*TODO: replace before*)
Fixpoint int_length {A: Type} (l: list A) : CoqBigInt.t :=
  match l with
  | nil => CoqBigInt.zero
  | _ :: t => CoqBigInt.succ (int_length t)
  end.

Require Import Ident.

Definition DuplicateTypeVar (t: tvsymbol) : errtype := 
  mk_errtype t.

(*NOTE: fold right, not left*)
Fixpoint fold_errorM {A B: Type} (f: A -> B -> errorM A) (x: A) (l: list B) : errorM A :=
  match l with
  | nil => ret x
  | h :: t => bnd (fun i => f i h) (fold_errorM f x t)
  end.

(*Version that can be used in nested recursion*)
Definition fold_errorM' := fun {A B: Type} (f: A -> B -> errorM A) =>
  fix fold_errorM (l: list B) (x: A) {struct l} :=
  match l with
  | nil => ret x
  | h :: t => bnd (fun i => f i h) (fold_errorM t x)
  end.

(*TODO: replace with this?*)
Fixpoint ty_v_fold_err {A: Type} (fn: A -> tvsymbol -> errorM A) (acc: A)
  (t: ty_c) {struct t} : errorM A :=
  match ty_node_of t with
  | Tyvar v => fn acc v
  | Tyapp _ tl => fold_errorM' (ty_v_fold_err fn) tl acc
  end.

Definition ty_v_all_err (pr: tvsymbol -> errorM bool) (t: ty_c) : 
  errorM bool :=
  ty_v_fold_err (fun acc v => bnd (fun i => ret (i && acc)) (pr v)) true t.

Definition UnboundTypeVar (t: tvsymbol) : errtype := 
  mk_errtype t.

Definition ignore {A: Type} (x: errorM A) : errorM unit :=
  bnd (fun _ => ret tt) x.

Definition null {A: Type} (l: list A) : bool :=
  match l with
  | nil => true
  | _ => false
  end.

Definition IllegalTypeParameters : errtype := mk_errtype tt.
Definition EmptyRange : errtype := mk_errtype tt.
Definition BadFloatSpec : errtype := mk_errtype tt.
(*TODO: monad transformers*)

(*Need EitherT transformer*)

Definition create_tysymbol (name: preid) (args: list tvsymbol) (d: type_def ty_c) (*: tysymbol_c*)
  : errorM (ctr tysymbol_c) :=
  let add (s: Stv.t) (v: tvsymbol) := Stv.add_new (DuplicateTypeVar v) v s in
  let s1 := fold_errorM add Stv.empty args in
  let check (v: tvsymbol) : errorM bool := bnd 
    (fun m => if Stv.mem v m then ret true 
      else throw (UnboundTypeVar v)) s1 in
  let c: errorM unit :=
    match d with
    | NoDef => ret tt
    | Alias d' => 
      ignore (ty_v_all_err check d')
    | Range ir =>
      if negb (null args) then
        throw IllegalTypeParameters
      else if CoqBigInt.lt ir.(Number.ir_upper) ir.(Number.ir_lower)
        then throw EmptyRange
      else ret tt
    | Float fp => if negb (null args) then
        throw IllegalTypeParameters
      else if CoqBigInt.lt fp.(Number.fp_exponent_digits) CoqBigInt.one ||
        CoqBigInt.lt (fp.(Number.fp_significand_digits)) CoqBigInt.one then
        throw BadFloatSpec
      else ret tt
    end in
  bnd (fun _ => ret (mk_ts name args d)) c.

(*Returns map of type variables to elements in list tl*)
Definition ts_match_args {A: Type} (s: tysymbol_c) (tl: list A) : 
  errorM (Mtv.t A) :=
  match fold_right2 Mtv.add (ts_args_of s) tl Mtv.empty with
  | Some m => ret m
  | None => throw (BadTypeArity (s, int_length tl))
  end.

Definition ty_match_args (t: ty_c) : errorM (Mtv.t ty_c) :=
  match ty_node_of t with
  | Tyapp s tl => ts_match_args s tl
  | _ => throw (Invalid_argument "Ty.ty_match_args")
  end.

Definition ty_app (s: tysymbol_c) (tl: list ty_c) : errorM (hashcons_st ty_c) :=
  match ts_def_of s with
  | Alias t => bnd (fun m => ty_full_inst m t) (ts_match_args s tl)
  | _ =>
    if negb (CoqBigInt.eqb (int_length (ts_args_of s)) (int_length tl)) then
      throw (BadTypeArity (s, int_length tl))
    else ret (ty_app1 s tl)
  end.
