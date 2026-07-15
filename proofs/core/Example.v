(*Require Import ADTIso.*)
Require Import Typing.
Require Import Denotational.
Require Import Lib_List.
(*Example term: TODO notation*)


(*For now, separate funsym*)

(*
Inductive sEmpty : SProp := .
Inductive sUnit : SProp := stt.
Definition sis_true (b:bool) : SProp := if b then sUnit else sEmpty.

(*TODO: we can use this to get results I think*)
Definition sis_true_eq_true b : sis_true b -> b
  := match b with
     | true => fun _ => eq_refl
     | false => sEmpty_ind _
     end.

Definition is_true_sis {b} (H: is_true b) : sis_true b.
Proof.
  unfold is_true in H.
  symmetry in H.
  destruct H.
  constructor.
Defined.
  

Record fpsym' : Set :=
  { s_name: string;
    s_params: list typevar;
    s_args: list vty;
    (*Well-formed - all type variables appear in params*)
    s_args_wf: sis_true (check_args s_params s_args);
    s_params_nodup: sis_true (nodupb typevar_eq_dec s_params)}.

Record funsym': Set :=
  { f_sym: fpsym';
    f_ret: vty;
    f_is_constr : bool; (*is the funsym a constructor?*)
    f_num_constrs : nat; (*if so, how many constrs in ADT?*)
    f_ret_wf : sis_true ((check_asubset (type_vars f_ret) 
                          (list_to_aset (s_params f_sym)))) }.


Ltac dec_false :=  right; intros C; injection C; intros; subst; contradiction.
Ltac dec_true := left; subst; reflexivity.

Lemma typesym_eq_dec (t1 t2: typesym) : {t1 = t2} + {t1 <> t2}.
Proof.
  destruct t1 as [n1 l1]. destruct t2 as [n2 l2].
  destruct (string_dec n1 n2); [|dec_false].
  destruct (list_eq_dec string_dec l1 l2); [|dec_false].
  dec_true.
Defined.

Eval compute in (typesym_eq_dec ts_unit ts_unit).

Lemma ForallT_hd {A: Type} (P: A -> Type) (x: A) (l: list A):
  ForallT P (x :: l) ->
  P x.
Proof.
  intros Hall. inversion Hall; subst. assumption.
Defined.

Lemma ForallT_tl {A: Type} (P: A -> Type) (x: A) (l: list A):
  ForallT P (x :: l) ->
  ForallT P l.
Proof.
  intros. inversion X; auto.
Defined.

Lemma sort_eq_dec (s1 s2: sort) : {s1 = s2} + {s1 <> s2}.
Proof.
  revert s2.
  induction s1 using sort_rect;
    intros [| | ts1 srts1 ]; auto.
  destruct (typesym_eq_dec ts ts1); [|dec_false].
  assert (Hsrts: {srts = srts1} + {srts <> srts1}).
  {
    revert srts1. induction srts as [| s1 t1 IHs]; intros [|s2 t2]; auto.
    destruct (ForallT_hd _ _ _ IH s2); [| dec_false].
    destruct (IHs (ForallT_tl _ _ _ IH) t2); [dec_true| dec_false].
  }
  destruct Hsrts; [dec_true|dec_false].
Defined.

Lemma vty_eq_dec (v1 v2: vty) : {v1 = v2} + {v1 <> v2}.
Proof.
  revert v2.
  induction v1 using vty_rect; intros [| | x2| ts2 tys2]; auto.
  - destruct (string_dec v x2); [dec_true|dec_false].
  - destruct (typesym_eq_dec tsym ts2); [|dec_false].
    assert (Hl: {vs = tys2} + {vs <> tys2}).
  {
    revert tys2. induction vs as [| s1 t1 IHs]; intros [|s2 t2]; auto.
    destruct (ForallT_hd _ _ _ H s2); [| dec_false].
    destruct (IHs (ForallT_tl _ _ _ H) t2); [dec_true| dec_false].
  }
  destruct Hl; [dec_true|dec_false].
Defined.

Eval compute in (sort_eq_dec (s_cons ts_unit [s_int; s_real]) (s_cons ts_unit [s_int; s_real])).

Eval compute in (vty_eq_dec (vty_cons ts_unit [vty_int; vty_real]) (vty_cons ts_unit [vty_int; vty_real])).

Lemma fpsym_eq_dec (f1 f2: fpsym') : {f1 = f2} + {f1 <> f2}.
Proof.
  destruct f1 as [n1 p1 a1 w1 d1]; destruct f2 as [n2 p2 a2 w2 d2].
  destruct (string_dec n1 n2); [|dec_false].
  destruct (list_eq_dec string_dec p1 p2);[|dec_false].
  destruct (list_eq_dec vty_eq_dec a1 a2);[|dec_false].
  dec_true.
Defined.

Lemma funsym_eq_dec (f1 f2: funsym'): {f1 = f2} + {f1 <> f2}.
Proof.
  Print funsym'.
  destruct f1 as [s1 r1 c1 n1 w1]; destruct f2 as [s2 r2 c2 n2 w2].
  destruct (fpsym_eq_dec s1 s2); [|dec_false].
  destruct (vty_eq_dec r1 r2); [|dec_false].
  destruct (Bool.bool_dec c1 c2); [|dec_false].
  destruct (Nat.eq_dec n1 n2); [|dec_false].
  dec_true.
Defined.

Section ID.

Definition id_name : string := "id".
Definition a_var : string := "a".
Definition id_params : list typevar := [a_var].
Definition id_args: list vty := [vty_var a_var].
Definition id_ret: vty := vty_var a_var.

Definition id_sym' : fpsym' := Build_fpsym' id_name id_params id_args ltac:(constructor) ltac:(constructor).

Definition id_fs' : funsym' := Build_funsym' id_sym' id_ret false 0 ltac:(constructor).

End ID.


Eval compute in (funsym_eq_dec id_fs' id_fs').
*)

(*1: Define polymorphic list*)
(*Section Syms.
Require Import Lib_List.

Definition Nil' := List.Nil.
Definition Cons' := List.Cons.
Definition App' := binop "app" List.list.
Definition unop (name: string) (ty: vty) := funsym_noconstr_noty name [ty] ty.
Definition Reverse' := unop "reverse" List.list.

End Syms.
*)




Section Defs.
  Require Import Notations.
  Require Import Lib_List.
  Local Open Scope why3_scope.
  Import List.

(*For now, copy from Lib_List*)

(*What we want:
 1. polymorphsm
 2. ADT
 3. recursive functions
 4. pattern matching

not yet included:
multi-arg type,
mutual recursion, inductive predicates, abstract types or functions*)
(*Problem: don't have plus yet*)
(*Problem (with mem): have to deal with decidable*)
(*Goal (eventually): prove that rev (l1 ++ l2) = rev l2 ++ rev l1*)
Definition gamma : context :=
  [
    StdLib.rec_fun reverse [l] reverse_body;
    StdLib.rec_fun app [l1; l2] app_body;
    datatype_def list_mut
  ].

Definition rev_app : formula :=
<f forall l1, forall l2, forall x,
      [list] app<a>(reverse<a>(Cons<a>({x}, {l1})), {l2}) =
        app<a>(reverse<a>({l1}), Cons<a>({x}, {l2})) f>.

End Defs.

(*Define the interp we want*)


Inductive Empty :=.

(*We use length-indexed lists (not sigma-typed lists with length proofs) because
  we want to extract elements only*)
(*Inductive vec (A: Set) : nat -> Set :=
| vnil: vec A 0
| vcons: forall (h: A) (n: nat) (t: vec A n), vec A (S n).*)
(*Definition vec (A: Set) : nat -> Set := Vector.t A.*)
  

(*Data for all types in context (to help dep types)*)
(*To make generic, should be iter_either or similar*)
(*Definition ty_ty (ts: typesym) : Set := vec sort (length (ts_args ts)).
  
Definition tys_ty (tys: list typesym) : Set :=
  fold_right (fun x acc => Either (ty_ty x) acc) unit tys.

Eval compute in tys_ty [List.list_ts].

Variant gamma_tys :=
 (*Note: sort here single, should be length-indexed list*)
| ListTy : sort -> gamma_tys
| *)                                  



Fixpoint pdc_aux (s: sort) : Set :=
  match s with
  | s_cons ts srts =>
      if typesym_eqb ts List.list_ts && Nat.eqb (length srts) 1 then
        let r := map pdc_aux srts in
        list (List.nth 0 r Empty)
      else unit
  | s_int => Z
  | s_real => R
  end.

(*Requirement for user: any poly.type inhabited is inhabited*)
Lemma list_inhab: forall {A: Set} (x: A), list A. Proof. intros A x. exact nil. Qed.

Eval compute in (pdc_aux (s_cons List.list_ts [s_int])).
Eval compute in (pdc_aux (s_cons List.list_ts [s_cons List.list_ts [s_int]])).

Set Bullet Behavior "Strict Subproofs".
Lemma pdc_ne s: domain_nonempty pdc_aux s.
Proof.
  constructor.
  induction s using sort_rect.
  - exact 0%Z.
  - exact 0%R.
  - simpl. destruct (_ && _) eqn : Heq; [|exact tt].
    rewrite andb_true_iff in Heq.
    destruct Heq as [Heq Hlen].
    destruct srts as [| s1 srts]; try discriminate.
    simpl. (*Of course we could use nil, but doing it this way so it extends to e.g. Either*)
    apply list_inhab.
    exact (ForallT_hd _ _ _ IH).
Qed.

(*Lemma domain_ne_domain {dom_aux: sort -> Set} {s: sort}:
  domain_nonempty dom_aux s ->
  domain_nonempty (domain dom_aux) s.
Proof.
  intros Hne. inversion Hne.
  constructor.
  destruct s; simpl; auto.
  - exact 0%Z.
  - exact 0%R.
Qed.*)

(*Definition pdc_ne: forall s,  domain_nonempty pdc_aux s := fun s => domain_ne_domain (pdc_ne_aux s).*)

Definition pdc : pi_dom := Build_pi_dom pdc_aux eq_refl eq_refl pdc_ne.

(*A bit silly*)
(*Definition pdc_remove_dom {s: sort} (x: domain pdc_aux s) : pdc_aux s.
Proof.
  destruct s; auto.
Defined.

Definition hlist_remove_dom {srts: list sort} (h: hlist (domain pdc_aux) srts) : hlist pdc_aux srts :=
  hlist_map _ _ (@pdc_remove_dom) srts h.*)

(*Now pfc*)

Definition default (pd: pi_dom) (s: sort):
  dom_aux pd s.
Proof.
  pose proof (domain_ne pd s) as Hne.
  destruct Hne.
  exact x.
Defined.
(*
Lemma length_nil_S {A: Type} {n}: ~ (@length A [] = S n).
Proof.
  intros Hlen; discriminate.
Qed.

Lemma length_cons_inj {A: Type} {x: A} {l: list A} {n: nat}:
  length (x :: l) = S n ->
  length l = n.
Proof.
  intros Hlen. injection Hlen. auto.
Qed.

(*Search Vector.t list.

Search Vector.t 

VectorDef.of_list: forall {A : Type} (l : list A), VectorDef.t A (Datatypes.length l)
 *)

Fixpoint mkvec {A: Set} (l: list A) (n: nat) (Hlen: length l = n) {struct n}:
  vec A n :=
  match n return forall (l: list A), length l = n -> vec A n with
  | O => fun _ _ => Vector.nil
  | S n' => fun l =>
              match l return length l = S n' -> vec A (S n') with
              | nil => fun Hlen => False_rect _ (length_nil_S Hlen)
              | cons x t => fun Hlen => Vector.cons x (mkvec t n' (length_cons_inj Hlen))
              end
  end l Hlen.

From Equations Require Import Equations.
Section AssocListVec.

Context {A B: Set} (eq_dec: forall (x y: A), {x=y} + {x <>y}).

Definition get_assoc_list_vec (n: nat) (keys: vec A n) (vals: vec B n) (x: A) : option B :=
  Vector.rect2 (fun _ _ _ => option B) None
               (fun _ _ _ rec x1 y1 => if eq_dec x x1 then Some y1 else rec) keys vals.
  

(*Fixpoint  get_assoc_list_vec (n: nat) (keys: vec A n) (vals: vec B n) (x: A) : option B :=
  match n return vec A n -> vec B n -> option B with
  | O => fun _ _ => None
  | S n' => fun v1 v2 =>
              match v1 in vec _ (S n') with
              | vcons x1 n1 k =>
                  match v2 in vec _ (S n') with
                  | vcons y1 _ v => if eq_dec x x1 then Some y1 else get_assoc_list_vec n' k v x
                  | vnil => False_rect _ _
                  end
              | vnil => False_rect _ _
              end
  end keys vals
    .
              match v1, v2 with
              | vcons x1 _ k, vcons y1 _ v =>
                  if eq_dec x x1 then Some y1 else get_assoc_list_vec n' k v x
              | _, _ => False_rect _ _
              end
  end.
    
                
    

Equations get_assoc_list_vec (n: nat) (keys: vec A n) (vals: vec B n) (x: A) : option B :=
  get_assoc_list_vec O _ _ x := None;
  get_assoc_list_vec (S n') (vcons _ x1 _ k) (vcons _ y1 _ v) x :=
    if eq_dec x x1 then Some y1 else get_assoc_list_vec n' k v x.*)
End AssocListVec.

Definition ty_subst_fun_vec {A: Set}
  {n: nat} (vs: vec typevar n) (s: vec A n) (d: A) (v: typevar) :=
  match get_assoc_list_vec typevar_eq_dec n vs s v with
  | Some ty => ty
  | None => d
  end.
         
Definition ty_subst_vec {n: nat} (params: vec typevar n) (srts: vec sort n) (t: vty) : sort :=
  v_subst (ty_subst_fun_vec params srts s_int) t.

Print funsym_sigma_ret.
Lemma funsym_sigma_ret_eq (f: funsym) (srts: list sort) (Hlen: length srts = length (s_params f)):
  funsym_sigma_ret f srts = ty_subst_vec (mkvec (s_params f) _ eq_refl) (mkvec srts _ Hlen) (f_ret f).
Proof.
Admitted.

Lemma fpsym_eqb_spec: forall (f1 f2: fpsym),
  reflect (f1 = f2) (fpsym_eqb f1 f2).
Proof.
  intros. unfold fpsym_eqb.
  dec (String.eqb_spec (s_name f1) (s_name f2)).
  dec (list_eqb_spec _ String.eqb_spec (s_params f1) (s_params f2)).
  dec (list_eqb_spec _ vty_eq_spec (s_args f1) (s_args f2)).
  apply ReflectT. apply fpsym_eq; auto.
Defined.

Lemma funsym_eqb_spec: forall (f1 f2: funsym),
  reflect (f1 = f2) (funsym_eqb f1 f2).
Proof.
  intros. unfold funsym_eqb.
  dec (fpsym_eqb_spec (f_sym f1) (f_sym f2)).
  dec (vty_eq_spec (f_ret f1) (f_ret f2)).
  dec (Bool.eqb_spec (f_is_constr f1) (f_is_constr f2)).
  dec (Nat.eqb_spec (f_num_constrs f1) (f_num_constrs f2)).
  apply ReflectT. apply funsym_eq; auto.
Defined.
Search (nat -> bool).

(*Set Definitional UIP.*)
(*Inductive seq {A} (a:A) : A -> SProp :=
  srefl : seq a a.*)

(*Definition eq_true_is_true (b: bool) (H:b = true) : sis_true b.
  rewrite H. constructor.
Defined.
Print eq_true_is_true.
  subst b.
destruct H. constructor.
  := match H in x = true return sis_true _ with eq_refl => stt end.
Definition sUnit_rect (P:sUnit->Type) (v:P stt) (x:sUnit) : P x := v.*)


Record test := mk {test1 : nat; test2: string; test3: sis_true (Nat.odd test1)}.

Lemma test_eq_dec (t1 t2: test) : {t1 = t2} + {t1 <> t2}.
Proof.
  destruct t1 as [n1 s1 o1]; destruct t2 as [n2 s2 o2].
  destruct (Nat.eq_dec n1 n2).
  2: { right; intros C; injection C; intros; subst; contradiction. }
  destruct (string_dec s1 s2).
  2: { right; intros C; injection C; intros; subst; contradiction. }
  left. subst. reflexivity.
Defined.


Lemma opaq1: sis_true (Nat.odd 1).
  constructor.
Qed.
Lemma opaq2: sis_true (Nat.odd 1).
  constructor.
Qed.
Eval compute in (test_eq_dec (mk 1 "6" opaq1) (mk 1 "6" opaq2)).
(*TODO: use sprop and this - no def UIP needed*)




Print sort.

Print typesym.

Eval compute in (list_eq_dec Nat.eq_dec [1;2] [1;2]).

(*It works!*)
(*TODO: use this (provide bridge lemmas for interface), push changes through all (maybe separate branch)
  do we also need eqb? not sure*)


  Record fpsym' : Set :=
  { s_name: string;
    s_params: list typevar;
    s_args: list vty;
    (*Well-formed - all type variables appear in params*)
    s_args_wf: check_args s_params s_args;
    s_params_nodup: nodupb typevar_eq_dec s_params}.


(*Let's try then with *)



(*This is a BAD way to do dec*)
Definition test_eqb (t1 t2: test) : bool :=
  Nat.eqb (test1 t1) (test1 t2) &&
    String.eqb (test2 t1) (test2 t2).

Lemma test_eqb_spec: forall t1 t2, reflect (t1 = t2) (test_eqb t1 t2).
Proof.
  intros [n1 s1 o1] [n2 s2 o2].
  destruct (Nat.eqb_spec 

(*Print UIP_dec.
Print  EqdepFacts.eq_dep_eq__UIP .
Print EqdepFacts.eq_dep_eq_on__UIP_on.
Print EqdepFacts.eq_indd.*)

(*OK, I should do this*)

(*so 1 option is to change this to sprop*)


(*Lemma fpsym_eq_dec (f1 f2: fpsym) : {f1 = f2} + {f1 <> f2}.
Proof.
  Print fpsym.
  destruct f1 as [n1 p1 a1 w1 d1].
  destruct f2 as [n2 p2 a2 w2 d2].
  destruct (string_dec n1 n2).
  2: { right. intro C; injection C.

Eval compute in (string_dec "foo" "foo").

Print string_dec.


*)

Definition funsym_eq_dec (f1 f2: funsym) : {f1 = f2} + {f1 <> f2} :=
  reflect_dec' (funsym_eqb_spec f1 f2).


(*
Inductive seq {A} (a:A) : A -> SProp :=
  srefl : seq a a.
*)
Inductive Squash (A:Type) : SProp := squash : A -> Squash A.

Definition scast' {A B: Set} (x: A) (Heq: seq A B) : B.
  destruct Heq. exact x.
Defined.

Definition eq_to_seq {A: Set} {x y: A} (H: x = y) : seq x y.
Proof.
  subst. constructor.
Defined.

Lemma seq_sym {A: Type} {x y: A}: seq x y -> seq y x.
Proof.
  intros Heq. destruct Heq. constructor.
Qed.

Check eq_rect.
Check seq_rect.
Definition seq_rect' {A: Type} {x: A} (P: A -> Set) {y: A} (Heq: seq x y)  (Px: P x) : P y.
  destruct Heq. exact Px.
Defined.*)

(*Definition remove_dom {s} (x: dom_aux pdc s) : dom_aux pdc s.
Proof.
destruct s; simpl in *; auto.
Defined.*)

(*NOTE: vectors do NOT help here - ultimately have arbitrary sort, oh well*)

(*Definition sym_sigma_args' (sym: fpsym') (s: list sort) := ty_subst_list_s (s_params sym) s (s_args sym).
Definition funsym_sigma_ret' (f: funsym') (s: list sort) := ty_subst_s (s_params (f_sym f)) s (f_ret f).*)

(*Eval compute in Nat.eq_dec (length [s_int]) (length (s_params List.Nil)).*)
Definition pfc_funs (f: funsym) (srts: list sort) (a: arg_list (dom_aux pdc) (sym_sigma_args (f_sym f) srts)) :
  dom_aux pdc (funsym_sigma_ret f srts).
Proof.
  destruct (Nat.eq_dec (length srts) (length (s_params (f_sym f)))) as [Hsrts | Hsrts]; [| exact (default _ _)].
  (*TODO: bad because this will not reduce I think, probably need concrete*)
  destruct (funsym_eq_dec f List.Nil) as [Heqnil | Hneqnil];
    [|destruct (funsym_eq_dec f List.Cons) as [Heqcons | Hneqcons]];
    [| | destruct (funsym_eq_dec f List.reverse) as [Heqrev | Heqrev]];
    [| | | destruct (funsym_eq_dec f List.app) as [Heqapp | Heqapp]].
  - rewrite Heqnil in a, Hsrts |- *.
    destruct srts as [| s1 srts]; [discriminate|].
    destruct srts; [|discriminate].
    exact nil.
 -  rewrite Heqcons in a, Hsrts|- *.
    destruct srts as [| s1 srts]; [discriminate|].
    destruct srts; [|discriminate].
    exact (cons (hlist_hd a) (hlist_hd (hlist_tl a))).
  - rewrite Heqrev in Hsrts, a |- *.
    destruct srts as [| s1 srts]; [discriminate|].
    destruct srts; [|discriminate].
    exact (List.rev (hlist_hd a)).
  - rewrite Heqapp in Hsrts, a |- *.
    destruct srts as [| s1 srts]; [discriminate|].
    destruct srts; [|discriminate].
    exact (Lists.List.app (hlist_hd a) (hlist_hd (hlist_tl a))).
  - (*Default*)
    exact (default _ _).
Defined.

(*Definition pfc_funs' (f: funsym) (srts: list sort) (a: arg_list (domain (dom_aux pdc)) (sym_sigma_args (f_sym f) srts)) :
  domain (dom_aux pdc) (funsym_sigma_ret f srts).
Proof.
  destruct (Nat.eq_dec (length srts) (length (s_params (f_sym f)))) as [Hsrts | Hsrts]; [| exact (default _ _)].
  (*TODO: bad because this will not reduce I think, probably need concrete*)
  destruct (funsym_eq_dec f List.Nil) as [Heqnil | Hneqnil];
    [|destruct (funsym_eq_dec f List.Cons) as [Heqcons | Hneqcons]];
    [| | destruct (funsym_eq_dec f List.reverse) as [Heqrev | Heqrev]];
    [| | | destruct (funsym_eq_dec f List.app) as [Heqapp | Heqapp]].
  - rewrite Heqnil in a, Hsrts |- *.
    destruct srts as [| s1 srts]; [discriminate|].
    destruct srts; [|discriminate].
    exact nil.
 -  rewrite Heqcons in a, Hsrts|- *.
    destruct srts as [| s1 srts]; [discriminate|].
    destruct srts; [|discriminate].
    exact (List.cons (remove_dom (hlist_hd a)) (hlist_hd (hlist_tl a))).
  - rewrite Heqrev in Hsrts, a |- *.
    destruct srts as [| s1 srts]; [discriminate|].
    destruct srts; [|discriminate].
    exact (List.rev (hlist_hd a)).
  - rewrite Heqapp in Hsrts, a |- *.
    destruct srts as [| s1 srts]; [discriminate|].
    destruct srts; [|discriminate].
    exact (Lists.List.app (hlist_hd a) (hlist_hd (hlist_tl a))).
  - (*Default*)
    exact (default _ _).
Defined.*)
(*
Check (pfc_funs List.Cons [s_int]).

Definition test : arg_list (dom_aux pdc) (sym_sigma_args' (f_sym Cons') [s_int]).
  exact (HL_cons pdc_aux s_int _  1%Z (HL_cons pdc_aux (s_cons List.list_ts [s_int]) _ [2%Z; 3%Z] (HL_nil _))).
Defined.
 *) 

Eval compute in (pfc_funs List.Nil [s_int] (HL_nil _)).
(*Eval compute in (pfc_funs Reverse' [s_int] (HL_cons _ _ _ [1%Z; 2%Z] (HL_nil _))).*)
(*Eval compute in arg_list (domain (dom_aux pdc)) (sym_sigma_args' (f_sym Cons') [s_int]).*)
(*E.g.: 1 :: [2;3] = [1;2;3]. Unfortunately, we need to annotate the types*)
Eval compute in (pfc_funs List.Cons [s_int] (HL_cons _ s_int _  1%Z (HL_cons _ (s_cons List.list_ts [s_int]) _ [2%Z; 3%Z] (HL_nil _)))).

Eval compute in (pfc_funs List.reverse [s_int] (HL_cons _ (s_cons List.list_ts [s_int]) _ [1%Z; 2%Z] (HL_nil _))).

(*A more complicated one: lists of lists*)
Definition list_int := (s_cons List.list_ts [s_int]).
Local Open Scope Z_scope.
Eval compute in (pfc_funs List.app [list_int]
                   (HL_cons _ (s_cons List.list_ts [list_int]) _ [[1;2;3]; [4;5;6]]
                            (HL_cons _ (s_cons List.list_ts [list_int]) _ [[7;8;9]] (HL_nil _)))).

Print pi_funpred.

Lemma gamma_valid : valid_context gamma.
assert (Typechecker.check_context gamma) by reflexivity.
destruct (Typechecker.check_context_correct gamma); auto.
discriminate.
Qed.

Fixpoint hlist_eq_prop {A: Type} {f: A -> Type} {l: list A} (h1 h2: hlist f l) : Prop :=
  match l return hlist  f l -> hlist  f l -> Prop with
    | nil => fun _ _ => True
    | x :: t => fun h1 h2 => (hlist_hd h1 = hlist_hd h2) /\ hlist_eq_prop (hlist_tl h1) (hlist_tl h2)
  end h1 h2.

Lemma expand_hlist_eq  {A: Type} {f: A -> Type} {l: list A} (h1 h2: hlist f l):
  h1 = h2 <-> hlist_eq_prop h1 h2.
Proof.
  split.
  - intros Heq; subst.
    induction l as [| x t IH]; [reflexivity|].
    rewrite (hlist_inv h2). simpl. auto.
  - induction l as [| x t IH].
    + rewrite (hlist_nil h1), (hlist_nil h2). auto.
    + rewrite (hlist_inv h1), (hlist_inv h2).
      simpl. intros [Hhd Hprop]. rewrite Hhd. f_equal. auto.
Qed.

(*Tactics for dealing with concrete contexts*)
(*TODO: test on >1 mut*)
Ltac case_mut  :=
    repeat lazymatch goal with
      | m_in: is_true ((proj_sumbool _ _ (mut_adt_dec ?m1 ?m2)) || ?o) |- _ =>
          destruct (mut_adt_dec m1 m2); [subst m1; clear m_in|simpl in m_in]
      | H: is_true false |- _ => discriminate
      | m_in: is_true (mut_in_ctx ?m ?g) |- _ =>
          let m_in' := fresh "m_in" in
          assert (m_in':=m_in); generalize dependent m_in;
          try (unfold g in m_in'); unfold mut_in_ctx in m_in'; simpl in m_in'
    end; intros.

(*TODO: make faster*)
Ltac get_sorts := repeat lazymatch goal with
      | srts_len: length ?srts = ?n |- _ =>
          let s' := fresh "s" in
          let srts' := fresh "srts" in
          let srts_len' := fresh "srts_len" in
          destruct srts as [| s' srts']; first [discriminate | try (injection srts_len; intros srts_len'); 
                                                               simpl in srts_len]
     end.

Ltac case_adt :=
  repeat lazymatch goal with
      | a_in: is_true ((proj_sumbool _ _ (adt_dec ?a1 ?a2)) || ?o) |- _ =>
          destruct (adt_dec a1 a2); [subst a1; clear a_in|simpl in a_in]
      | H: is_true false |- _ => discriminate
      | a_in: is_true (adt_in_mut ?a ?m) |- _ => 
          let a_in' := fresh "a_in" in
          assert (a_in' := a_in); generalize dependent a_in;
          try (unfold m in a_in'); unfold adt_in_mut in a_in'; simpl in a_in'
    end; intros.

Ltac case_constr :=
    repeat lazymatch goal with
      | c_in: is_true ((proj_sumbool _ _ (funsym_eq_dec ?f1 ?f2)) || ?o) |- _ =>
          destruct (funsym_eq_dec f1 f2); [subst f1; clear c_in|simpl in c_in]
      | c_in: is_true (proj_sumbool _ _ (funsym_eq_dec ?f1 ?f2)) |- _ =>
          destruct (funsym_eq_dec f1 f2); [subst f1; clear c_in | discriminate]
      | c_in: is_true (constr_in_adt ?c ?a) |- _ => 
          let c_in' := fresh "c_in" in
          assert (c_in' := c_in); generalize dependent c_in;
          try (unfold a in c_in'); unfold constr_in_adt in c_in'; simpl in c_in'
    end; intros.

Ltac case_indtype :=
  case_mut; get_sorts; case_adt; case_constr.

Ltac prove_adt_inj Heq :=
  unfold ADTSpec.constr_rep in Heq; rewrite !dom_cast_refl in Heq;
  cbv in Heq; apply expand_hlist_eq; simpl; auto; injection Heq; auto.

Ltac prove_adt_disj Heq :=
   unfold ADTSpec.constr_rep in Heq; rewrite !dom_cast_refl in Heq;
   cbv in Heq; discriminate.

Ltac simpl_constr_rep :=
  simpl; unfold ADTSpec.constr_rep; rewrite dom_cast_refl.

(*TODO: copied form ADTInd.v*)
Section Size.

Local Open Scope nat_scope.

Fixpoint sort_size (s: sort) : nat :=
  match s with
  | s_int => 1
  | s_real => 1
  | s_cons _ ts => 1 + sum (map sort_size ts)
  end.

Definition sorts_size (l: list sort) : nat :=
  sum (map sort_size l).

Lemma sort_size_eq (s: sort):
  sort_size s =
  match s with
  | s_int => 1
  | s_real => 1
  | s_cons _ ts => 1 + sorts_size ts
  end.
Proof.
  destruct s; auto.
Qed.

(*The size of a single sort is smaller than 
  the whole list*)
Lemma sorts_size_in (l: list sort) (s: sort):
  In s l ->
  sort_size s <= sorts_size l.
Proof.
  unfold sorts_size.
  induction l; simpl; intros; auto. contradiction.
  destruct_all; subst; try lia.
  specialize (IHl H). lia.
Qed.

Lemma sub_not_whole : forall s l,
    ~ In (s_cons s l) l.
Proof.
  intros. intro C.
  apply sorts_size_in in C.
  rewrite sort_size_eq in C. lia.
Qed.

Lemma s_neq_cons_s s ts srts:
  s = s_cons ts srts ->
  In s srts ->
  False.
Proof.
  intros Hs Hin. subst. apply sub_not_whole in Hin.
  auto.
Qed.

End Size.


Opaque hlist_hd. Opaque hlist_tl.
Lemma pfc_props: adt_interp_props gamma_valid pdc_aux eq_refl pfc_funs.
Proof.
  constructor.
  - intros m a c m_in a_in c_in srts srts_len a1 a2 Heq.
    case_indtype; prove_adt_inj Heq.
  - intros m a c1 c2 m_in a_in c1_in c2_in srts srts_len a1 a2 Hneq Heq.
    case_indtype; try contradiction; prove_adt_disj Heq.
  - intros m a m_in a_in srts srts_len x.
    (*TODO: this definition will be bad, will not compute*)
    case_indtype.
    destruct x as [| h t].
    + apply (existT List.Nil). apply (exist _ (eq_refl, HL_nil _)).
      simpl_constr_rep. reflexivity.
    + apply (existT List.Cons). apply (exist _ (eq_refl, 
            (HL_cons _ s _ h (HL_cons _ (s_cons List.list_ts [s]) _ t (HL_nil _))))).
      simpl_constr_rep. reflexivity.
  - intros m m_in srts srts_len P IH a a_in x.
    case_indtype.
    induction x as [| h t IHx].
    + apply (IH List.list_adt _ _ List.Nil (ltac:(reflexivity)) (HL_nil _)).
      * simpl_constr_rep. reflexivity.
      * simpl. lia. (*bc no args*)
    + apply (IH List.list_adt _ _ List.Cons eq_refl 
               (HL_cons _ s _ h (HL_cons _ (s_cons List.list_ts [s]) _ t (HL_nil _)))).
      * simpl_constr_rep. reflexivity.
      * intros i t' t_in' Heq Hi.
        (*need tactic*)
        cbv in Heq. destruct i as [| i'].
        { (*s not eq by size - TODO*) exfalso; apply s_neq_cons_s in Heq; simpl; auto. }
        destruct i' as [| i']. 2: { destruct i'; discriminate. }
        case_indtype. rewrite dom_cast_refl. clear Heq.
        simpl. (*Really don't like*) Transparent hlist_tl. Transparent hlist_hd. simpl.
        assert (a_in = t_in') by (apply bool_irrelevance). subst. apply IHx.
Defined.


(*TODO: make computable (and hide above)*)

Definition pfc : pi_funpred gamma_valid pdc := Build_pi_funpred gamma_valid pdc 
                                                 pfc_funs (fun _ _ _ => false) pfc_props.

Check rev_app.

Lemma rev_app_typed: formula_typed gamma rev_app.
Proof.
Check Typechecker.typecheck_formula_correct.
assert (Hcheck: Typechecker.typecheck_formula gamma rev_app) by reflexivity.
destruct (Typechecker.typecheck_formula_correct gamma rev_app); auto. discriminate.
Qed.

(*A version of [term_rep/formula_rep] that reduces
 in particular, we don't use the typing proof, instead we do typechecking, returning an option
 if typechecking fails, we later prove equivalence for well-typed terms*)

Section RepReduce.

(*TODO: is this OK, or do we need only certain types, different function, etc? (just need isomoprhic)*)

Context {gamma: context} (gamma_valid: valid_context gamma) (pd: pi_dom) (pf: pi_funpred gamma_valid pd)
  (vt: val_typevar).

Definition term_rep_res : Set := { ty : vty & dom_aux pd (v_subst vt ty) }.

Definition mk_rep_res (ty: vty) (d: dom_aux pd (v_subst vt ty)) : term_rep_res :=
  existT ty d.
  
Definition EVIL {A: Type} : A.
Admitted.

Check match_val_single.
Check option_bind.
Check is_vty_adt.
(*Note that this does NOT make a distinction between ill-typed and well-typed-but-not-matching
  This is OK, since we will only actually apply this on well-typed terms*)
Check sym_sigma_args_map.
Fixpoint match_val_single' (ty: vty)
  (d: dom_aux pd (v_subst vt ty))
  (p: pattern) 
  {struct p} : 
  (*For a pair (x, d), we just need that there is SOME type t such that
    d has type [domain (val v t)], but we don't care what t is.
    We prove later that it matches (snd x)*)
  option (amap vsymbol {s: sort & dom_aux pd s }) :=
  match p with
  | Pvar x => Some (amap_singleton x (existT (v_subst vt ty) d))
  | Pwild => Some amap_empty
  | Por p1 p2 => 
    match match_val_single' ty d p1 with
    | Some v1 => Some v1
    | None => match_val_single' ty d p2
    end
  | Pbind p1 x =>
    option_bind (match_val_single' ty d p1) (fun m1 => 
      Some (amap_set m1 x (existT (v_subst vt ty) d)))
  | Pconstr f params ps =>
      (*case on everything, don't use proofs*)
      option_bind (is_vty_adt gamma ty) (fun x =>
        match x with
          | (m, a, vs) => 
              match vty_eq_dec ty (vty_cons (adt_name a) vs) with
              | right _ => None
              | left Htyeq =>
                match adt_in_mut a m as b return adt_in_mut a m = b -> _ with
                | false => fun _ => None
                | true => fun a_in =>
                  match mut_in_ctx m gamma as b return mut_in_ctx m gamma = b -> _ with
                  | false => fun _ => None
                  | true => fun m_in => 
                    let srts := map (v_subst vt) vs in
                    match sort_eq_dec (v_subst vt ty) (s_cons (adt_name a) srts) with
                    | right _ => None
                    | left valeq =>
                      let adt : ADTSpec.adt_rep (dom_aux pd) a srts := dom_cast _ valeq d in
                      match Nat.eq_dec (length srts) (length (m_params m)) with
                      | right _ => None
                      | left srts_len =>
                        let Hrep := ADTSpec.find_constr_rep gamma_valid _ _ _ (adt_props gamma_valid _ pf)  
                                      m_in a_in srts_len adt in
                         let c : funsym := projT1 Hrep in
                         let args : arg_list (dom_aux pd) (sym_sigma_args c srts) := 
                           snd (proj1_sig (projT2 Hrep)) in
                           (*Start actual match*)
                           match funsym_eq_dec c f with
                           | right _ => None
                           | left Heq =>
                               (*inner match*)
                                 let fix iter_arg_list (tys: list vty)
                                       (a: arg_list (dom_aux pd) (map (v_subst vt) tys))
                                       (pats: list pattern)
                                       {struct pats} :
                                   option (amap vsymbol {s: sort & (dom_aux pd) s }) :=
                                   match tys as t' return arg_list (dom_aux pd) (map (v_subst vt) t') ->
                                                          list pattern ->
                                                          option (amap vsymbol {s: sort & (dom_aux pd) s })
                                   with 
                                   | nil => fun _ pats =>
                                              match pats with
                                              | nil => Some amap_empty
                                              | _ => None
                                              end
                                   | ty :: tl => fun a' ps' =>
                                                   match ps' with 
                                                   | nil => None
                                                   | phd :: ptl => 
                                                     match match_val_single' ty (hlist_hd a') phd with
                                                     | None => None
                                                     | Some l =>
                                                       match iter_arg_list tl (hlist_tl a') ptl with
                                                       | None => None
                                                       | Some l' => Some (amap_union (fun x _ => Some x) l l')
                                                       end
                                                    end
                                                  end
                                   end a pats
                                 in
                                 match constr_in_adt f a as b return constr_in_adt f a = b -> _ with
                                 | false => fun _ => None
                                 | true => fun c_in' =>
                                   match list_eq_dec sort_eq_dec (sym_sigma_args c srts) 
                                           (map (v_subst vt) (ty_subst_list (s_params c) vs (s_args c))) with
                                   | right _ => None
                                   | left Hcast =>                              
                                     iter_arg_list _ (cast_arg_list Hcast args) ps
                                   end
                                 end eq_refl


                           end
                         end
                    end
                  end eq_refl
                end eq_refl
              end
        end


      )
  end.

Definition gen_rep_res (b: bool) : Type :=
  match b with
  | true => term_rep_res
  | false => Prop
  end.

Definition match_rep' v
  (term_rep: val_vars pd vt -> term -> option term_rep_res)
  (formula_rep: val_vars pd vt -> formula -> option Prop)
  (b: bool) ty1 dom_t :=
 fix match_rep (ps: list (pattern * (gen_term b))) : option (gen_rep_res b) := 
    match ps with
    | (p , dat) :: ptl =>
      match match_val_single' ty1 dom_t p with
      | Some l => 
          match b return gen_term b -> option (gen_rep_res b) with
          | true => term_rep (extend_val_with_list pd vt v l)
          | false => formula_rep (extend_val_with_list pd vt v l)
          end dat
      | None => match_rep ptl
      end
    | _ => None
    end .


Definition get_arg_list'
  (vs: list vty) (ts: list term) 
  (reps: term -> option term_rep_res)
  (args: list vty)
  (params: list typevar):
    option (arg_list (dom_aux pd)
    (ty_subst_list_s params
      (map (v_subst vt) vs) args)).
Proof.
  generalize dependent args. induction ts; simpl; intros.
  - destruct args.
    + exact (Some (@HL_nil _ _)).
    + exact None. 
  - destruct args as [| a1 atl].
    + exact None. 
    + destruct (reps a) as [ [ty d] |]; [| exact None].
      destruct (sort_eq_dec (v_subst vt ty) 
        (ty_subst_s params (map (v_subst vt) vs) a1)) as [Htyeq | Hneq]; [| exact None].
      destruct (IHts atl) as [res | ]; [| exact None].
      exact (Some (HL_cons _ _ _ (dom_cast _ Htyeq d) res)).
Defined.
Check term_rep_equation_4.

Definition opt_prop_true (o: option Prop) : Prop :=
  match o with
  | Some P => P
  | None => False
  end.

Equations term_rep' (v: val_vars pd vt) (t: term) : option term_rep_res by struct t := {

term_rep' v (Tconst (ConstInt z)) :=
  Some (mk_rep_res vty_int (int_to_dom pd z));

term_rep' v (Tconst (ConstReal r)) :=
  Some (mk_rep_res vty_real (real_to_dom pd (Q2R r)));

term_rep' v (Tvar x) :=
  Some (mk_rep_res (snd x) (v x));

term_rep' v (Tlet t1 x t2) :=
  let y := term_rep' v t1 in
  match y with
  | Some (existT ty d) =>
      match vty_eq_dec ty (snd x) with
        | left Heq => term_rep' (substi pd vt v x (dom_cast (dom_aux pd) (f_equal (v_subst vt) Heq) d)) t2
        | right _ => None
      end
  | None => None
  end;



term_rep' v (Tfun f vs ts) :=
  match sort_eq_dec (v_subst vt (ty_subst (s_params f) vs (f_ret f)))
                    (ty_subst_s (s_params f) (map (v_subst vt) vs) (f_ret f)) with
  | left Heq =>
      match (get_arg_list' vs ts (term_rep' v) (s_args f) (s_params f)) with
      | Some args => Some (mk_rep_res (ty_subst (s_params f) vs (f_ret f))
                             (dom_cast (dom_aux pd) (eq_sym Heq) (funs gamma_valid pd pf f _ args)))
      | None => None
      end
  | _ => None
  end;

term_rep' v (Tif f t1 t2) :=
  option_bind (formula_rep' v f) (fun b =>
    if all_dec b then term_rep' v t1 else term_rep' v t2
  );

term_rep' v (Tmatch t ty1 xs) := 
  match term_rep' v t with
  | Some (existT ty d) => match_rep' v term_rep' formula_rep' true ty d xs
  | None => None
  end;

term_rep' v (Teps f x) := None (*no denotation for eps*)

}
with formula_rep' (v: val_vars pd vt) (f: formula) : option Prop by struct f :=

  formula_rep' v Ftrue := Some True;
  formula_rep' v Ffalse := Some False;
  formula_rep' v (Fnot f') := 
    option_bind (formula_rep' v f') (fun b => Some (not b));

  formula_rep' v (Flet t x f') :=
  let y := term_rep' v t in
  match y with
  | Some (existT ty d) =>
      match vty_eq_dec ty (snd x) with
        | left Heq => formula_rep' (substi pd vt v x (dom_cast (dom_aux pd) (f_equal (v_subst vt) Heq) d)) f'
        | right _ => None
      end
  | None => None
  end;

  formula_rep' v (Fif f1 f2 f3) :=
  option_bind (formula_rep' v f1) (fun b =>
    if all_dec b then formula_rep' v f2 else formula_rep' v f3
  );

  formula_rep' v (Fpred p vs ts) :=
    option_bind (get_arg_list' vs ts (term_rep' v) (s_args p) (s_params p)) (fun args =>
      Some (is_true (preds gamma_valid pd pf p _ args)));

  
  formula_rep' v (Fquant Tforall x f') :=
    (*TODO decide if all_dec here or in if*)
    Some (forall d, (*This is bad, could give none on some inputs but cant represent that
      because of infinte domain - don't know best way to handle*)
      match formula_rep' (substi pd vt v x d) f' return Prop with
      | Some b => b
      | None => False
      end);
  
  formula_rep' v (Fquant Texists x f') :=
    Some (exists d, 
     match formula_rep' (substi pd vt v x d) f' with
     | Some b => b
     | None => false
     end);

  formula_rep' v (Feq ty t1 t2) := 
    match term_rep' v t1, term_rep' v t2 with
    | Some (existT ty1 d1), Some (existT ty2 d2) =>
        match vty_eq_dec ty1 ty2 with
          | right _ => None
          | left Heq => Some (d1 = dom_cast (dom_aux pd) (f_equal (v_subst vt) (eq_sym Heq)) d2)
        end
    | _, _ => None
    end;

  formula_rep' v (Fmatch t ty1 xs) := 
    match term_rep' v t with
    | Some (existT ty d) => match_rep' v term_rep' formula_rep' false ty d xs
    | None => None
    end;   

  formula_rep' v f := EVIL

.

End RepReduce.





Lemma rev_app_true: opt_prop_true (formula_rep' gamma_valid pdc pfc triv_val_typevar (triv_val_vars _ _) rev_app).
Proof.
  (*TODO: with metaprogramming, wouldnt need this hopefully*)
  Opaque app. Opaque rev.
  cbv.
  Transparent app. Transparent rev. 
  (*The goal we want*)
  intros l1 l2 x.
  simpl.
  rewrite <- !app_assoc. reflexivity.
Qed.

(*TODO (next steps)
  1. need tactic to simplify body
  2. should probably try without all_dec
  3. want metaprogram version, then hopefully can prove eq with reflexivity or cbv
  4. prove equivalence with regular rep*)
