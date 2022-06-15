
Require Import Coq.ZArith.BinInt.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Require Import Util.

(*TODO: where do we need this? See. Also should we use Interval package?*)
Record int_range := mk_intrng { ir_lower : Z; ir_upper: Z}.

(* TODO: should really be machine-length integers *)
Record float_format := mk_floatfmt {
    fp_exponent_digits : Z;
    fp_significand_digits : Z
}.

(*TODO: do we need attributes or tag?*)
(* Need tag for comparison (use as key in map) *)
Record ident : Type := mk_ident {
    id_string : string;
    id_tag : Z (*We just use the concrete type, not hashtable tag*)
}.

Definition ident_eq_dec: forall (i1 i2: ident), {i1 = i2} + {i1 <> i2}.
Proof.
    solve_eq_dec.
Defined.

(*In the real implementation, there is a mutable counter for the tags of
    each ident that is registered (in id_register in ident.ml). Instead,
    we assume the existence of an injective string -> Z function (which
    does exist and we may write it later), and just use the fact that the
    string names are unique.*)
Section MakeTag.

Axiom string_to_Z : string -> Z.
Axiom string_to_Z_inj: forall s1 s2, string_to_Z s1 = string_to_Z s2 -> s1 = s2.
    
End MakeTag.

Definition mk_id (s: string) : ident := mk_ident s (string_to_Z s).
    
(*Types*)

Record tvsymbol : Type :=
    mk_tvsym { tv_name : ident }.

Definition tvsymbol_eq_dec: forall (t1 t2: tvsymbol), {t1 = t2} + {t1 <> t2}.
Proof.
    solve_eq_dec.
Defined.

(*Simplified version of types with no mutual recursion.
  We do not include Range/Float because they are not used
  in the frama-C translation.
  Frama-C does ues Alias, which we represent with an option type.*)

Inductive ty : Type :=
    | Tyvar : (ident * list tvsymbol * option ty) -> ty
    | Tyapp : (ident * list tvsymbol * option ty) -> list ty -> ty
    | Alias : ty -> ty.

Notation tysymbol := (ident * list tvsymbol * option ty)%type.

(*A more faithful (but annoying to use) version would be: 

Inductive type_def (A: Type) : Type :=
    | NoDef : type_def A
    | Alias : A -> type_def A
    | Range : int_range -> type_def A
    | Float : float_format -> type_def A.

Inductive tysymbol : Type :=
    | mk_tysym : ident -> list tvsymbol -> type_def ty -> tysymbol
(*simplified version - ignore tags, combine ty and ty_node into 1*)
with ty : Type := (*ignoring tag*)
    | mk_ty : ty_node -> ty
with ty_node : Type :=
    | Tyvar : tvsymbol -> ty_node
    | Tyapp : tysymbol -> list ty -> ty_node.
*)    

(*The default induction principle is useless, we need a better one:*)

Definition p_opt {A: Type} (P: A -> Prop) (o: option A) : Prop :=
    match o with
    | None => True
    | Some x => P x
    end.

Section TyInd.

Variable P: ty -> Prop.
Variable Hvar: forall (i: ident) (l: list tvsymbol) (o: option ty), 
    p_opt P o -> P (Tyvar (i, l, o)).
Variable Happ: forall (i: ident) (l: list tvsymbol) (o: option ty) (lty: list ty),
    p_opt P o -> Forall P lty ->P (Tyapp (i, l, o) lty).
Variable Halias: forall (t: ty), P t -> P (Alias t).

Fixpoint ty_ind' (t: ty): P t :=
let f := (fix list_ty_ind (ls: list ty) : Forall P ls :=
    match ls with
    | nil => (@Forall_nil ty P)
    | (x :: tl) => @Forall_cons ty P _ _ (ty_ind' x) (list_ty_ind tl)
    end) in
match t with
| Tyvar (i, l, (Some t)) => Hvar i l (Some t) (ty_ind' t)
| Tyvar (i, l, None) => Hvar i l None I
| Tyapp (i, l, Some t) lty => Happ i l (Some t) lty (ty_ind' t) (f lty)
| Tyapp (i, l, None) lty => Happ i l None lty I (f lty)
| Alias t' => Halias t' (ty_ind' t')
end.

End TyInd.

(* Decidable Equality on Types *)

(*Writing functions over this type is quite annoying, due to the nested
  options/lists*)
Fixpoint ty_eqb (t1 t2: ty) : bool :=
    match t1, t2 with
    | Tyvar (i1, l1, o1), Tyvar (i2, l2, o2) =>
        (ident_eq_dec i1 i2) &&
        (list_eq_dec tvsymbol_eq_dec l1 l2) &&
        match o1, o2 with
        | Some t1', Some t2' => ty_eqb t1' t2'
        | None, None => true
        | _, _ => false
        end
    | Tyapp (i1, l1, o1) tyl1, Tyapp (i2, l2, o2) tyl2 =>
        (ident_eq_dec i1 i2) &&
        (list_eq_dec tvsymbol_eq_dec l1 l2) &&
        match o1, o2 with
        | Some t1', Some t2' => ty_eqb t1' t2'
        | None, None => true
        | _, _ => false
        end &&
        ((fix eqb_ty_list (l1: list ty) (l2: list ty) : bool :=
            match l1, l2 with
            | nil, nil => true
            | t1 :: tl1, t2 :: tl2 => (ty_eqb t1 t2) && (eqb_ty_list tl1 tl2)
            | _, _ => false
            end) tyl1 tyl2)
    | Alias t1', Alias t2' => ty_eqb t1' t2'
    | _, _ => false
    end.

Ltac contra :=
    let C := fresh in
    intro C; inversion C; subst; contradiction.

Ltac destruct_eq x :=
    destruct x; simpl; [|contra]. 

Lemma eqb_ty_list_simpl: forall l l',
(fix eqb_ty_list (l1 l2 : list ty) {struct l1} : bool :=
match l1 with
| [] => match l2 with
        | [] => true
        | _ :: _ => false
        end
| t1 :: tl1 =>
    match l2 with
    | [] => false
    | t2 :: tl2 => ty_eqb t1 t2 && eqb_ty_list tl1 tl2
    end
end) l l' = (Nat.eqb (length l) (length l')) && forallb id (map2 l l' (fun x y => ty_eqb x y)).
Proof.
    intros l. induction l as [|h t IH]; intros l'; simpl.
    - destruct l'; reflexivity.
    - destruct l' as [|h1 t1]; simpl; auto.
      rewrite IH; simpl. rewrite andb_comm, andb_assoc.
      unfold id at 2. rewrite <- andb_assoc.
      rewrite (andb_comm _ (ty_eqb _ _)), andb_assoc.
      reflexivity.
Qed.
      
Lemma ty_eqb_eq: forall (t1 t2: ty),
    ty_eqb t1 t2 = true ->
    t1 = t2.
Proof.
    intros t1. induction t1 using ty_ind'.
    - intros t2. destruct t2; simpl; try contra.
      destruct p as [[i2 l2] o2]; simpl.
      destruct_eq (ident_eq_dec i i2).
      destruct_eq (list_eq_dec tvsymbol_eq_dec l l2).
      subst.
      destruct o as [t1|]; destruct o2 as [t2|]; try contra;[|reflexivity].
      simpl in H. intro Heq. subst. rewrite (H t2); auto.
    - intros t2. destruct t2; simpl; try contra.
      destruct p as [[i2 l2] o2]; simpl.
      destruct_eq (ident_eq_dec i i2).
      destruct_eq (list_eq_dec tvsymbol_eq_dec l l2).
      subst. intros Heq; apply andb_prop in Heq; destruct Heq.
      assert (lty = l0). {
          rewrite eqb_ty_list_simpl in H2.
          apply andb_prop in H2; destruct H2.
          apply EqNat.beq_nat_true in H2.
          rewrite map2_combine, forallb_forall in H3.
          apply list_combine_eq; auto.
          intros x y Hinxy. assert(Hmap:=Hinxy).
          eapply in_map in Hmap. apply H3 in Hmap.
          simpl in Hmap. unfold id in Hmap.
          apply in_combine_l in Hinxy.
          rewrite Forall_forall in H0. apply H0; assumption.
      } subst; clear H2.
      destruct o as [t1|]; destruct o2 as [t2|]; try solve[inversion H1].
      rewrite (H t2) by assumption. all: reflexivity.
    - simpl. intros t2; destruct t2; try contra; intros Heq.
      rewrite (IHt1 t2); auto. 
Qed.

Lemma ty_eqb_refl: forall (t: ty),
    ty_eqb t t = true.
Proof.
    intros t; induction t using ty_ind'; simpl.
    - destruct (ident_eq_dec i i); auto.
      destruct (list_eq_dec tvsymbol_eq_dec l l); auto.
      simpl. destruct o; simpl in *; auto.
    - destruct (ident_eq_dec i i); auto.
      destruct (list_eq_dec tvsymbol_eq_dec l l); auto.
      simpl. 
      (*Need nested lemma for fixpoint here:*)
      assert (
      (fix eqb_ty_list (l1 l2 : list ty) {struct l1} : bool :=
      match l1 with
      | [] => match l2 with
              | [] => true
              | _ :: _ => false
              end
      | t1 :: tl1 =>
          match l2 with
          | [] => false
          | t2 :: tl2 => ty_eqb t1 t2 && eqb_ty_list tl1 tl2
          end
      end) lty lty = true). {
        rewrite eqb_ty_list_simpl. apply andb_true_intro.
        split.
        - apply PeanoNat.Nat.eqb_refl.
        - rewrite map2_combine; apply forallb_forall. intros x Hin.
          rewrite in_map_iff in Hin. destruct Hin as [[t1 t2] [Heq Hin]].
          simpl in *; subst. assert (Heq:=Hin).
          apply in_combine_same in Heq; subst. apply in_combine_l in Hin.
          rewrite Forall_forall in H0. apply H0. assumption.
      }
      rewrite H1; clear H1.
      destruct o; simpl in *; auto.
      rewrite H. reflexivity.
    - assumption.
Qed.

Lemma ty_eqb_eq_iff: forall (t1 t2: ty),
  Bool.reflect (t1 = t2) (ty_eqb t1 t2).
Proof.
    intros t1 t2. destruct (ty_eqb t1 t2) eqn : Heq.
    - apply ReflectT. apply ty_eqb_eq. assumption.
    - apply ReflectF. intro C; subst.
      rewrite ty_eqb_refl in Heq. inversion Heq.
Qed.

Definition ty_eq_dec: forall (t1 t2: ty), {t1 = t2} + {t1 <> t2} :=
    fun t1 t2 => reflect_dec _ _ (ty_eqb_eq_iff t1 t2).

Definition tysymbol_eq_dec: forall (t1 t2: tysymbol), {t1 = t2} + {t1 <> t2}.
Proof.
    intros t1 t2. decide equality.
    - apply option_eq_dec. intros a1 a2. apply ty_eq_dec.
    - solve_eq_dec.
Qed. 

(* Type constructors *)
Definition mk_ts (name: string) (args: list tvsymbol) (def: option ty) : tysymbol :=
    ((mk_id name), args, def).

(* Built in type symbols *)
Definition ts_int : tysymbol :=
    mk_ts "int" nil None.

Definition ts_real : tysymbol :=
    mk_ts "real" nil None.

Definition ts_bool : tysymbol :=
    mk_ts "bool" nil None.

Definition ts_str : tysymbol :=
    mk_ts "string" nil None.

(*Their implementation uses mutable hashtables and lots of exceptions.
    This is a simpler version for the types we need*)
Definition ty_app (s: tysymbol) (tl : list ty) : ty :=
    (*TODO: ignoring alias for now, may need*)
    Tyapp s tl.

Definition ty_int : ty := ty_app ts_int nil.
Definition ty_real : ty := ty_app ts_real nil.
Definition ty_bool : ty := ty_app ts_bool nil.
Definition ty_str : ty := ty_app ts_str nil.

Definition ts_func : tysymbol :=
    let tv_a := mk_tvsym (mk_id "a") in
    let tv_b := mk_tvsym (mk_id "b") in
    mk_ts "->" [tv_a; tv_b] None.

Definition ty_func (ty_a ty_b : ty) : ty :=
    ty_app ts_func [ty_a; ty_b].

(*a -> bool function*)
Definition ty_pred (ty_a : ty) : ty :=
    ty_app ts_func [ty_a; ty_bool].

(*Tuples*)

Definition nat_to_string (n: nat) : string :=
    (String (Ascii.ascii_of_nat n) EmptyString).

(*In the OCaml impl, each element gets a different id. We model
  that by giving each a different name (technically, this means that
  tuples cannot have more than 256 elements)
  Do these have to be globally unique?*)
Definition ts_tuple (n: nat) : tysymbol :=
    let vl := fold_left (fun acc m => mk_tvsym (mk_id (nat_to_string m)) :: acc)
        (seq 0 n) nil in
    mk_ts ("tuple" ++ nat_to_string n) vl None.
    
Definition ty_tuple (tyl: list ty) : ty :=
    ty_app (ts_tuple (length tyl)) tyl.


