(*Only need definition (For Theory)*)
Require Import IdentDefs TyDefs TermDefs.

Inductive coercion_kind :=
  | CRCleaf: lsymbol -> coercion_kind
  | CRCcomp: coercion_kind -> coercion_kind -> coercion_kind.
  
Record coercion := {
  crc_kind   : coercion_kind;
  crc_src_ts : tysymbol_c;
  crc_src_tl : list ty_c;
  crc_tar_ts : tysymbol_c;
  crc_tar_tl : list ty_c;
}.

Definition t := Mts.t (Mts.t coercion).
(** invariant: transitively closed *)

(* Decidable Equality *)
Fixpoint coercion_kind_eqb (c1 c2: coercion_kind) : bool :=
  match c1, c2 with
  | CRCleaf l1, CRCleaf l2 => ls_equal l1 l2
  | CRCcomp c1 c2, CRCcomp c3 c4 => coercion_kind_eqb c1 c3 && coercion_kind_eqb c2 c4
  | _, _ => false
  end.

Definition coercion_eqb (c1 c2: coercion) : bool :=
  coercion_kind_eqb c1.(crc_kind) c2.(crc_kind) &&
  ts_equal c1.(crc_src_ts) c2.(crc_src_ts) &&
  list_eqb ty_eqb c1.(crc_src_tl) c2.(crc_src_tl) &&
  ts_equal c1.(crc_tar_ts) c2.(crc_tar_ts) &&
  list_eqb ty_eqb c1.(crc_tar_tl) c2.(crc_tar_tl).

Definition t_eqb (t1 t2: t) : bool :=
  Mts.equal (Mts.equal coercion_eqb) t1 t2.

Lemma coercion_kind_eqb_eq (c1 c2: coercion_kind) :
  c1 = c2 <-> coercion_kind_eqb c1 c2.
Proof.
  revert c2. induction c1 as [l1 | c1 IH1 c2 IH2]; intros [l2 | c3 c4]; simpl; auto;
  try solve_eqb_eq.
  - rewrite <- lsymbol_eqb_eq. solve_eqb_eq.
  - rewrite andb_true, <- (IH1 c3), <- (IH2 c4). solve_eqb_eq.
Qed.

Lemma coercion_eqb_eq (c1 c2: coercion) :
  c1 = c2 <-> coercion_eqb c1 c2.
Proof.
  unfold coercion_eqb.
  rewrite !andb_true, <- coercion_kind_eqb_eq,
  <- !tysymbol_eqb_eq, <- !(list_eqb_eq ty_eqb_eq).
  destruct c1; destruct c2; simpl.
  solve_eqb_eq.
Qed.

Lemma t_eqb_eq (t1 t2: t) : t1 = t2 <-> t_eqb t1 t2.
Proof.
  unfold t_eqb. apply Mts.eqb_eq.
  - apply Mts.eqb_eq.
    + apply coercion_eqb_eq.
    + apply tysymbol_eqb_eq.
  - apply tysymbol_eqb_eq.
Qed. 
