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

