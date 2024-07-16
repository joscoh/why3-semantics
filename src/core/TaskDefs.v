Require Import DeclDefs DeclFuncs TheoryDefs.

(*Clone and Meta History*)

(* 
(** Task *)
Inductive task_head := mk_task_head {
  task_decl  : tdecl;        (* last declaration *)
  task_prev  : option task_head;         (* context *)
  task_known : known_map;    (* known identifiers *)
  task_clone : clone_map;    (* use/clone history *)
  task_meta  : meta_map;     (* meta properties *)
  task_tag   : Weakhtbl.tag; (* unique magical tag *)
}.

Definition task := option task_head.

type task = task_hd option

and task_hd = {
  task_decl  : tdecl;        (* last declaration *)
  task_prev  : task;         (* context *)
  task_known : known_map;    (* known identifiers *)
  task_clone : clone_map;    (* use/clone history *)
  task_meta  : meta_map;     (* meta properties *)
  task_tag   : Weakhtbl.tag; (* unique magical tag *)
} *)