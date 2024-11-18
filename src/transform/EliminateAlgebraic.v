Require Import TermFuncs TermTraverse PatternComp.
(** Compile match patterns *)
Import MonadNotations.

Local Open Scope errst_scope.
Definition rewriteT (t: term_c) : errState (CoqBigInt.t * hashcons_ty ty_c) term_c :=
  term_map (hashcons_ty ty_c)
  (*let*)
  (tmap_let_default _)
  (tmap_if_default _)
  (tmap_app_default _)
  (*only interesting case*)
  (fun t1 r1 tb =>
    res <- compile_bare_aux t_case_close t_let_close_simp [r1] (map (fun x => ([fst (fst x)], snd x)) tb) ;;
    errst_ret (t_attr_copy t res)
    )
  (tmap_eps_default _)
  (tmap_quant_default _)
  (tmap_binop_default _)
  (tmap_not_default _)
  t.