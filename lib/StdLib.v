Require Export Task.
Require Export Theory.
Require Export Typechecker.
Require Export Tactics.
Require Export Notations.
From mathcomp Require Export all_ssreflect.

(*TODO: different than other version because we use [funsym_noty]
  instead of writing manually*)
Definition const name ty := funsym_noty name nil ty.
Definition binop name ty : funsym := funsym_noty name [ty;ty] ty.
Definition unop name ty : funsym := funsym_noty name [ty] ty.
Definition binpred name ty : predsym := predsym_noty name [ty; ty].

Definition nonrec_fun f args body : def := nonrec_def (fun_def f args body).
Definition nonrec_pred p args body : def := nonrec_def (pred_def p args body).
Definition rec_fun f args body : def := recursive_def [fun_def f args body].
Definition rec_pred p args body : def := recursive_def [pred_def p args body].

Notation mk_typemap l := (exist _ l erefl).
Definition emp_typemap : ty_map := (exist _ nil erefl).