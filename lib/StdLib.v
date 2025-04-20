From Proofs.core Require Export Task Theory Typechecker.
From Proofs.proofsystem Require Export Tactics Notations.
From mathcomp Require Export all_ssreflect.

(*Different than other version because we use [funsym_noty]
  instead of writing manually*)
Definition const_noconstr name ty := funsym_noconstr_noty name nil ty.
Definition const_constr name ty n := constr_noty name nil ty n.
Definition binop name ty : funsym := funsym_noconstr_noty name [ty;ty] ty.
Definition unop name ty : funsym := funsym_noconstr_noty name [ty] ty.
Definition binpred name ty : predsym := predsym_noty name [ty; ty].

Definition nonrec_fun f args body : def := nonrec_def (fun_def f args body).
Definition nonrec_pred p args body : def := nonrec_def (pred_def p args body).
Definition rec_fun f args body : def := recursive_def [fun_def f args body].
Definition rec_pred p args body : def := recursive_def [pred_def p args body].

Notation mk_typemap l := (exist _ l erefl).
Definition emp_typemap : ty_map := (exist _ amap_empty erefl).

Open Scope string_scope.
Open Scope why3_scope.