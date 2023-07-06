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