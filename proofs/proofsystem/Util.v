Require Export Logic.
(*utilities to prevent us from having to write the type
  variables in a function/predicate symbol*)

Definition constr_noty (name: string) (args: list vty) 
  (ret: vty) (num: nat) : funsym :=
  Build_funsym (Build_fpsym name (find_args (ret :: args)) args
    (find_args_check_args_l _ _ (fun x => in_cons _ x _)) (find_args_nodup _)) 
    ret true num (find_args_check_args_in _ _ (in_eq _ _)).

Definition predsym_noty (name: string) (args: list vty) : predsym :=
  Build_predsym (Build_fpsym name (find_args args) args
    (find_args_check_args_l _ _ (fun x H => H))
    (find_args_nodup _)).

(*Constant symbols*)

Definition const_noconstr (name: string) (ty: vty) : funsym :=
  funsym_noconstr_noty name nil ty.
Definition const_constr (name: string) (ty: vty) (num: nat) : funsym :=
  constr_noty name nil ty num.

(*Non-constr*)
Definition t_constsym name s : term :=
  Tfun (const_noconstr name s) nil nil.

Lemma t_constsym_fv name s:
  tm_fv (t_constsym name s) = nil.
Proof.
  reflexivity.
Qed.

Lemma t_constsym_mono name s:
  mono_t (t_constsym name s).
Proof.
  reflexivity.
Qed.