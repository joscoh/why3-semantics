Require Export Logic.
(*utilities to prevent us from having to write the type
  variables in a function/predicate symbol*)

(*NOTE: does not work with sets, sets dont compute very well except from vm_compute*)
Definition constr_noty (name: string) (args: list vty) 
  (ret: vty) (num: nat) : funsym :=
  Build_funsym (Build_fpsym name (find_args (ret :: args)) args
    (find_args_check_args_l _ _ (fun x => in_cons _ x _)) (find_args_nodup _)) 
    ret true num (find_args_check_args_in _ _ (in_eq _ _)).

Definition predsym_noty (name: string) (args: list vty) : predsym :=
  Build_predsym (Build_fpsym name (find_args args) args
    (find_args_check_args_l _ _ (fun x H => H))
    (find_args_nodup _)).
(*Use notation so we can use eq_refl*)
Notation mk_constr name params args ret num args1 nodup ret1 :=
  (Build_funsym (Build_fpsym name params args args1 nodup) ret true num ret1).
Notation mk_noconstr name params args ret args1 nodup ret1 :=
  (Build_funsym (Build_fpsym name params args args1 nodup) ret false 0 ret1).
(* Definition mk_constr (name: string) (params: list typesym) (args: list vty) (ret: vty) (num: nat) *)

(*Constant symbols*)

(*NOTE: be careful using using (see note in Syntax.v*)
Definition const_noconstr (name: string) (ty: vty) : funsym :=
  funsym_noconstr_noty name nil ty.
(*Definition const_constr (name: string) (ty: vty) (num: nat) : funsym :=
  constr_noty name nil ty num. *)

(*Non-constr*)
Definition t_constsym name s : term :=
  Tfun (const_noconstr name s) nil nil.

Lemma t_constsym_fv name s:
  tm_fv (t_constsym name s) = aset_empty.
Proof.
  reflexivity.
Qed.

Lemma t_constsym_mono name s:
  mono_t (t_constsym name s).
Proof.
  reflexivity.
Qed.