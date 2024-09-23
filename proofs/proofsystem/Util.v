Require Export Logic.
(*utilities to prevent us from having to write the type
  variables in a function/predicate symbol*)

Definition find_args (l: list vty) : list typevar :=
  big_union typevar_eq_dec type_vars l.

Lemma find_args_nodup l:
  nodupb typevar_eq_dec (find_args l).
Proof.
  apply (ssrbool.introT (nodup_NoDup _ _)).
  apply big_union_nodup.
Qed.

Lemma find_args_check_args_l l1 l2:
  (forall x, In x l1 -> In x l2) ->
  check_args (find_args l2) l1.
Proof.
  intros.
  apply (ssrbool.introT (check_args_correct _ _)).
  intros.
  unfold find_args, sublist. intros.
  simpl_set. exists x. split; auto.
Qed.

Lemma find_args_check_args_in x l:
  In x l ->
  check_sublist (type_vars x) (find_args l).
Proof.
  intros. apply (ssrbool.introT (check_sublist_correct _ _)).
  unfold sublist. intros. unfold find_args. simpl_set.
  exists x; auto.
Qed.

Definition funsym_noconstr_noty (name: string) (args: list vty) 
  (ret: vty)  : funsym :=
  Build_funsym (Build_fpsym name (find_args (ret :: args)) args
    (find_args_check_args_l _ _ (fun x => in_cons _ x _)) (find_args_nodup _)) 
    ret false 0 (find_args_check_args_in _ _ (in_eq _ _)).

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