
(*Some generally useful tactics*)
Require Export Coq.Lists.List.
Require Export Lia.
  
(*TODO: use elsewhere*)

Ltac all_inj :=
  repeat match goal with
  | H : ?f ?x = ?f ?y |- _ =>
    tryif progress(injection H) then intros; subst; clear H else fail
  end.

Ltac in_map_contra :=
  match goal with
  | H: In ?x ?l, H1: ~ In (?f ?x) (List.map ?f ?l) |- _ =>
    exfalso; apply H1; rewrite in_map_iff; exists x; auto
  end.

Ltac Forall_forall_all :=
  repeat match goal with
  | H: Forall ?P ?l |- _ => rewrite Forall_forall in H
  | |- Forall ?P ?l => rewrite Forall_forall
  end.

Ltac inv H :=
  try(intros H); inversion H; subst; clear H.

Ltac split_all :=
  repeat match goal with
  | H: ?P /\ ?Q |- _ => destruct H
  | |- ?P /\ ?Q => split
  end.

Ltac destruct_all :=
  repeat match goal with
  | H: ?P /\ ?Q |- _ => destruct H
  | H: exists x, ?P |- _ => destruct H
  | H: ?P \/ ?Q |- _ => destruct H
  end; subst.

Ltac solve_or :=
  match goal with
  | |- ?P \/ ?Q => first[left; solve_or | right; solve_or]
  | |- ?P => solve[auto; try reflexivity]
  end.

Ltac contra :=
  solve[let C := fresh in
    intro C; inversion C].

Ltac right_dec := solve[let C := fresh "C" in right; intro C; inversion C; try contradiction].

Ltac triv :=
  let inner := split_all; auto; 
  match goal with
  | |- ~ ?P => let C := fresh in intro C; subst; contradiction
  end
  in
  try solve[inner];
  match goal with
  | |- ?P \/ ?Q => solve[left; inner] + solve[right; inner]
  end.

Ltac not_or name :=
  repeat match goal with 
  | H: ~(?P \/ ?Q) |- _ => let N1 := fresh name in
    let N2 := fresh name in
    apply Decidable.not_or in H;
    destruct H as [N1 N2]
  end.

(*Destruct options*)
Ltac case_match_hyp :=
  repeat match goal with 
      |- (match ?p with |Some l => ?x | None => ?y end) = ?z -> ?q =>
        let Hp := fresh "Hmatch" in 
        destruct p eqn: Hp end.
Ltac case_match_goal :=
  repeat match goal with 
        |- (match ?p with |Some l => ?x | None => ?y end) = ?z =>
          let Hp := fresh "Hmatch" in 
          destruct p eqn: Hp end; auto.

(*Forward reasoning*)
Ltac forward_gen H tac :=
        match type of H with
        | ?X -> _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
        end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.
(*For compat: TODO: move remove*)
Ltac prove_hyp H := forward H.

Ltac simpl_len_extra := idtac.

Ltac simpl_len :=
  repeat (rewrite !length_map || rewrite !length_rev || 
  rewrite !length_app || rewrite !length_combine || rewrite !repeat_length || simpl_len_extra).

Ltac solve_len := simpl_len; try reflexivity; solve[auto; try lia].

(*For solving coals of form (forall  x y, x = y <-> eqb x y).
  We use this formulation (rather than "reflect") for extracted code, since this is in Prop*)
Ltac solve_eqb_eq :=
  solve[let Heq := fresh "Heq" in
  split; intros Heq; 
  ((progress (inversion Heq; destruct_all; subst))+
  (*TODO: why does inversion fail sometimes?*)
  (destruct Heq; subst) +
  (idtac)); 
  (* inversion Heq; destruct_all; subst; *)
  (*Solve goals*)
  auto; 
  try solve[split_all; auto];
  try discriminate; 
  try solve[ f_equal; auto];
  contradiction].