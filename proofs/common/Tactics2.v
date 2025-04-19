Require Import CommonList aset.
Require Export Coq.Lists.List.
Ltac len_tac :=
  repeat match goal with
  | |- context [length (firstn ?n ?l)] => rewrite length_firstn
  | |- context [length (skipn ?n ?l)] => rewrite length_skipn
  | H: length ?l = ?x |- context [length ?l] => rewrite H
  | |- context [length (?x ++ ?y)] => rewrite length_app
  end; try lia.
  
(*Deal with In (firstn) and similar goals*)
Ltac in_tac :=
  repeat match goal with
  | |- In (?x :: ?l) => simpl
  | |- In (nth ?i ?l ?x) ?l =>
    apply nth_In
  | H: In ?x (firstn ?n ?l) |- _ => apply In_firstn in H
  | H: In ?x (skipn ?n ?l) |- _ => apply In_skipn in H
  | |- In ?x (map ?g ?l) => rewrite in_map_iff
  | |- In ?x (?l1 ++ ?l2) => rewrite in_app_iff
  | |- In ?x ?l1 \/ In ?x ?l2 => solve[left; in_tac] + solve[right; in_tac]
  end; auto.

Ltac list_tac :=
  repeat(
  assumption +
  solve[len_tac] +
  solve[lia] +
  solve[in_tac] +
  match goal with
  | |- context [map snd (combine ?l1 ?l2)] =>
    rewrite map_snd_combine
  | |- context [map fst (combine ?l1 ?l2)] =>
    rewrite map_fst_combine
  | |- NoDup (firstn ?n ?l) => apply NoDup_firstn
  | |- NoDup (skipn ?n ?l) => apply NoDup_skipn
  | |- context [length (map ?f ?x)] => rewrite length_map
  | |- context [length (firstn ?n ?l)] => rewrite length_firstn
  | |- context [length (skipn ?n ?l)] => rewrite length_skipn
  | |- In (nth ?i ?l ?x) ?l =>
    apply nth_In
  | |- context [length (map2 ?f ?l1 ?l2)] =>
    rewrite map2_length
  | |- ?i < length ?l -> ?P => intros
  | |- context [Nat.min ?x ?x] =>
    rewrite Nat.min_id
  | |- context [In ?x (?l1 ++ ?l2)] =>
    rewrite in_app_iff
  (*Deal with some "In" goals*)
  | |- In ?x (map ?g ?l) => rewrite in_map_iff
  | H: In ?x (firstn ?n ?l) |- In ?x ?l => apply In_firstn in H
  | H: In ?x (skipn ?n ?l) |- In ?x ?l => apply In_skipn in H
  | H: In ?x (firstn ?n ?l1) |- In ?x ?l2 => apply In_firstn in H
  | |- exists y, ?f y = ?f ?x /\ ?P => exists x; split
  (*Solve the sum length goal*)
  | H: length ?l = length (concat (map ?f ?l1)) |-
    sum (map ?g ?l1) = length ?l => rewrite CommonList.length_concat in H;
    rewrite H; f_equal; rewrite map_map; apply map_ext
  | H: length (?x :: ?l) = ?n |- _ => simpl in H
  | H: ?x = length (?l1 ++ ?l2) |- _ => rewrite length_app in H
  end); auto; try lia. 

Ltac case_in :=
  repeat match goal with
  | |- context [if in_bool ?e ?x ?l then ?y else ?z] => 
    destruct (in_bool_spec e x l)
  end.

(* Ltac eq_mem_tac :=
  repeat match goal with
  | |- eq_mem ?l ?l => apply eq_mem_refl
  | |- eq_mem (union ?dec ?l1 ?l2) (union ?dec ?l2 ?l1) => apply eq_mem_union_comm
  | |- eq_mem (union ?dec ?l1 ?l2) (union ?dec ?l3 ?l4) => apply eq_mem_union
  end; auto. *)

(*TODO: use elsewhere*)
Ltac nodup_inj :=
  match goal with
  | H: ?f ?x = ?f ?y, Hn1: NoDup (List.map ?f ?l) |- _ => assert (x = y) by
    (apply (NoDup_map_in Hn1); assumption);
    subst y; clear H
  end.

Ltac simpl_and_destruct :=
  repeat (subst; simpl in *; destruct_all; try contradiction).

Ltac destruct_list_in :=
  repeat (match goal with
    | H: In ?x (concat ?l) |- _ => rewrite in_concat in H
    | H: In ?x (map ?f ?l) |- _ => rewrite in_map_iff in H
    | H: In ?x (rev ?l) |- _ => rewrite <- In_rev in H
    | H: In ?x (?l1 ++ ?l2) |- _ => rewrite in_app_iff in H
    end; simpl_and_destruct).