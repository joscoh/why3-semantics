Require Import Pattern.
Require Import Denotational.
Require Import Coq.Sorting.Permutation.
Require Import GenElts.
From Equations Require Import Equations. 
Set Bullet Behavior "Strict Subproofs".


(*TODO: move to common*)
Ltac inv H :=
  try(intros H); inversion H; subst; clear H.

(*General results we need*)
Lemma Forall2_inv_head {A B: Type} {R: A -> B -> Prop} {a: A} {la: list A}
  {b1: B} {lb: list B} (Hall: Forall2 R (a :: la) (b1 :: lb)) : R a b1.
Proof.
  inversion Hall; auto.
Qed.

Lemma Forall2_inv_tail {A B: Type} {R: A -> B -> Prop} {a: A} {la: list A}
  {b1: B} {lb: list B} (Hall: Forall2 R (a :: la) (b1 :: lb)) : Forall2 R la lb.
Proof.
  inversion Hall; auto.
Qed.

Lemma Forall2_rev {A B: Type} {R: A -> B -> Prop} {l1 : list A} {l2: list B}:
  Forall2 R l1 l2 ->
  Forall2 R (rev l1) (rev l2).
Proof.
  intros Hall. induction Hall; simpl; auto.
  apply Forall2_app; auto.
Qed.

Lemma Forall2_rev_inv {A B: Type} {R: A -> B -> Prop} {l1 : list A} {l2: list B}:
  Forall2 R (rev l1) (rev l2) ->
  Forall2 R l1 l2.
Proof.
  intros Hall.
  rewrite <- (rev_involutive l1), <- (rev_involutive l2).
  apply Forall2_rev; auto.
Qed.

Lemma Forall2_app_inv {A B: Type} {P: A -> B -> Prop} {l1 l2 l3 l4}:
  Forall2 P (l1 ++ l2) (l3 ++ l4) ->
  length l1 = length l3 ->
  Forall2 P l1 l3 /\ Forall2 P l2 l4.
Proof.
  generalize dependent l3. induction l1 as [| h1 t1 IH]; intros [| h3 t3]; simpl;
  intros Hall Hlen; try discriminate; auto.
  inversion Hall as [|? ? ? ? Hp Hallt]; subst.
  specialize (IH t3 Hallt ltac:(lia)).
  destruct_all; split; auto.
Qed.

Lemma Forall2_combine {A B: Type} (P: A -> B -> Prop) (l1 : list A) (l2: list B):
  Forall2 P l1 l2 <-> length l1 = length l2 /\ Forall (fun x => P (fst x) (snd x)) (combine l1 l2).
Proof.
  split.
  - intros Hall. induction Hall; simpl; auto.
    destruct IHHall as [Hlen IHall].
    split; auto.
  - revert l2. induction l1 as [| h1 t1 IH]; intros [| h2 t2]; simpl; intros [Hlen Hall]; try discriminate; auto.
    inversion Hall; subst.
    constructor; auto.
Qed.

Lemma Forall2_nth {B C: Type} {P: B -> C -> Prop} (l1: list B) (l2: list C):
  Forall2 P l1 l2 <-> (length l1 = length l2 /\ forall i d1 d2, i < length l1 ->
    P (nth i l1 d1) (nth i l2 d2)).
Proof.
  rewrite Forall2_combine. split; intros [Hlen Hith]; split; auto.
  - rewrite Forall_nth in Hith.
    rewrite combine_length, Hlen, Nat.min_id in Hith.
    intros i d1 d2 Hi.
    rewrite Hlen in Hi.
    specialize (Hith i (d1, d2) Hi).
    rewrite combine_nth in Hith; auto.
  - apply Forall_nth.
    intros i [d1 d2]. rewrite combine_length, Hlen, Nat.min_id, combine_nth; auto.
    intros Hi. apply Hith; lia.
Qed.

Lemma Forall_app_snd {A: Type} {P: A -> Prop} {l1 l2: list A}:
  Forall P (l1 ++ l2) ->
  Forall P l2.
Proof.
  rewrite Forall_app; intros [_ Hp]; auto.
Qed.

Lemma rev_inj {A: Type} (l1 l2: list A):
  rev l1 = rev l2 ->
  l1 = l2.
Proof.
  intros Hrev.
  rewrite <- (rev_involutive l1), <- (rev_involutive l2). rewrite Hrev; auto.
Qed.

Lemma combine_app {A B: Type} (l1 l2: list A) (l3 l4: list B):
  length l1 = length l3 ->
  combine (l1 ++ l2) (l3 ++ l4) = combine l1 l3 ++ combine l2 l4.
Proof.
  revert l3. induction l1 as [| h1 t1 IH]; simpl; intros [| h3 t3]; simpl; auto; try discriminate.
  intros Hlen. f_equal. apply IH. lia.
Qed.

Lemma rev_combine {A B: Type} (l1 : list A) (l2: list B):
  length l1 = length l2 ->
  rev (combine l1 l2) = combine (rev l1) (rev l2).
Proof.
  revert l2. induction l1 as [|h1 t1 IH]; simpl; auto.
  intros [| h2 t2] Hlen; simpl in *.
  - rewrite combine_nil. reflexivity.
  - rewrite combine_app.
    + rewrite IH; auto.
    + rewrite !rev_length; auto.
Qed.

(*TODO: move*)
(*Prevent expansion under simpl*)
Lemma big_union_cons {A B: Type} (eq_dec: forall x y: A, {x = y} + {x <> y})
  (f: B -> list A) (y: B) (l: list B):
  big_union eq_dec f (y :: l) = union eq_dec (f y) (big_union eq_dec f l).
Proof. reflexivity. Qed.

(*TODO: move*)
Lemma big_union_app {B C: Type} (eq_dec: forall (x y: C), {x = y} + {x <> y})
  (f: B -> list C) (l1 l2: list B):
  forall x, In x (big_union eq_dec f (l1 ++ l2)) <-> In x (union eq_dec (big_union eq_dec f l1) (big_union eq_dec f l2)).
Proof. 
  intros x. simpl_set. setoid_rewrite in_app_iff.
  split; intros; destruct_all; eauto.
Qed.

Lemma big_union_rev {B C: Type} eq_dec (f: B -> list C) (l: list B) x:
  In x (big_union eq_dec f (rev l)) <-> In x (big_union eq_dec f l).
Proof.
  induction l; simpl; [reflexivity|].
  rewrite big_union_app. simpl_set_small. simpl. split; intros Hin.
  - destruct Hin as [Hin | [Hin | []]]; auto; apply IHl in Hin; auto.
  - destruct Hin as [Hin | Hin]; auto; apply IHl in Hin; auto.
Qed.


Lemma in_map_big_union_app {B C D: Type} (f: B -> list C) (g: C -> D) eq_dec l1 l2 x:
  In x (map g (big_union eq_dec f (l1 ++ l2))) <->
  In x (map g (big_union eq_dec f l1)) \/ In x (map g (big_union eq_dec f l2)).
Proof.
  rewrite !in_map_iff. setoid_rewrite big_union_app. setoid_rewrite union_elts.
  split; intros; destruct_all; eauto.
Qed.

Lemma in_map_big_union_rev {B C D: Type} (f: B -> list C) (g: C -> D) eq_dec l x:
  In x (map g (big_union eq_dec f (rev l))) <->
  In x (map g (big_union eq_dec f l)).
Proof.
  rewrite !in_map_iff. setoid_rewrite big_union_rev. reflexivity.
Qed.

Lemma in_map_big_union {B C D: Type} (f: B -> list C) (g: C -> D)  eq_dec eq_dec1 l x:
  In x (map g (big_union eq_dec f l)) <->
  In x (big_union eq_dec1 (fun x => map g (f x)) l).
Proof.
  rewrite in_map_iff. simpl_set.
  split.
  - intros [y [Hx Hiny]]; subst. simpl_set.
    destruct Hiny as [z [Hinz Hiny]].
    exists z. rewrite in_map_iff. eauto.
  - intros [y [Hiny Hinx]]. rewrite in_map_iff in Hinx.
    destruct Hinx as [z [Hx Hinz]]; subst.
    exists z. simpl_set. eauto.
Qed.

Lemma in_map_union {B C: Type} (f: B -> C) eq_dec l1 l2 x:
  In x (map f (union eq_dec l1 l2)) <->
  In x (map f l1) \/ In x (map f l2).
Proof.
  rewrite !in_map_iff. setoid_rewrite union_elts. split; intros; destruct_all; eauto.
Qed.


(*TODO: move to hlist and do stuff with equations*)
Equations hlist_app {A: Type} (f: A -> Type) (l1 l2: list A) (h1: hlist f l1) (h2: hlist f l2):
  hlist f (l1 ++ l2) :=
  hlist_app f nil l2 h1 h2 := h2;
  hlist_app f (x :: l1) l2 (HL_cons _ a1 htl) h2 := HL_cons _ _ _ a1 (hlist_app f l1 l2 htl h2).

Equations hlist_rev {A: Type} (f: A -> Type) (l: list A) (h: hlist f l) : hlist f (rev l) :=
  hlist_rev f nil h := h;
  hlist_rev f (x :: t) (HL_cons _ a1 htl) := hlist_app f (rev t) [x] (hlist_rev f t htl) 
    (HL_cons _ _ _ a1 (HL_nil _)).


Lemma hlist_hd_app1 {A: Type} {f: A -> Type} hd l1 l2 h1 h2:
  hlist_hd (hlist_app f (hd :: l1) l2 h1 h2) =
  hlist_hd h1.
Proof.
  rewrite (hlist_inv h1). simp hlist_app. reflexivity.
Qed. 

Lemma hlist_tl_app1 {A: Type} {f: A -> Type} hd l1 l2 h1 h2:
  hlist_tl (hlist_app f (hd :: l1) l2 h1 h2) =
  (hlist_app f l1 l2 (hlist_tl h1) h2).
Proof.
  rewrite (hlist_inv h1). simp hlist_app. reflexivity.
Qed. 

Lemma hlist_app_cast1 {f: sort -> Set} (l1 l2 l3: list sort) (h: arg_list f l1) h2 (Heq: l1 = l2):
  hlist_app f l2 l3 (cast_arg_list Heq h) h2 =
  cast_arg_list (f_equal (fun x => x ++ l3) Heq) (hlist_app f l1 l3 h h2).
Proof.
  subst. simpl. unfold cast_arg_list; simpl. reflexivity.
Qed.

Lemma hlist_rev_cast {f: sort -> Set} (l1 l2: list sort) (Heq: l1 = l2) (h1: arg_list f l1):
  hlist_rev f l2 (cast_arg_list Heq h1) =
  cast_arg_list (f_equal (fun x => rev x) Heq) (hlist_rev f l1 h1).
Proof.
  subst. reflexivity.
Qed.

Lemma rev_nth1 {A: Type} (l: list A) (d: A) (n: nat):
  n < length l ->
  nth n l d = nth (length l - S n) (rev l) d.
Proof.
  intros Hn.
  rewrite <- (rev_involutive l) at 1.
  rewrite rev_nth; rewrite rev_length; auto.
Qed.
Lemma hlist_app_hnth1 (dom: sort -> Set) tys1 tys2 (h1 : arg_list (domain dom) tys1) (h2: arg_list (domain dom) tys2) d1 d2 n:
  n < length tys1 ->
  exists Heq,
  hnth n (hlist_app _ tys1 tys2 h1 h2) d1 d2 =
  dom_cast _ Heq (hnth n h1 d1 d2).
Proof.
  revert n.
  induction tys1 as [| ty1 tys IH]; simpl.
  - intros n Hn. lia.
  - intros [| n'] Hn.
    + exists eq_refl. rewrite (hlist_inv h1). reflexivity.
    + destruct (IH (hlist_tl h1) n' (ltac:(lia))) as [Heq Hnth].
      exists Heq. rewrite (hlist_inv h1). simp hlist_app.
Qed.

Lemma hlist_app_hnth2 (dom: sort -> Set) tys1 tys2 (h1 : arg_list (domain dom) tys1) (h2: arg_list (domain dom) tys2) d1 d2 n:
  n >= length tys1 ->
  exists Heq,
  hnth n (hlist_app _ tys1 tys2 h1 h2) d1 d2 =
  dom_cast _ Heq (hnth (n - length tys1) h2 d1 d2).
Proof.
  revert n.
  induction tys1; simpl.
  - intros n Hn. rewrite Nat.sub_0_r. exists eq_refl. reflexivity.
  - intros n Hn.
    remember (n - S (Datatypes.length tys1)) as j eqn : Hj.
    destruct j as [| j']; simpl.
    + assert (n = S (length tys1)) by lia. subst. 
      destruct (IHtys1 (hlist_tl h1) (length tys1) (ltac:(lia))) as [Heq1 IH].
      revert Heq1 IH. rewrite Nat.sub_diag. intros. exists Heq1.
      rewrite (hlist_inv h1). simp hlist_app.
    + (*assert (Hngt: n > S (length tys1)) by lia.*) destruct n as [| n']; [discriminate|].
      assert (Hn': n' >= length tys1) by lia.
      destruct (IHtys1 (hlist_tl h1) n' Hn') as [Heq1 IH].
      revert Heq1 IH.
      replace (n' - length tys1) with (S j') by lia.
      intros. exists Heq1. rewrite (hlist_inv h1). simp hlist_app.
Qed.

Lemma hlist_rev_hnth (dom: sort -> Set) i tys (h: arg_list (domain dom) tys) d1 d2:
  i < length tys ->
  exists Heq,
  hnth i (hlist_rev (domain dom) tys h) d1 d2 =
  dom_cast dom Heq (hnth (length tys - S i) h d1 d2).
Proof.
  revert i. induction tys as [| ty1 tys IH]; simpl.
  - intros i Hi; lia.
  - intros i Hi. remember (length tys - i) as j eqn : Hj. 
    destruct j as [| j'].
    + assert (i = length tys) by lia. subst.
      (*Use app2 lemma*)
      destruct (hlist_app_hnth2 dom _ _ (hlist_rev (domain dom) tys (hlist_tl h)) 
        (HL_cons (domain dom) ty1 [] (hlist_hd h) (HL_nil (domain dom))) d1 d2 (length tys)
        (ltac:(rewrite rev_length; lia))) as [Heq1 Happ].
      revert Heq1 Happ. rewrite rev_length, Nat.sub_diag. simpl. intros.
      exists Heq1. rewrite (hlist_inv h). simp hlist_rev.
    + (*Need IH and app1*)
      assert (Heq: nth j' tys d1 = nth i (rev tys ++ [ty1]) d1).
      {
        rewrite app_nth1; [|rewrite rev_length; lia].
        rewrite rev_nth; try lia. 
        f_equal. lia.
      }
      exists Heq.
      rewrite (hlist_inv h).
      simp hlist_rev.
     (*use app1 lemma*)
      destruct (hlist_app_hnth1 dom _ _ (hlist_rev (domain dom) tys (hlist_tl h)) 
        (HL_cons (domain dom) ty1 [] (hlist_hd h) (HL_nil (domain dom))) d1 d2 i
        (ltac:(rewrite rev_length; lia))) as [Heq1 Happ].
      rewrite Happ.
      destruct (IH (hlist_tl h) i ltac:(lia)) as [Heq2 IH2].
      rewrite IH2. rewrite !dom_cast_compose.
      simpl. generalize dependent (eq_trans Heq2 Heq1).
      replace (length tys - S i) with j' by lia. intros.
      apply dom_cast_eq.
Qed.

Ltac destruct_match_single l Hmatch :=
  match goal with |- context [match_val_single ?v ?pd ?vt ?ty ?phd ?H1 ?h1] =>
      destruct (match_val_single v pd vt ty phd H1 h1) as [l|] eqn : Hmatch; simpl
    end.

(*TODO: move*)
Lemma fold_left_opt_none {B C: Type} (f: B -> C -> option B) (l: list C) (base: B) :
  fold_left_opt f l base = None <->
  exists l1 x l2 y, l = l1 ++ x :: l2 /\ (fold_left_opt f l1 base)= Some y /\ f y x  = None.
Proof.
  revert base. induction l as [| h t IH]; simpl; intros; auto.
  - split; try discriminate.
    intros [l1 [x [l2 [y [Hl _]]]]]. destruct l1; inversion Hl.
  - destruct (f base h) eqn : Hf.
    + rewrite IH. split; intros [l1 [x [l2 [y [Hl [Hfold Hf']]]]]]; subst.
      * exists (h :: l1). exists x. exists l2. exists y. split_all; auto.
        simpl. rewrite Hf. auto.
      * destruct l1 as [| h1 t1].
        -- simpl in *. inversion Hfold; subst.
          inversion Hl; subst. rewrite Hf' in Hf. discriminate.
        -- inversion Hl; subst.
          simpl in Hfold. rewrite Hf in Hfold. 
          exists t1. exists x. exists l2. exists y. split_all; auto.
    + split; auto. intros _. exists nil. exists h. exists t.
      exists base. split_all; auto.
Qed.

Definition fold_left_opt_cons {B C D: Type} (g: C -> option D) (h: C -> B) base l y: 
  fold_left_opt (fun acc x =>
    match (g x) with
    | Some v => Some ((h x, v) :: acc)
    | None => None
    end) l base = Some y ->
  rev (map (fun x => (h x, g x)) l) ++ (map (fun x => (fst x, Some (snd x))) base) =
  map (fun x => (fst x, Some (snd x))) y.
Proof.
  revert base. revert y. induction l as [| h1 t1 IH]; simpl.
  - intros y base. inv Hbase. reflexivity.
  - intros y base.
    destruct (g h1) as [v1 |]; [|discriminate].
    simpl. intros Hopt.
    apply IH in Hopt.
    rewrite <- Hopt. simpl.
    rewrite <- app_assoc. simpl. reflexivity.
Qed.

(*Very annoying, but we need to slightly change the function so that we can use it*)
Lemma fold_left_opt_change_f {B C: Type} (f1 f2: B -> C -> option B) (l: list C) (x: B):
  (forall b c, f1 b c = f2 b c) ->
  fold_left_opt f1 l x = fold_left_opt f2 l x.
Proof.
  intros Hext.
  revert x. induction l; simpl; auto.
  intros x. rewrite Hext. destruct (f2 x a); auto.
Qed.


(*TODO: move to typing*)
Lemma P_Constr' {gamma} (params: list vty) (ps: list pattern) (f: funsym) ty:
  In f (sig_f gamma) ->
  Forall (valid_type gamma) params ->
  valid_type gamma (f_ret f) ->
  length params = length (s_params f) ->
  Forall2 (pattern_has_type gamma) ps (ty_subst_list (s_params f) params (s_args f)) ->
  (forall i j d, i < length ps -> j < length ps -> i <> j -> disj (pat_fv (nth i ps d)) (pat_fv (nth j ps d))) ->
  (exists (m: mut_adt) (a: alg_datatype), mut_in_ctx m gamma /\ adt_in_mut a m /\ constr_in_adt f a) ->
  ty = ty_subst (s_params f) params (f_ret f) ->
  pattern_has_type gamma (Pconstr f params ps) ty.
Proof.
  intros Hinf Hallval Hval Hlenparams Hallty Hdisj Hadt Ht; subst. constructor; auto.
  - apply Forall2_length in Hallty. unfold ty_subst_list in Hallty.
    rewrite map_length in Hallty. auto.
  - rewrite <- Forall_forall. rewrite Forall2_combine in Hallty. apply Hallty.
  - intros i j d x Hi Hj Hij [Hx1 Hx2]. apply (Hdisj i j d Hi Hj Hij x); auto.
Qed.

(*TODO: move*)
Lemma P_Var' {gamma} (x: vsymbol) ty:
  valid_type gamma ty ->
  snd x = ty ->
  pattern_has_type gamma (Pvar x) ty.
Proof.
  intros. subst. constructor. auto.
Qed.


(*TODO: replace [prove_hyp]*)
Ltac forward_gen H tac :=
        match type of H with
        | ?X -> _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
        end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.

(*TODO: move*)
Lemma disj_map {B C: Type} (f: B -> C) (l1 l2: list B):
  disj (map f l1) (map f l2) ->
  disj l1 l2.
Proof.
  unfold disj. intros Hdisj x [Hinx1 Hinx2].
  apply (Hdisj (f x)); rewrite !in_map_iff; split; exists x; auto.
Qed.


Section PatProofs.

Context {gamma: context} (gamma_valid: valid_context gamma).
Context (pd: pi_dom) (pf: pi_funpred gamma_valid pd) (vt: val_typevar).
(* Variable (v: val_vars pd vt). *)
Variable (b: bool). (*Generic over terms and formulas*)
Variable (ret_ty : gen_type b). (*The return type of the values*)

(*More "gen" results (TODO: should move somewhere)*)
Section Gen.
(*Generalized term/formula rep*)
Definition gen_rep (v: val_vars pd vt) (ty: gen_type b) (d: gen_term b) (Hty: gen_typed b d ty) : gen_ret pd vt b ty :=
  match b return forall (ty: gen_type b) (dat: gen_term b), 
    gen_typed b dat ty -> gen_ret pd vt b ty with
  | true => fun ty dat Hty => term_rep gamma_valid pd vt pf v dat ty Hty
  | false => fun ty dat Hty => formula_rep gamma_valid pd vt pf v dat Hty
  end ty d Hty.

Definition gen_fv (t: gen_term b) : list vsymbol :=
  match b return gen_term b -> list vsymbol with
  | true => tm_fv
  | false => fmla_fv
  end t.

Lemma gen_rep_change_vv v1 v2 ty t Hty:
  (forall x, In x (gen_fv t) -> v1 x = v2 x) ->
  gen_rep v1 ty t Hty = gen_rep v2 ty t Hty.
Proof.
  generalize dependent t.
  generalize dependent ty.
  unfold gen_term, gen_type, gen_typed, gen_fv, gen_rep.
  destruct b; simpl in *; intros; [apply tm_change_vv | apply fmla_change_vv]; auto.
Qed.

Lemma gen_rep_irrel v1 ty d Hty1 Hty2:
  gen_rep v1 ty d Hty1 = gen_rep v1 ty d Hty2.
Proof.
  generalize dependent d.
  revert ty. unfold gen_rep. destruct b; simpl; intros;
  [apply term_rep_irrel | apply fmla_rep_irrel].
Qed.

End Gen.

Definition pat_matrix := list (list pattern * gen_term b).

(*Typing of Pattern Matrices*)
Section PatMatrixTyping.

(*Typing for row*)
Definition row_typed (tys: list vty) (p: list pattern) : Prop :=
  Forall2 (fun p t => pattern_has_type gamma p t) p tys.

Lemma row_typed_length {tys ps}:
  row_typed tys ps ->
  length tys = length ps.
Proof.
  unfold row_typed. intros Hall2.
  apply Forall2_length in Hall2; auto.
Qed.

Lemma row_typed_rev tys ps:
  row_typed tys ps ->
  row_typed (rev tys) (rev ps).
Proof.
  apply Forall2_rev.
Qed.


(*Typing for matrix*)
Definition pat_matrix_typed (tys: list vty) (p: pat_matrix) : Prop :=
  Forall (fun row => row_typed tys (fst row)) p /\
  Forall (fun row => @gen_typed gamma b (snd row) ret_ty) p.

Lemma pat_matrix_typed_tail {tys p ps}:
  pat_matrix_typed tys (p :: ps) ->
  pat_matrix_typed tys ps.
Proof.
  intros Hp. destruct Hp as [Hp1  Hp2]; inversion Hp1; inversion Hp2; subst; split; auto.
Qed.

Lemma pat_matrix_typed_head {tys p ps}:
  pat_matrix_typed tys (p :: ps) ->
  row_typed tys (fst p) /\ @gen_typed gamma b (snd p) ret_ty.
Proof.
  intros Hp. destruct Hp as [Hp1  Hp2]; inversion Hp1; inversion Hp2; subst; split; auto.
Qed.

Lemma pat_matrix_typed_app {tys: list vty} {p1 p2}:
  pat_matrix_typed tys p1 ->
  pat_matrix_typed tys p2 ->
  pat_matrix_typed tys (p1 ++ p2).
Proof.
  unfold pat_matrix_typed; rewrite !Forall_app; intros; destruct_all; auto.
Qed.

Lemma pat_matrix_typed_app_inv {tys p1 p2}:
  pat_matrix_typed tys (p1 ++ p2) ->
  pat_matrix_typed tys p1 /\ pat_matrix_typed tys p2.
Proof.
  unfold pat_matrix_typed.
  rewrite !Forall_app. intros; destruct_all; split_all; auto.
Qed.

Lemma prove_pat_matrix_typed_cons {tys p ps}:
  row_typed tys (fst p) ->
  @gen_typed gamma b (snd p) ret_ty ->
  pat_matrix_typed tys ps ->
  pat_matrix_typed tys (p :: ps).
Proof.
  intros. unfold pat_matrix_typed in *.
  destruct_all; split; constructor; auto.
Qed.

Lemma pat_matrix_typed_nil l:
  pat_matrix_typed l nil.
Proof.
  split; auto.
Qed.

End PatMatrixTyping.

(*Semantics of multiple pattern matching*)
Section MultipleMatchSemantics.
Variable (v: val_vars pd vt).

(*Much, much easier with Equations*)
Equations matches_row (tys: list vty) 
  (al: arg_list (domain (dom_aux pd)) (map (v_subst vt) tys))
  (p: list pattern) 
  (Htys: row_typed tys p) :
  option ((list (vsymbol * {s: sort & domain (dom_aux pd) s }))) :=
matches_row nil al nil Htys := Some [];
matches_row (t1 :: tys1) al (p :: ps) Htys :=
  option_bind ((match_val_single gamma_valid pd vt _ p (Forall2_inv_head Htys) (hlist_hd al)))
      (fun l => option_bind (matches_row tys1 (hlist_tl al) ps (Forall2_inv_tail Htys)) (fun l1 => Some (l ++ l1))).

(*Semantics for whole matrix matching*)
Equations matches_matrix  (tys: list vty) 
  (al: arg_list (domain (dom_aux pd)) (map (v_subst vt) tys))
  (p: pat_matrix)
  (Hty: pat_matrix_typed tys p) :
  option (gen_ret pd vt b ret_ty):=
matches_matrix tys al nil Hty := None;
matches_matrix tys al (row :: ps) Hty :=
  match (matches_row tys al (fst row) (Forall_inv (proj1 Hty))) with
    | Some l => Some (gen_rep (extend_val_with_list pd vt v l) ret_ty (snd row) (Forall_inv (proj2 Hty)))
    | None => matches_matrix tys al ps (pat_matrix_typed_tail Hty)
  end.

(*TODO (later): prove these equivalent to semantics in Denotational.v*)

(*One more version, when we start with terms*)
Equations terms_to_hlist (ts: list term) (tys: list vty)
  (Hty: Forall2 (fun t ty => term_has_type gamma t ty) ts tys) :
  arg_list (domain (dom_aux pd)) (map (v_subst vt) tys) :=
terms_to_hlist nil nil Hty := HL_nil _;
terms_to_hlist (t :: ts) (ty :: tys) Hty :=
  HL_cons _ _ _ (term_rep gamma_valid pd vt pf v t ty (Forall2_inv_head Hty)) 
    (terms_to_hlist ts tys (Forall2_inv_tail Hty)).
  (*Wow equations is magic*)

Definition matches_matrix_tms (tms: list term) (tys: list vty) (P: pat_matrix)
  (Hty: Forall2 (term_has_type gamma) tms tys)
  (Hp: pat_matrix_typed tys P) : option (gen_ret pd vt b ret_ty) :=
  matches_matrix tys (terms_to_hlist tms tys Hty) P Hp.

(*Some simple lemmas:*)

Lemma terms_to_hlist_tl t ts ty tys Hty:
  hlist_tl (terms_to_hlist (t :: ts) (ty :: tys) Hty) =
  terms_to_hlist ts tys (Forall2_inv_tail Hty).
Proof.
  simp terms_to_hlist. reflexivity.
Qed.

Lemma terms_to_hlist_irrel ts tys H1 H2:
  terms_to_hlist ts tys H1 = terms_to_hlist ts tys H2.
Proof.
  revert tys H1 H2. induction ts as [| tm ts IH]; simpl; intros [| ty1 tys];
  intros Hall1 Hall2; auto; try solve[inversion Hall1].
  simp terms_to_hlist.
  rewrite term_rep_irrel with (Hty2:=(Forall2_inv_head Hall2)).
  f_equal. apply IH.
Qed.

Lemma terms_to_hlist_app (tys1 tys2 : list vty) (tms1 tms2 : list term) Hty Hty1 Hty2:
  length tys1 = length tms1 ->
  terms_to_hlist (tms1 ++ tms2) (tys1 ++ tys2)  Hty =
  cast_arg_list (eq_sym (map_app (v_subst vt) tys1 tys2))
    (hlist_app _ _ _ (terms_to_hlist tms1 tys1 Hty1) (terms_to_hlist tms2 tys2 Hty2)).
Proof.
  intros Hlen.
  generalize dependent (eq_sym (map_app (v_subst vt) tys1 tys2)).
  generalize dependent tms1.
  induction tys1 as [| ty1 tys1 IH]; simpl; intros [| tm1 tms1]; intros; simpl; simp hlist_app; auto;
  try discriminate.
  - assert (e = eq_refl). { apply UIP_dec, list_eq_dec, sort_eq_dec.  } subst.
    erewrite terms_to_hlist_irrel. reflexivity.
  - simp terms_to_hlist.
    simp hlist_app.
    rewrite cast_arg_list_cons. erewrite IH; auto. f_equal.
    generalize dependent (cons_inj_hd e). intros Heq.
    assert (Heq = eq_refl). { apply UIP_dec, sort_eq_dec. } subst.
    simpl. apply term_rep_irrel.
Qed.

Lemma terms_to_hlist_rev tys tms Hty Htyrev:
  terms_to_hlist (rev tms) (rev tys) Htyrev =
  cast_arg_list (eq_sym (map_rev _ _))
    (hlist_rev _ _ (terms_to_hlist tms tys Hty)).
Proof.
  generalize dependent (eq_sym (map_rev (v_subst vt) tys)).
  revert Hty Htyrev.
  revert tms.
  induction tys as [| ty tys IH]; simpl; intros[| tm1 tms]; intros; simpl; try solve[inversion Hty].
  - simp hlist_rev. assert (e = eq_refl). { apply UIP_dec, list_eq_dec, sort_eq_dec. } subst.
    reflexivity.
  - simp terms_to_hlist. simp hlist_rev.
    rewrite terms_to_hlist_app with (Hty1:=Forall2_rev (Forall2_inv_tail Hty))
      (Hty2:=(Forall2_cons _ _ (Forall2_inv_head Hty) (Forall2_nil _))).
    2: { rewrite !rev_length; auto. apply Forall2_length in Hty. simpl in Hty. lia. }
    assert (Happeq: rev (map (v_subst vt) tys) = map (v_subst vt) (rev tys)).
    {
      rewrite map_app in e. simpl in e.
      apply app_inj_tail_iff in e. destruct_all; auto.
    }
    rewrite IH with (Hty:=(Forall2_inv_tail Hty))(e:=Happeq).
    simpl in *.
    rewrite hlist_app_cast1.
    simp terms_to_hlist. simpl.
    erewrite term_rep_irrel with (Hty2:=Forall2_inv_head Hty).
    rewrite cast_arg_list_compose.
    apply cast_arg_list_eq.
Qed.

Lemma matches_row_irrel tys h ps Hr1 Hr2:
  matches_row tys h ps Hr1 = matches_row tys h ps Hr2.
Proof.
  revert Hr1 Hr2.
  revert ps.
  induction tys as [| ty tys IH]; intros; assert (Hlen:=row_typed_length Hr1);
  destruct ps as [| phd ptl]; try discriminate; simp matches_row; [reflexivity|].
  rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hr2)).
  apply option_bind_ext.
  intros x. erewrite IH. reflexivity.
Qed.

(*TODO: do we really need both? Probably not; as this shows, they are the same*)
Lemma iter_arg_list_matches_row (tys: list vty) (ps: list pattern)
  (Hrow: row_typed tys ps)
  (Htys: Forall (fun x => pattern_has_type gamma (fst x) (snd x)) (combine ps tys))
  (a: arg_list (domain (dom_aux pd)) (map (v_subst vt) tys)):
  iter_arg_list gamma_valid pd tys a ps Htys =
  matches_row tys a ps Hrow.
Proof.
  revert Hrow Htys. revert ps. induction tys as [| thd ttl IH]; 
  intros [| phd ptl]; intros; auto; try solve[inversion Hrow].
  simp matches_row. simpl.
  rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hrow)).
  destruct_match_single m1 Hmatch1; auto.
  rewrite IH with (Hrow:=(Forall2_inv_tail Hrow)).
  reflexivity.
Qed.

Lemma matches_row_vars {tys al ps Hty l}:
  matches_row tys al ps Hty = Some l ->
  forall v, In v (map fst l) <-> In v (big_union vsymbol_eq_dec pat_fv ps).
Proof.
  intros Hmatch. generalize dependent l.
  generalize dependent ps. induction tys as [|ty1 tys IH]; simpl; intros [|phd ptl]; intros;
  try solve [inversion Hty]; simp matches_row in Hmatch.
  - inversion Hmatch; subst. reflexivity.
  - destruct (match_val_single _ _ _ _ phd _) as [m1|] eqn : Hmatch1; simpl in Hmatch; try discriminate.
    destruct (matches_row _ _ ptl _) as [m2|] eqn : Hmatch2; try discriminate. simpl in Hmatch.
    inversion Hmatch; subst. simpl.
    rewrite map_app, in_app_iff, union_elts,
      (match_val_single_free_var _ _ _ _ _ _ _ _ _ Hmatch1), (IH _ _ _ _ Hmatch2).
    reflexivity.
Qed.

Lemma matches_matrix_irrel tys al p Hty1 Hty2:
  matches_matrix tys al p Hty1 =
  matches_matrix tys al p Hty2.
Proof.
  revert Hty1 Hty2. induction p; simpl; auto.
  intros. simp matches_matrix.
  rewrite (matches_row_irrel) with (Hr2:=(Forall_inv (proj1 Hty2))).
  destruct (matches_row _ _ _ _); simpl; auto. f_equal.
  apply gen_rep_irrel.
Qed.

Lemma matches_matrix_app tys al P1 P2 Hp1 Hp2 Hp12:
  matches_matrix tys al (P1 ++ P2) Hp12 =
  match (matches_matrix tys al P1 Hp1) with
  | None => matches_matrix tys al P2 Hp2
  | x => x
  end.
Proof.
  revert Hp1 Hp2 Hp12. induction P1 as [| rhd P1' IH]; simpl; intros; auto;
  simp matches_matrix;[apply matches_matrix_irrel|].
  rewrite matches_row_irrel with (Hr2:=(Forall_inv (proj1 Hp1))).
  destruct (matches_row _ _ _ _); simpl; auto.
  f_equal. apply gen_rep_irrel.
Qed.

End MultipleMatchSemantics.

Section SpecDefaultLemmas.
Variable (v: val_vars pd vt).

(*Prove the key intermediate results for the S and D matrices.
  First, we give nicer definitions*)

Definition spec(P: pat_matrix) (c: funsym) : pat_matrix :=
  Pattern.filter_map (fun x =>
      let ps := fst x in
      let a := snd x in
      match ps with
      | p :: ps =>
        match p with
        | Pwild => Some (repeat Pwild (length (s_args c)) ++ ps, a)
        | Pconstr fs tys pats =>
            if funsym_eqb fs c then Some (rev pats ++ ps, a) else None
        | _ => None
        end
      | _ => None
      end
) P.

Definition default(P: pat_matrix) : pat_matrix :=
  Pattern.filter_map (fun x =>
    match (fst x) with
    | Pwild :: ps => Some (ps, snd x)
    | _ => None
    end ) P.

(*The specifications: let ts = t :: tl. By typing, know [[t]] = [[c]](al)
  1. If c is in first column of P, then [[match((rev al) ++ [[tl]], S(P, c))]] = 
    [[match(ts, P)]] 
  2. If c is not in the first column of P, then [[match(tl, D(P, c))]] = [[match(ts, P)]]*)

(*A predicate that says "term t has semantic meaning c(al), where c is a constructor
  in ADT a in mutual m"*)
Definition tm_semantic_constr (t: term) {m: mut_adt} (m_in : mut_in_ctx m gamma)
  {a: alg_datatype} (a_in: adt_in_mut a m) {c: funsym} (c_in: constr_in_adt c a) 
  {args: list vty} (args_len: length args = length (m_params m))
  (Hty: term_has_type gamma t (vty_cons (adt_name a) args))
  (al: arg_list (domain (dom_aux pd)) (sym_sigma_args c (map (v_subst vt) args)))
   : Prop :=
  (*[[t]] =*)
  term_rep gamma_valid pd vt pf v t _ Hty = dom_cast (dom_aux pd) (*Need 2 casts*)
    (eq_sym (v_subst_cons (adt_name a) args)) 
  (scast 
    (eq_sym (adts pd m (map (v_subst vt) args) a a_in))
  (* [[c]](al)*)
  (constr_rep gamma_valid m m_in 
    (map (v_subst vt) args) (eq_trans (map_length _ _) args_len) (dom_aux pd) a a_in 
      c c_in (adts pd m (map (v_subst vt) args)) 
         al)).

(*If a term has type a(args) for ADT a, then we can find the constructor and arguments
  that its term_rep is equal to. This is a nicer, higher level interface for [find_constr_rep];
  it is a straightforward application*)
Lemma find_semantic_constr (t: term) {m: mut_adt} (m_in : mut_in_ctx m gamma)
  {a: alg_datatype} (a_in: adt_in_mut a m)  
  {args: list vty} (args_len: length args = length (m_params m))
  (Hty: term_has_type gamma t (vty_cons (adt_name a) args)) :
  {f : funsym & {Hf: constr_in_adt f a * arg_list (domain (dom_aux pd)) (sym_sigma_args f (map (v_subst vt) args))
    |  tm_semantic_constr t m_in a_in (fst Hf) args_len Hty (snd Hf) }}.
Proof.
  unfold tm_semantic_constr.
  assert (srts_len: length (map (v_subst vt) args) = length (m_params m)) by (rewrite map_length; auto).
  assert (Hunif: uniform m) by (apply (gamma_all_unif gamma_valid); auto). 
  (*Of course, use [find_constr_rep]*)
  destruct (find_constr_rep gamma_valid _ m_in (map (v_subst vt) args) srts_len (dom_aux pd) a a_in
    (adts pd m (map (v_subst vt) args)) Hunif
    (scast (adts pd m (map (v_subst vt) args) a a_in) (dom_cast (dom_aux pd) (v_subst_cons (adt_name a) args) 
      (term_rep gamma_valid pd vt pf v t
  (vty_cons (adt_name a) args) Hty)))) as [f [[c_in al] Hrep]]. simpl in Hrep.
  apply (existT _ f).
  apply (exist _ (c_in , al)). simpl.
  assert (Heq: srts_len = (eq_trans (map_length (v_subst vt) args) args_len)). { apply UIP_dec, Nat.eq_dec.  }
  subst.
  rewrite <- Hrep, scast_eq_sym.
  unfold dom_cast.
  rewrite <- eq_sym_map_distr, scast_eq_sym.
  reflexivity.
Qed.

Section SpecProof.

(*TODO: write this up more formally and remove comment in Coq code*)
(*The specialization proof is very involved. Recall that we want to prove
  that [[match((rev al) ++ [[tl]], S(P, c))]] = [[match(ts, P)]] if c is in the first column.
  We first consider the case when P is (c(ps) :: ptl) :: P'.
  Then S(P, c) = ((rev ps) ++ ptl) :: P'.
  For the LHS, we have that [[match(rev al ++ [tl], S(P, c))]] is decomposed into
    (match_row (rev al ++ [tl], (rev ps ++ ptl))) and (match(rev al ++ [tl], P'))
    We prove (1) that we can split up the first [match_row] into
    (match_row(rev al, rev ps)) and (match_row [tl], ptl)
    We then prove (2) that [match_row(rev al, rev ps)] is a permutation of [match_row(al, ps)]
      (NOTE: it is NOT true that they are equal)
  For the RHS, we have that [[match(ts, P)]] is decomposed into
    (match_row (t :: tl, (c(ps) :: ptl))) and (match(t :: tl, P'))
    the first [match_row] simplifies to [match_val_single c(ps) (term_rep t)]
      and (match_row(tl, ptl))
    We then prove (3) that [match_val_single c(ps) (term_rep t)], when [[t]] = c(al)
      equals [match_row(al, ps)] (i.e. we just match the arguments)
  Thus, we have that both sides are equivalent up to a permutation of the first list
  (from [match_row(al, ps)] = [match_val_single c(ps) (term_rep t)])
  Finally, we use known properties (NoDup) of [match_val_single] to show that the
  resulting valuation is equal, and conclude using the IH.

  Simple case: if c'(ps) where c!=c', need (4) that [match_val_single] is None here,
    and the rest is easy

  In the second case, P = (Pwild :: ptl) :: P'.
  Then S(P, c) = (repeat Pwild m ++ ptl) :: P'. (where m is the size of (s_args c)/al)
  For the LHS, we have that [[match(rev al) ++ [tl], (repeat Pwild m ++ ptl) :: P']]
  decomposes into (match_row (rev al ++ [tl], repeat Pwild m ++ ptl)) and 
    (match((rev al) ++ [tl], P')).
    The first row is again decomposed by (1) into (match_row(rev al, repeat Pwild m))
      and (match_row([tl], ptl)).
    We prove (5) that the first [match_row] is Some [] because all patterns are wilds.
  For the RHD, we have that [[match(t :: tl, (Pwild :: ptl) :: P')]] is decomposed int
    (match_row(t :: tl, Pwild :: ptl)) and (match(t :: tl, P'))
    The first simplifies to [match_val_single Pwild (term_rep t)] and (match_row(tl, ptl))
    and the [match_val_single] simplifies to Some [] as well. Thus, we get the desired equality.

Therefore, we need 4 intermediate lemmas:
(1) decomposing [match_row] for [app]
(2) relating [match_val_single c(ps) [[t]]] with [match_row ps al] where [[t]] = c(al)
(3) relating [match_row(l1, l2)] and [match_row(rev l1, rev l2)] (permutation)
(4) if [[t]] = c(al), then [match_val_single c'(ps), [[t]]] = None
(5) proving that matching a row of all wildcards gives Some []*)


(*1. Decompose [match_row] for [app]*)

(*Technically works for anything associative, can change*)
Lemma option_bind_appcomp {A: Type} (o1 o2: option (list A)) (m: list A):
  option_bind (option_bind o1 (fun x => option_bind o2 (fun y => Some (x ++ y)))) (fun x => Some (m ++ x)) =
  option_bind (option_bind o1 (fun x => Some (m ++ x))) (fun y => option_bind o2 (fun x => Some (y ++ x))).
Proof.
  destruct o1; destruct o2; simpl; auto.
  rewrite app_assoc. reflexivity.
Qed.

Lemma matches_row_app (tys1 tys2: list vty) 
  (h1: arg_list (domain (dom_aux pd)) (map (v_subst vt) tys1))
  (h2: arg_list (domain (dom_aux pd)) (map (v_subst vt) tys2))
  (h3: arg_list (domain (dom_aux pd)) (map (v_subst vt) (tys1 ++ tys2)))
  (Hheq: h3 = cast_arg_list (eq_sym (map_app _ _ _)) (hlist_app _ _ _ h1 h2))
  (ps1 ps2: list pattern)
  (Hlen1: length tys1 = length ps1)
  (Hlen2: length tys2 = length ps2)
  (Hr1: row_typed (tys1 ++ tys2) (ps1 ++ ps2))
  (*duplicate*)
  (Hr2: row_typed tys1 ps1)
  (Hr3: row_typed tys2 ps2):
  matches_row (tys1 ++ tys2) h3 (ps1 ++ ps2) Hr1 =
  option_bind (matches_row tys1 h1 ps1 Hr2) (fun l => 
    option_bind (matches_row tys2 h2 ps2 Hr3) (fun l1 => Some (l ++ l1))).
Proof.
  generalize dependent (eq_sym (map_app (v_subst vt) tys1 tys2)).
  revert Hr1 Hr2 Hr3.
  generalize dependent Hlen1. revert ps1. induction tys1 as [| ty tys1 IH]; simpl.
  - intros ps1 Hlen1. destruct ps1; try discriminate. simpl.
    intros. subst. simp matches_row. simpl. simp hlist_app.
    rewrite option_bind_id.
    assert (e = eq_refl) by (apply UIP_dec, list_eq_dec, sort_eq_dec).
    subst. unfold cast_arg_list; simpl.
    apply matches_row_irrel.
  - intros [| phd ps1] Hlen1; try discriminate. intros. subst. simpl.
    simp matches_row.
    rewrite hlist_hd_cast with (Heq2:=eq_refl). simpl.
    rewrite (hlist_hd_app1 (v_subst vt ty)) .
    rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hr2)).
    simpl in *.
    (*Unfortunately, for some reason Coq cannot unify the two*)
    destruct_match_single m1 Hmatch1.
    + (*fails: rewrite Hmatch1*) (*Can't even refer to other one*)
      match goal with |- context [match_val_single ?v ?pd ?vt ?ty ?phd ?H1 ?h1] =>
        replace (match_val_single v pd vt ty phd H1 h1) with (Some m1)
      end.
      erewrite IH with (h1:=hlist_tl h1) (Hr2:=(Forall2_inv_tail Hr2)) (Hr3:=Hr3); simpl.
      * (*Same problem again - this time, we prove a lemma*)
        apply option_bind_appcomp.
      * lia.
      * rewrite hlist_tl_cast.
        rewrite (hlist_tl_app1 (v_subst vt ty)). reflexivity.
    + match goal with |- context [match_val_single ?v ?pd ?vt ?ty ?phd ?H1 ?h1] =>
        replace (match_val_single v pd vt ty phd H1 h1) with (@None (list (vsymbol * {s : sort & domain (dom_aux pd) s})))
      end.
      reflexivity.
Qed.

(*2. if we have a constructor which matches,
  then [match_val_single] is the same as [matches_row] on the argument list.
  This lemma needs UIP*)
Lemma match_val_single_constr_row 
  (t: term) {m: mut_adt} (m_in : mut_in_ctx m gamma)
  {a: alg_datatype} (a_in: adt_in_mut a m) {c: funsym} (c_in: constr_in_adt c a) 
  {args: list vty} (args_len: length args = length (m_params m))
  (Hty: term_has_type gamma t (vty_cons (adt_name a) args))
  (al1: arg_list (domain (dom_aux pd)) (sym_sigma_args c (map (v_subst vt) args)))
  (Ht: tm_semantic_constr t m_in a_in c_in args_len Hty al1)
  params tms 
  (Hp :  pattern_has_type gamma (Pconstr c params tms) (vty_cons (adt_name a) args)) 
  (Hty1 : term_has_type gamma t (vty_cons (adt_name a) args)) Heq
  (Hrow: row_typed (ty_subst_list (s_params c) args (s_args c)) tms):
  match_val_single gamma_valid pd vt (vty_cons (adt_name a) args) (Pconstr c params tms) Hp 
    (term_rep gamma_valid pd vt pf v t (vty_cons (adt_name a) args) Hty1) =
  matches_row (ty_subst_list (s_params c) args (s_args c))
    (cast_arg_list Heq al1) tms Hrow.
Proof.
  rewrite match_val_single_rewrite.
  set (ty1:= (vty_cons (adt_name a) args)) in *.
  generalize dependent (@is_vty_adt_some gamma ty1).
  generalize dependent (@adt_vty_length_eq gamma gamma_valid ty1).
  generalize dependent (@constr_length_eq gamma gamma_valid ty1).
  assert (Hisadt: is_vty_adt gamma ty1 = Some (m, a, args)) by
    (apply is_vty_adt_iff; auto).
  rewrite Hisadt.
  intros Hvslen1 Hvslen2 Hadtspec.
  destruct (Hadtspec m a args eq_refl)
    as [Htyeq [Hinmut Hinctx]].
  assert (Hinmut = a_in) by (apply bool_irrelevance).
  assert (Hinctx = m_in) by (apply bool_irrelevance).
  subst.
  simpl.
  generalize dependent (Hvslen2 m a args eq_refl
  (pat_has_type_valid gamma (Pconstr c params tms) ty1 Hp)).
  intros.
  assert (e = args_len) by (apply UIP_dec, Nat.eq_dec). subst.
  (*We need to know things about the [find_constr_rep]. *)
  case_find_constr.
  intros s.
  destruct s as [f' Hf']. destruct Hf' as [[f_in1 arg1] Haarg]. simpl in *; subst.
  (*Need info about how [tm_semantic_constr] interacts with this [find_constr_rep]*)
  unfold tm_semantic_constr in Ht.
  erewrite term_rep_irrel in Haarg.
  unfold ty1 in Haarg.
  rewrite Ht in Haarg.
  unfold dom_cast in Haarg.
  rewrite !scast_scast in Haarg. 
  revert Haarg.
  match goal with |- context [scast ?E ?x] => generalize dependent E end.
  intros Heq1.
  rewrite scast_refl_uip; intros Hconstr.
  (*Then, know f' = c and arg1 = al by disjointness/injectivity*)
  destruct (funsym_eq_dec f' c); [|apply constr_rep_disjoint in Hconstr; auto; contradiction].
  subst.
  assert (f_in1 = c_in) by (apply bool_irrelevance). subst.
  apply constr_rep_inj in Hconstr; auto; [|apply (gamma_all_unif gamma_valid); auto].
  subst. clear Heq1. simpl.
  (*Now it is simple: prove that [matches_row] and [iter_arg_list] are equal
    (TODO: do we really need both? Prob not) *)
  match goal with | |- context [cast_arg_list ?Heq ?x] => generalize dependent Heq end.
  (*Why we needed to state the lemma with this exact type/cast for the matches_row: we need
    these two equality proofs to be equal - we CANNOT have casting
    Reason: in [match_val_single], it is NOT enough to know that val(ty1) = val(ty2), the
    types must be equal (say, if one is a variable that maps to same ADT as another, different
    result from matching)*)
  intros Heq1. assert (Heq = Heq1) by (apply UIP_dec, list_eq_dec, sort_eq_dec).
  subst.
  apply iter_arg_list_matches_row.
Qed.

(*4. If the [term_rep] matches a different constructor [match_val_single] gives None*)
Lemma match_val_single_constr_nomatch
  (t: term) {m: mut_adt} (m_in : mut_in_ctx m gamma)
  {a: alg_datatype} (a_in: adt_in_mut a m) {c1 c2: funsym} (c1_in: constr_in_adt c1 a) 
  {args: list vty} (args_len: length args = length (m_params m))
  (Hty: term_has_type gamma t (vty_cons (adt_name a) args))
  (al1: arg_list (domain (dom_aux pd)) (sym_sigma_args c1 (map (v_subst vt) args)))
  (Ht: tm_semantic_constr t m_in a_in c1_in args_len Hty al1)
  params tms 
  (Hp :  pattern_has_type gamma (Pconstr c2 params tms) (vty_cons (adt_name a) args)) 
  (Hty1 : term_has_type gamma t (vty_cons (adt_name a) args)) 
  (Hneq: c1 <> c2):
  match_val_single gamma_valid pd vt (vty_cons (adt_name a) args) (Pconstr c2 params tms) Hp 
    (term_rep gamma_valid pd vt pf v t (vty_cons (adt_name a) args) Hty1) =
  None.
Proof.
  rewrite match_val_single_rewrite.
  set (ty1:= (vty_cons (adt_name a) args)) in *.
  generalize dependent (@is_vty_adt_some gamma ty1).
  generalize dependent (@adt_vty_length_eq gamma gamma_valid ty1).
  generalize dependent (@constr_length_eq gamma gamma_valid ty1).
  assert (Hisadt: is_vty_adt gamma ty1 = Some (m, a, args)) by
    (apply is_vty_adt_iff; auto).
  rewrite Hisadt.
  intros Hvslen1 Hvslen2 Hadtspec.
  destruct (Hadtspec m a args eq_refl)
    as [Htyeq [Hinmut Hinctx]].
  assert (Hinmut = a_in) by (apply bool_irrelevance).
  assert (Hinctx = m_in) by (apply bool_irrelevance).
  subst.
  simpl.
  generalize dependent (Hvslen2 m a args eq_refl
  (pat_has_type_valid gamma (Pconstr c2 params tms) ty1 Hp)).
  intros.
  assert (e = args_len) by (apply UIP_dec, Nat.eq_dec). subst.
  (*We need to know things about the [find_constr_rep]. *)
  case_find_constr.
  intros s.
  destruct s as [f' Hf']. destruct Hf' as [[f_in1 arg1] Haarg]. simpl in *; subst.
  (*Need info about how [tm_semantic_constr] interacts with this [find_constr_rep]*)
  unfold tm_semantic_constr in Ht.
  erewrite term_rep_irrel in Haarg.
  unfold ty1 in Haarg.
  rewrite Ht in Haarg.
  unfold dom_cast in Haarg.
  rewrite !scast_scast in Haarg. 
  revert Haarg.
  match goal with |- context [scast ?E ?x] => generalize dependent E end.
  intros Heq1.
  rewrite scast_refl_uip; intros Hconstr.
  (*Result follows by disjointness*)
  destruct (funsym_eq_dec f' c2); auto.
  subst. apply constr_rep_disjoint in Hconstr; auto. contradiction.
Qed.

(*3. We can reverse the lists in [match_row]; the result is a permutation*)

Definition opt_related {A B: Type} (P: A -> B -> Prop) (o1: option A) (o2: option B) : Prop :=
  match o1, o2 with
  | Some x, Some y => P x y
  | None, None => True
  | _, _ => False
  end.

(*The relationship is annoying: they are permutations*)
Lemma matches_row_rev tys al ps Hty1 Hty2:
  opt_related (@Permutation _) 
    (matches_row tys al ps Hty1)
    (matches_row (rev tys) 
    (cast_arg_list (eq_sym (map_rev _ _)) (hlist_rev _ _ al)) (rev ps) Hty2).
Proof.
  generalize dependent (eq_sym (map_rev (v_subst vt) tys)).
  revert Hty1 Hty2.
  revert ps. induction tys as [| ty1 tys IH]; simpl; intros [| p1 ps]; simpl; intros; auto;
  try solve[inversion Hty1];  unfold opt_related; simp matches_row; auto.
  assert (Hty2':=Hty2).
  assert (Hlen: length ps = length tys). {
    inversion Hty1; subst. eapply Forall2_length; eauto.
  }
  apply Forall2_app_inv in Hty2'; [| rewrite !rev_length; auto].
  destruct Hty2' as [Hrowrev Hrowhd].
  (*Need correct typecast*)
  set (h2:=(HL_cons (domain (dom_aux pd)) (v_subst vt ty1) (map (v_subst vt) nil) 
    (hlist_hd al) (HL_nil _)) : arg_list (domain (dom_aux pd)) (map (v_subst vt) [ty1])).

  rewrite matches_row_app with (h1:=cast_arg_list (eq_sym (map_rev _ _)) 
    (hlist_rev _ (map (v_subst vt) tys) (hlist_tl al)))(h2:=h2)(Hr2:=Hrowrev)(Hr3:=Hrowhd); auto.
  3: rewrite !rev_length; auto.
  2: {
    rewrite hlist_app_cast1. rewrite !cast_arg_list_compose.
    simpl in *. rewrite (hlist_inv al) at 1.
    simp hlist_rev. simpl.
    apply cast_arg_list_eq.
  }
  simp matches_row. simpl.
  (*Using the IH is a bit complicated*)
  unfold option_bind.
  specialize (IH (hlist_tl al) ps (Forall2_inv_tail Hty1) Hrowrev (eq_sym (map_rev (v_subst vt) tys))).
  unfold opt_related in IH.
  (*Now lots of destructing*)
  destruct (matches_row tys (hlist_tl al) ps
    (Forall2_inv_tail Hty1)) as [m1|] eqn : Hmatch1.
  - destruct (matches_row (rev tys)
      (cast_arg_list (eq_sym (map_rev (v_subst vt) tys))
      (hlist_rev (domain (dom_aux pd)) (map (v_subst vt) tys)
      (hlist_tl al)))
      (rev ps) Hrowrev) as [m2|] eqn : Hmatch2; [|contradiction].
    (*Left with only [match_val_single]*)
    rewrite match_val_single_irrel with (Hval2:=Forall2_inv_head Hrowhd).
    destruct (match_val_single gamma_valid pd vt ty1 p1
      (Forall2_inv_head Hrowhd) (hlist_hd al)); auto.
    rewrite app_nil_r. eapply Permutation_trans. apply Permutation_app_comm.
    apply Permutation_app_tail; assumption.
  - destruct (matches_row (rev tys)
      (cast_arg_list (eq_sym (map_rev (v_subst vt) tys))
      (hlist_rev (domain (dom_aux pd)) (map (v_subst vt) tys)
      (hlist_tl al)))
      (rev ps) Hrowrev) as [m2|] eqn : Hmatch2; [contradiction|].
    destruct (match_val_single gamma_valid pd vt ty1 p1
      (Forall2_inv_head Hty1) (hlist_hd al)); auto.
Qed.

(*5. If a pattern list is all wilds, everything matches it and gives no bound vars*)
Lemma matches_row_all_wilds tys h ps Hty (Hall: forall p, In p ps -> p = Pwild):
  matches_row tys h ps Hty = Some [].
Proof.
  generalize dependent ps.
  induction tys; simpl in *; intros [| p ps]; intros; try solve[inversion Hty]; auto.
  simp matches_row. simpl in Hall.
  assert (p = Pwild) by (apply Hall; auto). subst. simpl.
  rewrite IHtys; auto.
Qed.

(*Finally, a few small results about [extend_val_with_list] - TODO move these*)

Lemma get_assoc_list_app {A B: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y}) (l1 l2: list (A * B)) (x: A):
  get_assoc_list eq_dec (l1 ++ l2) x =
  match (get_assoc_list eq_dec l1 x) with
  | Some y => Some y
  | _ => get_assoc_list eq_dec l2 x
  end.
Proof.
  induction l1 as [| [x1 y1] t1]; simpl; auto.
  destruct (eq_dec x x1); subst; auto.
Qed.

Lemma extend_val_app l1 l2 x:
  extend_val_with_list pd vt v (l1 ++ l2) x =
  if in_dec vsymbol_eq_dec x (map fst l1) then
    extend_val_with_list pd vt v l1 x
  else extend_val_with_list pd vt v l2 x.
Proof.
  unfold extend_val_with_list.
  rewrite get_assoc_list_app.
  destruct (get_assoc_list vsymbol_eq_dec l1 x) eqn : Hsome; simpl;
  destruct (in_dec vsymbol_eq_dec x (map fst l1)); auto.
  - apply get_assoc_list_some in Hsome.
    exfalso; apply n; rewrite in_map_iff; exists (x, s); auto.
  - apply get_assoc_list_none in Hsome. contradiction.
Qed.

Lemma extend_val_perm l1 l2 x:
  NoDup (map fst l1) ->
  Permutation l1 l2 ->
  extend_val_with_list pd vt v l1 x = extend_val_with_list pd vt v l2 x.
Proof.
  intros Hn Hp.
  destruct (in_dec vsymbol_eq_dec x (map fst l1)) as [Hin | Hnotin].
  - rewrite in_map_iff in Hin. destruct Hin as [[x1 d1] [Hx Hinx1]]; simpl in *; subst.
    rewrite !extend_val_lookup with (t:=d1); auto.
    + eapply Permutation_NoDup. apply Permutation_map. apply Hp. auto.
    + eapply Permutation_in. apply Hp. auto.
  - rewrite !extend_val_notin; auto.
    erewrite perm_in_iff. apply Hnotin. apply Permutation_sym, Permutation_map; auto.
Qed.

(*The exact one we need*)
Lemma extend_val_app_perm m1 m2 m3 x:
NoDup (map fst m1) ->
Permutation m1 m2 ->
extend_val_with_list pd vt v (m1 ++ m3) x =
extend_val_with_list pd vt v (m2 ++ m3) x.
Proof.
  intros Hn Hperm.
  rewrite !extend_val_app.
  assert (Hiff: In x (map fst m1) <-> In x (map fst m2)). {
    apply perm_in_iff, Permutation_map; auto.
  }
  destruct (in_dec vsymbol_eq_dec x (map fst m1)) as [Hin1 | Hnotin1];
  destruct (in_dec vsymbol_eq_dec x (map fst m2)) as [Hin2 | Hnotin2]; auto.
  - apply extend_val_perm; auto.
  - apply Hiff in Hin1; contradiction.
  - apply Hiff in Hin2; contradiction.
Qed. 

(*An easy cast, just a bunch of maps, revs, and apps together*)
Lemma spec_prop_cast c  args tys : 
  length (s_params c) = length args ->
  rev (sym_sigma_args c (map (v_subst vt) args)) ++
map (v_subst vt) tys =
map (v_subst vt)
  (rev (ty_subst_list (s_params c) args (s_args c)) ++
tys).
Proof.
  intros Hlen.
  unfold sym_sigma_args, ty_subst_list, ty_subst_list_s.
  rewrite map_app. f_equal.
  rewrite !map_rev, !map_map. f_equal. apply map_ext.
  intros. symmetry. apply funsym_subst_eq; auto. apply s_params_Nodup.
Qed.


(*And we can finally prove the result for S(c, P)*)
Theorem spec_match_eq 
  (*Info about first term*)
  (t: term) {m: mut_adt} (m_in : mut_in_ctx m gamma)
  {a: alg_datatype} (a_in: adt_in_mut a m) {c: funsym} (c_in: constr_in_adt c a) 
  {args: list vty} (args_len: length args = length (m_params m))
  (params_len: length (s_params c) = length args)
  (Hty: term_has_type gamma t (vty_cons (adt_name a) args))
  (al1: arg_list (domain (dom_aux pd)) (sym_sigma_args c (map (v_subst vt) args)))
  (Ht: tm_semantic_constr t m_in a_in c_in args_len Hty al1)
  (*Info about rest of terms*)
  (ts: list term) (tys: list vty)
  (Htsty: Forall2 (term_has_type gamma) (t :: ts) (vty_cons (adt_name a) args :: tys)) (*duplicate proof for irrelevance*)
  (*Info about pattern matrix*)
  (P: pat_matrix) (Hpsimp: simplified P)
  (Htyp: pat_matrix_typed (vty_cons (adt_name a) args :: tys) P)
  (Htyp': pat_matrix_typed (rev (ty_subst_list (s_params c) args (s_args c)) ++ tys)
    (spec P c)):

  matches_matrix_tms v (t :: ts) (vty_cons (adt_name a) args :: tys) P
    Htsty Htyp =

  matches_matrix v
  (*Type list more complicated: args of c + rest*)
  (rev (ty_subst_list (s_params c) args (s_args c)) ++ tys)
    (cast_arg_list (spec_prop_cast c args _ params_len)
   (hlist_app _ _ _ (hlist_rev _ _ al1) (terms_to_hlist v ts tys (Forall2_inv_tail Htsty))))
    (spec P c) Htyp'.
Proof.
  unfold matches_matrix_tms.
  generalize dependent (spec_prop_cast c args tys params_len).
  generalize dependent (Forall2_inv_tail Htsty).
  revert Htsty Htyp Htyp'.
  unfold matches_matrix_tms. 
  induction P as [| rhd rtl]; intros; simpl; simp matches_matrix; [reflexivity|].
  destruct rhd as [ps a1]; simpl.

  (*Useful "inversion" on equality proof*)
  assert (Heq1: rev (sym_sigma_args c (map (v_subst vt) args)) =
          (map (v_subst vt) (rev (ty_subst_list (s_params c) args (s_args c))))).
  {
    rewrite map_app in e.
    apply app_inv_tail in e. auto.
  }
  assert (Heq2: sym_sigma_args c (map (v_subst vt) args) =
          map (v_subst vt) (ty_subst_list (s_params c) args (s_args c))).
  {
    rewrite map_app in e. apply app_inv_tail in e.
    rewrite map_rev in e.
    apply rev_inj in e. auto.
  }

  (*Case on patterns*)
  destruct ps as [| phd ptl].
  - assert (Htyph:=Htyp). apply pat_matrix_typed_head in Htyph.
    simpl in Htyph. destruct Htyph as [Hrow _]; inversion Hrow. 
  - destruct phd as [| f' params tms | | |]; try discriminate.
    + (*Interesting case: Pconstr*) 
      revert Htyp'. simpl.

      (*Info from typing*)
      assert (Htyt:=pat_matrix_typed_head Htyp).
      destruct Htyt as [Htyr Htyt]; simpl in Htyr.
      assert (Htyconstr:=Forall2_inv_head Htyr).
      assert (Hlentms: length (s_args f') = length tms) by (inversion Htyconstr; auto).

      destruct (funsym_eqb_spec f' c); subst; simpl; intros.
      -- simp matches_matrix. simpl.
        (*Step 1: decompose [matches_row] and [app]*)
      
        (*Get [row_typed] info*)
        assert (Hr1:=pat_matrix_typed_head Htyp'). simpl in Hr1.
        destruct Hr1 as [Hr1 _].
        apply Forall2_app_inv in Hr1.
        2: {  unfold sorts_to_tys, ty_subst_list.
          rewrite !rev_length, !map_length. auto. }
        destruct Hr1 as [Hrow1 Hrow2].
        (*Now we can split the [app]*)
        rewrite matches_row_app with(h1:=cast_arg_list Heq1 (hlist_rev _ _ al1))(h2:=terms_to_hlist v ts tys f)
          (Hr2:=Hrow1)(Hr3:=Hrow2).
        (*We prove the easy goals first*)
        2: rewrite hlist_app_cast1, cast_arg_list_compose; apply cast_arg_list_eq.
        2: unfold ty_subst_list; rewrite !rev_length, map_length; auto.
        2: symmetry; apply (Forall2_length (Forall2_inv_tail Htyr)).

        (*Now we need to transform the [matches_row] into the corresponding
          [match_val_single] and the rest of the row; we then prove that
          [match_val_single] for a constructor is equivalent to [matches_row] 
          on the arg_list*)
        simp matches_row. simp terms_to_hlist. simpl hlist_hd.
        (*Coq is just awful at unifying things; this is really annoying*)
        match goal with
        | |- context [match_val_single ?v ?pd ?vt ?ty ?p ?Hp (term_rep _ _ _ _ _ _ _ ?Hty)] =>
          pose proof (match_val_single_constr_row _ m_in a_in c_in args_len _ al1 Ht params tms
          Hp Hty Heq2 (Forall2_rev_inv Hrow1)) as Hconstreq; rewrite Hconstreq
        end.
        (*Remove the [rev] by using the permutation result*)
        pose proof (matches_row_rev (ty_subst_list (s_params c) args (s_args c)) 
          (cast_arg_list Heq2 al1) tms (Forall2_rev_inv Hrow1)
          Hrow1) as Hrev.
        unfold opt_related in Hrev.
        assert (Heqarglist: cast_arg_list (eq_sym (map_rev _ _))
            (hlist_rev _  _ (cast_arg_list Heq2 al1)) =
            cast_arg_list Heq1 (hlist_rev _ _ al1)).
          {
            rewrite hlist_rev_cast.
            rewrite cast_arg_list_compose.
            apply cast_arg_list_eq.
          }
        rewrite Heqarglist in Hrev. clear Heqarglist.
        (*Now, time to destruct everything*)
        destruct (matches_row (ty_subst_list (s_params c) args (s_args c))
          (cast_arg_list Heq2 al1) tms (Forall2_rev_inv Hrow1)) as [m1 |] eqn : Hmatch1.
        ++ simpl.
          destruct (matches_row
            (rev (ty_subst_list (s_params c) args (s_args c)))
            (cast_arg_list Heq1
            (hlist_rev (domain (dom_aux pd))
            (sym_sigma_args c (map (v_subst vt) args)) al1))
            (rev tms) Hrow1) as [m2 |] eqn : Hm2; [| contradiction].
          simpl.
          (*Now, some proof irrelevance to show equality of the next two matches*)
          rewrite terms_to_hlist_irrel with (H2:=f).
          rewrite matches_row_irrel with (Hr2:=Hrow2).
          destruct (matches_row tys (terms_to_hlist v ts tys f) ptl Hrow2) as [m3|] eqn : Hmatch3; simpl.
          ** (*Here, use permutation result*) 
            assert (Hn: NoDup (map fst m1)). {
              eapply match_val_single_nodup. apply Hconstreq.
            } 
            f_equal. rewrite gen_rep_irrel with (Hty2:=(Forall_inv (proj2 Htyp'))). 
            apply gen_rep_change_vv.
            intros x Hinx.
            apply extend_val_app_perm; assumption.
          ** (*IH case*)
            erewrite <- IHrtl with (Htyp:=(pat_matrix_typed_tail Htyp))(Htsty:=Htsty); [| apply 
              (simplified_tl _ _ Hpsimp)].
            simp terms_to_hlist.
            erewrite terms_to_hlist_irrel; reflexivity.
        ++ (*first match is None - by Hrev, know second is as well*)
          destruct (matches_row
            (rev (ty_subst_list (s_params c) args (s_args c)))
            (cast_arg_list Heq1
            (hlist_rev (domain (dom_aux pd))
            (sym_sigma_args c (map (v_subst vt) args)) al1))
            (rev tms) Hrow1) as [m2 |] eqn : Hm2; [contradiction|].
          simpl.
          (*Another IH case*)
          erewrite <- IHrtl with (Htyp:=(pat_matrix_typed_tail Htyp))(Htsty:=Htsty); [| apply 
              (simplified_tl _ _ Hpsimp)].
          simp terms_to_hlist.
          erewrite terms_to_hlist_irrel; reflexivity. Unshelve. auto.
      -- (*funsym doesn't match - here, we do not have a match with the [match_val_single]*)
        simp matches_row terms_to_hlist. simpl hlist_hd. 
        (*Use nomatch result*) 
        rewrite match_val_single_constr_nomatch with (m_in := m_in) (a_in:=a_in)(c1_in:=c_in)
          (args_len:=args_len)(al1:=al1)(Hty:=Hty); auto.
        simpl.
        (*Thus, IH case*)
        erewrite <- IHrtl with (Htyp:=(pat_matrix_typed_tail Htyp))(Htsty:=Htsty); [| apply 
              (simplified_tl _ _ Hpsimp)].
        simp terms_to_hlist.
        erewrite terms_to_hlist_irrel; reflexivity. Unshelve. auto.
    + (*Pwild case*) 
      (*Idea: we add n terms and n wilds, that is the same (always matches) as 1 term and 1 wild*)
      simp matches_row matches_matrix. simpl.
      (*First, some typing*)
      assert (Htyp'':=Htyp').
      apply pat_matrix_typed_head in Htyp''. simpl in Htyp''.
      destruct Htyp'' as [Hrowty _].
      apply Forall2_app_inv in Hrowty.
      2: {
        rewrite repeat_length, rev_length.
        unfold ty_subst_list.
        rewrite !map_length. reflexivity.
      }
      destruct Hrowty as [Hr1 Hr2].
      (*Again decompose the row via append*)
      simpl.
      rewrite matches_row_app  with (h1:=cast_arg_list Heq1 (hlist_rev (domain (dom_aux pd))
          (sym_sigma_args c (map (v_subst vt) args)) al1) )
        (h2:=(terms_to_hlist v ts tys f))(Hr2:=Hr1)(Hr3:=Hr2).
      (*First, prove the side conditions*)
      2: {
        rewrite (hlist_app_cast1) with (Heq:=Heq1).
        rewrite !cast_arg_list_compose.
        apply cast_arg_list_eq.
      }
      2: {
        rewrite repeat_length.
        unfold ty_subst_list. rewrite rev_length, map_length; reflexivity. 
      }
      2: apply Forall2_length in Hr2; auto.
      (*Then simplify first because all wilds*)
      rewrite matches_row_all_wilds with (ps:=(repeat Pwild (Datatypes.length (s_args c)))); [| apply repeat_spec].
      simpl.
      (*A bit of simplification to get things together*)
      rewrite terms_to_hlist_tl.
      rewrite terms_to_hlist_irrel with (H2:=f).
      rewrite matches_row_irrel with (Hr2:=Hr2).
      destruct (matches_row tys (terms_to_hlist v ts tys f) ptl Hr2) as [m1|] eqn : Hmatch1; simpl; auto.
      f_equal. apply gen_rep_irrel.
Qed.

End SpecProof.

(*The proof for the default matrix is much easier*)
Theorem default_match_eq 
  (*Info about first term*)
  (t: term) {m: mut_adt} (m_in : mut_in_ctx m gamma)
  {a: alg_datatype} (a_in: adt_in_mut a m) {c: funsym} (c_in: constr_in_adt c a) 
  {args: list vty} (args_len: length args = length (m_params m))
  (params_len: length (s_params c) = length args)
  (Hty: term_has_type gamma t (vty_cons (adt_name a) args))
  (al1: arg_list (domain (dom_aux pd)) (sym_sigma_args c (map (v_subst vt) args)))
  (Ht: tm_semantic_constr t m_in a_in c_in args_len Hty al1)
  
  (*Info about rest of terms*)
  (ts: list term) (tys: list vty)
  (Htsty: Forall2 (term_has_type gamma) (t :: ts) (vty_cons (adt_name a) args :: tys)) (*duplicate proof for irrelevance*)
  (*Info about pattern matrix*)
  (P: pat_matrix) (Hpsimp: simplified P)
  (c_notin: constr_at_head_ex c P = false)
  (Htyp: pat_matrix_typed (vty_cons (adt_name a) args :: tys) P)
  (Htyp': pat_matrix_typed tys (default P)):

  matches_matrix_tms v (t :: ts) (vty_cons (adt_name a) args :: tys) P
    Htsty Htyp =

  matches_matrix v tys (terms_to_hlist v ts tys (Forall2_inv_tail Htsty)) (default P) Htyp'.
Proof.
  unfold matches_matrix_tms.
  generalize dependent (Forall2_inv_tail Htsty).
  revert Htsty Htyp Htyp'.
  induction P as [| rhd rtl]; intros; simpl; simp matches_matrix; [reflexivity|].
  destruct rhd as [ps a1]; simpl.
  (*Case on patterns*)
  destruct ps as [| phd ptl].
  - assert (Htyph:=Htyp). apply pat_matrix_typed_head in Htyph.
    simpl in Htyph. destruct Htyph as [Hrow _]; inversion Hrow. 
  - destruct phd as [| f' params tms | | |]; try discriminate.
    + (*Pconstr*)
      simpl in c_notin. apply orb_false_iff in c_notin.
      unfold constr_at_head in c_notin.
      simpl in c_notin.
      destruct c_notin as [c_eq c_notin].
      destruct (funsym_eqb_spec f' c); try discriminate.
      simp matches_row.
      (*Use fact that different constructor gives None*)
      rewrite terms_to_hlist_equation_4 at 1. simpl hlist_hd.
      rewrite match_val_single_constr_nomatch with (m_in:=m_in)(a_in:=a_in)(c1_in:=c_in)
        (args_len:=args_len)(Hty:=Hty)(al1:=al1); auto.
      simpl. apply IHrtl; auto.
    + (*Pwild*)
      simp matches_row. simpl.
      rewrite terms_to_hlist_tl.
      simp matches_matrix; simpl.
      rewrite terms_to_hlist_irrel with (H2:=f).
      rewrite matches_row_irrel with (Hr2:=(Forall_inv (proj1 Htyp'))). simpl.
      simpl in *.
      unfold option_bind.
      match goal with |- context [matches_row ?tys ?hl ?ptl ?H] =>
        destruct (matches_row tys hl ptl H) as [m1|] eqn : Hmatch1
      end.
      * (*TODO: why do we need to do this?*)
        match goal with |- context [matches_row ?tys ?hl ?ptl ?H] =>
          replace (matches_row tys hl ptl H) with (Some m1) by (apply Hmatch1); auto
        end.
        f_equal. apply gen_rep_irrel.
      * match goal with |- context [matches_row ?tys ?hl ?ptl ?H] =>
          replace (matches_row tys hl ptl H) with (@None (list (vsymbol * {s: sort & domain (dom_aux pd) s }))) by (apply Hmatch1); auto
        end.
Qed.

(*Another version: if the term is not a constructor at all*)
Theorem default_match_eq_nonadt 
  (*Info about first term*)
  (t: term) (ty: vty) (Htm: term_has_type gamma t ty) (Hnotadt: is_vty_adt gamma ty = None)
  (*Info about rest of terms*)
  (ts: list term) (tys: list vty)
  (Htsty: Forall2 (term_has_type gamma) (t :: ts) (ty :: tys)) (*duplicate proof for irrelevance*)
  (*Info about pattern matrix*)
  (P: pat_matrix) (Hpsimp: simplified P)
  (Htyp: pat_matrix_typed (ty :: tys) P)
  (Htyp': pat_matrix_typed tys (default P)):
   matches_matrix_tms v (t :: ts) (ty :: tys) P
    Htsty Htyp =

  matches_matrix v tys (terms_to_hlist v ts tys (Forall2_inv_tail Htsty)) (default P) Htyp'.
Proof.
  unfold matches_matrix_tms.
  generalize dependent (Forall2_inv_tail Htsty).
  revert Htsty Htyp Htyp'.
  induction P as [| rhd rtl]; intros; simpl; simp matches_matrix; [reflexivity|].
  destruct rhd as [ps a1]; simpl.
  (*Case on patterns*)
  destruct ps as [| phd ptl].
  - assert (Htyph:=Htyp). apply pat_matrix_typed_head in Htyph.
    simpl in Htyph. destruct Htyph as [Hrow _]; inversion Hrow. 
  - destruct phd as [| f' params tms | | |]; try discriminate.
    + (*Pconstr*)
      simp matches_row. rewrite terms_to_hlist_equation_4 at 1. simpl hlist_hd.
      rewrite match_val_single_rewrite.
      generalize dependent (@is_vty_adt_some gamma ty).
      generalize dependent (@adt_vty_length_eq gamma gamma_valid ty).
      generalize dependent (@constr_length_eq gamma gamma_valid ty).
      rewrite Hnotadt. simpl. auto. 
    + (*Pwild*)
      (*Same as above, should change*)
      simp matches_row. simpl.
      rewrite terms_to_hlist_tl.
      simp matches_matrix; simpl.
      rewrite terms_to_hlist_irrel with (H2:=f).
      rewrite matches_row_irrel with (Hr2:=(Forall_inv (proj1 Htyp'))). simpl.
      simpl in *.
      unfold option_bind.
      match goal with |- context [matches_row ?tys ?hl ?ptl ?H] =>
        destruct (matches_row tys hl ptl H) as [m1|] eqn : Hmatch1
      end.
      * (*TODO: why do we need to do this?*)
        match goal with |- context [matches_row ?tys ?hl ?ptl ?H] =>
          replace (matches_row tys hl ptl H) with (Some m1) by (apply Hmatch1); auto
        end.
        f_equal. apply gen_rep_irrel.
      * match goal with |- context [matches_row ?tys ?hl ?ptl ?H] =>
          replace (matches_row tys hl ptl H) with (@None (list (vsymbol * {s: sort & domain (dom_aux pd) s }))) by (apply Hmatch1); auto
        end.
Qed.

(*The last big result we need before the main proof: simplifying the pattern matrix
  does not change the semantics*)

(*First, we need a generalized notion of "let"*)

Definition gen_let (v: vsymbol) (t: term) (g: gen_term b) : gen_term b :=
  match b return gen_term b -> gen_term b with
  | true => fun t2 => Tlet t v t2
  | false => fun f => Flet t v f
  end g.

Lemma gen_rep_let vv (ty2: gen_type b) (x: vsymbol) (t: term) (a: gen_term b) Hty1 Hty2 Hty3:
  gen_rep vv ty2 (gen_let x t a) Hty2 =
  gen_rep (substi pd vt vv x (term_rep gamma_valid pd vt pf vv t (snd x) Hty1)) ty2 a Hty3.
Proof.
  clear ret_ty.
  revert ty2 a Hty2 Hty3.
  unfold gen_let, gen_rep.
  destruct b; simpl; intros; simpl_rep; simpl;
  rewrite term_rep_irrel with (Hty2:=Hty1);
  [apply term_rep_irrel | apply fmla_rep_irrel].
Qed.

Lemma gen_let_typed_inv {t x d ty}:
  @gen_typed gamma b (gen_let x t d) ty ->
  term_has_type gamma t (snd x) /\ @gen_typed gamma b d ty.
Proof.
  unfold gen_let. destruct b; simpl in *; intros Hty; inversion Hty; subst; auto.
Qed.

Lemma gen_let_ty x t a ty:
  @gen_typed gamma b a ty ->
  term_has_type gamma t (snd x) ->
  @gen_typed gamma b (gen_let x t a) ty.
Proof.
  unfold gen_let.
  destruct b; simpl; intros; constructor; auto.
Qed.

(*We need the condition that no variable free in the list of terms we match on
  also appears free in a pattern. To see why, consider:
   match Tvar y, Tvar z with
  | Pvar x, Pvar y -> f (x, y)
  end
  should be: f(y, z)
  But if we match by iterating over each term and binding in a "let", we get:
  let x = y in (let y = z in f(x, y))
  let (y = z in f(y, y)) -> f(z, z)*)

(*Two notions of disjointness*)

(* Definition pat_row_vars_disj (ts: list term) (ps: list pattern) : Prop :=
  disj (big_union vsymbol_eq_dec tm_fv ts) (big_union vsymbol_eq_dec pat_fv ps).

Definition pat_matrix_vars_disj (ts: list term) (P: pat_matrix) : Prop :=
  Forall (fun row => pat_row_vars_disj ts (fst row)) P. *)

(*TODO: prob dont use strong, just look at fv*)
Definition row_fv {B: Type} (row: list pattern * B) : list vsymbol :=
  big_union vsymbol_eq_dec pat_fv (fst row).
Definition pat_mx_fv (P: pat_matrix) : list vsymbol :=
  big_union vsymbol_eq_dec row_fv P.

Definition pat_row_vars_disj {B: Type} (ts: list term) (ps: list pattern * B) : Prop :=
  disj (big_union vsymbol_eq_dec tm_fv ts) (row_fv ps).

Definition pat_matrix_vars_disj (tms: list term) (P: pat_matrix) : Prop :=
  disj (big_union vsymbol_eq_dec tm_fv tms) (pat_mx_fv P).

Lemma pat_matrix_vars_disj_equiv tms P:
  (pat_matrix_vars_disj tms P) <-> Forall (pat_row_vars_disj tms) P.
Proof.
  unfold pat_matrix_vars_disj. split.
  - unfold pat_mx_fv. intros Hdisj.
    rewrite Forall_forall. intros row Hinrow x [Hxin1 Hinx2].
    revert Hxin1. rewrite <- big_union_elts. intros [t [Hint Hinx1]].
    apply (Hdisj x); split; auto. simpl_set. exists t; auto.
    simpl_set. exists row. split; auto.
  - intros Hall. intros x [Hinx1 Hinx2].
    unfold pat_mx_fv in Hinx2.
    revert Hinx2. rewrite <- big_union_elts.
    intros [row [Hinrow Hinx2]].
    rewrite Forall_forall in Hall.
    apply Hall in Hinrow.
    apply (Hinrow x). auto.
Qed.

Lemma pat_matrix_vars_disj_inv_tail tms p P:
  pat_matrix_vars_disj tms (p :: P) ->
  pat_matrix_vars_disj tms P.
Proof.
  rewrite !pat_matrix_vars_disj_equiv. intros Hall; inversion Hall; auto.
Qed.
(* 
Lemma pat_matrix_vars_disj_equiv tms P:
  (pat_matrix_vars_disj tms P) <-> (pat_matrix_vars_disj1 tms P).
Proof.
  unfold pat_matrix_vars_disj, pat_matrix_vars_disj1. split.
  - intros Hall. intros x [Hinx1 Hinx2].
    unfold pat_mx_fv in Hinx2.
    revert Hinx2. rewrite <- big_union_elts.
    intros [row [Hinrow Hinx2]].
    rewrite Forall_forall in Hall.
    apply Hall in Hinrow.
    apply (Hinrow x). auto.
  - unfold pat_mx_fv. intros Hdisj.
    rewrite Forall_forall. intros row Hinrow x [Hxin1 Hinx2].
    revert Hinx2. rewrite <- big_union_elts. intros [p [Hinp Hinx2]].
    apply (Hdisj x); split; auto. simpl_set. exists row. split; auto.
    unfold row_fv. simpl_set. exists p; auto.
Qed. *)

(*The interesting part: expanding with [simplify_single] is the same as matching the
  row, then substituting*)
Lemma simplify_single_match_eq t ts ty1 tys Htmty (row : list pattern * gen_term b) Hp1 Hp2
  (Htyrow: gen_typed b (snd row) ret_ty)
  (Htty: term_has_type gamma t ty1)
  (Hvars: pat_row_vars_disj (t :: ts) row):
  opt_related (fun d l => d = gen_rep (extend_val_with_list pd vt v l) ret_ty (snd row) Htyrow) 
  (matches_matrix v (ty1 :: tys) (terms_to_hlist v (t :: ts) (ty1 :: tys) Htmty)
    (simplify_single gen_let t row) Hp1)
  (matches_row (ty1 :: tys) (terms_to_hlist v (t :: ts) (ty1 :: tys) Htmty) (fst row) Hp2).
Proof.
  destruct row as [row a]; simpl in *.
  destruct row as [| rhd rtl]; simpl in *.
  - simp matches_matrix; simpl.
    inversion Hp2.
  - simp terms_to_hlist matches_row. simpl hlist_hd.
    (*Let's try this*)
    generalize dependent a.
    induction rhd; auto; intros.
    + (*Pvar*) 
      simpl in *. simp matches_matrix; simpl. simp matches_row; simpl.
      assert (Hletty := proj2 (pat_matrix_typed_head Hp1)); simpl in Hletty.
      rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hp2)).
      destruct (matches_row _ _ rtl _) as [m1|] eqn : Hmatch1; simpl; auto.
      assert (Hty1: term_has_type gamma t (snd v0)). {
        apply gen_let_typed_inv in Hletty; apply Hletty.
      }
      erewrite gen_rep_let with (Hty1:=proj1 (gen_let_typed_inv Hletty))
        (Hty3:=Htyrow).
      apply gen_rep_change_vv.
      (*Prove that valuations are the same*)
      intros x Hinx.
      unfold substi. destruct (vsymbol_eq_dec x v0); subst.
      * unfold extend_val_with_list at 2. simpl.
          destruct (vsymbol_eq_dec v0 v0); try contradiction.
        simpl.
        assert (ty1 = (snd v0)). {
          inversion Hp2; subst. inversion H2; subst. reflexivity.
        }
        subst. destruct (sort_eq_dec (v_subst vt (snd v0))
          (v_subst vt (snd v0))); try contradiction.
        assert (e0 = eq_refl). apply UIP_dec. apply sort_eq_dec. subst.
        simpl. unfold dom_cast; simpl.
        rewrite term_rep_irrel with (Hty2:=(Forall2_inv_head Htmty)).
        apply tm_change_vv.
        intros v1 Hinv1.
        apply extend_val_notin.
        rewrite (matches_row_vars Hmatch1).
        unfold pat_row_vars_disj in Hvars.
        intros Hinv1'.
        apply (Hvars v1). unfold row_fv. simpl fst.
        rewrite !big_union_cons, !union_elts. auto.
      * unfold extend_val_with_list at 2. simpl.
        destruct (vsymbol_eq_dec x v0); subst; try contradiction.
        unfold extend_val_with_list. reflexivity.
    + (*Pconstr case*)
      (*constr not simplified so case is easy*)
      simpl simplify_aux.
      simpl hlist_tl. simpl map.
      simp matches_matrix.
      simpl fst. simpl snd.
      simp matches_row.
      simpl hlist_tl.
      simpl hlist_hd.
      rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hp2)).
      destruct (match_val_single _ _ _ _ _ _ _) as [m1|] eqn : Hmatch1; simpl; auto.
      rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hp2)).
      destruct (matches_row _ _ _ _) as [m2|] eqn : Hmatch2; simpl; auto.
      apply gen_rep_irrel.
    + (*Pwild case -easy*)
      simpl simplify_aux. simpl map.
      simp matches_matrix.
      simpl fst. simpl snd. 
      simp matches_row. simpl.
      rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hp2)).
      destruct (matches_row _ _ _ _) as [m1|] eqn : Hmatch1; simpl; auto.
      apply gen_rep_irrel.
    + (*Por case - interesting one*)
      generalize dependent Hp1.
      simpl simplify_aux.
      rewrite map_app. intros Hp1.
      assert (Hrtemp := (pat_matrix_typed_app_inv Hp1)).
      destruct Hrtemp as [Hr1 Hr2].
      rewrite matches_matrix_app with (Hp1:=Hr1)(Hp2:=Hr2).
      simpl hlist_tl.
      (*from IH*)
      assert (Hp2' : row_typed (ty1 :: tys) (rhd1 :: rtl)).
      {
        inversion Hp2; subst; constructor; auto.
        inversion H2; auto.
      }
      assert (Hdisj1: pat_row_vars_disj (t :: ts) (rhd1 :: rtl, a)). {
        clear -Hvars.
        unfold pat_row_vars_disj in *.
        unfold row_fv,fst in *.
        unfold disj in *.
        intros x [Hinx1 Hinx2].
        apply (Hvars x).
        simpl_set_small. destruct_all; split; auto.
      } 
      specialize (IHrhd1 Hp2' a Hr1 Htyrow Hdisj1).
      destruct (matches_matrix _ _ _ _ Hr1) as [m1 |] eqn : Hmatch1.
      * (*First pattern matches*) simpl.
        simpl in IHrhd1.
        (*Make everything in goal match IH, need to destruct, all other cases contradictions*)
        rewrite match_val_single_irrel with (Hval2:=Forall2_inv_head Hp2').
        destruct (match_val_single _ _ _ _ _ (Forall2_inv_head Hp2') _) as [m2 |] eqn : Hmatch2;
        [|contradiction].
        simpl in IHrhd1 |- *.
        rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hp2')).
        destruct (matches_row _ _ rtl _) as [m3 |] eqn : Hmatch3; [|contradiction].
        simpl in IHrhd1 |- *. apply IHrhd1.
      * (*First pattern does not match - use second IH similarly*)
        assert (Hp2'': row_typed (ty1 :: tys) (rhd2 :: rtl)). {
          inversion Hp2; subst; constructor; auto.
          inversion H2; auto.
        }
        assert (Hdisj2: pat_row_vars_disj (t :: ts) (rhd2 :: rtl, a)). {
          clear -Hvars.
          unfold pat_row_vars_disj in *.
          unfold row_fv, fst in *.
          unfold disj in *.
          intros x [Hinx1 Hinx2].
          apply (Hvars x).
          simpl_set_small. destruct_all; split; auto.
        }
        specialize (IHrhd2 Hp2'' a Hr2 Htyrow Hdisj2).
        simpl hlist_tl in *.
        destruct (matches_matrix _ _ _ _ Hr2) as [m2|] eqn : Hmatch2.
        --(*Second pattern matches*)
          simpl in *.
          (*Still need info from first IH - cannot match*)
          rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hp2')).
          destruct (match_val_single _ _ _ _ rhd1 (Forall2_inv_head Hp2') _) as [m3|] eqn : Hmatch3; simpl in *.
          ++ (*Get contradiction from first IH*)
            rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hp2')).
            destruct (matches_row _ _ rtl _) as [m4|] eqn : Hmatch4; simpl in *; [contradiction|].
            (*Now use second IH*)
            destruct (match_val_single _ _ _ _ rhd2 _ _) as [m5|] eqn : Hmatch5;
            simpl in IHrhd2; [|contradiction].
            erewrite matches_row_irrel in Hmatch4; rewrite Hmatch4 in IHrhd2.
            contradiction.
          ++ (*Otherwise rhd does not match - no more info from IH1. rest of case is like first*)
            rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hp2'')).
            destruct (match_val_single _ _ _ _ rhd2 _ _) as [m4|] eqn : Hmatch4; simpl in *;
            [|contradiction]. 
            rewrite matches_row_irrel with (Hr2:=Forall2_inv_tail Hp2'').
            destruct (matches_row _ _ rtl _) as [m5|] eqn : Hmatch5; [|contradiction].
            simpl in *. apply IHrhd2.
        -- (*Neither matches*)
          simpl in *.
          (*Use info from both IHs*)
          rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hp2')).
          destruct (match_val_single _ _ _ _ rhd1 _ _) as [m3|] eqn : Hmatch3; simpl in *.
          ++ (*If rhd1 matches, by IH1, rtl cannot*)
            rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hp2')).
            destruct (matches_row _ _ rtl _) as [m4|] eqn : Hmatch4; [contradiction| auto].
          ++ (*see if rh2 matches*) 
            rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hp2'')).
            destruct (match_val_single _ _ _ _ rhd2 _ _) as [m4|] eqn : Hmatch4; simpl in *; auto.
            (*If rh2 matches, rtl cannot by IH2*)
            rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hp2'')).
            destruct (matches_row _ _ rtl) as [m5|] eqn : Hmatch5; [contradiction| auto].
    + (*Pbind case - recursive + Pvar case*)
      simpl simplify_aux.
      assert (Hr2: row_typed (ty1 :: tys) (rhd :: rtl)). {
        inversion Hp2; subst; constructor; auto.
        inversion H2; subst; auto.
      }
      assert (Hdisj: pat_row_vars_disj (t :: ts) (rhd :: rtl, a)).
      {
        clear -Hvars.
        unfold pat_row_vars_disj in *.
        unfold row_fv, fst in *.
        unfold disj in *.
        intros x [Hinx1 Hinx2].
        apply (Hvars x).
        simpl_set_small. destruct_all; split; auto.
      } 
      assert (Htty': term_has_type gamma t (snd v0)). {
        inversion Hp2; subst.
        inversion H2; subst. auto.
      }
      assert (Hletty: @gen_typed gamma b (gen_let v0 t a) ret_ty).
      {
        apply gen_let_ty; auto.
      }
      specialize (IHrhd Hr2 (gen_let v0 t a) Hp1 Hletty Hdisj).
      (*Now destruct LHS and use IH*)
      (*Coq has trouble again*)
      match goal with 
      | |- context [matches_matrix ?a ?b ?c ?d] => destruct (matches_matrix a b c d) as [m1|]
        eqn : Hmatch1; simpl in *
      end.
      * (*Case 1: LHS matches, by IH we know that RHS matches also*)
        rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hr2)).
        destruct (match_val_single _ _ _ _ rhd _ _) as [m2|] eqn : Hmatch2; simpl in *;[|contradiction].
        rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hr2)).
        destruct (matches_row _ _ rtl _) as [m3|] eqn : Hmatch3; simpl in *;[|contradiction].
        subst.
        rewrite gen_rep_let with (Hty1:=Htty')(Hty3:=Htyrow).
        (*Now deal with variable stuff*)
        apply gen_rep_change_vv.
        intros x Hinx.
        unfold substi.
        destruct (vsymbol_eq_dec x v0); subst.
        -- simpl. unfold extend_val_with_list at 2. simpl. destruct (vsymbol_eq_dec v0 v0); try contradiction; simpl.
          assert (ty1 = (snd v0)). {
            inversion Hp2; subst. inversion H2; subst. reflexivity.
          }
          subst. destruct (sort_eq_dec _ _); [| contradiction].
          assert (e0 = eq_refl). apply UIP_dec. apply sort_eq_dec. subst.
          simpl. unfold dom_cast; simpl.
          rewrite term_rep_irrel with (Hty2:=(Forall2_inv_head Htmty)).
          apply tm_change_vv.
          intros v1 Hinv1.
          apply extend_val_notin.
          rewrite map_app, in_app_iff.
          rewrite (matches_row_vars Hmatch3).
          rewrite <- (match_val_single_free_var _ _ _ _ _ _ _ _ _ Hmatch2).
          unfold pat_row_vars_disj in Hdisj.
          unfold row_fv, fst in Hdisj.
          intros Hinv1'.
          apply (Hdisj v1).
          rewrite !big_union_cons.
          rewrite !union_elts. auto.
        -- unfold extend_val_with_list at 2. simpl.
          destruct (vsymbol_eq_dec x v0); subst; try contradiction.
          unfold extend_val_with_list. reflexivity.
      * (*Case 2: LHS doesnt match. Show same for RHS*)
        rewrite match_val_single_irrel with (Hval2:=(Forall2_inv_head Hr2)).
        destruct (match_val_single _ _ _ _ rhd _ _) as [m2|] eqn : Hmatch2; simpl in *; [| auto].
        (*If rhd matches, know rtl does not*)
        rewrite matches_row_irrel with (Hr2:=(Forall2_inv_tail Hr2)).
        destruct (matches_row _ _ rtl _) as [m3|] eqn : Hmatch3; simpl in *; [contradiction| auto].
Qed.

(*And the full result*)
Theorem simplify_match_eq (t: term) (ts: list term) (tys: list vty) (P: pat_matrix)
  Htmty Hty1 Hty2
  (Hdisj: pat_matrix_vars_disj (t :: ts) P):
  matches_matrix_tms v (t :: ts) tys (simplify gen_let t P) Htmty Hty1 =
  matches_matrix_tms v (t :: ts) tys P Htmty Hty2.
Proof.
  revert Htmty Hty1 Hty2.
  induction P as [| rhd P' IH]; simpl; intros.
  - unfold simplify. simpl. apply matches_matrix_irrel.
  - unfold simplify in *. simpl.
    unfold matches_matrix_tms.
    simpl in Hty1.
    assert (Htemp:=pat_matrix_typed_app_inv Hty1).
    destruct Htemp as [Hp1 Hp2].
    rewrite matches_matrix_app with (Hp1:=Hp1)(Hp2:=Hp2).
    simp matches_matrix.
    destruct tys as [| ty1 tys]; [inversion Htmty|].
    assert (Hdisj1: pat_row_vars_disj (t :: ts) rhd ). {
      apply pat_matrix_vars_disj_equiv in Hdisj.
      inversion Hdisj; auto.
    }
    (*Bulk is [simplify_single_match_eq] can't rewrite bc not rewritable relation*)
    pose proof (simplify_single_match_eq t ts ty1 tys Htmty rhd Hp1 (Forall_inv (proj1 Hty2))
      (Forall_inv (proj2 Hty2)) (Forall2_inv_head Htmty) Hdisj1) as Hrelated.
    destruct (matches_matrix _ _ _ _ Hp1) as [m1 |] eqn : Hmatch1; simpl in *.
    + (*If LHS matches, easy from lemma*)
      destruct (matches_row _ _ (fst rhd) _) as [m2|] eqn : Hmatch2; [|contradiction].
      subst. reflexivity.
    + (*If LHS doesn't match, use lemma to show RHS doesn't, then use IH*)
      destruct (matches_row _ _ (fst rhd) _) as [m2|] eqn : Hmatch2;[contradiction|].
      apply IH.
      apply pat_matrix_vars_disj_inv_tail in Hdisj; auto.
Qed.

End SpecDefaultLemmas.

(*Proving the correctness of [compile]*)

(*The specific functions for matches, variables, constructors, etc for generic terms*)

Definition gen_match (t: term) (ty: vty) (l: list (pattern * gen_term b)) : gen_term b :=
  match b return list (pattern * gen_term b) -> gen_term b with
  | true => fun pats => Tmatch t ty pats
  | false => fun pats => Fmatch t ty pats
  end l.

Definition gen_getvars (x: gen_term b) : list vsymbol :=
  match b return gen_term b -> list vsymbol with
  | true => fun t => tm_bnd t ++ tm_fv t
  | false => fun f => fmla_bnd f ++ fmla_fv f
  end x.

Definition get_constructors (ts: typesym) : list funsym :=
  match (find_ts_in_ctx gamma ts) with
  | Some (m, a) => adt_constr_list a
  | None => nil
  end.

Lemma in_get_constructors {m a f} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m):
  In f (get_constructors (adt_name a)) <->
  constr_in_adt f a.
Proof.
  unfold get_constructors.
  assert (Hts: find_ts_in_ctx gamma (adt_name a) = Some (m, a)). {
    apply find_ts_in_ctx_iff; auto.
  }
  rewrite Hts. rewrite constr_in_adt_eq. reflexivity. 
Qed. 

(*Part 1: Lemmas for Typing Contradictions*)
(*We need to know that if e.g. populate_all gives None, this gives a contradiction
  with the well-typedeness of the pattern matrix. We need several results for this*)

(*If populate is None, there is a Pconstr that is not a constructor*)
Lemma populate_none_simpl (is_constr: funsym -> bool) acc p:
  simplified_aux p ->
  populate is_constr acc p = None ->
  exists c tys ps, p = Pconstr c tys ps /\ is_constr c = false.
Proof.
  destruct p; try discriminate. simpl. intros _.
  destruct acc as [css csl]; simpl.
  destruct (is_constr f) eqn : Hf.
  + destruct (amap_mem funsym_eq_dec f css ); discriminate.
  + intros _. exists f. exists l. exists l0. auto.
Qed.

(*Some results about [get_heads]*)

(*Anything in the result of [get_heads] is well-typed, assuming the matrix is*)
Lemma in_get_heads_tys (ty: vty) (tys: list vty) (P: pat_matrix) (p: pattern) l
  (Hp: pat_matrix_typed (ty :: tys) P)
  (Hheads: get_heads P = Some l)
  (Hinp: In p l):
  pattern_has_type gamma p ty.
Proof.
  generalize dependent l.
  induction P as [| [ps a] P' IH]; simpl; intros l.
  - inv Hsome. contradiction.
  - destruct ps as [| phd ptl]; [discriminate|].
    destruct (get_heads P') as [l'|]; [|discriminate].
    simpl. inv Hsome. simpl.
    intros [Hpeq | Hinp]; subst.
    + apply pat_matrix_typed_head in Hp.
      destruct Hp as [Hrow _].
      apply Forall2_inv_head in Hrow. auto.
    + apply pat_matrix_typed_tail in Hp. eauto.
Qed.


Lemma get_heads_simplified (rl: pat_matrix) l p:
  simplified rl ->
  get_heads rl = Some l ->
  In p l -> simplified_aux p.
Proof.
  generalize dependent l.
  induction rl as [| [ps a] rtl IH]; simpl; intros l.
  - intros _. inv Hsome. contradiction.
  - destruct ps as [| phd ptl]; [discriminate|].
    intros Hsimp. apply andb_prop in Hsimp.
    destruct Hsimp as [Hsimphd Hsimptl].
    destruct (get_heads rtl); simpl in *;[|discriminate].
    inv Hsome. simpl. intros [Hp | Hinp]; subst; eauto.
Qed.

Lemma get_heads_none_iff {B: Type} (l: list (list pattern * B)):
  get_heads l = None <-> existsb (fun x => null (fst x)) l.
Proof.
  induction l as [| [ps a] t IH]; simpl; auto.
  - split; discriminate.
  - destruct ps; simpl; auto.
    + split; auto.
    + destruct (get_heads t); simpl; auto.
      rewrite <- IH. split; discriminate.
Qed.

(*And a few more lemmas for typing contradictions*)
Lemma pat_matrix_typed_row_lengths tys rl p:
  pat_matrix_typed tys rl ->
  In p rl ->
  length (fst p) = length tys.
Proof.
  induction rl as [| h t IH]; simpl; auto; [contradiction|].
  intros Htyped. assert (Htl:=Htyped). apply pat_matrix_typed_head in Htyped.
  apply pat_matrix_typed_tail in Htl. destruct Htyped as [Hrow Hty].
  intros [Hhp | Hinp]; subst; eauto.
  apply Forall2_length in Hrow; auto.
Qed.

Lemma pat_matrix_typed_not_null {ty tys rl}:
  pat_matrix_typed (ty :: tys) rl ->
  existsb (fun x => null (fst x)) rl = false.
Proof.
  intros Htyped.
  destruct (existsb _ rl) eqn : Hex; auto.
  apply existsb_exists in Hex.
  destruct Hex as [row [Hinrow Hnullrow]].
  exfalso.
  apply pat_matrix_typed_row_lengths with (p:=row) in Htyped; auto.
  destruct (fst row); discriminate.
Qed.

(* Part 2: Results about [simplify] (disjointness, well-typed)*)
(*One of the first things we do is eliminate the [simplify], but we need some well-formedness
  results first*)


(*All variables in simplification are in original matrix - the converse does not hold*)
Lemma simplify_subset mk_let t rl:
  forall x, In x (pat_mx_fv (simplify mk_let t rl)) -> In x (pat_mx_fv rl).
Proof.
  intros x.
  induction rl as [| rhd rtl IH]; simpl; auto.
  unfold pat_mx_fv in *; simpl. unfold simplify in *. simpl.
  rewrite big_union_app. simpl_set_small.
  intros [Hinx | Hinx]; auto.
  (*The inner lemma we need*)
  clear -Hinx. destruct rhd as [[| phd ptl] a]; simpl; [contradiction|].
  unfold simplify_single in Hinx. unfold row_fv at 1. simpl.
  simpl_set_small.
  generalize dependent a.
  induction phd; simpl in *; intros; unfold row_fv in Hinx; simpl in Hinx; simpl_set_small;
  try (destruct Hinx as [Hinx | Hf]; [|contradiction]); simpl_set_small; auto.
  - rewrite map_app in Hinx. apply big_union_app in Hinx.
    simpl_set_small. destruct Hinx as [Hinx | Hinx]; auto.
    + apply IHphd1 in Hinx. destruct_all; auto.
    + apply IHphd2 in Hinx. destruct_all; auto.
  - apply IHphd in Hinx. destruct_all; auto.
Qed.

(*We need a stronger notion of disjointness: the names are disjoint, not just the variables*)

Definition pat_matrix_var_names_disj (tms: list term) (P: pat_matrix) :=
  disj (map fst (big_union vsymbol_eq_dec tm_fv tms)) (map fst (pat_mx_fv P)).

Lemma pat_matrix_var_names_vars_disj tms P:
  pat_matrix_var_names_disj tms P ->
  pat_matrix_vars_disj tms P.
Proof.
  apply disj_map.
Qed.

Lemma pat_matrix_vars_subset tms P1 P2:
  (forall x, In x (pat_mx_fv P2) -> In x (pat_mx_fv P1)) (*could weaken to map fst i think*) ->
  pat_matrix_var_names_disj tms P1 -> 
  pat_matrix_var_names_disj tms P2.
Proof.
  intros Hall.
  unfold pat_matrix_var_names_disj.
  intros Hdisj x [Hx1 Hx2].
  rewrite in_map_iff in Hx1, Hx2.
  destruct Hx1 as [x1 [Hx Hinx1]]; subst.
  destruct Hx2 as [x2 [Hx Hinx2]]; subst.
  apply (Hdisj (fst x1)).
  rewrite !in_map_iff; split; [exists x1 | exists x2]; auto.
Qed.

(*And so we get the disjointness result we want*)
Lemma simplify_disj mk_let tms t rl:
  pat_matrix_var_names_disj tms rl ->
  pat_matrix_var_names_disj tms (simplify mk_let t rl).
Proof.
  apply pat_matrix_vars_subset.
  apply simplify_subset.
Qed.

(*[simplify] is well-typed if the original pattern matrix is and if the term has the 
  correct type*)
Lemma simplify_typed {tys t ty rl}:
  term_has_type gamma t ty ->
  pat_matrix_typed (ty :: tys) rl ->
  pat_matrix_typed (ty :: tys) (simplify gen_let t rl).
Proof.
  intros Htm.
  induction rl as [| rhd rtl IH].
  - unfold simplify. simpl. auto.
  - unfold simplify in *. simpl.
    intros Htyped.
    pose proof (pat_matrix_typed_head Htyped) as Hhd.
    pose proof (pat_matrix_typed_tail Htyped) as Htl.
    apply pat_matrix_typed_app; auto.
    clear -Hhd Htm.
    (*Inner result*)
    destruct Hhd as [Hrow Htm1].
    destruct rhd as [[| phd ptl] a]; simpl in *.
    + apply prove_pat_matrix_typed_cons; simpl; auto.
      inversion Hrow; subst.
    + assert (Hrowtl:=Hrow). apply Forall2_inv_tail in Hrowtl.
      apply Forall2_inv_head in Hrow. rename Hrow into Hphdty. simpl in Hphdty.
      generalize dependent a.
      induction phd; simpl in *; intros; try (apply prove_pat_matrix_typed_cons; simpl; auto);
      inversion Hphdty; subst;
      try(solve[constructor; auto]); try solve[apply pat_matrix_typed_nil];
      try solve[apply gen_let_ty; auto].
      * repeat(constructor; auto).
      * rewrite map_app. apply pat_matrix_typed_app; auto.
      * apply IHphd; auto. apply gen_let_ty; auto.
Qed.

(*Part 3: Typing for [default] and [spec]*)

(*First, prove equivalent to dispatch*)
Lemma dispatch1_equiv_default mk_let t types rl:
  simplified rl -> (*Makes things easier*)
  snd (dispatch1 mk_let t types rl) = default rl.
Proof.
  intros Hsimp.
  rewrite dispatch_equiv.
  unfold dispatch2.
  rewrite simplified_simplify; auto.
  rewrite dispatch2_gen_snd.
  reflexivity.
Qed.

(*Specialize is more complicated because we need some assumptions that will come
  from typing*)
(*Idea: need to show that lengths are the same, so need to know that whatever
  f maps to in (fst o) is actually in P. Thus, it is well-typed, so the lengths are equal.
  But the end result is that we have a functional spec that does NOT refer to o, t, etc at all*)
Lemma dispatch1_equiv_spec mk_let is_constr t {f tys o P}:
  simplified P ->
  populate_all is_constr P = Some o ->
  pat_matrix_typed tys P ->
  amap_mem funsym_eq_dec f (fst o) ->
  amap_get funsym_eq_dec (fst (dispatch1 mk_let t (fst o) P)) f = Some (spec P f).
Proof.
  intros Hsimp Hpop Hty Hinf.
  rewrite dispatch_equiv.
  unfold dispatch2. rewrite simplified_simplify; auto.
  rewrite amap_mem_spec in Hinf.
  destruct (amap_get funsym_eq_dec (fst o) f) as [ys|] eqn : Hget; [|discriminate].
  rewrite dispatch2_gen_fst_in with (ys:=ys); auto.
  2: {
    apply orb_true_iff. left. apply (populate_all_in _ _ _ f Hsimp Hpop).
    rewrite amap_mem_spec. rewrite Hget; auto.
  }
  unfold spec.
  replace (length ys) with (length (s_args f)); [auto|].
  (*The reason we need the typing*)
  pose proof (populate_all_in_strong _ _ _ _ _ Hsimp Hpop Hget) as Hex.
  apply existsb_exists in Hex.
  destruct Hex as [[ps a] [Hinrow Hconstr]].
  destruct Hty as [Hrows _].
  rewrite Forall_forall in Hrows.
  specialize (Hrows _ Hinrow).
  unfold constr_args_at_head in Hconstr.
  simpl in *.
  destruct ps as [| p ps]; [discriminate|].
  destruct p as [| c tys1 pats1 | | |]; try discriminate.
  inversion Hrows; subst.
  destruct (funsym_eqb_spec c f); try discriminate. subst.
  destruct (list_eqb_spec _ pattern_eqb_spec ys pats1); [|discriminate]. subst.
  inversion H1; subst; auto.
Qed.

(*Prove [disj] for default*)

Lemma default_vars_subset rl:
  sublist (pat_mx_fv (default rl)) (pat_mx_fv rl).
Proof.
  unfold sublist, pat_mx_fv. induction rl as [| [ps a] rtl IH]; auto.
  intros x. simpl.
  destruct ps as [| p ptl]; simpl; auto.
  destruct p; simpl; auto; intros Hinx; unfold row_fv at 1; simpl_set_small; auto.
  simpl fst. rewrite big_union_cons. simpl.
  unfold row_fv at 1 in Hinx; destruct_all; auto.
Qed.

Lemma disj_default t ts rl:
  pat_matrix_var_names_disj (t :: ts) rl ->
  pat_matrix_var_names_disj ts (default rl).
Proof.
  unfold pat_matrix_var_names_disj.
  intros Hdisj.
  eapply disj_sublist_lr.
  - apply Hdisj.
  - rewrite big_union_cons. apply sublist_map. apply union_sublist_r.
  - apply sublist_map. apply default_vars_subset.
Qed.

Lemma default_typed {t ts rl}:
  pat_matrix_typed (t :: ts) rl ->
  pat_matrix_typed ts (default rl).
Proof.
  induction rl as [| [ps a] rtl IH]; intros Hpat.
  - apply pat_matrix_typed_nil.
  - simpl.
    pose proof (pat_matrix_typed_tail Hpat) as Htl.
    pose proof (pat_matrix_typed_head Hpat) as Hhd; simpl in Hhd;
    destruct Hhd as [Hrow Hty].
    destruct ps as [| phd ptl]; auto.
    inversion Hrow; subst.
    destruct phd; auto.
    apply prove_pat_matrix_typed_cons; auto.
Qed.

(*Typing for [spec P c]*)
Lemma spec_typed P (f: funsym) ts tys args
  (Hf: Forall (valid_type gamma) (s_args f))
  (Hp: pat_matrix_typed (vty_cons ts args :: tys) P):
  pat_matrix_typed (rev (ty_subst_list (s_params f) args (s_args f)) ++ tys) (spec P f).
Proof.
  induction P as [| [ps a] rtl IH].
  - apply pat_matrix_typed_nil.
  - simpl.  pose proof (pat_matrix_typed_tail Hp) as Htl.
    pose proof (pat_matrix_typed_head Hp) as Hhd; simpl in Hhd;
    destruct Hhd as [Hrow Hty].
    destruct ps as [| phd ptl]; auto.
    inversion Hrow; subst.
    destruct phd as [| f1 tys1 ps1 | | |]; auto. 
    + (*constr case*)
      destruct (funsym_eqb_spec f1 f); auto. subst.
      apply prove_pat_matrix_typed_cons; auto. simpl.
      apply Forall2_app; auto.
      apply Forall2_rev.
      inversion H2; subst.
      unfold sigma in H3.
      destruct H13 as [m [a1 [m_in [a_in c_in]]]].
      rewrite (adt_constr_ret gamma_valid m_in a_in c_in) in H3.
      rewrite ty_subst_cons in H3.
      assert (Hparams: s_params f = m_params m) by
        apply (adt_constr_params gamma_valid m_in a_in c_in).
      rewrite Hparams in H3.
      assert (Heq: ts = adt_name a1 /\ args = tys1). {
        rewrite map_ty_subst_var in H3; auto.
        - inversion H3; subst; auto.
        - rewrite <- Hparams; auto.
        - rewrite <- Hparams. apply s_params_Nodup.
      }
      destruct Heq; subst; clear H3.
      (*And now we just have to unify the "Forall"s - should really make everything Forall2*) 
      (*replace (map vty_var (m_params m)) with (seq.map vty_var (m_params m)) in H3 by auto.*)
      rewrite <- Forall_forall in H11.
      apply Forall2_combine.
      split; auto. unfold ty_subst_list; rewrite map_length. auto.
    + apply prove_pat_matrix_typed_cons; auto. simpl.
      apply Forall2_app; auto.
      (*This is pretty easy because Pwild can have any (valid) type*)
      assert (Hval: Forall (valid_type gamma) (rev (ty_subst_list (s_params f) args (s_args f)))). {
        apply Forall_rev. unfold ty_subst_list. rewrite Forall_map.
        rewrite Forall_forall. intros x Hinx.
        apply valid_type_ty_subst; auto.
        - rewrite Forall_forall in Hf; auto.
        - inversion H2; subst. inversion H; subst. rewrite Forall_forall; auto.
      }
      assert (Hlen: length (repeat Pwild (Datatypes.length (s_args f))) =
        length (rev (ty_subst_list (s_params f) args (s_args f)))).
      {
        unfold ty_subst_list.
        rewrite repeat_length, rev_length, map_length; reflexivity.
      }
      clear -Hval Hlen.
      generalize dependent (rev (ty_subst_list (s_params f) args (s_args f))).
      rewrite repeat_length. generalize dependent (length (s_args f)).
      intros n l Hval Hn; subst. induction l; simpl; auto.
      inversion Hval; subst.
      do 2(constructor; auto).
Qed.

(*And a corollary for ADTs*)
Lemma spec_typed_adt {a m f} (m_in: mut_in_ctx m gamma) (a_in: adt_in_mut a m) (f_in: constr_in_adt f a)
  {P tys args}
  (Hp: pat_matrix_typed (vty_cons (adt_name a) args :: tys) P):
  pat_matrix_typed (rev (ty_subst_list (s_params f) args (s_args f)) ++ tys) (spec P f).
Proof.
  apply spec_typed with (ts:=adt_name a); auto.
  rewrite Forall_forall.
  apply (constr_ret_valid gamma_valid m_in a_in f_in).
Qed.

(*disj for [spec] - we need 2 results*)

Lemma spec_vars_subset rl f:
  sublist (pat_mx_fv (spec rl f)) (pat_mx_fv rl).
Proof.
  unfold sublist, pat_mx_fv. induction rl as [| [ps a] rtl IH]; auto.
  intros x. simpl.
  destruct ps as [| p ptl]; simpl; auto.
  destruct p as [| f1 tys ps | | |]; simpl; auto; intros Hinx; unfold row_fv at 1; simpl_set_small; auto.
  - (*Pconstr*) simpl fst. rewrite big_union_cons. simpl.
    destruct (funsym_eqb_spec f1 f); subst; auto.
    revert Hinx. simpl. unfold row_fv at 1; simpl.
    simpl_set_small.
    rewrite big_union_app. simpl_set_small.
    rewrite big_union_rev. intros; destruct_all; auto.
  - (*Pwild*) simpl fst.
    rewrite big_union_cons. revert Hinx. unfold row_fv at 1. simpl.
    rewrite big_union_app. simpl_set_small.
    assert (Hrep: (big_union vsymbol_eq_dec pat_fv
      (repeat Pwild (Datatypes.length (s_args f)))) = nil).
    {
      generalize dependent (length (s_args f)). clear.
      induction n; simpl; auto.
    }
    rewrite Hrep. simpl.
    intros; destruct_all; auto. contradiction.
Qed.

Lemma spec_names_subset rl f:
  sublist (map fst (pat_mx_fv (spec rl f))) (map fst (pat_mx_fv rl)).
Proof.
  apply sublist_map, spec_vars_subset.
Qed.

Lemma disj_spec {f args tms tl rl}:
  pat_matrix_var_names_disj
    (Tfun f args tms :: tl) rl ->
  pat_matrix_var_names_disj
    (rev tms ++ tl) (spec rl f).
Proof.
  unfold pat_matrix_var_names_disj.
  intros Hdisj.
  eapply disj_sublist_lr.
  - apply Hdisj.
  - rewrite big_union_cons. simpl.
    intros x. rewrite in_map_big_union_app, in_map_union. rewrite in_map_big_union_rev. auto.
  - apply spec_names_subset.
Qed.

Lemma disj_spec1 {f t tms tl rl}:
  pat_matrix_var_names_disj (t :: tl) rl ->
  disj (map fst (big_union vsymbol_eq_dec tm_fv tms)) (map fst (pat_mx_fv rl)) ->
  pat_matrix_var_names_disj (tms ++ tl) (spec rl f).
Proof.
  unfold pat_matrix_var_names_disj.
  unfold disj. rewrite big_union_cons. setoid_rewrite in_map_big_union_app.
  intros Hdisj1 Hdisj2 x [Hinx1 Hinx2].
  simpl_set_small.
  apply spec_names_subset in Hinx2.
  destruct Hinx1 as [Hinx1 | Hinx1]; [apply (Hdisj2 x) | apply (Hdisj1 x)]; simpl_set_small; auto.
  rewrite in_map_union. auto.
Qed.

(*Part 4: Proofs for [Tfun] case*)

(*Express [get_arg_list] via [terms_to_hlist]*)
Lemma get_arg_list_eq v (f: funsym) (ty: vty) (tys: list vty) (tms: list term) 
  (Hty: term_has_type gamma (Tfun f tys tms) ty) Hp Hlents Hlenvs Hall Htms constrs_len:
  get_arg_list pd vt tys tms (term_rep gamma_valid pd vt pf v) Hp Hlents Hlenvs Hall =
  cast_arg_list  (eq_sym (sym_sigma_args_map vt f tys constrs_len))
    (terms_to_hlist v tms ((ty_subst_list (s_params f) tys (s_args f))) Htms).
Proof.
  revert Hp Hlents Hlenvs Hall Htms.
  generalize dependent (eq_sym (sym_sigma_args_map vt f tys constrs_len)).
  unfold sym_sigma_args.
  generalize dependent (s_args f).
  intros args; revert args. clear.
  induction tms as [| thd ttl IH]; simpl; intros.
  - destruct args as [| ahd atl]; auto; [| inversion Htms].
    simpl in *. assert (e = eq_refl). { apply UIP_dec, list_eq_dec, sort_eq_dec. }
    subst. reflexivity.
  - destruct args as [| ahd atl]; auto; [inversion Htms|].
    simpl.
    simp terms_to_hlist.
    rewrite cast_arg_list_cons.
    erewrite IH. f_equal. unfold dom_cast.
    repeat match goal with
    | |- context [scast (f_equal _ ?Heq)] => generalize dependent Heq 
    end.
    intros Heq1 Heq2. assert (Heq1 = Heq2). { apply UIP_dec, sort_eq_dec. }
    subst.
    erewrite term_rep_irrel. reflexivity.
Qed.

Lemma fun_arg_list_eq (v: val_vars pd vt) (f: funsym) (ty: vty) (tys: list vty) (tms: list term) 
  (Hty: term_has_type gamma (Tfun f tys tms) ty) Htms constrs_len:
  fun_arg_list pd vt f tys tms (term_rep gamma_valid pd vt pf v) Hty =
  cast_arg_list  (eq_sym (sym_sigma_args_map vt f tys constrs_len))
    (terms_to_hlist v tms ((ty_subst_list (s_params f) tys (s_args f))) Htms).
Proof.
  unfold fun_arg_list.
  eapply get_arg_list_eq. apply Hty.
Qed.

(*If (Tfun f args tms) is a semantic constr of c(al), then f = c, and
  al = terms_to_hlist tms (with the appropriate cast)*)
Lemma tfun_semantic_constr {m a c f} (m_in: mut_in_ctx m gamma)
  (a_in: adt_in_mut a m) (c_in : constr_in_adt c a) (f_in: constr_in_adt f a)
  (v: val_vars pd vt)
  (args: list vty) (tms: list term)
  (al : arg_list (domain (dom_aux pd)) (sym_sigma_args c (map (v_subst vt) args)))
  (Htty : term_has_type gamma (Tfun f args tms) (vty_cons (adt_name a) args))
  (constrs_len : length (s_params f) = length args)
  (args_len : length args = length (m_params m))
  (Htms : Forall2 (term_has_type gamma) tms (ty_subst_list (s_params f) args (s_args f)))
  (Hsem: tm_semantic_constr v (Tfun f args tms) m_in a_in c_in args_len Htty al):
  exists Heq : c = f,
  al =
  cast_arg_list
    (f_equal
    (fun x : funsym =>
  sym_sigma_args x (map (v_subst vt) args))
    (eq_sym Heq))
    (cast_arg_list
    (eq_sym (sym_sigma_args_map vt f args constrs_len))
    (terms_to_hlist v tms
    (ty_subst_list (s_params f) args (s_args f)) Htms)).
Proof.
  unfold tm_semantic_constr in Hsem.
  simp term_rep in Hsem.
  erewrite fun_arg_list_eq with (constrs_len:=constrs_len) (Htms:=Htms) in Hsem .
  (*Now lots of casting until we can get to injectivity*)
  rewrite (constrs gamma_valid pd pf m a f m_in a_in f_in (map (v_subst vt) args) 
    (eq_trans (map_length (v_subst vt) args) args_len)) in Hsem.
  unfold constr_rep_dom in Hsem. 
  unfold cast_dom_vty, dom_cast in Hsem.
  rewrite !scast_scast in Hsem.
  revert Hsem.
  repeat match goal with 
  |- context [scast ?Heq _] => generalize dependent Heq
  end.
  intros Heq1 Heq2. assert (Heq1 = Heq2). { (*use UIP*) apply Cast.UIP. }
  subst.
  intros Hconstr; apply scast_inj in Hconstr.
  (*First, prove c = f*)
  assert (c = f). {
    destruct (funsym_eq_dec c f); auto.
    apply constr_rep_disjoint in Hconstr; auto. contradiction.
  }
  subst.
  exists eq_refl. unfold cast_arg_list at 1; simpl.
  (*Now use injectivity*)
  assert (c_in = f_in) by (apply bool_irrelevance); subst.
  apply constr_rep_inj in Hconstr; auto.
  apply (gamma_all_unif gamma_valid); auto.
Qed.

(*Part 5: Relationship between [types] and [cslist] (parts of [populate_all])*)

Definition constr_args_at_head_strong {B: Type} (c: funsym) (tys: list vty) (ps: list pattern)
  (P: list pattern * B) : bool :=
  match (fst P) with
  | Pconstr f tys1 pats1 :: _ => funsym_eqb f c && list_eqb vty_eqb tys tys1 && list_eqb pattern_eqb ps pats1
  | _ => false
  end.

Lemma populate_all_fst_snd_full {B: Type} (is_constr: funsym -> bool)
  (P: list (list pattern * B)) y:
  simplified P ->
  populate_all is_constr P = Some y ->
  NoDup (map (fun x => fst (fst x)) (snd y)) /\
  forall c ps,
    amap_get funsym_eq_dec (fst y) c = Some ps <->
    exists tys,
    In (c, tys, ps) (snd y).
Proof.
  intros Hsimpl. unfold populate_all.
  destruct (get_heads P) as[heads|] eqn : Hhead; [|discriminate].
  rewrite fold_left_right_opt.
  assert (Hhead1: get_heads (rev P) = Some (rev heads)). {
    rewrite get_heads_rev, Hhead. reflexivity.
  }
  clear Hhead.
  rewrite <- simplified_rev in Hsimpl.
  generalize dependent (rev heads). clear heads.
  revert y.
  induction (rev P) as [| [ps a] t IH]; simpl; auto; intros y head.
  - inv Hhead. simpl. inv Hsome. simpl. split; [constructor|]. 
    intros c ps. rewrite amap_empty_get.
    split; [discriminate| intros; destruct_all; contradiction].
  - simpl in Hsimpl. apply andb_prop in Hsimpl.
    destruct Hsimpl as [Hsimphd Hsimptl]. destruct ps as [| p ps]; [discriminate|].
    destruct (get_heads t); simpl in *; [|discriminate].
    inv Hhead. simpl.
    destruct (fold_right_opt _ l _) as [y1|] eqn : Hfold; simpl; [|discriminate].
    specialize (IH Hsimptl _ _ eq_refl Hfold).
    destruct IH as [IH1 IH2].
    destruct p as [| f1 tys1 pats1 | | |]; simpl in *; try discriminate.
    + destruct y1 as [css csl]; simpl in *.
      destruct (is_constr f1); [|discriminate].
      destruct (amap_mem funsym_eq_dec f1 css) eqn : Hmem.
      * inv Hsome. simpl; auto.
      * inv Hsome. simpl in *.
        (*First, prove NoDup*)
        split.
        -- constructor; [|apply IH1].
          intros Hinf1. rewrite in_map_iff in Hinf1.
          destruct Hinf1 as [[[f2 tys2] pats2] [Hf2 Hinf2]]; subst; simpl in *.
          (*contradiction with [amap_mem]*)
          assert (Hget: amap_get funsym_eq_dec css f2 = Some pats2). {
            apply IH2. exists tys2; auto.
          }
          rewrite amap_mem_spec in Hmem.
          rewrite Hget in Hmem.
          discriminate.
        -- (*Now prove, iff*)
          intros c ps1.
          destruct (funsym_eqb_spec c f1); subst.
          ++ rewrite amap_set_get_same.
            split.
            ** inv Hsome. exists tys1. auto.
            ** intros [tys [Hex | Hin]].
              { inversion Hex; auto. }
              (*Why we need iff - show that f1 cannot be csl if f1 not in css*)
              rewrite amap_mem_spec in Hmem.
              assert (Hget: amap_get funsym_eq_dec css f1 = Some ps1). {
                apply IH2. exists tys. auto.
              }
              rewrite Hget in Hmem. discriminate.
          ++ rewrite amap_set_get_diff; auto.
            rewrite IH2. 
            split; intros [tys Hintys].
            ** exists tys; auto.
            ** destruct Hintys as [Heq | Hin]; exists tys; auto; inversion Heq; subst; contradiction.
    + (*Pwild case*)
      inv Hsome. split; assumption.
Qed.

Lemma populate_all_snd_strong {B: Type} (is_constr: funsym -> bool)
  (P: list (list pattern * B)) y (f: funsym) tys ps:
  simplified P ->
  populate_all is_constr P = Some y ->
  In (f, tys, ps) (snd y) ->
  existsb (constr_args_at_head_strong f tys ps) P.
Proof.
  intros Hsimpl. unfold populate_all.
  destruct (get_heads P) as[heads|] eqn : Hhead; [|discriminate].
  rewrite fold_left_right_opt.
  (* unfold constr_args_at_head_strong. *)
  rewrite <- (rev_involutive P) at 1.
  rewrite existsb_rev. 
  assert (Hhead1: get_heads (rev P) = Some (rev heads)). {
    rewrite get_heads_rev, Hhead. reflexivity.
  }
  clear Hhead.
  rewrite <- simplified_rev in Hsimpl.
  (*Now, same direction*)
  generalize dependent (rev heads).
  revert y f tys ps. 
  induction (rev P) as [| [ps a] t IH]; simpl; auto; intros y cs tys pats hds1.
  - inv Hsome. simpl. inv Hsome. simpl. contradiction.
  - simpl in *. destruct ps as [| p ps]; [discriminate|].
    apply andb_prop in Hsimpl.
    destruct Hsimpl as [Hsimphd Hsimptl].
    destruct (get_heads t) as [tl|] eqn : Hheadtl; simpl in *; [|discriminate].
    inv Hsome. simpl.
    specialize (IH Hsimptl).
    destruct (fold_right_opt _ tl _) as [y1|] eqn : Hfold; simpl; [|discriminate].
    specialize (IH y1 cs tys pats tl eq_refl Hfold).
    intros Hpop Hin.
    destruct p as [| f1 tys1 pats1 | | |]; simpl in *; try discriminate.
    + (*Pconstr*)
      destruct y1 as [css csl]; simpl in *.
      destruct (is_constr f1) eqn : Hconstr; [|discriminate].
      destruct (amap_mem funsym_eq_dec f1 css) eqn : Hmem.
      * inversion Hpop; subst; simpl in *.
        apply IH in Hin. rewrite Hin, orb_true_r. auto.
      * inversion Hpop; subst; simpl in *.
        destruct Hin as [Heq | Hin].
        -- inversion Heq; subst.
          unfold constr_args_at_head_strong. simpl.
          destruct (funsym_eqb_spec cs cs); [|contradiction].
          destruct (list_eqb_spec _ vty_eq_spec tys tys); [|contradiction].
          destruct (list_eqb_spec _ pattern_eqb_spec pats pats); [|contradiction].
          reflexivity.
        -- rewrite IH; auto. rewrite orb_true_r; auto.
    + (*Pwild*)
      inversion Hpop; subst; auto.
Qed.

(*Part 6: Dealing with [match_rep] (iterated pattern matching)*)

(*TODO: move - also proved in Denotational implicitly - move to sep lemma*)
Lemma match_rep_irrel v
   (b1: bool) (ty: gen_type b1) ty1 
  (d: domain (dom_aux pd) (v_subst vt ty1)) pats Hpats1 Hpats2 Hpats3 Hpats4 :

  match_rep gamma_valid pd vt v (term_rep gamma_valid pd vt pf) 
    (formula_rep gamma_valid pd vt pf) b1 ty ty1 d pats Hpats1 Hpats2 =
  match_rep gamma_valid pd vt v (term_rep gamma_valid pd vt pf) 
    (formula_rep gamma_valid pd vt pf) b1 ty ty1 d pats Hpats3 Hpats4.
Proof.
  revert Hpats1 Hpats2 Hpats3 Hpats4. induction pats as [| p ptl IH]; simpl; auto.
  intros. destruct p as [p a]; simpl.
  rewrite match_val_single_irrel with (Hval2:=Forall_inv Hpats3). simpl in *.
  destruct (match_val_single _ _ _ _ p (Forall_inv Hpats3) _) eqn : Hmatch; auto.
  destruct b1; auto.
  - apply term_rep_irrel.
  - apply fmla_rep_irrel.
Qed.  

Lemma gen_match_rep v (ty: gen_type b) (t: term) (ty1: vty) (pats: list (pattern * gen_term b)) 
  (Hty: gen_typed b (gen_match t ty1 pats) ty) 
  (Hty1: term_has_type gamma t ty1)
  (Hpats1: Forall (fun x => pattern_has_type gamma (fst x) ty1) pats)
  (Hpats2: Forall (fun x => gen_typed b (snd x) ty) pats):
  gen_rep v ty (gen_match t ty1 pats) Hty =
  match_rep gamma_valid pd vt v (term_rep gamma_valid pd vt pf) (formula_rep gamma_valid pd vt pf)
    b ty ty1 (term_rep gamma_valid pd vt pf v t ty1 Hty1) pats Hpats1 Hpats2.
Proof.
  revert Hty.
  unfold gen_match, gen_rep. destruct b; simpl in *; auto; intros;
  simp term_rep; simpl; erewrite term_rep_irrel with (Hty2:=Hty1); erewrite match_rep_irrel;
    reflexivity.
Qed.

(*TODO: fix [gen_typed] implicits*)
Lemma gen_match_typed (tm: term) (ty1: vty) (ps: list (pattern * gen_term b))
  (ty2: gen_type b):
  term_has_type gamma tm ty1 ->
  Forall (fun x => pattern_has_type gamma (fst x) ty1 /\  @gen_typed gamma b (snd x) ty2) ps ->
  negb (null ps) ->
  @gen_typed gamma b (gen_match tm ty1 ps) ty2.
Proof.
  unfold gen_match.
  destruct b; simpl; intros Htm Hand; apply Forall_and_inv in Hand; destruct Hand as [Hpats Htms];
  intros Hnull; constructor; auto; rewrite <- Forall_forall; auto.
Qed.

(*If everything in the first list does not match, we can ignore it in [match_rep]*)
Lemma match_rep_app2 v ps1 ps2 ty dom_t Hty1 Hty2
  (Hps1: forall p Hp, In p ps1 -> match_val_single gamma_valid pd vt ty (fst p) Hp dom_t = None):
  match_rep gamma_valid pd vt v (term_rep gamma_valid pd vt pf) (formula_rep gamma_valid pd vt pf) b ret_ty ty dom_t 
    (ps1 ++ ps2) Hty1 Hty2 =
  match_rep gamma_valid pd vt v (term_rep gamma_valid pd vt pf) (formula_rep gamma_valid pd vt pf) b ret_ty ty dom_t 
    ps2 (Forall_app_snd Hty1) (Forall_app_snd Hty2).
Proof.
  generalize dependent (Forall_app_snd Hty1). generalize dependent (Forall_app_snd Hty2). revert Hty1 Hty2.
  induction ps1 as [|[p t] ptl IH]; simpl; auto.
  - intros. apply match_rep_irrel.
  - simpl in *. intros Hty1 Hty2 Hty3 Hty4. rewrite (Hps1 (p, t)); auto.
Qed.

(*Alt version with [gen_rep] (can't use before because term_rep/formula_rep were not defined)*)
Definition match_rep' v (ty: gen_type b) ty1 dom_t :=
  fix match_rep (ps: list (pattern * (gen_term b)))
    (Hps: Forall (fun x => pattern_has_type gamma (fst x) ty1) ps)
    (Hall: Forall (fun x => gen_typed b (snd x) ty) ps) :
      (gen_ret pd vt b ty) :=
    match ps as l' return
      Forall (fun x => pattern_has_type gamma (fst x) ty1) l' ->
      Forall (fun x => gen_typed b (snd x) ty) l' ->
      gen_ret pd vt b ty with
    | (p , dat) :: ptl => fun Hpats Hall =>
      match (match_val_single gamma_valid pd vt ty1 p (Forall_inv Hpats) dom_t) with
      | Some l => 
          gen_rep (extend_val_with_list pd vt v l) ty dat (Forall_inv Hall)
      | None => match_rep ptl (Forall_inv_tail Hpats) (Forall_inv_tail Hall)
      end
    | _ => (*Will not reach if exhaustive*) fun _ _ => gen_default pd vt b ty 
    end Hps Hall .

Lemma match_rep_equiv v ty ty1 dom_t ps Hps Hall:
  match_rep gamma_valid pd vt v (term_rep gamma_valid pd vt pf) (formula_rep gamma_valid pd vt pf) b ty ty1 dom_t ps Hps Hall =
  match_rep' v ty ty1 dom_t ps Hps Hall.
Proof.
  unfold match_rep'.
  reflexivity.
Qed.


(*Part 7: Lemmas about [gen_getvars]*)

Lemma gen_getvars_let (v1: vsymbol) (tm: term) (a: gen_term b) (x: vsymbol):
  In x (gen_getvars (gen_let v1 tm a)) <->
  v1 = x \/ In x (tm_bnd tm) \/ In x (tm_fv tm) \/ In x (gen_getvars a).
Proof.
  unfold gen_let, gen_getvars.
  destruct b; simpl; simpl_set_small; rewrite !in_app_iff; simpl_set_small;
  split; intros; destruct_all; auto; destruct (vsymbol_eq_dec v1 x); auto.
Qed.

Lemma gen_fv_getvars t: forall x, In x (gen_fv t) -> In x (gen_getvars t).
Proof.
  intros x. unfold gen_fv, gen_getvars. destruct b; rewrite in_app_iff; auto.
Qed.

(*We need a lemma: verything in gen_getvars of a row in (spec rl c) is in
  gen_getvars of a row in rl*)
Lemma gen_getvars_spec {rl c row x}:
  In row (spec rl c) -> In x (gen_getvars (snd row)) ->
  exists row1, In row1 rl /\ In x (gen_getvars (snd row1)).
Proof.
  induction rl as [| rhd rtl IH]; simpl; [contradiction|].
  destruct rhd as [ps a]; simpl in *.
  destruct ps as [| phd ptl]; auto.
  - intros Hinr Hinx. destruct (IH Hinr Hinx) as [r1 [Hinr1 Hinx1]].
    exists r1. auto.
  - destruct phd; auto; try solve[intros Hinr Hinx; destruct (IH Hinr Hinx) as [r1 [Hinr1 Hinx1]];
    exists r1; auto].
    + destruct (funsym_eqb_spec f c); subst; 
      [|solve[intros Hinr Hinx; destruct (IH Hinr Hinx) as [r1 [Hinr1 Hinx1]]; exists r1; auto]].
      simpl. intros [Hr | Hinr] Hinx;
      [|solve[destruct (IH Hinr Hinx) as [r1 [Hinr1 Hinx1]]; exists r1; auto]].
      subst. simpl in Hinx. exists ((Pconstr c l l0 :: ptl, a)). auto.
    + simpl. intros [Hr | Hinr] Hinx; (*WAY too repetitive*)
      [|solve[destruct (IH Hinr Hinx) as [r1 [Hinr1 Hinx1]]; exists r1; auto]].
      subst. simpl in Hinx. exists (Pwild :: ptl, a); auto.
Qed.

(*Part 8: Dealing with valuations*)

(*If we have [matches_row] of a list of variables and arg list al,
  [extend_val_with_list] of the result is just [val_with_args] (map each var to the 
  corresponding element of the arg_list)*)
Lemma matches_row_allvars v tys1 (tys2 : list sort) (Heq: tys2 = map (v_subst vt) tys1) (*ugh*) (al: arg_list (domain (dom_aux pd)) tys2) vars Hvarsty:
  exists l, matches_row tys1 (cast_arg_list Heq al) (map Pvar vars) Hvarsty = Some l /\
  forall x, extend_val_with_list pd vt v l x = val_with_args pd vt v vars al x.
Proof.
  subst. unfold cast_arg_list. simpl.
  generalize dependent Hvarsty.
  revert vars.
  induction tys1 as [| ty tys1 IH]; simpl; intros [| var1 vars] Hvarsty; try solve[inversion Hvarsty]; simpl.
  - simp matches_row. exists nil. split; auto.
  - simpl in *. simp matches_row. simpl.
    rewrite (hlist_inv al). simpl.
    specialize (IH (hlist_tl al) vars (Forall2_inv_tail Hvarsty)).
    destruct IH as [l1 [Hl1 Hvals]]. rewrite Hl1. simpl.
    eexists. split; [reflexivity|].
    intros x.
    inversion Hvarsty; subst. inversion H2; subst.
    destruct (vsymbol_eq_dec var1 x); subst.
    + destruct (vty_eq_dec _ _); [|contradiction].
      unfold extend_val_with_list; simpl. destruct (vsymbol_eq_dec x x); [|contradiction]. simpl.
      destruct (sort_eq_dec _ _); [|contradiction].
      apply dom_cast_eq.
    + (*Both cases identical*)
      assert (extend_val_with_list pd vt v
        ((var1, existT (domain (dom_aux pd)) (v_subst vt (snd var1)) (hlist_hd al)) :: l1) x =
        val_with_args pd vt v vars (hlist_tl al) x).
      {
        unfold extend_val_with_list. simpl.
        destruct (vsymbol_eq_dec x var1); subst; [contradiction|].
        apply Hvals.
      }
      destruct (vty_eq_dec _ _); auto.
Qed.

(*Reverse [val_with_args] (TODO: move?) is equivalent*)
Lemma val_with_args_rev v vars {srts} (al: arg_list (domain (dom_aux pd)) srts):
  NoDup vars ->
  map (v_subst vt) (map snd vars) = srts -> 
  forall x, val_with_args pd vt v (rev vars) (hlist_rev (domain (dom_aux pd)) _ al) x =
    val_with_args pd vt v vars al x.
Proof.
  rewrite map_map. intros Hnodup Hsrts x; subst.
  set (srts:=(map (fun x0 : string * vty => v_subst vt (snd x0)) vars)). 
  destruct (in_dec vsymbol_eq_dec x vars) as [Hin | Hnotin].
  - destruct (In_nth _ _ vs_d Hin) as [i [Hi Hx]].
    assert (Hnth: nth i srts s_int = v_subst vt (snd x)).
    {
      unfold srts. rewrite map_nth_inbound with (d2:=vs_d); subst; auto.
    }
    rewrite (val_with_args_in') with (i:=i)(Heq:=Hnth); auto.
    2: unfold srts; rewrite map_length; reflexivity.
    assert (Hx': nth ((length vars - S i )) (rev vars) vs_d  = x). {
      subst. symmetry. rewrite rev_nth1; auto.
    }
    assert (Hnth': nth (length vars - S i) (rev srts) s_int = v_subst vt (snd x)).
    {
      rewrite <- Hx. rewrite (rev_nth1 vars); auto.
      unfold srts. rewrite <- map_rev.
      rewrite map_nth_inbound with (d2:=vs_d); auto. rewrite rev_length.
      destruct vars; simpl in *; try lia.
    }
    rewrite (val_with_args_in') with (i:=(length vars - S i))(Heq:=Hnth'); auto;
    try rewrite !rev_length; auto; [| apply NoDup_rev; auto|
      unfold srts; rewrite map_length; auto |destruct vars; simpl in *; lia].
    destruct (hlist_rev_hnth _ (length vars - S i) srts al s_int (dom_int pd)
      ltac:(unfold srts; rewrite map_length; destruct vars; simpl in *; lia)) as [Heq Hrev].
    rewrite Hrev. rewrite dom_cast_compose.
    generalize dependent (eq_trans Heq Hnth').
    replace (Datatypes.length srts - S (Datatypes.length vars - S i)) with i.
    2: { unfold srts; rewrite map_length. destruct vars; simpl in *; try lia.
      (*Why can't lia solve this directly?*)
    assert (i <= length vars) by (apply Arith_prebase.lt_n_Sm_le in Hi; assumption). lia.
    }
    intros e. apply dom_cast_eq.
  - rewrite !val_with_args_notin; auto. rewrite <- List.in_rev. auto.
Qed.

Lemma terms_to_hlist_change_vv v1 v2 ts tys Hall:
  (forall t x, In t ts -> In x (tm_fv t) -> v1 x = v2 x) ->
  terms_to_hlist v1 ts tys Hall = terms_to_hlist v2 ts tys Hall.
Proof.
  intros Halleq. generalize dependent tys. induction ts as [| t ts IH]; intros [| ty1 tys] Hall;
  try solve[inversion Hall]; auto.
  simp terms_to_hlist. simpl in *.
  rewrite tm_change_vv with (v2:=v2) by (intros x Hinx; apply (Halleq t); auto).
  rewrite IH; auto.
  intros t1 x Hint1 Hinx; apply (Halleq t1 x); auto.
Qed.

(*[terms_to_hlist] on vars vs under valuation (vs -> al) is just al*)
Lemma terms_to_hlist_val_with_args v vars tys {srts1} (Heq: srts1 = map (v_subst vt) tys) al Htys (Hn: NoDup vars):
  terms_to_hlist (val_with_args pd vt v vars al) (map Tvar vars) tys Htys = cast_arg_list Heq al.
Proof.
  subst. unfold cast_arg_list; simpl.
  generalize dependent tys. induction vars as [| v1 vars IH]; intros [| ty1 tys]; simpl; intros
  al Htys; try solve[inversion Htys]; auto.
  - simp terms_to_hlist. symmetry. apply hlist_nil.
  - simp terms_to_hlist. simpl. simp term_rep. simpl.
    unfold var_to_dom. rewrite (hlist_inv al). simpl.
    inversion Htys; subst. inversion H2; subst.
    destruct (vty_eq_dec _ _); [|contradiction].
    destruct (vsymbol_eq_dec _ _); [| contradiction].
    inversion Hn; subst; auto.
    erewrite terms_to_hlist_change_vv with (v2:=val_with_args pd vt v vars (hlist_tl al)).
    + rewrite IH; auto. f_equal. rewrite !dom_cast_compose. apply dom_cast_refl.
    + intros t x Hint Hinx.
      rewrite in_map_iff in Hint. destruct Hint as [y [Ht Hiny]]; subst.
      destruct Hinx as [Hx | []]; subst.
      destruct (vsymbol_eq_dec v1 x); subst; [contradiction|].
      destruct (vty_eq_dec _ _); auto.
Qed.

(*We can change the valuation for [matches_matrix] as long
  as they agree on all free variables in the matrix actions*)
Lemma matches_matrix_change_vv (v1 v2: val_vars pd vt) tys al P Hp
  (Heq: forall x row, In row P -> In x (gen_getvars (snd row)) -> v1 x = v2 x):
  matches_matrix v1 tys al P Hp = matches_matrix v2 tys al P Hp.
Proof.
  revert Hp. induction P; intros Hp; simp matches_matrix; auto.
  simpl in *.
  destruct (matches_row _ _ _ _); auto.
  - f_equal. apply gen_rep_change_vv.
    intros x Hinx. simpl in *.
    assert (Hv12: v1 x = v2 x). {
      apply (Heq x a); auto. apply gen_fv_getvars; auto.
    }
    unfold extend_val_with_list.
    destruct (get_assoc_list vsymbol_eq_dec l x); auto.
    destruct (sort_eq_dec _ _); auto.
  - apply IHP; auto. intros x row Hinrow Hinx; apply (Heq x row); auto.
Qed.

(*Part 9: Rewrite [add] function in nicer way*)

(*A "map" version of "add" (asusming all options are Some) that is more pleasant to work with*)
Definition add_map (getvars: gen_term b -> list vsymbol) (comp_cases : funsym -> list (term * vty) -> option (gen_term b)) (t: term) ty tl rl :=
(fun (x: funsym * list vty * list pattern) =>
          let '(cs, params, ql) := x in 
          let pat_tys := map (ty_subst (s_params cs) params) (s_args cs) in 
          let new_var_names := gen_strs (Datatypes.length ql) (compile_fvs getvars ((t, ty) :: tl) rl) in
          let typed_vars := (combine new_var_names pat_tys) in
          let vl := rev typed_vars in 
          let pl := rev_map Pvar vl in 
          let al := rev_map Tvar vl in
          (Pconstr cs params pl, comp_cases cs (combine al (rev (map snd vl))))).

(*And the spec*)
Lemma fold_right_opt_add_map getvars comp_cases t ty rl tl cslist bse pats:
  fold_left_opt (add getvars comp_cases t ty rl tl) cslist bse = Some pats ->
  (* map Some l = bse -> *)
  rev (map (add_map getvars comp_cases t ty tl rl) cslist) ++ (map (fun x => (fst x, Some (snd x))) bse) =
  map (fun x => (fst x, Some (snd x))) pats.
Proof.
  intros Hadd.
  unfold add in Hadd.
  erewrite fold_left_opt_change_f in Hadd.
  apply (fold_left_opt_cons (fun (x: funsym * list vty * list pattern) =>
    let cs := fst (fst x) in
    let params := snd (fst x) in
    let ql := snd x in
    let pat_tys := map (ty_subst (s_params cs) params) (s_args cs) in 
    let new_var_names := gen_strs (Datatypes.length ql) (compile_fvs getvars ((t, ty) :: tl) rl) in
    let typed_vars := (combine new_var_names pat_tys) in
    let vl := rev typed_vars in 
    let pl := rev_map Pvar vl in 
    let al := rev_map Tvar vl in
    comp_cases cs (combine al (rev (map snd vl))))
    (fun (x: funsym * list vty * list pattern) =>
      let cs := fst (fst x) in
      let params := snd (fst x) in
      let ql := snd x in
      let pat_tys := map (ty_subst (s_params cs) params) (s_args cs) in 
      let new_var_names := gen_strs (Datatypes.length ql) (compile_fvs getvars ((t, ty) :: tl) rl) in
      let typed_vars :=(combine new_var_names pat_tys) in
      let vl := rev typed_vars in 
      let pl := rev_map Pvar vl in 
      Pconstr cs params pl
      )
  ) in Hadd.
  2: { simpl. intros. destruct c as [[f vs] ps]; simpl; reflexivity. }
  erewrite (map_ext (fun x => (fst x, Some (snd x)))). rewrite <- Hadd.
  simpl. f_equal.
  2: simpl; intros [x1 y1]; auto.
  f_equal.
  apply map_ext. intros [[f vs] ps]; simpl; auto.
Qed.

(*Part 10: 2 more typing lemmas*)

Lemma constr_typed_row {c tys ps ty}:
  pattern_has_type gamma (Pconstr c tys ps) ty ->
  row_typed (ty_subst_list (s_params c) tys (s_args c)) ps.
Proof.
  intros Hp; inversion Hp; subst.
  apply Forall2_nth.
  unfold ty_subst_list; rewrite !map_length. split; auto. intros i d1 d2 Hi.
  apply (H8 (nth i ps d1, (nth i (seq.map (ty_subst (s_params c) tys) (s_args c)) d2))).
  rewrite in_combine_iff; [| rewrite map_length; lia].
  exists i. split; auto. intros. f_equal; apply nth_indep; auto. rewrite map_length; lia.
Qed.

(*A constructor at the head of a well-typed pattern matrix has the first type*)
Lemma constr_at_head_ex_type {ty tys rl c}:
  pat_matrix_typed (ty :: tys) rl ->
  constr_at_head_ex c rl ->
  exists tys ps, pattern_has_type gamma (Pconstr c tys ps) ty.
Proof.
  unfold pat_matrix_typed. intros [Hrows _] Hex.
  apply existsb_exists in Hex.
  destruct Hex as [row [Hinrow Hconstr]].
  unfold constr_at_head in Hconstr.
  rewrite Forall_forall in Hrows.
  specialize (Hrows _ Hinrow).
  destruct row as [[| phd ptl] a]; simpl in *; [discriminate|].
  destruct phd as [| f' tys1 ps1 | | |]; try discriminate.
  destruct (funsym_eqb_spec f' c); subst; [|discriminate].
  inversion Hrows; subst.
  exists tys1. exists ps1. auto.
Qed.

Section CompileTheorem.

(*First, as separate lemma, prove main case directly (comp_full), assuming IH*)
Lemma comp_full_correct (v : val_vars pd vt) (t : term) (ty : vty) (tl : list (term * vty)) 
(rl : list (list pattern * gen_term b)) t1
(Htmtys : Forall2 (term_has_type gamma) (t :: map fst tl) (ty :: map snd tl))
(Hp : pat_matrix_typed (map snd ((t, ty) :: tl)) rl)
(Hdisj : pat_matrix_var_names_disj (map fst ((t, ty) :: tl)) rl)
(Hsimp : simplified rl)
(casewild : amap funsym (list (list pattern * gen_term b)) * list (list pattern * gen_term b))
(types_cslist : amap funsym (list pattern) * list (funsym * list vty * list pattern))
{m : mut_adt} {a : alg_datatype} {args : list vty} (m_in : mut_in_ctx m gamma)
(a_in : adt_in_mut a m)
(Hty : ty = vty_cons (adt_name a) args)
(args_len : length args = length (m_params m))
:
let css := match ty with
| vty_cons ts _ => get_constructors ts
| _ => []
end  : list funsym in
let is_constr := fun fs : funsym => in_bool funsym_eq_dec fs css in
let types := fst types_cslist in
let cslist := snd types_cslist in
let cases := fst casewild in
let wilds := snd casewild in
forall (Hpop : populate_all is_constr rl = Some types_cslist)
(Hdisp : casewild = dispatch1 gen_let t types rl)
(IHconstrs : forall (cs : funsym)
  (al : list (term * vty))
  (l : list (list pattern * gen_term b)),
amap_get funsym_eq_dec cases cs = Some l ->
pat_matrix_var_names_disj
  (map fst (rev al ++ tl)) l ->
forall
  (Htys : Forall2 (term_has_type gamma)
  (map fst (rev al ++ tl))
  (map snd (rev al ++ tl)))
  (Hp : pat_matrix_typed (map snd (rev al ++ tl)) l)
  (v : val_vars pd vt) (t : gen_term b),
compile get_constructors gen_match gen_let
  gen_getvars (rev al ++ tl) l =
Some t ->
exists Hty : gen_typed b t ret_ty,
matches_matrix_tms v
  (map fst (rev al ++ tl))
  (map snd (rev al ++ tl)) l Htys Hp =
Some (gen_rep v ret_ty t Hty))
(Htywild : pat_matrix_typed (map snd tl) wilds)
(IHwilds : forall (v : val_vars pd vt)
  (t0 : gen_term b),
compile get_constructors gen_match gen_let
  gen_getvars tl wilds =
Some t0 ->
exists Hty : gen_typed b t0 ret_ty,
matches_matrix_tms v (map fst tl)
  (map snd tl) wilds
  (Forall2_inv_tail Htmtys) Htywild =
Some (gen_rep v ret_ty t0 Hty))
(Htypesemp : amap_is_empty types = false),
let comp_wilds := fun _ : unit => compile get_constructors gen_match gen_let gen_getvars tl wilds in
let comp_cases := fun (cs : funsym) (al : list (term * vty)) =>
  comp_cases (compile get_constructors gen_match gen_let gen_getvars) cases tl cs al in
let comp_full := comp_full gen_match gen_getvars
  comp_wilds comp_cases types cslist css t ty tl rl : unit -> option (gen_term b) in
comp_full tt = Some t1 ->
      exists Hty : gen_typed b t1 ret_ty,
      matches_matrix_tms v (t :: map fst tl)
        (ty :: map snd tl) rl Htmtys Hp =
      Some (gen_rep v ret_ty t1 Hty).
Proof.
  intros css is_constr types cslist cases wilds Hpop Hdisp IHconstrs Htywild IHwilds Htypesemp 
    comp_wilds comp_cases comp_full.
  unfold comp_full, Pattern.comp_full.
  intros Ht1.
  (*First, get [comp_full] in a nicer form*)
  set (no_wilds := forallb (fun f : funsym => amap_mem funsym_eq_dec f types) css) in *.
  set (base :=(if no_wilds then Some [] else option_map (fun x : gen_term b => [(Pwild, x)]) (comp_wilds tt))) in *.
  destruct base as [bse|] eqn : Hbase; [| discriminate]. simpl in Ht1.
  destruct (fold_left_opt (add gen_getvars comp_cases t ty rl tl) cslist bse) as [pats|] eqn : Hadd;[|discriminate].
  simpl in Ht1.
  revert Ht1. inv Ht1.
  (*Nicer to use map rather than [fold_left_opt]*)
  assert (Hpats:
    rev (map (add_map gen_getvars comp_cases t (vty_cons (adt_name a) args) tl rl) cslist) ++ (if no_wilds then [] else [(Pwild, comp_wilds tt)]) =
    map (fun x => (fst x, Some (snd x))) pats).
  {
    apply fold_right_opt_add_map in Hadd. rewrite <- Hadd.
    f_equal. destruct no_wilds; simpl in *.
    - unfold base in Hbase. revert Hbase. inv Hsome. reflexivity.
    - revert Hbase. unfold base. destruct (comp_wilds tt); simpl; inv Hsome; auto.
  }
  (*This spec is much easier to work with*)
  clear Hadd.
  (*This result will be useful in several places - typing for elements of [cslist]*)
  assert (Hclist_types: forall {c tys ps},
    In (c, tys, ps) cslist ->
    pattern_has_type gamma (Pconstr c tys ps) (vty_cons (adt_name a) args)).
  {
    clear -Hp Hpop Hsimp. simpl in *.
    intros c tys ps Hinc.
    assert (Hconstrc: existsb (constr_args_at_head_strong c tys ps) rl).
    {
      eapply populate_all_snd_strong; auto.
      apply Hpop. auto.
    }
    apply existsb_exists in Hconstrc.
    destruct Hconstrc as [row [Hinrow Hstrong]].
    revert Hp. simpl.
    unfold pat_matrix_typed. intros [Hrows _].
    rewrite Forall_forall in Hrows.
    specialize (Hrows _ Hinrow).
    unfold constr_args_at_head_strong in Hstrong.
    destruct row as [[| p1 row1] a1]; [discriminate|].
    simpl in Hstrong.
    destruct p1 as [| f1 tys1 pats1 | | |]; try discriminate.
    destruct (funsym_eqb_spec f1 c); subst; [|discriminate].
    destruct (list_eqb_spec _ vty_eq_spec tys tys1); subst; [|discriminate].
    destruct (list_eqb_spec _ pattern_eqb_spec ps pats1); subst; [|discriminate].
    inversion Hrows; subst; auto.
  }
  (*Some additional info we need from typing*)
  assert (Hcargs: forall {c tys ps},
    In (c, tys, ps) cslist -> constr_in_adt c a /\ tys = args).
  {
    intros c tys ps Hinc; specialize (Hclist_types c tys ps Hinc).
    inversion Hclist_types; subst.
    destruct H11 as [m1 [a1 [m_in1 [a_in1 c_in1]]]].
    rewrite (adt_constr_ret gamma_valid m_in1 a_in1) in H2; auto.
    unfold sigma in H2. rewrite ty_subst_cons in H2.
    inversion H2; subst.
    assert (m1 = m) by (apply (mut_adts_inj (valid_context_wf _ gamma_valid) m_in1 m_in a_in1 a_in); auto).
    subst.
    assert (a1 = a) by (apply (adt_names_inj' gamma_valid a_in1 a_in m_in); auto). subst.
    split; [exact c_in1 |].
    rewrite <- (adt_constr_params gamma_valid m_in a_in c_in1).
    rewrite map_ty_subst_var; auto. apply s_params_Nodup.
  }
  assert (Hcallval: forall {c tys ps},
    In (c, tys, ps) cslist ->
    Forall (valid_type gamma) (map (ty_subst (s_params c) tys) (s_args c))). 
  {
    intros c tys ps Hin.
    specialize (Hclist_types _ _ _ Hin).
    inversion Hclist_types; subst. rewrite Forall_nth. intros i d. rewrite map_length; intros Hi.
    apply pat_has_type_valid with (p:=nth i ps Pwild).
    specialize (H9 (nth i ps Pwild, nth i 
      (map (ty_subst (s_params c) tys) (s_args c)) d)).
    apply H9. rewrite in_combine_iff; [| rewrite map_length; auto].
    exists i. split; [lia|]. intros d1 d2.
    f_equal; apply nth_indep; [| rewrite map_length]; lia.
  }
  (*Instantiate IHconstrs for each possible constructor so that we don't need to
    do it multiple times*)
  assert (IHconstrs' : forall (c: funsym) tys1 ps1,
    In (c, tys1, ps1) cslist ->
    let ty := vty_cons (adt_name a) args in
    let new_typs := (map (ty_subst (s_params c) tys1) (s_args c)) in
    let new_vars :=(combine (gen_strs (Datatypes.length ps1) (compile_fvs gen_getvars ((t, ty) :: tl) rl)) new_typs) in
    forall (v: val_vars pd vt) (t: gen_term b),
        compile get_constructors gen_match gen_let gen_getvars (rev (combine (map Tvar new_vars) new_typs) ++ tl) (spec rl c) = Some t ->
    (*Exists so we only have to prove once*)
    exists (Htys: Forall2 (term_has_type gamma) ((rev (map Tvar new_vars)) ++ map fst tl)
      (rev new_typs ++ map snd tl))
      (Hp: pat_matrix_typed (rev new_typs ++ map snd tl) (spec rl c))
      (Hty: gen_typed b t ret_ty),
          matches_matrix_tms v ((rev (map Tvar new_vars)) ++ map fst tl) (rev new_typs ++ map snd tl) (spec rl c) Htys Hp =
          Some (gen_rep v ret_ty t Hty)).
  {
    intros c tys1 ps1 Hinc ty new_typs new_vars v1 t1 Hcompile.
    specialize (IHconstrs c (combine (map Tvar new_vars) new_typs) (spec rl c)).
    forward IHconstrs.
    { unfold cases. eapply dispatch1_equiv_spec; eauto.
      rewrite amap_mem_spec.
      replace (amap_get funsym_eq_dec (fst types_cslist) c) with (Some ps1); auto.
      symmetry. apply (proj2 (populate_all_fst_snd_full _ _ _ Hsimp Hpop)).
      exists tys1; apply Hinc.
    }
    assert (Hvarstyps: length new_vars = length new_typs). {
      unfold new_vars. rewrite combine_length, gen_strs_length.
      assert (length ps1 = length new_typs); try lia.
      unfold new_typs. rewrite map_length; auto. 
      specialize (Hclist_types _ _ _ Hinc); inversion Hclist_types; auto.
    }
    revert IHconstrs.
    (*Simplify lists in IHConstrs*)
    rewrite !rev_combine, !map_app, !map_fst_combine;
    try solve[try rewrite !rev_length; try rewrite !map_length; auto].
    rewrite !map_snd_combine; [| rewrite !rev_length, !map_length; auto].
    intros IHconstrs.
    assert (Hlen: length ps1 = length (s_args c)). {
      specialize (Hclist_types _ _ _ Hinc); inversion Hclist_types; subst; auto.
    }
    forward IHconstrs.
    {
      (*Prove disjoint*) unfold vsymbol in *.
      (*Different [disj] lemma*)
      eapply disj_spec1. apply Hdisj.
      revert Hdisj; clear -Hlen. (*need to know length ps = length (s_argcs c)*) simpl. 
      unfold pat_matrix_var_names_disj; intros Hdisj.
      intros x [Hinx1 Hinx2].
      rewrite in_map_big_union with (eq_dec1:=string_dec)  in Hinx1 .
      simpl_set. destruct Hinx1 as [t1 [Hint1 Hinx1]]. rewrite <- List.in_rev in Hint1.
      rewrite in_map_iff in Hint1. destruct Hint1 as [[n ty1] [Ht1 Hiny]]; subst. simpl in Hinx1.
      destruct Hinx1 as [Hx | []]; subst.
      unfold new_vars, new_typs in Hiny.
      (*Contradiction, x cannot be in names of rl and in [gen_strs]*)
      rewrite in_combine_iff in Hiny; rewrite gen_strs_length in *; [| rewrite map_length; auto] .
      destruct Hiny as [i [Hi Hxty]]. specialize (Hxty ""%string vty_int).
      inversion Hxty.
      assert (Hnotin: ~ In x (map fst (compile_fvs gen_getvars ((t, ty) :: tl) rl))). {
        apply (gen_strs_notin' (length ps1)). subst. apply nth_In. rewrite gen_strs_length; auto. }
      apply Hnotin. unfold compile_fvs. rewrite !map_app. rewrite !in_app_iff; auto.
    }
    assert (Htys : Forall2 (term_has_type gamma)
      (rev (map Tvar new_vars) ++ map fst tl)
      (rev new_typs ++ map snd tl)).
    {
      (*Prove terms are typed correctly*) 
      unfold vsymbol in *.
      apply Forall2_app.
      2: { inversion Htmtys; auto. }
      apply Forall2_rev.
      (*Prove all variables have correct type*)
      apply Forall2_nth; rewrite map_length; split; [auto|].
      intros i d1 d2 Hi.
      assert (Hi': i < length (s_args c)) by
        (rewrite Hvarstyps in Hi; unfold new_typs in Hi; rewrite map_length in Hi; exact Hi).
      rewrite map_nth_inbound with (d2:=(""%string, vty_int)) by auto. 
      apply T_Var'.
      -- (*We proved [valid_type] already*)
        specialize (Hcallval _ _ _ Hinc).
        rewrite Forall_forall in Hcallval; apply Hcallval, nth_In. rewrite map_length; assumption.
      -- unfold new_vars, new_typs. rewrite combine_nth; [| rewrite gen_strs_length, map_length; lia].
          simpl. apply nth_indep; rewrite map_length; assumption.
    }
    assert (Hp' : pat_matrix_typed (rev new_typs ++ map snd tl) (spec rl c)).
    {
      specialize (Hcargs _ _ _ Hinc). destruct Hcargs as [c_in Htys1]; subst.
      apply (spec_typed_adt m_in a_in); auto.
    }
    (*Now we use IH*)
    exists Htys. exists Hp'. apply (IHconstrs Htys Hp' v1 t1).
    rewrite <- Hcompile. f_equal. rewrite rev_combine. reflexivity.
    rewrite map_length. assumption.
  }
  (*The stronger typing result we need in multiple places:*)
  (*Now we use previous result about [pats]*)
  assert (Hallty: Forall (fun x =>
    pattern_has_type gamma (fst x) (vty_cons (adt_name a) args) /\
    forall y, snd x = Some y -> @gen_typed gamma b y ret_ty)
    (map (fun x => (fst x, Some (snd x))) pats)).
  {
    rewrite <- Hpats.
    rewrite Forall_app. split.
    - (*Prove constrs*)
      rewrite Forall_forall.
      intros x. rewrite <- List.in_rev, in_map_iff.
      intros [y [Hx Hiny]]; subst. simpl. 
      destruct y as [[c tys] ps]; simpl.
      unfold rev_map.
      specialize (Hclist_types _ _ _ Hiny).
      split.
      + (*Prove pattern has correct type*)
        inversion Hclist_types; subst.
        apply P_Constr'; auto.
        2: { unfold rev_map. (*prove disj by uniqueness of generated variable names*)
          rewrite !map_rev, !rev_involutive, !map_length, 
          !combine_length, !gen_strs_length,
          !map_length, H6, Nat.min_id.
          intros i j d Hi Hj Hij.
          rewrite !map_nth_inbound with (d2:=(""%string, vty_int));
          try solve [rewrite combine_length, gen_strs_length,
            map_length; lia].
          simpl.
          rewrite !combine_nth; try solve[rewrite gen_strs_length, map_length; auto].
          intros x. simpl. intros [[Hx1 | []] [Hx2 | []]]; subst.
          inversion Hx2; subst.
          pose proof (gen_strs_nodup (length (s_args c)) (compile_fvs gen_getvars ((t, sigma (f_ret c)) :: tl) rl)) as Hnodup.
          rewrite NoDup_nth in Hnodup.
          rewrite gen_strs_length in Hnodup.
          specialize (Hnodup i j Hi Hj (eq_sym H0)). subst; contradiction.
        }
        unfold rev_map. rewrite !map_rev, !rev_involutive. 
        (*Prove all variables have correct type: not too hard - TODO maybe factor out*)
        apply Forall2_nth; unfold ty_subst_list; rewrite !map_length, combine_length,
            gen_strs_length, map_length, H6, Nat.min_id. split; [reflexivity|].
        intros i d1 d2 Hi.
        rewrite !map_nth_inbound with (d2:=(""%string, vty_int));
          [| rewrite combine_length, gen_strs_length, map_length; lia].
        apply P_Var'.
        * (*We proved valid above*)
          specialize (Hcallval _ _ _ Hiny); rewrite Forall_forall in Hcallval; apply Hcallval.
          apply nth_In.
          rewrite map_length; assumption.
        * rewrite combine_nth; auto.
          -- simpl. apply nth_indep. rewrite map_length; auto.
          -- erewrite gen_strs_length, map_length; auto.
      + (*Now prove that pattern row action is valid - follows from IH, we proved above*)
        specialize (IHconstrs' c tys ps Hiny).
        inversion Hclist_types; subst.
        intros y. unfold comp_cases, Pattern.comp_cases.
        destruct (amap_get funsym_eq_dec cases c) as [c_spec|] eqn : Hccase;
        [|discriminate].
        unfold cases in Hccase.
        assert (Hget:=Hccase).
        erewrite (dispatch1_equiv_spec _ _ _ Hsimp Hpop Hp) in Hccase.
        2: { eapply constrs_in_types. apply Hccase. apply Hpop. }
        revert Hccase; inv Hsome.
        unfold rev_map. rewrite !map_rev, !rev_involutive, !map_snd_combine;
          [|rewrite gen_strs_length, map_length; lia].
        intros Hcompile.
        specialize (IHconstrs' v _ Hcompile).
        destruct IHconstrs' as [Htys [Hp' [Hty Heq]]].
        apply Hty.
    - (*Prove typing for base - easier*)
      rewrite Forall_forall. intros x. destruct no_wilds eqn : Hnowilds; [contradiction|].
      intros [Hx | []]; subst. simpl.
      split.
      2: { intros y Hy. specialize (IHwilds v y Hy).
          destruct IHwilds as [Hty ?]; exact Hty.  }
      (*Idea: some pattern has the type we need, since cslist is not empty*)
      rewrite amap_not_empty_exists in Htypesemp. destruct Htypesemp as  [fs [pats1 Hget]].
      unfold types in Hget.
      rewrite (proj2 (populate_all_fst_snd_full _ _ _ Hsimp Hpop)) in Hget.
      destruct Hget as [tys1 Hinc].
      apply Hclist_types in Hinc. constructor; auto. eapply pat_has_type_valid. apply Hinc.
  }
  (*Prove typing*)
  assert (Htyall: @gen_typed gamma b
    (gen_match t (vty_cons (adt_name a) args) pats) ret_ty).
  {
    apply gen_match_typed; auto.
    - clear -Htmtys. apply Forall2_inv_head in Htmtys; auto.
    - revert Hallty. rewrite Forall_map. apply Forall_impl. simpl.
      intros x [Hall1 Hall2]. split; auto.
    - (*Use fact that types not empty to show pats not null*)
      assert (Hlen: length pats <> 0). {
        erewrite <- map_length, <- Hpats. rewrite app_length, rev_length, map_length.
        (*TODO: factor out? Similar to above, cslist not empty bc types not empty*)
        rewrite amap_not_empty_exists in Htypesemp. destruct Htypesemp as  [fs [pats1 Hget]].
        unfold types in Hget.
        rewrite (proj2 (populate_all_fst_snd_full _ _ _ Hsimp Hpop)) in Hget.
        destruct Hget as [tys1 Hincs]. unfold cslist.
        destruct (snd types_cslist); simpl; auto.
      }
      destruct pats; auto.
  }
  (*Typing proof complete, now prove semantics*)
  exists Htyall.
  assert (Htty: term_has_type gamma t (vty_cons (adt_name a) args)).
  { inversion Htmtys; auto. }
  assert (Hpatsty: Forall (fun x => pattern_has_type gamma (fst x) (vty_cons (adt_name a) args)) pats). {
    revert Hallty. rewrite Forall_map. apply Forall_impl. intros x [Hpat _]; auto. }
  assert (Hactty: Forall (fun x : pattern * gen_term b => @gen_typed gamma b (snd x) ret_ty) pats). {
    revert Hallty. rewrite Forall_map. apply Forall_impl. intros x [_ Htys]. specialize (Htys (snd x)); auto. }
  erewrite gen_match_rep with (Hty1:=Htty)(Hpats1:=Hpatsty)(Hpats2:=Hactty).
  (*Proof sketch:
      [match_rep] is equivalent to [matches_matrix] with single-valued columns.
    then show tha we can split pats into l1 ++ x ++ l2 for any x in l1 st x not in l1.
    Then we get the constructor of [term_rep t].
    Case 1: constructor is in types
      Then we split pats as above and use matches_matrix_app. We know that the result on l1 must be none,
      so we use x, which is [compile] - use IH for the result
    Case 2: constructor not in types
      Then we know all of pats list (before base) is nil, then use base, use default lemma*)
  
  (*One more simplification of [pats] - we can split it into [pats1] and [pats2] corresponding to each list*)
  symmetry in Hpats.
  apply map_eq_app in Hpats. destruct Hpats as [pats1 [pats2 [Hpats [Hpats1 Hpats2]]]]. subst pats.
  destruct (find_semantic_constr v t m_in a_in args_len Htty) as [c [[c_in al] Hsem]]; simpl in Hsem.
  destruct (in_dec funsym_eq_dec c (map (fun x => fst (fst x)) cslist)).
  - (*Case 1: c is in [cslist]*)
    rewrite in_map_iff in i.
    destruct i as [[[f1 tys1] ps1] [Hc Hinc]]; simpl in Hc; subst f1.
    set (ty := (vty_cons (adt_name a) args)) in *.
    assert (Hinpats: In (add_map gen_getvars comp_cases t ty tl rl (c, tys1, ps1)) 
      (map (fun x : pattern * gen_term b => (fst x, Some (snd x))) pats1)).
    {
      rewrite Hpats1, <- In_rev, in_map_iff. exists (c, tys1, ps1); auto.
    }
    rewrite in_map_iff in Hinpats. destruct Hinpats as [[p1 tm1] [Hadd Hinx]].
    (*simplify Hadd*)
    revert Hadd. simpl. unfold rev_map. rewrite !map_rev, !rev_involutive, map_snd_combine.
    2: { rewrite map_length, gen_strs_length; auto. apply Hclist_types in Hinc; inversion Hinc; auto. }
    set (new_typs := (map (ty_subst (s_params c) tys1) (s_args c))) in *.
    set (new_vars :=(combine (gen_strs (Datatypes.length ps1) (compile_fvs gen_getvars ((t, ty) :: tl) rl)) new_typs)) in *.
    intros Hadd; inversion Hadd; subst p1.
    (*Now we know that Pconstr c tys1... is in pats. So we can split pats here - the [NoDup] is important*)
    assert (Hsplitpats1: exists patsa patsb, pats1 = patsa ++ (Pconstr c tys1 (map Pvar new_vars), tm1) :: patsb /\
      forall x y, In (x, y) patsa -> exists c1 tys1 ps1, x = (Pconstr c1 tys1 ps1) /\ c1 <> c).
    {
      apply in_split in Hinx. destruct Hinx as [patsa [patsb Hpats1eq]]; subst. exists patsa. exists patsb.
      split; auto.
      (*Now we need to prove NoDups from NoDups of cslist*)
      revert Hpats1.
      rewrite map_app. simpl. rewrite <- map_rev. intros Hpats1; symmetry in Hpats1.
      apply map_eq_app in Hpats1. destruct Hpats1 as [cl1 [cl2 [Hrev [Hmapc1 Hmapc2]]]].
      subst. intros x y Hinxy.
      assert (Hin2: In (x, Some y) (map (add_map gen_getvars comp_cases t ty tl rl) cl1)). {
        rewrite Hmapc1, in_map_iff. exists (x, y); auto.
      }
      rewrite in_map_iff in Hin2.
      destruct Hin2 as [[[f2 vs2] ps2] [Hxy Hinxy1]]; simpl in Hxy.
      inversion Hxy; subst. exists f2. exists vs2. eexists. split; [reflexivity|].
      intros Hceq.
      (*Contradiction arises from NoDups of cslist*)
      pose proof (proj1 (populate_all_fst_snd_full _ _ _ Hsimp Hpop)) as Hnodup.
      unfold cslist in Hrev.
      apply NoDup_rev in Hnodup. rewrite <- map_rev in Hnodup.
      rewrite Hrev in Hnodup.
      destruct cl2 as [|chd cl2]; [discriminate | inversion Hmapc2; subst; clear Hmapc2].
      revert Hnodup. rewrite map_app. simpl. rewrite NoDup_app_iff'.
      intros [_ [_ Hnotin]]. apply (Hnotin c).
      simpl. split.
      -(*  rewrite in_map_iff in Hin2. destruct Hin2 as [y [Hy Hiny]]. *)
        rewrite in_map_iff. exists (c, vs2, ps2). split; auto.
      - left. destruct chd as [[y1 y2] y3]; simpl in H0; inversion H0; subst; auto.
    }
    destruct Hsplitpats1 as [patsa [patsb [Hpats1eq Hcnotin]]].
    subst pats1.
    assert (forall p Hp, In p patsa -> match_val_single gamma_valid pd vt ty (fst p) Hp
      (term_rep gamma_valid pd vt pf v t ty Htty) = None).
    {
      (*Use [match_val_single_constr_nomatch] to show that all None*)
      intros [p1 a1] Hp' Hinp'.
      destruct (Hcnotin _ _ Hinp') as [f2 [vs2 [ps2 [Hx Hf12]]]]; subst. simpl fst.
      eapply (match_val_single_constr_nomatch _ _ m_in a_in c_in args_len); eauto.
    }
    (*So patsa is irrelevant, and we can manually simplify [match_rep]*)
    revert Hpatsty Hactty.
    rewrite <- app_assoc. intros.
    rewrite match_rep_app2; [|assumption].
    rewrite match_rep_equiv. 
    (*And the thing we care about is the [match_val_single] here*)
    (*Awful hack*) Opaque match_val_single.
    simpl match_rep'. Transparent match_val_single. unfold ty.
    assert (Heq: sym_sigma_args c (map (v_subst vt) args) = map (v_subst vt) (ty_subst_list (s_params c) args (s_args c))).
    { apply sym_sigma_args_map. rewrite (adt_constr_params gamma_valid m_in a_in c_in). auto. }
    (*Useful to know*)
    assert (Hpcty: pattern_has_type gamma (Pconstr c tys1 (map Pvar new_vars)) ty). {
      rewrite Forall_forall in Hallty.
      specialize (Hallty (Pconstr c tys1 (map Pvar new_vars), Some tm1)).
      forward Hallty. 
      { rewrite in_map_iff. exists (Pconstr c tys1 (map Pvar new_vars), tm1); split; auto.
        rewrite !in_app_iff; simpl; auto.
      }
      apply Hallty.
    }
    assert (Heqty: tys1 = args). {
      inversion Hpcty; subst.
      unfold sigma in H4.
      rewrite (adt_constr_ret gamma_valid m_in a_in c_in) in H4.
      rewrite ty_subst_cons in H4.
      rewrite <- (adt_constr_params gamma_valid m_in a_in c_in) in H4.
      rewrite map_ty_subst_var in H4; auto.
      - unfold ty in H4; inversion H4; auto.
      - apply s_params_Nodup.
    }
    subst tys1.
    assert (Hvarsty: row_typed (ty_subst_list (s_params c) args (s_args c)) (map Pvar new_vars)).
    {
      apply constr_typed_row in Hpcty. auto.
    }
    (*Now we have all the typing info to rewrite the [match_val_single]*)
    rewrite (match_val_single_constr_row _ _ m_in a_in c_in args_len Htty al Hsem _ _ _ _ Heq Hvarsty).
    (*We can solve this explicitly: we know that [matches_row] succeeds here (these are all variables)
      and each variable is mapped to the corresponding element of the hlist*)
    (*Rest of proof (sketch):
      We can directly simplify the [matches_row] into the valuation vs -> al
      We want to show that matches_matrix v (t :: tl) rl = Some (gen_rep (vs -> al) tm1)
        where compile (vs ++ tl) (spec c rl) = Some tm1.
      From the IH, we have that matches_matrix (vs -> al) (vs ++ tl) (spec c rl) =
        Some (gen_rep (vs -> al) tm1) (NOTE: we need to adjust v here!)
      From our spec lemma, we know that matches_matrix v (t :: tl) rl =
        matches_matrix v (al ++ rl) (spec c rl).
        Thus, it remains to show that
        matches_matrix v (al ++ rl) P = matches_matrix (vs -> al) (vs ++ rl) P
        This follows by considering each row - the terms only matter based on what they
          become under (domain (v_subst vt)), and by the definition of the valuation, 
          the resulting domain values are equivalent (as long as rl does not have any variables in vs)
    *)
    (*First, rewrite this [matches_row]*)
    destruct (matches_row_allvars v _ _ Heq al new_vars Hvarsty) as [l [Hl Hvall]].
    rewrite Hl.
    (*Need to reverse here to match to ending result of [compile]**)
    assert (params_len : Datatypes.length (s_params c) = Datatypes.length args). {
      specialize (Hclist_types _ _ _ Hinc); inversion Hclist_types; auto.
    }
    assert (Hlenps: length ps1 = length new_typs). {
      unfold new_typs. rewrite map_length; auto. 
      specialize (Hclist_types _ _ _ Hinc); inversion Hclist_types; auto.
    }
    assert (Hvarstyps: length new_vars = length new_typs). {
      unfold new_vars. rewrite combine_length, gen_strs_length. lia.
    }
    assert (Hnodup: NoDup new_vars). {
      unfold new_vars. apply NoDup_combine_l. apply gen_strs_nodup.
    }
    rewrite gen_rep_change_vv with (v2:=val_with_args pd vt v (rev new_vars) (hlist_rev _ _ al)).
    2: { 
      intros x Hinx'. rewrite val_with_args_rev; auto.
      rewrite Heq. unfold new_vars. rewrite map_snd_combine; auto. rewrite gen_strs_length. lia.
    }
    (*Step 2: We already simplified IHconstrs, now we destruct - need to change v!*)
    specialize (IHconstrs' _ _ _ Hinc (val_with_args pd vt v (rev new_vars) (hlist_rev _ _ al)) tm1).
    forward IHconstrs'. (*prove the compile equivalence*)
    {
      rewrite H1. unfold comp_cases, Pattern.comp_cases. (*some duplication too*)
      unfold cases.
      erewrite (dispatch1_equiv_spec _ _ _ Hsimp Hpop Hp); auto. 
      unfold cslist in Hinc.
      rewrite amap_mem_spec.
      replace (amap_get funsym_eq_dec (fst types_cslist) c) with (Some ps1); auto.
      symmetry.
      rewrite (proj2 (populate_all_fst_snd_full _ _ _ Hsimp Hpop)). exists args; assumption.
    }
    (*Need to simplify again - bad*)
    subst new_typs new_vars.
    set (new_typs := (map (ty_subst (s_params c) args) (s_args c))) in *.
    set (new_vars :=(combine (gen_strs (Datatypes.length ps1) (compile_fvs gen_getvars ((t, ty) :: tl) rl)) new_typs)) in *.
    (*Why we needed the "exists" in the alternate IHconstrs: now we don't need to prove typing again*)
    destruct IHconstrs' as [Htys [Hp' [Hty IHmatch]]].
    erewrite gen_rep_irrel.
    rewrite <- IHmatch.
    (*Step 3: Use spec lemma to rewrite*)
    rewrite (spec_match_eq v t m_in a_in c_in args_len params_len Htty al Hsem _ _ _ _ Hsimp _ Hp').
    (*Step 4: Show that we can change the valuation in this case*)
    clear -Hvarstyps Hnodup Hlenps.
    revert Hp' Htys. generalize dependent (spec_prop_cast c args (map snd tl) params_len).
    unfold ty_subst_list.
    unfold matches_matrix_tms.
    change (seq.map (ty_subst (s_params c) args) (s_args c)) with new_typs.
    (*NOTE: first, prove that none of new_vars are in terms, so we can replace
      second [terms_to_hlist] with just v*)

    intros Heq Hp' Htys.
    (*We can use [terms_to_hlist app] to split and prove directly*)
    assert (Hlen: length (rev (map Tvar new_vars)) = length (rev new_typs)). {
      rewrite !rev_length, map_length; auto.
    }
    rewrite terms_to_hlist_app with (Hty2:=Forall2_inv_tail Htmtys)
      (Hty1:=proj1(Forall2_app_inv Htys Hlen)) by auto.
    (*Now we know that [terms_to_hlist] on (map Tvar new_vars) is just al*)
    assert (Heqrev: rev (sym_sigma_args c (map (v_subst vt) args)) =
      map (v_subst vt) (rev new_typs)).
    {
      rewrite map_app in Heq. apply app_inv_tail in Heq. exact Heq.
    }
    generalize dependent (proj1 (Forall2_app_inv Htys Hlen)).
    replace (rev (map Tvar new_vars)) with (map Tvar (rev new_vars)) by (rewrite map_rev; reflexivity).
    intros Hall.
    rewrite (terms_to_hlist_val_with_args v (rev new_vars) (rev new_typs)) with (Heq:=Heqrev);
    [| apply NoDup_rev; assumption].

    rewrite matches_matrix_change_vv with (v1:=val_with_args _ _ _ _ _) (v2:=v).
    2: {
      (*Prove these valuations are equivalent for all action vars -relies on fresh vars*)
      intros x row Hinrow Hinx.
      rewrite val_with_args_notin; auto.
      rewrite <- In_rev. unfold new_vars. unfold vsymbol in *.
      rewrite in_combine_iff; rewrite gen_strs_length; [|solve[auto]].
      intros [i [Hi Hx]]. specialize (Hx ""%string vty_int).
      assert (Hinget: In (fst x)((gen_strs (length ps1) (compile_fvs gen_getvars ((t, ty) :: tl) rl) ))).
      { subst. simpl. apply nth_In. rewrite gen_strs_length. auto. }
      apply gen_strs_notin in Hinget.
      apply Hinget.
      (*contradiction - in action vars, so must be in [compile_fvs]*)
      unfold compile_fvs. rewrite !in_app_iff. right. right.
      unfold pat_mx_act_vars. simpl_set. Search gen_getvars spec.
      apply (gen_getvars_spec Hinrow Hinx).
    }

    f_equal.
    (*Get all casts to beginning*)
    rewrite hlist_app_cast1.
    rewrite (terms_to_hlist_change_vv (val_with_args pd vt v (rev new_vars)
      (hlist_rev (domain (dom_aux pd))
      (sym_sigma_args c (map (v_subst vt) args)) al)) v).
    2: {
      (*Last subgoal: prove no intersection between vars and terms*)
      intros tm x Htm Hx.
      rewrite val_with_args_notin; auto.
      rewrite <- In_rev.
      unfold new_vars, vsymbol. rewrite in_combine_iff; rewrite gen_strs_length; [|solve[auto]].
      intros [i [Hi Hxeq]].
      specialize (Hxeq ""%string vty_int).
      assert (Hinget: In (fst x)((gen_strs (length ps1) (compile_fvs gen_getvars ((t, ty) :: tl) rl) ))).
      { subst. simpl. apply nth_In. rewrite gen_strs_length. auto. }
      apply gen_strs_notin in Hinget.
      apply Hinget.
      (*contradiction - in action vars, so must be in [compile_fvs]*)
      unfold compile_fvs. rewrite !in_app_iff. left.
      unfold tmlist_vars. rewrite in_concat. simpl.
      exists ((tm_fv tm ++ tm_bnd tm)). rewrite in_map_iff, in_app_iff. split; auto.
      right. rewrite in_map_iff in Htm. destruct Htm as [y [Htm Hiny]]. subst.
      exists y. auto. 
    }
    (*Only need to prove casts equivalent now*)
    rewrite !cast_arg_list_compose.
    apply cast_arg_list_eq.
- (*Second case: constructor is NOT in list - then we fall through to defaults*)
  (*Similar, show pats1 has constructors which are not c*)
  assert (Hpats1c: forall x y, In (x, y) pats1 -> 
    exists c1 tys1 ps1, x = (Pconstr c1 tys1 ps1) /\ c1 <> c).
  {
    intros x y Hinxy.
    assert (Hinxy1: In (x, Some y) (map (fun x => (fst x, Some (snd x))) pats1)) by
      (rewrite in_map_iff; exists (x, y); auto).
    rewrite Hpats1 in Hinxy1. rewrite <- List.in_rev in Hinxy1.
    rewrite in_map_iff in Hinxy1. destruct Hinxy1 as [[[f1 tys1] ps1] [Hxy Hinfs]]; simpl in Hxy.
    inversion Hxy; subst.
    exists f1. exists tys1. eexists. split; [reflexivity| auto]. 
    (*Show not c by notin*)
    intro Heq; subst. apply n. rewrite in_map_iff.
    eexists; split; [| apply Hinfs]; reflexivity.
  }
  set (ty := vty_cons (adt_name a) args) in *.
  assert (forall p Hp, In p pats1 -> match_val_single gamma_valid pd vt ty (fst p) Hp
    (term_rep gamma_valid pd vt pf v t ty Htty) = None).
  {
    (*Use [match_val_single_constr_nomatch] to show that all None*)
    intros [p1 a1] Hp' Hinp'.
    destruct (Hpats1c _ _ Hinp') as [f2 [vs2 [ps2 [Hx Hf12]]]]; subst. simpl fst.
    eapply (match_val_single_constr_nomatch _ _ m_in a_in c_in args_len); eauto.
  }
  (*Similarly, pats1 is irrelevant, so we go to pats2 (wild)*)
  rewrite match_rep_app2; [|assumption].
  (*Now we show that [no_wilds] is false, so that pats2 = (Pwild, comp_wilds)*)
  assert (Hno: no_wilds = false). {
    (*If true, impossible - we know that c is in constructors but not cslist*)
    unfold no_wilds.
    apply forallb_false.
    exists c. split; auto.
    - unfold css. apply (in_get_constructors m_in a_in); auto.
    - unfold types.
      rewrite amap_mem_spec.
      destruct (amap_get funsym_eq_dec (fst types_cslist) c) as [y|] eqn : Hget; auto.
      rewrite (proj2 (populate_all_fst_snd_full _ _ _ Hsimp Hpop)) in Hget.
      destruct Hget as [tys Hincslist]. exfalso.
      apply n. rewrite in_map_iff. exists (c, tys, y); auto.
  }
  rewrite Hno in Hpats2.
  (*Now explicitly get parts of pats2*)
  destruct pats2 as [| [y1 y2] [|]]; try discriminate.
  simpl in Hpats2. injection Hpats2. intros Hcompwilds Hy1; subst y1.
  rewrite match_rep_equiv.
  simpl.
  unfold extend_val_with_list. simpl.
  (*Now use IH and show default*)
  symmetry in Hcompwilds; unfold comp_wilds in Hcompwilds.
  specialize (IHwilds v y2 Hcompwilds). destruct IHwilds as [Hty IHmatch].
  erewrite gen_rep_irrel.
  rewrite <- IHmatch. subst wilds.
  (*And now we use [default_match_eq]*)
  unfold matches_matrix_tms at 2.
  pose proof (default_match_eq). unfold ty. clear IHmatch.
  revert Htywild.
  rewrite (dispatch1_equiv_default _ _ _ _ Hsimp). intros.
  apply (default_match_eq v t m_in a_in c_in args_len) with (Hty:=Htty) (al1:=al); auto.
  + rewrite (adt_constr_params gamma_valid m_in a_in c_in); auto.
  + (*Last goal: show that since not in cslist, constr_at_head_ex is false*)
    destruct (constr_at_head_ex c rl) eqn : Hconstr; auto.
    apply (populate_all_in _ _ _ _ Hsimp Hpop) in Hconstr.
    rewrite amap_mem_spec in Hconstr.
    destruct (amap_get funsym_eq_dec (fst types_cslist) c) as [y|] eqn : Hget; auto.
    apply (proj2 (populate_all_fst_snd_full _ _ _ Hsimp Hpop)) in Hget.
    destruct Hget as [tys Hinc].
    (*Contradiction from not in cslist*)
    exfalso. apply n.
    rewrite in_map_iff. exists (c, tys, y). auto.
Qed.


(*Finally, Our main correctness theorem: if [compile is_constr gen_let gen_case tms tys P] =
  Some t, then [matches_matrix_tms tms tys P] = Some (term_rep v t).
  We CANNOT prove the converse; it does not hold, as semantic exhaustiveness is undecidable*)
Theorem compile_correct (v: val_vars pd vt) (tms: list (term * vty)) 
  (P: pat_matrix) 
  (Htys: Forall2 (term_has_type gamma) (map fst tms) (map snd tms))
  (Hp: pat_matrix_typed (map snd tms) P)
  (Hdisj: pat_matrix_var_names_disj (map fst tms) P)
  t :
  compile get_constructors gen_match gen_let gen_getvars tms P = Some t ->
  exists (Hty : gen_typed b t ret_ty),  
    matches_matrix_tms v (map fst tms) (map snd tms) P Htys Hp = Some (gen_rep v ret_ty t Hty).
Proof.
  revert v t. (*It is very important that we generalize v*)
  apply (compile_ind get_constructors gen_match gen_let gen_getvars gen_getvars_let
    (fun tms P o =>
      forall (Hdisj: pat_matrix_var_names_disj (map fst tms) P) Htys Hp,
      forall v t, o = Some t ->
      exists Hty : gen_typed b t ret_ty,
      matches_matrix_tms v (map fst tms) (map snd tms) P Htys
        Hp =
      Some (gen_rep v ret_ty t Hty))); auto; clear.
  - (*extensionality*)
    intros t ty tms rl Hopt Hdisj Htys Hp v. simpl in *.
    (*Proved hyps for Hopt*)
    specialize (Hopt (simplify_disj _ _ _ _ Hdisj) Htys (simplify_typed (Forall2_inv_head Htys) Hp) v).
    rewrite <- compile_simplify in Hopt.
    intros tm Hcomp. apply Hopt in Hcomp.
    destruct Hcomp as [Hty Hmatch].
    exists Hty. rewrite <- Hmatch.
    erewrite simplify_match_eq. reflexivity.
    apply pat_matrix_var_names_vars_disj; assumption.
    apply gen_getvars_let.
  - (*P is nil*) intros. discriminate.
  - (*P not nil, ts is nil*) intros ps a P' Hdisj Htys Hp v.
    simpl in *. unfold matches_matrix_tms. simp terms_to_hlist. simp matches_matrix. simpl.
    intros tm. inv Hsome.
    destruct ps as [| phd ptl].
    + simp matches_row. eexists. unfold extend_val_with_list. simpl. reflexivity.
    + (*Cannot have non-null row in this case*)
      exfalso.
      apply pat_matrix_typed_head in Hp.
      destruct Hp as [Hrow _]; inversion Hrow.
  - (*Ill-typed (populate_all or dispatch don't give Some)*)
    intros t ty tl rl css is_constr Hsimp [Hpop | Hdisj] Hdisj1.
    + unfold populate_all in Hpop.
      destruct (get_heads rl) as [l|] eqn : Hget.
      * (*Case 1: [get_heads] is Some, [fold_left_opt] is None*)
        simpl. intros Htyps Hp v.
        apply fold_left_opt_none in Hpop.
        destruct Hpop as [ps1 [p [ps2 [acc1 [Hl [Hfold Hpop]]]]]].
        subst. apply populate_none_simpl in Hpop.
        2: {
          apply (get_heads_simplified rl (ps1 ++ p :: ps2)); auto.
          rewrite in_app_iff; simpl; auto.
        }
        (*Idea: contradiction, by None we found a constructor in 1st column that is
          not [is_constr]. But by tying, it has to be*)
        destruct Hpop as [c [tys [ps [Hpeq Hnotconstr]]]]; subst.

        assert (Htyp: pattern_has_type gamma (Pconstr c tys ps) ty). {
          eapply in_get_heads_tys. apply Hp. apply Hget.
          rewrite !in_app_iff; simpl; auto.
        }
        (*The contradiction*)
        assert (Hconstr: is_constr c). {
          unfold is_constr. unfold css.
          inversion Htyp; subst.
          unfold sigma.
          destruct H11 as [m [a [m_in [a_in c_in]]]].
          rewrite (adt_constr_ret gamma_valid m_in a_in c_in).
          rewrite ty_subst_cons. 
          apply In_in_bool, (in_get_constructors m_in a_in); auto.
        }
        rewrite Hnotconstr in Hconstr; discriminate.
      * (*Second typing contradiction: if get_heads is None*)
        (*By typing, cannot have an empty pattern list in a row*)
        apply get_heads_none_iff in Hget. intros Htys Hp.
        rewrite (pat_matrix_typed_not_null Hp) in Hget.
        discriminate.
    + (*Final typing contradiction - dispatch1_opt is None, same as previous.*)
      intros Htyps Hp. simpl in *.
      destruct Hdisj as [types_cslist [Hpop Hdisp]].
      apply dispatch1_opt_none in Hdisp.
      rewrite (pat_matrix_typed_not_null Hp) in Hdisp.
      discriminate.
  - (*The interesting case*)
    intros t ty tl rl css is_constr Hsimp types_cslist Hpop types cslist casewild
      Hdisp cases wilds IH Hdisj Htmtys Hp v. simpl in Htmtys.
    set (comp_wilds := fun (_: unit) => compile get_constructors gen_match gen_let gen_getvars tl
      wilds) in *.
    set (comp_cases := fun cs (al : list (term * vty)) =>
      comp_cases (compile get_constructors gen_match gen_let gen_getvars) cases tl cs al).
    simpl.
    set (comp_full := comp_full gen_match gen_getvars comp_wilds comp_cases types cslist css t ty tl rl).
    destruct IH as [IHwilds IHconstrs].
    assert (Hwilds: wilds = default rl). {
      unfold wilds.
      apply dispatch1_opt_some in Hdisp.
      destruct Hdisp as [Hnotnull Hcasewild]; subst.
      rewrite dispatch1_equiv_default; auto.
    }
    (*Might as well prove hypotheses for IH now*)
    prove_hyp IHwilds.
    {
      rewrite Hwilds.
      eapply disj_default; eauto.
    }
    assert (Htywild: pat_matrix_typed (map snd tl) wilds). {
      rewrite Hwilds. eapply default_typed; eauto.
    }
    specialize (IHwilds (Forall2_inv_tail Htmtys) Htywild).
    (*Case 1: types is empty*)
    destruct (amap_is_empty types) eqn : Htypesemp.
    {
      (*We know:
        1. All elements are Pwild in first column
        2. No matter what type ty is, it cannot be a constructor that is in the first column.
        3. Thus, we can use either of our default lemmas*)
      destruct (is_vty_adt gamma ty) as [[[m a] args]|] eqn : Hisadt.
      - (*case 1: ADT. Know constructor not in first column*)
        assert (args_len: length args = length (m_params m)). {
          apply adt_vty_length_eq in Hisadt; auto.
          clear -Htmtys.
          apply Forall2_inv_head in Htmtys.
          apply has_type_valid in Htmtys; auto.
        }
        apply is_vty_adt_some in Hisadt.
        destruct Hisadt as [Hty [a_in m_in]]; subst.
        destruct (find_semantic_constr v t m_in a_in args_len (Forall2_inv_head Htmtys))
        as [f [[c_in al] Hrep]].
        simpl in Hrep.
        assert (Hnotin: constr_at_head_ex f rl = false).
        {
          destruct (constr_at_head_ex f rl) eqn : Hconstr; auto.
          apply (populate_all_in _ _ _ _ Hsimp Hpop) in Hconstr.
          unfold types in Htypesemp.
          assert (Hconstrf: amap_mem funsym_eq_dec f (fst types_cslist) = false).
            apply amap_is_empty_mem; auto.
          rewrite Hconstrf in Hconstr; discriminate.
        }
        (*Now we apply default lemma 1*)
        unfold comp_wilds. simpl in Hdisj.
        assert (constrs_len: length (s_params f) = length args).
        {
          rewrite args_len. f_equal. apply (adt_constr_params gamma_valid m_in a_in c_in).
        }
        rewrite (default_match_eq v _ m_in a_in c_in args_len constrs_len (Forall2_inv_head Htmtys) al Hrep _ 
          _ Htmtys rl Hsimp Hnotin Hp (default_typed Hp)).
        (*And use IH about wilds*)
        revert IHwilds.
        unfold matches_matrix_tms.
        generalize dependent Htywild.
        rewrite Hwilds.
        intros Htywild.
        setoid_rewrite matches_matrix_irrel with (Hty2:=(default_typed Hp)). auto.
      - (*Case 2: not ADT at all. Similar but use second default lemma*)
        rewrite (default_match_eq_nonadt _ _ _ (Forall2_inv_head Htmtys) Hisadt _ _ Htmtys
          rl Hsimp Hp (default_typed Hp)).
        revert IHwilds.
        unfold comp_wilds.
        unfold matches_matrix_tms.
        generalize dependent Htywild.
        rewrite Hwilds.
        intros Htywild.
        setoid_rewrite matches_matrix_irrel with (Hty2:=(default_typed Hp)).
        auto.
    }
    (*Now that we know that [types] is non-empty, we know that there is at least
      one constructor in the first column. By typing, ty is an ADT*)
    assert (Hadt: exists m a args, mut_in_ctx m gamma /\ adt_in_mut a m /\
      ty = vty_cons (adt_name a) args /\ length args = length (m_params m)).
    {
      rewrite (amap_not_empty_mem funsym_eq_dec) in Htypesemp.
      destruct Htypesemp as [c Hintypes].
      (*From [types], know that c is in first column*)
      apply (populate_all_in _ _ _ _ Hsimp Hpop) in Hintypes.
      destruct (constr_at_head_ex_type Hp Hintypes) as [tys [ps Hcty]].
      simpl in Hcty.
      inversion Hcty; subst.
      (*Use fact that constructor patterns must arise from ADT*)
      destruct H11 as [m [a [m_in [a_in c_in]]]].
      exists m. exists a. unfold sigma.
      rewrite (adt_constr_ret gamma_valid m_in a_in c_in).
      rewrite ty_subst_cons. rewrite !map_map.
      eexists. split_all; try assumption. reflexivity.
      rewrite !map_length. reflexivity.
    }
    destruct Hadt as [m [a [args [m_in [a_in [Hty args_len]]]]]].
    apply dispatch1_opt_some in Hdisp.
    destruct Hdisp as [Hnotnull Hdisp].
    
    (*The important and difficult case (we proved above)*)
    assert (Hfull: forall t1, comp_full tt = Some t1 ->
      exists Hty : gen_typed b t1 ret_ty,
      matches_matrix_tms v (t :: map fst tl)
        (ty :: map snd tl) rl Htmtys Hp =
      Some (gen_rep v ret_ty t1 Hty)). 
    {
      intros t1 Ht1.
      eapply comp_full_correct; eauto.
    }
    destruct (is_fun t) as [s1 | s2]; auto.
    destruct s1 as [[[f tys] tms] Ht]; subst t; simpl.
    (*Now, see if t is a constructor application that can be simplified*)
    destruct (is_constr f) eqn : Hconstr; auto.
    (*We know that f is a constructor, so we can get its arg_list*)
    assert (Htty: term_has_type gamma (Tfun f tys tms) (vty_cons (adt_name a) args)). {
      subst. clear -Htmtys. apply (Forall2_inv_head Htmtys).
    }
    destruct (find_semantic_constr v (Tfun f tys tms) m_in a_in args_len Htty) as 
    [c [[c_in al] Hrep]].
    simpl in Hrep.
    assert (f_in: constr_in_adt f a). {
      unfold is_constr, css in Hconstr.
      rewrite Hty in Hconstr.
      apply in_bool_In in Hconstr.
      rewrite (in_get_constructors m_in a_in) in Hconstr. exact Hconstr.
    }
    assert (constrs_len: length (s_params f) = length args).
    {
      rewrite args_len. f_equal. apply (adt_constr_params gamma_valid m_in a_in f_in).
    }
    (*From this info, we will need to link [al] to [tms]. Need a few results*)
    assert (Heqty: tys = args). {
      inversion Htty; subst.
      rewrite (adt_constr_ret gamma_valid m_in a_in f_in) in H2.
      rewrite ty_subst_cons in H2.
      assert (Hparams: s_params f = m_params m) by
        apply (adt_constr_params gamma_valid m_in a_in f_in).
      rewrite <- Hparams in H2.
      rewrite map_ty_subst_var in H2; auto.
      - inversion H2; subst; auto.
      - apply s_params_Nodup.
    }
    subst.
    assert (Htms': Forall2 (term_has_type gamma) tms
      (ty_subst_list (s_params f) args (s_args f))).
    {
      inversion Htty; subst. unfold ty_subst_list.
      rewrite Forall2_combine. split; [rewrite map_length; auto|]. assumption.
    }
    (*Now, we can related c and f, and al with [terms_to_hlist tms] by our
      lemma [tfun_semantic_constr]*)
    destruct (tfun_semantic_constr m_in a_in c_in f_in v _ _ al Htty constrs_len args_len Htms' Hrep)
      as [Heq Hal]. subst c. unfold cast_arg_list at 1 in Hal; simpl in Hal.
    destruct (amap_mem funsym_eq_dec f types) eqn : Hfintypes; auto.
    2: {
      (*If not in types, similar to above, use default result*)
      unfold comp_wilds.
      assert (Hnotin: constr_at_head_ex f rl = false).
      {
        destruct (constr_at_head_ex f rl) eqn : Hconstr1; auto.
        apply (populate_all_in _ _ _ _ Hsimp Hpop) in Hconstr1.
        unfold types in Hfintypes.
        rewrite Hfintypes in Hconstr1.
        discriminate.
      }
      (*Now we apply default lemma 1*)
      rewrite (default_match_eq v _ m_in a_in c_in args_len constrs_len Htty al Hrep _ 
        _ Htmtys rl Hsimp Hnotin Hp (default_typed Hp)).
      (*And use IH about wilds*)
      revert IHwilds.
      unfold matches_matrix_tms.
      generalize dependent Htywild.
      rewrite Hwilds.
      intros Htywild.
      setoid_rewrite matches_matrix_irrel with (Hty2:=(default_typed Hp)).
      auto.
    }
    (*If f is in types, then we use specialization result and IH*)
    unfold comp_cases, Pattern.comp_cases.
    assert (Hgetf: amap_get funsym_eq_dec cases f = Some (spec rl f)) by
      apply (dispatch1_equiv_spec _ _ _ Hsimp Hpop Hp Hfintypes).
    rewrite Hgetf.
    (*Now can use [spec] lemma*)
    pose proof (@spec_typed_adt _ _ _ m_in a_in f_in _ (map snd tl) _ Hp) as Hspecty.
    rewrite (spec_match_eq v (Tfun f args tms) m_in a_in c_in args_len constrs_len Htty al
      Hrep _ _ Htmtys rl Hsimp Hp Hspecty).
    (*And we need the IH*)
    specialize (IHconstrs _ (combine tms
      (map (ty_subst (s_params f) args) (s_args f))) _ Hgetf). 
    assert (Htmslen: Datatypes.length tms = Datatypes.length (s_args f)). {
      inversion Htty; subst; auto.
    }
    rewrite !map_app, !map_rev, !map_fst_combine in IHconstrs by (rewrite map_length; auto).
    rewrite !map_snd_combine in IHconstrs by (rewrite map_length; auto).
    (*Prove IH premises*)
    assert (Htysrev: Forall2 (term_has_type gamma)
      (rev tms ++ map fst tl)
      (rev (map (ty_subst (s_params f) args) (s_args f)) ++
    map snd tl)).
    {
      apply Forall2_app.
      - apply Forall2_rev. auto.
      - inversion Htmtys; auto.
    }
    specialize (IHconstrs (disj_spec Hdisj) Htysrev Hspecty).
    intros tm Hcompile.
    specialize (IHconstrs v tm Hcompile).
    (*Now, we use the IH*)
    destruct IHconstrs as [IHty IHmatch].
    exists IHty.
    unfold matches_matrix_tms in IHmatch.
    revert IHmatch.
    match goal with 
    | |- matches_matrix _ ?l1 ?al1 ?P ?H = Some ?x ->
         matches_matrix _ ?l2 ?al2 ?P2 ?H = Some ?y =>
      replace al1 with al2; auto
    end.
    (*And now, use [al] equality result*)
    subst.
    rewrite terms_to_hlist_app with (Hty1:=(Forall2_rev Htms'))(Hty2:= (Forall2_inv_tail Htmtys)).
    2: unfold ty_subst_list; rewrite !rev_length, !map_length; auto.
    rewrite terms_to_hlist_rev with (Hty:=Htms').
    (*Bring all casts to front*)
    rewrite hlist_rev_cast,  !hlist_app_cast1.
    rewrite !cast_arg_list_compose.
    apply cast_arg_list_eq.
Qed.

End CompileTheorem.

(*Some corollaries*)
Corollary compile_typed (v: val_vars pd vt) (tms: list (term * vty)) 
  (P: pat_matrix) 
  (Htys: Forall2 (term_has_type gamma) (map fst tms) (map snd tms))
  (Hp: pat_matrix_typed (map snd tms) P)
  (Hdisj: pat_matrix_var_names_disj (map fst tms) P)
  t :
  compile get_constructors gen_match gen_let gen_getvars tms P = Some t ->
  @gen_typed gamma b t ret_ty.
Proof.
  intros Hcomp. apply compile_correct in Hcomp; auto.
Qed.

Corollary compile_rep (v: val_vars pd vt) (tms: list (term * vty)) 
  (P: pat_matrix) 
  (Htys: Forall2 (term_has_type gamma) (map fst tms) (map snd tms))
  (Hp: pat_matrix_typed (map snd tms) P)
  (Hdisj: pat_matrix_var_names_disj (map fst tms) P) t
  (Hty: @gen_typed gamma b t ret_ty) :
  compile get_constructors gen_match gen_let gen_getvars tms P = Some t ->
  matches_matrix_tms v (map fst tms) (map snd tms) P Htys Hp = Some (gen_rep v ret_ty t Hty).
Proof.
  intros Hcomp.
  destruct (compile_correct v tms P Htys Hp Hdisj t Hcomp) as [Hty' Hrep].
  rewrite Hrep. f_equal. apply gen_rep_irrel.
Qed.

(*A corollary: If [matches_matrix] is None (i.e., no semantic match), 
  then [compile] returns None, indicating an error.
  We cannot prove the converse; it does not hold*)
Corollary exhaustiveness_correct (v: val_vars pd vt) (tms: list (term * vty)) 
  (P: pat_matrix) 
  (Htys: Forall2 (term_has_type gamma) (map fst tms) (map snd tms))
  (Hp: pat_matrix_typed (map snd tms) P)
  (Hdisj: pat_matrix_var_names_disj (map fst tms) P):
  matches_matrix_tms v (map fst tms) (map snd tms) P Htys Hp = None ->
  compile get_constructors gen_match gen_let gen_getvars tms P = None.
Proof.
  intros Hmatch.
  destruct (compile get_constructors gen_match gen_let gen_getvars tms P) as [t|] eqn : Hcomp; auto.
  destruct (compile_correct v tms P Htys Hp Hdisj t Hcomp) as [Hty' Hrep].
  rewrite Hrep in Hmatch. discriminate.
Qed. 

(*Unlike the OCaml one, we cannot give a context-insensitive exhaustiveness check
  We do not store size of ADT in funsym, so we have no way of knowing if the match
  is exhaustive.
  Basically, we have 2 options:
  1. just change why3 check to be context sensitive
  2. prove at OCaml level that, under well-typedness there, the context-insensitive one
    is equivalent to the context-sensivite one (using fact about constrs).
    Then relate context sensitive to this one (makes more sense)*)

Section SimplePat.

(*Definition of a simple pattern*)
(*A simple pattern consists of only c(vs) or _ *)
(*A simple pattern match consists only of simple patterns, and no repeated constructors/redundant
  matches*)
(*We prove that compilation results in a simple pattern match, though the result is a bit complicated
  because the action terms might not have simple matches.
  As a corollary, every pattern match is semantically equivalent to a simple one*)

Definition simple_pat (p: pattern) : bool :=
  match p with
  | Pconstr c tys ps => forallb (fun p => match p with | Pvar _ => true | _ => false end) ps
  | Pwild => true
  | _ => false
  end.

Definition simple_pat_match (ps: list pattern) : bool :=
  forallb simple_pat ps &&
  nodupb funsym_eq_dec (Pattern.filter_map 
    (fun p => match p with | Pconstr c _ _ => Some c | _ => None end) ps).

(*TODO: move*)

Fixpoint term_simple_pats (t: term) : bool :=
  match t with
  | Tfun c tys tms => forallb term_simple_pats tms
  | Tlet t1 x t2 => term_simple_pats t1 && term_simple_pats t2
  | Tif f t1 t2 => fmla_simple_pats f && term_simple_pats t1 && term_simple_pats t2
  | Teps f v => fmla_simple_pats f
  | Tmatch t ty pats => term_simple_pats t && forallb (fun x => term_simple_pats (snd x)) pats &&
    simple_pat_match (map fst pats)
  | _ => true
  end
with fmla_simple_pats (f: formula) : bool :=
  match f with
  | Fpred p tys tms => forallb term_simple_pats tms
  | Flet t x f => term_simple_pats t && fmla_simple_pats f
  | Fif f1 f2 f3 => fmla_simple_pats f1 && fmla_simple_pats f2 && fmla_simple_pats f3
  | Feq ty t1 t2 => term_simple_pats t1 && term_simple_pats t2
  | Fbinop b f1 f2 => fmla_simple_pats f1 && fmla_simple_pats f2
  | Fmatch t ty pats => term_simple_pats t && forallb (fun x => fmla_simple_pats (snd x)) pats &&
    simple_pat_match (map fst pats)
  | Fnot f => fmla_simple_pats f
  | _ => true
  end.

Definition gen_simple_pats (t: gen_term b) : bool :=
  match b return gen_term b -> bool with
  | true => term_simple_pats
  | false => fmla_simple_pats
  end t.

Lemma gen_simple_pats_let v t1 t2:
  term_simple_pats t1 ->
  gen_simple_pats t2 ->
  gen_simple_pats (gen_let v t1 t2).
Proof.
  unfold gen_simple_pats, gen_let. destruct b; simpl; intros Hsimp1 Hsimp2;
  rewrite Hsimp1; auto.
Qed.

Lemma gen_simple_pats_simplify_single t x:
  term_simple_pats t ->
  gen_simple_pats (snd x) ->
  forallb gen_simple_pats (map snd (simplify_single gen_let t x)).
Proof.
  intros Hsimp1 Hsimp2. unfold simplify_single. destruct x as [ps t1]; simpl in *.
  destruct ps as [| phd ptl]; simpl; [rewrite Hsimp2|]; auto.
  rewrite !map_map. simpl. rewrite forallb_map. generalize dependent t1.
  induction phd; simpl; intros t1 Hsimp2; try solve[rewrite Hsimp2; auto].
  - rewrite gen_simple_pats_let; auto.
  - rewrite forallb_app, IHphd1, IHphd2; auto.
  - apply IHphd. apply gen_simple_pats_let; auto.
Qed.


Lemma gen_simple_pats_simplify t rl:
  term_simple_pats t ->
  forallb gen_simple_pats (map snd rl) ->
  forallb gen_simple_pats (map snd (simplify gen_let t rl)).
Proof.
  intros Hsimp1 Hsimp2. unfold simplify.
  rewrite concat_map.
  rewrite forallb_concat. rewrite !map_map.
  rewrite !forallb_map.
  apply forallb_forall. intros x Hinx.
  apply gen_simple_pats_simplify_single; auto.
  unfold is_true in Hsimp2.
  rewrite forallb_forall in Hsimp2; apply Hsimp2; auto.
  rewrite in_map_iff. exists x; auto.
Qed.

Lemma gen_simple_pats_default rl:
  forallb gen_simple_pats (map snd rl) ->
  forallb gen_simple_pats (map snd (default rl)).
Proof.
  induction rl; simpl; auto.
  intros Hsimp. apply andb_prop in Hsimp.
  destruct Hsimp as [Ha Hrl].
  destruct a as [ps a]; simpl in *.
  destruct ps as [| phd ptl]; simpl; auto.
  destruct phd; auto. simpl.
  rewrite Ha; auto.
Qed.

(*Don't use spec directly because don't assume typing - very tedious*)
Lemma gen_simple_pats_spec rl t types cs ys
  (Hsimpl: simplified rl)
  (Hsimp1: forallb gen_simple_pats (map snd rl))
  (Hget: amap_get funsym_eq_dec (fst (dispatch1 gen_let t types rl)) cs = Some ys):
  forallb gen_simple_pats (map snd ys).
Proof.
  rewrite dispatch_equiv in Hget.
  unfold dispatch2 in Hget.
  rewrite simplified_simplify in Hget; auto.
  clear t. generalize dependent ys.
  induction rl as [| rhd rtl IH]; simpl in *; intros ys Hget.
  - rewrite amap_empty_get in Hget. discriminate.
  - apply andb_prop in Hsimp1. destruct Hsimp1 as [Hhd Htl]. 
    unfold dispatch2_aux in Hget. destruct rhd as [ps a]; simpl in *.
    destruct (dispatch2_gen types rtl)  as [cases wilds] eqn : Hdis1; simpl in *.
    apply andb_prop in Hsimpl. destruct Hsimpl as [Hsimphd Hsimptl].
    destruct ps as [| phd ptl]; auto.
    destruct phd; try discriminate; simpl in *.
    + unfold add_case, amap_change in Hget. 
      destruct (funsym_eq_dec f cs); subst.
      * destruct (amap_get funsym_eq_dec cases cs) as [y2|] eqn : Hget1.
        -- rewrite amap_replace_get_same1 with (y1:=y2) in Hget; auto.
          revert Hget. inv Hsome. simpl. rewrite Hhd; auto. apply IH; auto.
        -- rewrite amap_replace_get_same2 in Hget; auto. revert Hget. inv Hget.
          simpl. rewrite Hhd; auto.
      * rewrite amap_replace_get_diff in Hget; auto.
    + unfold union_cases in Hget.
      destruct (amap_get funsym_eq_dec cases cs) as [y2|] eqn : Hget1.
      * destruct (amap_get funsym_eq_dec types cs) as [y3|] eqn : Hget2.
        -- erewrite amap_union_inboth in Hget; eauto.
          2: { erewrite amap_map_key_get_some; eauto. }
          simpl in Hget. revert Hget. inv Hsome. simpl.
          rewrite Hhd; apply IH; auto.
        -- rewrite amap_union_inr with(y:=y2) in Hget; auto.
          rewrite amap_map_key_get_none; auto.
      * destruct (amap_get funsym_eq_dec types cs) as [y3|] eqn : Hget2.
        -- erewrite amap_union_inl in Hget; auto.
          2: { erewrite amap_map_key_get_some; eauto. }
          revert Hget. inv Hget. simpl. rewrite Hhd; auto.
        -- rewrite amap_union_notin in Hget; auto.
          rewrite amap_map_key_get_none; auto.
Qed.

Lemma option_map_some {A B: Type} (f: A -> B) (o: option A) y:
  option_map f o = Some y ->
  exists z, o = Some z /\ y = f z.
Proof.
  destruct o; simpl; try discriminate.
  inv Hsome. exists a; auto.
Qed.

Lemma gen_simple_pats_match t ty pats:
  term_simple_pats t ->
  forallb gen_simple_pats (map snd pats) ->
  simple_pat_match (map fst pats) ->
  gen_simple_pats (gen_match t ty pats).
Proof.
  intros Hsimp1. unfold gen_simple_pats, gen_match. destruct b; simpl; bool_to_prop;
  rewrite !forallb_map; intros; destruct_all; split_all; auto.
Qed.

Lemma filter_map_app {A B: Type} (f: A -> option B) (l1 l2: list A):
  Pattern.filter_map f (l1 ++ l2) = Pattern.filter_map f l1 ++ Pattern.filter_map f l2.
Proof.
  induction l1 as [| h t IH]; simpl; auto.
  destruct (f h); auto. rewrite IH. reflexivity.
Qed.

Lemma filter_map_rev {A B: Type} (f: A -> option B) (l: list A) :
  Pattern.filter_map f (rev l) = rev (Pattern.filter_map f l).
Proof.
  induction l as [| h t IH]; simpl; auto.
  rewrite filter_map_app, IH; simpl.
  destruct (f h); simpl; auto. rewrite app_nil_r. reflexivity.
Qed.

Lemma filter_map_map {A B C: Type} (f: A -> B) (g: B -> option C) (l: list A) :
  Pattern.filter_map g (map f l) = Pattern.filter_map (fun x => g (f x)) l.
Proof.
  induction l as [| h t IH]; simpl; auto. destruct (g (f h)); rewrite IH; auto.
Qed.

Lemma option_bind_some {A B: Type} (f: A -> option B) (o: option A) y:
  option_bind o f = Some y ->
  exists z, o = Some z /\ f z = Some y.
Proof. destruct o; simpl; [|discriminate]. intros Ha. exists a. auto.
Qed.


Lemma compile_simple_pats (tms: list (term * vty)) (P: pat_matrix) t
  (Hsimp1: forallb term_simple_pats (map fst tms))
  (Hsimp2: forallb gen_simple_pats (map snd P)):
  compile get_constructors gen_match gen_let gen_getvars tms P = Some t ->
  gen_simple_pats t.
Proof.
  revert Hsimp1 Hsimp2 t.
  apply (compile_ind get_constructors gen_match gen_let gen_getvars gen_getvars_let
    (fun tms P o =>
      forall (Hsimp1 : forallb term_simple_pats (map fst tms)) (Hsimp2 : forallb gen_simple_pats (map snd P))
      (t: gen_term b),
      o = Some t -> gen_simple_pats t)); clear tms P; try discriminate.
  - (*invariance under [simplify]*)
    intros t ty tms rl Hsimplify Hsimp1 Hsimp2 t1 Hcomp.
    assert (Hsimpsimp: forallb gen_simple_pats (map snd (simplify gen_let t rl))).
    {
      apply gen_simple_pats_simplify; auto. simpl in Hsimp1. bool_hyps; auto.
    }
    specialize (Hsimplify Hsimp1 Hsimpsimp t1).
    rewrite <- compile_simplify in Hsimplify; auto.
    apply gen_getvars_let.
  - (*Empty list*)
    intros ps a l Hsimp1. simpl. intros Hsimp. apply andb_prop in Hsimp.
    destruct Hsimp as [Hsimpa _]. intros t. inv Ha; auto.
  - (*Interesting case*)
    intros t ty tl rl css is_constr Hsimpl types_cslist Hpop types cslist casewild Hdisp cases wilds
    [IHwilds IHcases] Hsimp1 Hsimp2 t1. simpl.
    simpl in Hsimp1.
    apply andb_prop in Hsimp1. destruct Hsimp1 as [Hsimpt Hsimptl].
    apply dispatch1_opt_some in Hdisp.
    destruct Hdisp as [Hnotnull Hcasewild].
    (*Prove IH hyps*)
    specialize (IHwilds Hsimptl).
    forward IHwilds.
    {
      unfold wilds. subst casewild. rewrite dispatch1_equiv_default; auto.
      apply gen_simple_pats_default; auto.
    }
    (*[comp_full] - more interesting case (TODO: separate lemma also)*)
    assert (Hcompfull: forall t, 
      term_simple_pats t ->
      comp_full gen_match gen_getvars
      (fun _ : unit =>
    compile get_constructors gen_match gen_let
      gen_getvars tl wilds)
      (fun (cs0 : funsym) (al0 : list (term * vty)) =>
    comp_cases
      (compile get_constructors gen_match gen_let
      gen_getvars)
      cases tl cs0 al0)
      types cslist css t ty tl rl tt =
    Some t1 ->
    gen_simple_pats t1).
    {
      intros t' Hsimpt'.
      unfold comp_full.
      rewrite <- option_map_bind.
      intros Hopt. apply option_map_some in Hopt.
      destruct Hopt as [ps [Hps Ht1]]; subst t1.
      apply option_bind_some in Hps.
      destruct Hps as [ps1 [Hps1 Hopt]].
      (*This way we can deal with [fold_left_opt] before destructing 'forallb'*)
      apply fold_right_opt_add_map in Hopt.
      (*Much more useful than destructing and simplifying each time*)
      assert (Hps1': ps1 = nil \/ 
        exists t2, compile get_constructors gen_match gen_let gen_getvars tl wilds = Some t2 /\
          ps1 = [(Pwild, t2)]).
      {
        destruct (forallb (fun f => amap_mem funsym_eq_dec f types) css); simpl in Hps1;
        try solve[inversion Hps1; subst; auto].
        apply option_map_some in Hps1. destruct Hps1 as [t1 [Hwilds Hps1]]; subst. right.
        exists t1. auto.
      }
      clear Hps1.
      apply gen_simple_pats_match; auto.
      - (*First, prove all are simple (from IHconstrs)*)
        assert (Hall1: Forall (fun x => forall y, snd x = Some y -> gen_simple_pats y) 
          (map (fun x => (fst x, Some (snd x)))  ps)).
        2: {
          rewrite forallb_map.
          apply forallb_forall. intros x Hinx.
          rewrite Forall_map in Hall1. simpl in Hall1.
          rewrite Forall_forall in Hall1.
          specialize (Hall1 _ Hinx _ eq_refl); apply Hall1.
        }
        (*Now prove the obligation*)
        rewrite <- Hopt. apply Forall_app; split.
        + apply Forall_rev. apply Forall_map.
          rewrite Forall_forall.
          intros [[c tys] pats1] Hinx y. simpl. 
          unfold rev_map. rewrite !map_rev, !rev_involutive.
          unfold comp_cases.
          (*TODO: should do IH*)
          destruct (amap_get funsym_eq_dec cases c ) as [y1|] eqn : Hget; [|discriminate].
          eapply IHcases; eauto; [| solve[subst; eapply gen_simple_pats_spec; eauto]].
          rewrite map_app, forallb_app, Hsimptl, andb_true_r.
          rewrite map_rev, forallb_rev.
          set (new_vars := (combine (gen_strs (length pats1) (compile_fvs gen_getvars ((t, ty) :: tl) rl)))
            (map (ty_subst (s_params c) tys) (s_args c))) in *.
          rewrite map_fst_combine; auto; [| rewrite !map_length; auto].
          (*Easy: all added are vars*)
          rewrite forallb_map. simpl. apply forallb_t.
        + (*Now case on [ps1] for end*)
          destruct Hps1' as [Hps1 | [t2 [Hwilds Hps1]]]; subst; simpl; auto.
          constructor; auto. simpl. rewrite <- Hwilds. apply IHwilds.
      - (*Simple follows from nodups of cslist*)
        replace (map fst ps) with (map fst (map
          (fun x => (fst x, Some (snd x))) ps)) by
          (rewrite !map_map; simpl; reflexivity).
        rewrite <- Hopt. rewrite map_app. simpl.
        rewrite !map_rev, !map_map.
        unfold simple_pat_match.
        apply andb_true_iff. split.
        + rewrite forallb_app. apply andb_true_iff; split.
          * (*Prove all pats are simple - they are vars*)
            rewrite forallb_rev, forallb_map.
            apply forallb_forall.
            intros [[c tys1] pats1] Hinc. simpl.
            unfold rev_map. rewrite map_rev, rev_involutive.
            rewrite forallb_map. apply forallb_t.
          * simpl. (*easy - just a wild*)
            destruct Hps1' as [Hps1 | [t2 [Hwilds Hps1]]]; subst; simpl; auto.
        + unfold cslist. apply (reflect_iff _ _ (nodup_NoDup _ _)).
          rewrite filter_map_app, !filter_map_rev, !filter_map_map. simpl.
          (*second list is nil*)
          assert (Hsnd: (Pattern.filter_map
            (fun x : pattern * gen_term b => match fst x with
          | Pconstr c _ _ => Some c
          | _ => None
          end) ps1) = nil); [| rewrite Hsnd, app_nil_r].
          {
            destruct Hps1' as [Hps1 | [t2 [Hwilds Hps1]]]; subst; simpl; auto.
          }
          apply NoDup_rev.
          apply populate_all_fst_snd_full in Hpop; [|assumption].
          destruct Hpop as [Hnodup Hpop].
          revert Hnodup.
          match goal with |- NoDup ?l1 -> NoDup ?l2 => 
            replace l1 with l2; [solve[auto]|]
          end.
          clear.
          induction (snd (types_cslist)) as [| x xs IH]; simpl; auto.
          destruct x as [[cs tys1] pats1]; simpl in *. rewrite IH; auto.
    }
    destruct (amap_is_empty types) eqn : Htyemp; [solve[apply IHwilds]|].
    destruct (is_fun t); [|apply Hcompfull; auto].
    destruct s as [[[cs params] al] Ht]. simpl in *.
    destruct (is_constr cs) eqn: Hconstr; [| apply Hcompfull; auto].
    destruct (amap_mem funsym_eq_dec cs types) eqn : Hmem.
    + unfold comp_cases.
      rewrite amap_mem_spec in Hmem.
      destruct (amap_get funsym_eq_dec cases cs) as [ys|] eqn : Hget; [|discriminate].
      eapply IHcases; eauto.
      * rewrite map_app, forallb_app. rewrite map_rev, forallb_rev.
        rewrite Hsimptl, andb_true_r.
        subst t. clear -Hsimpt. simpl in Hsimpt.
        generalize dependent (map (ty_subst (s_params cs) params) (s_args cs)).
        induction al; simpl; auto. intros l.
        destruct l; auto. simpl. simpl in Hsimpt.
        apply andb_true_iff in Hsimpt. destruct Hsimpt as [Hsimpa Hsimpal].
        rewrite Hsimpa. apply IHal; auto.
      * subst;eapply gen_simple_pats_spec; eauto.
    + apply IHwilds.
Qed.
   

(*We will prove a more limited result: suppose that the term list and the actions
  consist of all simple pattern matches. Then so does the result. We will use this
  to show that we can completely transform a pattern*)



End SimplePat.
End PatProofs.