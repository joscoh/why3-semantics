(*Simple map based on association lists*)
Require Import Common.
Definition get_assoc_list {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (l: list (A * B)) (x: A) : option B :=
  fold_right (fun y acc => if eq_dec x (fst y) then Some (snd y) else acc) None l.

Lemma get_assoc_list_some {A B: Type} 
(eq_dec: forall (x y: A), {x = y} + { x <> y}) 
(l: list (A * B)) (x: A) (res: B):
  get_assoc_list eq_dec l x = Some res ->
  In (x, res) l.
Proof.
  induction l; simpl. intro C; inversion C.
  destruct (eq_dec x (fst a)); subst. intro C; inversion C; subst.
  left. destruct a; auto.
  intros. right. apply IHl. assumption.
Qed.

Lemma get_assoc_list_none {A B: Type} 
(eq_dec: forall (x y: A), {x = y} + { x <> y}) 
(l: list (A * B)) (x: A) :
  get_assoc_list eq_dec l x = None <->
  ~ In x (map fst l).
Proof.
  induction l; simpl; split; intros; auto.
  - intro C. destruct (eq_dec x (fst a)); subst.
    inversion H. destruct C. subst. contradiction.
    apply IHl; auto.
  - destruct (eq_dec x (fst a)); subst. exfalso. apply H. left; auto.
    apply IHl. intro C. apply H. right; assumption.
Qed.

Lemma get_assoc_list_nodup {A B: Type} 
  (eq_dec: forall (x y: A), {x=y} +{x<> y})
  (l: list (A * B)) (x: A) (y: B)
  (Hnodup: NoDup (map fst l))
  (Hin: In (x, y) l):
  get_assoc_list eq_dec l x = Some y.
Proof.
  unfold get_assoc_list. induction l; simpl; auto.
  inversion Hin.
  inversion Hnodup; subst.
  destruct Hin as [Heq | Hin]; subst; auto; simpl in *.
  destruct (eq_dec x x); try contradiction; auto.
  destruct a as [h1 h2]; subst; simpl in *.
  destruct (eq_dec x h1); subst; auto.
  exfalso. apply H1. rewrite in_map_iff. exists (h1, y); auto.
Qed.

(*Replace if element there, do nothing if not*)
Definition replace_assoc_list_aux {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B) : list (A * B) := 
  fold_right (fun h acc => (if eq_dec x (fst h) then (x, f x (snd h)) else h) :: acc) nil l.
  

Lemma replace_assoc_list_aux_elt {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B) :
  forall z1 z2, In (z1, z2) (replace_assoc_list_aux eq_dec l x f) <->
     (In (z1, z2) l /\ z1 <> x) \/ (z1 = x /\ exists y1, In (x, y1) l /\ z2 = f x y1).
Proof.
  intros z1 z2. induction l as [| [x1 y1] tl IH]; simpl.
  - split; intros; destruct_all; contradiction.
  - split; intros Hin.
    + destruct Hin as [Heq|Hin].
      * destruct (eq_dec x x1); simpl in Heq; inversion Heq; subst.
        -- right. split; auto. exists y1. auto.
        -- left. auto.
      * apply IH in Hin.
        destruct Hin as [[Hin Hneq]|[Heq [y2 [Hiny2 Heqy2]]]].
        -- left. auto.
        -- subst. right. split; auto. exists y2. auto.
    + destruct Hin as [[[Heq | Hin] Hneq] | [Heq [y2 [[Heq1 | Hin] Heqy2]]]].
      * inversion Heq; subst. destruct (eq_dec x z1); subst; auto; contradiction.
      * right. apply IH; auto.
      * inversion Heq1; subst. destruct (eq_dec x x); auto; contradiction.
      * subst. right. apply IH. right. split; auto.
        exists y2. auto.
Qed.

Lemma replace_assoc_list_map_fst {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B):
  map fst (replace_assoc_list_aux eq_dec l x f) = map fst l.
Proof.
  induction l as [| [x1 y1] tl IH]; simpl; auto.
  destruct (eq_dec x x1); simpl; subst; rewrite IH; reflexivity.
Qed.


Definition replace_assoc_list {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B) (y: B) : list (A * B) :=
  match (get_assoc_list eq_dec l x) with
  | Some _ => replace_assoc_list_aux eq_dec l x f
  | None => (x, y) :: l
  end.

Lemma replace_assoc_list_keys {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B) (y: B):
  forall z1 z2, In (z1, z2) (replace_assoc_list eq_dec l x f y) <->
    ((In (z1, z2) l /\ z1 <> x) \/ (z1 = x /\ exists y1, In (x, y1) l /\ z2 = f x y1)) \/
    (z1 = x /\ z2 = y /\ ~ In x (map fst l)).
Proof.
  intros z1 z2.
  unfold replace_assoc_list.
  destruct (get_assoc_list eq_dec l x) eqn : Hget.
  - rewrite replace_assoc_list_aux_elt.
    split; intros Hin.
    + left. auto.
    + destruct Hin as [? | [Hx [Hy Hinx]]]; auto; subst.
      assert (Hget': get_assoc_list eq_dec l x = None) by (apply get_assoc_list_none; auto).
      rewrite Hget' in Hget. discriminate.
  - simpl. apply get_assoc_list_none in Hget.
    split; intros Hin.
    + destruct Hin as [ Heq | Hin]; [inversion Heq |]; subst; auto.
      left. left. split; auto. intro C; subst.
      apply Hget. rewrite in_map_iff. exists (x, z2); auto.
    + destruct Hin as [[[Hin Hneq] | [Heq [y1 [Hiny1 Heqy1]]]] | [Hx [Hy _]]]; subst; auto.
      exfalso. apply Hget. rewrite in_map_iff. exists (x, y1); auto.
Qed.

Lemma replace_assoc_list_nodup {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (f: A -> B -> B) (y: B) :
  NoDup (map fst l) ->
  NoDup (map fst (replace_assoc_list eq_dec l x f y)).
Proof.
  unfold replace_assoc_list.
  destruct (get_assoc_list eq_dec l x) eqn : Hget.
  - rewrite replace_assoc_list_map_fst. auto.
  - intros Hnodup. simpl. constructor; auto.
    apply get_assoc_list_none in Hget. auto.
Qed.
    
Definition set_assoc_list  {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
 (l: list (A * B)) (x: A) (y: B) : list (A * B) :=
 replace_assoc_list eq_dec l x (fun _ _ => y) y.

Definition map_aux (A B: Type) := list (A * B).
Definition map_get_aux {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: map_aux A B) (x: A) : option B := get_assoc_list eq_dec m x.
Definition map_set_aux {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: map_aux A B) (x: A) (y: B) : map_aux A B := set_assoc_list eq_dec m x y.
Definition map_replace_aux {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: map_aux A B) (x: A) (f: A -> B -> B) y: map_aux A B := replace_assoc_list eq_dec m x f y.
Definition map_bindings_aux {A B: Type} (m: map_aux A B) : list (A * B) := m.
Definition map_singleton_aux {A B: Type} (x: A) (y: B) : map_aux A B := [(x, y)].
Definition map_empty_aux {A B: Type} : map_aux A B := nil.
Definition map_map_aux {A B C: Type} (f: B -> C) (m: map_aux A B) : map_aux A C :=
  map (fun x => (fst x, f (snd x))) m.
(*VERY inefficient - O(n^2) union *)
(*Merge 2 maps*)
Definition map_contains {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) (m: map_aux A B)
  (x: A) : bool :=
  match map_get_aux eq_dec m x with
  | Some _ => true
  | _ => false
  end.
Definition combine_common {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y})
  (f: A -> B -> B -> option B) (m1 m2: map_aux A B) :=
  fold_right (fun x acc => 
    match (map_get_aux eq_dec m2 (fst x)) with
    | None => x :: acc
    | Some y => 
      match f (fst x) (snd x) y with
      | Some z => (fst x, z) :: acc
      | None => acc
      end
    end) nil m1.

Definition map_union_aux {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y})
  (f: A -> B -> B -> option B) (m1 m2: map_aux A B) : map_aux A B :=
  (*Filter m1 into those in m2 and those not in m2*)
  let t := List.partition (fun x => map_contains eq_dec m2 (fst x)) m1 in
  let m1_in := fst t in
  let m1_notin := snd t in
  let t := List.partition (fun x => map_contains eq_dec m1 (fst x)) m2 in
  let m2_in := fst t in
  let m2_notin := snd t in
  (*For those in m1, get elements and compute values*)
  combine_common eq_dec f m1_in m2_in ++ m1_notin ++ m2_notin.
(*   let combined := 
  fold_right (fun x acc => 
    match (map_get_aux eq_dec m2 (fst x)) with
    | None => x :: acc
    | Some y => 
      match f (fst x) (snd x) y with
      | Some z => (fst x, z) :: acc
      | None => acc
      end
    end) nil m1_in

  in combined ++ m1_notin *)

Definition map_wf {A B: Type} (m: map_aux A B) : Prop :=
  NoDup (map fst m).
Definition amap (A B: Type) := {m: map_aux A B | map_wf m}.
Definition amap_get {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: amap A B) (x: A) : option B := map_get_aux eq_dec (proj1_sig m) x.
Definition amap_set_proof {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: amap A B) (x: A) (y: B) : map_wf (map_set_aux eq_dec (proj1_sig m) x y).
Proof.
  unfold map_wf, map_set_aux, set_assoc_list.
  apply replace_assoc_list_nodup.
  destruct m as [m m_wf].
  apply m_wf.
Qed.
Definition amap_replace_proof {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: amap A B) (x: A) (f: A -> B -> B) (y: B) : map_wf (map_replace_aux eq_dec (proj1_sig m) x f y).
Proof.
  unfold map_wf, map_replace_aux. apply replace_assoc_list_nodup.
  destruct m as [m m_wf].
  apply m_wf.
Qed.
Definition map_singleton_proof {A B: Type} (x: A) (y: B) : map_wf (map_singleton_aux x y).
Proof.
  constructor; auto. constructor.
Qed.
Definition map_empty_proof {A B: Type} : map_wf (@map_empty_aux A B).
Proof. constructor. Qed.

Definition map_map_proof {A B C: Type} (f: B -> C) (m: amap A B) : map_wf (map_map_aux f (proj1_sig m)).
Proof. unfold map_map_aux, map_wf. rewrite map_map. simpl. destruct m; simpl. apply m.
Qed.

(*The hard one*)
Lemma combine_common_in {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y})
  (f: A -> B -> B -> option B) (m1 m2: map_aux A B) 
  (Hn2: NoDup (map fst m2)) x y:
  In (x, y) (combine_common eq_dec f m1 m2) <->
  (In (x, y) m1 /\ ~ In x (map fst m2)) \/
  (exists z1 z2, In (x, z1) m1 /\ In (x, z2) m2 /\ f x z1 z2 = Some y).
Proof.
  induction m1 as [| [x1 y1] t1 IH]; simpl.
  - split; intros; destruct_all; contradiction.
  - unfold map_get_aux.
    (*inversion Hn1 as [|? ? Hnotin Hn1']; subst.*)
    (* destruct (eq_dec x x1); subst. *)
    + (*case 1: x = x1*)
      destruct (get_assoc_list eq_dec m2 x1) as [z2|] eqn : Hm2.
      * apply get_assoc_list_some in Hm2.
        assert (Hiff: In (x, y)
          match f x1 y1 z2 with
          | Some z => (x1, z) :: combine_common eq_dec f t1 m2
          | None => combine_common eq_dec f t1 m2
          end <-> ((exists z, x = x1 /\ y = z /\ f x1 y1 z2 = Some z) \/ In (x, y) (combine_common eq_dec f t1 m2))).
        { destruct (f x1 y1 z2); simpl; split; intros Hin; auto.
          - destruct Hin as [Heq | Hin];[inversion Heq|]; subst; auto. left. exists y; auto.
          - destruct Hin as [[z [Hz [Hz1 Hbz]]] | Hin]; subst; auto. inversion Hbz; subst; auto.
          - destruct Hin as [[z [Hz [Hz1 Hbz]]] | Hin]; subst; auto. inversion Hbz; subst; auto.
        }
        rewrite Hiff. clear Hiff. rewrite IH; clear IH; auto.
        (*Now just solve this mess*) split; intros Hin.
        -- destruct Hin as [[z3 [Hx [Hy Hf]]] | Hinc]; subst; auto.
          ++ right. exists y1. exists z2. auto.
          ++ destruct Hinc as [[Hin1 Hnotin2] | [z1 [z3 [Hz1 [Hz3 Hf1]]]]]; auto.
             right. exists z1. exists z3. auto.
        -- destruct Hin as [[[Heq | Hin1] Hnotin2] | Hin1]; auto.
          ++ inversion Heq; subst. exfalso. apply Hnotin2. rewrite in_map_iff; exists (x, z2); auto.
          ++ destruct Hin1 as [z1 [z3 [[Heq | Hz1] [Hz3 Hf]]]]; auto.
            ** inversion Heq; subst. assert (z2 = z3) by apply (nodup_fst_inj Hn2 Hm2 Hz3); subst.
              left. exists y; auto.
            ** right. right. exists z1. exists z3. auto.
      * apply get_assoc_list_none in Hm2.
        simpl. rewrite IH; auto.
        (*again, solve mess.easier this time*)
        split; intros Hin.
        -- destruct Hin as [Heq | [[Hin1 Hnotin2] | [z1 [z2 [Hinz1 [Hinz2 Hf]]]]]]; [inversion Heq| |]; subst; auto.
          right. exists z1. exists z2. auto.
        -- destruct Hin as [[[Heq | Hin1] Hnotin2] |[z1 [z2 [[Heq | Hz1] [Hz2 Hf]]]]]; [inversion Heq | | inversion Heq |]; subst; auto.
          ++ exfalso. apply Hm2. rewrite in_map_iff. exists (x, z2); auto.
          ++ right. right. exists z1. exists z2; auto.
Qed.

(*A corollary*)
Lemma combine_common_in_fst {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y})
  (f: A -> B -> B -> option B) (m1 m2: map_aux A B) 
  (Hn2: NoDup (map fst m2)) x:
  In x (map fst (combine_common eq_dec f m1 m2)) ->
  In x (map fst m1).
Proof.
  rewrite !in_map_iff.
  intros [[x1 y1] [Hx1 Hinx]]; simpl in Hx1; subst.
  apply combine_common_in in Hinx; auto.
  destruct Hinx as [[Hinx _] | [z1 [z2 [Hinx _]]]]; eexists; split; try eassumption; auto.
Qed.

Lemma combine_common_nodup {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y})
  (f: A -> B -> B -> option B) (m1 m2: map_aux A B)
  (Hm1: NoDup (map fst m1))
  (Hm2: NoDup (map fst m2)):
  NoDup (map fst (combine_common eq_dec f m1 m2)).
Proof.
  induction m1 as [| [x1 y1] t IH]; simpl; auto.
  inversion Hm1 as [|? ? Hnotin Hm1']; subst.
  destruct (map_get_aux eq_dec m2 x1); simpl;
  [destruct (f x1 y1 b); auto; simpl |]; constructor; auto;
  intros Hinx1; apply combine_common_in_fst in Hinx1; auto.
Qed.

Lemma nodup_map_filter {A B: Type} (f: A -> B) (p: A -> bool) (l: list A):
  NoDup (map f l) ->
  NoDup (map f (filter p l)).
Proof.
  induction l as [| h t IH]; simpl; auto.
  intros Hn; inversion Hn as [|? ? Hnotin Hn1]; subst.
  destruct (p h); auto. simpl; constructor; auto.
  rewrite in_map_iff. intros [x [Hxh Hinx]].
  apply Hnotin. rewrite in_map_iff. exists x. split; auto.
  rewrite in_filter in Hinx. apply Hinx.
Qed. 

Lemma nodup_map_partition_fst {A B: Type} (f: A -> B) (p: A -> bool) (l: list A):
  NoDup (map f l) ->
  NoDup (map f (fst (partition p l))).
Proof.
  intros Hn. rewrite partition_as_filter. simpl. apply nodup_map_filter; auto.
Qed.

Lemma nodup_map_partition_snd {A B: Type} (f: A -> B) (p: A -> bool) (l: list A):
  NoDup (map f l) ->
  NoDup (map f (snd (partition p l))).
Proof.
  intros Hn. rewrite partition_as_filter. simpl. apply nodup_map_filter; auto.
Qed.

Lemma map_contains_iff {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) (m: map_aux A B)
  (x: A):
  map_contains eq_dec m x <-> In x (map fst m).
Proof.
  unfold map_contains.
  destruct (map_get_aux eq_dec m x) as [y|] eqn : Hm.
  - apply get_assoc_list_some in Hm.
    split; auto. intros _. rewrite in_map_iff. exists (x, y); auto.
  - apply get_assoc_list_none in Hm.
    split; intros; try discriminate. contradiction.
Qed.

Lemma map_contains_negb_iff {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) (m: map_aux A B)
  (x: A):
  negb (map_contains eq_dec m x) <-> ~ (In x (map fst m)).
Proof.
  destruct (map_contains eq_dec m x) eqn : Hcont.
  - apply map_contains_iff in Hcont. split; auto; try discriminate.
  - simpl. split; auto. intros _ Hinx. eapply map_contains_iff in Hinx.
    rewrite Hcont in Hinx. discriminate.
Qed.

(*Useful later*)
Lemma map_union_in {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y})
  (f: A -> B -> B -> option B) (m1 m2: map_aux A B) (Hm1: NoDup (map fst m1))
  (Hm2: NoDup (map fst m2)) x y:
  In (x, y) (map_union_aux eq_dec f m1 m2) <->
  (In (x, y) m1 /\ ~ In x (map fst m2)) \/
  (In (x, y) m2 /\ ~ In x (map fst m1)) \/
  (exists z1 z2, In (x, z1) m1 /\ In (x, z2) m2 /\ f x z1 z2 = Some y).
Proof.
  unfold map_union_aux.
  rewrite !in_app_iff.
  rewrite !partition_as_filter; simpl.
  rewrite combine_common_in; auto.
  2: { apply nodup_map_filter; auto. }
  rewrite !in_filter. simpl.
  rewrite !map_contains_negb_iff, !map_contains_iff. simpl.
  split; intros Hin.
  - destruct Hin as [[[[Hinm1 Hinm2] Hnotf] | [z1 [z2 [Hz1 [Hz2 Hf]]]]] | [[Hnotin2 Hin1] | [Hnotin1 Hin2]]]; auto.
    + exfalso. apply Hnotf. rewrite in_map_iff in Hinm1.
      destruct Hinm1 as [[x1 y1] [Hx Hinm1]]; simpl in Hx; subst.
      rewrite in_map_iff. exists (x, y1). split; auto. rewrite in_filter.
      split; auto. apply map_contains_iff; simpl. rewrite in_map_iff. exists (x, y); auto.
    + rewrite !in_filter, !map_contains_iff in Hz1, Hz2. simpl in Hz1, Hz2.
      destruct Hz1 as [Hinm1 Hinm1']; destruct Hz2 as [Hinm2' Hinm2].
      right. right. exists z1. exists z2; auto.
  - destruct Hin as [[Hin1 Hnotin2] | [[Hin2 Hnotin1] | [z1 [z2 [Hin1 [Hin2 Hf]]]]]]; auto.
    left. right. exists z1. exists z2. rewrite !in_filter, !map_contains_iff; simpl.
    split_all; auto; rewrite in_map_iff; eexists; split; try eassumption; auto.
Qed. 

Lemma map_union_proof {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y})
  (f: A -> B -> B -> option B) (m1 m2: amap A B) : map_wf (map_union_aux eq_dec f
    (proj1_sig m1) (proj1_sig m2)).
Proof.
  unfold map_union_aux, map_wf. destruct m1 as [m1 m1_wf]; destruct m2 as [m2 m2_wf]; simpl.
  rewrite map_app.
  (*Need twice*)
  assert (Hintersect: forall x : A,
    In x
      (map fst
         (combine_common eq_dec f (fst (partition (fun x0 : A * B => map_contains eq_dec m2 (fst x0)) m1))
            (fst (partition (fun x0 : A * B => map_contains eq_dec m1 (fst x0)) m2)))) ->
    ~
    In x
      (map fst
         (snd (partition (fun x0 : A * B => map_contains eq_dec m2 (fst x0)) m1) ++
          snd (partition (fun x0 : A * B => map_contains eq_dec m1 (fst x0)) m2)))).
  {
    intros x Hinx1 Hinx2. revert Hinx1 Hinx2. rewrite map_app, in_app_iff, !partition_as_filter; simpl.
    rewrite !in_map_iff.
    intros [[x1 y1] [Hx Hinx]] [[[x2 y2] [Hy Hiny]]|[[x2 y2] [Hy Hiny]]]; simpl in *; subst;
    apply combine_common_in in Hinx; auto; try (apply nodup_map_filter; auto).
    - destruct Hinx as [[Hinboth Hnotin] | [z1 [z2 [Hz1 [Hz2 Hf]]]]].
      + rewrite in_filter in Hinboth, Hiny. destruct Hinboth as [Htrue _]; destruct Hiny as [Hfalse _].
        simpl in *. rewrite Htrue in Hfalse; discriminate.
      + rewrite in_filter in Hz1, Hiny. simpl in *. destruct Hz1 as [Htrue _]; destruct Hiny as [Hfalse _];
        rewrite Htrue in Hfalse; discriminate.
    - destruct Hinx as [[Hinboth Hnotin] | [z1 [z2 [Hz1 [Hz2 Hf]]]]].
      + rewrite in_filter in Hinboth, Hiny. destruct Hinboth as [_ Hinm1]; destruct Hiny as [Hfalse _].
        simpl in *. rewrite map_contains_negb_iff in Hfalse.
        apply Hfalse. rewrite in_map_iff. exists (x, y1). auto.
      + rewrite in_filter in Hz2, Hiny. simpl in *. destruct Hz2 as [Htrue _]; destruct Hiny as [Hfalse _];
        rewrite Htrue in Hfalse; discriminate.
  }
 assert (Hpart: forall x : A,
  In x (map fst (snd (partition (fun x0 : A * B => map_contains eq_dec m2 (fst x0)) m1))) ->
  ~ In x (map fst (snd (partition (fun x0 : A * B => map_contains eq_dec m1 (fst x0)) m2)))).
  {
    intros x. rewrite !partition_as_filter; simpl. rewrite !in_map_iff; intros [[x1 y1] [Hx1 Hinx1]] [[x2 y2] [Hx2 Hinx2]];
    simpl in *; subst. 
    rewrite in_filter in Hinx1, Hinx2; simpl in *. destruct Hinx1 as [Hnot2 Hin1]. destruct Hinx2 as [Hnot1 Hin2].
    rewrite map_contains_negb_iff in Hnot2. apply Hnot2. rewrite in_map_iff. exists (x, y2); auto.
  }
  apply NoDup_app_iff.
  split_all; auto.
  - apply combine_common_nodup; auto;
    apply nodup_map_partition_fst; auto.
  - rewrite map_app. apply NoDup_app_iff. split_all; auto.
    + apply nodup_map_partition_snd; auto.
    + apply nodup_map_partition_snd; auto.
    + intros x Hinx1 Hinx2. apply (Hpart x Hinx2 Hinx1).
  - intros x Hinx1 Hinx2; apply (Hintersect x Hinx2 Hinx1).
Qed.

Definition amap_set {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: amap A B) (x: A) (y: B) : amap A B := exist _ _ (amap_set_proof eq_dec m x y).
Definition amap_replace {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}) 
  (m: amap A B) (x: A) (f: A -> B -> B) (y: B) : amap A B := exist _ _ (amap_replace_proof eq_dec m x f y).
Definition amap_bindings {A B: Type} (m: amap A B) : list (A * B) := map_bindings_aux (proj1_sig m).
Definition amap_singleton {A B: Type} x y : amap A B := exist _ _ (map_singleton_proof x y).
Definition amap_empty {A B: Type} : amap A B := exist _ _ (@map_empty_proof A B).
Definition amap_map {A B C: Type} (f: B -> C) (m: amap A B) : amap A C := exist _ _ (map_map_proof f m).
Definition amap_union {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y})
  (f: A -> B -> B -> option B) (m1 m2: amap A B) := exist _ _ (map_union_proof eq_dec f m1 m2).

(*And now the proofs*)
Section MapProofs.
Context  {A B: Type} (eq_dec: forall (x y: A), {x = y} + { x <> y}).

Local Lemma amap_get_some_iff (m: amap A B) (x: A) (y: B):
  amap_get eq_dec m x = Some y <-> In (x, y) (proj1_sig m).
Proof.
  unfold amap_get, map_get_aux. split; intros Hin.
  - apply get_assoc_list_some in Hin; auto.
  - apply get_assoc_list_nodup; auto. destruct m; auto.
Qed.

Local Lemma amap_get_none_iff (m: amap A B) (x: A):
  amap_get eq_dec m x = None <-> ~ In x (List.map fst (proj1_sig m)).
Proof.
  apply get_assoc_list_none.
Qed.

Local Lemma amap_get_eq_iff (m1 m2: amap A B) (x: A):
  amap_get eq_dec m1 x = amap_get eq_dec m2 x <-> 
  (forall y, In (x, y) (proj1_sig m1) <-> In (x, y) (proj1_sig m2)).
Proof.
  destruct (amap_get eq_dec m2 x) as [y2 |] eqn : Hget2.
  - rewrite !amap_get_some_iff in Hget2 |- *.
    split.
    + intros Hget1 y.
      split; intros Hin.
      -- assert (y = y2) by (apply (nodup_fst_inj (proj2_sig m1) Hin); auto);
          subst; auto.
      -- assert (y = y2) by (apply (nodup_fst_inj (proj2_sig m2) Hin); auto);
          subst; auto.
    + intros Hiff. apply Hiff; auto.
  - rewrite !amap_get_none_iff in Hget2 |- *.
    split.
    + intros Hget1 y. split; intros Hin; exfalso; [apply Hget1 | apply Hget2];
      rewrite in_map_iff; exists (x, y); auto.
    + intros Hiff Hinfst. apply Hget2.
      rewrite !in_map_iff in Hinfst |- *.
      destruct Hinfst as [[x1 y1] [Hx Hinx]]; subst.
      exists (x1, y1); split; auto. apply Hiff; auto.
Qed.


Lemma amap_set_get_same (m: amap A B) (x: A) (y: B):
  amap_get eq_dec (amap_set eq_dec m x y) x = Some y.
Proof.
  rewrite amap_get_some_iff. simpl.
  unfold map_set_aux.
  apply replace_assoc_list_keys.
  destruct (in_dec eq_dec x (List.map fst (proj1_sig m))) as [Hin | Hnotin].
  + left. right. split; auto. rewrite in_map_iff in Hin.
    destruct Hin as [[x1 y1] [Hxx1 Hin1]]; subst; exists y1; auto.
  + right. auto.
Qed.

Lemma amap_set_get_diff (m: amap A B) (x: A) (y: B) (z: A):
  x <> z ->
  amap_get eq_dec (amap_set eq_dec m x y) z = amap_get eq_dec m z.
Proof.
  intros Hneq.
  apply amap_get_eq_iff.
  intros z2. simpl.
  unfold map_set_aux, set_assoc_list. rewrite replace_assoc_list_keys.
  split; intros; destruct_all; subst; try contradiction; auto.
Qed.

Lemma amap_singleton_get1 (x : A) (y: B) :
  amap_get eq_dec (amap_singleton x y) x = Some y.
Proof.
  apply amap_get_some_iff. simpl. auto.
Qed.

Lemma amap_singleton_get2 (x : A) (y: B) z:
  x <> z ->
  amap_get eq_dec (amap_singleton x y) z = None.
Proof.
  intros Hneq.
  apply amap_get_none_iff. simpl. intros [Heq | []]; auto.
Qed.

Lemma amap_empty_get z: @amap_get A B eq_dec amap_empty z = None.
Proof.
  apply amap_get_none_iff. simpl. auto.
Qed.

(*Replace lemmas*)
Lemma amap_replace_get_same1 (m: amap A B) (x: A) (f: A -> B -> B) (y: B) (y1: B)
  (Hget: amap_get eq_dec m x = Some y1):
  amap_get eq_dec (amap_replace eq_dec m x f y) x = Some (f x y1).
Proof.
  apply amap_get_some_iff. simpl. apply replace_assoc_list_keys.
  apply get_assoc_list_some in Hget.
  left. right. split; auto. exists y1; auto.
Qed.

Lemma amap_replace_get_same2 (m: amap A B) (x: A) (f: A -> B -> B) (y: B)
  (Hget: amap_get eq_dec m x = None):
  amap_get eq_dec (amap_replace eq_dec m x f y) x = Some y.
Proof.
  apply amap_get_some_iff.
  apply amap_get_none_iff in Hget.
  apply replace_assoc_list_keys. right. auto.
Qed.

Lemma amap_replace_get_diff (m: amap A B) (x: A) (f: A -> B -> B) (y: B) (z: A):
  x <> z ->
  amap_get eq_dec (amap_replace eq_dec m x f y) z = amap_get eq_dec m z.
Proof.
  intros Hneq.
  apply amap_get_eq_iff. intros y1; simpl.
  rewrite replace_assoc_list_keys. 
  split; intros; destruct_all; subst; auto; contradiction.
Qed.

Lemma amap_bindings_iff (m: amap A B) (x: A) (y: B) :
  In (x, y) (amap_bindings m) <-> amap_get eq_dec m x = Some y.
Proof.
  rewrite amap_get_some_iff. reflexivity.
Qed.

Lemma amap_union_inl (f: A -> B -> B -> option B) (m1 m2: amap A B) (x: A) (y: B)
  (Hin1: amap_get eq_dec m1 x = Some y)
  (Hnotin2: amap_get eq_dec m2 x = None):
  amap_get eq_dec (amap_union eq_dec f m1 m2) x = Some y.
Proof.
  destruct m1 as [m1 m1_wf]; destruct m2 as [m2 m2_wf]; simpl in *.
  apply amap_get_some_iff in Hin1.
  apply amap_get_none_iff in Hnotin2.
  apply amap_get_some_iff.
  simpl. apply map_union_in; auto.
Qed.

Lemma amap_union_inr (f: A -> B -> B -> option B) (m1 m2: amap A B) (x: A) (y: B)
  (Hnotin1: amap_get eq_dec m1 x = None)
  (Hin2: amap_get eq_dec m2 x = Some y):
  amap_get eq_dec (amap_union eq_dec f m1 m2) x = Some y.
Proof.
  destruct m1 as [m1 m1_wf]; destruct m2 as [m2 m2_wf]; simpl in *.
  apply amap_get_some_iff in Hin2.
  apply amap_get_none_iff in Hnotin1.
  apply amap_get_some_iff.
  simpl. apply map_union_in; auto.
Qed.

Lemma amap_union_inboth (f: A -> B -> B -> option B) (m1 m2: amap A B) (x: A) (y1 y2: B)
  (Hin1: amap_get eq_dec m1 x = Some y1)
  (Hin2: amap_get eq_dec m2 x = Some y2):
  amap_get eq_dec (amap_union eq_dec f m1 m2) x = f x y1 y2.
Proof.
  destruct m1 as [m1 m1_wf]; destruct m2 as [m2 m2_wf]; simpl in *.
  apply amap_get_some_iff in Hin1, Hin2. simpl in *.
  destruct (f x y1 y2) eqn : Hf.
  - apply amap_get_some_iff. simpl. apply map_union_in; auto. right. right. exists y1. exists y2. auto.
  - apply amap_get_none_iff. simpl. rewrite in_map_iff. intros [[t1 t2] [Hx Hinx]]; simpl in *; subst.
    apply map_union_in in Hinx; auto.
    destruct Hinx as [[Hinm1 Hnotin2] | [[Hinm2 Hnotin1] | [z1 [z2 [Hz1 [Hz2 Hf1]]]]]].
    + apply Hnotin2. rewrite in_map_iff. exists (x, y2); auto.
    + apply Hnotin1. rewrite in_map_iff. exists (x, y1); auto.
    + assert (y1 = z1) by apply (nodup_fst_inj m1_wf Hin1 Hz1).
      assert (y2 = z2) by apply (nodup_fst_inj m2_wf Hin2 Hz2). subst. rewrite Hf in Hf1; discriminate.
Qed.

End MapProofs.