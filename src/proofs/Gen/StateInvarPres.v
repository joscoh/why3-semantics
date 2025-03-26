(*Preservation of the state invariant*)
Require Export TermDefs ErrStateHoare StateInvar.
Set Bullet Behavior "Strict Subproofs".

Local Open Scope Z_scope.

Section Pres.

(*In general, if the state is *)

(*Preservation of states (move)*)


(*1. If the counter only increases, everything that was wf is still wf (for idents)*)
Lemma idents_of_term_wf_pres {A: Type} (tm: term_c) (o: errState full_st A):
  errst_spec (fun _ => True) o (fun s1 _ s2 =>(fst s1 <= fst s2)%Z) ->
  errst_spec (idents_of_term_wf tm) o (fun _ _ s2 => idents_of_term_wf tm s2).
Proof.
  intros Hspec.
  eapply errst_spec_weaken with (P1:= fun s => True /\ idents_of_term_wf tm s)
   (Q1:=fun s1 _ s2 => fst s1 <= fst s2 /\ idents_of_term_wf tm s1); auto.
  - intros s1 _ s2 [Hle Hwf].
    (*separate lemma?*)
    unfold idents_of_term_wf in *. intros i Hi. specialize (Hwf _ Hi). lia.
  - apply errst_spec_and; auto.
    apply errst_spec_init.
Qed.

Lemma idents_of_vsym_wf_pres {A: Type} (v: vsymbol) (o: errState full_st A):
  errst_spec (fun _ => True) o (fun s1 _ s2 =>(fst s1 <= fst s2)%Z) ->
  errst_spec (vsym_ident_wf v) o (fun _ _ s2 => vsym_ident_wf v s2).
Proof.
  intros Hspec.
  eapply errst_spec_weaken with (P1:= fun s => True /\ vsym_ident_wf v s)
   (Q1:=fun s1 _ s2 => fst s1 <= fst s2 /\ vsym_ident_wf v s1); auto.
  - intros s1 _ s2 [Hle Hwf].
    (*separate lemma?*)
    unfold vsym_ident_wf in *. lia.
  - apply errst_spec_and; auto.
    apply errst_spec_init.
Qed.

(*2. If the type hash counter only increases and the hash table only grows larger,
  then [term_hash_wf] is preserved
  NOTE: this is NOT true of weak hashtables, which Why3 uses for hashing. Reasoning
  about garbage collection would be much trickier *)

Definition hashset_subset {key} (hash: key -> CoqBigInt.t) (eqb: key -> key -> bool) (h1 h2: CoqHashtbl.hashset key)
 : Prop := forall (k: key) v, CoqHashtbl.find_opt_hashset hash eqb h1 k = Some v ->  
  CoqHashtbl.find_opt_hashset hash eqb h2 k = Some v.

(*TODO: write definition for these*)
Lemma term_hash_wf_pres {A: Type} (tm: term_c) (o: errState full_st A):
  errst_spec (fun _ => True) o (fun s1 _ s2 => hashcons_ctr (full_ty_hash s1) <= hashcons_ctr (full_ty_hash s2) /\
    hashset_subset ty_hash ty_eqb (hashcons_hash (full_ty_hash s1)) (hashcons_hash (full_ty_hash s2))) ->
  errst_spec (term_hash_wf tm) o (fun _ _ s2 => term_hash_wf tm s2).
Proof.
  intros Hspec.
  eapply errst_spec_weaken with (P1:= fun s => True /\ term_hash_wf tm s)
   (Q1:=fun s1 _ s2 => (hashcons_ctr (full_ty_hash s1) <= hashcons_ctr (full_ty_hash s2) /\
    hashset_subset ty_hash ty_eqb (hashcons_hash (full_ty_hash s1)) (hashcons_hash (full_ty_hash s2))) 
    /\ term_hash_wf tm s1); auto.
  - intros s1 _ s2 [[Hle Hhash] Hwf].
    (*separate lemma?*)
    unfold term_hash_wf in *.
    unfold gen_hash_wf in *. destruct Hwf as [Hwf1 Hwf2]. split.
    + unfold all_in_hashtable in *. intros x Hinx. specialize (Hwf1 _ Hinx).
      apply Hhash; auto.
    + unfold all_idents_smaller in *. intros x Hinx. specialize (Hwf2 _ Hinx).
      lia.
  - apply errst_spec_and; auto.
    apply errst_spec_init.
Qed.

Lemma ty_hash_wf_pres {A: Type} (t: option ty_c) (o: errState full_st A):
  errst_spec (fun _ => True) o (fun s1 _ s2 => hashcons_ctr (full_ty_hash s1) <= hashcons_ctr (full_ty_hash s2) /\
    hashset_subset ty_hash ty_eqb (hashcons_hash (full_ty_hash s1)) (hashcons_hash (full_ty_hash s2))) ->
  errst_spec (ty_hash_wf t) o (fun _ _ s2 => ty_hash_wf t s2).
Proof.
  intros Hspec.
  eapply errst_spec_weaken with (P1:= fun s => True /\ ty_hash_wf t s)
   (Q1:=fun s1 _ s2 => (hashcons_ctr (full_ty_hash s1) <= hashcons_ctr (full_ty_hash s2) /\
    hashset_subset ty_hash ty_eqb (hashcons_hash (full_ty_hash s1)) (hashcons_hash (full_ty_hash s2))) 
    /\ ty_hash_wf t s1); auto.
  - intros s1 _ s2 [[Hle Hhash] Hwf].
    (*separate lemma?*)
    unfold ty_hash_wf, gen_hash_wf in *. destruct Hwf as [Hwf1 Hwf2]. split.
    + unfold all_in_hashtable in *. intros x Hinx. specialize (Hwf1 _ Hinx).
      apply Hhash; auto.
    + unfold all_idents_smaller in *. intros x Hinx. specialize (Hwf2 _ Hinx).
      lia.
  - apply errst_spec_and; auto.
    apply errst_spec_init.
Qed.

Lemma vsym_hash_wf_pres {A: Type} (v: vsymbol) (o: errState full_st A):
  errst_spec (fun _ => True) o (fun s1 _ s2 => hashcons_ctr (full_ty_hash s1) <= hashcons_ctr (full_ty_hash s2) /\
    hashset_subset ty_hash ty_eqb (hashcons_hash (full_ty_hash s1)) (hashcons_hash (full_ty_hash s2))) ->
  errst_spec (vsym_hash_wf v) o (fun _ _ s2 => vsym_hash_wf v s2).
Proof.
  intros Hspec.
  eapply errst_spec_weaken with (P1:= fun s => True /\ vsym_hash_wf v s)
   (Q1:=fun s1 _ s2 => (hashcons_ctr (full_ty_hash s1) <= hashcons_ctr (full_ty_hash s2) /\
    hashset_subset ty_hash ty_eqb (hashcons_hash (full_ty_hash s1)) (hashcons_hash (full_ty_hash s2))) 
    /\ vsym_hash_wf v s1); auto.
  - intros s1 _ s2 [[Hle Hhash] Hwf].
    (*separate lemma?*)
    unfold vsym_hash_wf, gen_hash_wf in *. destruct Hwf as [Hwf1 Hwf2]. split.
    + unfold all_in_hashtable in *. intros x Hinx. specialize (Hwf1 _ Hinx).
      apply Hhash; auto.
    + unfold all_idents_smaller in *. intros x Hinx. specialize (Hwf2 _ Hinx).
      lia.
  - apply errst_spec_and; auto.
    apply errst_spec_init.
Qed.

Definition term_wf_pres_cond (s1 s2: full_st) :=
  (fst s1 <= fst s2)%Z /\ 
  (hashcons_ctr (full_ty_hash s1) <= hashcons_ctr (full_ty_hash s2) /\
  hashset_subset ty_hash ty_eqb (hashcons_hash (full_ty_hash s1)) (hashcons_hash (full_ty_hash s2))).

Lemma term_st_wf_pres {A: Type} (tm: term_c) (o: errState full_st A):
  errst_spec (fun _ => True) o (fun s1 _ s2 => term_wf_pres_cond s1 s2) ->
  errst_spec (term_st_wf tm) o (fun _ _ s2 => term_st_wf tm s2).
Proof.
  unfold term_st_wf, term_wf_pres_cond. intros Hspec.
  apply errst_spec_and.
  - apply idents_of_term_wf_pres. revert Hspec. apply errst_spec_weaken; auto.
    intros; destruct_all; auto.
  - apply term_hash_wf_pres. revert Hspec. apply errst_spec_weaken; auto.
    intros; destruct_all; split; auto.
Qed.

Lemma ty_st_wf_pres {A: Type} (t: option ty_c) (o: errState full_st A):
  errst_spec (fun _ => True) o (fun s1 _ s2 => term_wf_pres_cond s1 s2) ->
  errst_spec (ty_st_wf t) o (fun _ _ s2 => ty_st_wf t s2).
Proof.
  unfold ty_st_wf, term_wf_pres_cond. intros Hspec.
  apply ty_hash_wf_pres. revert Hspec. apply errst_spec_weaken_post. intros; destruct_all; auto.
Qed.

Lemma vsym_st_wf_pres {A: Type} (v: vsymbol) (o: errState full_st A):
  errst_spec (fun _ => True) o (fun s1 _ s2 => term_wf_pres_cond s1 s2) ->
  errst_spec (vsym_st_wf v) o (fun _ _ s2 => vsym_st_wf v s2).
Proof.
  unfold vsym_st_wf, term_wf_pres_cond. intros Hspec.
  apply errst_spec_and.
  - apply idents_of_vsym_wf_pres. revert Hspec. apply errst_spec_weaken; auto.
    intros; destruct_all; auto.
  - apply vsym_hash_wf_pres. revert Hspec. apply errst_spec_weaken; auto.
    intros; destruct_all; split; auto.
Qed.

Lemma term_wf_pres_cond_refl s: term_wf_pres_cond s s.
Proof.
  unfold term_wf_pres_cond. split_all; try lia.
  unfold hashset_subset; auto.
Qed.

Lemma term_wf_pres_cond_trans s1 s2 s3: term_wf_pres_cond s1 s2 -> term_wf_pres_cond s2 s3 ->
  term_wf_pres_cond s1 s3.
Proof.
  unfold term_wf_pres_cond. intros; destruct_all; split_all; try lia.
  unfold hashset_subset in *. auto.
Qed.


End Pres.