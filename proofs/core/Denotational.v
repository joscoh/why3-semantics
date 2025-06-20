(*Here we give a denotational semantics for Why3, assuming some classical axioms*)
Require Export Substitution.
Require Import Typechecker. (*For unique types*)
Require Export Interp.
Require Import Coq.Sorting.Permutation.
Set Bullet Behavior "Strict Subproofs".

From Equations Require Import Equations.

(*The axioms we need: excluded middle and definite description*)
Require Import Coq.Logic.ClassicalEpsilon.

(*This gives us the following (we give a shorter name)*)
Definition all_dec : forall (P : Prop), {P} + {~P} := excluded_middle_informative.

Ltac simpl_all_dec_tac :=
  repeat match goal with |- context[ all_dec ?P ] => destruct (all_dec P); auto end.

Lemma all_dec_eq: forall (P Q: Prop),
  (P <-> Q) ->
  (@eq bool (proj_sumbool _ _ (all_dec P)) (proj_sumbool _ _ (all_dec Q))).
Proof.
  intros. simpl_all_dec_tac; exfalso.
  - apply n. apply H. apply p.
  - apply n. apply H. apply q.
Qed.

Lemma simpl_all_dec (P: Prop):
   (all_dec P) <-> P.
Proof.
  split; intros;
  destruct (all_dec P); auto.
  inversion H.
Qed.

 (*A computable version - why is standard version not computable?*)
 Definition proj1' {A B: Prop} (H: A /\ B) : A :=
  match H with
  | conj x x0 => x
  end.

Definition proj2' {A B: Prop} (H: A /\ B) : B :=
  match H with
  | conj x x0 => x0
  end.

(*Useful for [match_val_single]*)
Ltac case_find_constr :=
  repeat match goal with
  | |- context [match funsym_eq_dec (projT1 ?x) ?f with 
    | left Heq => _ | right Hneq => _ end] =>
      generalize dependent x
  end. 

(*First, we give the definitions, and then we prove properties
  of these definitions.
  We need to be very careful about which variables are generic
  and which are fixed in Sections.
*)

Section DenotDef.

Context {gamma: context} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) .

(*Representation of terms, formulas, patterns*)

Notation domain := (domain (dom_aux pd)).
Notation val x :=  (v_subst x).
(*Notation val_typevar := (@val_typevar sigma).*)
Notation substi := (substi pd).

Definition cast_dom_vty {v: val_typevar} 
{v1 v2: vty} (Heq: v1 = v2) (x: domain (val v v1)) : domain (val v v2) :=
  dom_cast _ (f_equal (val v) Heq) x.

(*First, lemmas for function case - quite nontrivial *)

(*A crucial result for the function arguments:
  Suppose we have a function f<alpha>(tau) : t, where alpha and tau are vectors
  In a well-typed function application f<mu>(ts), ts_i has type sigma(tau_i), where
  sigma maps alpha_i -> mu_i. Thus, [[ts_i]]_v has type [[v(sigma(tau_i))]].

  When dealing with valuations, we apply [[f<v(mu)>]] to arguments [[ts_i]]_v,
  each of which has must have type [[sigma'(tau_i)]], 
  where sigma maps alpha_i -> v(mu_i)

  Thus, we need to show that v(sigma(tau)) = sigma'(tau_i), which we do in the
  following lemma.
*)
Lemma funsym_subst_eq: forall (params: list typevar) (args: list vty) (v: typevar -> sort) (ty: vty),
  NoDup params ->
  length params = length args ->
  v_subst v (ty_subst params args ty) =
  ty_subst_s params (map (v_subst v) args) ty.
Proof.
  intros. unfold ty_subst_s. unfold ty_subst.
  apply sort_inj. unfold v_subst; simpl.
  induction ty; simpl; auto.
  - destruct (in_dec typevar_eq_dec v0 params).
    + destruct (In_nth _ _ EmptyString i) as [i1 [Hi1 Hv0]]; subst.
      rewrite -> ty_subst_fun_nth with (s:=s_int); auto.
      simpl.
      unfold sorts_to_tys. rewrite map_map. simpl. 
      rewrite -> ty_subst_fun_nth with(s:=s_int); auto; 
        [| rewrite length_map; auto].
      rewrite -> map_nth_inbound with(d2:=vty_int); auto.
      rewrite <- H0; auto.
    + rewrite -> !ty_subst_fun_notin by assumption. auto.
  - f_equal. apply list_eq_ext'; rewrite !length_map; auto.
    intros n d Hn. rewrite -> !map_nth_inbound with (d2:=vty_int); auto.
    2: rewrite length_map; auto. rewrite Forall_forall in H1. apply H1.
    apply nth_In. auto.
Qed.

Lemma ty_fun_ind_ret {f vs ts ty} (H: term_has_type gamma (Tfun f vs ts) ty):
  ty = ty_subst (s_params f) vs (f_ret f).
Proof.
  inversion H; auto.
Qed.

(*We use the above to get the arg list*)
(*For some reason, Coq can tell that code is structurally
  decreasing when it uses this, but not when we write it with
  a Fixpoint (even though we use "exact" everywhere and nearly
  get the same proof term)*)
Definition get_arg_list (v: val_typevar)
  (vs: list vty) (ts: list term) 
  (reps: forall (t: term) (ty: vty),
    term_has_type gamma t ty ->
    domain (v_subst v ty))
  {args: list vty}
  {params: list typevar}
  (Hp: NoDup params)
  (Hlents: length ts = length args)
  (Hlenvs: length vs = length params)
  (Hall: Forall (fun x => term_has_type gamma (fst x) (snd x))
    (combine ts (map (ty_subst params vs) args))):
    arg_list (domain )
    (ty_subst_list_s params
      (map (v_subst v) vs) args).
Proof.
  generalize dependent args. induction ts; simpl; intros.
  - destruct args.
    + exact (@HL_nil _ _).
    + exact (False_rect _ (Nat.neq_0_succ (length args) Hlents)).
  - destruct args as [| a1 atl].
    + exact ( False_rect _ (Nat.neq_succ_0 (length ts) Hlents)).
    + exact ((HL_cons _ _ _ (dom_cast (dom_aux pd)
    (funsym_subst_eq params vs v a1
    Hp (Logic.eq_sym Hlenvs))
      (reps _ _ (Forall_inv Hall)))
       (IHts atl (*atl*) 
        (Nat.succ_inj (length ts) (length atl) Hlents)
        (Forall_inv_tail Hall)))).
Defined.

Lemma get_arg_list_hnth (v: val_typevar)
(s: fpsym) (vs: list vty) (ts: list term) 
(reps: forall (t: term) (ty: vty),
  term_has_type gamma t ty ->
  domain (v_subst v ty))
(Hreps: forall (t: term) (ty: vty)
  (Hty1 Hty2: term_has_type gamma t ty),
  reps t ty Hty1 = reps t ty Hty2)
{args: list vty}
{params: list typevar}
(Hp: NoDup params)
(Hlents: length ts = length args)
(Hlenvs: length vs = length params)
(Hall: Forall (fun x => term_has_type gamma (fst x) (snd x))
  (combine ts (map (ty_subst params vs) args)))
(i: nat)
(Hi: i < length args):
forall Heq Hty,
hnth i
  (get_arg_list v vs ts reps Hp Hlents Hlenvs Hall) s_int (dom_int pd) =
  dom_cast (dom_aux pd) Heq
  (reps (nth i ts tm_d) (ty_subst params vs (nth i args vty_int))
  Hty).
Proof.
  revert i Hi.
  generalize dependent args. induction ts; simpl; intros.
  - destruct args. simpl in Hi. lia.
    inversion Hlents.
  - destruct args. simpl in Hi. lia.
    inversion Hlents.
    simpl. destruct i; simpl.
    + rewrite Hreps with(Hty2:=Hty). simpl.
      apply dom_cast_eq.
    + apply IHts. lia.
Qed. 

(*Version of [get_arg_list_hnth] with typing lemmas, 
specialized to fun or predsym args*)
Lemma arg_list_hnth_eq (s: fpsym) {i: nat} {args: list vty} {params}
  (Hparams: params = map vty_var (s_params s))
  (Hi: i < length args) vt:
  v_subst vt (ty_subst (s_params s) params (nth i args vty_int)) =
  nth i (ty_subst_list_s (s_params s) (map (v_subst vt) params)
    args) s_int.
Proof.
  subst.
  unfold ty_subst_list_s.
  rewrite map_nth_inbound with(d2:=vty_int);
  auto.
  apply funsym_subst_eq.
  apply s_params_Nodup. rewrite length_map; auto.
Qed.

Lemma arg_list_hnth_ty{s: fpsym} {ts: list term} 
{vs: list vty} {args: list vty}
(Hlents : length ts = length args)
(Hall : Forall
  (fun x : term * vty => term_has_type gamma (fst x) (snd x))
  (combine ts (map (ty_subst (s_params s) vs) args)))
{i: nat} (Hi: i < length args): 
term_has_type gamma (nth i ts tm_d) (ty_subst (s_params s) vs (nth i args vty_int)).
Proof.
  rewrite Forall_forall in Hall.
  apply (Hall (nth i ts tm_d, ty_subst (s_params s) vs (nth i args vty_int))).
  rewrite in_combine_iff; [| rewrite length_map; auto].
  exists i. split; try lia. intros.
  f_equal; [apply nth_indep |]; try lia.
  rewrite map_nth_inbound with (d2:=vty_int); auto.
Qed.

(*When our params are [map vty_var (s_params p)]*)
Lemma get_arg_list_hnth_unif 
(v: val_typevar)
(s: fpsym) (ts: list term) 
(reps: forall (t: term) (ty: vty),
  term_has_type gamma t ty ->
  domain  (v_subst v ty))
(Hreps: forall (t: term) (ty: vty)
  (Hty1 Hty2: term_has_type gamma t ty),
  reps t ty Hty1 = reps t ty Hty2)
{args: list vty}
{params}
(Heqparams: params = map vty_var (s_params s))
(Hlents: length ts = length args)
(Hlenvs: length params  = length (s_params s))
(Hall: Forall (fun x => term_has_type gamma (fst x) (snd x))
  (combine ts (map (ty_subst (s_params s) params) args)))
(i: nat)
(Hi: i < length args):
hnth i
  (get_arg_list v params ts reps (s_params_Nodup s) Hlents Hlenvs Hall) s_int (dom_int pd) =
  dom_cast (dom_aux pd) (arg_list_hnth_eq s Heqparams Hi v)
  (reps (nth i ts tm_d) (ty_subst (s_params s) 
    (params) (nth i args vty_int))
  (arg_list_hnth_ty Hlents Hall Hi)).
Proof.
  apply get_arg_list_hnth; auto.
Qed. 

(*The function version*)

Lemma fun_ty_inv {s} {f: funsym} 
  {vs: list vty} {tms: list term} {ty_ret}:
  term_has_type s (Tfun f vs tms) ty_ret ->
  length tms = length (s_args f) /\
  length vs = length (s_params f) /\
  Forall (fun x => term_has_type s (fst x) (snd x)) 
    (combine tms (map (ty_subst (s_params f) vs) (s_args f))) /\
  ty_ret = ty_subst (s_params f) vs (f_ret f).
Proof.
  intros. inversion H; subst; auto.
Qed.

Definition fun_arg_list {ty} (v: val_typevar)
(f: funsym) (vs: list vty) (ts: list term) 
(reps: forall (t: term) (ty: vty),
  term_has_type gamma t ty ->
  domain (val v ty))
(Hty: term_has_type gamma (Tfun f vs ts) ty):
arg_list domain
  (sym_sigma_args f
    (map (v_subst v) vs)) :=
get_arg_list v vs ts reps (s_params_Nodup f)
  (proj1' (fun_ty_inv Hty))
  (proj1' (proj2' (fun_ty_inv Hty)))
  (proj1' (proj2' (proj2' (fun_ty_inv Hty)))).

(*The predsym version*)

Lemma pred_val_inv {s} {p: predsym} 
  {vs: list vty} {tms: list term}:
  formula_typed s (Fpred p vs tms) ->
  length tms = length (s_args p) /\
  length vs = length (s_params p) /\
  Forall (fun x => term_has_type s (fst x) (snd x)) 
    (combine tms (map (ty_subst (s_params p) vs) (s_args p))).
Proof.
  intros. inversion H; subst; auto.
Qed.

Definition pred_arg_list (v: val_typevar)
(p: predsym) (vs: list vty) (ts: list term) 
(reps: forall (t: term) (ty: vty),
  term_has_type gamma t ty ->
  domain (val v ty))
(Hval: formula_typed gamma (Fpred p vs ts)):
arg_list domain
  (sym_sigma_args p
    (map (v_subst v) vs)) :=
get_arg_list v vs ts reps (s_params_Nodup p)
  (proj1' (pred_val_inv Hval))
  (proj1' (proj2' (pred_val_inv Hval)))
  (proj2' (proj2' (pred_val_inv Hval))).

(*Inversion lemmas we use in the semantics to 
  destruct and reconstruct typing proofs*)

Lemma tfun_params_length {s f vs ts ty}:
  term_has_type s (Tfun f vs ts) ty ->
  length (s_params f) = length vs.
Proof.
  intros. inversion H; subst. rewrite H9. reflexivity.
Qed.

Lemma fpred_params_length {s p vs ts}:
  formula_typed s (Fpred p vs ts) ->
  length (s_params p) = length vs.
Proof.
  intros. inversion H; subst. auto.
Qed.

Lemma ty_constint_inv {s z ty} (H: term_has_type s (Tconst (ConstInt z)) ty) :
  ty = vty_int.
Proof.
  inversion H; auto.
Qed.

Lemma ty_constreal_inv {s r ty} (H: term_has_type s (Tconst (ConstReal r)) ty) :
ty = vty_real.
Proof.
inversion H; auto.
Qed.

Lemma ty_var_inv {s x ty} (H: term_has_type s (Tvar x) ty):
ty = snd x .
Proof.
  inversion H; auto.
Qed.

Lemma ty_let_inv {s t1 x t2 ty} (H: term_has_type s (Tlet t1 x t2) ty):
term_has_type s t1 (snd x) /\ term_has_type s t2 ty.
Proof.
  inversion H; auto.
Qed.

Lemma ty_if_inv {s f t1 t2 ty} (H: term_has_type s (Tif f t1 t2) ty):
term_has_type s t1 ty /\
term_has_type s t2 ty /\
formula_typed s f.
Proof.
  inversion H; auto.
Qed.

Lemma ty_match_inv {s t ty1 ty2 xs} (H: term_has_type s (Tmatch t ty1 xs) ty2):
  term_has_type s t ty1 /\
  Forall (fun x => pattern_has_type s (fst x) ty1) xs /\
  Forall (fun x : pattern * term => term_has_type s (snd x) ty2) xs.
Proof.
  inversion H; subst; split; auto; split; 
  rewrite Forall_forall; auto.
Qed.

Lemma ty_eps_inv {s f x ty'} (H: term_has_type s (Teps f x) ty'):
  formula_typed s f /\ ty' = snd x.
Proof.
  inversion H; subst; auto.
Qed.

Lemma typed_not_inv {s f} (H: formula_typed s (Fnot f)):
  formula_typed s f.
Proof.
  inversion H; auto.
Qed.

Lemma typed_let_inv {s t x f} (H: formula_typed s (Flet t x f)):
term_has_type s t (snd x) /\
formula_typed s f.
Proof.
  inversion H; auto.
Qed.

Lemma typed_binop_inv {s b f1 f2} (H: formula_typed s (Fbinop b f1 f2)):
formula_typed s f1 /\
formula_typed s f2.
Proof.
  inversion H; auto.
Qed.

Lemma typed_if_inv {s f1 f2 f3} (H: formula_typed s (Fif f1 f2 f3)):
formula_typed s f1 /\
formula_typed s f2 /\
formula_typed s f3.
Proof.
  inversion H; auto.
Qed.

Lemma typed_quant_inv {s q x f} (H: formula_typed s (Fquant q x f)):
  formula_typed s f.
Proof.
  inversion H; auto.
Qed.

Lemma typed_match_inv {s t ty1 xs} (H: formula_typed s (Fmatch t ty1 xs)):
  term_has_type s t ty1 /\
  Forall (fun x => pattern_has_type s (fst x) ty1) xs /\
  Forall (fun x : pattern * formula => formula_typed s (snd x)) xs.
Proof.
  inversion H; subst; rewrite !Forall_forall; split; auto. 
Qed.

Lemma typed_eq_inv {s ty t1 t2} (H: formula_typed s (Feq ty t1 t2)):
  term_has_type s t1 ty /\ term_has_type s t2 ty.
Proof.
  inversion H; auto.
Qed.

(*Pattern matches are quite complicated. Rather than compiling down
  to elementary let statements, as in the paper, we instead build up
  the entire valuation (consisting of pairs of vsymbols and domain
  elements for an appropriate type). Doing this is conceptually simple,
  but very difficult in practice due to depenedent type obligations.
  
  The interesting case is the case when we match against a constructor.
  In this case, we determine if the type is an instance of and ADT, 
  and if so, we use [find_constr_rep] (after some casting) to get 
  the constructor and arguments (arg_list) that comprise this instance.
  Then, we check if the constructor equals the one in the pattern match,
  and if so, we iterate through the arg_list and build up the valuation
  entries recursively, returning None if we ever find a non-matching pattern.
  
  We need many of the above lemmas to handle the preconditions for
  [find_constr_rep] and casting.
  *)

Lemma pat_var_inv {s x ty}:
  pattern_has_type s (Pvar x) ty ->
  snd x = ty.
Proof.
  intros. inversion H; subst; auto.
Qed.

Lemma pat_or_inv {s p1 p2 ty}:
  pattern_has_type s (Por p1 p2) ty ->
  pattern_has_type s p1 ty /\ pattern_has_type s p2 ty.
Proof.
  intros. inversion H; subst. auto.
Qed.

Lemma pat_bind_inv {s p x ty}:
  pattern_has_type s (Pbind p x) ty ->
  pattern_has_type s p ty /\ ty = snd x.
Proof.
  intros. inversion H; subst. auto.
Qed.

(*Typecast we need for inner arg list*)
Lemma sym_sigma_args_map (v: val_typevar) (f: funsym) 
  (vs: list vty):
  length (s_params f) = length vs ->
  sym_sigma_args f (map (val v) vs) =
  map (val v) (ty_subst_list (s_params f) vs (s_args f)).
Proof.
  intros Hlen.
  unfold sym_sigma_args, ty_subst_list_s, ty_subst_list.
  apply list_eq_ext'; rewrite !length_map; auto.
  intros n d Hn.
  rewrite !map_nth_inbound with (d2:=vty_int); auto;
  [|rewrite length_map]; auto.
  symmetry. apply funsym_subst_eq; auto.
  apply s_params_Nodup.
Qed.

Lemma constr_length_eq: forall {ty m a vs c},
  is_vty_adt gamma ty = Some (m, a, vs) ->
  valid_type gamma ty ->
  constr_in_adt c a ->
  length (s_params c) = length vs.
Proof.
  intros.
  rewrite (adt_vty_length_eq gamma gamma_valid H H0).
  f_equal.
  apply is_vty_adt_some in H. destruct_all; subst.
  apply (adt_constr_params gamma_valid H3 H2 H1).
Qed.

Lemma adt_constr_subst_ret {params a m f}:
  mut_in_ctx m gamma ->
  adt_in_mut a m ->
  constr_in_adt f a ->
  length params = length (s_params f) ->
  ty_subst (s_params f) params (f_ret f) = vty_cons (adt_name a) params.
Proof.
  intros m_in a_in c_in Hlen.
  rewrite (adt_constr_ret gamma_valid m_in a_in c_in).
  rewrite (adt_constr_params gamma_valid m_in a_in c_in) in Hlen |- *.
  unfold ty_subst. simpl. f_equal.
  apply list_eq_ext'; rewrite !length_map; auto.
  intros n d Hn.
  rewrite map_nth_inbound with (d2:=vty_int); [|rewrite length_map; auto].
  rewrite (map_nth_inbound) with (d2:=EmptyString); auto.
  simpl.
  rewrite ty_subst_fun_nth with(s:=d); auto.
  rewrite <- (adt_constr_params gamma_valid m_in a_in c_in).
  apply s_params_Nodup.
Qed.

Lemma pat_constr_ind {s params ps vs f1 f2 m a}:
  pattern_has_type s (Pconstr f1 params ps) (vty_cons (adt_name a) vs) ->
  mut_in_ctx m gamma ->
  adt_in_mut a m ->
  f1 = f2 ->
  constr_in_adt f2 a ->
  Forall (fun x => pattern_has_type s (fst x) (snd x))
    (combine ps (ty_subst_list (s_params f2) vs (s_args f2))).
Proof.
  intros. subst.
  inversion H; subst.
  subst sigma.
  rewrite (adt_constr_subst_ret H0 H1 H3) in H6; auto.
  inversion H6; subst.
  rewrite Forall_forall.
  intros. apply H13.
  apply H2. 
Qed.

Definition cast_prop {A: Set} (P: A -> Prop) {a1 a2: A} (H: a1 = a2)
  (Hp: P a1) : P a2 := eq_ind _ P Hp _ H.

Definition pat_has_type_eq {s p ty1 ty2} (H: ty1 = ty2) 
  (Hp: pattern_has_type s p ty1):
  pattern_has_type s p ty2 :=
  cast_prop (pattern_has_type s p) H Hp.


(*Updated version: relies on well-typedness
  and matches on ty for constr case, NOT (val ty), which
  removes useful information*)
Fixpoint match_val_single (v: val_typevar) (ty: vty)
  (p: pattern) 
  (Hp: pattern_has_type gamma p ty)
  (d: domain (val v ty))
  {struct p} : 
  (*For a pair (x, d), we just need that there is SOME type t such that
    d has type [domain (val v t)], but we don't care what t is.
    We prove later that it matches (snd x)*)
  option (amap vsymbol {s: sort & domain s }) :=
  match p as p' return pattern_has_type gamma p' ty -> 
    option (amap vsymbol {s: sort & domain s }) with
  | Pvar x => fun Hty' =>
    (*Here, it is safe to always give Some*)
    Some (amap_singleton x (existT (val v ty) d))
  | Pwild => fun _ => Some amap_empty
  | Por p1 p2 => fun Hty' =>
    match (match_val_single v ty p1 (proj1' (pat_or_inv Hty')) d) with
                  | Some v1 => Some v1
                  | None => match_val_single v ty p2 
                    (proj2' (pat_or_inv Hty')) d
                  end
  | Pbind p1 x => fun Hty' =>
    (*Binding adds an additional binding at the end for the whole
      pattern*)
    match (match_val_single v ty p1 (proj1' (pat_bind_inv Hty')) d) with
    | None => None
    | Some l => Some (amap_set l x (existT (val v ty) d))
      (*if (vty_eq_dec (snd x) ty) then 
       Some ((x, (existT _ ty d)) :: l) else None*)
    end
  | Pconstr f params ps => fun Hty' =>

    match (is_vty_adt gamma ty) as o return
      is_vty_adt gamma ty = o ->
      option (amap vsymbol {s: sort & domain s })
    with
    | Some (m, a, vs) => fun Hisadt => 
      (*Get info from [is_vty_adt_some]*)
      let Htyeq : ty = vty_cons (adt_name a) vs :=
        proj1' (is_vty_adt_some gamma Hisadt) in
      let a_in : adt_in_mut a m :=
        proj1' (proj2' (is_vty_adt_some gamma Hisadt)) in
      let m_in : mut_in_ctx m gamma :=
        proj2' (proj2' (is_vty_adt_some gamma Hisadt)) in

      let srts := (map (val v) vs) in

      let valeq : val v ty = typesym_to_sort (adt_name a) srts :=
        eq_trans (f_equal (val v) Htyeq)
          (v_subst_cons (adt_name a) vs) in

      (*We cast to get an ADT, now that we know that this actually is
          an ADT*)
      let adt : adt_rep m srts (dom_aux pd) a a_in :=
        scast (adts pdf m srts a m_in a_in) (dom_cast _ 
          valeq d) in

      (*Need a lemma about lengths for [find_constr_rep]*)
      let lengths_eq : length srts = length (m_params m) := 
        eq_trans (length_map _ _)
          (adt_vty_length_eq gamma gamma_valid Hisadt 
          (pat_has_type_valid _ _ _ Hty')) in

      (*The key part: get the constructor c and arg_list a
          such that d = [[c(a)]]*)
      let Hrep := find_constr_rep gamma_valid m m_in srts lengths_eq 
        (dom_aux pd) a a_in (adts pdf m srts) 
        (gamma_all_unif gamma_valid m m_in) adt in

      (*The different parts of Hrep we need*)
      let c : funsym := projT1 Hrep in
      let c_in : constr_in_adt c a :=
        fst (proj1_sig (projT2 Hrep)) in
      let args : arg_list domain (sym_sigma_args c srts) := 
        snd (proj1_sig (projT2 Hrep)) in

      let lengths_eq' : length (s_params c) = length vs :=
        (constr_length_eq Hisadt 
        (pat_has_type_valid _ _ _ Hty') c_in) in
      (*If the constructors match, check all arguments,
        otherwise, gives None*)
      (*We need proof of equality*)
      match funsym_eq_dec c f with
      | left Heq =>
        (*Idea: iterate over arg list, build up valuation, return None
        if we every see None*)
        (*This function is actually quite simple, we just need a bit
        of dependent pattern matching for the [arg_list]*)
        let fix iter_arg_list (tys: list vty)
          (a: arg_list domain (map (val v) tys))
          (pats: list pattern)
          (Hall: Forall (fun x => pattern_has_type gamma (fst x) (snd x)) 
            (combine pats tys))
          {struct pats} :
          option (amap vsymbol {s: sort & domain s }) :=
          match tys as t' return arg_list domain (map (val v) t') ->
            forall (pats: list pattern)
            (Hall: Forall (fun x => pattern_has_type gamma (fst x) (snd x)) 
              (combine pats t')),
            option (amap vsymbol {s: sort & domain s })
          with 
          | nil => fun _ pats _ =>
            (*matches only if lengths are the same*)
            match pats with
            | nil => Some amap_empty
            | _ => None
            end
          | ty :: tl => fun a' ps' Hall' =>
            match ps' as pats return 
              Forall (fun x => pattern_has_type gamma (fst x) (snd x)) 
                (combine pats (ty :: tl) ) ->
              option (amap vsymbol {s: sort & domain s })
            with 
            | nil => fun _ => None
            | phd :: ptl => fun Hall' =>
              (*We try to evaluate the head against the first pattern.
                If this succeeds we combine with tail, if either fails
                we give None*)
              (*Since ty is a sort, val v ty = ty, therefore we can cast*)
              match (match_val_single v ty phd (Forall_inv Hall') 
                (hlist_hd a')) with
              | None => None
              | Some l =>
                match iter_arg_list tl (hlist_tl a') ptl
                  (Forall_inv_tail Hall') with
                | None => None
                | Some l' => Some (amap_union (fun x _ => Some x) l l')
                end
              end
            end Hall'
          end a pats Hall
        in

        let c_in': constr_in_adt f a :=
          cast_prop (fun x => constr_in_adt x a) Heq c_in in

        iter_arg_list _ (cast_arg_list 
          (sym_sigma_args_map v c vs lengths_eq') args) ps
          (pat_constr_ind (pat_has_type_eq Htyeq Hty') m_in a_in 
            (eq_sym Heq) c_in)

      | right Hneq => None
      end

    (*Has to be ADT, will rule out later*)
    | None => fun _ => None
    end eq_refl
  end Hp.

(*Rewrite version*)
Fixpoint iter_arg_list {v: val_typevar} (tys: list vty)
  (a: arg_list domain (map (val v) tys))
  (pats: list pattern)
  (Hall: Forall (fun x => pattern_has_type gamma (fst x) (snd x)) 
    (combine pats tys))
  {struct pats} :
  option (amap vsymbol {s: sort & domain s }) :=
  match tys as t' return arg_list domain (map (val v) t') ->
    forall (pats: list pattern)
    (Hall: Forall (fun x => pattern_has_type gamma (fst x) (snd x)) 
      (combine pats t')),
    option (amap vsymbol {s: sort & domain s })
  with 
  | nil => fun _ pats _ =>
    (*matches only if lengths are the same*)
    match pats with
    | nil => Some amap_empty
    | _ => None
    end
  | ty :: tl => fun a' ps' Hall' =>
    match ps' as pats return 
      Forall (fun x => pattern_has_type gamma (fst x) (snd x)) 
        (combine pats (ty :: tl) ) ->
      option (amap vsymbol {s: sort & domain s })
    with 
    | nil => fun _ => None
    | phd :: ptl => fun Hall' =>
      (*We try to evaluate the head against the first pattern.
        If this succeeds we combine with tail, if either fails
        we give None*)
      (*Since ty is a sort, val v ty = ty, therefore we can cast*)
      match (match_val_single v ty phd (Forall_inv Hall') 
        (hlist_hd a')) with
      | None => None
      | Some l =>
        match iter_arg_list tl (hlist_tl a') ptl
          (Forall_inv_tail Hall') with
        | None => None
        | Some l' => Some (amap_union (fun x _ => Some x) l l')
        end
      end
    end Hall'
  end a pats Hall.

Lemma match_val_single_rewrite  (v: val_typevar) (ty: vty)
  (p: pattern) 
  (Hp: pattern_has_type gamma p ty)
  (d: domain (val v ty)) : 
  match_val_single v ty p Hp d =
  match p as p' return pattern_has_type gamma p' ty -> 
    option (amap vsymbol {s: sort & domain s }) with
  | Pvar x => fun Hty' =>
    Some (amap_singleton x (existT (val v ty) d))
  | Pwild => fun _ => Some amap_empty
  | Por p1 p2 => fun Hty' =>
    match (match_val_single v ty p1 (proj1' (pat_or_inv Hty')) d) with
                  | Some v1 => Some v1
                  | None => match_val_single v ty p2 
                    (proj2' (pat_or_inv Hty')) d
                  end
  | Pbind p1 x => fun Hty' =>
    match (match_val_single v ty p1 (proj1' (pat_bind_inv Hty')) d) with
    | None => None
    | Some l =>Some (amap_set l x (existT (val v ty) d))
    end
  | Pconstr f params ps => fun Hty' =>
    match (is_vty_adt gamma ty) as o return
      is_vty_adt gamma ty = o ->
      option (amap vsymbol {s: sort & domain s }) 
    with
    | Some (m, a, vs) =>  fun Hisadt => 
      let Htyeq : ty = vty_cons (adt_name a) vs :=
        proj1' (is_vty_adt_some gamma Hisadt) in
      let a_in : adt_in_mut a m :=
        proj1' (proj2' (is_vty_adt_some gamma Hisadt)) in
      let m_in : mut_in_ctx m gamma :=
        proj2' (proj2' (is_vty_adt_some gamma Hisadt)) in

      let srts := (map (val v) vs) in

      let valeq : val v ty = typesym_to_sort (adt_name a) srts :=
        eq_trans (f_equal (val v) Htyeq)
          (v_subst_cons (adt_name a) vs) in

      let adt : adt_rep m srts (dom_aux pd) a a_in :=
        scast (adts pdf m srts a m_in a_in) (dom_cast _ 
          valeq d) in

      let lengths_eq : length srts = length (m_params m) := 
        eq_trans (length_map _ _)
          (adt_vty_length_eq gamma gamma_valid Hisadt 
          (pat_has_type_valid _ _ _ Hty')) in

      let Hrep := find_constr_rep gamma_valid m m_in srts lengths_eq 
        (dom_aux pd) a a_in (adts pdf m srts) 
        (gamma_all_unif gamma_valid m m_in) adt in

      let c : funsym := projT1 Hrep in
      let c_in : constr_in_adt c a :=
        fst (proj1_sig (projT2 Hrep)) in
      let args : arg_list domain (sym_sigma_args c srts) := 
        snd (proj1_sig (projT2 Hrep)) in

      let lengths_eq' : length (s_params c) = length vs :=
        (constr_length_eq Hisadt 
        (pat_has_type_valid _ _ _ Hty') c_in) in

      match funsym_eq_dec c f with
      | left Heq =>

        let c_in': constr_in_adt f a :=
          cast_prop (fun x => constr_in_adt x a) Heq c_in in

        iter_arg_list _ (cast_arg_list 
          (sym_sigma_args_map v c vs lengths_eq') args) ps
          (pat_constr_ind (pat_has_type_eq Htyeq Hty') m_in a_in 
            (eq_sym Heq) c_in)

      | right Hneq => None
      end
    | None => fun _ => None
    end eq_refl
  end Hp.
Proof.
  destruct p; try solve[reflexivity].
  unfold match_val_single; fold match_val_single.
  generalize dependent (@is_vty_adt_some gamma ty).
  generalize dependent (@adt_vty_length_eq gamma gamma_valid ty).
  generalize dependent (@constr_length_eq ty).
  destruct (is_vty_adt gamma ty) eqn : Hisadt; [|reflexivity].
  intros Hvslen1 Hvslen2 Hadtspec.
  destruct p as [[m adt] vs2].
  destruct (Hadtspec m adt vs2 eq_refl)
    as [Htyeq [Hinmut Hinctx]].
  simpl.
  (*Need nested induction, simplify first*)
  case_find_constr. intros.
  destruct (funsym_eq_dec (projT1 s) f); [|reflexivity].
  destruct s as [f' Hf']. simpl in *. subst. 
  match goal with 
  | |- ?f ?x1 ?x2 ?x3 ?x4 = ?g ?x1 ?x2 ?x3 ?x4 =>
    let H := fresh in
    assert (H: forall a b c d, f a b c d = g a b c d); [|apply H]
  end. clear.
  induction a; intros.
  - simpl. destruct c; reflexivity.
  - destruct c; try reflexivity.
    simpl.
    destruct (match_val_single v a p (Forall_inv d) (hlist_hd b)) eqn : Hm1;
    try reflexivity.
    rewrite IHa. reflexivity.
Qed.


Lemma pat_constr_disj_map {s f vs ps ty}:
  pattern_has_type s (Pconstr f vs ps) ty ->
  disj_map' pat_fv ps.
Proof.
  intros. inversion H; subst.
  unfold disj_map'.
  intros.
  apply H11; lia.
Qed.
  
(*Now we want a generic way to prove things about
  [match_val_single] so we don't have to do all of the very
  tedious generalization and nested induction every time*)
(*NOTE: this is not very useful, we cannot use in many places*)
Lemma match_val_single_ind 
(P : forall (v : val_typevar) (ty : vty) (p : pattern)
  (d: domain (val v ty)),
  option (amap vsymbol {s: sort & domain s}) -> Prop)
(*In arg list case, lets us retain info*)
(Q: forall (l: list sort), arg_list domain l -> Prop)
(Hvar: forall (v : val_typevar) (ty : vty) (x : vsymbol)
  (Hty' : pattern_has_type gamma (Pvar x) ty) 
  (d : domain (val v ty)),
    P v ty (Pvar x) d (*ty (Pvar x) Hty' d*)
      (Some (amap_singleton x (existT (val v ty) d))))
(*This one is different; we don't want the user to have
  to do induction every time, so we give more concrete conditions*)
(*If not ADT, None*)
(Hconstr1: forall (v: val_typevar) (ty: vty) (f: funsym) (params: list vty)
  (ps: list pattern) (Hty': pattern_has_type gamma (Pconstr f params ps) ty)
  (d: domain (val v ty))
  (Hnone: is_vty_adt gamma ty = None),
  P v ty (Pconstr f params ps) d None)
(*If not funsym, None*)
(Hconstr2: forall (v: val_typevar) (ty: vty) (f: funsym) (params: list vty)
  (ps: list pattern) (Hty': pattern_has_type gamma (Pconstr f params ps) ty)
  (d: domain (val v ty))
  m vs2 adt
  (Hisadt: is_vty_adt gamma ty = Some (m, adt, vs2))
  (Htyeq: ty = vty_cons (adt_name adt) vs2)
  (Hinmut: adt_in_mut adt m)
  (Hinctx: mut_in_ctx m gamma)
  (Hvslen2: Datatypes.length vs2 = Datatypes.length (m_params m)),
  projT1
  (find_constr_rep gamma_valid m Hinctx (map (val v) vs2)
    (eq_trans (length_map (val v) vs2)
        (Hvslen2)) 
    (dom_aux pd) adt Hinmut (adts pdf m (map (val v) vs2)) 
    (gamma_all_unif gamma_valid m Hinctx)
    (scast (adts pdf m (map (val v) vs2) adt Hinctx Hinmut)
        (dom_cast (dom_aux pd)
          (eq_trans (f_equal (val v) Htyeq) 
          (v_subst_cons (adt_name adt) vs2)) d))) <>
  f ->
    P v ty (Pconstr f params ps) d None)
(*Note: we add as much info as possible to make the condition
  as weak as possible*)
(Hq: forall
  (v: val_typevar) (f: funsym) (*(vs: list vty)*)
  (adt: alg_datatype) (vs2: list vty) (m: mut_adt)
  (Hvslen2: forall (m0 : mut_adt) (a : alg_datatype) (vs : list vty),
    Some (m, adt, vs2) = Some (m0, a, vs) ->
    valid_type gamma (vty_cons (adt_name adt) vs2) ->
    Datatypes.length vs = Datatypes.length (m_params m0))
  (Hisadt: is_vty_adt gamma (vty_cons (adt_name adt) vs2) = Some (m, adt, vs2))
  (d: domain (val v (vty_cons (adt_name adt) vs2)))
  (Hinmut: adt_in_mut adt m)
  (Hinctx: mut_in_ctx m gamma)
  (i: constr_in_adt f adt)
  (Hval: valid_type gamma (vty_cons (adt_name adt) vs2))
  (a: arg_list domain (ty_subst_list_s (s_params f) (map (val v) vs2) 
    (s_args f)))
  (e: scast (adts pdf m (map (val v) vs2) adt Hinctx Hinmut)
        (dom_cast (dom_aux pd) (eq_trans eq_refl (v_subst_cons (adt_name adt) vs2)) d) =
      constr_rep gamma_valid m Hinctx (map (val v) vs2)
        (eq_trans (length_map (val v) vs2) (Hvslen2 m adt vs2 eq_refl Hval)) 
        (dom_aux pd) adt Hinmut f i (adts pdf m (map (val v) vs2)) a),
    Q _ a)
(Hconstr3: forall (v: val_typevar) (f: funsym) (params: list vty)
  (adt: alg_datatype) (vs2: list vty) (m: mut_adt)
  (Hisadt: is_vty_adt gamma (vty_cons (adt_name adt) vs2) = Some (m, adt, vs2))
  (d: domain (val v (vty_cons (adt_name adt) vs2)))
  (Hinmut: adt_in_mut adt m)
  (Hinctx: mut_in_ctx m gamma)
  (i: constr_in_adt f adt)
  (Hval: valid_type gamma (vty_cons (adt_name adt) vs2))
  (l: list vty)
  (ps: list pattern)
  (Hps: disj_map' pat_fv ps) 
  (*Here, we generalize a but assume it satisfies Q, so we can
    retain some info*)
  (Hall: Forall
    (fun p : pattern =>
    forall (ty : vty) (Hp : pattern_has_type gamma p ty) (d : domain (val v ty)),
    P v ty p d (match_val_single v ty p Hp d)) ps)
  (a : arg_list domain (ty_subst_list_s (s_params f) (map (val v) vs2) l))
  (e : ty_subst_list_s (s_params f) (map (val v) vs2) l =
        map (val v) (ty_subst_list (s_params f) vs2 l))
  (f0 : Forall (fun x : pattern * vty => pattern_has_type gamma (fst x) (snd x))
          (combine ps (ty_subst_list (s_params f) vs2 l)))
  (*We assume q holds of a*)
  (Hq: Q _ a),
  P v (vty_cons (adt_name adt) vs2) (Pconstr f params ps) d (iter_arg_list 
    (ty_subst_list (s_params f) vs2 l) (cast_arg_list e a) ps f0))
(Hwild: forall (v : val_typevar) (ty : vty)
  (Hty' : pattern_has_type gamma Pwild ty) 
  (d : domain (val v ty)), P v ty Pwild (*Hty'*) d (Some amap_empty))
(Hor: forall (v : val_typevar) (ty : vty) (p1 p2 : pattern)
  (Hty' : pattern_has_type gamma (Por p1 p2) ty)
  (d : domain (val v ty))
  (IH1: P v ty p1 d (*ty p1 (proj1' (pat_or_inv Hty')) d*)
    (match_val_single v ty p1 (proj1' (pat_or_inv Hty')) d))
  (IH2: P v ty p2 d (*ty p2 (proj2' (pat_or_inv Hty')) d*)
    (match_val_single v ty p2 (proj2' (pat_or_inv Hty')) d)),
  P v ty (Por p1 p2) d (*ty (Por p1 p2) Hty' d*)
    match
      match_val_single v ty p1 (proj1' (pat_or_inv Hty')) d
    with
    | Some v1 => Some v1
    | None => match_val_single v ty p2 (proj2' (pat_or_inv Hty')) d
    end)
(Hbind: forall (v : val_typevar) (ty : vty) (p1 : pattern) 
  (x : vsymbol) (Hty' : pattern_has_type gamma (Pbind p1 x) ty)
  (d : domain (val v ty))
  (IH: P v ty p1 d (*ty p1 (proj1' (pat_bind_inv Hty')) d*)
    (match_val_single v ty p1 (proj1' (pat_bind_inv Hty')) d)),
  P v ty (Pbind p1 x) d (*ty (Pbind p1 x) Hty' d*)
    match
      match_val_single v ty p1 (proj1' (pat_bind_inv Hty')) d
    with
    | Some l =>
       Some (amap_set l x (existT (val v ty) d))
    | None => None
    end):
forall (v : val_typevar) (ty : vty) (p : pattern)
 (Hp : pattern_has_type gamma p ty) (d : domain (val v ty)),
P v ty p (*Hp*) d (match_val_single v ty p Hp d).
Proof.
  intros. generalize dependent ty.
  induction p; intros.
  - simpl. apply Hvar. auto.
  - (*The hard case: do work here so we don't have to repeat*)
    rewrite match_val_single_rewrite. simpl.
    generalize dependent (@is_vty_adt_some gamma ty).
    generalize dependent (@adt_vty_length_eq gamma gamma_valid ty).
    generalize dependent (@constr_length_eq ty).
    destruct (is_vty_adt gamma ty) eqn : Hisadt.
    2: {
      intros. apply (Hconstr1 v ty f vs ps Hp d). auto. }
    intros Hvslen1 Hvslen2 Hadtspec.
    destruct p as [[m adt] vs2].
    destruct (Hadtspec m adt vs2 eq_refl)
      as [Htyeq [Hinmut Hinctx]].
    simpl.
    match goal with
    | |- context [match funsym_eq_dec (projT1 ?x) ?f with 
      | left Heq => _ | right Hneq => _ end ] =>
        destruct (funsym_eq_dec (projT1 x) f) ;[
          generalize dependent x| 
          apply (Hconstr2 v ty f vs ps Hp d m vs2 adt Hisadt Htyeq Hinmut _ _ n)
        ]
    end.
    intros constr. destruct constr as [f' Hf']. simpl. intros Hf; subst.
    simpl.
    match goal with
    | |- P ?v ?ty ?p ?d (iter_arg_list ?l ?vs2 ?a ?H) =>
      generalize dependent H
    end.
    destruct Hf'. simpl. (*clear e.*)
    destruct x. simpl.
    generalize dependent ((pat_has_type_valid gamma (Pconstr f vs ps)
    (vty_cons (adt_name adt) vs2) Hp)).
    intros Hval e. simpl in e.
    generalize dependent (sym_sigma_args_map v f vs2
    (Hvslen1 m adt vs2 f eq_refl
       Hval i)).
    intros.
    apply (Hconstr3 v f vs adt vs2 m Hisadt 
      d Hinmut Hinctx i Hval); auto.
    apply (pat_constr_disj_map Hp).
    eapply Hq. apply Hisadt. apply e.
  - apply (Hwild v ty); auto.
  - apply Hor. apply IHp1. apply IHp2.
  - apply Hbind. apply IHp.
Qed.

(*Lemmas about [match_val_single]*)

(*1. All types align with that of the vsymbol*)
(*Note that we do NOT need induction on p, and 
  we need no generalization*)
Lemma match_val_single_typs (v: val_typevar) (ty: vty)
(p: pattern)
(Hty: pattern_has_type gamma p ty)
(d: domain (val v ty)) l:
match_val_single v ty p Hty d = Some l ->
forall x t, amap_lookup l x = Some t -> projT1 t = val v (snd x).
Proof.
  revert v ty p Hty d l.
  apply (match_val_single_ind (fun v ty p d o =>
  forall l,
    o = Some l ->
  forall x t, amap_lookup l x = Some t-> projT1 t = val v (snd x))
  (fun _ _ => True)); auto.
  - intros v ty x Hty d m Hsome y t Hlookup.
    inversion Hsome; subst; auto; clear Hsome. unfold amap_singleton in Hlookup.
    destruct (vsymbol_eq_dec x y); subst; auto.
    + rewrite amap_set_lookup_same in Hlookup. inversion Hlookup; subst; auto.
      inversion Hty; subst; auto.
    + rewrite amap_set_lookup_diff in Hlookup; auto.
      rewrite amap_empty_get in Hlookup. discriminate.
  - intros. inversion H.
  - intros. discriminate. 
  - intros v f adt vs2 m Hisadt d adt_in m_in f_in Hval.
    induction l; simpl; intros; auto. 
    + destruct ps.
      * inversion H; subst. inversion H0.
      * inversion H.
    + revert H. destruct ps; simpl.
      intros Hc; inversion Hc.
      repeat match goal with 
      |- (match ?p with |Some l => ?x | None => ?y end) = ?z -> ?q =>
        let Hp := fresh "Hmatch" in 
        destruct p eqn: Hp end.
      all: intro C; inversion C.
      subst. inversion Hall; subst.
      rewrite amap_union_lookup in H0.
      destruct (amap_lookup a1 x) as [y1|] eqn : Hget1;
      destruct (amap_lookup a2 x) as [y2|] eqn : Hget2;
      inversion H0; subst; eauto.
      rewrite hlist_tl_cast in Hmatch0.
      apply IHl with(x:=x)(t:=t) in Hmatch0; auto.
      apply (disj_map_cons_impl Hps).
  - intros. inversion H; subst. inversion H0.
  - intros. destruct (match_val_single v ty p1 (proj1' (pat_or_inv Hty')) d) eqn : Hm.
    + apply (IH1 _ H); auto.
    + apply (IH2 _ H); auto.
  - intros. destruct (match_val_single v ty p1 (proj1' (pat_bind_inv Hty')) d) eqn : Hm.
    + inversion H; subst. clear H.
      destruct (vsymbol_eq_dec x x0); subst.
      * rewrite amap_set_lookup_same in H0. inversion H0; subst. inversion Hty'; subst; auto.
      * rewrite amap_set_lookup_diff in H0; auto. apply IH in H0; auto.
    + inversion H.
Qed.

(*3. The variables bound are exactly the free variables of pattern p.
  Note that we do NOT get equality because of OR patterns, but
  Permutation is sufficient*)

(*We put one case in a separate lemma because we need it later*)
Lemma iter_arg_list_fv:
forall (v : val_typevar) (f : funsym)
(vs2 : list vty),
forall (l : list vty) (ps : list pattern),
disj_map' pat_fv ps ->
Forall
(fun p : pattern =>
 forall (ty : vty) (Hp : pattern_has_type gamma p ty) (d0 : domain (val v ty))
   (l0 : amap vsymbol {s : sort & domain s}),
 match_val_single v ty p Hp d0 = Some l0 -> keys l0 = (pat_fv p)) ps ->
forall (a : arg_list domain (ty_subst_list_s (s_params f) (map (val v) vs2) l))
(e : ty_subst_list_s (s_params f) (map (val v) vs2) l =
     map (val v) (ty_subst_list (s_params f) vs2 l))
(f0 : Forall (fun x : pattern * vty => pattern_has_type gamma (fst x) (snd x))
        (combine ps (ty_subst_list (s_params f) vs2 l))),
forall l0 : amap vsymbol {s: sort & domain s},
iter_arg_list (ty_subst_list (s_params f) vs2 l) (cast_arg_list e a) ps f0 = Some l0 ->
keys l0 = aset_big_union pat_fv ps.
Proof.
  intros v f vs2.
  induction l; simpl; intros; auto. 
  + destruct ps; inversion H1; subst.
    rewrite aset_big_union_nil. rewrite keys_empty. reflexivity.
  + revert H1. destruct ps; simpl.
    intros Hc; inversion Hc.
    repeat match goal with 
    |- (match ?p with |Some l => ?x | None => ?y end) = ?z -> ?q =>
      let Hp := fresh "Hmatch" in 
      destruct p eqn: Hp end.
    all: intro C; inversion C.
    subst. clear C.
    (*Now, just need to handle the pieces*)
    inversion H0; subst.
    rewrite hlist_tl_cast in Hmatch0.
    apply IHl in Hmatch0; auto.
    apply H3 in Hmatch.
    rewrite keys_union.
    * rewrite Hmatch, Hmatch0. reflexivity.
    * (*Prove disj - exactly the same*)
      rewrite disj_map_cons_iff in H.
      intros x [Hinx1 Hinx2].
      rewrite Hmatch in Hinx1.
      rewrite Hmatch0 in Hinx2. simpl_set.
      destruct Hinx2 as [p' [Hinp' Hinx2]].
      destruct (In_nth _ _ Pwild Hinp') as [i[ Hi Hp']]; subst.
      destruct H as [Hdisj Hdisj2].
      apply (Hdisj2 i Pwild x Hi); auto.
    * apply (disj_map_cons_impl H).
Qed.

Lemma match_val_single_fv {vt} ty d p l
  (Hty: pattern_has_type gamma p ty):
  match_val_single vt ty p Hty d = Some l ->
  keys l = pat_fv p.
(*   Permutation (map fst l) (pat_fv p). *)
Proof.
  revert vt ty p Hty d l.
  apply (match_val_single_ind (fun v ty p d o =>
  forall l,
    o = Some l ->
    keys l = pat_fv p)
  (fun _ _ => True)); auto; try solve[intros; discriminate].
  - intros. inversion H; subst. simpl. unfold vsymbol. apply keys_singleton.
  - intros. apply (iter_arg_list_fv v f vs2 l ps Hps Hall a e f0).
    auto. 
  - intros. inversion H; subst. apply keys_empty.
  - intros.   
    inversion Hty'; subst.
    simpl. rewrite H6.
    rewrite aset_union_refl. 
    destruct (match_val_single v ty p1 (proj1' (pat_or_inv Hty')) d) eqn: Hm.
    + rewrite <- H6; apply IH1; auto.
    + apply IH2; auto.
  - simpl; intros.
    inversion Hty'; subst.
    destruct (match_val_single v (snd x) p1 (proj1' (pat_bind_inv Hty')) d) eqn : Hm; [|discriminate].
    inversion H; subst; simpl.
    specialize (IH _ eq_refl). rewrite <- IH in H3.
    rewrite keys_set_disj; auto.
    rewrite IH; auto.
Qed.

(*Corollaries*)
(* Corollary match_val_single_free_var vt ty p Hty d l x:
  match_val_single vt ty p Hty d = Some l ->
  In x (pat_fv p) <-> In x (map fst l).
Proof.
  intros. apply match_val_single_perm in H.
  split; apply Permutation_in; auto.
  apply Permutation_sym; auto.
Qed.

Lemma match_val_single_nodup {vt} ty p Hty d l: 
  match_val_single vt ty p Hty d = Some l ->
  NoDup (map fst l).
Proof.
  intros. apply match_val_single_perm in H; auto.
  apply Permutation_sym in H.
  apply Permutation_NoDup in H; auto.
  apply NoDup_pat_fv.
Qed.

Lemma iter_arg_list_free_var:
forall (v : val_typevar) (f : funsym)
(vs2 : list vty),
forall (l : list vty) (ps : list pattern),
disj_map pat_fv ps ->
Forall
(fun p : pattern =>
 forall (ty : vty) (Hp : pattern_has_type gamma p ty) (d0 : domain (val v ty))
   (l0 : list (vsymbol * {s : sort & domain s})),
 match_val_single v ty p Hp d0 = Some l0 -> Permutation (map fst l0) (pat_fv p)) ps ->
forall (a : arg_list domain (ty_subst_list_s (s_params f) (map (val v) vs2) l))
(e : ty_subst_list_s (s_params f) (map (val v) vs2) l =
     map (val v) (ty_subst_list (s_params f) vs2 l))
(f0 : Forall (fun x : pattern * vty => pattern_has_type gamma (fst x) (snd x))
        (combine ps (ty_subst_list (s_params f) vs2 l))),
forall l0 : list (vsymbol * {s: sort & domain s}),
iter_arg_list (ty_subst_list (s_params f) vs2 l) (cast_arg_list e a) ps f0 = Some l0 ->
forall x, In x (big_union vsymbol_eq_dec pat_fv ps) <-> In x (map fst l0).
Proof.
  intros. apply (iter_arg_list_perm v f vs2) in H1; auto.
  split; apply Permutation_in; auto.
  apply Permutation_sym; auto.
Qed. *)

(*Now we give the denotational semantics:*)

Section TermFmlaRep.

Variable vt: val_typevar.

Definition bool_of_binop (b: binop) : bool -> bool -> bool :=
  match b with
  | Tand => andb
  | Tor => orb
  | Timplies => implb
  | Tiff => eqb
  end.

Variable (pf: pi_funpred gamma_valid pd pdf).
Notation funs := (funs gamma_valid pd pf).

(*The match case*)
Section MatchCase.

(*The match case involves iterating over the inner pattern list, calling [match_val_single]
  on each one. We don't want to repeat this each time, so we define a single function
  here instead of using nested recursion. We need an awkward dependently typed encoding
  because terms and formulas are different and have different typing rules. But 
  encoding it this way means that all the types we need are definitionally equal when
  we instantiate with true/false, so we don't need anything special later.*)

Definition gen_ret (b: bool) (ty: gen_type b) :=
  match b return gen_type b -> Type with
  | true => fun ty => domain (val vt ty)
  | false => fun _ => bool
end ty.
Definition gen_default (b: bool) (ty: gen_type b) : gen_ret b ty :=
  match b return forall (ty: gen_type b), gen_ret b ty with
  | true => fun ty => match domain_ne pd (val vt ty) with | DE x => x end
  | false => fun _ => false
  end ty.

(*NOTE: we do not (yet?) prove we never hit None on well-typed pattern
  match by exhaustivenss - need to give exhaustiveness check,
  use ADT rep to show that pattern matches all cases*) 

(*Pattern matching needs nested recursion, just as [get_arg_list]*)
Definition match_rep v 
  (term_rep: forall (v: val_vars pd vt) (t: term) (ty: vty)
    (Hty: term_has_type gamma t ty), domain (val vt ty))
  (formula_rep: forall (v: val_vars pd vt) (f: formula)
    (Hty: formula_typed gamma f), bool)
  (b: bool) (ty:gen_type b) ty1 dom_t :=
 fix match_rep (ps: list (pattern * (gen_term b))) 
      (Hps: Forall (fun x => pattern_has_type gamma (fst x) ty1) ps)
      (Hall: Forall (fun x => gen_typed gamma b (snd x) ty) ps) :
        (gen_ret b ty) := 
    match ps as l' return 
      Forall (fun x => pattern_has_type gamma (fst x) ty1) l' ->
      Forall (fun x => gen_typed gamma b (snd x) ty) l' ->
      gen_ret b ty with
    | (p , dat) :: ptl => fun Hpats Hall =>
      match (match_val_single vt ty1 p (Forall_inv Hpats) dom_t) with
      | Some l => 
          match b return forall (ty: gen_type b) (dat: gen_term b), gen_typed gamma b dat ty -> gen_ret b ty with
          | true => fun ty dat Hty => term_rep (extend_val_with_list pd vt v l) dat ty Hty
          | false => fun ty dat Hty => formula_rep (extend_val_with_list pd vt v l) dat Hty
          end ty dat (Forall_inv Hall)
      | None => match_rep ptl (Forall_inv_tail Hpats) (Forall_inv_tail Hall)
      end
    | _ => (*Will not reach if exhaustive*) fun _ _ => gen_default b ty 
    end Hps Hall .


End MatchCase. 


(*Terms*)
(* There are many dependent type obligations and casting to ensure that
  the types work out. In each case, we separate the hypotheses and give
  explicit types for clarity. The final result is often quite simple and just
  needs 1 or more casts for dependent type purposes. 
  We use Equations to make the dependent pattern matching (on Hty)
  nicer, but we still need a nested fix.
  This also avoids needing to prove separate rewrite lemmas
  for use in different files, since Coq does not unfold some
  parts of this function*)

Equations term_rep (v: val_vars pd vt) (t: term) (ty: vty)
(Hty: term_has_type gamma t ty) : domain (val vt ty) by struct t := {

term_rep v (Tconst (ConstInt z)) ty Hty :=
  let Htyeq : vty_int = ty :=
  eq_sym (ty_constint_inv Hty) in
  cast_dom_vty Htyeq z;

term_rep v (Tconst (ConstReal r)) ty Hty :=
  let Htyeq : vty_real = ty :=
  eq_sym (ty_constreal_inv Hty) in
  cast_dom_vty Htyeq (Q2R r);

term_rep v (Tvar x) ty Hty :=
  let Heq : ty = snd x := ty_var_inv Hty in
  (dom_cast _ (f_equal (val vt) (eq_sym Heq)) (var_to_dom _ vt v x));

term_rep v (Tfun f vs ts) ty Hty :=
  (*Some proof we need; we give types for clarity*)
  let Htyeq : ty_subst (s_params f) vs (f_ret f) = ty :=
    eq_sym (ty_fun_ind_ret Hty) in
  (*The main typecast: v(sigma(ty_ret)) = sigma'(ty_ret), where
    sigma sends (s_params f)_i -> vs_i and 
    sigma' sends (s_params f) _i -> v(vs_i)*)
  let Heqret : v_subst vt (ty_subst (s_params f) vs (f_ret f)) =
    ty_subst_s (s_params f) (map (v_subst vt) vs) (f_ret f) :=
      funsym_subst_eq (s_params f) vs vt (f_ret f) (s_params_Nodup f)
      (tfun_params_length Hty) in

  (* The final result is to apply [funs] to the [arg_list] created recursively
    from the argument domain values. We need two casts to make the dependent
    types work out*)

  cast_dom_vty Htyeq (
    dom_cast (dom_aux pd)
      (eq_sym Heqret)
        ((funs f (map (val vt) vs)) 
          (fun_arg_list vt f vs ts (term_rep v) Hty)));
  
term_rep v (Tlet t1 x t2) ty Hty :=
  let Ht1 : term_has_type gamma t1 (snd x) :=
    proj1' (ty_let_inv Hty) in
  let Ht2 : term_has_type gamma t2 ty :=
    proj2' (ty_let_inv Hty) in 
  term_rep (substi vt v x (term_rep v t1 (snd x) Ht1)) t2 ty Ht2;

term_rep v (Tif f t1 t2) ty Hty :=
  let Ht1 : term_has_type gamma t1 ty :=
    (proj1' (ty_if_inv Hty)) in
  let Ht2 : term_has_type gamma t2 ty :=
    (proj1' (proj2' (ty_if_inv Hty))) in
  let Hf: formula_typed gamma f :=
    (proj2' (proj2' (ty_if_inv Hty))) in
  if (formula_rep v f Hf) then term_rep v t1 ty Ht1 
  else term_rep v t2 ty Ht2;

term_rep v (Tmatch t ty1 xs) ty Hty :=
  let Ht1 : term_has_type gamma t ty1 :=
    proj1' (ty_match_inv Hty) in
  let Hps : Forall (fun x => pattern_has_type gamma (fst x) ty1) xs :=
    proj1' (proj2' (ty_match_inv Hty)) in
  let Hall : Forall (fun x => term_has_type gamma (snd x) ty) xs :=
    proj2' (proj2' (ty_match_inv Hty)) in

  let dom_t := term_rep v t ty1 Ht1 in

  match_rep v term_rep formula_rep true ty ty1 dom_t xs Hps Hall;

term_rep v (Teps f x) ty Hty :=
  let Hval : formula_typed gamma f := proj1' (ty_eps_inv Hty) in
  let Heq : ty = snd x := proj2' (ty_eps_inv Hty) in
  (*We need to show that domain (val v ty) is inhabited*)
  let def : domain (val vt ty) :=
  match (domain_ne pd (val vt ty)) with
  | DE x => x 
  end in
  (*Semantics for epsilon - use Coq's classical epsilon,
    we get an instance y of [domain (val v ty)]
    that makes f true when x evaluates to y*)

  epsilon (inhabits def) (fun (y: domain (val vt ty)) =>
    is_true (formula_rep (substi vt v x (dom_cast _ (f_equal (val vt) Heq) y)) f Hval));
}

with formula_rep (v: val_vars pd vt) (f: formula) 
  (Hval: formula_typed gamma f) : bool by struct f :=

  formula_rep v Ftrue Hval := true;
  formula_rep v Ffalse Hval := false;
  formula_rep v (Fnot f') Hval :=
    let Hf' : formula_typed gamma f' :=
      typed_not_inv Hval
    in 
    negb (formula_rep v f' Hf');

  formula_rep v (Fbinop b f1 f2) Hval :=
    let Hf1 : formula_typed gamma f1 :=
    proj1' (typed_binop_inv Hval) in
    let Hf2 : formula_typed gamma f2 :=
      proj2' (typed_binop_inv Hval) in
    bool_of_binop b (formula_rep v f1 Hf1) (formula_rep v f2 Hf2);

  formula_rep v (Flet t x f') Hval :=
    let Ht: term_has_type gamma t (snd x) :=
      (proj1' (typed_let_inv Hval)) in
    let Hf': formula_typed gamma f' :=
      (proj2' (typed_let_inv Hval)) in
    formula_rep (substi vt v x (term_rep v t (snd x) Ht)) f' Hf';

  formula_rep v (Fif f1 f2 f3) Hval :=
    let Hf1 : formula_typed gamma f1 :=
      proj1' (typed_if_inv Hval) in
    let Hf2 : formula_typed gamma f2 :=
      proj1' (proj2' (typed_if_inv Hval)) in
    let Hf3 : formula_typed gamma f3 :=
      proj2' (proj2' (typed_if_inv Hval)) in
    if formula_rep v f1 Hf1 then formula_rep v f2 Hf2 else formula_rep v f3 Hf3;

  (*Much simpler than Tfun case above because we don't need casting*)
  formula_rep v (Fpred p vs ts) Hval :=
    preds _ _ pf p (map (val vt) vs)
      (pred_arg_list vt p vs ts (term_rep v) Hval);

  formula_rep v (Fquant Tforall x f') Hval :=
    let Hf' : formula_typed gamma f' :=
      typed_quant_inv Hval in
    (*NOTE: HERE is where we need the classical axiom assumptions*)
    all_dec (forall d, formula_rep (substi vt v x d) f' Hf');
  
  formula_rep v (Fquant Texists x f') Hval :=
    let Hf' : formula_typed gamma f' :=
      typed_quant_inv Hval in
    (*NOTE: HERE is where we need the classical axiom assumptions*)
    all_dec (exists d, formula_rep (substi vt v x d) f' Hf');

  formula_rep v (Feq ty t1 t2) Hval := 
    let Ht1 : term_has_type gamma t1 ty := 
      proj1' (typed_eq_inv Hval) in
    let Ht2 : term_has_type gamma t2 ty :=
      proj2' (typed_eq_inv Hval) in
    all_dec (term_rep v t1 ty Ht1 = term_rep v t2 ty Ht2);

  formula_rep v (Fmatch t ty1 xs) Hval :=
    (*Similar to term case*)
    let Ht1 : term_has_type gamma t ty1 :=
      proj1' (typed_match_inv Hval) in
    let Hps : Forall (fun x => pattern_has_type gamma (fst x) ty1) xs :=
      proj1' (proj2' (typed_match_inv Hval)) in
    let Hall : Forall (fun x => formula_typed gamma (snd x)) xs :=
      proj2' (proj2' (typed_match_inv Hval)) in

    let dom_t := term_rep v t ty1 Ht1 in
    
    match_rep v term_rep formula_rep false tt ty1 dom_t xs Hps Hall.

End TermFmlaRep.

End DenotDef.

(*Tactics for proving things about the denotational semantics*)

Ltac simpl_rep :=
  repeat match goal with
  | |- context [term_rep ?valid ?pd _ ?vt ?pf ?v ?t ?ty ?Hty] =>
    lazymatch t with
    | Tconst (ConstInt ?z) => rewrite term_rep_equation_1
    | Tconst (ConstReal ?r) => rewrite term_rep_equation_2
    | Tvar ?v => rewrite term_rep_equation_3
    | Tfun ?f ?l1 ?l2 => rewrite term_rep_equation_4
    | Tlet ?t1 ?v ?t2 => rewrite term_rep_equation_5
    | Tif ?f ?t1 ?t2 => rewrite term_rep_equation_6
    | Tmatch ?t ?v ?ps => rewrite term_rep_equation_7
    | Teps ?f ?v => rewrite term_rep_equation_8
    end
  | |- context [formula_rep ?valid ?pd _ ?vt ?pf ?v ?f ?Hval] =>
    lazymatch f with
    | Fpred ?p ?vs ?ts => rewrite formula_rep_equation_1
    | Fquant Tforall ?x ?f' => rewrite formula_rep_equation_2
    | Fquant Texists ?x ?f' => rewrite formula_rep_equation_3
    | Feq ?ty ?t1 ?t2 => rewrite formula_rep_equation_4
    | Fbinop ?b ?f1 ?f2 => rewrite formula_rep_equation_5
    | Fnot ?f => rewrite formula_rep_equation_6
    | Ftrue => rewrite formula_rep_equation_7
    | Ffalse => rewrite formula_rep_equation_8
    | Flet ?t ?x ?f' => rewrite formula_rep_equation_9
    | Fif ?f1 ?f2 ?f3 => rewrite formula_rep_equation_10
    | Fmatch ?t ?ty1 ?xs => rewrite formula_rep_equation_11
    end
  end.


Ltac destruct_match_single l Hmatch :=
  match goal with |- context [match_val_single ?v ?pd ?vt ?ty ?phd ?H1 ?h1] =>
      destruct (match_val_single v pd vt ty phd H1 h1) as [l|] eqn : Hmatch; simpl
    end.

Ltac destruct_iter_arg_list l Hmatch :=
         match goal with |- context [iter_arg_list ?v ?pd ?ty ?a ?ps ?H1] =>
          destruct (iter_arg_list v pd ty a ps H1) as [l|] eqn : Hmatch; simpl
         end.

Ltac simpl_rep_full :=
  repeat (simpl_rep; cbv zeta; simpl).

Ltac iter_match_gen Hval Htm Hpat Hty :=
  match type of Hval with
  | term_has_type ?s ?t ?ty =>
    generalize dependent (proj1' (ty_match_inv Hval));
    generalize dependent (proj1' (proj2' (ty_match_inv Hval)));
    generalize dependent (proj2' (proj2' (ty_match_inv Hval)))
  | formula_typed ?s ?f =>
    generalize dependent (proj1' (typed_match_inv Hval));
    generalize dependent (proj1' (proj2' (typed_match_inv Hval)));
    generalize dependent (proj2' (proj2' (typed_match_inv Hval)))
  end;
  clear Hval;
  intros Htm Hpat Hty;
  revert Htm Hpat Hty.

(*Now we prove theorems about these semantics. The most 
  important of these are various irrelevance and extensionality 
  results, allowing us to change or ignore the various parameters
  of [term_rep] and [formula_rep] in different cases.
  *)

Section Theorems.

(*The first set of theorems do not fix the context;
  they allow us to change the context under certain circumstances*)

Section ChangeContext.

(*Extensionality for [arg_list]*)
Lemma get_arg_list_ext {gamma1 gamma2 pd} (v: val_typevar)
  (vs: list vty) (ts1 ts2: list term) 
  (reps1: forall (t: term) (ty: vty),
    term_has_type gamma1 t ty ->
    domain (dom_aux pd) (v_subst v ty))
  (reps2: forall (t: term) (ty: vty),
    term_has_type gamma2 t ty ->
    domain (dom_aux pd) (v_subst v ty))
  (Hts: length ts1 = length ts2)
  (Hreps: forall (i: nat),
    i < length ts1 ->
    forall (ty : vty) Hty1 Hty2,
    reps1 (nth i ts1 tm_d) ty Hty1 = reps2 (nth i ts2 tm_d) ty Hty2)
  {args: list vty}
  {params: list typevar}
  (Hp1 Hp2: NoDup params)
  (Hlents1: length ts1 = length args)
  (Hlents2: length ts2 = length args)
  (Hlenvs1 Hlenvs2: length vs = length params)
  (Hall1: Forall (fun x => term_has_type gamma1 (fst x) (snd x))
    (combine ts1 (map (ty_subst params vs) args)))
  (Hall2: Forall (fun x => term_has_type gamma2 (fst x) (snd x))
    (combine ts2 (map (ty_subst params vs) args))):
  get_arg_list pd v vs ts1 reps1 Hp1 Hlents1 Hlenvs1 Hall1 =
  get_arg_list pd v vs ts2 reps2 Hp2 Hlents2 Hlenvs2 Hall2.
Proof.
  unfold get_arg_list. simpl.
  assert (Hlenvs1 = Hlenvs2). apply UIP_dec. apply Nat.eq_dec.
  subst.
  generalize dependent args.
  generalize dependent ts2. 
  induction ts1; simpl; intros. 
  - destruct ts2; [|subst; inversion Hts].
    destruct args; auto. inversion Hlents1.
  - destruct ts2; inversion Hts.
    destruct args.
    + inversion Hlents2.
    + simpl in Hlenvs2. simpl. f_equal.
      * f_equal. apply UIP_dec. apply sort_eq_dec.
        apply (Hreps 0). lia.
      * apply IHts1; auto.
        intros j Hj ty Hty1 Hty2.
        apply (Hreps (S j)); lia.
Qed.

(*An alternate, nicer form when ts are equal*)
Lemma get_arg_list_eq {gamma} pd (v: val_typevar)
(vs: list vty) (ts: list term) 
(reps1 reps2: forall (t: term) (ty: vty),
  term_has_type gamma t ty ->
  domain (dom_aux pd) (v_subst v ty))
(Hreps: Forall
(fun tm : term =>
 forall (ty : vty) (Hty1 Hty2: term_has_type gamma tm ty),
 reps1 tm ty Hty1 = reps2 tm ty Hty2) ts)
{args: list vty}
{params: list typevar}
(Hp1 Hp2: NoDup params)
(Hlents1 Hlents2: length ts = length args)
(Hlenvs1 Hlenvs2: length vs = length params)
(Hall1 Hall2: Forall (fun x => term_has_type gamma (fst x) (snd x))
  (combine ts (map (ty_subst params vs) args))):
get_arg_list pd v vs ts reps1 Hp1 Hlents1 Hlenvs1 Hall1 =
get_arg_list pd v vs ts reps2 Hp2 Hlents2 Hlenvs2 Hall2.
Proof.
  apply get_arg_list_ext; auto.
  intros i Hi ty H1 H2.
  rewrite Forall_forall in Hreps; apply Hreps.
  apply nth_In; auto.
Qed.

Lemma is_vty_adt_same_muts {gamma1 gamma2: context}
  (Hadts: mut_of_context gamma1 = mut_of_context gamma2)
  ty:
  is_vty_adt gamma1 ty = is_vty_adt gamma2 ty.
Proof.
  unfold is_vty_adt. destruct ty; auto.
  assert (find_ts_in_ctx gamma1 t = find_ts_in_ctx gamma2 t). {
    unfold find_ts_in_ctx. rewrite Hadts. reflexivity.
  }
  rewrite H. reflexivity.
Qed.


(*A similar result for [match_val_single]*)

(*NOTE: might need lemma for ones without pat matching
  to remove [mut_of_context] assumption*)
(*TODO: (remove this comment) - used for be Forall2. Here we have in iff,
  which is OK because we can still prove equality for maps by extensionality*)
Lemma match_val_single_ext {gamma1 gamma2: context}
  (gamma_valid1: valid_context gamma1)
  (gamma_valid2: valid_context gamma2)
  (*The contexts must agree on all ADTs*)
  (Hadts: mut_of_context gamma1 = mut_of_context gamma2)
  (pd: pi_dom)
  (pdf1: pi_dom_full gamma1 pd)
  (pdf2: pi_dom_full gamma2 pd)
  (vt1 vt2: val_typevar) (ty: vty)
  (Heq: v_subst vt2 ty = v_subst vt1 ty)
  (p: pattern)
  (Hval1: pattern_has_type gamma1 p ty)
  (Hval2: pattern_has_type gamma2 p ty)
  (d: domain (dom_aux pd) (v_subst vt2 ty)):
  opt_related (fun m1 m2 =>
    forall x1 y1, amap_lookup m1 x1 = Some y1 <->
      exists y2 (Heq: projT1 y1 = projT1 y2),
      amap_lookup m2 x1 = Some y2 /\ 
      projT2 y2 = dom_cast (dom_aux pd) Heq (projT2 y1))
    (match_val_single gamma_valid1 pd pdf1 vt1 ty p Hval1
      (dom_cast (dom_aux pd) Heq d))
    (match_val_single gamma_valid2 pd pdf2 vt2 ty p Hval2 d).
Proof.
  revert ty Hval1 Hval2 Heq d. (*TODO: generalize vt?*)
  induction p; intros ty Hval1 Hval2 Heq d.
  (*NOTE: var MUCH more complicated than before, is there better way?*)
  - (*Pvar*) simpl. intros x1 y1. unfold amap_singleton.
    destruct (vsymbol_eq_dec x1 v); subst; auto.
    + setoid_rewrite amap_set_lookup_same. split.
      * intros Hsome; inversion Hsome; subst. simpl.
        eexists (existT (v_subst vt2 ty) _).
        simpl. exists (eq_sym Heq). split; [reflexivity|].
        rewrite !dom_cast_compose, eq_trans_sym_inv_r. reflexivity.
      * intros [y2 [Heq1 [Hy2 Hproj2]]]. inversion Hy2; subst; clear Hy2. simpl in *.
        subst. f_equal. rewrite !dom_cast_compose.
        destruct y1 as [s d1]. simpl in *. subst. rewrite eq_trans_refl_l.
        destruct Heq. reflexivity.
    + rewrite amap_set_lookup_diff by auto. rewrite amap_empty_get.
      split; try discriminate. setoid_rewrite amap_set_lookup_diff; auto.
      setoid_rewrite amap_empty_get. intros; destruct_all; discriminate.
  - (*Pconstr*)
    rewrite !match_val_single_rewrite. cbn.
    generalize dependent (@is_vty_adt_some gamma1 ty).
    generalize dependent (@is_vty_adt_some gamma2 ty).
    generalize dependent (@adt_vty_length_eq gamma1 gamma_valid1 ty).
    generalize dependent (@adt_vty_length_eq gamma2 gamma_valid2 ty).
    generalize dependent (@constr_length_eq gamma1 gamma_valid1 ty).
    generalize dependent (@constr_length_eq gamma2 gamma_valid2 ty).
    rewrite (is_vty_adt_same_muts Hadts).
    destruct (is_vty_adt gamma2 ty) eqn : Hisadt; [|reflexivity].
    intros Hvslen1_1 Hvslen1_2 Hvslen2_1 Hvslen2_2 Hadtspec1 Hadtspec2.
    destruct p as [[m adt] vs2].
    destruct (Hadtspec1 m adt vs2 eq_refl)
      as [Htyeq1 [Hinmut1 Hinctx1]].
    destruct (Hadtspec2 m adt vs2 eq_refl)
      as [Htyeq2 [Hinmut2 Hinctx2]].
    cbn.
    (*Some easy equalities*)
    assert (Hinmut1 = Hinmut2) by apply bool_irrelevance. subst.
    assert (Htyeq2 = eq_refl). apply UIP_dec. apply vty_eq_dec. subst.
    generalize dependent  (Hvslen2_2 m adt vs2 eq_refl
    (pat_has_type_valid gamma1 (Pconstr f vs ps)
       (vty_cons (adt_name adt) vs2) Hval1)).
    generalize dependent (Hvslen2_1 m adt vs2 eq_refl
    (pat_has_type_valid gamma2 (Pconstr f vs ps)
       (vty_cons (adt_name adt) vs2) Hval2)).
    intros.
    assert (e = e0) by (apply UIP_dec; apply Nat.eq_dec). subst.
    cbn.
    generalize dependent (gamma_all_unif gamma_valid2 m Hinctx1).
    generalize dependent  (gamma_all_unif gamma_valid1 m Hinctx2).
    intros. assert (i = i0) by (apply bool_irrelevance). subst.
    assert (Heq2: map (v_subst vt2) vs2 = map (v_subst vt1) vs2). {
      assert (Heq2:=Heq).
      rewrite !v_subst_cons in Heq2.
      injection Heq2; intros Hmap.
      apply map_inj in Hmap. auto. intros. apply sort_inj. auto.
    }
    (*Relate the two constr reps*)
    case_find_constr.
    intros [f1 [[x_in1 a1] Hcast1]] [f2 [[x_in2 a2] Hcast2]]; simpl in *;
    subst.
    rewrite eq_trans_refl_l in Hcast1, Hcast2. 
    assert (Hconstr:
      (constr_rep gamma_valid2 m Hinctx1 (map (v_subst vt2) vs2)
        (eq_trans (length_map (v_subst vt2) vs2) e0) (dom_aux pd) adt Hinmut2 f1
        x_in1 (adts pdf2 m (map (v_subst vt2) vs2)) a1 =
       scast (f_equal 
        (fun x => adt_rep m x (dom_aux pd) adt Hinmut2) (eq_sym Heq2))
      (constr_rep gamma_valid1 m Hinctx2 (map (v_subst vt1) vs2)
        (eq_trans (length_map (v_subst vt1) vs2) e0) (dom_aux pd) adt Hinmut2 f2
        x_in2 (adts pdf1 m (map (v_subst vt1) vs2)) a2))).
    {
      rewrite <- Hcast1, <- Hcast2. unfold dom_cast.
      rewrite !scast_scast.
      apply scast_eq_uip.
    }
    clear Hcast1 Hcast2.
    (*Now, we put everything in gamma1*)
    erewrite (constr_rep_change_gamma gamma_valid2 gamma_valid1 m Hinctx1
      Hinctx2 (map (v_subst vt2) vs2)
      (eq_trans (length_map (v_subst vt2) vs2) e0) (dom_aux pd))
    with (adts2:=(adts pdf1 m (map (v_subst vt2) vs2))) in Hconstr.
    (*Now both constrs are in gamma1, so we can begin to relate them*)
    (*Now, we first show that f1 = f2*)
    assert (f1 = f2). {
      generalize dependent (eq_trans (length_map (v_subst vt2) vs2) e0).
      generalize dependent (eq_trans (length_map (v_subst vt1) vs2) e0).
      generalize dependent (map (v_subst vt2) vs2).
      intros. subst. (*simpl in H0.*)
      (*Now, we show that if x <> x0, this contradicts disjointness*)
      destruct (funsym_eq_dec f1 f2); subst; auto.
      exfalso. assert (e = e1) by (apply UIP_dec; apply Nat.eq_dec); subst.
      simpl in Hconstr.
      apply (constr_rep_disjoint gamma_valid1 m Hinctx2 _ e1 (dom_aux pd) adt
      Hinmut2 (adts pdf1 m (map (v_subst vt1) vs2)) a1 a2 (ltac:(auto)) Hconstr).
    }
    subst f1.
    (*And now we can show that a1 = a2 (with casting)*)
    assert (a1 = (cast_arg_list (f_equal (sym_sigma_args f2) (eq_sym Heq2)) a2)). {
      generalize dependent (eq_trans (length_map (v_subst vt2) vs2) e0).
      generalize dependent (eq_trans (length_map (v_subst vt1) vs2) e0).
      generalize dependent (map (v_subst vt2) vs2).
      intros. subst.
      (*Now we use injectivity of constructors (knowing that f1 = f2)*) 
      simpl.  unfold cast_arg_list. simpl.
      assert (e = e1) by (apply UIP_dec; apply Nat.eq_dec); subst.
      assert (x_in1 = x_in2) by apply bool_irrelevance; subst.
      simpl in Hconstr.
      apply (constr_rep_inj) in Hconstr; auto.
    }
    subst.
    (*Now that we know all of this information, we can simplify for induction*)
    destruct (funsym_eq_dec f2 f); [| simpl; solve[auto]]. subst.
    (*Deal with Hvslen1*)
    repeat match goal with
    | |- context [sym_sigma_args_map ?vt ?f ?vs ?H] => generalize dependent H
    end.
    intros Hlen1 Hlen2.
    assert (Hlen1 = Hlen2) by (apply UIP_dec; apply Nat.eq_dec); subst.
    simpl.
    assert (x_in2 = x_in1) by (apply bool_irrelevance); subst.
    assert (Heqty: 
      map (v_subst vt2) (ty_subst_list (s_params f) vs2 (s_args f)) =
      map (v_subst vt1) (ty_subst_list (s_params f) vs2 (s_args f))).
    {
      apply list_eq_ext'; rewrite !length_map; auto.
      intros n d'. unfold ty_subst_list; rewrite length_map; intros.
      rewrite !map_nth_inbound with(d2:=vty_int); auto;
      try rewrite length_map; auto.
      rewrite !funsym_subst_eq; auto; try apply s_params_Nodup.
      rewrite Heq2. reflexivity.
    }
    (*Only want 1 cast*)
    assert (Hcast: (cast_arg_list (sym_sigma_args_map vt1 f vs2 Hlen2) a2) =
      cast_arg_list Heqty
      (cast_arg_list (sym_sigma_args_map vt2 f vs2 Hlen2)
        (cast_arg_list (f_equal (sym_sigma_args f) (eq_sym Heq2)) a2))). 
    {
      rewrite !cast_arg_list_compose. apply cast_arg_list_eq.
    }
    rewrite Hcast; clear Hcast.
    generalize dependent (cast_arg_list (sym_sigma_args_map vt2 f vs2 Hlen2)
        (cast_arg_list (f_equal (sym_sigma_args f) (eq_sym Heq2)) a2)).
    intros a3. clear Hconstr. clear a2.
    (*Now generalize for induction*)
    generalize dependent (pat_constr_ind gamma_valid2 Hval2 Hinctx1 Hinmut2 eq_refl x_in1).
    generalize dependent (pat_constr_ind gamma_valid1 Hval1 Hinctx2 Hinmut2 eq_refl x_in1).
    generalize dependent Heqty.
    unfold sym_sigma_args in *.
    clear Hadtspec1 Hadtspec2 Hvslen2_1 Hvslen2_1 Hvslen1_1 Hvslen1_2 
      Hisadt Hval1 Hval2.
    generalize dependent ps.
    generalize dependent a3.
    generalize dependent (s_args f).
    (*The "interesting" part*)
    induction l as [| ahd atl IH]; intros.
    + destruct ps; simpl; try contradiction; auto.
      intros.
      setoid_rewrite amap_empty_get. split; intros; destruct_all; discriminate.
    + destruct ps; [simpl; auto|]. simpl. 
      inversion H; subst.
      (*Now we proceed by cases*)
      rewrite hlist_hd_cast with (Heq2:=cons_inj_hd Heqty).
      rewrite hlist_tl_cast with (Heq:=Heqty).
      specialize (H2 (ty_subst (s_params f) vs2 ahd)
        (Forall_inv f0) (Forall_inv f1) (cons_inj_hd Heqty)
          (hlist_hd a3)).
      revert H2.
      destruct_match_single l1 Hmatch1;
      destruct_match_single l2 Hmatch2; simpl; try contradiction; [|solve[auto]].
      intros Hsome1.
      specialize (IH (hlist_tl a3) _ H3
        (cons_inj_tl Heqty)
        (Forall_inv_tail f0) (Forall_inv_tail f1)).
      revert IH.
      destruct_iter_arg_list l3 Hmatch3;
      destruct_iter_arg_list l4 Hmatch4; simpl; try contradiction; [|solve[auto]].
      intros Hsome2.
      (*And the actual proof*)
      intros x1 y2.
      (*Useful to know None iff None*)
      (*Awkward to state*)
      assert (Hnone: forall l1 l2 (Hm12: forall (x1 : vsymbol) (y1 : {x : sort & domain (dom_aux pd) x}),
         amap_lookup l1 x1 = Some y1 <->
         (exists (y2 : {x : sort & domain (dom_aux pd) x}) (Heq : projT1 y1 = projT1 y2),
            amap_lookup l2 x1 = Some y2 /\ projT2 y2 = dom_cast (dom_aux pd) Heq (projT2 y1))),
        forall x1, amap_lookup l1 x1 = None <-> amap_lookup l2 x1 = None).
      {
        clear.
        intros m1 m2 Hsomem x. destruct (amap_lookup m1 x) as [y|] eqn : Hget1.
        - apply Hsomem in Hget1. destruct Hget1 as [y2 [Heq [Hy2 Hproj2]]].
          split; try discriminate. destruct (amap_lookup m2 x) as [y1|] eqn : Hget2; discriminate.
        - split; auto. intros _. destruct (amap_lookup m2 x) as [y1|] eqn : Hget2; auto.
          assert (Hlookup: amap_lookup m1 x = Some y1). {
            apply Hsomem. exists y1. exists eq_refl. auto.
          }
          rewrite Hlookup in Hget1. discriminate.
      } 
      (*Bunch of cases for union*)
      setoid_rewrite amap_union_lookup.
      destruct (amap_lookup l1 x1) as [y1|] eqn : Hget1;
      destruct (amap_lookup l3 x1) as [y3|] eqn : Hget3;
      assert (Hget1':=Hget1); assert (Hget3':=Hget3);
      try (apply Hsome1 in Hget1'); try (apply Hsome2 in Hget3').
      * destruct Hget1' as [y2' [Heq' [Hy2' Hproj2']]].
        destruct Hget3' as [y2'' [Heq'' [Hy2'' Hproj2'']]]. setoid_rewrite Hy2'.
        split.
        -- intros Hy12; inversion Hy12; subst; clear Hy12. eauto.
        -- intros [y4 [Heq4 [Hy24 Hproj24]]]; subst.
          destruct y1; destruct y2; destruct y2'; destruct y2''; destruct y4; simpl in *; subst.
          unfold dom_cast in Hy24; simpl in Hy24. auto. 
      * destruct Hget1' as [y2' [Heq' [Hy2' Hproj2']]]. setoid_rewrite Hy2'.
        split.
        -- intros Hy12; inversion Hy12; subst; clear Hy12. eauto.
        -- intros [y4 [Heq4 [Hy24 Hproj24]]]; subst.
          destruct y1; destruct y2; destruct y2'; destruct y4; simpl in *; subst.
          unfold dom_cast in Hy24; simpl in Hy24. auto. 
      * (*Mirror of previous*)
        destruct Hget3' as [y2'' [Heq'' [Hy2'' Hproj2'']]].
        assert (Hl2: amap_lookup l2 x1 = None) by (rewrite <- Hnone; eauto).
        setoid_rewrite Hl2. setoid_rewrite Hy2''.
        (*Now do both cases again*)
        split. (*TODO: automate*)
        -- intros Hy12; inversion Hy12; subst; clear Hy12. eauto.
        -- intros [y4 [Heq4 [Hy24 Hproj24]]]; subst.
          destruct y2''; destruct y2; destruct y3; destruct y4; simpl in *; subst.
          unfold dom_cast in Hy24; simpl in Hy24. auto.
      * assert (Hl2: amap_lookup l2 x1 = None) by (rewrite <- (Hnone l1 l2); eauto).
        assert (Hl4: amap_lookup l4 x1 = None) by (rewrite <- (Hnone l3 l4); eauto).
        setoid_rewrite Hl2. setoid_rewrite Hl4. split; intros; intros; destruct_all; discriminate.
  - (*Pwild*) simpl. intros x1 y1. setoid_rewrite amap_empty_get. 
    split; intros; destruct_all; discriminate.
  - (*Por*) simpl.
    specialize (IHp1  _ (proj1' (pat_or_inv Hval1)) (proj1' (pat_or_inv Hval2)) Heq d).
    revert IHp1.
    destruct_match_single l1 Hmatch1;
    destruct_match_single l2 Hmatch2; auto; try contradiction.
  - (*Pbind*) simpl.
    specialize (IHp _ (proj1' (pat_bind_inv Hval1)) (proj1' (pat_bind_inv Hval2)) Heq d).
    revert IHp.
    destruct_match_single l1 Hmatch1;
    destruct_match_single l2 Hmatch2; auto; try contradiction.
    (*var case*)
    intros Hsome x1 y1. 
    destruct (vsymbol_eq_dec x1 v); subst; auto.
    + setoid_rewrite amap_set_lookup_same. split.
      * intros Hsome1; inversion Hsome1; subst. simpl.
        eexists (existT (v_subst vt2 ty) _).
        simpl. exists (eq_sym Heq). split; [reflexivity|].
        rewrite !dom_cast_compose, eq_trans_sym_inv_r. reflexivity.
      * intros [y2 [Heq1 [Hy2 Hproj2]]]. inversion Hy2; subst; clear Hy2. simpl in *.
        subst. f_equal. rewrite !dom_cast_compose.
        destruct y1 as [s d1]. simpl in *. subst. rewrite eq_trans_refl_l.
        clear.
        destruct Heq. reflexivity.
    + rewrite amap_set_lookup_diff by auto. 
      (*IH case*)
      setoid_rewrite amap_set_lookup_diff; auto.
Qed.

(*Corollaries:*)

(*1. Just change gamma*)
Lemma match_val_single_change_gamma {gamma1 gamma2: context}
  (gamma_valid1: valid_context gamma1)
  (gamma_valid2: valid_context gamma2)
  (*The contexts must agree on all ADTs*)
  (Hadts: mut_of_context gamma1 = mut_of_context gamma2)
  (pd: pi_dom)
  (pdf1: pi_dom_full gamma1 pd)
  (pdf2: pi_dom_full gamma2 pd)
  (vt: val_typevar) (ty: vty)
  (p: pattern)
  (Hval1: pattern_has_type gamma1 p ty)
  (Hval2: pattern_has_type gamma2 p ty)
  (d: domain (dom_aux pd) (v_subst vt ty)):
  match_val_single gamma_valid1 pd pdf1 vt ty p Hval1 d =
  match_val_single gamma_valid2 pd pdf2 vt ty p Hval2 d.
Proof.
  pose proof (match_val_single_ext gamma_valid1 gamma_valid2 Hadts pd 
    pdf1 pdf2 vt vt ty eq_refl p Hval1 Hval2 d) as Hrel.
  destruct_match_single l1 Hmatch1;
  destruct_match_single l2 Hmatch2; try contradiction; auto.
  simpl in Hrel.
  f_equal. clear -Hrel.
  (*Prove that this implies equality*)
  apply amap_ext.
  intros x. destruct (amap_lookup l1 x) as [y1|] eqn : Hget.
  - symmetry. apply Hrel in Hget. destruct Hget as [y2 [Heq [Hget2 Hproj2]]].
    destruct y1; destruct y2; simpl in *; subst. unfold dom_cast in Hget2. simpl in Hget2.
    assumption.
  - destruct (amap_lookup l2 x) as [y2|] eqn : Hget1; auto.
    assert (Hlookup: amap_lookup l1 x = Some y2).
    { apply Hrel. exists y2. exists eq_refl. auto. }
    rewrite Hlookup in Hget. discriminate.
Qed.

(*2: Just change typing proof*)
Corollary match_val_single_irrel {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) (v: val_typevar) (ty: vty)
  (p: pattern)
  (Hval1 Hval2: pattern_has_type gamma p ty)
  (d: domain (dom_aux pd) (v_subst v ty)) :
  match_val_single gamma_valid pd pdf v ty p Hval1 d =
  match_val_single gamma_valid pd pdf v ty p Hval2 d.
Proof.
  apply match_val_single_change_gamma; auto.
Qed.

(*3: Change typevar but not gamma*)
Lemma match_val_single_change_vt {gamma: context}
  (gamma_valid: valid_context gamma)
  (pd: pi_dom)
  (pdf: pi_dom_full gamma pd)
  (vt1 vt2: val_typevar) (ty: vty)
  (Heq: v_subst vt2 ty = v_subst vt1 ty)
  (p: pattern)
  (Hval: pattern_has_type gamma p ty)
  (d: domain (dom_aux pd) (v_subst vt2 ty)):
  opt_related (fun l1 l2 =>
  forall x (y: {s: sort & domain (dom_aux pd) s}),
    amap_lookup l2 x = Some y ->
    exists z (Heq: projT1 y = projT1 z), amap_lookup l1 x = Some z /\
    projT2 z =  (dom_cast (dom_aux pd) Heq (projT2 y)))
    (match_val_single gamma_valid pd pdf vt1 ty p Hval
      (dom_cast (dom_aux pd) Heq d))
    (match_val_single gamma_valid pd pdf vt2 ty p Hval d).
Proof.
  pose proof (match_val_single_ext gamma_valid gamma_valid 
    eq_refl pd pdf pdf vt1 vt2 ty Heq p Hval Hval d) as Hopt.
  revert Hopt.
  apply opt_related_impl.
  (*Easy implication*)
  intros a b Hsome x y Hlookup.
  assert (Hget: amap_lookup a x = Some y). {
    apply Hsome. exists y. exists eq_refl. auto.
  }
  exists y. exists eq_refl. auto.
Qed.

(*And finally, an extensionality result for terms and formulas:
  We can change gamma and pf, as long as the interps
  agree on all function and predicate symbols in the term/
  formula *)
(*NOTE: here, we require vv1 and vv2 to agree (modulo casting).
  Later, we will allow it to change, but the result becomes too
  unwieldy if done all at once*)



Theorem term_fmla_change_gamma_pf {gamma1 gamma2: context}
(gamma_valid1: valid_context gamma1)
(gamma_valid2: valid_context gamma2)
(Hadts: mut_of_context gamma1 = mut_of_context gamma2)
(pd: pi_dom)
(pdf1: pi_dom_full gamma1 pd)
(pdf2: pi_dom_full gamma2 pd)
(pf1: pi_funpred gamma_valid1 pd pdf1)
(pf2: pi_funpred gamma_valid2 pd pdf2)
(vt: val_typevar)
(t: term) (f: formula):
(forall (ty: vty) vv
  (Htty1: term_has_type gamma1 t ty)
  (Htty2: term_has_type gamma2 t ty)
  (Hpext: forall p srts a, predsym_in_tm p t -> 
    preds gamma_valid1 pd pf1 p srts a = 
    preds gamma_valid2 pd pf2 p srts a)
  (Hfext: forall f srts a, funsym_in_tm f t ->
    funs gamma_valid1 pd pf1 f srts a = 
    funs gamma_valid2 pd pf2 f srts a),
    term_rep gamma_valid1 pd pdf1 vt pf1 vv t ty Htty1 =
    term_rep gamma_valid2 pd pdf2 vt pf2 vv t ty Htty2
) /\
(forall (vv: val_vars pd vt)
  (Hval1: formula_typed gamma1 f)
  (Hval2: formula_typed gamma2 f)
  (Hpext: forall p srts a, predsym_in_fmla p f -> 
    preds gamma_valid1 pd pf1 p srts a = 
    preds gamma_valid2 pd pf2 p srts a)
  (Hfext: forall fs srts a, funsym_in_fmla fs f ->
    funs gamma_valid1 pd pf1 fs srts a = 
    funs gamma_valid2 pd pf2 fs srts a),
  formula_rep gamma_valid1 pd pdf1 vt pf1 vv f Hval1 =
  formula_rep gamma_valid2 pd pdf2 vt pf2 vv f Hval2).
Proof.
revert t f; apply term_formula_ind; simpl; intros; simpl_rep_full; auto.
- destruct c; simpl_rep_full; f_equal; apply UIP_dec; apply vty_eq_dec.
- f_equal. apply UIP_dec. apply sort_eq_dec.
- (*Tfun*) 
  rewrite Hfext by (destruct (funsym_eq_dec f1 f1); auto). 
  assert ((ty_fun_ind_ret Htty1) = (ty_fun_ind_ret Htty2)).
  { apply UIP_dec. apply vty_eq_dec. }
  rewrite H0; clear H0; f_equal.
  assert ((tfun_params_length Htty1) = (tfun_params_length Htty2)). {
    apply UIP_dec. apply Nat.eq_dec.
  }
  rewrite H0; clear H0; f_equal.
  f_equal.
  apply get_arg_list_ext; auto.
  intros.
  assert (Hith: In (nth i l1 tm_d) l1). {
    apply nth_In; auto.
  }
  revert H.
  rewrite Forall_forall; intros.
  apply H; auto.
  + intros p srts a Hinp.
    apply Hpext. apply existsb_exists.
    exists (nth i l1 tm_d); auto.
  + intros fs srts a Hinfs.
    apply Hfext. bool_to_prop. right.
    exists (nth i l1 tm_d); auto.
- erewrite H. apply H0; auto.
  all: intros; try (apply Hfext); try (apply Hpext); simpl;
  rewrite H1; auto; simpl_bool; auto.
- rewrite (H _ _ (proj2' (proj2' (ty_if_inv Htty2)))),
  (H0 _ _ _ (proj1' (ty_if_inv Htty2))),
  (H1 _ _ _ (proj1' (proj2' (ty_if_inv Htty2)))); auto;
  intros p srts a Hinp; try (apply Hfext); try (apply Hpext);
  simpl; rewrite Hinp; simpl_bool; auto.
- (*match*)
  iter_match_gen Htty1 Htm1 Hpat1 Hty1.
  iter_match_gen Htty2 Htm2 Hpat2 Hty2.
  revert v.
  induction ps; simpl; intros; auto.
  destruct a as [pat1 t1]; simpl.
  rewrite H with(Htty2:=Hty2) at 1.
  + inversion H0; subst.
    rewrite match_val_single_change_gamma with(gamma_valid2:=gamma_valid2)
    (Hval2:=Forall_inv Hpat2)(pdf2:=pdf2); auto. simpl.
    destruct (match_val_single gamma_valid2 pd pdf2 vt v pat1 (Forall_inv Hpat2)
    (term_rep gamma_valid2 pd pdf2 vt pf2 vv tm v Hty2)) eqn : Hm.
    * apply H3; intros; [apply Hpext | apply Hfext]; 
      simpl; rewrite H1; simpl_bool; auto.
    * apply IHps; auto; intros; [apply Hpext | apply Hfext];
      simpl; bool_hyps; destruct H1 as [H1 | H1]; rewrite H1;
      simpl_bool; auto.
  + intros. apply Hpext; simpl; rewrite H1; simpl_bool; auto.
  + intros. apply Hfext; simpl; rewrite H1; simpl_bool; auto.
- f_equal. repeat (apply functional_extensionality_dep; intros).
  replace (proj2' (ty_eps_inv Htty1)) with (proj2' (ty_eps_inv Htty2))
  by (apply UIP_dec; apply vty_eq_dec).
  erewrite H; [reflexivity | |]; intros;
  [apply Hpext | apply Hfext]; auto.
- rewrite Hpext by (destruct (predsym_eq_dec p p); auto). 
  f_equal.
  apply get_arg_list_ext; auto.
  intros.
  assert (Hith: In (nth i tms tm_d) tms). {
    apply nth_In; auto.
  }
  revert H.
  rewrite Forall_forall; intros.
  apply H; auto.
  + intros ps srts a Hinp.
    apply Hpext. bool_to_prop. right.
    exists (nth i tms tm_d); auto.
  + intros fs srts a Hinfs.
    apply Hfext. apply existsb_exists.
    exists (nth i tms tm_d); auto.
- assert (Hd: forall d,
    formula_rep gamma_valid1 pd pdf1 vt pf1 (substi pd vt vv v d) f 
      (typed_quant_inv Hval1) =
    formula_rep gamma_valid2 pd pdf2 vt pf2 (substi pd vt vv v d) f 
      (typed_quant_inv Hval2)).
  {
    intros. apply H; intros; [apply Hpext | apply Hfext]; auto.
  }
  destruct q; simpl_rep_full; apply all_dec_eq; split; 
  try(intros Hall d; specialize (Hall d)); 
  try (intros [d Hall]; exists d);
  try rewrite Hd; auto;
  rewrite <- Hd; auto.
- rewrite (H _ _ _ (proj1' (typed_eq_inv Hval2))),
  (H0 _ _ _ (proj2' (typed_eq_inv Hval2))); auto;
  intros; try apply Hpext; try apply Hfext; rewrite H1; 
  simpl_bool; auto.
- rewrite (H _  _ (proj1' (typed_binop_inv Hval2))),
  (H0 _ _ (proj2' (typed_binop_inv Hval2))); auto;
  intros; try apply Hpext; try apply Hfext; rewrite H1; 
  simpl_bool; auto.
- erewrite H; [reflexivity | |]; intros; [apply Hpext | apply Hfext];
  auto. 
- erewrite H. apply H0; auto.
  all: intros; try (apply Hfext); try (apply Hpext); simpl;
  rewrite H1; auto; simpl_bool; auto.
- rewrite (H _ _ (proj1' (typed_if_inv Hval2))),
  (H0 _ _ (proj1' (proj2' (typed_if_inv Hval2)))),
  (H1 _ _ (proj2' (proj2' (typed_if_inv Hval2)))); auto;
  intros p srts a Hinp; try (apply Hfext); try (apply Hpext);
  simpl; rewrite Hinp; simpl_bool; auto.
- (*match - exactly the same proof*)
  iter_match_gen Hval1 Htm1 Hpat1 Hty1.
  iter_match_gen Hval2 Htm2 Hpat2 Hty2.
  revert v.
  induction ps; simpl; intros; auto.
  destruct a as [pat1 t1]; simpl.
  rewrite H with(Htty2:=Hty2) at 1.
  + inversion H0; subst.
    rewrite match_val_single_change_gamma with(gamma_valid2:=gamma_valid2)
    (Hval2:=Forall_inv Hpat2)(pdf2:=pdf2); auto. simpl.
    destruct (match_val_single gamma_valid2 pd pdf2 vt v pat1 (Forall_inv Hpat2)
    (term_rep gamma_valid2 pd pdf2 vt pf2 vv tm v Hty2)) eqn : Hm.
    * apply H3; intros; [apply Hpext | apply Hfext]; 
      simpl; rewrite H1; simpl_bool; auto.
    * apply IHps; auto; intros; [apply Hpext | apply Hfext];
      simpl; bool_hyps; destruct H1 as [H1 | H1];
      rewrite H1; simpl_bool; auto.
  + intros. apply Hpext; simpl; rewrite H1; simpl_bool; auto.
  + intros. apply Hfext; simpl; rewrite H1; simpl_bool; auto.
Qed.

(*Many useful corollaries from this*)

(*First, change gamma and pf:*)

Definition term_change_gamma_pf {gamma1 gamma2: context}
(gamma_valid1: valid_context gamma1)
(gamma_valid2: valid_context gamma2)
(Hadts: mut_of_context gamma1 = mut_of_context gamma2)
(pd: pi_dom)
(pdf1: pi_dom_full gamma1 pd)
(pdf2: pi_dom_full gamma2 pd)
(pf1: pi_funpred gamma_valid1 pd pdf1)
(pf2: pi_funpred gamma_valid2 pd pdf2)
(t: term)
(ty: vty)
(vt: val_typevar):=
(proj_tm (term_fmla_change_gamma_pf gamma_valid1 gamma_valid2
Hadts pd pdf1 pdf2 pf1 pf2 vt) t) ty.

Definition fmla_change_gamma_pf {gamma1 gamma2: context}
(gamma_valid1: valid_context gamma1)
(gamma_valid2: valid_context gamma2)
(Hadts: mut_of_context gamma1 = mut_of_context gamma2)
(pd: pi_dom)
(pdf1: pi_dom_full gamma1 pd)
(pdf2: pi_dom_full gamma2 pd)
(pf1: pi_funpred gamma_valid1 pd pdf1)
(pf2: pi_funpred gamma_valid2 pd pdf2)
(f: formula)
(vt: val_typevar):=
(proj_fmla (term_fmla_change_gamma_pf gamma_valid1 gamma_valid2
  Hadts pd pdf1 pdf2 pf1 pf2 vt) f).

(*Given a fixed gamma, we can change the pf as long as it
  agrees on all function and predicate symbols in t/f*)
Corollary tm_change_pf {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
  (p1 p2: pi_funpred gamma_valid pd pdf) 
  (vt: val_typevar) (v: val_vars pd vt) 
  (t: term) (ty: vty)
  (Hty: term_has_type gamma t ty)
  (Hpext: forall p srts a, predsym_in_tm p t -> 
    preds gamma_valid pd p1 p srts a = 
    preds gamma_valid pd p2 p srts a)
  (Hfext: forall f srts a, funsym_in_tm f t ->
    funs gamma_valid pd p1 f srts a = 
    funs gamma_valid pd p2 f srts a):
  term_rep gamma_valid pd pdf vt p1 v t ty Hty = 
  term_rep gamma_valid pd pdf vt p2 v t ty Hty.
Proof.
  apply term_change_gamma_pf; auto.
Qed.

Corollary fmla_change_pf {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
  (p1 p2: pi_funpred gamma_valid pd pdf) 
  (vt: val_typevar) (v: val_vars pd vt) 
  (f: formula)
  (Hval: formula_typed gamma f)
  (Hpext: forall p srts a, predsym_in_fmla p f -> 
    preds gamma_valid pd p1 p srts a = 
    preds gamma_valid pd p2 p srts a)
  (Hfext: forall fs srts a, funsym_in_fmla fs f -> 
    funs gamma_valid pd p1 fs srts a = 
    funs gamma_valid pd p2 fs srts a):
  formula_rep gamma_valid pd pdf vt p1 v f Hval = 
  formula_rep gamma_valid pd pdf vt p2 v f Hval.
Proof.
  apply fmla_change_gamma_pf; auto.
Qed.

(*Third, given a fixed gamma and pf, our reps
  are irrelevant in the choice of typing proof
  (this follows from proof irrelevance, but we do
  not use it directly)*)

Corollary term_rep_irrel {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
  (pf: pi_funpred gamma_valid pd pdf)
  (vt: val_typevar) (vv: val_vars pd vt)
  (t: term) (ty: vty) (Hty1 Hty2: term_has_type gamma t ty):
  term_rep gamma_valid pd pdf vt pf vv t ty Hty1 =
  term_rep gamma_valid pd pdf vt pf vv t ty Hty2.
Proof.
  apply term_change_gamma_pf; auto.
Qed.

Corollary fmla_rep_irrel {gamma} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
  (pf: pi_funpred gamma_valid pd pdf)
  (vt: val_typevar) (vv: val_vars pd vt)
  (f: formula) (Hval1 Hval2: formula_typed gamma f):
  formula_rep gamma_valid pd pdf vt pf vv f Hval1 = 
  formula_rep gamma_valid pd pdf vt pf vv f Hval2.
Proof.
  apply fmla_change_gamma_pf; auto.
Qed.

(*Also useful, especially in pattern matching compilation*)
Lemma match_rep_irrel {gamma} (gamma_valid: valid_context gamma) 
  pd pdf pf vt v
   (b1: bool) (ty: gen_type b1) ty1 
  (d: domain (dom_aux pd) (v_subst vt ty1)) pats Hpats1 Hpats2 Hpats3 Hpats4 :

  match_rep gamma_valid pd pdf vt v (term_rep gamma_valid pd pdf vt pf) 
    (formula_rep gamma_valid pd pdf vt pf) b1 ty ty1 d pats Hpats1 Hpats2 =
  match_rep gamma_valid pd pdf vt v (term_rep gamma_valid pd pdf vt pf) 
    (formula_rep gamma_valid pd pdf vt pf) b1 ty ty1 d pats Hpats3 Hpats4.
Proof.
  revert Hpats1 Hpats2 Hpats3 Hpats4. induction pats as [| p ptl IH]; simpl; auto.
  intros. destruct p as [p a]; simpl.
  rewrite match_val_single_irrel with (Hval2:=Forall_inv Hpats3). simpl in *.
  destruct (match_val_single _ _ _ _ _ p (Forall_inv Hpats3) _) eqn : Hmatch; auto.
  destruct b1; auto.
  - apply term_rep_irrel.
  - apply fmla_rep_irrel.
Qed.  

End ChangeContext.

(*Theorems where the context (and pd) is fixed, but neither pf
  not any part of the valuation are fixed*)

Section FixedInterp.

Context {gamma: context} (gamma_valid: valid_context gamma)
  (pd: pi_dom) (pdf: pi_dom_full gamma pd).
Variable (pf: pi_funpred gamma_valid pd pdf).
Notation funs := (funs gamma_valid pd pf).
Notation domain := (domain (dom_aux pd)).
Notation term_rep := (term_rep gamma_valid pd pdf).
Notation formula_rep := (formula_rep gamma_valid pd pdf).
Notation match_val_single := (match_val_single gamma_valid pd pdf).

(*Now we prove an extensionality theorem for
  the valuations: If we have 2 val_typevars
  and val_vars which agree on all type variables and free variables,
  respectively, then the term/formula reps agree.
  This is complicated, because the output depends on vt, so we need
  lots of casts. This makes [match_val_single] especially tricky*)
Section ValExt.

(*Now we need a theorem to tell us what happens if we modify vt, the
  typevar valuation - as long as the two agree on all fvs in the type -
  we get the same result, with a cast
  *)

(*First, a few helper lemmas*)

Lemma vv_cast_tm1 {t: term} {vt1 vt2: val_typevar}
  (vv1: val_vars pd vt1)
  (vv2: val_vars pd vt2)
  (Hvt: forall x, aset_mem x (tm_type_vars t) -> vt1 x = vt2 x)
  {x} (Hinx: aset_mem x (tm_fv t)):
  v_subst vt1 (snd x) = v_subst vt2 (snd x).
Proof.
  apply v_subst_ext.
  intros.
  apply Hvt.
  eapply tm_fv_vars_type_vars. apply Hinx. auto.
Qed.
  
Lemma vv_cast_tm2 {t: term} {vt1 vt2: val_typevar}
  (vv1: val_vars pd vt1)
  (vv2: val_vars pd vt2)
  (Hvt: forall x, aset_mem x (tm_type_vars t) -> vt1 x = vt2 x)
  {x} (Hinx: In x (tm_bnd t)):
  v_subst vt1 (snd x) = v_subst vt2 (snd x).
Proof.
  apply v_subst_ext.
  intros.
  apply Hvt.
  eapply tm_bnd_vars_type_vars. apply Hinx. auto.
Qed.
  
Lemma vv_cast_fmla1 {f: formula} {vt1 vt2: val_typevar}
  (vv1: val_vars pd vt1)
  (vv2: val_vars pd vt2)
  (Hvt: forall x, aset_mem x (fmla_type_vars f) -> vt1 x = vt2 x)
  {x} (Hinx: aset_mem x (fmla_fv f)):
  v_subst vt1 (snd x) = v_subst vt2 (snd x).
Proof.
  apply v_subst_ext.
  intros.
  apply Hvt.
  eapply fmla_fv_vars_type_vars. apply Hinx. auto.
Qed.
    
Lemma vv_cast_fmla2 {f: formula} {vt1 vt2: val_typevar}
  (vv1: val_vars pd vt1)
  (vv2: val_vars pd vt2)
  (Hvt: forall x, aset_mem x (fmla_type_vars f) -> vt1 x = vt2 x)
  {x} (Hinx: In x (fmla_bnd f)):
  v_subst vt1 (snd x) = v_subst vt2 (snd x).
Proof.
  apply v_subst_ext.
  intros.
  apply Hvt.
  eapply fmla_bnd_vars_type_vars. apply Hinx. auto.
Qed.

(*Cast funs and preds*)
Lemma funs_cast_eq f {s1 s2: list sort} (Heq: s1 = s2)
  a:
  dom_cast (dom_aux pd) (f_equal (funsym_sigma_ret f) Heq)
  (funs f s1 a) =
  funs f s2 (cast_arg_list (f_equal (sym_sigma_args f) Heq) a).
Proof.
  subst. unfold dom_cast, cast_arg_list. simpl. reflexivity.
Qed.

Lemma preds_cast_eq p {s1 s2: list sort} (Heq: s1 = s2)
  a:
  preds gamma_valid pd pf p s1 a =
  preds gamma_valid pd pf p s2 (cast_arg_list (f_equal (sym_sigma_args p) Heq) a).
Proof.
  subst. reflexivity. 
Qed.

(*Lemma for [get_arg_list] - this is a different extensionality lemma
  than above (particularly with how reps are handled).
  This allows us to modify the val_typevar, val_vars, 
  reps, and proofs.*)

Lemma get_arg_list_vt_ext
(vt1 vt2: val_typevar)
  (vs1 vs2: list vty) (ts1 ts2: list term) vv1 vv2
  (reps1 reps2: forall (vt: val_typevar) (pf: pi_funpred gamma_valid pd pdf) 
    (vv: val_vars pd vt)
    (t: term) (ty: vty) (Hty: term_has_type gamma t ty),
    domain (v_subst vt ty))
  (Hts: length ts1 = length ts2)
  (Hreps: forall (i: nat),
    (i < length ts1) ->
    forall (ty1 ty2: vty) Hty1 Hty2 Heq,
      dom_cast (dom_aux pd) Heq 
        (reps1 vt1 pf vv1 (List.nth i ts1 tm_d) ty1 Hty1) =
      reps2 vt2 pf vv2 (List.nth i ts2 tm_d) ty2 Hty2)
  {args: list vty}
  {params: list typevar}
  (Hp: NoDup params)
  (Hlents1: length ts1 = length args)
  (Hlents2: length ts2 = length args)
  (Hlenvs1: length vs1 = length params)
  (Hlenvs2: length vs2 = length params)
  (Hall1: Forall (fun x => term_has_type gamma (fst x) (snd x))
    (combine ts1 (map (ty_subst params vs1) args)))
  (Hall2: Forall (fun x => term_has_type gamma (fst x) (snd x))
    (combine ts2 (map (ty_subst params vs2) args)))
  (Heq: map (v_subst vt1) vs1 = map (v_subst vt2) vs2):
  cast_arg_list 
    (f_equal (fun x => ty_subst_list_s params x args) Heq)
    (get_arg_list pd vt1 vs1 ts1 (reps1 vt1 pf vv1) Hp Hlents1 Hlenvs1 Hall1) =
  get_arg_list pd vt2 vs2 ts2 (reps2 vt2 pf vv2) Hp Hlents2 Hlenvs2 Hall2.
Proof.
  match goal with
  | |- cast_arg_list ?H ?a = _ => generalize dependent H end.
  clear Heq.
  unfold get_arg_list.
  generalize dependent args.
  generalize dependent ts2. 
  induction ts1; simpl; intros. 
  - destruct ts2; [|subst; inversion Hts].
    destruct args; simpl; auto; [|inversion Hlents1].
    assert (e = Logic.eq_refl). apply UIP_dec. apply list_eq_dec.
    apply sort_eq_dec. 
    subst. reflexivity.
  - destruct ts2; inversion Hts.
    destruct args.
    + inversion Hlents2.
    + simpl in Hlenvs2. simpl.
      simpl in e.
      rewrite (cast_arg_list_cons e).
      f_equal.
      * rewrite -> rewrite_dom_cast, !dom_cast_compose.
        assert (Heq': v_subst vt1 (ty_subst params vs1 v) = v_subst vt2 (ty_subst params vs2 v)). {
          rewrite !funsym_subst_eq; auto.
          apply (cons_inj_hd e).
        }
        erewrite <- (Hreps 0) with(Hty1:=Forall_inv Hall1)(Heq:=Heq'); try lia.
        rewrite !dom_cast_compose. apply dom_cast_eq.
      * apply IHts1; auto.
        intros i Hi ty Hty1 Hty2 Heq.
        apply (Hreps (S i) (ltac:(lia))).
Qed.

(*A specialized version of the above without quite as much
  extensionality in the proofs and with a more convenient 
  Hreps*)
Lemma get_arg_list_vt_eq (vt1 vt2: val_typevar) (s: fpsym)
  (vs: list vty) (ts: list term) vv1 vv2
  (reps: forall (vt: val_typevar) (pf: pi_funpred gamma_valid pd pdf) 
    (vv: val_vars pd vt)
    (t: term) (ty: vty) (Hty: term_has_type gamma t ty),
    domain (v_subst vt ty))
  (Hreps: Forall
    (fun tm : term =>
      forall (ty: vty) (Hty1 Hty2: term_has_type gamma tm ty) 
        (Heq: v_subst vt2 ty = v_subst vt1 ty),
        reps vt1 pf vv1 tm ty Hty1 =
        dom_cast (dom_aux pd) Heq (reps vt2 pf vv2 tm ty Hty2)
      ) ts)
  Hp Hlents Hlenvs Hall
  (Heq: map (v_subst vt2) vs = map (v_subst vt1) vs):
  cast_arg_list (f_equal (sym_sigma_args s) (eq_sym Heq))
    (get_arg_list pd vt1 vs ts (reps vt1 pf vv1) Hp Hlents Hlenvs Hall) =
  get_arg_list pd vt2 vs ts (reps vt2 pf vv2) Hp Hlents Hlenvs Hall.
Proof.
  apply get_arg_list_vt_ext; auto. 
  rewrite Forall_forall in Hreps.
  intros.
  symmetry.
  assert (ty1 = ty2). {
    apply (term_has_type_unique _ _ _ _ Hty1 Hty2).
  }
  subst.
  rewrite Hreps with(Heq:=eq_sym Heq0)(Hty2:=Hty2).
  rewrite !dom_cast_twice. reflexivity.
  apply nth_In. auto.
Qed. 
  
(*We proved the [match_val_single] result about, so we can
  prove the theorem. This is complicated
  due to all the casting*)
Theorem tm_fmla_change_vt (t: term) (f: formula):
  (forall (vt1 vt2: val_typevar) (vv1: val_vars pd vt1)
    (vv2: val_vars pd vt2)
    (Hvt: forall x, aset_mem x (tm_type_vars t) -> vt1 x = vt2 x)
    (Hvv: forall x (Hinx: aset_mem x (tm_fv t)) 
      (*NOTE: can use (vv_cast_tm1) for cast, but easier to prove
        more general*)                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             
      (Heq: v_subst vt1 (snd x) = v_subst vt2 (snd x)), vv2 x = 
      (dom_cast (dom_aux pd) Heq (vv1 x)))
    (ty: vty)
    (Hty: term_has_type gamma t ty)
    (Heq: v_subst vt2 ty = v_subst vt1 ty),
    term_rep vt1 pf vv1 t ty Hty =
    dom_cast (dom_aux pd) Heq 
      (term_rep vt2 pf vv2 t ty Hty)) /\
  (forall (vt1 vt2: val_typevar) (vv1: val_vars pd vt1)
    (vv2: val_vars pd vt2)
    (Hvt: forall x, aset_mem x (fmla_type_vars f) -> vt1 x = vt2 x)
    (Hvv: forall x (Hinx: aset_mem x (fmla_fv f))
      (Heq: v_subst vt1 (snd x) = v_subst vt2 (snd x)), vv2 x = 
      (dom_cast (dom_aux pd) Heq (vv1 x)))
    (Hval: formula_typed gamma f),
    formula_rep vt1 pf vv1 f Hval =
    formula_rep vt2 pf vv2 f Hval).
Proof.
  revert t f. apply term_formula_ind; intros; simpl; simpl_rep_full.
  - destruct c; simpl; simpl_rep_full;
    inversion Hty; subst; simpl in Heq. 
    + unfold cast_dom_vty.
      generalize dependent ((eq_sym (ty_constint_inv Hty))); intros.
      assert (e = eq_refl). apply UIP_dec. apply vty_eq_dec.
      subst. simpl. unfold dom_cast; simpl.
      assert ((f_equal domain Heq) = eq_refl). {
        (*NOTE: relies on UIP*)
        apply UIP.
      }
      rewrite H. reflexivity.
    + unfold cast_dom_vty. 
      generalize dependent (eq_sym (ty_constreal_inv Hty)); intros.
      assert (e = eq_refl). apply UIP_dec. apply vty_eq_dec.
      subst. simpl. unfold dom_cast; simpl.
      assert ((f_equal domain Heq) = eq_refl). {
        (*NOTE: relies on UIP*)
        apply UIP.
      }
      rewrite H. reflexivity.
  - (*Variable case - more casting*)
    unfold var_to_dom.
    inversion Hty; subst.
    rewrite Hvv with(Heq:= eq_sym Heq); simpl; auto.
    rewrite !dom_cast_compose. apply dom_cast_eq. 
    simpl_set. auto.
  - (*Function case - hard because of casting already and
    need nested inductive lemma for get_arg_list*)
    unfold cast_dom_vty. rewrite !dom_cast_compose.
    assert (Hmap: map (v_subst vt2) l = map (v_subst vt1) l). {
      apply list_eq_ext'; rewrite !length_map; auto.
      intros n d Hn.
      rewrite !(map_nth_inbound) with(d2:=vty_int); auto.
      apply v_subst_ext. intros.
      symmetry.
      apply Hvt. simpl.
      simpl_set. left. exists (nth n l vty_int). split; auto.
      apply nth_In; auto.
    }
    assert (Hargs: 
    (cast_arg_list (f_equal (sym_sigma_args f1) (eq_sym Hmap)) 
      (fun_arg_list pd vt1 f1 l l1 (term_rep vt1 pf vv1) Hty)) =
    
      (fun_arg_list pd vt2 f1 l l1 (term_rep vt2 pf vv2) Hty)). {
      unfold fun_arg_list.
      apply get_arg_list_vt_eq.
      revert H.
      rewrite !Forall_forall; intros.
      assert (Hvt': forall x0 : typevar, aset_mem x0 (tm_type_vars x) -> vt1 x0 = vt2 x0). {
        intros. apply Hvt. simpl. simpl_set. right. exists x. auto.
      }
      rewrite term_rep_irrel with (Hty1:=Hty1)(Hty2:=Hty2).
      apply (H _ H0 _ _ _ _ Hvt').
      intros.
      assert (Hinx': aset_mem x0 (tm_fv (Tfun f1 l l1))). {
        simpl. simpl_set. exists x. auto.
      }
      intros. apply Hvv with(Heq:=Heq1); auto. 
    }
    rewrite <- Hargs.
    assert (Hfuns: 
    (funs f1 (map (v_subst vt2) l)
    (cast_arg_list (f_equal (sym_sigma_args f1) (eq_sym Hmap))
        (fun_arg_list pd vt1 f1 l l1 (term_rep vt1 pf vv1) Hty))) =
    dom_cast (dom_aux pd) (f_equal (funsym_sigma_ret f1) (eq_sym Hmap))
    (funs f1 (map (v_subst vt1) l)
    (fun_arg_list pd vt1 f1 l l1 (term_rep vt1 pf vv1) Hty))
    ).
    { rewrite funs_cast_eq. reflexivity.
    }
    rewrite Hfuns.
    rewrite !dom_cast_compose. f_equal. apply UIP_dec. apply sort_eq_dec.
  - (*Tlet case*)
    assert (Heq1: v_subst vt2 (snd v) = v_subst vt1 (snd v)). {
      eapply (@vv_cast_tm2 (Tlet tm1 v tm2) _ _ vv2 vv1); simpl; auto.
      intros; symmetry; apply Hvt; auto.
    }
    rewrite H with (vv2:=vv2)(Heq:=Heq1); intros;
    [| apply Hvt | apply Hvv]; simpl; simpl_set; auto.
    (*Now the outer term_rep*)
    apply H0; intros; [apply Hvt |]; simpl; simpl_set; auto.
    (*Now have to show vv condition*)
    unfold substi. destruct (vsymbol_eq_dec x v); subst; simpl.
    + unfold eq_rec_r, eq_rec, eq_rect. simpl.
      rewrite !dom_cast_compose.
      rewrite dom_cast_refl. reflexivity.
    + apply Hvv. simpl; simpl_set; auto. 
  - (*Tif case*)
    rewrite (H vt1 vt2 vv1 vv2),
    (H0 vt1 vt2 vv1 vv2) with(Heq:=Heq),
    (H1 vt1 vt2 vv1 vv2) with(Heq:=Heq); intros;
    try(apply Hvt); try (apply Hvv); simpl; simpl_set; auto.
    (*Now we show that these casts are OK*)
    destruct (formula_rep vt2 pf vv2 f (proj2' (proj2' (ty_if_inv Hty)))); auto.
  - (*Tmatch*)
    iter_match_gen Hty Htm Hpat Hty.
    induction ps; simpl; auto; intros.
    { (*A trivial case*)
      generalize dependent (v_subst vt1 ty).
      intros. subst. reflexivity.
    } 
    destruct a.
    inversion H0; subst.
    (*First step: handle term_rep in case*)
    assert (Heq1: v_subst vt2 v = v_subst vt1 v). {
      apply v_subst_ext.
      intros. symmetry. apply Hvt. simpl. simpl_set; auto.
    }
    erewrite (H vt1 vt2 vv1 vv2) with (Heq:=Heq1); intros;
    [| apply Hvt | apply Hvv]; try(simpl; simpl_set; auto).
    pose proof (match_val_single_change_vt gamma_valid pd pdf vt1 vt2
      v Heq1 p (Forall_inv Hpat) (term_rep vt2 pf vv2 tm v Hty)) as Hopt.
    revert Hopt.
    destruct_match_single l1 Hmatch1;
    destruct_match_single l2 Hmatch2; auto; try contradiction.
    2: {
      (*None case*)
      intros _. 
      assert (Hvt1: (forall x : typevar, aset_mem x (tm_type_vars (Tmatch tm v ps)) -> vt1 x = vt2 x)). {
        simpl. intros; apply Hvt; simpl; repeat(simpl_set_small; destruct_all; auto).
      }
      assert (Hvv1: (forall x : vsymbol,
      aset_mem x (tm_fv (Tmatch tm v ps)) ->
      forall Heq : v_subst vt1 (snd x) = v_subst vt2 (snd x),
      vv2 x = dom_cast (dom_aux pd) Heq (vv1 x))). {
        simpl. intros; apply Hvv. simpl.
        repeat(simpl_set_small; destruct_all); auto.
      }
      rewrite <- (H vt1 vt2 vv1 vv2) with (Heq:=Heq1); intros;
      [| apply Hvt | apply Hvv]; try(simpl; simpl_set; auto).
    }
    + (*Some case*) intros Hsome.
      apply H3; [intros; apply Hvt; simpl; simpl_set; auto|].
      intros x Hinx Heq'.
      destruct (aset_mem_dec x (pat_fv p)).
      2: {
        (*Not in: follows from Hvv*)
        rewrite !extend_val_notin; auto.
        - erewrite Hvv. reflexivity.
          simpl. simpl_set; auto.
        - assert (Hnotin: ~ aset_mem x (keys l1)). {
            erewrite (match_val_single_fv gamma_valid pd pdf); eauto.
          }
          rewrite<- amap_mem_keys in Hnotin.
          destruct (amap_mem x l1); auto; exfalso; apply Hnotin; auto.
        - assert (Hnotin: ~ aset_mem x (keys l2)). {
            erewrite (match_val_single_fv gamma_valid pd pdf); eauto.
          }
          rewrite<- amap_mem_keys in Hnotin.
          destruct (amap_mem x l2); auto; exfalso; apply Hnotin; auto.
      }
      assert (Hinl2: aset_mem x (keys l2)). {
        erewrite (match_val_single_fv gamma_valid pd pdf); eauto. 
      }
      rewrite <- amap_mem_keys in Hinl2.
      unfold amap_mem in Hinl2.
      destruct (amap_lookup l2 x) as [y|] eqn : Hget; try discriminate.
      rewrite extend_val_lookup with (t:=y) by auto.
      destruct (Hsome _ _ Hget) as [z [Hz1 [Hinz Hz2]]].
      rewrite extend_val_lookup with(t:=z); auto.
      assert (projT1 y = v_subst vt2 (snd x)). {
        eapply match_val_single_typs.
        apply Hmatch2. auto.
      }
      assert (projT1 z = v_subst vt1 (snd x)). {
        eapply match_val_single_typs.
        apply Hmatch1. auto.
      }
      destruct (sort_eq_dec (v_subst vt2 (snd x)) (projT1 y) ); auto. 
      2: { exfalso. apply n; auto. }
      destruct (sort_eq_dec (v_subst vt1 (snd x)) (projT1 z)); auto.
      2: { exfalso. apply n; auto. }
      (*Coq cannot rewrite for some reason*)
      simpl.
      clear -Hz2.
      (*Need eta-equivalence*)
      change (fun s => Domain.domain (dom_aux pd) s) with (Domain.domain (dom_aux pd)).
      rewrite Hz2.
      rewrite !dom_cast_compose.
      apply dom_cast_eq.
  - (*epsilon case*)
    (*First, cast inhabited*)
    assert (match domain_ne pd (v_subst vt2 ty) with
    | @DE _ _ x => x
    end = dom_cast (dom_aux pd) (eq_sym Heq) (match domain_ne pd (v_subst vt1 ty) with
    | @DE _ _ x => x
    end)). {
      generalize dependent (v_subst vt2 ty); intros; subst.
      unfold dom_cast; reflexivity.
    }
    generalize dependent (match domain_ne pd (v_subst vt2 ty) with
    | @DE _ _ x => x
    end).
    generalize dependent (match domain_ne pd (v_subst vt1 ty) with
    | @DE _ _ x => x
    end).
    intros i1 i2 Hi; subst.
    (*We need to "cast" the function*)
    match goal with
    | |- epsilon ?i1 ?f = dom_cast ?d ?Heq (epsilon ?i2 ?g) => 
      let H := fresh in
      assert (H: g = (fun (z: domain (v_subst vt2 ty)) =>
        f (dom_cast (dom_aux pd) Heq z))); [| generalize dependent f;
        intros; rewrite H]
    end.
    {
      apply functional_extensionality_dep; intros.
      rewrite !dom_cast_compose. symmetry. erewrite H.
      reflexivity.
      intros. apply Hvt. simpl. simpl_set; auto.
      intros. unfold substi. destruct (vsymbol_eq_dec x0 v); subst.
      - unfold eq_rec_r, eq_rec, eq_rect; simpl.
        rewrite !dom_cast_compose. apply dom_cast_eq.
      - inversion Hty; subst. rewrite Hvv with(Heq:=Heq0); simpl; [|simpl_set; auto].
        reflexivity.
    }
    clear H0.
    (*Now, we can generalize*)
    generalize dependent (v_subst vt2 ty); intros; subst; 
    unfold dom_cast; simpl.
    reflexivity.
  - (*Preds case*)
    assert (Hmap: map (v_subst vt2) tys = map (v_subst vt1) tys). {
      apply list_eq_ext'; rewrite !length_map; auto.
      intros n d Hn.
      rewrite !(map_nth_inbound) with(d2:=vty_int); auto.
      apply v_subst_ext. intros.
      symmetry.
      apply Hvt. simpl.
      simpl_set. left. exists (nth n tys vty_int). split; auto.
      apply nth_In; auto.
    }
    assert (Hargs: 
    (cast_arg_list (f_equal (sym_sigma_args p) (eq_sym Hmap)) 
      (pred_arg_list pd vt1 p tys tms (term_rep vt1 pf vv1) Hval)) =
    
    (pred_arg_list pd vt2 p tys tms (term_rep vt2 pf vv2) Hval)). {
      unfold pred_arg_list.
      apply get_arg_list_vt_eq.
      revert H.
      rewrite !Forall_forall; intros.
      assert (Hvt': forall x0 : typevar, aset_mem x0 (tm_type_vars x) -> vt1 x0 = vt2 x0). {
        intros. apply Hvt. simpl. simpl_set. right. exists x. auto.
      }
      rewrite term_rep_irrel with (Hty2:=Hty2).
      apply (H _ H0 _ _ _ _ Hvt').
      intros.
      assert (Hinx': aset_mem x0 (fmla_fv (Fpred p tys tms))). {
        simpl. simpl_set. exists x. auto.
      }
      intros. apply Hvv with(Heq:=Heq0); auto. 
    }
    rewrite <- Hargs.
    apply preds_cast_eq.
  - (*Fquant*)
    assert (Heq: v_subst vt1 (snd v) = v_subst vt2 (snd v)). {
      apply v_subst_ext.
      intros.
      apply Hvt. simpl. simpl_set. left. auto.
    }
    assert (forall d1 d2,
      d1 = dom_cast (dom_aux pd) (eq_sym Heq) d2 ->
      formula_rep vt1 pf (substi pd vt1 vv1 v d1) f
      (typed_quant_inv Hval) =
      formula_rep vt2 pf (substi pd vt2 vv2 v d2) f
      (typed_quant_inv Hval)).
    {
      intros; subst. apply H; intros.
      - apply Hvt. simpl. simpl_set; auto.
      - unfold substi. destruct (vsymbol_eq_dec x v); subst.
        + simpl. rewrite dom_cast_compose.
          rewrite dom_cast_refl. reflexivity.
        + rewrite Hvv with(Heq:= Heq0); simpl; auto. simpl_set; auto.
    }
    destruct q; simpl_rep_full;
    apply all_dec_eq; split; intros.
    + erewrite <- H0. apply H1. reflexivity.
    + erewrite H0. apply H1.
      Unshelve.
      2: exact (dom_cast (dom_aux pd) Heq d).
      rewrite dom_cast_compose.
      rewrite dom_cast_refl. reflexivity.
    + destruct H1 as [d Hd].
      exists (dom_cast (dom_aux pd) Heq d).
      erewrite <- H0. apply Hd.
      rewrite dom_cast_compose, dom_cast_refl; reflexivity.
    + destruct H1 as [d Hd].
      exists (dom_cast (dom_aux pd) (eq_sym Heq) d).
      erewrite H0. apply Hd.
      reflexivity.
  - (*Feq*) 
    assert (Heq: v_subst vt2 v = v_subst vt1 v). {
      apply v_subst_ext. intros. symmetry. apply Hvt.
      simpl. simpl_set; auto.
    }
    rewrite H with (vt2:=vt2)(vv2:=vv2) (Heq:=Heq),
    H0 with (vt2:=vt2)(vv2:=vv2) (Heq:=Heq); intros;
    [| apply Hvt | apply Hvv | apply Hvt | apply Hvv]; 
    simpl; simpl_set; auto.
    apply all_dec_eq; split; intros.
    apply dom_cast_inj in H1. auto.
    rewrite H1. reflexivity.
  - (*Fbinop*)
    rewrite (H _ vt2 _ vv2), (H0 _ vt2 _ vv2); intros;
    [| apply Hvt | apply Hvv | apply Hvt | apply Hvv]; 
    simpl; simpl_set; auto.
  - (*Fnot*)
    rewrite (H _ vt2 _ vv2); auto.
  - auto.
  - auto.
  - (*Flet*)
    assert (Heq1: v_subst vt2 (snd v) = v_subst vt1 (snd v)). {
      eapply (@vv_cast_fmla2 (Flet tm v f) _ _ vv2 vv1); simpl; auto. 
      intros; symmetry; apply Hvt; auto.
    }
    rewrite H with (vv2:=vv2)(Heq:=Heq1); intros;
    [| apply Hvt | apply Hvv]; simpl; simpl_set; auto.
    (*Now the outer term_rep*)
    apply H0; intros; [apply Hvt |]; simpl; simpl_set; auto.
    (*Now have to show vv condition*)
    unfold substi. destruct (vsymbol_eq_dec x v); subst; simpl.
    + unfold eq_rec_r, eq_rec, eq_rect. simpl.
      rewrite !dom_cast_compose.
      rewrite dom_cast_refl. reflexivity.
    + apply Hvv. simpl; simpl_set; auto.
  - (*Fif*)
    rewrite (H vt1 vt2 vv1 vv2), (H0 vt1 vt2 vv1 vv2),
    (H1 vt1 vt2 vv1 vv2); intros;
    try(apply Hvt); try (apply Hvv); simpl; simpl_set; auto.
  - (*Fmatch - basically identical to Tmatch*)
    iter_match_gen Hval Htm Hpat Hty.
    induction ps; simpl; auto; intros.
    destruct a.
    inversion H0; subst.
    (*First step: handle term_rep in case*)
    assert (Heq1: v_subst vt2 v = v_subst vt1 v). {
      apply v_subst_ext.
      intros. symmetry. apply Hvt. simpl. simpl_set; auto.
    }
    erewrite (H vt1 vt2 vv1 vv2) with (Heq:=Heq1); intros;
    [| apply Hvt | apply Hvv]; try(simpl; simpl_set; auto).
    pose proof (match_val_single_change_vt gamma_valid pd pdf vt1 vt2
      v Heq1 p (Forall_inv Hpat) (term_rep vt2 pf vv2 tm v Hty)) as Hopt.
    revert Hopt.
    destruct_match_single l1 Hmatch1;
    destruct_match_single l2 Hmatch2; auto; try contradiction.
    2: {
      (*None case*)
      intros _. 
      assert (Hvt1: (forall x : typevar, 
        aset_mem x (fmla_type_vars (Fmatch tm v ps)) -> vt1 x = vt2 x)). {
        simpl. intros; apply Hvt; simpl; repeat(simpl_set_small; destruct_all; auto).
      }
      assert (Hvv1: (forall x : vsymbol,
      aset_mem x (fmla_fv (Fmatch tm v ps)) ->
      forall Heq : v_subst vt1 (snd x) = v_subst vt2 (snd x),
      vv2 x = dom_cast (dom_aux pd) Heq (vv1 x))). {
        simpl. intros; apply Hvv. simpl.
        repeat(simpl_set_small; destruct_all); auto.
      }
      rewrite <- (H vt1 vt2 vv1 vv2) with (Heq:=Heq1); intros;
      [| apply Hvt | apply Hvv]; try(simpl; simpl_set; auto).
    }
    + (*Some case*) intros Hsome.
      apply H3; [intros; apply Hvt; simpl; simpl_set; auto|].
      intros x Hinx Heq'.
      destruct (aset_mem_dec x (pat_fv p)).
      2: {
        (*Not in: follows from Hvv*)
        rewrite !extend_val_notin; auto.
        - erewrite Hvv. reflexivity.
          simpl. simpl_set; auto.
        - assert (Hnotin: ~ aset_mem x (keys l1)). {
            erewrite (match_val_single_fv gamma_valid pd pdf); eauto.
          }
          rewrite<- amap_mem_keys in Hnotin.
          destruct (amap_mem x l1); auto; exfalso; apply Hnotin; auto.
        - assert (Hnotin: ~ aset_mem x (keys l2)). {
            erewrite (match_val_single_fv gamma_valid pd pdf); eauto.
          }
          rewrite<- amap_mem_keys in Hnotin.
          destruct (amap_mem x l2); auto; exfalso; apply Hnotin; auto.
      }
      assert (Hinl2: aset_mem x (keys l2)). {
        erewrite (match_val_single_fv gamma_valid pd pdf); eauto. 
      }
      rewrite <- amap_mem_keys in Hinl2.
      unfold amap_mem in Hinl2.
      destruct (amap_lookup l2 x) as [y|] eqn : Hget; try discriminate.
      rewrite extend_val_lookup with (t:=y) by auto.
      destruct (Hsome _ _ Hget) as [z [Hz1 [Hinz Hz2]]].
      rewrite extend_val_lookup with(t:=z); auto.
      assert (projT1 y = v_subst vt2 (snd x)). {
        eapply match_val_single_typs.
        apply Hmatch2. auto.
      }
      assert (projT1 z = v_subst vt1 (snd x)). {
        eapply match_val_single_typs.
        apply Hmatch1. auto.
      }
      destruct (sort_eq_dec (v_subst vt2 (snd x)) (projT1 y) ); auto. 
      2: { exfalso. apply n; auto. }
      destruct (sort_eq_dec (v_subst vt1 (snd x)) (projT1 z)); auto.
      2: { exfalso. apply n; auto. }
      (*Coq cannot rewrite for some reason*)
      simpl.
      clear -Hz2.
      (*Need eta-equivalence*)
      change (fun s => Domain.domain (dom_aux pd) s) with (Domain.domain (dom_aux pd)).
      rewrite Hz2.
      rewrite !dom_cast_compose.
      apply dom_cast_eq.
Qed.

Definition tm_change_vt t := proj_tm tm_fmla_change_vt t.
Definition fmla_change_vt f := proj_fmla tm_fmla_change_vt f.

End ValExt.
  
Section ValExtCor.

(*From this, we have several corollaries, for which we fix the
  val_typevar*)
Variable vt: val_typevar.

(* A term/formula is interpreted the
  same on all valuations that agree on the free variables *)
Corollary tm_change_vv (t: term) :
(forall (v1 v2: val_vars pd vt) (ty: vty) 
  (Hty: term_has_type gamma t ty),
  (forall x, aset_mem x (tm_fv t) -> v1 x = v2 x) ->
  term_rep vt pf v1 t ty Hty = term_rep vt pf v2 t ty Hty).
Proof.
  intros.
  rewrite tm_change_vt with(vt2:=vt)(vv2:=v2)(Heq:=eq_refl); auto.
  intros. assert (Heq = eq_refl). apply UIP_dec. apply sort_eq_dec.
  rewrite H, H0; auto.
Qed.

Corollary fmla_change_vv f:
(forall (v1 v2: val_vars pd vt) 
  (Hval: formula_typed gamma f),
  (forall x, aset_mem x (fmla_fv f) -> v1 x = v2 x) ->
  formula_rep vt pf v1 f Hval = formula_rep vt pf v2 f Hval).
Proof.
  intros.
  apply (fmla_change_vt) with(vt2:=vt) (vv2:=v2); auto.
  intros.
  assert (Heq=eq_refl) by (apply UIP_dec; apply sort_eq_dec).
  rewrite H, H0; auto.
Qed.

(*The interpretation of any 
  closed term is equivalent under any valuation*)
Corollary term_closed_val (t: term)
  (v1 v2: val_vars pd vt) (ty: vty)
  (Hty: term_has_type gamma t ty):
  closed_term t ->
  term_rep vt pf v1 t ty Hty = term_rep vt pf v2 t ty Hty.
Proof.
  unfold closed_term. intros.
  apply tm_change_vv; intros.
  exfalso; eapply aset_is_empty_mem; eauto.
Qed.

Corollary fmla_closed_val (f: formula)
  (v1 v2: val_vars pd vt) 
  (Hval: formula_typed gamma f):
  closed_formula f ->
  formula_rep vt pf v1 f Hval = formula_rep vt pf v2 f Hval.
Proof.
  unfold closed_formula; intros.
  apply fmla_change_vv; intros.
  exfalso; eapply aset_is_empty_mem; eauto.
Qed.

End ValExtCor.
End FixedInterp.
End Theorems.

(*[gen] versions*)
Section Gen.

Context {gamma: context} (gamma_valid: valid_context gamma).
Context (pd: pi_dom) (pdf: pi_dom_full gamma pd) 
  (pf: pi_funpred gamma_valid pd pdf) (vt: val_typevar).

Context {b: bool}.
(* Variable (v: val_vars pd vt). *)

Definition gen_rep (v: val_vars pd vt) (ty: gen_type b) (d: gen_term b) (Hty: gen_typed gamma b d ty) : gen_ret pd vt b ty :=
  match b return forall (ty: gen_type b) (dat: gen_term b), 
    gen_typed gamma b dat ty -> gen_ret pd vt b ty with
  | true => fun ty dat Hty => term_rep gamma_valid pd pdf vt pf v dat ty Hty
  | false => fun ty dat Hty => formula_rep gamma_valid pd pdf vt pf v dat Hty
  end ty d Hty.

Lemma gen_rep_change_vv v1 v2 ty t Hty:
  (forall x, aset_mem x (gen_fv t) -> v1 x = v2 x) ->
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

Lemma gen_rep_let vv (ty2: gen_type b) (x: vsymbol) (t: term) (a: gen_term b) Hty1 Hty2 Hty3:
  gen_rep vv ty2 (gen_let x t a) Hty2 =
  gen_rep (substi pd vt vv x (term_rep gamma_valid pd pdf vt pf vv t (snd x) Hty1)) ty2 a Hty3.
Proof.
  revert ty2 a Hty2 Hty3.
  unfold gen_let, gen_rep.
  destruct b; simpl; intros; simpl_rep; simpl;
  rewrite term_rep_irrel with (Hty2:=Hty1);
  [apply term_rep_irrel | apply fmla_rep_irrel].
Qed.

Lemma gen_match_rep v (ty: gen_type b) (t: term) (ty1: vty) (pats: list (pattern * gen_term b)) 
  (Hty: gen_typed gamma b (gen_match t ty1 pats) ty) 
  (Hty1: term_has_type gamma t ty1)
  (Hpats1: Forall (fun x => pattern_has_type gamma (fst x) ty1) pats)
  (Hpats2: Forall (fun x => gen_typed gamma b (snd x) ty) pats):
  gen_rep v ty (gen_match t ty1 pats) Hty =
  match_rep gamma_valid pd pdf vt v (term_rep gamma_valid pd pdf vt pf) (formula_rep gamma_valid pd pdf vt pf)
    b ty ty1 (term_rep gamma_valid pd pdf vt pf v t ty1 Hty1) pats Hpats1 Hpats2.
Proof.
  revert Hty.
  unfold gen_match, gen_rep. destruct b; simpl in *; auto; intros;
  simp term_rep; simpl; erewrite term_rep_irrel with (Hty2:=Hty1); erewrite match_rep_irrel;
    reflexivity.
Qed.

End Gen.