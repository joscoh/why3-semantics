Require Import Task.
Require Import Alpha GenElts.
Require Import eliminate_inductive. (*TODO: not great, factor out common stuff*)
Require Import PatternProofs. (*TODO: factor out gen stuff*)
Require Import Denotational2.
Set Bullet Behavior "Strict Subproofs".

(*TODO: really make [gen] versions more extensive and organized*)

Section Gen.
Definition gen_sym (b: bool) : Set := if b then funsym else predsym.

Definition gen_sym_name {b: bool} (f: gen_sym b) : string :=
  match b return gen_sym b -> string with
  | true => fun f => s_name f
  | false => fun f => s_name f
  end f.

Definition gen_sym_params {b: bool} (f: gen_sym b) : list typevar :=
  match b return gen_sym b -> list typevar with
  | true => s_params
  | false => s_params
  end f.

Definition gen_funpred_def (b: bool) (f: gen_sym b) (l: list vsymbol) (t: gen_term b) : funpred_def :=
  match b return gen_sym b -> gen_term b -> funpred_def with
  | true => fun ls t => fun_def ls l t
  | false => fun ls f => pred_def ls l f
  end f t.

Definition gen_funpred_def_match (x: funpred_def) : {b: bool & (gen_sym b * list vsymbol * gen_term b)%type} :=
  match x with
  | fun_def ls vs t => existT _ true (ls, vs, t)
  | pred_def ls vs f => existT _ false (ls, vs, f)
  end.

(*Common features: let, match, app (fun or predsym), if*)
Definition gen_app (b: bool) (f: gen_sym b) (tys: list vty) (tms: list term) : gen_term b :=
  match b return gen_sym b -> gen_term b with
  | true => fun f => Tfun f tys tms
  | false => fun p => Fpred p tys tms
  end f.

Definition gen_if (b: bool) (f: formula) (t1 t2: gen_term b) : gen_term b :=
  match b return gen_term b -> gen_term b -> gen_term b with
  | true => fun t1 t2 => Tif f t1 t2
  | false => fun f1 f2 => Fif f f1 f2
  end t1 t2.

(*Generalized equality (Teq or Fiff)*)
Definition gen_eq (b: bool) (ty: gen_type b) (t1 t2: gen_term b) : formula :=
  match b return gen_type b -> gen_term b -> gen_term b -> formula with
  | true => fun ty t1 t2 => Feq ty t1 t2
  | false => fun _ f1 f2 => Fbinop Tiff f1 f2
  end ty t1 t2.

Definition gen_sym_ret {b: bool} (f: gen_sym b) : gen_type b :=
  match b return gen_sym b -> gen_type b with
  | true => f_ret
  | false => fun _ => tt
  end f.

Definition gen_abs {b: bool} (f: gen_sym b) : def :=
  match b return gen_sym b -> def with
  | true => abs_fun
  | false => abs_pred
  end f.

Definition a_convert_gen {b: bool} (t: gen_term b) (vs: list vsymbol) : gen_term b :=
  match b return gen_term b -> gen_term b with
  | true => fun t => a_convert_t t vs
  | false => fun f => a_convert_f f vs
  end t.


End Gen.

(*Easy: don't need to change b as wer recurse*)

(*Assume everything alpha converted already so no free var in hd in bound in t*)
Fixpoint t_insert (ty: vty) (hd t: term) : formula :=
  match t with
  | Tif f t2 t3 => Fif f (t_insert ty hd t2) (t_insert ty hd t3)
  | Tlet t1 v t2 => Flet t1 v (t_insert ty hd t2)
  | Tmatch tm ty1 pats => Fmatch tm ty1 (map (fun x => (fst x, (t_insert ty hd (snd x)))) pats)
  | _ => Feq ty hd t
  end.

Fixpoint f_insert (hd t: formula) : formula :=
  match t with
  | Fif f t2 t3 => Fif f (f_insert hd t2) (f_insert hd t3)
  | Flet t1 v t2 => Flet t1 v (f_insert hd t2)
  | Fmatch tm ty1 pats => Fmatch tm ty1 (map (fun x => (fst x, (f_insert hd (snd x)))) pats)
  | _ => Fbinop Tiff hd t
  end.

(*Need this to get around positivity checker*)
Definition t_insert_gen {b: bool} (ty: gen_type b) (hd t: gen_term b) : formula :=
  match b return gen_type b -> gen_term b -> gen_term b -> formula with
  | true => t_insert
  | false => fun _ => f_insert
  end ty hd t.




Definition add_ld (which: forall b, gen_sym b -> bool) (x: funpred_def) 
  (y: list def * list funpred_def * list (string * formula)) : 
  list def * list funpred_def * list (string * formula) :=
  let '(abst, defn, axl) := y in
  match (gen_funpred_def_match x) with
  | existT b (ls, vl, e) =>
    if which b ls then
      (*Create new name for axiom*)
      let pr := ((gen_sym_name ls) ++ "_'def")%string in
      (*produce e.g. the term fact(n) - note that these are always polymorphic so we can give vars*)
      let hd := gen_app b ls (map vty_var (gen_sym_params ls)) (map Tvar vl) in
      let ty := gen_sym_ret ls in
      (*Axiom: forall n, fact n = e*)
      (*First, alpha convert e so there are no freevars in common*)
      let e' := a_convert_gen e vl in
      let ax1 := fforalls vl (t_insert_gen ty hd e') in
      let ax2 := (pr, ax1) in
      (*abstract logical symbol*)
      let ld := gen_abs ls in
      (ld :: abst, defn, ax2 :: axl)
    else 
      (abst, x :: defn, axl)
  end.

(*Here, nonrec means that we are giving in non-recursive*)
Definition elim_decl (which: forall b, gen_sym b -> bool)(nonrec: bool) (l: list funpred_def) : list def * list (string * formula) :=
  let '(abst, defn, axl)  :=
    fold_right (add_ld which) (nil, nil, nil) l in
  let defn :=
    match defn with
    | nil => nil
    | [d] => if nonrec then [nonrec_def d] else [recursive_def [d]]
    | _ => [recursive_def defn]
    end in
  (abst ++ defn, axl). 

(*Slightly different; we also choose if we eliminate nonrecursive*)
Definition elim (which: forall b, gen_sym b -> bool) (nonrec: bool) (d: def) : list def * list (string * formula) :=
  match d with
  | recursive_def l => elim_decl which false l
  | nonrec_def l => if nonrec then elim_decl which true [l] else ([d], nil)
  | _ => ([d], nil)
  end.

(*Only eliminate recursion*)
(* Definition elim_recursion (d: def) : list def * list (string * formula) :=
  match d with
  | recursive_def l => (*Don't need to check for sym inside because we separate them
    also we don't allow mutual, non-recursive*)
    elim_decl (fun _ _ => true) l
  | _ => ([d], nil)
  end. *)

(*Versions to handle only structural (we only allow structural) and mutual, which we don't
  include at the moment*)

Definition eliminate_definition_gen which nonrec : trans :=
  fun t => [trans_decl (elim which nonrec) t].
Definition eliminate_definition_func : trans :=
  eliminate_definition_gen (fun b _ => b) true.
Definition eliminate_definition_pred : trans :=
  eliminate_definition_gen (fun b _ => negb b) true.
Definition eliminate_definition : trans :=
  eliminate_definition_gen (fun _ _ => true) true.
Definition eliminate_recursion : trans :=
  eliminate_definition_gen (fun _ _ => true) false.

(*Proofs*)

Section Proofs.

(*Part 1: Rewrite lemmas*)

(*Just like [eliminate_inductive], easier to reason about gamma and delta
  separately*)

(*Helpful for us - get axiom for single logic def*)
Definition rec_axiom {b: bool} (ls: gen_sym b)
  (vl: list vsymbol) (e: gen_term b) : string * formula :=
  let pr := ((gen_sym_name ls) ++ "_'def")%string in
  let hd := gen_app b ls (map vty_var (gen_sym_params ls)) (map Tvar vl) in
  let ty := gen_sym_ret ls in
  let e' := a_convert_gen e vl in
  let ax1 := fforalls vl (t_insert_gen ty hd e') in
  (pr, ax1).

(*Decls for each recursive def: either single one or one abstract symbol per element*)



Definition axioms_of_def (which : forall b, gen_sym b -> bool) 
  (l: list funpred_def) : list (string * formula) :=
  concat (map (fun x =>
    match (gen_funpred_def_match x) with
    | existT b (ls, vl, e) => 
      if which _ ls then [rec_axiom ls vl e] else []
    end) l).

(* Definition partition_map {A B C: Type} (f: A -> option B) (g: A -> C)  (l: list A) :
  list B * list C :=
  (Pattern.filter_map f l, 
  Pattern.filter_map (fun x => match f x with | None => Some (g x) | _ => None end) l). *)

(*We do this in 2 parts: give both the axioms and the ones to go in the recursive
  decl, separately*)
Definition decls_of_def_aux (which: forall b, gen_sym b -> bool) (nonrec : bool)
  (l: list funpred_def) : list def * list funpred_def :=
  (*TODO: partition*)
  (Pattern.filter_map (fun x =>
  match (gen_funpred_def_match x) with
  | existT b (ls, vl, e) => if which _ ls then Some (gen_abs ls) else None
  end
  ) l,
  Pattern.filter_map (fun x =>
  match (gen_funpred_def_match x) with
  | existT b (ls, vl, e) => if which _ ls then None else Some x
  end) l).

Definition decls_of_def (which: forall b, gen_sym b -> bool) (nonrec : bool)
  (l: list funpred_def) : list def * option def :=
  let x := decls_of_def_aux which nonrec l in
  (fst x, match snd x with
    | nil => None
    | [d] => Some (if nonrec then nonrec_def d else recursive_def [d])
    | _ => Some (recursive_def (snd x))
  end).

Definition decl_list_of_def (which: forall b, gen_sym b -> bool) (nonrec : bool)
  (l: list funpred_def) : list def :=
  let x := decls_of_def which nonrec l in
  fst x ++ match (snd x) with | None => nil | Some d => [d] end.


(*We have two transformations: one that generates axioms, one that
  changes gamma*)

Definition gen_axioms which (nonrec : bool) (t: task) : task :=
  let new_d :=
  concat (map (fun x =>
    match x with
    | recursive_def l => rev (axioms_of_def which l)
    | nonrec_def l => if nonrec then rev (axioms_of_def which [l]) else nil
    | _ => []
    end) (task_gamma t)) in
  add_axioms t new_d.

Definition gen_new_ctx which (nonrec : bool) (t: task) : task :=
  let new_g :=
  concat (map (fun x =>
    match x with
    | recursive_def l => rev (decl_list_of_def which false l)
    | nonrec_def l => if nonrec then rev (decl_list_of_def which true [l]) else [x]
    | _ => [x]
    end) (task_gamma t)) in
  mk_task new_g (task_delta t) (task_goal t).

Definition eliminate_definition_alt which nonrec : trans :=
  compose_single_trans (gen_axioms which nonrec) (gen_new_ctx which nonrec).

(*TODO: move*)
(* Definition task_decl_gamma (f: def -> list def * list (string * formula)) 
  (t: task) : task :=



Lemma trans_decl_split (f: def -> list def * list (string * formula)) 
  (t: task) :
  trans_decl f t = 
  compose_single_trans ()

Definition trans_decl (f: def -> list def * list (string * formula)) 
  (t: task) : task :=
  let (g, d) :=
  List.fold_left (fun acc x =>
    let (g, d) := f x in
    let t := acc in
    (g ++ fst t, d ++ snd t)
  ) (task_gamma t) (nil, nil) in
  mk_task (List.rev g) (List.rev d ++ task_delta t) (task_goal t).
 *)

 (*Lemmas we need*)
Lemma decls_of_def_elim which nonrec (l: list funpred_def):
   (fst (elim_decl which nonrec l)) = decl_list_of_def which nonrec l.
Proof.
  unfold elim_decl, decl_list_of_def.
  (*Handle end first*)
  destruct (fold_right _ _ _) as [[abst defn] axl] eqn : Hfold.
  simpl fst at 1. f_equal.
  - (*First, prove abstract*)
    replace abst with (fst (fst (fold_right (add_ld which) (nil, nil, nil) l))) by (rewrite Hfold; reflexivity).
    clear Hfold. induction l as [| x t IH]; simpl; auto.
    unfold add_ld at 1.
    destruct (gen_funpred_def_match x) as [b [[ls vs] e]] eqn : Hgen; simpl in *.
    destruct (fold_right (add_ld which) ([], [], []) t ) as [[abst1 defn1] axl1]; simpl.
    destruct (which b ls) eqn : Hwhich; simpl; [f_equal|]; auto.
  - (*Now prove end*)
    assert (Habs: forall l,snd (fst (fold_right (add_ld which) (nil, nil, nil)l)) = 
      snd (decls_of_def_aux which nonrec l)).
    {
      clear. induction l as [| h t IH]; simpl; auto.
      unfold add_ld at 1.
      destruct (fold_right (add_ld which) ([], [], []) t ) as [[abst1 defn1] axl1]; simpl.
      simpl snd at 1 in IH.
      destruct (gen_funpred_def_match h) as [b [[ls vs] e]] eqn : Hgen.
      destruct (which b ls) eqn : Hwhich; auto.
      simpl. f_equal; auto.
    }
    (*The rest is just case analysis*)
    unfold decls_of_def at 1. Opaque decls_of_def_aux. simpl snd. Transparent decls_of_def_aux.
    destruct defn as [| def1 deft].
    { rewrite <- Habs, Hfold. reflexivity. }
    destruct deft as [|def2 deft].
    + destruct nonrec; rewrite <- Habs, Hfold; reflexivity.
    + rewrite <- Habs, Hfold; reflexivity.
Qed.


(*And the proof of equivalence*)
Lemma eliminate_definition_split which nonrec: forall t,
  eliminate_definition_gen which nonrec t =
  eliminate_definition_alt which nonrec t.
Proof.
  intros t. unfold eliminate_definition_gen, eliminate_definition_alt, compose_single_trans, single_trans, trans_decl.
  f_equal. unfold gen_new_ctx, gen_axioms.
  destruct t as [[gamma delta] goal]; simpl_task.
  rewrite (surjective_pairing (fold_left _ gamma _)); simpl. f_equal. f_equal.
  - (*Prove gamma equivalent*)
    rewrite <- fold_left_rev_right. simpl_task.
    rewrite <- (rev_involutive gamma) at 2.
    (*TODO: bad*)
    induction (rev gamma); simpl; auto.
    rewrite (surjective_pairing (elim _ _ a)); simpl.
    rewrite rev_app_distr.
    rewrite map_app, concat_app. simpl. rewrite app_nil_r.
    rewrite IHl. f_equal.
    (*The interesting part*)
    destruct a; simpl; try reflexivity.
    + rewrite decls_of_def_elim. reflexivity.
    + destruct nonrec; simpl; [| reflexivity]. rewrite decls_of_def_elim. reflexivity.
  - (*Prove delta part*)
    f_equal. rewrite <- fold_left_rev_right.
    rewrite <- (rev_involutive gamma) at 2.
    rewrite map_rev.
    induction (rev gamma); simpl; auto.
    rewrite (surjective_pairing (elim _ _ a)); simpl.
    rewrite !rev_app_distr.  (*TODO: STAET HERE*)
    
    rewrite rev_map.
    destruct a; simpl; try rewrite concat_app; simpl;
    try rewrite IHl, app_nil_r; auto.
    rewrite build_ind_axioms_eq. simpl.
    rewrite rev_app_distr, IHl, app_nil_r.
    reflexivity.
      admit.
  - 
    
     unfold decls_of_def, elim_decl.
      rewrite (surjective_pairing (partition _ _)). simpl.

    
     simpl.


intros. unfold eliminate_inductive, eliminate_inductive_alt,
  compose_single_trans, single_trans.
  f_equal.
  unfold trans_decl, gen_new_ctx, gen_axioms.
  destruct t as [[gamma delta] goal]; simpl_task.
  rewrite (surjective_pairing (fold_left
  (fun (acc : list def * list (string * formula)) (x : def) =>
   let (g, d) := elim x in (g ++ fst acc, d ++ snd acc)) gamma (
  [], []))); simpl. f_equal. f_equal.
  - (*Prove gamma equivalent*)
    (*Eliminate fold_left*)
    rewrite <- fold_left_rev_right. simpl_task. 
    rewrite <- (rev_involutive gamma) at 2.
    induction (rev gamma); simpl; auto.
    rewrite (surjective_pairing (elim a)); simpl.
    rewrite rev_app_distr.
    destruct a; simpl; try 
    (rewrite IHl, map_app; simpl; rewrite concat_app; reflexivity).
    rewrite map_app; simpl. 
    rewrite get_indpred_defs_eq; simpl.
    rewrite concat_app, IHl; simpl. 
    rewrite app_nil_r; auto.
  - (*Prove delta part*)
    f_equal. rewrite <- fold_left_rev_right.
    rewrite <- (rev_involutive gamma) at 2.
    rewrite map_rev.
    induction (rev gamma); simpl; auto.
    rewrite (surjective_pairing (elim a)); simpl.
    destruct a; simpl; try rewrite concat_app; simpl;
    try rewrite IHl, app_nil_r; auto.
    rewrite build_ind_axioms_eq. simpl.
    rewrite rev_app_distr, IHl, app_nil_r.
    reflexivity.



(*Prove soundness*)
Theorem eliminate_definition_gen_sound which:
  sound_trans (eliminate_definition_gen which).
Proof.
  (*First, split into two parts*)
  rewrite sound_trans_ext.
  2: apply eliminate_inductive_split.
  unfold eliminate_inductive_alt.
  (*Prove sound by composition*)
  apply compose_single_trans_sound.
  - (*The very hard part:*) apply gen_axioms_sound.
  - (*The easier part*) apply gen_new_ctx_sound.
  - (*All axioms are well-formed*) apply gen_axioms_wf.
Qed.
