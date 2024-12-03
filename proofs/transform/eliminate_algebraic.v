Require Import AssocList.
Require Import Task.
Require Import GenElts.


(*Here, we ignore metas since they don't exist in the core language.
  We also (mostly) ignore tuples, we can prove soundness separately
  because this is trivial - ex: tp_map just determines if we should compile or not.
  This just includes the critical path - when the ADT is actually axiomatized
  NOTE: we do not use keep_e, keep_r, and keep_m, kept_m - we will just have a generic
  selector function to determine which types to axiomatize and which to keep
  (esesntially, enc_ty/kept_no_case is a parameter).
  In contrast, we do need no_ind, no_inv, and no_sel (though these will also be abstract)
  because we need to prove soundness in all cases
  *)

From RecordUpdate Require Import RecordSet.
Record state := mk_state {
  mt_map : amap typesym funsym;       (* from type symbols to selector functions *)
  cc_map : amap funsym funsym;       (* from old constructors to new constructors *)
  cp_map : amap funsym (list funsym);  (* from old constructors to new projections *)
  pp_map : amap funsym funsym;       (* from old projections to new projections *)
  kept_m : amap typesym (list vty);         (* should we keep constructors/projections/Tcase for this type? *)
  (* tp_map : Mid.t (decl*theory_c); skipped tuple symbols *)
  (* inf_ts : Sts.t;               infinite types *)
  (* ma_map : Mts.t (list bool );     material type arguments *)
  (* keep_e : bool;                keep monomorphic enumeration types *)
  (* keep_r : bool;                keep non-recursive records *)
  (* keep_m : bool;                keep monomorphic data types *)
  no_ind : bool;                (* do not generate indexing functions *)
  no_inv : bool;                (* do not generate inversion axioms *)
  no_sel : bool;                (* do not generate selector *)
}.

(*Here, we can use coq-record-update*)

#[export] Instance etaX : Settable _ := settable! mk_state <mt_map; cc_map; cp_map; pp_map; kept_m; no_ind; no_inv; no_sel>.
Import RecordSetNotations. 

(*Infer args for functions - hard to get it right*)

Definition fold_right2_opt {A B C: Type} (f: A -> B -> C -> option C) (base: C) :=
  fix fold (l1: list A) (l2: list B) : option C :=
    match l1, l2 with
    | nil, nil => Some base
    | x1 :: t1, x2 :: t2 => option_bind (fold t1 t2) (f x1 x2) 
    | _, _ => None
    end.

(*gives a map from vars to types such that [v_subst s t1] = t2 if one exists*)
Fixpoint ty_match (t1 t2: vty) (s: amap typevar vty) : option (amap typevar vty) :=
  match t1, t2 with
  | vty_cons ts1 tys1, vty_cons ts2 tys2 =>
    if typesym_eqb ts1 ts2 then
    fold_right2_opt ty_match s tys1 tys2
    else None
  | vty_var n1, _ =>
    (*See if n1 is mapped to t2 (OK) or nothing (add), else None*)
    match amap_get typevar_eq_dec s n1 with
    | Some ty3 => if vty_eqb t2 ty3 then Some s else None
    | None => Some (amap_set typevar_eq_dec s n1 t2)
    end
  | _, _ => if vty_eqb t1 t2 then Some s else None
  end.

(*Now use this to infer type map for functions*)
(*Is there a type substitution sigma such that sigma (args) = *)
Definition find_fpsym_map (f: fpsym) (tys: list vty) : option (amap typevar vty) :=
  fold_right2_opt ty_match amap_empty (s_args f) tys.

Definition find_param_vals (params: list typevar) (s: amap typevar vty) : list vty :=
  map (fun p => 
    match amap_get typevar_eq_dec s p with
    | Some t => t
    | None => vty_int (*not used so instantiate to anything*)
    end) params.

Definition tfun_infer (f: funsym) (tys: list vty) (tms: list term) : option term :=
  match (find_fpsym_map f tys) with
  | Some s => 
    (*Find values for all type params from s - if not there, not used, so we can
      just assign it int (or whatever)*)
    Some (Tfun f (find_param_vals (s_params f) s) tms)
  | None => None
  end.

Definition tfun_infer_ret (f: funsym) (tys: list vty) (tms: list term) : option (term * vty) :=
  match (find_fpsym_map f (f_ret f :: tys)) (*TODO: is this right?*) with
  | Some s => 
    (*Find values for all type params from s - if not there, not used, so we can
      just assign it int (or whatever)*)
    let tys := (find_param_vals (s_params f) s) in
    Some (Tfun f tys tms, ty_subst (s_params f) tys (f_ret f))
  | None => None
  end.

(*TODO: prove doesnt happen (how?)*)
Definition tfun_infer' (f: funsym) (tys: list vty) (tms: list term) : term :=
match tfun_infer f tys tms with | Some t => t | _ => tm_d end.
Definition tfun_infer_ret' (f: funsym) (tys: list vty) (tms: list term) : term * vty :=
match tfun_infer_ret f tys tms with | Some t => t | _ => (tm_d, vty_int) end.

    


Section ElimADT.

Variable keep_tys : typesym -> bool.

Definition enc_ty (t: vty) : bool :=
  match t with
  | vty_cons ts _ => negb (keep_tys ts)
  | _ => false
  end.

(*TODO move:*)
Definition amap_get_def {A B: Type} eq_dec (m: amap A B) (x: A) (d: B) : B :=
  match amap_get eq_dec m x with
  | Some y => y
  | None => d
  end.

(*TODO: move from CoqUtil to Common*)
Definition fold_left2 {A B C: Type} (f: C -> A -> B -> C) :=
  fix fold_left2 (l1: list A) (l2: list B) (accu: C) : option C :=
    match l1, l2 with
    | nil, nil => Some accu
    | a1 :: l1, a2 :: l2 => 
      fold_left2 l1 l2 (f accu a1 a2)
    | _, _ => None
    end.

(*Note: dangerous, need to prove lists have same length*)
Definition fold_left2' {A B C: Type} (f: C -> A -> B -> C) (l1: list A) (l2: list B) (accu: C) : C :=
  match fold_left2 f l1 l2 accu with 
  | Some l => l
  | None => accu
  end.

  (*TODO: move from eliminate_let*)
Section MoveFromLet.


(*Inspired by Equations/examples/RoseTree.v*)

Definition dep_map {A B: Type} {P: A -> Prop} (f: forall x, P x -> B) := 
fix dep_map (l: list A) (Hall: Forall P l) : list B :=
  match l as l' return Forall P l' -> list B with
  | nil => fun _ => nil
  | x :: tl => fun Hforall => f x (Forall_inv Hforall) ::
    dep_map tl (Forall_inv_tail Hforall)
  end Hall.

Definition map_In {A B: Type} (l: list A) 
  (f: forall (x: A), In x l -> B) : list B :=
  dep_map f l (all_in_refl l).

Lemma dep_map_length {A B: Type} {P: A -> Prop} 
  (f: forall x: A, P x -> B) (l: list A) (Hall: Forall P l):
  length (dep_map f l Hall) = length l.
Proof.
  revert Hall.
  induction l; simpl; intros; auto.
Qed.

Lemma dep_map_nth {A B: Type} {P: A -> Prop}
(f: forall x: A, P x -> B) (l: list A) (Hall: Forall P l)
(i: nat) (d1: A) (d2: B) (Hnth: P (nth i l d1)):
i < length l ->
nth i (dep_map f l Hall) d2 =
f (nth i l d1) Hnth.
Proof.
  revert i Hall Hnth. induction l; simpl; intros; auto.
  - lia.
  - destruct i. f_equal. apply proof_irrel.
    apply IHl. lia.
Qed.

Lemma map_In_length {A B: Type} (l: list A) 
(f: forall (x: A), In x l -> B):
length (map_In l f) = length l.
Proof.
  unfold map_In; rewrite dep_map_length; auto.
Qed.

Lemma map_In_spec {A B : Type} (f : A -> B) (l : list A) :
  map_In l (fun (x : A) (_ : In x l) => f x) = map f l.
Proof.
  (*This is very dumb, but we need an A*)
  destruct l; auto.
  remember (a :: l) as l'.
  unfold map_In.
  apply list_eq_ext'; rewrite dep_map_length; [rewrite map_length |]; auto.
  intros n d Hn.
  erewrite dep_map_nth with(d1:=a); auto; [|apply nth_In; auto].
  rewrite map_nth_inbound with(d2:=a); auto.
Qed.

(* Lemma in_map_In_iff {A B: Type} (l: list A)
  (f: forall (x: A), In x l -> B) (y: B):
  In y (map_In l f) <-> exists x Hin, f x Hin = y.
Proof.
  unfold map_In. split; intros.
  - apply dep_map_in in H.
    destruct H as [x [H [Hinx Hy]]]; subst; exists x; exists H; auto.
  - destruct H as [x [Hin Hy]]; subst.
    assert (Hinx:=Hin).
    apply in_dep_map with(f:=f)(Hall:=all_in_refl l) in Hinx.
    destruct Hinx as [Hin' Hinx].
    assert (Hin = Hin') by apply proof_irrel.
    subst; auto.
Qed. *)

Definition t_map (f1: term -> term) (f2: formula -> formula) 
  (t: term): term :=
  match t with
  | Tfun f vs tms => Tfun f vs (map_In tms (fun x H => f1 x))
  | Tlet t1 v t2 => Tlet (f1 t1) v (f1 t2)
  | Tif f t1 t2 => Tif (f2 f) (f1 t1) (f1 t2)
  | Tmatch tm ty ps => Tmatch (f1 tm) ty 
      (map (fun x => (fst x, f1 (snd x))) ps)
  | Teps f v => Teps (f2 f) v
  | _ => t
  end.

Definition f_map (f1: term -> term) (f2: formula -> formula) 
  (f: formula): formula :=
  match f with
  | Fpred p tys tms => Fpred p tys (map f1 tms)
  | Fquant q x f => Fquant q x (f2 f)
  | Feq ty t1 t2 => Feq ty (f1 t1) (f1 t2)
  | Fbinop b fa fb => Fbinop b (f2 fa) (f2 fb)
  | Fnot f => Fnot (f2 f)
  | Flet t v f => Flet (f1 t) v (f2 f)
  | Fif fa fb fc => Fif (f2 fa) (f2 fb) (f2 fc)
  | Fmatch tm ty ps => Fmatch (f1 tm) ty
  (map (fun x => (fst x, f2 (snd x))) ps)
  | _ => f
  end.

End MoveFromLet.

(*TODO: move*)
Definition f_map_sign (fn1: bool -> term -> term) (fn2: bool -> formula -> formula) (sign: bool) (f: formula) : formula :=
  match f with
  | Fbinop Timplies f1 f2 =>
    Fbinop Timplies (fn2 (negb sign) f1) (fn2 sign f2)
  | Fbinop Tiff f1 f2 =>
    let f1p := fn2 sign f1 in let f1n := fn2 (negb sign) f1 in
    let f2p := fn2 sign f2 in let f2n := fn2 (negb sign) f2 in
    if formula_eqb f1p f1n && formula_eqb f2p f2n then Fbinop Tiff f1p f2p
    else if sign
      then Fbinop Tand (Fbinop Timplies f1n f2p) (Fbinop Timplies f2n f1p)
      else Fbinop Timplies (Fbinop Tor f1n f2n) (Fbinop Tand f1p f2p)
  | Fnot f1 => Fnot (fn2 (negb sign) f1)
  | Fif f1 f2 f3 =>
    let f1p := fn2 sign f1 in let f1n := fn2 (negb sign) f1 in
    let f2 := fn2 sign f2 in let f3 := fn2 sign f3 in
    if formula_eqb f1p f1n then Fif f1p f2 f3 else if sign
      then Fbinop Tand (Fbinop Timplies f1n f2) (Fbinop Timplies (Fnot f1p) f3)
      else Fbinop Tor (Fbinop Tand f1p f2) (Fbinop Tand (Fnot f1n) f3)
  | _ => f_map (fn1 sign) (fn2 sign) f
  end.
(*TODO: is this right definition?*)
Definition t_map_sign (fn1: bool -> term -> term) (fn2: bool -> formula -> formula) (sign: bool) (t: term) : term :=
  t_map (fn1 sign) (fn2 sign) t.


(*TODO: move*)
Definition ts_d : typesym := mk_ts "" [].

(*TODO: move PatternProofs.get_constructors*)

Section Rew.
Variable (gamma: context).
Variable (s: state).

(*TODO: bad, can we find the type differently?*)
Definition pat_match_ty (pats: list (pattern * term)) : option vty :=
  match pats with
  | nil => None
  | (p, t) :: _ => Typechecker.typecheck_term gamma t
  end.

(*TODO: move*)
Definition set_diff {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y}) (l1 l2: list A) : list A :=
  filter (fun x => negb (in_dec eq_dec x l2)) l1.

Definition set_add {A: Type} (eq_dec: forall (x y: A), {x = y} + {x <> y}) (x: A) (l: list A) :=
  if in_dec eq_dec x l then l else x :: l.

(*Assume we have a list of banned variables (instantiate with term vars)*)
Variable badvars : list vsymbol.

(*TODO: move*)
Definition map_join_left {A B: Type} (map: A -> B) (join: B -> B -> B) (l: list A) : option B :=
  match l with
  | x :: xl => Some (fold_left (fun acc x => join acc (map x)) xl (map x))
  | _ => None
  end.
Definition map_join_left' {A B: Type} (d: B) (map: A -> B) (join: B -> B -> B) 
  (l: list A) : B :=
  match map_join_left map join l with | Some y => y | None => d end.

(*It is often difficult to figure out what the type arguments for functions should be.
  We will do it as they do, trying to instantiate a type mapping*)


Fixpoint rewriteT (t: term) : term :=
  match t with
  | Tmatch t1 ty pats => 
    if enc_ty ty then
      let t1 := rewriteT t1 in
      let mk_br (x: option term * amap funsym term) (br: pattern * term) :=
        let w := fst x in
        let m := snd x in
        let e := rewriteT (snd br) in
        match (fst br) with
        | Pconstr cs tys pl =>
          let add_var e p pj :=
            match p with
            | Pvar v => Tlet (Tfun pj [snd v] [t1]) v e
            | _ => tm_d (*NOTE: default, because we never hit it anyway by assumption*)
            end
            in
            let pjl := amap_get_def funsym_eq_dec s.(cp_map) cs nil in 
             (*match amap_get funsym_eq_dec s.(cp_map) cs with
            | Some cp => cp
            | None => nil (*TODO: prove don't hit (basically, will prove by knowing that all
              defined types appeared before and hence have already been added to map)*)
            end in*)
            let e := fold_left2' add_var pl pjl e in
            (w, amap_set funsym_eq_dec m cs e)
        | Pwild => (Some e, m)
        | _ => (*Prove don't hit*) x
        end
      in
      let res := fold_left mk_br pats (None, amap_empty) in
      let w := fst res in
      let m := snd res in (*gives map constructors to new terms*)
      let find x := 
        match amap_get funsym_eq_dec m x with
        | Some e => e
        | None => match w with | Some x => x | None => (*impossible*) tm_d end
        end
      in
      let ts := match ty with | vty_cons ts _ => ts | _ => ts_d (*impossible*) end in
      match map find (@PatternProofs.get_constructors gamma ts) with
      | [t] => t
      | tl => (*Get *) 
        (*Get the type - NOTE: use fact that not empty*)
        let ty1 := match pat_match_ty pats with | Some t => t | None => ty end in 
        tfun_infer' (amap_get_def typesym_eq_dec s.(mt_map) ts id_fs) (ty :: repeat ty1 (length tl))
          (t1 :: tl) (*TODO: prove not default*)
        (*return type: list a -> b -> b -> b, so give [vty_var a; ty1] if a is list var
          (types of args are [(ty :: repeat ty1 (length tl))])*)
          (*Don;t know if this type is right?*)
        (*this gives projection*) (*(map vty_var (ts_args ts) ++ [ty1]) (t1 :: tl) (*what is ty?*)*) 
        (*Type should be original type of term - can we tell this?
          arguments have type: [ty; ty1; ty1, ... ty1] if elements in pat match have type ty1. 
          We may need to carry around this information*)
      end
    else t_map rewriteT (rewriteF nil true) t
  | Tfun ls tys args => (*map old constrs to new constr*)
    if ls.(f_is_constr) && enc_ty (f_ret ls) (*we can just pass in return type because only depends on typesym*)
    then Tfun (amap_get_def funsym_eq_dec s.(cc_map) ls id_fs) tys args
    else t_map rewriteT (rewriteF nil true) t
  (*Don't have projections*)
  | _ => t_map rewriteT (rewriteF nil true) t
  end
with rewriteF (av: list vsymbol) (sign: bool) (f: formula) : formula := 
  match f with
  | Fmatch t1 ty1 pats =>
    if enc_ty ty1 then
      let t1 := rewriteT t1 in
      let av' := set_diff vsymbol_eq_dec av (tm_fv t1) in (*TODO: what is this doing?*)
      let mk_br (x: option formula * amap funsym (list vsymbol * formula)) br :=
        let p := fst br in
        let e := snd br in
        let w := fst x in
        let m := snd x in
        let e := rewriteF av' sign e in
        match p with
        | Pconstr cs tys pl =>
          let get_var p := match p with
            | Pvar v => v
            | _ => (*TODO: prove don't hit*) vs_d
          end in
          (w, amap_set funsym_eq_dec m cs (map get_var pl, e))
        | Pwild => (Some e, m)
        | _ => (*TODO: prove dont hit*) x
        end in
      let res := fold_left mk_br pats (None, amap_empty) in
      let w := fst res in
      let m := snd res in
      let find cs :=
        let res := match amap_get funsym_eq_dec m cs with
        | Some y => y
        | None => (*Need fresh vars - TODO: *)
            let projs := amap_get_def funsym_eq_dec (s.(cp_map)) cs nil in
            let names := gen_strs (length projs) badvars in
            (*NOTE: I think type should be ty_subst (s_params s) [ty1] (s_ret s) - they use t_app_infer*)
            let vars := map2 (fun n (p: funsym) => (n, ty_subst (s_params p) [ty1] (f_ret p))) names projs : list vsymbol in
            (vars, match w with | Some y => y | None => Ftrue end) (*TODO: prove dont hit*)
        end
        in
        let vl := fst res in let e := snd res in
        let hd := tfun_infer' (amap_get_def funsym_eq_dec (s.(cc_map)) cs id_fs) (map snd vl) (map Tvar vl) in
        match t1 with
        | Tvar v => if in_dec vsymbol_eq_dec v av then
          let hd := Flet hd v e in if sign then fforalls vl hd else fexists vl hd
          else
          let hd := Feq ty1 t1 hd (*TODO: ty1?*) in if sign then fforalls vl (Fbinop Timplies hd e)
          else fexists vl (Fbinop Tand hd e)
        | _ => let hd := Feq ty1 t1 hd (*TODO: ty1?*) in if sign then fforalls vl (Fbinop Timplies hd e)
          else fexists vl (Fbinop Tand hd e)
        end
      in
      let ts :=
        match ty1 with | vty_cons ts _ => ts | _ => ts_d end (*TODO: show dont hit*) in
      let op := if sign then (Fbinop Tand) else (Fbinop Tor) in
      match map_join_left find op (@PatternProofs.get_constructors gamma ts) with
      | Some f => f
      | None => Ftrue (*TODO: prove don't hit*)
      end
    else f_map_sign (fun _ => rewriteT) (rewriteF nil) sign f
  | Fquant q v f1 =>
    if (quant_eqb q Tforall && sign) || (quant_eqb q Texists && negb sign) then
      let av := fold_right (set_add vsymbol_eq_dec) [v] av in
      Fquant q v (rewriteF av sign f1)
    else f_map_sign (fun _ => rewriteT) (rewriteF nil) sign f
  | Fbinop o _ _ =>
    if (binop_eqb o Tand && sign) || (binop_eqb o Tor && negb sign) then
      f_map_sign (fun _ => rewriteT) (rewriteF av) sign f (*not nil*)
    else f_map_sign (fun _ => rewriteT) (rewriteF nil) sign f
  | Flet t1 _ _ =>
    let av := set_diff vsymbol_eq_dec av (tm_fv t1) in
    f_map_sign (fun _ => rewriteT) (rewriteF av) sign f 
  | _ => f_map_sign (fun _ => rewriteT) (rewriteF nil) sign f
  end.

End Rew.

(*TODO: move from utils*)
Section MoveFromUtils.

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

End MoveFromUtils.

(*TODO: move from Pattern*)
Definition rev_map {B C: Type} (f: B -> C) (l: list B) : list C :=
  rev (map f l).


(*Generate axioms*)

Definition add_param_decl (t: task) (f: funsym) : task :=
  (abs_fun f :: task_gamma t, task_delta t, task_goal t).

Definition add_axiom (t: task) (n: string) (f: formula) : task :=
  (task_gamma t, (n, f) :: task_delta t, task_goal t).

(*NOTE: will prob need to separate out for proof purposes (e.g. map2 vs fold_left2 and separate function)*)
Definition add_selector_aux (st: state * task) (ts: typesym) (ty: vty) (csl: list funsym) :=
  let s := fst st in
  let tsk := snd st in
  if s.(no_sel) then (s, tsk) else
  (* declare the selector function *)
  let mt_id : string := ("match_" ++ ts_name ts)%string in
  (*TODO: does it need to be fresh?*)
  let mt_ty : vty := vty_var "a"%string in
  (* let mt_ty = ty_var (create_tvsymbol (id_fresh "a")) in *)
  let mt_al := ty :: rev_map (fun _ => mt_ty) csl in
  let mt_ls := funsym_noconstr_noty mt_id mt_al mt_ty in
  let mt_map2 := amap_set typesym_eq_dec s.(mt_map) ts mt_ls in
  let task  := add_param_decl tsk mt_ls in
  (* define the selector function *)
  (*Generate new vars*)
  let varnames := gen_names (length csl) "z"%string nil in
  let mt_vl : list vsymbol := rev_map (fun x => (x, mt_ty)) varnames in
  (* let mt_vs _ = create_vsymbol (id_fresh "z") mt_ty in *)
  (* let mt_vl = List.rev_map mt_vs csl in *)
  let mt_tl := rev_map Tvar mt_vl in
  let mt_add tsk (cs: funsym) t :=
    let id := (mt_id ++ "_" ++ (s_name cs))%string in
    (* let id = mt_ls.ls_name.id_string ^ "_" ^ cs.ls_name.id_string in *) 
    (* let pr = create_prsymbol (id_derive id cs.ls_name) in *)
    (*Create new vars - they can be the same among axioms (TODO: inefficient)*)
    let varnames2 := gen_names (length (s_args cs)) "u"%string varnames in
    let vl := rev (combine varnames2 (s_args cs)) in
    (* let vl = List.rev_map (create_vsymbol (id_fresh "u")) cs.ls_args in *)
    let newcs := amap_get_def funsym_eq_dec (s.(cc_map)) cs id_fs in (*TODO: show have*)
    let hd := tfun_infer' newcs (rev_map snd vl) (rev_map Tvar vl) in (*TODO: is return type right? - they say f_ret cs*)
    let hd := tfun_infer' mt_ls ((f_ret cs) :: map snd mt_vl) (hd :: mt_tl) in
    let vl := rev_append mt_vl (rev vl) in
    let ax := fforalls vl (Feq mt_ty hd t) in
    add_axiom tsk id ax
  in 
  let task := fold_left2 mt_add csl mt_tl tsk in
  (s <|mt_map := mt_map2|>, tsk).

Definition add_selector (acc : state * task) (ts: typesym) (ty: vty) (x: list funsym) :
  state * task :=
  match x with
  | [_] => acc
  | csl => add_selector_aux acc ts ty csl
  end.

(*TODO: move*)
Fixpoint iota m n := 
  match n with
  | S n' => m :: iota (S m) n'
  | _ => nil
  end.

Definition add_indexer_aux (st: state * task) (ts: typesym) (ty : vty) (csl : list funsym) : state * task :=
  let s := fst st in
  let tsk := snd st in
  (* declare the indexer function *)
  let mt_id := ("index_" ++ (ts_name ts))%string in
  let mt_ls := funsym_noconstr_noty mt_id [ty] vty_int in
  let tsk  := add_param_decl tsk mt_ls in
  (* define the indexer function *)
  let mt_add tsk (cs: funsym) idx :=
    let id := (mt_id ++ "_" ++ (s_name cs))%string in
    (* let pr = create_prsymbol (id_derive id cs.ls_name) in *)
    let varnames := gen_names (length (s_args cs)) "u" nil in
    let vl := rev (combine varnames (s_args cs)) in
    let newcs := amap_get_def funsym_eq_dec s.(cc_map) cs id_fs in
    (*NOTE: THESE TYPES MAY BE WRONG!*)
    let hd := tfun_infer' newcs (rev (map snd vl)) (rev_map Tvar vl) in
    (* let hd = fs_app newcs (List.rev_map t_var vl) (Option.get cs.ls_value) in *)
    let ax := Feq vty_int (tfun_infer' mt_ls (*TODO: what is hd type?*) [(f_ret newcs)] [hd] )  
      (Tconst (ConstInt (Z.of_nat idx))) in
    let ax := fforalls (rev vl) ax in
    add_axiom tsk id ax
  in
  let task := fold_left2' mt_add csl (iota 0 (length csl)) tsk in
  (s, task).

Definition t_neq (ty: vty) (t1 t2: term) : formula :=
  Fnot (Feq ty t1 t2).

Definition add_discriminator (st: state * task) (ts: typesym) (ty: vty) (csl: list funsym) : state * task :=
  let s := fst st in
  let tsk := snd st in
  let d_add (c1: funsym) tsk (c2: funsym) :=
    let id : string := ((s_name c1) ++ "_" ++ (s_name c2))%string in
    (* let pr = create_prsymbol (id_derive id ts.ts_name) in *)
    (*Create vars - TODO: does it have to be fresh against some vars?*)
    let ul := rev (combine (gen_names (length (s_args c1)) "u" nil) (s_args c1)) in
    let vl := rev (combine (gen_names (length (s_args c2)) "v" nil) (s_args c2)) in
    (* let ul := rev_map (create_vsymbol (id_fresh "u")) c1.ls_args in
    let vl = List.rev_map (create_vsymbol (id_fresh "v")) c2.ls_args in *)
    let newc1 := amap_get_def funsym_eq_dec (s.(cc_map)) c1 id_fs in
    let newc2 := amap_get_def funsym_eq_dec (s.(cc_map)) c2 id_fs in
    let t1 := tfun_infer' newc1 (rev (map snd ul)) (rev_map Tvar ul) in
    let t2 := tfun_infer' newc2 (rev (map snd vl)) (rev_map Tvar vl) in
    (* let t1 = fs_app newc1 (List.rev_map t_var ul) ty in
    let t2 = fs_app newc2 (List.rev_map t_var vl) ty in *)
    let ax := t_neq ty t1 t2 in
    let ax := fforalls (rev vl) ax in
    let ax := fforalls (rev ul) ax in
    add_axiom tsk id ax 
    (* let ax = t_forall_close (List.rev vl) [[t2]] ax in
    let ax = t_forall_close (List.rev ul) [[t1]] ax in
    add_prop_decl task Paxiom pr ax *)
  in
  let fix dl_add task l := 
    match l with
    | c :: cl => dl_add (fold_left (d_add c) cl task) cl
    | _ => task
    end
  in
  (s, dl_add tsk csl).

Definition add_indexer (acc: state * task) (ts: typesym) (ty: vty) (cs: list funsym) := 
  match cs with
  | [_] => acc
  | csl => if negb (fst acc).(no_ind) then add_indexer_aux acc ts ty csl
    else if Nat.leb (length csl) 16 then add_discriminator acc ts ty csl 
    else acc
  end.

Definition mapi {A B: Type} (f: nat -> A -> B) (l: list A) : list B :=
  map (fun x => f (fst x) (snd x)) (combine (iota 0 (length l)) l).

(*NOTE: complete_projections just copies over projections if they exist.
  We do not have any projections in our data, so we only implement the "None" case.
  TODO: we will need a predicate/typing rule asserting that projection is correct if it exists
  or something (not sure exactly what we need - will certainly need typing info) *)
(*ONLY creates function symbols - so projections are just user-named functions essentially - spec should
  just be that this produces SOME function symbol of the right type*)
Definition complete_projections (csl: list funsym) : list (funsym * list funsym) :=
  let conv_c (c: funsym) :=
    let conv_p (i: nat) (ty: vty) :=
      let id := ((s_name c) ++ "_proj_" ++ (nat_to_string i))%string in
      (*TODO: do we need option?*)(funsym_noconstr_noty id [f_ret c] ty)
    in
    (c, mapi conv_p (s_args c))
  in
  map conv_c csl.

Definition add_projections {A B: Type} (st: state * task) (_ts : A) (_ty : B) (csl: list funsym) :
  state * task :=
  let s := fst st in
  let tsk := snd st in
  (* declare and define the projection functions *)
  let pj_add x (y: funsym * _) :=
    let '(cp_map,pp_map,tsk) := x in
    let '(cs,pl) := y in
    (*Fresh vars TODO*)
    let vl := combine (gen_names (length (s_args cs)) "u" nil) (s_args cs) in
    (* let vl = List.map (create_vsymbol (id_fresh "u")) cs.ls_args in *)
    let tl := map Tvar vl in
    let hd := tfun_infer' (amap_get_def funsym_eq_dec (s.(cc_map)) cs id_fs)
      (map snd vl) tl in
    (* let hd = fs_app (Mls.find cs state.cc_map) tl (Option.get cs.ls_value) in *)
    (*TODO: added ty*)
     let add (x: list funsym * amap funsym funsym * task) (tty: term * vty) (pj: funsym) :
        list funsym * amap funsym funsym * task :=
      let t := fst tty in let ty := snd tty in
      let '(pjl,pp_map,tsk) := x in
      (* let pj := option_get_Option.get pj in *)
      let '(ls,pp_map) :=
        match amap_get funsym_eq_dec pp_map pj with
        | Some pj => (pj, pp_map)
        | None =>
          let id := (s_name pj) in
          let ls := funsym_noconstr_noty id (s_args pj) (f_ret pj) in
          (*NOTE: since we don't have unique ids, is this just pj? Is that a problem?*)
          (ls, amap_set funsym_eq_dec pp_map pj ls)
        end
      in
        (* match Mls.find pj pp_map with
        | pj -> pj,pp_map
        | exception Not_found ->
          let id = id_clone pj.ls_name in
          let ls = create_lsymbol id pj.ls_args pj.ls_value in
          ls,Mls.add pj ls pp_map
      in *)
      let tsk := add_param_decl tsk ls in
      let id := ((s_name ls) ++ "'def")%string in
      (* let id = id_derive (ls.ls_name.id_string ^ "'def") ls.ls_name in
      let pr = create_prsymbol id in *)
      let hh := tfun_infer' ls [(f_ret cs)] [hd] in
      (* let hh = t_app ls [hd] t.t_ty in *)
      let ax := fforalls vl (Feq ty hh t) in
      let tsk := add_axiom tsk id ax in
      (*Ignore metas*)
      (* let ax = t_forall_close vl [] (t_equ hh t) in
      let tsk = add_prop_decl tsk Paxiom pr ax in
      let tsk = add_meta_model_projection tsk ls in *)
      (ls::pjl,pp_map,tsk)
    in
    let '(pjl,pp_map,tsk) := fold_left2' add (combine tl (map snd vl)) pl ([],pp_map,tsk)  in
    (amap_set funsym_eq_dec cp_map cs (rev pjl), pp_map, tsk)
  in
  let csl := complete_projections csl in
  let '(cp_map2, pp_map2, task) :=
    fold_left pj_add csl (s.(cp_map), s.(pp_map), tsk)
  in
  (s <| cp_map := cp_map2 |> <|pp_map := pp_map2 |>, task).

Definition add_inversion (st: state * task) (ts: typesym) (ty: vty) (csl: list funsym) :
  state * task :=
  let s := fst st in let tsk := snd st in
  if s.(no_inv) then st else
  (* add the inversion axiom *)
  let ax_id := ((ts_name ts) ++ "_inversion")%string in
  (* let ax_pr = create_prsymbol (id_derive ax_id ts.ts_name) in *)
  (*TODO: fresh?*)
  let ax_vs := (gen_name "u"%string nil, ty) in 
  let ax_hd := Tvar ax_vs in
  let mk_cs (cs: funsym) :=
    let pjl := amap_get_def funsym_eq_dec s.(cp_map) cs nil in 
    (*NOTE: change app to also give return type*)
    let app pj := tfun_infer_ret' pj [ty] [ax_hd] in
    (* let app pj = t_app_infer pj [ax_hd] in *)
    let cs := amap_get_def funsym_eq_dec s.(cc_map) cs id_fs in
    (* let cs = Mls.find cs state.cc_map in *)
    let pjl' := map app pjl in
    Feq ty ax_hd (tfun_infer' cs (map snd pjl') (map fst pjl'))
    (* t_equ ax_hd (fs_app cs (List.map app pjl) ty) in *)
  in
  let ax_f := map_join_left' Ftrue mk_cs (Fbinop Tor) csl in
  let ax_f := Fquant Tforall ax_vs ax_f (*t_forall_close [ax_vs] [] ax_f in*) in
  (s, add_axiom tsk ax_id ax_f).

(*TODO: since we don't have builtin projections, we can't do the
  [kept_no_case] part for projections. We don't implement it at all.
  TODO: need to figure out: do we prove only a subset of allowed behaviors sound?
  or can we prove the rest at the higher level - assuming something about projections, etc
  Or should we add projections? Need to figure this out!*)

Definition add_axioms (st: state * task) (d: typesym * list funsym) : state * task :=
  let s := fst st in
  let tsk := snd st in
  let ts := fst d in
  let csl := snd d in
  (*NOTE: might be very easy to infer all types - might not need infer, might just all be typesym args*)
  let ty := vty_cons ts (map vty_var (ts_args ts)) in
  (*TODO: SKIP KEPT_NO_CASE*)
  if negb (null (ts_args ts)) || negb (amap_mem typesym_eq_dec ts s.(kept_m)) then
    (* declare constructors as abstract functions *)
    let cs_add (st: state * task) (cs: funsym) :=
      let s := fst st in let tsk := snd st in
      let id := s_name cs in (*TODO: no clone, is this ok*)
      let ls := funsym_noconstr_noty id (s_args cs) (f_ret cs) in (*TODO: this is ls*)
      (* let ls = create_lsymbol id cs.ls_args cs.ls_value in *)
      (s <| cc_map := amap_set funsym_eq_dec s.(cc_map) cs ls |>, add_param_decl tsk ls)
      (* { state with cc_map = Mls.add cs ls state.cc_map },add_param_decl task ls *)
    in
    let st := fold_left cs_add csl st in
    (* add selector, projections, and inversion axiom *)
    let st := add_selector st ts ty csl in
    let st := add_indexer st ts ty csl in
    let st := add_projections st ts ty csl in
    add_inversion st ts ty csl
  else st.

(*Skip [add_tags] and finding infinite types - only deals with metas*)



End ElimADT.

