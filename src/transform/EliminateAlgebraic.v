Require Import TermFuncs TermTraverse PatternComp TransDefs.
(** Compile match patterns *)
Import MonadNotations.

Local Open Scope errst_scope.
Definition rewriteT (t: term_c) : errState (CoqBigInt.t * hashcons_ty ty_c) term_c :=
  term_map (hashcons_ty ty_c)
  (*let*)
  (tmap_let_default _)
  (tmap_if_default _)
  (tmap_app_default _)
  (*only interesting case*)
  (fun _ t1 r1 tb =>
    res <- compile_bare_aux t_case_close t_let_close_simp [r1] (map (fun x => ([fst (fst x)], snd x)) tb) ;;
    errst_ret (t_attr_copy t res)
    )
  (tmap_eps_default _)
  (tmap_quant_default _)
  (tmap_binop_default _)
  (tmap_not_default _)
  t.

(*NOTE: type of trans not sufficient - might have state*)
Definition compile_match := decl_errst 
  (fun d => 
    l <-  errst_assoc5 (errst_tup1 (errst_tup1 (
        errst_list [decl_map (fun t => errst_tup1 (rewriteT t)) d]))) ;;
    errst_ret l)
    (*TODO: automate: need int * ty * decl -> int * full*) None.


Record state := {
  mt_map : Mts.t lsymbol;       (* from type symbols to selector functions *)
  cc_map : Mls.t lsymbol;       (* from old constructors to new constructors *)
  cp_map : Mls.t (list lsymbol);  (* from old constructors to new projections *)
  pp_map : Mls.t lsymbol;       (* from old projections to new projections *)
  kept_m : Mts.t Sty.t;         (* should we keep constructors/projections/Tcase for this type? *)
  tp_map : Mid.t (decl*theory); (* skipped tuple symbols *)
  inf_ts : Sts.t;               (* infinite types *)
  ma_map : Mts.t (list bool );     (* material type arguments *)
  keep_e : bool;                (* keep monomorphic enumeration types *)
  keep_r : bool;                (* keep non-recursive records *)
  keep_m : bool;                (* keep monomorphic data types *)
  no_ind : bool;                (* do not generate indexing functions *)
  no_inv : bool;                (* do not generate inversion axioms *)
  no_sel : bool;                (* do not generate selector *)
}.

(*Determin if this type should be kept (false) or axiomatized (true) - should only be called
  on ADTs*)
(*TODO: their implementation gives errors, ours just false - prove don't hit it*)
Definition enc_ty (s: state) (t: option ty_c) : (*errorM*) bool :=
  match t with
  | Some ty =>
    match ty_node_of ty with
    | Tyapp ts _ =>  (negb (Sty.mem ty (Mts.find_def _ Sty.empty ts s.(kept_m))))
    | _ => false (*assert_false "enc_ty"*)
    end
  | _ => false (*assert_false "enc_ty"*)
  end.
  
Require Import TermTraverse.

(*Axiomatize*)
(*NOTE: they call Printer.unsupportedTerm, we throw directly*)
Definition UnsupportedTerm (t: term_c * string) : errtype :=
  mk_errtype "UnsupportedTerm" t.

Definition uncompiled : string := "eliminate_algebraic: compile_match required".

(*move*)
Definition option_get {A: Type} (d: option A) : errorM A :=
  match d with
  | Some x => err_ret x
  | None => throw (Invalid_argument "option is None")
  end.

(*We write it manually: for this one, it is safe to use t_view_branch and similar, which
  makes things much simpler since we don't need a [traverse]*)
(*making 1 function, do type casing manually*)
Local Open Scope errst_scope.

Definition is_forall (q: quant) : bool :=
  match q with | Tforall => true | Texists => false end.
Definition is_exists (q: quant) : bool := negb (is_forall q).

Definition is_and (b: binop) : bool :=
  match b with | Tand => true | _ => false end.
Definition is_or (b: binop) : bool :=
  match b with | Tor => true | _ => false end.

(*No, we need hashconsing*)
(*Note: in term part, always ok to send Svs.empty, true -> only call rewriteF with these arguments*)
(*Very impressed that Coq's termination checker can handle this*)
Fixpoint rewriteT'  (kn: known_map) (s: state) (t: term_c) : errState (CoqBigInt.t * hashcons_ty ty_c) term_c :=
  match (t_node_of t) with
  | Tcase t1 bl =>
    (*First, if ignoring this type, ignore*)
    if negb (enc_ty s (t_ty_of t1)) then 
    TermTFAlt.t_map_errst_unsafe (rewriteT' kn s)  (rewriteF' kn s Svs.empty true) t
    else 
      t1 <- rewriteT' kn s t1 ;;
      let mk_br (x: option term_c * Mls.t term_c) br :=
        let '(w, m) := x in
        let b1 := t_view_branch br in
        let p := fst b1 in
        let e := snd b1 in
        e <- rewriteT' kn s e ;;
        match (pat_node_of p) with
        | Papp cs pl => 
        (*creates nested let: for variables
        *)
          let add_var e p pj := match (pat_node_of p) with
            (*TODO: can we prove that this is well-typed? Using unsafe t_app1 instead of fs_app*)
            | Pvar v => 
              a1 <- errst_tup2 (fs_app pj [t1] (v.(vs_ty))) ;;
              errst_lift2 (t_let_close_simp v a1 e)
            | _ => errst_throw (UnsupportedTerm (t, uncompiled))
          end
          in
          pjl <- errst_lift2 (Mls.find _ cs s.(cp_map)) ;;
          e <- fold_left2_errst add_var e pl pjl;;
          match e with
          | Some e => errst_ret (w, Mls.add cs e m)
          | None => (*lists different length*) errst_throw (Invalid_argument "List.fold_left2")
          end
        | Pwild => errst_ret (Some e, m)
        | _ => errst_lift2 (throw (UnsupportedTerm (t, uncompiled)))
        end
      in
      (*w is Some iff there is a wild*)
      (*map gives map of constructor to new term*)
      wm <- foldl_errst mk_br bl (None, Mls.empty) ;;
      let '(w, m) := wm in
      let find x :=
        match (Mls.find_opt (fst x) m) with
        | None => option_get w
        | Some y => err_ret y
        end in
      ts <- match (t_ty_of t1) with
      | Some ty => match (ty_node_of ty) with
                  | Tyapp ts _ => errst_ret ts
                  | _ => errst_throw (UnsupportedTerm (t, uncompiled))
                  end
      | None => errst_throw (UnsupportedTerm (t, uncompiled))
      end ;;
      res <-
        l <- errst_lift2 (errorM_list ((map find (find_constructors kn ts)))) ;;
        match l with
        | [t] => errst_ret t
        | tl => l <- errst_lift2 (Mts.find _ ts s.(mt_map)) ;;
        (*again, use non-hashcons version (only hashcons in typecheck anyway, prove well-typed)*)
          errst_tup2 (t_app l (t1 :: tl) (t_ty_of t))
        end ;;
      errst_ret (t_attr_copy t res)
  | Tapp ls args =>
    if (CoqBigInt.pos ls.(ls_constr) && enc_ty s (t_ty_of t)) then
      args <- errst_list (map (rewriteT' kn s) args) ;;
      cc <- errst_lift2 (Mls.find _ ls s.(cc_map)) ;;
      t1 <- errst_tup2 (t_app cc args (t_ty_of t)) ;;
      errst_ret (t_attr_copy t t1)
    else
      match args with
      (*Is this for tuples? see*)
      | [arg] =>
        if (ls.(ls_proj) && enc_ty s (t_ty_of t)) then
          arg <- rewriteT' kn s arg ;;
          pp <- errst_lift2 (Mls.find _ ls s.(pp_map)) ;;
          t1 <- errst_tup2 (t_app pp [arg] (t_ty_of t)) ;;
          errst_ret (t_attr_copy t t1)
        else 
          TermTFAlt.t_map_errst_unsafe (rewriteT' kn s)  (rewriteF' kn s Svs.empty true) t
      | _ => TermTFAlt.t_map_errst_unsafe (rewriteT' kn s)  (rewriteF' kn s Svs.empty true) t
      end
  | _ => TermTFAlt.t_map_errst_unsafe (rewriteT' kn s) (rewriteF' kn s Svs.empty true) t
  end
with rewriteF' (kn: known_map) (s: state) (av: Svs.t) (sign: bool) (f: term_c) :
  errState (CoqBigInt.t * hashcons_ty ty_c) term_c :=
  match (t_node_of f) with
  | Tcase t1 bl => if negb (enc_ty s (t_ty_of t1)) then 
      TermTFAlt.t_map_sign_errst_unsafe (fun _ => (rewriteT' kn s)) (rewriteF' kn s av) sign f
    else
      t1 <- rewriteT' kn s t1 ;;
    let av' := Mvs.set_diff _ _ av (t_vars t1) in
    let mk_br (x: option term_c * Mls.t (list vsymbol * term_c)) br :=
        let '(w, m) := x in
        let b1 := t_view_branch br in
        let p := fst b1 in
        let e := snd b1 in
        (*rewriteF*)
        e <- rewriteF' kn s av' sign e ;;
        match (pat_node_of p) with
        | Papp cs pl => 
          (**)
          let get_var p : errorM vsymbol := match (pat_node_of p) with
            (*TODO: can we prove that this is well-typed? Using unsafe t_app1 instead of fs_app*)
            | Pvar v => err_ret v
            | _ => throw (UnsupportedTerm (f, uncompiled))
          end
          in
          vs <- errst_lift2 (errorM_list (map get_var pl)) ;;
          errst_ret (w, Mls.add cs (vs, e) m)
        | Pwild => errst_ret (Some e, m)
        | _ => errst_throw (UnsupportedTerm (f, uncompiled))
        end
    in
    wm <- foldl_errst mk_br bl (None, Mls.empty) ;;
    let '(w, m) := wm in
    let find x :=
      let cs := fst x in
      vle <-
        match Mls.find_opt cs m with
        | Some x => errst_ret x
        | None =>
          let get_var pj := 
            t1 <- errst_tup2 (t_app_infer pj [t1]);;
            ty <- errst_lift2 (t_type t1) ;;
            errst_tup1 (errst_lift1 (create_vsymbol (id_fresh1 "w") ty)) in
          vs <- errst_lift2 (Mls.find _ cs s.(cp_map)) ;;
          l <- errst_list (map get_var vs) ;;
          w1 <- errst_lift2 (option_get w) ;;
          errst_ret (l, w1)
        end ;;
      let '(vl, e) := vle in
      ls <- errst_lift2 (Mls.find _ cs s.(cc_map)) ;;
      hd <- errst_tup2 (t_app ls (List.map t_var vl) (t_ty_of t1)) ;;
      match t_node_of t1 with
      | Tvar v =>
        if Svs.mem v av then
          errst_lift2 
          (hd <- t_let_close_simp v hd e;; 
            (if sign
            then t_forall_close_simp vl [] hd
            else t_exists_close_simp vl [] hd))%err
        else
          hd <- errst_tup2 (t_equ t1 hd) ;; 
          errst_lift2 (if sign
          then t1 <- (t_implies_simp hd e) ;; t_forall_close_simp vl [] t1
          else t1 <- (t_and_simp     hd e) ;; t_exists_close_simp vl [] t1)%err
      | _ => 
        hd <- errst_tup2 (t_equ t1 hd) ;; 
        errst_lift2 (if sign
        then t1 <- (t_implies_simp hd e) ;; t_forall_close_simp vl [] t1
        else t1 <- (t_and_simp     hd e) ;; t_exists_close_simp vl [] t1)%err
      end
    in
    ts <- errst_lift2 match t_ty_of t1 with
      | Some ty =>
        match ty_node_of ty with
        | Tyapp ts _ => err_ret ts
        | _ => throw (UnsupportedTerm (f, uncompiled))
        end
      | None => throw (UnsupportedTerm (f, uncompiled))
      end ;;
    (*TODO: why is op used for? when is and vs or? before implication?*)
    let op := if sign then t_and_simp else t_or_simp in
    res <- map_join_left_errst t_true (*JOSH: added*) find (fun x y => errst_lift2 (op x y)) 
      (find_constructors kn ts) ;;
    (* Preserve attributes and location of f *)
    errst_ret (t_attr_copy f res)
  | Tquant q bf =>
    if (is_forall q && sign) || (is_exists q && negb sign) then
      let '(vl, tr, f1, close) := t_view_quant_cb bf in
      tr <- TermTFAlt.tr_map_errst (rewriteT' kn s) (rewriteF' kn s Svs.empty sign) tr ;;
      let av := fold_right Svs.add av vl in
      f1 <- rewriteF' kn s av sign f1 ;;
      (* Preserve attributes and location of f *)
      c <- errst_lift2 (close vl tr f1) ;;
      t1 <- errst_lift2 (t_quant_simp1 q c) ;;
      errst_ret (t_attr_copy f t1)
    else
      TermTFAlt.t_map_sign_errst_unsafe (fun _ => rewriteT' kn s) (rewriteF' kn s Svs.empty) sign f
  | Tbinop o _ _ =>
    if (is_and o && sign) || (is_or o && negb sign) then
      TermTFAlt.t_map_sign_errst_unsafe (fun _ => rewriteT' kn s) (rewriteF' kn s av) sign f
    else 
      TermTFAlt.t_map_sign_errst_unsafe (fun _ => rewriteT' kn s) (rewriteF' kn s Svs.empty) sign f
  | Tlet t1 tb =>
    (*Flet*)
    let av := Mvs.set_diff _ _ av (t_vars t1) in
    TermTFAlt.t_map_sign_errst_unsafe (fun _ => rewriteT' kn s) (rewriteF' kn s av) sign f
  | _ => TermTFAlt.t_map_sign_errst_unsafe (fun _ => rewriteT' kn s) (rewriteF' kn s Svs.empty) sign f
  end.