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
  tp_map : Mid.t (decl*theory_c); (* skipped tuple symbols *)
  inf_ts : Sts.t;               (* infinite types *)
  ma_map : Mts.t (list bool );     (* material type arguments *)
  keep_e : bool;                (* keep monomorphic enumeration types *)
  keep_r : bool;                (* keep non-recursive records *)
  keep_m : bool;                (* keep monomorphic data types *)
  no_ind : bool;                (* do not generate indexing functions *)
  no_inv : bool;                (* do not generate inversion axioms *)
  no_sel : bool;                (* do not generate selector *)
}.

(*TODO use coq-record-update?*)
Definition state_with_mt_map (s: state) (mt_map: Mts.t lsymbol) : state :=
  {| mt_map := mt_map; cc_map := s.(cc_map); cp_map := s.(cp_map);
    pp_map := s.(pp_map); kept_m := s.(kept_m); tp_map := s.(tp_map);
    inf_ts := s.(inf_ts); ma_map:= s.(ma_map) ; keep_e := s.(keep_e);
    keep_r := s.(keep_r); keep_m := s.(keep_m); no_ind := s.(no_ind);
    no_inv := s.(no_inv); no_sel := s.(no_sel)|}.

Definition state_with_cc_map (s: state) cc_map : state :=
  {| mt_map := s.(mt_map); cc_map := cc_map; cp_map := s.(cp_map);
    pp_map := s.(pp_map); kept_m := s.(kept_m); tp_map := s.(tp_map);
    inf_ts := s.(inf_ts); ma_map:= s.(ma_map) ; keep_e := s.(keep_e);
    keep_r := s.(keep_r); keep_m := s.(keep_m); no_ind := s.(no_ind);
    no_inv := s.(no_inv); no_sel := s.(no_sel)|}.

Definition state_with_cp_map (s: state) (cp_map: Mls.t (list lsymbol)) : state :=
  {| mt_map := s.(mt_map); cc_map := s.(cc_map); cp_map := cp_map;
    pp_map := s.(pp_map); kept_m := s.(kept_m); tp_map := s.(tp_map);
    inf_ts := s.(inf_ts); ma_map:= s.(ma_map) ; keep_e := s.(keep_e);
    keep_r := s.(keep_r); keep_m := s.(keep_m); no_ind := s.(no_ind);
    no_inv := s.(no_inv); no_sel := s.(no_sel)|}.

Definition state_with_pp_map (s: state) (pp_map: Mls.t lsymbol) : state :=
  {| mt_map := s.(mt_map); cc_map := s.(cc_map); cp_map := s.(cp_map);
    pp_map := (pp_map); kept_m := s.(kept_m); tp_map := s.(tp_map);
    inf_ts := s.(inf_ts); ma_map:= s.(ma_map) ; keep_e := s.(keep_e);
    keep_r := s.(keep_r); keep_m := s.(keep_m); no_ind := s.(no_ind);
    no_inv := s.(no_inv); no_sel := s.(no_sel)|}.

Definition state_with_kept_m (s: state) kept_m : state :=
  {| mt_map := s.(mt_map); cc_map := s.(cc_map); cp_map := s.(cp_map);
    pp_map := s.(pp_map); kept_m := kept_m; tp_map := s.(tp_map);
    inf_ts := s.(inf_ts); ma_map:= s.(ma_map) ; keep_e := s.(keep_e);
    keep_r := s.(keep_r); keep_m := s.(keep_m); no_ind := s.(no_ind);
    no_inv := s.(no_inv); no_sel := s.(no_sel)|}.

Definition state_with_tp_map (s: state) tp_map : state :=
  {| mt_map := s.(mt_map); cc_map := s.(cc_map); cp_map := s.(cp_map);
    pp_map := s.(pp_map); kept_m := s.(kept_m); tp_map := (tp_map);
    inf_ts := s.(inf_ts); ma_map:= s.(ma_map) ; keep_e := s.(keep_e);
    keep_r := s.(keep_r); keep_m := s.(keep_m); no_ind := s.(no_ind);
    no_inv := s.(no_inv); no_sel := s.(no_sel)|}.

Definition state_with_inf_ts (s: state) inf_ts : state :=
  {| mt_map := s.(mt_map); cc_map := s.(cc_map); cp_map := s.(cp_map);
    pp_map := s.(pp_map); kept_m := s.(kept_m); tp_map := s.(tp_map);
    inf_ts := inf_ts; ma_map:= s.(ma_map) ; keep_e := s.(keep_e);
    keep_r := s.(keep_r); keep_m := s.(keep_m); no_ind := s.(no_ind);
    no_inv := s.(no_inv); no_sel := s.(no_sel)|}.

Definition state_with_ma_map (s: state) ma_map : state :=
  {| mt_map := s.(mt_map); cc_map := s.(cc_map); cp_map := s.(cp_map);
    pp_map := s.(pp_map); kept_m := s.(kept_m); tp_map := s.(tp_map);
    inf_ts := s.(inf_ts); ma_map:= ma_map ; keep_e := s.(keep_e);
    keep_r := s.(keep_r); keep_m := s.(keep_m); no_ind := s.(no_ind);
    no_inv := s.(no_inv); no_sel := s.(no_sel)|}.

Definition state_with_keep_e (s: state) keep_e : state :=
  {| mt_map := s.(mt_map); cc_map := s.(cc_map); cp_map := s.(cp_map);
    pp_map := s.(pp_map); kept_m := s.(kept_m); tp_map := s.(tp_map);
    inf_ts := s.(inf_ts); ma_map:= s.(ma_map) ; keep_e := keep_e;
    keep_r := s.(keep_r); keep_m := s.(keep_m); no_ind := s.(no_ind);
    no_inv := s.(no_inv); no_sel := s.(no_sel)|}.

Definition state_with_keep_r (s: state) keep_r : state :=
  {| mt_map := s.(mt_map); cc_map := s.(cc_map); cp_map := s.(cp_map);
    pp_map := s.(pp_map); kept_m := s.(kept_m); tp_map := s.(tp_map);
    inf_ts := s.(inf_ts); ma_map:= s.(ma_map) ; keep_e := s.(keep_e);
    keep_r := keep_r; keep_m := s.(keep_m); no_ind := s.(no_ind);
    no_inv := s.(no_inv); no_sel := s.(no_sel)|}.

Definition state_with_keep_m (s: state) keep_m : state :=
  {| mt_map := s.(mt_map); cc_map := s.(cc_map); cp_map := s.(cp_map);
    pp_map := s.(pp_map); kept_m := s.(kept_m); tp_map := s.(tp_map);
    inf_ts := s.(inf_ts); ma_map:= s.(ma_map) ; keep_e := s.(keep_e);
    keep_r := s.(keep_r); keep_m := keep_m; no_ind := s.(no_ind);
    no_inv := s.(no_inv); no_sel := s.(no_sel)|}.

Definition state_with_no_ind (s: state) no_ind : state :=
  {| mt_map := s.(mt_map); cc_map := s.(cc_map); cp_map := s.(cp_map);
    pp_map := s.(pp_map); kept_m := s.(kept_m); tp_map := s.(tp_map);
    inf_ts := s.(inf_ts); ma_map:= s.(ma_map) ; keep_e := s.(keep_e);
    keep_r := s.(keep_r); keep_m := s.(keep_m); no_ind := no_ind;
    no_inv := s.(no_inv); no_sel := s.(no_sel)|}.

Definition state_with_no_inv (s: state) no_inv : state :=
  {| mt_map := s.(mt_map); cc_map := s.(cc_map); cp_map := s.(cp_map);
    pp_map := s.(pp_map); kept_m := s.(kept_m); tp_map := s.(tp_map);
    inf_ts := s.(inf_ts); ma_map:= s.(ma_map) ; keep_e := s.(keep_e);
    keep_r := s.(keep_r); keep_m := s.(keep_m); no_ind := s.(no_ind);
    no_inv := no_inv; no_sel := s.(no_sel)|}.

Definition state_with_no_sel (s: state) no_sel : state :=
  {| mt_map := s.(mt_map); cc_map := s.(cc_map); cp_map := s.(cp_map);
    pp_map := s.(pp_map); kept_m := s.(kept_m); tp_map := s.(tp_map);
    inf_ts := s.(inf_ts); ma_map:= s.(ma_map) ; keep_e := s.(keep_e);
    keep_r := s.(keep_r); keep_m := s.(keep_m); no_ind := s.(no_ind);
    no_inv := s.(no_inv); no_sel := no_sel|}.


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
        if (ls.(ls_proj) && enc_ty s (t_ty_of arg)) then
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

Definition add_selector_aux {A: Type} (st: state * task) (ts: tysymbol_c) (ty: ty_c) (csl: list (lsymbol * A)) :
  errState (CoqBigInt.t * hashcons_full) (state * task) :=
  let s := fst st in
  let tsk := snd st in
  if s.(no_sel) then errst_ret st else
  (* declare the selector function *)
  let mt_id := id_derive1 ("match_"%string ++ (ts_name_of ts).(id_string))%string (ts_name_of ts) in
  v <- errst_tup1 (errst_lift1 (create_tvsymbol (id_fresh1 "a"))) ;;
  mt_ty <- errst_tup2 (full_of_ty (errst_lift1 (ty_var v))) ;;
  let mt_al := ty :: rev_map (fun _ => mt_ty) csl in
  mt_ls <- errst_tup1 (errst_lift1 (create_fsymbol1 mt_id mt_al mt_ty)) ;;
  let mt_map := Mts.add ts mt_ls s.(mt_map) in
  task  <- add_param_decl tsk mt_ls ;;
  (* define the selector function *)
  let mt_vs _ := create_vsymbol (id_fresh1 "z") mt_ty in
  mt_vl <- errst_tup1 (errst_lift1 (st_list (rev_map mt_vs csl))) ;;
  let mt_tl := rev_map t_var mt_vl in
  let mt_add tsk x t :=
    let cs := fst x in
    let id := (mt_ls.(ls_name).(id_string) ++ "_"%string ++ cs.(ls_name).(id_string))%string in
    pr <- errst_tup1 (errst_lift1 (create_prsymbol (id_derive1 id cs.(ls_name)))) ;;
    vl <- errst_tup1 (errst_lift1 (st_list (rev_map (create_vsymbol (id_fresh1 "u")) cs.(ls_args))));;
    newcs <- errst_lift2 (Mls.find _ cs s.(cc_map)) ;;
    v <- errst_lift2 (option_get cs.(ls_value)) ;;
    hd <- errst_tup2 (full_of_ty (fs_app newcs (rev_map t_var vl) v)) ;;
    hd <- errst_tup2 (full_of_ty (fs_app mt_ls (hd::mt_tl) mt_ty)) ;;
    let vl := List.rev_append mt_vl (List.rev vl) in
    e <- errst_tup2 (full_of_ty (t_equ hd t)) ;;
    ax <- errst_lift2 (t_forall_close vl [] e);;
    add_prop_decl tsk Paxiom pr ax
  in
  (*TODO: write non-err version*)
  task <- fold_left2_errst' mt_add task csl mt_tl ;;
  errst_ret (state_with_mt_map s mt_map, task).

(*Don't need selector for ADT with only 1 constructor - why?*)
Definition add_selector {A: Type} (acc : state * task) (ts: tysymbol_c) (ty: ty_c) (x: list (lsymbol * A)) :
  errState (CoqBigInt.t * hashcons_full) (state * task) :=
  match x with
  | [_] => errst_ret acc
  | csl => add_selector_aux acc ts ty csl
  end.

Definition add_indexer_aux {A: Type} (st: state * task) (ts: tysymbol_c) (ty: ty_c) (csl: list (lsymbol * A)) :
  errState (CoqBigInt.t * hashcons_full) (state * task) :=
  let s := fst st in
  let tsk := snd st in
  (* declare the indexer function *)
  let mt_id := id_derive1 ("index_" ++ (ts_name_of ts).(id_string))%string (ts_name_of ts) in
  mt_ls <- errst_tup1 (errst_lift1 (create_fsymbol1 mt_id [ty] ty_int)) ;;
  task <- add_param_decl tsk mt_ls ;;
  (* define the indexer function - NOTE: we do without mutable reference *)
  (*let index = ref (-1) in*)
  let mt_add tsk x (index : CoqBigInt.t) :=
    let cs := fst x in
    (* incr index; *)
    let id := (mt_ls.(ls_name).(id_string) ++ "_" ++ cs.(ls_name).(id_string))%string in
    pr <-  errst_tup1 (errst_lift1 (create_prsymbol (id_derive1 id cs.(ls_name)))) ;;
    vl <- (errst_tup1 (errst_lift1 (st_list (rev_map (create_vsymbol (id_fresh1 "u")) cs.(ls_args))))) ;;
    newcs <- errst_lift2 (Mls.find _ cs s.(cc_map)) ;;
    o <- errst_lift2 (option_get cs.(ls_value)) ;;
    hd <- errst_tup2 (full_of_ty (fs_app newcs (rev_map t_var vl) o));; 
    t1 <- errst_tup2 (full_of_ty (fs_app mt_ls [hd] ty_int)) ;;
    ax <- errst_tup2 (full_of_ty (t_equ t1 (t_int_const index))) ;; (*safe to use int vs nat*)
    ax <- errst_lift2 (t_forall_close (List.rev vl) [[hd]] ax) ;;
    add_prop_decl tsk Paxiom pr ax
  in
  task <- fold_left2_errst' mt_add task csl (IntFuncs.iota2 (IntFuncs.int_length csl)) ;;
  errst_ret (s, task).

Definition add_discriminator {A: Type} (st: state * task) (ts : tysymbol_c) (ty : ty_c) 
  (csl : list (lsymbol * A)) : errState (CoqBigInt.t * hashcons_full) (state * task) :=
  let s := fst st in
  let tsk := snd st in
  let d_add x task y :=
    let c1 := fst x in
    let c2 := fst y in
    let id := (c1.(ls_name).(id_string) ++ "_" ++ c2.(ls_name).(id_string))%string in
    pr <- errst_tup1 (errst_lift1 (create_prsymbol (id_derive1 id (ts_name_of ts)))) ;;
    ul <- errst_tup1 (errst_lift1 (st_list (rev_map (create_vsymbol (id_fresh1 "u")) c1.(ls_args)))) ;;
    vl <- errst_tup1 (errst_lift1 (st_list (rev_map (create_vsymbol (id_fresh1 "v")) c2.(ls_args)))) ;;
    newc1 <- errst_lift2 (Mls.find _ c1 s.(cc_map)) ;;
    newc2 <- errst_lift2 (Mls.find _ c2 s.(cc_map)) ;;
    t1 <- errst_tup2 (full_of_ty (fs_app newc1 (rev_map t_var ul) ty)) ;;
    t2 <- errst_tup2 (full_of_ty (fs_app newc2 (rev_map t_var vl) ty)) ;;
    ax <- errst_tup2 (full_of_ty (t_neq t1 t2)) ;;
    ax <- errst_lift2 (t_forall_close (List.rev vl) [[t2]] ax) ;;
    ax <- errst_lift2 (t_forall_close (List.rev ul) [[t1]] ax) ;;
    add_prop_decl task Paxiom pr ax
  in
  let fix dl_add (tsk : task) l : errState (CoqBigInt.t * hashcons_full) task :=
    match l with
    | c :: cl => 
      t <- (foldl_errst (d_add c) cl tsk) ;;
      dl_add t cl
    | _ => errst_ret tsk
    end
  in
  t' <- dl_add tsk csl ;;
  errst_ret (s, t').

(*TODO: why length 16? Maybe discriminators get too large?*)
(* discriminator is only added if indexers not generated
  think that indexers imply discriminator - because we have (e.g.
  axiom index_list_cons: forall u1, u2, index_list (cons' (u1, u2)) = 0
axiom index_list_nil: index_list nil' = 1
so clearly cons' <> nil (or else 1 = 0))*)
Definition add_indexer {A: Type} (acc : state * task) (ts : tysymbol_c) (ty: ty_c)
  (l: list (lsymbol * A)) : errState (CoqBigInt.t * hashcons_full) (state * task) :=
  match l with
  | [_] => errst_ret acc
  | csl => if negb (fst acc).(no_ind) then add_indexer_aux acc ts ty csl
           else if CoqBigInt.lt (IntFuncs.int_length csl) CoqBigInt.sixteen 
            then add_discriminator acc ts ty csl
           else errst_ret acc
  end.

Local Open Scope state_scope.
Definition complete_projections (csl: list (lsymbol * list (option lsymbol))) : 
  ctr (list (lsymbol * list (option lsymbol)))  :=
  let conv_c x :=
    let c := fst x in
    let pjl := snd x in
    let conv_p i (t : option lsymbol * ty_c) := 
      match t with
      | (None, ty) =>
        (*don't have printf - but we need to convert CoqBigInt.t to string*)
        let id := (c.(ls_name).(id_string) ++ "_proj_" ++ (CoqBigInt.to_string (CoqBigInt.succ i)))%string in
         (* let id = Printf.sprintf "%s_proj_%d" c.ls_name.id_string (i+1) in *)
        let id := id_derive1 id c.(ls_name) in
          let v := (*they use option_get but I will use default - prove not reached*)
            match  c.(ls_value) with
            | Some t => t
            | None => ty_int
            end in
          s <- create_fsymbol2 CoqBigInt.zero true id [v] ty ;;
          st_ret (Some s)
         (* Some (create_fsymbol1 ~proj:true id [Option.get c.ls_value] ty) *)
      | (pj, _) => st_ret pj
      end
    in
    l <- st_list (IntFuncs.mapi conv_p (combine pjl c.(ls_args))) ;;
    st_ret (c, l)
  in
 st_list (List.map conv_c csl).

(*Note: don't care about meta definitions, only proving soundness*)
Axiom meta_model_projection : meta.

Definition add_meta_model_projection tsk ls :=
  add_meta tsk meta_model_projection [MAls ls].
Local Open Scope errst_scope.
Definition add_projections {A B: Type} (st : state * task) (_ts : A) (_ty : B) 
  (csl: list (lsymbol * list (option lsymbol))) :
  errState (CoqBigInt.t * hashcons_full) (state * task) :=
  let s := fst st in
  let tsk := snd st in
  (* declare and define the projection functions *)
  let pj_add x y :=
    let '(cp_map,pp_map,tsk) := x in
    let '(cs,pl) := y in
    vl <- errst_tup1 (errst_lift1 (st_list (map (create_vsymbol (id_fresh1 "u")) cs.(ls_args)))) ;;
    let tl := map t_var vl in
    cc <- errst_lift2 (Mls.find _ cs s.(cc_map)) ;;
    v <- errst_lift2 (option_get cs.(ls_value)) ;;
    hd <- errst_tup2 (full_of_ty (fs_app cc tl v)) ;;
    let add (x: list lsymbol * Mls.t lsymbol * task) (t: term_c) (pj: option lsymbol) :
      errState (CoqBigInt.t * hashcons_full) (list lsymbol * Mls.t lsymbol * task) :=
      let '(pjl,pp_map,tsk) := x in
      pj <- errst_lift2 (option_get pj) ;;
      lspp <-
        match Mls.find_opt pj pp_map with
        | Some pj => errst_ret (pj,pp_map)
        | None =>
          let id := (id_clone1 None Sattr.empty pj.(ls_name)) in
          ls <- errst_tup1 (errst_lift1 (create_lsymbol1 id pj.(ls_args) pj.(ls_value))) ;;
          errst_ret (ls,Mls.add pj ls pp_map)
        end ;;
      let '(ls,pp_map) := lspp in
      tsk <- add_param_decl tsk ls ;;
      let id := id_derive1 (ls.(ls_name).(id_string) ++ "'def")%string ls.(ls_name) in
      pr <- errst_tup1 (errst_lift1 (create_prsymbol id)) ;;
      hh <- errst_tup2 (full_of_ty (t_app ls [hd] (t_ty_of t)));;
      hht <- errst_tup2 (full_of_ty (t_equ hh t)) ;;
      ax <- errst_lift2 (t_forall_close vl [] hht) ;;
      tsk <- add_prop_decl tsk Paxiom pr ax ;;
      tsk <- errst_tup2 (add_meta_model_projection tsk ls) ;;
      errst_ret (ls::pjl,pp_map,tsk)
    in
    res <- fold_left2_errst' add ([],pp_map,tsk) tl pl ;;
    let '(pjl,pp_map,tsk) := res in
    errst_ret (Mls.add cs (rev pjl) cp_map, pp_map, tsk)
  in
  csl <- errst_tup1 (errst_lift1 (complete_projections csl));;
  res <- foldl_errst pj_add csl (s.(cp_map), s.(pp_map), tsk) ;;
  let '(cp_map, pp_map, tsk) := res in
  errst_ret (state_with_cp_map (state_with_pp_map s pp_map) cp_map, tsk).

Definition add_inversion {A: Type} (st: state * task) (ts: tysymbol_c) (ty: ty_c) (csl: list (lsymbol * A)) 
  : errState (CoqBigInt.t * hashcons_full) (state * task) :=
  let s := fst st in
  let tsk := snd st in
  if s.(no_inv) then errst_ret (s, tsk) else
  (* add the inversion axiom *)
  let ax_id := ((ts_name_of ts).(id_string) ++ "_inversion")%string in
  ax_pr <- errst_tup1 (errst_lift1 (create_prsymbol (id_derive1 ax_id (ts_name_of ts)))) ;;
  ax_vs <- errst_tup1 (errst_lift1 (create_vsymbol (id_fresh1 "u") ty)) ;;
  let ax_hd := t_var ax_vs in
  let mk_cs x :=
    let cs := fst x in
    pjl <- errst_lift2 (Mls.find _ cs s.(cp_map)) ;;
    let app pj := t_app_infer pj [ax_hd] in
    cs <- errst_lift2 (Mls.find _ cs s.(cc_map)) ;;
    errst_tup2 (full_of_ty (
      pjl' <- (errst_list (map app pjl)) ;;
      c <- (fs_app cs pjl' ty) ;;
      t_equ ax_hd c
    ))
    in
  ax_f <- map_join_left_errst t_true mk_cs (fun x y => errst_lift2 (t_or x y)) csl;;
  ax_f <- errst_lift2 (t_forall_close [ax_vs] [] ax_f) ;;
  pd <- add_prop_decl tsk Paxiom ax_pr ax_f ;;
  errst_ret (s, pd).

Definition kept_no_case {A B: Type} (used : Sid.t) s (x : tysymbol_c * list (A * list B)) :=
  match x with
  | (ts, [(_ , _ :: _)]) => s.(keep_r) && negb (Sid.mem (ts_name_of ts) used)
  | (ts, csl) =>
    match (ts_args_of ts) with
    | nil => s.(keep_e) && forallb (fun x => null (snd x)) csl &&
       negb (Mts.mem ts s.(kept_m))
    | _ => false
    end
  end.

Definition add_axioms (used: Sid.t) (st: state * task) 
  (d: tysymbol_c * list (lsymbol * list (option lsymbol))) :
  errState (CoqBigInt.t * hashcons_full) (state * task) :=
  let s := fst st in
  let tsk := snd st in
  let ts := fst d in
  let csl := snd d in
  l <- errst_tup2 (full_of_ty (errst_lift1 (st_list (map ty_var (ts_args_of ts))))) ;;
  ty <- errst_tup2 (full_of_ty (ty_app ts l)) ;;
  if kept_no_case used s d then
    (* for kept enums and records, we still use the selector function, but
       always use the non-encoded projections and constructors *)
    s <- errst_lift2(
      let fold_c s x :=
        let '(c, pjs) := x in
        (pjs <-  errorM_list (map option_get pjs) ;;
        let cc_map := Mls.add c c s.(cc_map) in
        let cp_map := Mls.add c pjs s.(cp_map) in
        let fold_pj pp_map pj := Mls.add pj pj pp_map in
        let pp_map := fold_left fold_pj pjs s.(pp_map) in
        err_ret (state_with_pp_map (state_with_cp_map (state_with_cc_map s cc_map) cp_map) pp_map))%err
        (* { s with cc_map; cp_map; pp_map } *)
      in
      foldl_err fold_c csl s)
    ;;
    add_selector (s, tsk) ts ty csl
  else if negb (null (ts_args_of ts)) || negb (Mts.mem ts s.(kept_m)) then
    (* declare constructors as abstract functions *)
    let cs_add x y :=
      let '(s,tsk) := x in
      let cs := fst y in
      let id := id_clone1 None Sattr.empty cs.(ls_name) in
      ls <- errst_tup1 (errst_lift1 (create_lsymbol1 id cs.(ls_args) cs.(ls_value))) ;;
      d <- add_param_decl tsk ls ;;
      errst_ret (state_with_cc_map s (Mls.add cs ls s.(cc_map)), d)
      (* { s with cc_map = Mls.add cs ls s.cc_map },add_param_decl tsk ls *)
    in
    st1 <- foldl_errst cs_add csl (s,tsk) ;;
    (* add selector, projections, and inversion axiom *)
    st2 <- add_selector st1 ts ty csl ;;
    st3 <- add_indexer st2 ts ty csl ;;
    st4 <- add_projections st3 ts ty csl ;;
    add_inversion st4 ts ty csl
  else errst_ret (s,tsk).

(*Separate out nested rec: hard for coq to deal with inline mutual recursion*)
Section Fix.
Context {A: Type}.
Variable (mts: Mts.t (list (lsymbol * A))) (s: state).
Local Open Scope err_scope.

(*use fuel*)
(*TODO: fuel?
  Why does this terminate? Idea: csl must be constructor list for some type, so by well-foundedness
    of ADTs, terminates.
    Not going to prove this, just give fuel as with type_inhab*)
Definition mat_ts sts ts csl (z: CoqBigInt.t) :=
  @IntFuncs.int_rect (fun _ => (*forall A, state -> Mts.t (list (lsymbol * A)) -> *)
    Sts.t -> tysymbol_c -> list (lsymbol * A) -> errorM (list bool))
  (*neg case*)
  (fun _ _ sts stv ty  => throw Exit)
  (*zero case*)
  (fun sts stv ty => throw Exit)
  (*pos case*)
  (fun _ _ _ rec sts stv ty =>
    let fix mat_ty sts stv ty { struct ty } : errorM Stv.t := 
    match (ty_node_of ty) with
    | Tyvar tv => err_ret (Stv.add tv stv)
    | Tyapp ts tl =>
        if Sts.mem ts sts then throw Exit else (* infinite type *)
        matl <- 
          match Mts.find_opt ts s.(ma_map) with
          | Some y => err_ret y
          | None => rec sts ts (Mts.find_def _ [] ts mts)
          end ;;
        let add s ty (mat : bool) := if mat then mat_ty sts s ty else err_ret s in
        fold_left2_err' add stv tl matl
    end in
    let sts := Sts.add ts sts in
    let add s x := foldl_err (mat_ty sts) (fst x).(ls_args) s in
    stv <- foldl_err add csl Stv.empty ;;
    err_ret (map (Stv.contains stv) (ts_args_of ts))
  ) z sts ts csl.

End Fix.

(*We don't care about the values of these (NOTE: OCaml functions are effectful, this isn't quite sound)*)
Axiom meta_infinite : meta.
Axiom meta_material : meta.

Definition add_tags {A: Type} (mts: Mts.t (list (lsymbol * A))) (st: state * task) 
  (x: tysymbol_c * list (lsymbol * A)) : errState (hashcons_full) (state * task) :=
  let s := fst st in
  let tsk := snd st in
  let ts := fst x in
  let csl := snd x in
  errst_trywith (*try*) (fun _ =>
    matl <- errst_lift2 (mat_ts mts s s.(inf_ts) ts csl CoqBigInt.sixteen) ;;
    let s := state_with_ma_map s (Mts.add ts matl s.(ma_map)) in
    let add_material tsk (m: bool) (c: CoqBigInt.t) :=
      if m then add_meta tsk meta_material [MAts ts; MAint c] else errst_ret tsk
    in
    l <- fold_left2_errst' add_material tsk matl (IntFuncs.iota2 (IntFuncs.int_length matl)) ;;
    errst_ret (s, l))
  (*with*)
  Exit
  (*->*)
  (fun _ => let s := state_with_inf_ts s (Sts.add ts s.(inf_ts)) in
    l <- add_meta tsk meta_infinite [MAts ts] ;;
    errst_ret (s, l)).


Definition has_nested_use {A: Type} (sts : Sts.t) (csl : list (lsymbol * A)) : bool :=
  let check_c x :=
    let check_arg ty := match ty_node_of ty with
    | Tyapp _ tl => existsb (ty_s_any (fun_flip Sts.mem sts)) tl
    | Tyvar _ => false
    end in
    existsb check_arg (fst x).(ls_args)
  in
  existsb check_c csl.

Definition comp_aux (t: task_hd) (st : state * task) : 
  errState (CoqBigInt.t * hashcons_full) (state * task) := 
  let s := fst st in
  let tsk := snd st in
  match td_node_of t.(task_decl) with
  | Decl d =>
    match d.(d_node) with
    | Ddata dl =>
      let used := get_used_syms_decl d in
      let sts := fold_left (fun acc x => Sts.add (fst x) acc) dl Sts.empty in
      let fold_kept_m s d : errorHashconsT ty_c state :=
        let '(ts,csl) := d in
        if has_nested_use sts csl then errst_ret (state_with_kept_m s (Mts.remove _ ts s.(kept_m)))
        else if null (ts_args_of ts) && s.(keep_m) && negb (kept_no_case used s d) then
          t1 <- (ty_app ts []) ;;
          errst_ret (state_with_kept_m s (Mts.add ts (Sty.singleton t1) s.(kept_m)))
        else errst_ret s
      in
      s <- errst_tup2 (full_of_ty (foldl_errst fold_kept_m dl s)) ;;
      (* add projections to records with keep_recs *)
      let conv_t d : ctr (tysymbol_c *(list (lsymbol * list (option lsymbol)))) :=
        let '(ts, csl) := d in
        (* complete_projections can only be called on records or enums, so it
            won't introduced ill-formed projections *)
        if kept_no_case used s d then (r <- complete_projections csl ;; st_ret (ts, r))%state else st_ret d
      in
      dl <- errst_tup1 (errst_lift1 (st_list (map conv_t dl))) ;;
      (* add type declarations *)
      let concrete d := Mts.mem (fst d) s.(kept_m) || kept_no_case used s d in
      let '(dl_concr, dl_abs) := List.partition concrete dl in
      tsk <- foldl_errst (fun t x => add_ty_decl t (fst x)) dl_abs tsk ;;
      tsk <- if null dl_concr then errst_ret tsk else add_data_decl tsk dl_concr;;
      (* add needed functions and axioms *)
      r1 <- foldl_errst (add_axioms used) dl (s,tsk) ;;
      (* add the tags for infinite types and material arguments *)
      let mts := fold_right (fun x acc => Mts.add (fst x) (snd x) acc) Mts.empty dl in
      (* return the updated state and task *)
      errst_tup2 (foldl_errst (add_tags mts) dl r1)
      (* return the updated state and task *)
      (* s, tsk *)
    | _ =>
        let fnT := rewriteT' t.(task_known) s in
        let fnF := rewriteF' t.(task_known) s Svs.empty true in
        d1 <- (errst_assoc5 (errst_tup1 (errst_tup1 (DeclTFAlt.decl_map (fun x => errst_tup1 (fnT x)) (fun x => errst_tup1 (fnF x)) d)))) ;;
        d1 <- add_decl tsk  d1;;
        errst_ret (s, d1)
    end
  | _ =>
    d1 <- add_tdecl tsk t.(task_decl) ;;
    errst_ret (s, d1) 
  end.

(*NOTE: UNSOUND - tuple_theory is stateful, although it is memoized so it does return
  the same value if called multiple times. But we really don't want to have to reason about it*)
Axiom tuple_theory : CoqBigInt.t -> theory_c.

Definition comp (t: task_hd) (st: state * task) : errState (CoqBigInt.t * hashcons_full) (state * task) :=
  let s := fst st in
  let tsk := snd st in
  (*Separate out tuple case separately to avoid repeating all times*)

  b <- errst_lift2 
    match td_node_of (t.(task_decl)) with
    | Use th =>
      match th_decls_of th with
      | [x] =>
        match td_node_of x with
        | Decl d =>
          match d.(d_node) with
          | Ddata [(ts, _)] => is_ts_tuple ts   
          | _ => err_ret false
          end
        | _ => err_ret false
        end
      | _ => err_ret false
      end
    | _ => err_ret false
    end ;;
  if (b : bool) then errst_ret (s, tsk) else
  match td_node_of (t.(task_decl)) with
  | Decl d =>
    b <- errst_lift2
    match d.(d_node) with
    | Ddata [(ts, _)] => (b <- is_ts_tuple ts ;; if (b : bool) then err_ret (Some ts) else err_ret None)%err
    | _ => err_ret None
    end ;;
    match b with
    | Some ts => 
      let th := tuple_theory (IntFuncs.int_length (ts_args_of ts)) in
      let tp_map := Mid.add (ts_name_of ts) (d,th) s.(tp_map) in
      errst_ret (state_with_tp_map s tp_map , tsk)
    | None => (*unlike them, do in 2 pieces to avoid mutable state
        (seems like a bad idea to use a stateful update function
        in a set diff)*)
      let m := Mid.inter (fun _ x _ => Some x) s.(tp_map) (get_used_syms_decl d) in
      f <- foldl_errst (fun x y =>
        let '(rstate, rtask) := x in
        let '(_, (d, th)) := y in
        t1 <- (add_decl None d) ;;
        t <- errst_lift2 (option_get t1) ;;
        c <- comp_aux t (rstate,rtask) ;;
        let '(s,tsk) := c in
        u <- errst_tup2 (full_of_td (errst_lift1 (create_use th))) ;;
        tsk <- add_tdecl tsk u ;;
        errst_ret (s, tsk))  (Mid.bindings m) (s, tsk) ;;
      let (rstate, rtask) := (f : state * task) in
      

      (* let rstate,rtask = ref state, ref task in
      let add _ (d,th) () =
        let t = Option.get (add_decl None d) in
        let state,task = comp_aux t (!rstate,!rtask) in
        let task = add_tdecl task (create_use th) in
        rstate := state ; rtask := task ; None
      in *)
      let tp_map := Mid.diff (fun _ _  _ => None) s.(tp_map) (get_used_syms_decl d) in
      comp_aux t (state_with_tp_map rstate tp_map, rtask)
    end
  | _ => comp_aux t (s,tsk)
  end.

Definition fold_comp st : trans_errst (state * task) :=
  trans_bind
  (init <- errst_tup2 (TaskFuncs.add_meta None meta_infinite [MAts ts_int]) ;;
  init <- errst_tup2 (TaskFuncs.add_meta init meta_infinite [MAts ts_real]) ;;
  init <- errst_tup2 (TaskFuncs.add_meta init meta_infinite [MAts ts_str]) ;;
  TaskFuncs.add_param_decl init ps_equ)
  (fun init => TransDefs.fold_errst comp (st,init)).

Definition on_empty_state {A: Type} (t: state -> trans_errst A) : trans_errst A :=
  TransDefs.on_tagged_ts meta_infinite (fun inf_ts =>
  TransDefs.on_meta meta_material (fun ml =>
    let inf_ts := Sts.union inf_ts (Sts.of_list [ts_real; ts_int; ts_str]) in
    let fold ma_map x := 
      match x with
      | [MAts ts; MAint i] =>
        let ma := match Mts.find_opt ts ma_map with
        | Some l => (*Array.of_list*) l
        | None => IntFuncs.init  (IntFuncs.int_length (ts_args_of ts)) (fun _ => false)
        end in
        let ma := IntFuncs.change_nth ma true i in
        (* ma.(i) <- true; *)
        err_ret (Mts.add ts (*(Array.to_list ma)*) ma ma_map)
      | _ => assert_false "on_empty_state"
      end
    in
    trans_bind
    (errst_lift2 (foldl_err fold ml Mts.empty)) (fun ma_map =>
    let empty_state := {|
      mt_map := Mts.empty; cc_map := Mls.empty; cp_map := Mls.empty;
      pp_map := Mls.empty; kept_m := Mts.empty; tp_map := Mid.empty;
      inf_ts := inf_ts; ma_map := ma_map; keep_e := false; keep_r := false; keep_m := false;
      no_ind := false; no_inv := false; no_sel := false
    |} in 
    t empty_state))).

(* We need to rewrite metas *after* the main pass, because we need to know the
    final state. Some metas may mention symbols declared after the meta. *)

(*Separate out cases, since this is annoying*)
Definition meta_constr_case (s: state) ls : option tysymbol_c :=
  match ls.(ls_value) with
  | Some t =>
    match ty_node_of t with
    | Tyapp ts _ => if CoqBigInt.pos ls.(ls_constr) && negb (Mts.mem ts s.(kept_m)) then Some ts
    else None
    | _ => None
    end
  | _ => None
  end.

Definition meta_proj_case s ls :=
  if ls.(ls_proj) then
    match ls.(ls_args) with
    | [t] =>
      match ty_node_of t with
      | Tyapp ts _ =>
        if negb (Mts.mem ts s.(kept_m)) then Some ts else None
      | _ => None
      end
    | _ => None
    end
  else None.


Definition fold_rewrite_metas (s: state) (t: task_hd) (tsk: task) : 
  errState (CoqBigInt.t * hashcons_full) task
  := match td_node_of (t.(task_decl)) with
  | Meta m mal =>
    let map_arg ma := match ma with
    | MAls ls =>
      (*Case 1: constr*)
      match meta_constr_case s ls with
      | Some ts => MAls (Mls.find_def _ ls ls s.(cc_map))
      | None =>
        match meta_proj_case s ls with
        | Some ts => MAls (Mls.find_def _ ls ls s.(pp_map))
        | None => ma
        end
      end
    | _ => ma
    end in
    errst_tup2 (add_meta tsk m (map map_arg mal))
  | _ =>
    add_tdecl tsk t.(task_decl)
  end.

Definition rewrite_metas (st : state) : trans_errst task := 
  fold_errst (fold_rewrite_metas st) None.

Definition eliminate_match : trans_errst task :=
  bind_errst (compose_errst compile_match (on_empty_state fold_comp))
              (fun '(state, task) => seq_errst [return_errst task; rewrite_metas state]).

(*TODO: is this correct*)
Definition quote: string := """"%string.

(*Also stateful, registers*)
Axiom meta_kept : meta.
Axiom meta_alg_kept : meta.
Axiom meta_elim : meta.

(*TODO: factor out into module functor?*)

Definition sty_fold_errst {A St: Type} (f: ty_c -> A -> errState St A) (l: Sty.t) (acc: A) : errState St A :=
  foldl_errst (fun x y => f y x) (Sty.elements l) acc.
Definition mts_fold_errst {A B St: Type} (f: tysymbol_c -> A -> B -> errState St B) (l: Mts.t A) (acc: B):
  errState St B :=
  foldl_errst (fun x y => f (fst y) (snd y) x) (Mts.bindings l) acc.



Definition eliminate_algebraic : trans_errst task :=
  TransDefs.on_meta meta_elim (fun ml =>
  TransDefs.on_tagged_ty meta_alg_kept (fun kept =>
  on_empty_state (fun st =>
  let check st x :=
    match x with
    (*TODO: equality instead of matching?*)
    (* | [MAstr "keep_enums"] => err_ret (state_with_keep_e st true)
    | [MAstr "keep_recs"]  => err_ret (state_with_keep_r st true)
    | [MAstr "keep_mono"]  => err_ret (state_with_keep_m st true)
    | [MAstr "no_index"]   => err_ret (state_with_no_ind st true)
    | [MAstr "no_inversion"] => err_ret (state_with_no_inv st true)
    | [MAstr "no_selector"]  => err_ret (state_with_no_sel st true) *)
    | [MAstr s] =>
      (*Matching gives horrible term and takes forever to typecheck*)
      if (String.eqb s "keep_enums") then err_ret (state_with_keep_e st true)
      else if (String.eqb s "keep_recs") then err_ret (state_with_keep_r st true)
      else if (String.eqb s "keep_mono") then err_ret (state_with_keep_m st true)
      else if (String.eqb s "no_index") then err_ret (state_with_no_ind st true)
      else if (String.eqb s "no_inversion") then err_ret (state_with_no_inv st true)
      else if (String.eqb s "no_selector") then err_ret (state_with_no_sel st true)
      else
        throw (
            Invalid_argument (
                "meta eliminate_algebraic, arg = " ++ quote ++ s ++ quote))
    | l =>
        throw (
            Invalid_argument (
                "meta eliminate_algebraic, nb arg = " ++
                  CoqBigInt.to_string (IntFuncs.int_length l) ++ ""))
    end
  in
  trans_bind
  (errst_lift2 (foldl_err check ml st)) (fun st =>
  let kept_fold ty m :=
    match ty_node_of ty with
    | Tyapp ts _ => (*TODO: is this same match?*)
        let s := Mts.find_def _ Sty.empty ts m in
        Mts.add ts (Sty.add ty s) m
    | _ => m
    end
  in
  let st := state_with_kept_m st (Sty.fold kept_fold kept Mts.empty) in
  let add ty decls := m <- errst_tup2 (full_of_ty_td (create_meta meta_kept [MAty ty])) ;; errst_ret (m :: decls) in
  let add_meta_decls kept_m :=
    trans_bind (mts_fold_errst (fun _ => sty_fold_errst add) kept_m [])
    TransDefs.add_tdecls_errst
  in
  bind_errst (compose_errst compile_match (fold_comp st))
              (fun '(s, tsk) =>
              seq_errst [return_errst tsk;
                          rewrite_metas s;
                          add_meta_decls s.(kept_m)]))))).