Require Import Pattern.
Require Import Denotational.

Section PatProofs.

Context {gamma: context} (gamma_valid: valid_context gamma).
Context (pd: pi_dom) (pf: pi_funpred gamma_valid pd) (vt: val_typevar).
Variable (v: val_vars pd vt).
Variable (b: bool). (*Generic over terms and formulas*)
Variable (ret_ty : gen_type b). (*The return type of the values*)

(*First, we define the semantics of multiple pattern matching*)
Section MultipleMatchSemantics.

(*Generalized term/formula rep*)
Definition gen_rep (v: val_vars pd vt) (ty: gen_type b) (d: gen_term b) (Hty: gen_typed b d ty) : gen_ret pd vt b ty :=
  match b return forall (ty: gen_type b) (dat: gen_term b), 
    gen_typed b dat ty -> gen_ret pd vt b ty with
  | true => fun ty dat Hty => term_rep gamma_valid pd vt pf v dat ty Hty
  | false => fun ty dat Hty => formula_rep gamma_valid pd vt pf v dat Hty
  end ty d Hty.

Definition pat_matrix := list (list pattern * gen_term b).


(*Typing for row*)
Definition row_typed (tys: list vty) (p: list pattern) : Prop :=
  Forall2 (fun p t => pattern_has_type gamma p t) p tys.

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

End MultipleMatchSemantics.

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

(*(TODO: prove simplify later)*)

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

(*TODO: move*)
Equations hlist_app {A: Type} (f: A -> Type) (l1 l2: list A) (h1: hlist f l1) (h2: hlist f l2):
  hlist f (l1 ++ l2) :=
  hlist_app f nil l2 h1 h2 := h2;
  hlist_app f (x :: l1) l2 (HL_cons _ a1 htl) h2 := HL_cons _ _ _ a1 (hlist_app f l1 l2 htl h2).

Equations hlist_rev {A: Type} (f: A -> Type) (l: list A) (h: hlist f l) : hlist f (rev l) :=
  hlist_rev f nil h := h;
  hlist_rev f (x :: t) (HL_cons _ a1 htl) := hlist_app f (rev t) [x] (hlist_rev f t htl) 
    (HL_cons _ _ _ a1 (HL_nil _)).

(*Is there a better way to do this without all the casting, etc*)

(*An easy cast, just a bunch of maps, revs, and apps together*)
Lemma spec_prop_cast params sargs args tys : (map (v_subst vt)
  (rev
  (sorts_to_tys
  (ty_subst_list_s params (map (v_subst vt) args)
  sargs)) ++
tys)) = (rev (ty_subst_list_s params  (map (v_subst vt) args) sargs)) ++
map (v_subst vt) tys.
Proof.
  unfold sorts_to_tys, ty_subst_list_s. rewrite !map_map, !map_app, !map_rev, !map_map.
  f_equal. f_equal. apply map_ext. intros. rewrite <- subst_sort_eq; reflexivity.
Qed. 

Set Bullet Behavior "Strict Subproofs".
Lemma spec_prop 
  (*Info about first term*)
  (t: term) {m: mut_adt} (m_in : mut_in_ctx m gamma)
  {a: alg_datatype} (a_in: adt_in_mut a m) {c: funsym} (c_in: constr_in_adt c a) 
  {args: list vty} (args_len: length args = length (m_params m))
  (Hty: term_has_type gamma t (vty_cons (adt_name a) args))
  (al1: arg_list (domain (dom_aux pd)) (sym_sigma_args c (map (v_subst vt) args)))
  (Ht: tm_semantic_constr t m_in a_in c_in args_len Hty al1)
  (*Info about rest of terms*)
  (ts: list term) (tys: list vty) (al2: arg_list (domain (dom_aux pd)) (map (v_subst vt) tys))
  (Htsty: Forall2 (term_has_type gamma) (t :: ts) (vty_cons (adt_name a) args :: tys)) (*duplicate proof for irrelevance*)
  (*Info about pattern matrix*)
  (P: pat_matrix) (Hpsimp: simplified P) (*(Hc: constr_at_head_ex c P)*) (*TODO: don't think we need - SEEE*)
  (Htyp: pat_matrix_typed (vty_cons (adt_name a) args :: tys) P)
  (Htyp': pat_matrix_typed (rev (sorts_to_tys (ty_subst_list_s (s_params c) (map (v_subst vt) args) (s_args c))) ++ tys)
    (spec P c)):

  matches_matrix_tms (t :: ts) (vty_cons (adt_name a) args :: tys) P
    Htsty Htyp =

  matches_matrix 
  (*Type list more complicated: args of c + rest*)
  (rev (sorts_to_tys (ty_subst_list_s (s_params c) (map (v_subst vt) args) (s_args c))) ++ tys)
    (cast_arg_list (eq_sym (spec_prop_cast (s_params c) (s_args c) args tys))
   (hlist_app _ _ _ (hlist_rev _ _ al1) (terms_to_hlist ts tys (Forall2_inv_tail Htsty))))
    (spec P c) Htyp'.
Proof.
  unfold matches_matrix_tms.
  generalize dependent (eq_sym (spec_prop_cast (s_params c) (s_args c) args tys)).
  generalize dependent (Forall2_inv_tail Htsty).
  revert Htsty Htyp Htyp'.
  unfold matches_matrix_tms. (*TODO: get [matches_matrix_elim] to work?*)
  induction P as [| rhd rtl].
  - intros. simpl. rewrite !matches_matrix_equation_1. reflexivity.
  - intros. simpl. rewrite !matches_matrix_equation_2.
    destruct rhd as [ps a1]; simpl.
    (*Case on patterns*)
    destruct ps as [| phd ptl].
    + (*TODO: prove that we cannot have nil row in matrix if well-typed*) admit.
    + destruct phd as [| f' params tms | | |]; try discriminate.
      * (*Interesting case: Pconstr*)
        revert Htyp'. simpl.
        destruct (funsym_eqb_spec f' c); subst; simpl; intros.
        (*TODO: need to decompose [matches_matrix] for app (matches_matrix (tys1 ++ tys2) (hlist_app h1 h2)
          = matches_matrix tys1 h1 && matches_matrix tys2 h2 (assuming lengths are correct and && = option bind)
          then prove that the first one is equal to this [matches_row]
          )*)
        -- rewrite matches_matrix_equation_2. simpl.
        (*Above is wrong - need to just decompose [matches_row] in way described above
          and then prove that [match_val_single] in constr case (assuming we know constr matches)
          is equal to [matches_row] for that given arg list - result follows from this*)

        2: {

        }
        (*TODO: prove that match_val_single, in constr_case (if equal) is equal to
          matches_row*)


      * try discriminate. (*Pvar case*) rewrite matches_row_equation_4.

    (*Really, what we want to prove:
      Suppose that (t :: ts) matches row r*)


    rewrite terms_to_hlist_equation_4.
    destruct ps as [| phd ptl].
    + (*TODO: prove that we cannot have nil row in matrix if well-typed*) admit.
    + rewrite matches_row_equation_4.
      (*Think we need a different lemma*)
      destruct phd.
      * simpl.
      unfold match_val_single at 1.
      (*Core of the proof: *)
    
    
   rewrite (matches_row_equation_4 (vty_cons (adt_name a) args) tys
      (HL_cons (domain (dom_aux pd))
  (v_subst vt (vty_cons (adt_name a) args))
  (map (v_subst vt) tys)
  (term_rep gamma_valid pd vt pf v t
  (vty_cons (adt_name a) args) (Forall2_inv_head Htsty))
  (terms_to_hlist ts tys (Forall2_inv_tail Htsty)))).
    (*Probably need: if matches_row *)

    Check matches_row_equation_4.
    rewrite matches_row_equation_4.

    simpl in Hc. unfold constr_at_head in Hc.


  
   unfold matches_matrix_tms.
    Search matches_matrix.
    simpl.
    Print matches_matrix.



  generalize dependent Hty. Htysty.



has type
"hlist (domain (dom_aux pd))
  (rev (sym_sigma_args c (map (v_subst vt) args)) ++
map (v_subst vt) tys)"
while it is expected to have type
"arg_list (domain (dom_aux pd))
  (map (v_subst vt)
  (sorts_to_tys
  (ty_subst_list_s (s_params c) (map (v_subst vt) args)
  (s_args c)) ++
tys))".




Definition matches_matrix_tms (tms: list term) (tys: list vty) (P: pat_matrix)
  (Hty: Forall2 (term_has_type gamma) tms tys)
  (Hp: pat_matrix_typed tys P) : option (gen_ret pd vt b ret_ty) :=
  matches_matrix tys (terms_to_hlist tms tys Hty) P Hp.




(tl: list term) (c: funsym) (ty1: vty) (tys1: list vty) 
  (al: arg_list (domain (dom_aux pd)) (map (v_subst vt) tys1))
  (P: pat_matrix)
  (Hsimp: simplified P)
  (Hc: constr_at_head_ex c P) Hty1 Htyp:
  
  matches_matrix (terms_to_hlist (t :: tl) (ty1 :: tys1) Hty1) P Htyp =
  matches_matrix (hlist_app (hlist_rev al) 


Lemma default_prop




(tys: list vty) 
  (al: arg_list (domain (dom_aux pd)) (map (v_subst vt) tys))
  (p: pat_matrix)
  (Hty: pat_matrix_typed tys p)