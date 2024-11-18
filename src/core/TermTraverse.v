Require Import Monads TermDefs TermFuncs TermTraverseAux.
Import MonadNotations.
Local Open Scope errst_scope.

(*A traversal function*)


(*This will be generic for any errState (CoqBigInt.t * St) for some state St.
  This is the most generic we will need for our purposes*)
(*This is similar to [t_map] in the OCaml version, with 1 big difference:
  t_map is not explicitly recursive. However, it can be used recursively by instantiating
  the function argument with a recursive function. This doesn't work for us because Coq would
  not be able to prove such a function terminating.
  So instead we give a generic recursive traversal function that opens all the bindings.
  Defining this is extremely complicated. The recursion is not structural (since we do substitution
  when opening bindings). So we give a size metric and prove that substitution of variables
  preserves size (which is not trivial). Then, since we need to make recursive calls inside state
  monad bind operations, we need a dependently typed bind operator to remember the hypotheses
  we need. For similar reasons, we also need a dependently typed [map] function on lists*)
Section Traverse.
(*NOT dependently typed for OCaml purposes*)
Variable (St: Type). (*The type of state*)
Variable (R: Type). (*Return type*)

Notation T := (errState (CoqBigInt.t * St) R).

Variable (var_case: forall (x: vsymbol), T).

Variable (const_case: forall (c: constant), T).
(*For now, only do let*)
(*NOTE: recursive case 2 on [t_open_bound], v is the NEW variable, t2 is the new term*)
Variable (let_case: forall (t1: term_c) (v: vsymbol) (t2: term_c) (r1 r2: R), T).
Variable (if_case: forall (t1 t2 t3: term_c) (r1 r2 r3: R), T).

Variable (app_case: forall (l: lsymbol) (tms: list term_c) (rs: list R), T).
(*Again, tbs is a list of (new pattern, new term, recursive call)*)
Variable (match_case: forall (t1: term_c) (r1: R) (tb: list (pattern_c * term_c * R)), T).
(*As above: new variable, new term, new result*)
Variable (eps_case: forall (v: vsymbol) (t: term_c) (r: R), T).
Variable (quant_case: forall (q: quant) (vs: list vsymbol) (tr: list (list (term_c))) (rr: list (list R))
  (t: term_c) (r: R), T).
Variable (binop_case: forall (b: binop) (t1 t2: term_c) (r1 r2: R), T).
Variable (not_case: forall (t: term_c) (r: R), T).
Variable (true_case: T).
Variable (false_case : T).

(*This is annoying for sure*)


(*We can't use Equations because it doesn't support mutual well-founded
  definitions. So we will use Xavier trick again*)


Fixpoint term_traverse (tm1: term_c) (ACC: Acc lt (term_size tm1)) : T :=
  match (t_node_of tm1) as t1 return term_node_size t1 = term_size tm1 -> _ with
  | Tconst c => fun _ => const_case c
  | Tvar x => fun _ => var_case x
  | Tif t1 t2 t3 => fun Hsz =>
    v1 <- term_traverse t1 (Acc_inv ACC (tif_size1 Hsz)) ;;
    v2 <- term_traverse t2 (Acc_inv ACC (tif_size2 Hsz)) ;;
    v3 <- term_traverse t3 (Acc_inv ACC (tif_size3 Hsz)) ;;
    if_case t1 t2 t3 v1 v2 v3
  | Tlet t1 b => fun Hsz =>
    v1 <- term_traverse t1 (Acc_inv ACC (tlet_size1 Hsz)) ;;
    (*Need dependent types here to have enough information for the proof*)
    errst_bind_dep (errst_tup1 (errst_lift1 (t_open_bound b)))
      (fun y s Heq => 
        v2 <- (term_traverse (snd y) (Acc_inv ACC (tlet_size2 Hsz Heq))) ;;
        let_case t1 (fst y) (snd y)  v1 v2)
  | Tapp l ts => fun Hsz =>
    (*Need dependent map for termination proof*)
    recs <- errst_list (@dep_map _ _ (fun t => term_size t < term_size tm1) 
      (fun t1 (Ht1: term_size t1 < term_size tm1) => 
        term_traverse t1 (Acc_inv ACC Ht1)) ts (tapp_size Hsz)) ;;
    (app_case l ts recs)
  (*Case is the trickiest: we need both a dependent map and a dependent bind*)
  | Tcase t1 tbs => fun Hsz =>
    r1 <- term_traverse t1 (Acc_inv ACC (tmatch_size1 Hsz)) ;;
    tbs2 <- errst_list (@dep_map _ _ (fun x => term_size (snd x) < term_size tm1)
      (*Idea: For each element in list, use dependent bind and recursively traverse*)
      (fun b (Hx: term_size (snd b) < term_size tm1) =>
        errst_bind_dep (errst_tup1 (errst_lift1 (t_open_branch b)))
          (fun y s Heq =>
            t2 <- term_traverse (snd y) (Acc_inv ACC (tmatch_size2 Hx Heq)) ;;
            errst_ret (y, t2))
        ) tbs (tmatch_size3 Hsz)) ;;
    match_case t1 r1 tbs2
  | Teps b => fun Hsz =>
    errst_bind_dep (errst_tup1 (errst_lift1 (t_open_bound b)))
      (fun y s Heq => 
        v <- (term_traverse (snd y) (Acc_inv ACC (teps_size Hsz Heq))) ;;
        eps_case (fst y) (snd y) v)
  (*A slight complication from the triggers - need nested dependent match*)
  | Tquant q tq => fun Hsz =>
    (*NOTE: doing bind ... ret, need for proofs even though superflous*)
    errst_bind_dep (errst_tup1 (errst_lift1 (t_open_quant1 tq)))
      (fun (y : list vsymbol * trigger * term_c) s Heq => 
        v <- (term_traverse (snd y) (Acc_inv ACC (tquant_size1 Hsz Heq))) ;;
        let vs := fst (fst y) in
        let tr := snd (fst y) in
        let t := snd y in
        (*Then traverse over triggers*)
        v2 <- errst_list (dep_map (fun l1 (Hl1: Forall (fun x => term_size x < term_size tm1) l1) =>
          errst_list (dep_map (fun tr1 (Ht1: term_size tr1 < term_size tm1) => 
            term_traverse tr1 (Acc_inv ACC Ht1))
            l1 Hl1)) tr (tquant_size_tr Hsz Heq)) ;;
        quant_case q vs tr v2 t v)
  | Tbinop b t1 t2 => fun Hsz =>
    r1 <- term_traverse t1 (Acc_inv ACC (tbinop_size1 Hsz)) ;;
    r2 <- term_traverse t2 (Acc_inv ACC (tbinop_size2 Hsz)) ;;
    binop_case b t1 t1 r1 r2
  | Tnot t1 => fun Hsz =>
    r1 <- term_traverse t1 (Acc_inv ACC (tnot_size1 Hsz)) ;;
    not_case t1 r1
  | Ttrue => fun _ => true_case
  | Tfalse => fun _ => false_case
  end (eq_sym (term_size_eq tm1)).

(* 
Equations term_traverse (tm1: term_c) : T by wf (term_size tm1) lt :=
  term_traverse tm1 := term_node_traverse (t_node_of tm1) 
with term_node_traverse (tm1: term_node) : T :=
  term_node_traverse (Tconst c) := const_case c;
  term_node_traverse (Tvar x) := var_case x;
  term_node_traverse (Tif t1 t2 t3) :=
    v1 <- term_traverse t1 ;;
    v2 <- term_traverse t2 ;;
    v3 <- term_traverse t3 ;;
    if_case t1 t2 t3 v1 v2 v3;
  term_node_traverse (Tlet t1 b) :=
    v1 <- term_traverse t1 ;;
    (*Need dependent types here to have enough information for the proof*)
    st_bind_dep _ _ _ (t_open_bound b)
      (fun y s Heq => 
        v2 <- (term_traverse (snd y)) ;;
        let_case t1 ((fst y), (snd b)) v1 v2). *)

End Traverse.