(*Various forms of mapping over terms and formulas*)
Require Import Syntax Common.

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