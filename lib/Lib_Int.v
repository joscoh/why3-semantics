Require Import StdLib.
Require Import Lib_Algebra.

(*For now, we only define the main Int module. Maybe do more later*)
Module Int.

Definition zero : funsym := const "zero" vty_int.
Definition one : funsym := const "one" vty_int.

Definition eq : predsym := binpred "eq" vty_int.
Definition neg : funsym := unop "neg" vty_int.
Definition plus: funsym := binop "plus" vty_int.
Definition mult: funsym := binop "mult" vty_int.
Definition lt : predsym := binpred "lt" vty_int.

Definition sub : funsym := binop "sub" vty_int.
Definition gt : predsym := binpred "gt" vty_int.
Definition le : predsym := binpred "le" vty_int.
Definition ge : predsym := binpred "ge" vty_int.

Definition x : vsymbol := ("x", vty_int).
Definition y : vsymbol := ("y", vty_int).

(*For now, we ignore the equality in the theory because
  in our semantics we have decidable equality anyway*)
Definition Int : theory :=
  rev [
    tdef (nonrec_fun zero nil (Tconst (ConstInt 0)));
    tdef (nonrec_fun one nil (Tconst (ConstInt 1)));
    tdef (abs_fun neg);
    tdef (abs_fun plus);
    tdef (abs_fun mult);
    tdef (abs_pred lt);
    tdef (nonrec_fun sub [x;y] <t plus({x}, neg({y})) t>);
    tdef (nonrec_pred gt [x;y] <f lt({y}, {x}) f>);
    tdef (nonrec_pred le [x;y] 
      <f lt({x}, {y}) \/ [vty_int] {x} = {y} f>);
    tdef (nonrec_pred ge [x;y] <f le({y}, {x}) f>);
    tclone Algebra.OrderedUnitaryCommutativeRing None
      (*TODO: sub for types, not just typesyms*)
      [(Algebra.t_ts, (*vty_int*) Algebra.t_ts)]
      [(Algebra.neg, neg); (Algebra.plus, plus); (Algebra.mult, mult)]
      [(Algebra.le, le)]
  ].
