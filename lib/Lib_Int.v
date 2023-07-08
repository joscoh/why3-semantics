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

(*Function bodies to make the context nicer*)
Definition sub_body : term :=  <t plus({x}, neg({y})) t>.
Definition gt_body : formula :=  <f lt({y}, {x}) f>.
Definition le_body : formula :=  <f lt({x}, {y}) \/ [vty_int] {x} = {y} f>.
Definition ge_body : formula := <f le({y}, {x}) f>.

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
    tdef (nonrec_fun sub [x;y] sub_body);
    tdef (nonrec_pred gt [x;y] gt_body);
    tdef (nonrec_pred le [x;y] le_body);
    tdef (nonrec_pred ge [x;y] ge_body);
    tclone Algebra.OrderedUnitaryCommutativeRing None
      (mk_typemap [(Algebra.t, vty_int)])
      [(Algebra.zero, zero); (Algebra.one, one); 
        (Algebra.neg, neg); (Algebra.plus, plus); (Algebra.mult, mult)]
      [(Algebra.le, le)]
  ].

End Int.