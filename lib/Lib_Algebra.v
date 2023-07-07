Require Import StdLib.
Require Import Lib_Relations.
Set Bullet Behavior "Strict Subproofs".

(*TODO: maybe change TheoryTest, see*)


Module Algebra.
Local Open Scope why3_scope.

(*Generic definitions*)
Definition t_ts : typesym := mk_ts "t" nil.
Definition t : vty := vty_cons t_ts nil.

(*TODO: move, make more general*)
Definition op: funsym := binop "op" t. 
Definition unit : funsym := const "Unit" t.

Definition inv : funsym := unop "inv" t. 
(*Definition op (t1 t2: term) : term :=
  Tfun op_fs nil [t1; t2].*)

Definition x : vsymbol := ("x"%string, t).
Definition y : vsymbol := ("y"%string, t).
Definition z : vsymbol := ("z"%string, t).

Coercion Tvar : vsymbol >-> term.

(*TODO: the brackets for variables are ugly, but Coq will not convert appropriately*)

(*Associativity*)
Definition Assoc : theory :=
  rev [
    tdef (abs_type t_ts);
    tdef (abs_fun op);
    tprop Paxiom "Assoc"
      <f forall x, forall y, forall z, 
        [t] (op (op ({x}, {y}), {z})) = (op ({x}, (op({y}, {z})))) f>
  ].

(*Commutativity*)
Definition Comm : theory :=
  rev [
    tdef (abs_type t_ts);
    tdef (abs_fun op);
    tprop Paxiom "Comm" <f
     forall x, forall y, [t] op({x}, {y}) = op({y}, {x}) f>
  ].

(*Associativity and Commutativity*)
Definition AC : theory :=
  rev [
    tclone Assoc None nil nil nil;
    tclone Comm None [(t_ts, t_ts)] [(op, op)] nil
  ].

(*Monoids*)
Definition Monoid : theory :=
  rev [
    tclone Assoc None nil nil nil;
    tdef (abs_fun unit);
    tprop Paxiom "Unit_def_l" <f
      forall x, [t] op (unit(), {x}) = {x} f>
  ].

(*Commutative monoids*)
Definition CommutativeMonoid : theory :=
  rev [
    tclone Monoid None nil nil nil;
    tclone Comm None [(t_ts, t_ts)] [(op, op)] nil
  ].

(*Groups*)
Definition Group : theory :=
  rev [
    tclone Monoid None nil nil nil;
    tdef (abs_fun inv);
    tprop Paxiom "Inv_def_l" <f
      forall x, [t] op (inv({x}), {x}) = unit() f>;
    tprop Paxiom "Inv_def_r" <f
      forall x, [t] op ({x}, inv({x})) = unit() f>
  ].

(*Commutative groups*)
Definition CommutativeGroup : theory :=
  rev [
    tclone Group None nil nil nil;
    tclone Comm None [(t_ts, t_ts)] [(op, op)] nil
  ].

(*Rings*)
Definition zero : funsym := const "zero" t.
Definition plus : funsym := binop "plus" t.
Definition mult : funsym := binop "mult" t.
Definition neg : funsym := unop "neg" t.
(*Qualified names - TODO: improve*)
Definition MA_t_ts : typesym := mk_ts "MulAssoc.t" nil.
Definition MA_t : vty := vty_cons MA_t_ts nil.
Definition MA_op: funsym := binop "MulAssoc.op" MA_t.

(*We do not support infix notation*)
Definition Ring : theory :=
  rev [
    tdef (abs_type t_ts);
    tdef (abs_fun zero);
    tdef (abs_fun plus);
    tdef (abs_fun neg);
    tdef (abs_fun mult);
    tclone CommutativeGroup None [(t_ts, t_ts)] 
      [(unit, zero); (op, plus); (inv, neg)] nil;
    tclone Assoc (Some "MulAssoc")  [(MA_t_ts, t_ts)] [(MA_op, mult)] nil;
    tprop Paxiom "Mul_distr_l" <f
      forall x, forall y, forall z, 
        [t] mult({x}, plus({y}, {z})) = plus(mult({x}, {y}), mult({x}, {z}))
    f>;
    tprop Paxiom "Mul_distr_r" <f
      forall x, forall y, forall z,
        [t] mult(plus({y}, {z}), {x}) = plus(mult({y}, {x}), mult({z}, {x}))
    f>
  ].

(*Commutative Rings*)
Definition MC_t_ts : typesym := mk_ts "MulComm.t" nil.
Definition MC_t : vty := vty_cons MC_t_ts nil.
Definition MC_op: funsym := binop "MulComm.op" MC_t.
Definition CommutativeRing : theory :=
  rev [
    tclone Ring None nil nil nil;
    tclone Comm (Some "MulComm") [(MC_t_ts, t_ts)] [(MC_op, mult)] nil
  ].

(*Commutative Rings With Unit*)
Definition one : funsym := const "one" t.
Definition UnitaryCommutativeRing : theory :=
  rev [
    tclone CommutativeRing None nil nil nil;
    tdef (abs_fun one);
    tprop Paxiom "Unitary" <f forall x, [t] mult(one(), {x}) = {x} f>;
    tprop Paxiom "NonTrivialRing" <f ([t] zero() != one()) f>
  ].

(*Ordered Commutative Rings*)
Definition le : predsym := binpred "le" t.
Definition OrderedUnitaryCommutativeRing : theory :=
  rev [
    tclone UnitaryCommutativeRing None nil nil nil;
    tdef (abs_pred le);
    tclone Relations.TotalOrder None [(Relations.t_ts, t_ts)] nil [(Relations.rel, le)];
    tprop Paxiom "ZeroLessOne" <f le (zero(), one()) f>;
    tprop Paxiom "CompatOrderAdd" <f forall x, forall y, forall z,
      le({x}, {y}) -> le(plus({x}, {z}), plus({y}, {z})) f>;
    tprop Paxiom "CompatOrderMult" <f 
      forall x, forall y, forall z,
      le({x}, {y}) -> le(zero(), {z}) -> 
      le(mult({x}, {z}), mult({y}, {z})) f>
  ].

(*Fields*)
Definition sub : funsym := binop "sub" t.
Definition div: funsym := binop "div" t.

Definition Field : theory :=
  rev [
    tclone UnitaryCommutativeRing None nil nil nil;
    tdef (abs_fun inv);
    tprop Paxiom "Inverse" <f forall x,
      [t] {x} != zero() -> [t] mult({x}, inv({x})) = one() f>;
    tdef (nonrec_fun sub [x;y] <t plus({x}, neg({y})) t>);
    tdef (nonrec_fun div [x;y] <t mult({x}, inv({y})) t>);
    tprop Plemma "add_div" <f forall x, forall y, forall z,
      [t] z != zero() -> 
      [t] div(plus({x}, {y}), {z}) = plus(div({x}, {z}), div({y}, {z})) f>;
    tprop Plemma "sub_div" <f forall x, forall y, forall z,
      [t] z != zero() -> 
      [t] div(sub({x}, {y}), {z}) = sub(div({x}, {z}), div({y}, {z})) f>;
    tprop Plemma "neg_div" <f forall x, forall y,
      [t] y != zero() -> 
      [t] div(neg({x}), {z}) = neg(div({x}, {z})) f>;
    tprop Plemma "assoc_mul_div" <f forall x, forall y, forall z,
      [t] z != zero() ->
      [t] div(mult({x}, {y}), {z}) = mult({x}, div({y}, {z})) f>;
    tprop Plemma "assoc_div_mul" <f forall x, forall y, forall z,
      ([t] y != zero() /\ [t] z != zero()) -> (*TODO: change after notations*)
      [t] div(div({x}, {y}), {z}) = div({x}, mult({y}, {z})) f>;
    tprop Plemma "assoc_div_div" <f forall x, forall y, forall z,
      ([t] y != zero() /\ [t] z != zero()) -> (*TODO: change after notations*)
      [t] div({x}, div({y}, {z})) = div(mult({x}, {z}), {y}) f>
  ].

Definition OrderedField : theory :=
  rev [
    tclone Field None nil nil nil;
    tdef (abs_pred le);
    tclone Relations.TotalOrder None [(Relations.t_ts, t_ts)] nil [(Relations.rel, le)];
    tprop Paxiom "ZeroLessOne" <f le (zero(), one()) f>;
    tprop Paxiom "CompatOrderAdd" <f forall x, forall y, forall z,
      le({x}, {y}) -> le(plus({x}, {z}), plus({y}, {z})) f>;
    tprop Paxiom "CompatOrderMult" <f 
      forall x, forall y, forall z,
      le({x}, {y}) -> le(zero(), {z}) -> 
      le(mult({x}, {z}), mult({y}, {z})) f>
  ].

End Algebra.