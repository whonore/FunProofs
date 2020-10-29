From Coq Require Import
  Arith
  Bool
  List
  ZArith.

Class EqDec (A : Type) := { eq_dec (x y : A): {x = y} + {x <> y} }.
Module Import EqDecNotations.
  Infix "==" := eq_dec (at level 70).
End EqDecNotations.

Fact eq_dec_true A `{EqDec} : forall x y (T E : A),
  x = y ->
  (if x == y then T else E) = T.
Proof. intros; now destruct (_ == _). Qed.

Fact eq_dec_false A `{EqDec} : forall x y (T E : A),
  x <> y ->
  (if x == y then T else E) = E.
Proof. intros; now destruct (_ == _). Qed.

Instance nat_eq_dec : EqDec nat := {| eq_dec := Nat.eq_dec |}.
Instance Z_eq_dec : EqDec Z := {| eq_dec := Z.eq_dec |}.
Instance bool_eq_dec : EqDec bool := {| eq_dec := bool_dec |}.
Instance list_eq_dec {A} `{eq: EqDec A} : EqDec (list A) := {|
  eq_dec := list_eq_dec eq_dec
|}.
