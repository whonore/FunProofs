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

