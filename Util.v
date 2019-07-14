Ltac inv H := inversion H; clear H; subst.

Ltac inj :=
  repeat match goal with
  | H: _ = _ |- _ => assert_succeeds (injection H); inv H
  end.

Local Ltac prename' pat H name :=
  match type of H with
  | context[?pat'] => unify pat pat'; rename H into name
  end.

Tactic Notation "prename" open_constr(pat) "into" ident(name) :=
  lazymatch goal with
  | H: pat, H': pat |- _ =>
      fail 0 "Multiple possible matches for" pat ":" H "and" H'
  | H: pat |- _ => prename' pat H name
  | H: context[pat], H': context[pat] |- _ =>
      fail 0 "Multiple possible matches for" pat ":" H "and" H'
  | H: context[pat] |- _ => prename' pat H name
  | _ => fail 0 "No hypothesis matching" pat
  end.

Tactic Notation "intuition" tactic3(tactic) := intuition tactic.
Tactic Notation "intuition" := intuition auto.

Class EqDec (A : Type) := { eq_dec (x y : A): {x = y} + {x <> y} }.
Infix "==" := eq_dec (at level 70).

Fact eq_dec_true A `{EqDec} : forall x y (T E : A),
  x = y ->
  (if x == y then T else E) = T.
Proof. intros; now destruct (_ == _). Qed.

Fact eq_dec_false A `{EqDec} : forall x y (T E : A),
  x <> y ->
  (if x == y then T else E) = E.
Proof. intros; now destruct (_ == _). Qed.
