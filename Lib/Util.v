From FunProofs.Lib Require Export
  EqDec
  Tactics.

Fact iff_not : forall b P,
  (b = true <-> P) -> (b = false <-> ~P).
Proof.
  intuition (subst; auto; try easy).
  destruct b; cbn in *; intuition.
Qed.

Fact not_exist : forall A (P : A -> Prop),
  ~(exists x, P x) <-> (forall x, ~P x).
Proof. intuition (destr *; eauto). Qed.
