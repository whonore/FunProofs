From Coq Require Import
  Bool.
From FunProofs.Lib Require Import
  Tactics.

Fact iff_not_true : forall b P,
  (b = true <-> P) -> (b = false <-> ~P).
Proof. destruct b; intuition simplify. Qed.

Fact iff_not_false : forall b P,
  (b = false <-> P) -> (b = true <-> ~P).
Proof. destruct b; intuition simplify. Qed.

Fact not_exist : forall A (P : A -> Prop),
  ~(exists x, P x) <-> (forall x, ~P x).
Proof. intuition (destr *; eauto). Qed.

Fact reflect_not : forall b P,
  reflect P b -> reflect (~P) (negb b).
Proof.
  intros * Hb.
  apply reflect_iff in Hb; apply iff_reflect.
  destruct b; cbn; intuition simplify.
Qed.
