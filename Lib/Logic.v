From Coq Require Import
  Bool.
From FunProofs.Lib Require Import
  Tactics.

Fact iff_not_true b P : (b = true <-> P) -> (b = false <-> ~P).
Proof. destruct b; intuition simplify. Qed.

Fact iff_not_false b P : (b = false <-> P) -> (b = true <-> ~P).
Proof. destruct b; intuition simplify. Qed.

Fact not_exist A (P : A -> Prop) : ~(exists x, P x) <-> (forall x, ~P x).
Proof. intuition (destr *; eauto). Qed.

Fact reflect_not b P : reflect P b -> reflect (~P) (negb b).
Proof.
  intros Hb%reflect_iff; apply iff_reflect.
  destruct b; cbn; intuition simplify.
Qed.
