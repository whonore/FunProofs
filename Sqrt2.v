(*
 * Irrationality of sqrt 2.
 * There are no relatively prime p and q such that (p/q)^2 = 2.
 *)

From Coq Require Import
  ssrbool
  ssreflect
  ssrfun
  Lia
  QArith.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma Qred_int x : Qred (x # 1) = x # 1.
Proof.
  by case: x => //; case.
Qed.

Lemma Qmult_den p q r : p # q == r <-> p # 1 == (Z.pos q # 1) * r.
Proof.
  set den := inject_Z (Z.pos q).
  by rewrite !Qmake_Qdiv -[_ == r](Qmult_inj_l _ _ den) ?Qmult_div_r -?Qmake_Qdiv.
Qed.

Lemma even_sqr_even p : Z.even (p * p) -> Z.even p.
Proof.
  by rewrite Z.even_mul; case: orP => //; case.
Qed.

Theorem sqrt2_irrational p q : Z.gcd p (Z.pos q) = 1%Z -> ~((p # q)^2 == 2 # 1).
Proof.
  set q' := Z.pos q; move=> Hred; rewrite Qmult_den -Qred_eq_iff ?Qred_int.
  case; rewrite ?Pos2Z.inj_mul; move=> Heq; move: Hred.
  have /Z.even_spec[k Hk]: Z.even p by apply even_sqr_even; rewrite Heq Z.even_mul orb_true_r.
  have Heq': (q' * q' = k * k * 2)%Z by lia.
  have /Z.even_spec[? Hq]: Z.even q' by apply even_sqr_even; rewrite Heq' Z.even_mul orb_true_r.
  rewrite Hk Hq Z.gcd_mul_mono_l; lia.
Qed.
