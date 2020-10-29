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
  case: x; auto; case; auto.
Qed.

Lemma Qmult_den p q r : p # q == r <-> p # 1 == (Z.pos q # 1) * r.
Proof.
  set den := inject_Z (Z.pos q).
  by rewrite !Qmake_Qdiv -[_ == r](Qmult_inj_l _ _ den) ?Qmult_div_r -?Qmake_Qdiv.
Qed.

Theorem sqrt2_irrational p q : Z.gcd p (Z.pos q) = 1%Z -> ~(p # q)^2 == 2 # 1.
Proof.
  move=> Hred; rewrite Qmult_den -Qred_eq_iff ?Qred_int.
  case; rewrite ?Pos2Z.inj_mul; set q' := Z.pos q; move=> Heq.
  have Heven: Z.even p.
  { suff: Z.even (p * p) by rewrite Z.even_mul; case: orP; auto; case.
    by rewrite Heq Z.even_mul; case: orP; auto.
  }
  apply Z.even_spec in Heven; case: Heven => k ?; subst.
  have Heq': (k * k * 2 = q' * q')%Z by lia.
  have Heven': Z.even q'.
  { suff: Z.even (q' * q') by rewrite Z.even_mul; case: orP; auto; case.
    by rewrite -Heq' Z.even_mul; case: orP; auto.
  }
  apply Z.even_spec in Heven'; case: Heven' => j Hq; subst q'.
  move: Hred; rewrite Hq Z.gcd_mul_mono_l; lia.
Qed.
