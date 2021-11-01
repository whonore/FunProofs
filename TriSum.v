(*
 * Closed forms for the sum of the p-th power of the first n natural numbers.
 * TODO: Faulhaber’s formula
 *)

From Coq Require Import
  Arith
  List
  Lia.
From FunProofs.Lib Require Import
  Series
  Util.

Import NSum.

Section TriangleSum.
  Notation numer n := (n * (n + 1)) (only parsing).

  Lemma tri_div_2 n : numer n mod 2 = 0.
  Proof.
    apply Nat.mod_divides, Nat.even_spec; try lia.
    rewrite Nat.even_mul, Nat.add_1_r, Nat.even_succ.
    apply Nat.orb_even_odd.
  Qed.

  Lemma triangle_sum n : sum (seq 1 n) = numer n / 2.
  Proof.
    induction n; auto.
    cbn [seq]; rewrite <- seq_shift; cbn -[Nat.div Nat.mul]; normalize_sums.
    rewrite sum_succ, sum_shift, IHn, seq_length.
    apply Nat.div_unique_exact; [lia |].
    unfold NSumOps.Tadd, NSumOps.T_of_nat, NSumOps.T0, id.
    enough (numer n = 2 * (numer n / 2)) by lia.
    apply Nat.div_exact; [lia | apply tri_div_2].
  Qed.
End TriangleSum.

Section SumSquare.
  Notation numer n := (n * (n + 1) * (2 * n + 1)) (only parsing).

  Lemma square_succ n : Nat.square (S n) = Nat.square n + 2 * n + 1.
  Proof. unfold Nat.square; lia. Qed.

  Lemma sum_square_succ ns n :
    sum' n (map (fun m => Nat.square (S m)) ns) =
    sum' n (map Nat.square ns) + 2 * sum ns + length ns.
  Proof.
    erewrite map_ext by (apply square_succ).
    rewrite !sum_add; fold (@const _ NSumOps.T 1).
    rewrite sum_const, sum_mul_id; cbn.
    unfold NSumOps.Tadd, NSumOps.T_of_nat, NSumOps.T, id in *; lia.
  Qed.

  Lemma square_div_6 n : numer n mod 6 = 0.
  Proof.
    induction n; auto.
    apply Nat.mod_divides in IHn as (m & IHn); try lia.
    match goal with |- ?x mod _ = _ => remember x as lhs end.
    replace lhs with (6 * (m + n * n + 2 * n + 1)) by lia.
    rewrite Nat.mul_comm; apply Nat.mod_mul; lia.
  Qed.

  Lemma sum_square n : sum (map Nat.square (seq 1 n)) = numer n / 6.
  Proof.
    induction n; auto.
    cbn [seq]; rewrite <- seq_shift; cbn -[Nat.div Nat.mul]; normalize_sums.
    change (Nat.square 1) with 1; rewrite sum_shift.
    rewrite map_map, sum_square_succ, IHn, triangle_sum, seq_length.
    apply Nat.div_unique_exact; [lia |].
    pose proof (tri_div_2 n) as Htri; apply Nat.div_exact in Htri; try lia.
    unfold NSumOps.Tadd, NSumOps.T_of_nat, NSumOps.T0, id.
    enough (numer n = 6 * (numer n / 6)) by lia.
    apply Nat.div_exact; [lia | apply square_div_6].
  Qed.
End SumSquare.

Section SumCube.
  Notation numer n := (n * n * (n + 1) * (n + 1)) (only parsing).

  Definition cube n := n * n * n.

  Lemma cube_succ n : cube (S n) = cube n + 3 * Nat.square n + 3 * n + 1.
  Proof. unfold cube, Nat.square; lia. Qed.

  Lemma sum_cube_succ ns n :
    sum' n (map (fun m => cube (S m)) ns) =
    sum' n (map cube ns) + 3 * sum (map (Nat.square) ns) + 3 * sum ns + length ns.
  Proof.
    erewrite map_ext by (apply cube_succ).
    rewrite !sum_add; fold (@const _ NSumOps.T 1).
    rewrite sum_const, sum_mul_id, sum_mul; cbn.
    unfold NSumOps.Tadd, NSumOps.T_of_nat, NSumOps.T, id in *; lia.
  Qed.

  Lemma cube_div_4 n : numer n mod 4 = 0.
  Proof.
    replace (numer n) with ((n * (n + 1)) * (n * (n + 1))) by lia.
    pose proof (tri_div_2 n) as Htri.
    apply Nat.mod_divides in Htri as (m & ->); try lia.
    replace (2 * m * (2 * m)) with (m * m * 4) by lia.
    apply Nat.mod_mul; lia.
  Qed.

  Lemma cube_square n : sum (map cube (seq 1 n)) = numer n / 4.
  Proof.
    induction n; auto.
    cbn [seq]; rewrite <- seq_shift; cbn -[Nat.div Nat.mul]; normalize_sums.
    change (cube 1) with 1; rewrite sum_shift.
    rewrite map_map, sum_cube_succ, IHn, sum_square, triangle_sum, seq_length.
    apply Nat.div_unique_exact; [lia |].
    pose proof (tri_div_2 n) as Htri; apply Nat.div_exact in Htri; try lia.
    pose proof (square_div_6 n) as Hsq; apply Nat.div_exact in Hsq; try lia.
    unfold NSumOps.Tadd, NSumOps.T_of_nat, NSumOps.T0, id.
    enough (numer n = 4 * (numer n / 4)) by lia.
    apply Nat.div_exact; [lia | apply cube_div_4].
  Qed.
End SumCube.
