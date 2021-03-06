From Coq Require Import
  Lia
  List
  ZArith.
From FunProofs.Lib Require Import
  Arith.
From FunProofs.Lib Require Export
  AltMap.

Local Open Scope Z.

Section ZSum.
  Definition zsum (xs : list Z) : Z :=
    fold_right Z.add 0 xs.

  Definition zaltsum (xs : list Z) : Z :=
    zsum (altmap Z.opp xs).

  Lemma zsum_zero : forall n,
    zsum (repeat 0 n) = 0.
  Proof. now induction n. Qed.

  Lemma zsum_off : forall xs x off,
    fold_right Z.add (off + x) xs = off + fold_right Z.add x xs.
  Proof.
    induction xs; cbn; intros; auto.
    rewrite IHxs; lia.
  Qed.

  Corollary zsum_off_0 : forall xs off,
    fold_right Z.add off xs = off + fold_right Z.add 0 xs.
  Proof. now intros; rewrite <- zsum_off, Z.add_0_r. Qed.

  Lemma zsum_mod : forall xs n,
    n <> 0 ->
    (zsum xs) mod n = zsum (map (fun x => x mod n) xs) mod n.
  Proof.
    induction xs; cbn; intros; auto.
    rewrite (Z.add_mod (a mod n)) by auto.
    rewrite <- IHxs, Z.mod_mod, Z.add_mod; auto.
  Qed.

  Lemma zsum_rev : forall xs,
    zsum (rev xs) = zsum xs.
  Proof.
    induction xs; cbn; auto.
    fold (zsum xs).
    rewrite <- IHxs, fold_right_app; cbn.
    rewrite zsum_off; auto.
  Qed.

  Lemma zsum_app : forall xs ys,
    zsum (xs ++ ys) = zsum xs + zsum ys.
  Proof.
    unfold zsum; intros.
    rewrite fold_right_app, zsum_off_0; auto; lia.
  Qed.
End ZSum.

Section Geom.
  Definition geom r n := map (fun x => Z.pow r (Z.of_nat x)) (seq 0 n).
  Definition tens := geom 10.

  Lemma geom_length : forall r n,
    length (geom r n) = n.
  Proof. unfold geom; intros; rewrite map_length, seq_length; auto. Qed.

  Lemma geom_mod : forall r r' n b,
    b <> 0 ->
    r mod b = r' mod b ->
    map (fun x => x mod b) (geom r n) = map (fun x => x mod b) (geom r' n).
  Proof.
    unfold geom; intros.
    erewrite !map_map, map_ext; eauto.
    intros; apply pow_mod; lia.
  Qed.

  Lemma geom_one : forall n,
    geom 1 n = repeat 1 n.
  Proof.
    unfold geom; induction n; cbn; auto.
    rewrite <- seq_shift, map_map, <- IHn.
    erewrite map_ext; auto.
    intros; rewrite !Z.pow_1_l; lia.
  Qed.

  Lemma geom_none : forall n,
    geom (-1) n = altmap Z.opp (repeat 1 n).
  Proof.
    unfold geom; induction n; cbn; auto.
    rewrite <- seq_shift, map_map.
    erewrite map_ext with (g := fun x => _).
    2: intros; rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    2: rewrite Z.mul_comm, <- Z.opp_eq_mul_m1; eauto.
    rewrite <- map_map, IHn.
    clear IHn; induction n; cbn; auto.
    rewrite <- IHn; cbn; auto.
    rewrite map_map.
    erewrite map_ext with (g := fun x => x), map_id; auto using Z.opp_involutive.
  Qed.

  Lemma geom_zero' : forall n,
    tl (geom 0 n) = repeat 0 (n - 1).
  Proof.
    unfold geom; induction n; cbn; auto.
    destruct n; auto; cbn -[Z.of_nat].
    replace (S n - 1)%nat with n in IHn by lia.
    rewrite <- seq_shift, map_map, <- IHn; cbn -[Z.of_nat].
    f_equal; apply map_ext_in; intros * Hin.
    apply in_seq in Hin; rewrite !Z.pow_0_l; lia.
  Qed.

  Corollary geom_zero : forall n,
    (0 < n)%nat ->
    geom 0 n = 1 :: repeat 0 (n - 1).
  Proof. intros; rewrite <- geom_zero'; now destruct n. Qed.
End Geom.
