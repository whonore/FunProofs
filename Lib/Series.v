From Coq Require Import
  Lia
  List
  ZArith.
From FunProofs.Lib Require Import
  Arith.
From FunProofs.Lib Require Export
  AltMap.

Section Series.
  Open Scope Z.

  Definition zsum (xs : list Z) : Z :=
    fold_right Z.add 0 xs.

  Definition zaltsum (xs : list Z) : Z :=
    zsum (altmap Z.opp xs).

  Definition geom r n := map (fun x => Z.pow r (Z.of_nat x)) (seq 0 n).
  Definition tens := geom 10.

  Lemma zsum_mod : forall xs n,
    n <> 0 ->
    (zsum xs) mod n = zsum (map (fun x => x mod n) xs) mod n.
  Proof.
    induction xs; cbn; intros; auto.
    rewrite (Z.add_mod (a mod n)) by auto.
    rewrite <- IHxs, Z.mod_mod, Z.add_mod; auto.
  Qed.

  Lemma zsum_off : forall xs x off,
    fold_right Z.add (off + x) xs = off + fold_right Z.add x xs.
  Proof.
    induction xs; cbn; intros; auto.
    rewrite IHxs; lia.
  Qed.

  Lemma zsum_rev : forall xs,
    zsum (rev xs) = zsum xs.
  Proof.
    induction xs; cbn; auto.
    fold (zsum xs).
    rewrite <- IHxs, fold_right_app; cbn.
    rewrite zsum_off; auto.
  Qed.

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
    unfold geom; intros.
    induction n; cbn; auto.
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
End Series.
