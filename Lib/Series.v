From Coq Require Import
  Lia
  List
  ZArith.
From FunProofs.Lib Require Import
  Arith
  List
  Tactics.
From FunProofs.Lib Require Export
  AltMap
  Sum.

#[local] Open Scope Z.

Section Maximum.
  Definition maximum min (xs : list Z) : Z :=
    fold_right Z.max min xs.

  Definition maximum0 (xs : list Z) : Z :=
    maximum (hd 0 xs) xs.

  Lemma maximum_case : forall min xs,
    let m := maximum min xs in
    Forall (fun x => x <= m) xs /\
    (In m xs \/ (m = min /\ Forall (fun x => x < min) xs)).
  Proof.
    induction xs as [| x xs]; cbn in *; auto;
      destruct IHxs as (Hmax & Hin); fold (maximum min xs); split.
    - constructor; auto using Z.le_max_l.
      rewrite Forall_forall in *; intros * Hin'; apply Hmax in Hin'; lia.
    - rewrite Z.max_comm; pattern (Z.max (maximum min xs) x);
        apply Zmax_case_strong_lt; intros; auto.
      intuition auto.
      right; split; auto; constructor; auto; lia.
  Qed.

  Lemma maximum0_case : forall xs,
    let m := maximum0 xs in
    xs <> nil ->
    Forall (fun x => x <= m) xs /\ In m xs.
  Proof.
    intros; pose proof (maximum_case (hd 0 xs) xs).
    repeat intuition auto.
    destruct xs as [| x xs]; cbn in *; [easy |].
    prename (fun _ => _ < _) into Hfalse; inv Hfalse; lia.
  Qed.

  Lemma maximum_lower_bound : forall min xs,
    min <= maximum min xs.
  Proof.
    unfold maximum; induction xs as [| x xs]; cbn; intros; lia.
  Qed.

  Lemma maximum_le_mono : forall min min' xs,
    min <= min' ->
    maximum min xs <= maximum min' xs.
  Proof.
    unfold maximum; induction xs as [| x xs]; cbn; intros; lia.
  Qed.

  Lemma maximum_cons_le : forall min xs x,
    maximum min xs <= maximum min (x :: xs).
  Proof. unfold maximum; intros; cbn; lia. Qed.

  Lemma maximum_in : forall min xs,
    let m := maximum min xs in
    min < maximum min xs ->
    In m xs.
  Proof.
    induction xs as [| x xs]; cbn; intros; [lia |].
    fold (maximum min xs) in *.
    assert (x < maximum min xs \/ maximum min xs <= x) as [|] by lia.
    - rewrite Z.max_r in * by lia; auto.
    - rewrite Z.max_l in * by lia; auto.
  Qed.

  Lemma maximum_weaken_in : forall min min' xs,
    min <= min' ->
    In (maximum min' xs) xs ->
    maximum min xs = maximum min' xs.
  Proof.
    induction xs as [| x xs]; cbn; intros * Hlt Hin; [easy |].
    pose proof (maximum_le_mono min min' xs); unfold maximum in *.
    destruct Hin as [Heq | Hin]; subst; try lia.
    pattern (Z.max x (fold_right Z.max min' xs)); apply Z.max_case_strong; intros; try lia.
    rewrite Z.max_r in Hin by auto; apply IHxs in Hin; auto; lia.
  Qed.

  Corollary maximum_weaken_lt : forall min min' xs,
    min <= min' < maximum min' xs ->
    maximum min xs = maximum min' xs.
  Proof. intros; apply maximum_weaken_in, maximum_in; lia. Qed.

  Lemma maximum0_unfold : forall x xs,
    0 <= x ->
    maximum0 (x :: xs) = Z.max x (maximum0 xs).
  Proof.
    intros; destruct xs as [| x' xs]; cbn; [lia |].
    fold (maximum x xs); fold (maximum x' xs).
    assert (x <= x' \/ x' < x) as [|] by lia.
    - destruct (maximum_case x' xs) as (? & [? | (? & Hmax)]).
      + rewrite (maximum_weaken_in x x' xs); auto; lia.
      + destruct (maximum_case x xs) as (? & [Hin | (? & ?)]); try lia.
        rewrite Forall_forall in Hmax; apply Hmax in Hin; lia.
    - destruct (maximum_case x xs) as (? & [? | (? & Hmax)]).
      + rewrite (maximum_weaken_in x' x xs); auto; lia.
      + destruct (maximum_case x' xs) as (? & [Hin | (? & ?)]); try lia.
        rewrite Forall_forall in Hmax; apply Hmax in Hin; lia.
  Qed.
End Maximum.

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
