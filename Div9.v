(* Divisibility by 9
   A decimal number is divisible by 9 iff the sum of its digits are. *)

Require Import Lia.
Require Import List.
Require Import ZArith.

Notation "( x | y )" := (Nat.divide x y) (at level 0).

Section ModFacts.
  Lemma pow_mod : forall x r n,
    n <> 0 ->
    (r ^ x) mod n = (r mod n) ^ x mod n.
  Proof.
    induction x; cbn; intros; auto.
    rewrite (Nat.mul_mod (r mod n)); auto.
    rewrite <- IHx, Nat.mod_mod, Nat.mul_mod; auto.
  Qed.

  Lemma mod_mod_mul : forall x n m,
    n <> 0 -> m <> 0 ->
    (x mod (n * m)) mod n = x mod n.
  Proof.
    intros.
    rewrite Nat.mod_mul_r by auto.
    rewrite Nat.add_mod, (Nat.mul_comm n), Nat.mod_mul by auto; cbn.
    rewrite Nat.add_0_r, !Nat.mod_mod; auto.
  Qed.

  Lemma mod_mul_congr : forall x y n m,
    n <> 0 -> m <> 0 ->
    x mod (n * m) = y mod (n * m) ->
    x mod n = y mod n.
  Proof.
    intros * ? ? Hmod.
    assert (n * m <> 0) by (apply Nat.neq_mul_0; auto).
    assert (x mod (n * m) = 0 \/ x mod (n * m) <> 0) as [Heq0 |] by lia.
    - rewrite Heq0 in Hmod; symmetry in Hmod.
      rewrite Nat.mod_divide in Heq0, Hmod by auto.
      destruct Heq0, Hmod; subst.
      rewrite !(Nat.mul_comm n m), !Nat.mul_assoc, !Nat.mod_mul; auto.
    - rewrite (Nat.mod_eq y) in Hmod by auto.
      replace y with ((m * (y / (n * m)) * n) + x mod (n * m)) by lia.
      rewrite Nat.add_mod, Nat.mod_mul by auto; cbn.
      rewrite mod_mod_mul, Nat.mod_mod; auto.
  Qed.
End ModFacts.

Section ListFacts.
  Context {A : Type}.

  Lemma list_eq_pointwise : forall (xs ys : list A),
    xs = ys <-> (forall n, nth_error xs n = nth_error ys n).
  Proof.
    split; intros Heq; subst; auto.
    revert ys Heq; induction xs; intros; destruct ys;
      auto; try solve [now specialize (Heq 0)].
    f_equal.
    - specialize (Heq 0); inversion Heq; auto.
    - apply IHxs; intros.
      specialize (Heq (S n)); auto.
  Qed.

  Lemma repeat_nth : forall (x : A) n m,
    m < n ->
    nth_error (repeat x n) m = Some x.
  Proof.
    induction n; cbn; intros; try lia.
    destruct m; cbn; auto.
    apply IHn; lia.
  Qed.

  Lemma rev_repeat_nth : forall (x : A) n m,
    m < n ->
    nth_error (rev (repeat x n)) m = Some x.
  Proof.
    induction n; cbn; intros; try lia.
    assert (Hn: length (rev (repeat x n)) = n)
      by (rewrite rev_length, repeat_length; auto).
    assert (m = n \/ m < n) as [| Hlt] by lia; subst.
    - rewrite nth_error_app2 by lia.
      rewrite Hn, Nat.sub_diag; auto.
    - rewrite nth_error_app1 by lia; auto.
  Qed.

  Lemma rev_repeat : forall (x : A) n,
    rev (repeat x n) = repeat x n.
  Proof.
    intros; rewrite list_eq_pointwise; intros m.
    assert (Hn: length (repeat x n) = n) by (rewrite repeat_length; auto).
    assert (Hn': length (rev (repeat x n)) = n) by (rewrite rev_length; auto).
    assert (m < n \/ m >= n) as [Hlt | Hle] by lia.
    - rewrite <- Hn in Hlt; apply nth_error_Some in Hlt as ?.
      rewrite Hn, <- Hn' in Hlt;  apply nth_error_Some in Hlt as ?.
      rewrite repeat_nth, rev_repeat_nth by lia; auto.
    - rewrite <- Hn in Hle; apply nth_error_None in Hle as ?.
      rewrite Hn, <- Hn' in Hle;  apply nth_error_None in Hle as ?.
      congruence.
  Qed.

  Lemma map_repeat {B} : forall (f : A -> B) n x,
    map f (repeat x n) = repeat (f x) n.
  Proof.
    induction n; intros; cbn; auto.
    rewrite IHn; auto.
  Qed.
End ListFacts.

Definition zipMap {A B C} (f : A -> B -> C) xs ys : list C :=
  map (fun xy => f (fst xy) (snd xy)) (combine xs ys).

Definition nsum (xs : list nat) : nat :=
  fold_right Nat.add 0 xs.

Definition geom r n := rev (map (Nat.pow r) (seq 0 n)).
Definition tens := geom 10.

Definition digs_to_nat (ds : list nat) : nat :=
  nsum (zipMap Nat.mul ds (tens (length ds))).

Lemma zipMap_split {A B C D E} : forall (f : A -> B) (g : C -> D) (h : B -> D -> E) xs ys,
  map (fun xy => h (f (fst xy)) (g (snd xy))) (combine xs ys) =
  zipMap h (map f xs) (map g ys).
Proof.
  unfold zipMap; induction xs; cbn; intros; auto.
  destruct ys; cbn; auto.
  rewrite IHxs; auto.
Qed.

Lemma zipMap_repeat_r {A B C} : forall (f : A -> B -> C) y xs n,
  n = length xs ->
  zipMap f xs (repeat y n) = map (fun x => f x y) xs.
Proof.
  unfold zipMap; induction xs; cbn; intros; subst; auto.
  erewrite <- IHxs; eauto; auto.
Qed.

Lemma nsum_mod : forall xs n,
  n <> 0 ->
  (nsum xs) mod n = nsum (map (fun x => x mod n) xs) mod n.
Proof.
  induction xs; cbn; intros; auto.
  rewrite (Nat.add_mod (a mod n)) by auto.
  rewrite <- IHxs, Nat.mod_mod, Nat.add_mod; auto.
Qed.

Lemma geom_mod : forall r n b,
  b <> 0 ->
  map (fun x => x mod b) (geom r n) = map (fun x => x mod b) (geom ((r mod b)) n).
Proof.
  unfold geom; intros.
  erewrite !map_rev, !map_map, map_ext; eauto.
  intros; apply pow_mod; auto.
Qed.

Lemma geom_one : forall n,
  geom 1 n = repeat 1 n.
Proof.
  unfold geom; intros; rewrite <- rev_repeat.
  induction n; cbn; auto.
  rewrite <- seq_shift, map_map, <- IHn.
  erewrite map_ext; auto.
  intros; cbn; lia.
Qed.

Lemma sumdigs_9_congr : forall ds,
  let n := digs_to_nat ds in
  n mod 9 = (nsum ds) mod 9.
Proof.
  intros *; subst n; unfold digs_to_nat, zipMap.
  rewrite nsum_mod, map_map by auto.
  erewrite map_ext with (g := fun xy => _).
  2: intros; rewrite Nat.mul_mod; eauto.
  erewrite (zipMap_split
    (fun x => x mod 9) (fun y => y mod 9)
    (fun x y => (x * y) mod 9)
  ).
  unfold tens; rewrite geom_mod, geom_one, map_repeat by auto.
  rewrite zipMap_repeat_r by (rewrite map_length; auto).
  erewrite map_map, map_ext with (g := fun x => _).
  2: intros; rewrite Nat.mul_1_r, Nat.mod_mod; auto.
  rewrite <- nsum_mod; easy.
Qed.

Corollary sumdigs_9_div : forall ds,
  let n := digs_to_nat ds in
  (9 | n) <-> (9 | nsum ds).
Proof.
  intros *; subst n; now rewrite <- !Nat.mod_divide, sumdigs_9_congr.
Qed.

Corollary sumdigs_3_congr : forall ds,
  let n := digs_to_nat ds in
  n mod 3 = (nsum ds) mod 3.
Proof.
  intros; subst n.
  apply mod_mul_congr with (m := 3); auto.
  apply sumdigs_9_congr.
Qed.

Corollary sumdigs_3_div : forall ds,
  let n := digs_to_nat ds in
  (3 | n) <-> (3 | nsum ds).
Proof.
  intros *; subst n; now rewrite <- !Nat.mod_divide, sumdigs_3_congr.
Qed.
