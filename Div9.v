(* Divisibility by 9
   A decimal number is divisible by 9 iff the sum of its digits are. *)

Require Import Lia.
Require Import List.
Require Import Util.
Require Import ZArith.

Open Scope Z.

Ltac pop_hyp H name :=
  match goal with
  | |- H -> _ => intros name
  | |- ?x -> _ => let tmp := fresh x in intros tmp; pop_hyp H name; revert tmp
  end.

Ltac ninduction x :=
  let tmp := fresh in
  let IH := fresh "IH" x in
  intros until x; pop_hyp (0 <= x) tmp;
    pattern x; apply natlike_ind; [| | assumption];
    clear x tmp; [| intros x Hle IH].

Section ModFacts.
  Lemma pow_mod : forall x r r' n,
    0 <= x -> n <> 0 ->
    r mod n = r' mod n ->
    (r ^ x) mod n = (r' ^ x) mod n.
  Proof.
    ninduction x; cbn; intros * ? Heq; auto.
    rewrite !Z.pow_succ_r by auto.
    rewrite (Z.mul_mod Z0); auto.
    erewrite <- Heq, <- IHx, Z.mul_mod; auto.
  Qed.

  Lemma mod_mod_mul : forall x n m,
    n <> 0 -> 0 < m ->
    (x mod (n * m)) mod n = x mod n.
  Proof.
    intros.
    rewrite Z.rem_mul_r by auto.
    rewrite Z.add_mod, (Z.mul_comm n), Z.mod_mul by auto; cbn.
    rewrite Z.add_0_r, !Z.mod_mod; auto.
  Qed.

  Lemma mod_mul_congr : forall x y n m,
    n <> 0 -> 0 < m ->
    x mod (n * m) = y mod (n * m) ->
    x mod n = y mod n.
  Proof.
    intros * ? ? Hmod.
    assert (n * m <> 0) by (apply Z.neq_mul_0; lia).
    assert (x mod (n * m) = 0 \/ x mod (n * m) <> 0) as [Heq0 |] by lia.
    - rewrite Heq0 in Hmod; symmetry in Hmod.
      rewrite Z.mod_divide in Heq0, Hmod by auto.
      destruct Heq0, Hmod; subst.
      rewrite !(Z.mul_comm n m), !Z.mul_assoc, !Z.mod_mul; auto.
    - rewrite (Z.mod_eq y) in Hmod by auto.
      replace y with ((m * (y / (n * m)) * n) + x mod (n * m)) by lia.
      rewrite Z.add_mod, Z.mod_mul by auto; cbn.
      rewrite mod_mod_mul, Z.mod_mod; auto.
  Qed.
End ModFacts.

Section ListFacts.
  Context {A : Type}.

  Open Scope nat.

  Lemma list_eq_pointwise : forall (xs ys : list A),
    xs = ys <-> (forall n, nth_error xs n = nth_error ys n).
  Proof.
    split; intros Heq; subst; auto.
    revert ys Heq; induction xs; intros; destruct ys;
      auto; try solve [now specialize (Heq 0)].
    f_equal.
    - specialize (Heq 0); inj; auto.
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

  Lemma combine_app {B} : forall (xs xs' : list A) (ys ys' : list B),
    length xs = length ys ->
    length xs' = length ys' ->
    combine (xs ++ xs') (ys ++ ys') = combine xs ys ++ combine xs' ys'.
  Proof.
    induction xs; destruct ys; cbn; intros * Hlen Hlen'; auto; try easy.
    rewrite IHxs; auto.
  Qed.

  Lemma combine_rev {B} : forall (xs : list A) (ys : list B),
    length xs = length ys ->
    rev (combine xs ys) = combine (rev xs) (rev ys).
  Proof.
    induction xs; destruct ys; cbn; intros * Hlen; auto; try easy.
    rewrite combine_app, IHxs; auto.
    rewrite !rev_length; auto.
  Qed.

  Lemma combine_nth_error {B} : forall n (xs : list A) (ys : list B) p,
    length xs = length ys ->
    nth_error (combine xs ys) n = Some p ->
    nth_error xs n = Some (fst p) /\ nth_error ys n = Some (snd p).
  Proof.
    induction n; cbn; intros * Hlen Hnth; auto.
    - now destruct xs, ys; cbn in *; inj; auto.
    - now destruct xs, ys; cbn in *; auto.
  Qed.
End ListFacts.

Section ZipMap.
  Context {A B C : Type}.

  Definition zipMap (f : A -> B -> C) xs ys : list C :=
    map (fun xy => f (fst xy) (snd xy)) (combine xs ys).

  Lemma zipMap_split {D E} : forall (f : D -> A) (g : E -> B) (h : A -> B -> C) xs ys,
    map (fun xy => h (f (fst xy)) (g (snd xy))) (combine xs ys) =
    zipMap h (map f xs) (map g ys).
  Proof.
    unfold zipMap; induction xs; cbn; intros; auto.
    destruct ys; cbn; auto.
    rewrite IHxs; auto.
  Qed.

  Lemma zipMap_repeat_r : forall (f : A -> B -> C) y xs n,
    n = length xs ->
    zipMap f xs (repeat y n) = map (fun x => f x y) xs.
  Proof.
    unfold zipMap; induction xs; cbn; intros; subst; auto.
    erewrite <- IHxs; eauto; auto.
  Qed.
End ZipMap.

Section AltMap.
  Fixpoint altmap {A} (f : A -> A) (xs : list A) : list A :=
    match xs with
    | nil => nil
    | x :: nil => x :: nil
    | x :: x' :: xs' => x :: f x' :: altmap f xs'
    end.

  Lemma altmap_length {A} : forall f (xs : list A),
    length (altmap f xs) = length xs.
  Proof.
    induction xs as [| x xs]; cbn [length]; auto.
    rewrite <- IHxs.
    clear; revert x; induction xs; cbn [length]; intros; auto.
    rewrite IHxs; auto.
  Qed.

  Lemma altmap_nth_error : forall A f (n : nat) xs (x : A),
    nth_error xs n = Some x ->
    (Nat.Even n /\ nth_error (altmap f xs) n = Some x) \/
    (Nat.Odd n /\ nth_error (altmap f xs) n = Some (f x)).
  Proof.
    intros until n; pattern n; apply Nat.pair_induction; clear n; intros *.
    { now hnf; intros; subst. }
    - rewrite <- Nat.even_spec.
      destruct xs as [| ? []]; inversion 1; subst; cbn; auto.
    - rewrite <- Nat.odd_spec.
      destruct xs as [| ? []]; inversion 1; subst; cbn; auto.
    - intros IHn _ * Hnth.
      rewrite Nat.Even_succ_succ, Nat.Odd_succ_succ.
      assert (S (S n) < length xs)%nat by (apply nth_error_Some; congruence).
      destruct xs as [| ? []]; cbn in *; try lia; eauto.
  Qed.
End AltMap.

Section Series.
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

Definition digs_to_Z (ds : list Z) : Z :=
  zsum (zipMap Z.mul ds (rev (tens (length ds)))).

Section Div9.
  Lemma sum_digs_9_congr : forall ds,
    let n := digs_to_Z ds in
    n mod 9 = (zsum ds) mod 9.
  Proof.
    intros *; subst n; unfold digs_to_Z, zipMap.
    rewrite zsum_mod, map_map by easy.
    erewrite map_ext with (g := fun xy => _).
    2: intros; rewrite Z.mul_mod by easy; eauto.
    erewrite (zipMap_split
      (fun x => x mod 9) (fun y => y mod 9)
      (fun x y => (x * y) mod 9)
    ).
    unfold tens; rewrite map_rev, (geom_mod _ 1), geom_one, map_repeat, rev_repeat by easy.
    rewrite zipMap_repeat_r by (rewrite map_length; auto).
    erewrite map_map, map_ext with (g := fun x => _).
    2: intros; rewrite Z.mul_1_r, Z.mod_mod; auto; lia.
    now rewrite <- zsum_mod.
  Qed.

  Corollary sum_digs_9_div : forall ds,
    let n := digs_to_Z ds in
    (9 | n) <-> (9 | zsum ds).
  Proof.
    intros *; subst n; now rewrite <- !Z.mod_divide, sum_digs_9_congr.
  Qed.
End Div9.

Section Div3.
  Corollary sum_digs_3_congr : forall ds,
    let n := digs_to_Z ds in
    n mod 3 = (zsum ds) mod 3.
  Proof.
    intros; subst n.
    apply mod_mul_congr with (m := 3); try easy.
    apply sum_digs_9_congr.
  Qed.

  Corollary sum_digs_3_div : forall ds,
    let n := digs_to_Z ds in
    (3 | n) <-> (3 | zsum ds).
  Proof.
    intros *; subst n; now rewrite <- !Z.mod_divide, sum_digs_3_congr.
  Qed.
End Div3.

Section Div11.
  Lemma altsum_digs_11_congr : forall ds,
    let n := digs_to_Z ds in
    n mod 11 = (zaltsum (rev ds)) mod 11.
  Proof.
    intros *; subst n; unfold digs_to_Z, zipMap, zaltsum.
    rewrite <- zsum_rev, <- map_rev, zsum_mod, map_map, combine_rev, rev_involutive; try easy.
    2: unfold tens, geom; rewrite rev_length, map_length, seq_length; auto.
    erewrite map_ext with (g := fun xy => _).
    2: intros; rewrite Z.mul_mod by easy; eauto.
    erewrite (zipMap_split
      (fun x => x mod 11) (fun y => y mod 11)
      (fun x y => (x * y) mod 11)
    ).
    unfold tens; rewrite map_rev, (geom_mod _ (-1)), geom_none by easy.
    rewrite <- map_rev, <- zipMap_split.
    erewrite map_ext with (g := fun xy => _).
    2: intros; rewrite <- Z.mul_mod by easy; eauto.
    rewrite (zsum_mod (altmap _ _)) by easy.
    f_equal; f_equal.
    apply list_eq_pointwise; intros.
    assert (n < length ds \/ n >= length ds)%nat as [|] by lia.
    - match goal with
      | |- nth_error (map _ ?x) n = nth_error (map _ ?y) n =>
        assert (exists a b, nth_error x n = Some a /\ nth_error y n = Some b)
          as (? & ? & Hnth & Hnth')
      end.
      { match goal with
        | |- exists _ _, ?x = _ /\ ?y = _ => assert (x <> None /\ y <> None)
        end.
        { split; apply nth_error_Some;
            rewrite ?combine_length, altmap_length, rev_length, ?repeat_length; lia.
        }
        now destruct (nth_error _ _), (nth_error _); eauto.
      }
      erewrite !map_nth_error; eauto.
      rewrite Hnth'; f_equal.
      apply combine_nth_error in Hnth as (Hnth1 & Hnth2).
      2: rewrite altmap_length, rev_length, repeat_length; auto.
      assert (Hrep: nth_error (repeat 1 (length ds)) n = Some 1) by (rewrite repeat_nth; auto).
      apply altmap_nth_error with (f := Z.opp) in Hrep.
      apply altmap_nth_error with (f := Z.opp) in Hnth1.
      assert (Nat.Even n -> Nat.Odd n -> False).
      { rewrite <- Nat.even_spec, <- Nat.odd_spec; unfold Nat.odd; now destruct (Nat.even _). }
      rewrite Hnth', Hnth2 in *.
      destruct Hnth1 as [(? & ?) | (? & ?)], Hrep as [(? & ?) | (? & ?)]; intuition; inj.
      + replace (snd _) with 1 by auto; lia.
      + replace (snd _) with (-1) by auto; lia.
    - match goal with
      | |- ?x = ?y => enough (x = None /\ y = None) as (? & ?) by congruence
      end.
      split; apply nth_error_None;
        rewrite map_length, ?combine_length, altmap_length, rev_length, ?repeat_length; lia.
  Qed.

  Corollary sum_digs_11_div : forall ds,
    let n := digs_to_Z ds in
    (11 | n) <-> (11 | zaltsum (rev ds)).
  Proof.
    intros *; subst n; now rewrite <- !Z.mod_divide, altsum_digs_11_congr.
  Qed.
End Div11.
