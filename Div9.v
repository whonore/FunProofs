(*
 * Divisibility rules.
 * E.g., an integer is divisible by 9 iff the sum of its digits are.
 *)

From Coq Require Import
  ZArith.
From FunProofs.Lib Require Import
  Series
  Util
  ZipMap.
Import ListNotations.

Open Scope Z.

Definition Z_of_digits (ds : list Z) : Z :=
  zsum (zipMap Z.mul ds (rev (tens (length ds)))).

Lemma Z_of_digits_mod : forall ds m,
  let n := Z_of_digits ds in
  m <> 0 ->
  n mod m = zsum (zipMap
    (fun x y => (x * y) mod m)
    (map (fun x => x mod m) ds)
    (map (fun y => y mod m) (rev (tens (length ds))))) mod m.
Proof.
  intros; subst n.
  rewrite <- zipMap_split.
  unfold Z_of_digits, zipMap.
  rewrite zsum_mod, map_map by easy.
  erewrite map_ext with (g := fun xy => _); auto.
  intros; rewrite Z.mul_mod by easy; eauto.
Qed.

Section Div9.
  Lemma sum_digs_9_congr : forall ds,
    let n := Z_of_digits ds in
    n mod 9 = (zsum ds) mod 9.
  Proof.
    intros; subst n; rewrite Z_of_digits_mod by easy.
    unfold tens; rewrite map_rev, (geom_mod _ 1), geom_one, map_repeat, rev_repeat by easy.
    rewrite zipMap_repeat_r, map_map by (now rewrite map_length).
    erewrite map_ext with (g := fun x => _).
    2: now intros; rewrite Z.mul_1_r, Z.mod_mod.
    symmetry; now apply zsum_mod.
  Qed.

  Corollary divisibility_9 : forall ds,
    let n := Z_of_digits ds in
    (9 | n) <-> (9 | zsum ds).
  Proof.
    intros; subst n; now rewrite <- !Z.mod_divide, sum_digs_9_congr.
  Qed.
End Div9.

Section Div3.
  Corollary sum_digs_3_congr : forall ds,
    let n := Z_of_digits ds in
    n mod 3 = (zsum ds) mod 3.
  Proof.
    intros; subst n.
    apply mod_mul_congr with (m := 3); try easy.
    apply sum_digs_9_congr.
  Qed.

  Corollary divisibility_3 : forall ds,
    let n := Z_of_digits ds in
    (3 | n) <-> (3 | zsum ds).
  Proof.
    intros; subst n; now rewrite <- !Z.mod_divide, sum_digs_3_congr.
  Qed.
End Div3.

Section Div11.
  Lemma altsum_digs_11_congr : forall ds,
    let n := Z_of_digits ds in
    n mod 11 = (zaltsum (rev ds)) mod 11.
  Proof.
    intros; subst n; rewrite Z_of_digits_mod by easy.
    rewrite <- zsum_rev, zipMap_rev, <- !map_rev, rev_involutive.
    2: unfold tens; now rewrite !map_length, rev_length, geom_length.
    unfold tens; rewrite map_rev, (geom_mod _ (-1)), geom_none by easy.
    rewrite <- map_rev, <- zipMap_split.
    erewrite map_ext with (g := fun xy => _).
    2: intros; rewrite <- Z.mul_mod by easy; eauto.
    unfold zaltsum; rewrite (zsum_mod (altmap _ _)) by easy.
    do 2 f_equal.
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
      destruct Hnth1 as [(? & ?) | (? & ?)], Hrep as [(? & ?) | (? & ?)]; intuition; simplify.
      + replace (snd _) with 1 by auto; lia.
      + replace (snd _) with (-1) by auto; lia.
    - match goal with
      | |- ?x = ?y => enough (x = None /\ y = None) as (? & ?) by congruence
      end.
      split; apply nth_error_None;
        rewrite map_length, ?combine_length, altmap_length, rev_length, ?repeat_length; lia.
  Qed.

  Corollary divisibility_11 : forall ds,
    let n := Z_of_digits ds in
    (11 | n) <-> (11 | zaltsum (rev ds)).
  Proof.
    intros; subst n; now rewrite <- !Z.mod_divide, altsum_digs_11_congr.
  Qed.
End Div11.

Section Div2.
  Lemma last_dig_even_congr : forall ds,
    let n := Z_of_digits ds in
    n mod 2 = (last ds 0) mod 2.
  Proof.
    intros; subst n; rewrite Z_of_digits_mod by easy.
    assert (ds = nil \/ 0 < length ds)%nat as [|]
      by (destruct ds; cbn; intuition lia); [subst; auto |].
    unfold tens; rewrite map_rev, (geom_mod _ 0), geom_zero, map_cons, map_repeat by easy.
    rewrite (@app_removelast_last _ ds 0) at 1 by (now destruct ds).
    rewrite map_app; cbn [rev]; rewrite rev_repeat, zipMap_app; auto.
    2: now rewrite map_length, repeat_length, removelast_length.
    rewrite zipMap_repeat_r by (now rewrite map_length, removelast_length).
    erewrite map_map, map_ext with (g := fun x => _).
    2: now intros; rewrite Z.mul_0_r; cbn.
    rewrite map_const, removelast_length, zsum_app0, zsum_repeat; cbn.
    now rewrite Z.mul_1_r, !Z.mod_mod.
  Qed.

  Lemma divisibility_2 : forall ds,
    let n := Z_of_digits ds in
    (2 | n) <-> (2 | last ds 0).
  Proof.
    intros; subst n; now rewrite <- !Z.mod_divide, last_dig_even_congr.
  Qed.
End Div2.
