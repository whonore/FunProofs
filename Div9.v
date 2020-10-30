(*
 * Divisibility by 9.
 * A decimal number is divisible by 9 iff the sum of its digits are.
 *)

From Coq Require Import
  ZArith.
From FunProofs.Lib Require Import
  Series
  Util
  ZipMap.

Open Scope Z.

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
      destruct Hnth1 as [(? & ?) | (? & ?)], Hrep as [(? & ?) | (? & ?)]; intuition; simplify.
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
