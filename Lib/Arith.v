From Coq Require Import
  Lia
  ZArith.

Section ModFacts.
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

Section DivNatFacts.
  Open Scope nat.

  Lemma div_range : forall n x y,
    n * y <= x < (n + 1) * y ->
    x / y = n.
  Proof.
    intros * Hrange.
    replace x with (y * n + (x - y * n)) by lia.
    symmetry; eapply Nat.div_unique; eauto; lia.
  Qed.
End DivNatFacts.
