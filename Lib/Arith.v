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
    try intros until x; pop_hyp (0 <= x) tmp;
    pattern x; apply natlike_ind; [| | assumption];
      clear x tmp; [| intros x Hle IH].

  Lemma pow_mod x : forall r r' n,
    0 <= x -> n <> 0 -> r mod n = r' mod n -> (r ^ x) mod n = (r' ^ x) mod n.
  Proof.
    ninduction x; cbn; intros * ? Heq; auto.
    rewrite !Z.pow_succ_r by auto.
    rewrite (Z.mul_mod Z0); auto.
    erewrite <- Heq, <- IHx, Z.mul_mod; auto.
  Qed.

  Lemma mod_mod_mul x n m : n <> 0 -> 0 < m -> (x mod (n * m)) mod n = x mod n.
  Proof.
    intros.
    rewrite Z.rem_mul_r by auto.
    rewrite Z.add_mod, (Z.mul_comm n), Z.mod_mul by auto; cbn.
    rewrite Z.add_0_r, !Z.mod_mod; auto.
  Qed.

  Lemma mod_mul_congr x y n m :
    n <> 0 -> 0 < m -> x mod (n * m) = y mod (n * m) -> x mod n = y mod n.
  Proof.
    intros ? ? Hmod.
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

Section NModFacts.
  Lemma Even_mod_Even n m : Nat.Even n -> Nat.Even m -> Nat.Even (n mod m).
  Proof.
    intros (n' & ->) (m' & ->).
    assert (m' = 0 \/ m' <> 0) as [-> | ?] by lia; [now rewrite <- Nat.even_spec |].
    rewrite Nat.mul_mod_distr_l by lia; hnf; eauto.
  Qed.

  Lemma Odd_mod_Even n m : m <> 0 -> Nat.Odd n -> Nat.Even m -> Nat.Odd (n mod m).
  Proof.
    intros ? (n' & ->) (m' & ->).
    rewrite Nat.mod_mul_r by lia.
    rewrite (Nat.mul_comm 2 n'), Nat.div_add_l, Nat.add_0_r by lia.
    rewrite Nat.add_mod, Nat.mod_mul, Nat.mod_1_l by lia.
    rewrite Nat.add_comm; hnf; eauto.
  Qed.

  Corollary even_mod_even n m :
    m <> 0 -> Nat.even m = true -> Nat.even (n mod m) = Nat.even n.
  Proof.
    intros ? ?%Nat.even_spec.
    destruct (Nat.Even_or_Odd n) as [Heven | Hodd].
    - pose proof Heven as ->%Nat.even_spec.
      eapply (Even_mod_Even n m), Nat.even_spec in Heven as ->; auto.
    - rewrite <- !Nat.negb_odd.
      pose proof Hodd as ->%Nat.odd_spec.
      eapply (Odd_mod_Even n m), Nat.odd_spec in Hodd as ->; auto.
  Qed.

  Corollary odd_mod_even n m :
    m <> 0 -> Nat.even m = true -> Nat.odd (n mod m) = Nat.odd n.
  Proof. now intros; rewrite <- !Nat.negb_even, even_mod_even. Qed.
End NModFacts.

Section DivNatFacts.
  Open Scope nat.

  Lemma div_range n x y : n * y <= x < (n + 1) * y -> x / y = n.
  Proof.
    intros Hrange.
    replace x with (y * n + (x - y * n)) by lia.
    symmetry; eapply Nat.div_unique; eauto; lia.
  Qed.
End DivNatFacts.

Section ZMinMaxFacts.
  Open Scope Z.

  Lemma Zmax_case_strong_lt n m (P : Z -> Type) :
    (m < n -> P n) -> (n <= m -> P m) -> P (Z.max n m).
  Proof.
    intros; destruct (Z_lt_le_dec m n); rewrite ?Z.max_l, ?Z.max_r by lia; auto.
  Qed.

  Lemma Zmin_case_strong_lt n m (P : Z -> Type) :
    (m < n -> P m) -> (n <= m -> P n) -> P (Z.min n m).
  Proof.
    intros; destruct (Z_lt_le_dec m n); rewrite ?Z.min_l, ?Z.min_r by lia; auto.
  Qed.
End ZMinMaxFacts.
