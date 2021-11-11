From Coq Require Import
  Lia
  List
  ZArith.
From FunProofs.Lib Require Import
  AltMap
  Arith
  Extrema
  Function
  List
  Tactics.

Module Type SumOps.
  Parameter T : Type.
  Parameter T0 : T.
  Parameter T1 : T.
  Parameter Tadd : T -> T -> T.
  Parameter Tmul : T -> T -> T.
  Parameter Tsucc : T -> T.
  Parameter Tmodulo : T -> T -> T.
  Parameter T_of_nat : nat -> T.
End SumOps.

Module Type CanSum(Import S : SumOps).
  Axiom T_sring : semi_ring_theory T0 T1 Tadd Tmul eq.
  Axiom T_add_1_r : forall n, Tadd n T1 = Tsucc n.
  Axiom T_of_nat_0 : T_of_nat 0%nat = T0.
  Axiom T_of_nat_inj_S : forall n, T_of_nat (S n) = Tsucc (T_of_nat n).
  Axiom T_mod_mod : forall n m, m <> T0 -> Tmodulo (Tmodulo n m) m = Tmodulo n m.
  Axiom T_add_mod : forall n m p,
    p <> T0 -> Tmodulo (Tadd n m) p = Tmodulo (Tadd (Tmodulo n p) (Tmodulo m p)) p.
End CanSum.

Module GenSum(Import S : SumOps)(Import CS : CanSum(S)).
  Add Ring T_sring : T_sring.

  #[local] Notation "0" := T0.
  #[local] Notation "1" := T1.
  #[local] Infix "+" := Tadd.
  #[local] Infix "*" := Tmul.
  #[local] Infix "mod" := Tmodulo.
  #[local] Hint Rewrite T_of_nat_0 T_of_nat_inj_S : ring.
  #[local] Hint Rewrite <- T_add_1_r : ring.

  #[local] Ltac ring_norm := repeat (
    autorewrite with ring in *;
    try match goal with
    | H: context[?n + 0] |- _ => ring_simplify (n + 0) in H
    | H: context[0 + ?n] |- _ => ring_simplify (0 + n) in H
    | |- context[?n + 0] => ring_simplify (n + 0)
    | |- context[0 + ?n] => ring_simplify (0 + n)
    end).

  Definition sum' (n : T) ns := fold_left Tadd ns n.
  Notation sum := (sum' T0).

  #[local] Ltac fold_sums :=
    repeat match goal with
           | H: context[fold_left Tadd ?ns ?n] |- _ => fold (sum' n ns)
           | |- context[fold_left Tadd ?ns ?n] => fold (sum' n ns)
           end.

  Lemma sum_shift ns : forall n, sum' n ns = n + sum ns.
  Proof.
    induction ns as [| m ns]; intros; cbn; ring_norm; [ring |]; fold_sums.
    rewrite (IHns (_ + _)), (IHns m); ring.
  Qed.

  #[local] Ltac shift_sums :=
    repeat match goal with
           | H: context[sum' ?n ?ns] |- _ =>
             lazymatch n with
             | T0 => fail
             | _ => rewrite (sum_shift ns n) in H
             end
           | |- context[sum' ?n ?ns] =>
             lazymatch n with
             | T0 => fail
             | _ => rewrite (sum_shift ns n)
             end
           end.

  Ltac normalize_sums := fold_sums; shift_sums.

  #[local] Ltac prep := cbn in *; normalize_sums; ring_norm.

  Lemma sum_const {A} (ns : list A) : forall n m,
    sum' n (map (const m) ns) = n + m * T_of_nat (length ns).
  Proof.
    induction ns; intros; prep; [ring |].
    rewrite IHns; ring.
  Qed.

  Lemma sum_repeat p : forall n m, sum' n (repeat m p) = n + m * T_of_nat p.
  Proof.
    induction p; intros; prep; [ring |].
    rewrite IHp; ring.
  Qed.

  Lemma sum_add (f g : T -> T) ns : forall n,
    sum' n (map (fun m => f m + g m) ns) = sum' n (map f ns) + sum (map g ns).
  Proof.
    induction ns; intros; prep; [ring |].
    rewrite IHns; ring.
  Qed.

  Lemma sum_mul (f : T -> T) ns : forall n m,
    sum' n (map (fun p => m * f p) ns) = n + m * sum (map f ns).
  Proof.
    induction ns; intros; prep; [ring |].
    rewrite IHns; ring.
  Qed.

  Lemma sum_succ ns n : sum' n (map Tsucc ns) = T_of_nat (length ns) + sum' n ns.
  Proof.
    erewrite map_ext by (symmetry; apply T_add_1_r).
    rewrite sum_add.
    fold (@const _ T 1); rewrite sum_const, map_id; ring.
  Qed.

  Lemma sum_mul_id ns n m : sum' n (map (Tmul m) ns) = n + m * sum ns.
  Proof. rewrite sum_mul, map_id; auto. Qed.

  Lemma sum_rev ns : forall n, sum' n (rev ns) = sum' n ns.
  Proof.
    induction ns; intros; cbn; auto.
    rewrite fold_left_app; cbn; normalize_sums.
    rewrite IHns; ring.
  Qed.

  Lemma sum_app ns ms n m p :
    n = m + p -> sum' n (ns ++ ms) = sum' m ns + sum' p ms.
  Proof. unfold sum'; intros; subst; rewrite fold_left_app; normalize_sums; ring. Qed.

  Lemma sum_app0 ns ms : sum (ns ++ ms) = sum ns + sum ms.
  Proof. now rewrite (sum_app _ _ 0 0 0) by ring. Qed.

  Lemma sum_mod ns : forall n m,
    m <> 0 -> (sum' n ns) mod m = sum' (n mod m) (map (fun x => x mod m) ns) mod m.
  Proof.
    induction ns; intros; cbn; fold_sums; [now rewrite T_mod_mod |].
    rewrite IHns by auto. normalize_sums.
    now rewrite !(T_add_mod _ (sum _)), <- (T_add_mod n _), T_mod_mod.
  Qed.
End GenSum.

Module Type AltSumOps(Import S : SumOps).
  Parameter Topp : T -> T.
End AltSumOps.

Module GenAltSum(S : SumOps)(CS : CanSum(S))(AS : AltSumOps(S)).
  Module GS := GenSum(S)(CS).
  Import S AS GS.
  Definition altsum (ns : list T) : T := sum (altmap Topp ns).
End GenAltSum.

Module ZSumOps <: SumOps.
  Definition T := Z.
  Definition T0 := 0%Z.
  Definition T1 := 1%Z.
  Definition Tadd := Z.add.
  Definition Tmul := Z.mul.
  Definition Tsucc := Z.succ.
  Definition Tmodulo := Z.modulo.
  Definition T_of_nat := Z.of_nat.
End ZSumOps.

Module ZCanSum <: CanSum(ZSumOps).
  Import ZSumOps.

  Lemma T_sring : semi_ring_theory T0 T1 Tadd Tmul eq.
  Proof. constructor; auto with zarith. Qed.

  Lemma T_add_1_r : forall n, Tadd n T1 = Tsucc n.
  Proof. apply Z.add_1_r. Qed.

  Lemma T_of_nat_0 : T_of_nat 0%nat = T0.
  Proof. apply Nat2Z.inj_0. Qed.

  Lemma T_of_nat_inj_S n : T_of_nat (S n) = Tsucc (T_of_nat n).
  Proof. apply Nat2Z.inj_succ. Qed.

  Lemma T_mod_mod n m : m <> T0 -> Tmodulo (Tmodulo n m) m = Tmodulo n m.
  Proof. apply Z.mod_mod. Qed.

  Lemma T_add_mod n m p :
    p <> T0 -> Tmodulo (Tadd n m) p = Tmodulo (Tadd (Tmodulo n p) (Tmodulo m p)) p.
  Proof. apply Z.add_mod. Qed.
End ZCanSum.

Module ZAltSumOps <: AltSumOps(ZSumOps).
  Definition Topp := Z.opp.
End ZAltSumOps.

Module ZSum := GenSum(ZSumOps)(ZCanSum).
Module ZAltSum := GenAltSum(ZSumOps)(ZCanSum)(ZAltSumOps).

Module NSumOps <: SumOps.
  Definition T := nat.
  Definition T0 := 0%nat.
  Definition T1 := 1%nat.
  Definition Tadd := Nat.add.
  Definition Tmul := Nat.mul.
  Definition Tsucc := Nat.succ.
  Definition Tmodulo := Nat.modulo.
  Definition T_of_nat := @id nat.
End NSumOps.

Module NCanSum <: CanSum(NSumOps).
  Import NSumOps.

  Lemma T_sring : semi_ring_theory T0 T1 Tadd Tmul eq.
  Proof. unfold T0, T1, Tadd, Tmul; constructor; auto with zarith. Qed.

  Lemma T_add_1_r n : Tadd n T1 = Tsucc n.
  Proof. apply Nat.add_1_r. Qed.

  Lemma T_of_nat_0 : T_of_nat 0%nat = T0.
  Proof. auto. Qed.

  Lemma T_of_nat_inj_S n : T_of_nat (S n) = Tsucc (T_of_nat n).
  Proof. auto. Qed.

  Lemma T_mod_mod n m : m <> T0 -> Tmodulo (Tmodulo n m) m = Tmodulo n m.
  Proof. apply Nat.mod_mod. Qed.

  Lemma T_add_mod n m p :
    p <> T0 -> Tmodulo (Tadd n m) p = Tmodulo (Tadd (Tmodulo n p) (Tmodulo m p)) p.
  Proof. apply Nat.add_mod. Qed.
End NCanSum.

Module NSum := GenSum(NSumOps)(NCanSum).

Lemma nsum_bound ns n :
  NSum.sum' n ns <= n + length ns * Z.to_nat (maximum0 (map Z.of_nat ns)).
Proof.
  induction ns; cbn -[maximum0] in *; [lia |]; NSum.normalize_sums.
  rewrite maximum0_unfold by lia.
  unfold NSumOps.Tadd.
  match goal with
  | |- ?n + ?x + ?y <= ?n + (?z + ?w) => enough (x <= z /\ n + y <= n + w) by lia
  end.
  split; [lia | etransitivity; eauto].
  apply Nat.add_le_mono, Nat.mul_le_mono_nonneg_l; lia.
Qed.
