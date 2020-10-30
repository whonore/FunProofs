(*
 * Definition of Graham's number and facts about Knuth "up-arrow" notation.
 *)

From Coq Require Import
  Program.Wf.
From FunProofs.Lib Require Import
  Util.

Definition lex_order (xs ys : nat * nat) :=
  let '(x1, x2) := xs in let '(y1, y2) := ys in
  x1 < y1 \/ (x1 = y1 /\ x2 < y2).

Lemma lex_order_wf : well_founded lex_order.
Proof.
  intros [a b]; pattern a, b; apply lt_wf_double_rec; clear a b; intros.
  constructor; intros [] [| []]; subst; auto.
Defined.

Lemma sub_1_lt : forall n, n <> 0 -> n - 1 < n.
Proof.
  induction n; intros; [easy |].
  cbn; destruct n; constructor.
Defined.

Definition up' (b : nat) : (nat * nat) -> nat.
Proof.
  unshelve refine (Fix lex_order_wf (fun _ => nat)
    (fun (args : nat * nat)
         (up' : forall args', lex_order args' args -> nat) =>
       let n := fst args in let p := snd args in
       if Nat.eq_dec n O then b * p
       else if Nat.eq_dec p O then 1
       else up' (n - 1, (up' (n, p - 1) _)) _));
    destruct args as []; subst n p; cbn in *; auto using sub_1_lt.
Defined.
Definition up n b p : nat := up' b (n, p).

Notation "b '^{' n '}' p" := (up n b p) (at level 30, right associativity).

Lemma up_0_mul : forall b p, b ^{0} p = b * p.
Proof. auto. Qed.

Lemma up_pow_0_1 : forall n b, b ^{S n} 0 = 1.
Proof. destruct n; auto. Qed.

Lemma up_unroll : forall n b p,
  b ^{S n} (S p) = b ^{n} b ^{S n} p.
Proof.
  intros; remember (up _ _ (up _ _ _)) as rhs.
  unfold up, up'; rewrite Init.Wf.Fix_eq.
  - repeat fold (up' b); cbn [fst snd].
    repeat (destruct (Nat.eq_dec _ _); [easy |]).
    subst rhs; unfold up; repeat f_equal; lia.
  - intros [] **; repeat (destruct Nat.eq_dec; auto).
    cbn; rewrite !H; auto.
Qed.

Corollary up_1_pow : forall b p, b ^{1} p = b ^ p.
Proof.
  induction p; auto.
  rewrite up_unroll, up_0_mul, IHp; auto.
Qed.

Corollary up_pow_1_base : forall n b, b ^{n} 1 = b.
Proof.
  induction n; intros.
  - rewrite up_0_mul, Nat.mul_1_r; auto.
  - rewrite up_unroll, up_pow_0_1; auto.
Qed.

Corollary up_1_1 : forall p n, 1 ^{S n} p = 1.
Proof.
  induction p; intros.
  - rewrite up_pow_0_1; auto.
  - rewrite up_unroll, IHp, up_pow_1_base; auto.
Qed.

Corollary up_2_2_4 : forall n, 2 ^{n} 2 = 4.
Proof.
  induction n; auto.
  rewrite !up_unroll, up_pow_0_1, up_pow_1_base; auto.
Qed.

Definition strict_increase (min : nat) (f : nat -> nat) :=
  forall n n', min < n < n' -> f n < f n'.

Definition strict_increase_1 (min : nat) (f : nat -> nat) :=
  forall n, min < n -> f n < f (S n).

Definition abundant (min : nat) (f : nat -> nat) :=
  forall n, min < n -> n < f n.

Lemma strict_increase_iff : forall min f,
  strict_increase_1 min f <-> strict_increase min f.
Proof.
  unfold strict_increase, strict_increase_1; split; intros * Hstrict **.
  - induction n'; [easy |].
    assert (n < n' \/ n = n') as [] by lia; subst; [| eapply Hstrict; lia].
    etransitivity; [eapply IHn'; lia |]; eapply Hstrict; lia.
  - apply Hstrict; lia.
Qed.

Lemma strict_increase_pos : forall min f, strict_increase min f ->
  min < f (S min) -> forall n, min < n -> min < f n.
Proof.
  intros * Hstrict Hf1; induction n; intros; try easy.
  assert (min < n \/ n = min) as [|] by lia; subst; auto.
  etransitivity; [eapply IHn; eauto |].
  eapply Hstrict; lia.
Qed.

Section Composition.
  Variables (f g : nat -> nat) (b : nat).
  Hypotheses (b_min : 1 < b) (f_min : 1 < f 1).
  Hypotheses (f_strict : strict_increase 0 f) (f_abundant : abundant 0 f).
  Hypotheses (g_base : g 1 = b) (g_succ : forall n, g (S n) = f (g n)).

  Lemma strict_abundant_comp_pos : forall n, 0 < n -> 0 < g n.
  Proof.
    induction n as [| []]; intros; [easy | |].
    - rewrite g_base; lia.
    - rewrite g_succ; apply strict_increase_pos; auto; lia.
  Qed.

  Lemma strict_abundant_comp_strict : strict_increase 0 g.
  Proof.
    rewrite <- strict_increase_iff; hnf; intros.
    rewrite g_succ; apply f_abundant, strict_abundant_comp_pos; auto.
  Qed.

  Lemma strict_abundant_comp_abundant : abundant 0 g.
  Proof.
    hnf; induction n as [| []]; intros; [easy | |].
    - rewrite g_base; auto.
    - enough (g (S n) < g (S (S n))) by lia.
      eapply strict_abundant_comp_strict with (n := S n); lia.
  Qed.
End Composition.

Section UpPowStrictAbundant.
  Variable (b : nat).
  Hypothesis (b_min : 1 < b).
  Notation f := (fun n p => b ^{n} p) (only parsing).

  Let mul_strict : strict_increase 0 (f 0).
  Proof.
    hnf; intros; apply Nat.mul_lt_mono_pos_l; auto; lia.
  Qed.

  Let mul_abundant : abundant 0 (f 0).
  Proof.
    hnf; intros.
    rewrite <- (Nat.mul_1_l n) at 1.
    apply Nat.mul_lt_mono_pos_r; lia.
  Qed.

  Corollary up_pow_strict_abundant : forall n, strict_increase 0 (f n) /\ abundant 0 (f n).
  Proof.
    induction n; auto using mul_strict, mul_abundant; destruct IHn; split.
    - eapply strict_abundant_comp_strict with (f := fun p => b ^{n} p) (b := b);
        eauto using up_unroll.
      rewrite up_pow_1_base; auto.
    - eapply strict_abundant_comp_abundant with (f := fun p => b ^{n} p) (b := b);
        eauto using up_unroll.
      rewrite up_pow_1_base; auto.
  Qed.
End UpPowStrictAbundant.

Section UpBaseStrict.
  Corollary up_pos : forall b n p, 0 < (S b) ^{S n} p.
  Proof.
    intros; destruct b; [rewrite up_1_1; auto |].
    destruct p; [rewrite up_pow_0_1; auto |].
    apply strict_increase_pos; auto; try lia.
    - eapply up_pow_strict_abundant; lia.
    - rewrite up_pow_1_base; lia.
  Qed.

  Corollary up_base_strict : forall n p, 0 < p -> strict_increase 0 (fun b => b ^{n} p).
  Proof.
    induction n; intros * Hp; hnf; intros n' n'' **.
    - apply Nat.mul_lt_mono_pos_r; lia.
    - induction p; [easy |].
      assert (0 < p \/ p = 0) as [|] by lia; subst.
      + rewrite !up_unroll.
        destruct n'; [easy |].
        etransitivity; [eapply IHn; eauto using up_pos |].
        eapply up_pow_strict_abundant; eauto using up_pos; lia.
      + rewrite !up_pow_1_base; lia.
  Qed.
End UpBaseStrict.

Section UpDegreeStrict.
  Corollary up_degree_strict : forall p b, 0 < p -> strict_increase 2 (fun n => b ^{n} p).
  Proof.
    intros * Hp; rewrite <- strict_increase_iff; hnf; intros.
    revert p b Hp; induction n; intros; try lia.
    destruct p; try easy.
    rewrite !up_unroll.
  Admitted.
End UpDegreeStrict.

(* Lemma up_pow_add : forall b p p' n, *)
(*   (b ^{n} p) ^{n} p' < b ^{n} (p + p'). *)
(* Proof. *)
(* Admitted. *)

Fixpoint graham_aux n :=
  match n with
  | O => 4
  | S n' => 3 ^{graham_aux n'} 3
  end.
Definition graham_num := graham_aux 64.
