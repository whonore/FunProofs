(* Definition of Graham's number and facts about Knuth "up-arrow" notation. *)
Require Import Arith.
Require Import Lia.
Require Import Program.Wf.

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
    destruct args as []; subst n p; cbn in *; info_auto using sub_1_lt.
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

Corollary up_2_2_4 : forall n, up n 2 2 = 4.
Proof.
  induction n; auto.
  rewrite !up_unroll, up_pow_0_1, up_pow_1_base; auto.
Qed.

Fixpoint graham_aux n :=
  match n with
  | O => 4
  | S n' => 3 ^{graham_aux n'} 3
  end.
Definition graham_num := graham_aux 64.
