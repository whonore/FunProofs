From Coq Require Import
  Arith
  List
  Lia.
Import ListNotations.

Fixpoint altmap {A} (f : A -> A) (xs : list A) : list A :=
  match xs with
  | [] => []
  | [x] => [x]
  | x :: x' :: xs' => x :: f x' :: altmap f xs'
  end.

Section AltMap.
  Context {A : Type} (f : A -> A).

  Lemma altmap_length (xs : list A) : length (altmap f xs) = length xs.
  Proof.
    induction xs as [| x xs]; cbn [length]; auto.
    rewrite <- IHxs.
    clear; revert x; induction xs; cbn [length]; intros; auto.
    rewrite IHxs; auto.
  Qed.

  Lemma altmap_nth_error n : forall xs (x : A),
    nth_error xs n = Some x ->
    (Nat.Even n /\ nth_error (altmap f xs) n = Some x) \/
    (Nat.Odd n /\ nth_error (altmap f xs) n = Some (f x)).
  Proof.
    pattern n; apply Nat.pair_induction; clear n; intros *.
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
