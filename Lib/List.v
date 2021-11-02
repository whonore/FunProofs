From Coq Require Import
  Arith
  Lia
  List.
From FunProofs.Lib Require Import
  Tactics.
Export ListNotations.

Notation "xs @@ x" := (xs ++ [x]) (at level 60, right associativity) : list_scope.

Section ListFacts.
  Context {A : Type}.

  Lemma list_eq_pointwise (xs ys : list A) :
    xs = ys <-> (forall n, nth_error xs n = nth_error ys n).
  Proof.
    split; intros Heq; subst; auto.
    revert ys Heq; induction xs; intros; destruct ys;
      auto; try solve [now specialize (Heq 0)].
    f_equal.
    - specialize (Heq 0); simplify; auto.
    - apply IHxs; intros.
      specialize (Heq (S n)); auto.
  Qed.

  (* Every element of a list but the nth. *)
  Definition remove_nth (n : nat) (xs : list A) :=
    firstn n xs ++ skipn (n + 1) xs.

  (* Apply f to every index of a list. *)
  Definition mapIdx {B} (f : nat -> B) (xs : list A) := map f (seq 0 (length xs)).

  Fixpoint chunks' (m n : nat) (xs chunk : list A) : list (list A) :=
    match m, xs with
    | _, [] => [chunk]
    | 0, x :: xs => chunk :: chunks' n n xs [x]
    | S m, x :: xs => chunks' m n xs (chunk @@ x)
    end.

  Definition chunks (n : nat) (xs : list A) : list (list A) :=
    match xs, n with [], _ | _, 0 => [] | _, _ => chunks' n (n - 1) xs [] end.

  Section Repeat.
    Lemma repeat_nth (x : A) n : forall m, m < n -> nth_error (repeat x n) m = Some x.
    Proof.
      induction n; cbn; intros; try lia.
      destruct m; cbn; auto.
      apply IHn; lia.
    Qed.

    Lemma rev_repeat_nth (x : A) n : forall m,
      m < n -> nth_error (rev (repeat x n)) m = Some x.
    Proof.
      induction n; cbn; intros; try lia.
      assert (Hn: length (rev (repeat x n)) = n)
      by (rewrite rev_length, repeat_length; auto).
      assert (m = n \/ m < n) as [| Hlt] by lia; subst.
      - rewrite nth_error_app2 by lia.
        rewrite Hn, Nat.sub_diag; auto.
      - rewrite nth_error_app1 by lia; auto.
    Qed.

    Lemma rev_repeat (x : A) n : rev (repeat x n) = repeat x n.
    Proof.
      rewrite list_eq_pointwise; intros m.
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

    Lemma map_repeat {B} (f : A -> B) x n : map f (repeat x n) = repeat (f x) n.
    Proof.
      induction n; cbn; auto.
      rewrite IHn; auto.
    Qed.

    Lemma map_const {B} (xs : list A) (c : B) :
      map (fun _ => c) xs = repeat c (length xs).
    Proof.
      induction xs; cbn; auto.
      rewrite IHxs; auto.
    Qed.
  End Repeat.

  Section Combine.
    Context {B : Type}.

    Lemma combine_app (xs : list A) : forall xs' (ys ys' : list B),
      length xs = length ys ->
      length xs' = length ys' ->
      combine (xs ++ xs') (ys ++ ys') = combine xs ys ++ combine xs' ys'.
    Proof.
      induction xs; intros *; destruct ys; cbn; intros Hlen Hlen'; auto; try easy.
      rewrite IHxs; auto.
    Qed.

    Lemma combine_rev (xs : list A) : forall (ys : list B),
      length xs = length ys -> rev (combine xs ys) = combine (rev xs) (rev ys).
    Proof.
      induction xs; intros []; cbn; intros Hlen; auto; try easy.
      rewrite combine_app, IHxs; auto.
      rewrite !rev_length; auto.
    Qed.

    Lemma combine_nth_error n : forall (xs : list A) (ys : list B) p,
      length xs = length ys ->
      nth_error (combine xs ys) n = Some p ->
      nth_error xs n = Some (fst p) /\ nth_error ys n = Some (snd p).
    Proof.
      induction n; cbn; intros * Hlen Hnth; auto.
      - now destruct xs, ys; cbn in *; simplify; auto.
      - now destruct xs, ys; cbn in *; auto.
    Qed.
  End Combine.

  Section Concat.
    Lemma concat_length (xs : list (list A)) : forall n,
      Forall (fun x => length x = n) xs -> length (concat xs) = n * length xs.
    Proof.
      induction xs; intros * Hall; cbn; auto; inv Hall.
      erewrite app_length, IHxs; eauto; lia.
    Qed.
  End Concat.

  Section NthError.
    Lemma nth_error_nil n : @nth_error A [] n = None.
    Proof. now destruct n. Qed.
  End NthError.

  Section Last.
    Lemma removelast_length (xs : list A) : length (removelast xs) = length xs - 1.
    Proof. rewrite removelast_firstn_len, firstn_length; lia. Qed.
  End Last.
End ListFacts.
