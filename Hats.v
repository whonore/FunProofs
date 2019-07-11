(* Hat problem.
   A group of people are all given either a red or blue hat. They cannot communicate
   with each other and they cannot see their own hat. They are eached asked to guess
   what color hat they have and if any if wrong then they all lose. What strategy
   allows them to win exactly 50% of the time?
*)
Require Import List.
Require Import PeanoNat.

Module Hat.
  Inductive Hat := Red | Blue.

  Definition eq (h1 h2 : Hat) : bool :=
    match h1, h2 with
    | Red, Red | Blue, Blue => true
    | _, _ => false
    end.
  Infix "==" := eq (at level 70).

  Lemma eq_sym : forall h1 h2, (h1 == h2) = (h2 == h1).
  Proof. now destruct h1. Qed.

  Definition opp h := match h with Red => Blue | Blue => Red end.

  Lemma opp_involutive : forall h, opp (opp h) = h.
  Proof. now destruct h. Qed.

  Lemma opp_neq : forall h, (h == opp h) = false.
  Proof. now destruct h. Qed.
End Hat.

Notation Hat := Hat.Hat.
Notation Red := Hat.Red.
Notation Blue := Hat.Blue.
Infix "==" := Hat.eq (at level 70).

(* Every element of a list but the nth. *)
Definition all_but {A} (n : nat) (xs : list A) :=
  firstn n xs ++ skipn (n + 1) xs.

(* Apply f to every index of a list. *)
Definition mapIdx {A B} (f : nat -> B) (xs : list A) := map f (seq 0 (length xs)).

(* A strategy guesses a hat color given the visible hats. *)
Definition strategy := list Hat -> Hat.

(* Each person guesses by applying the strategy to all hats but their own. *)
Definition guess (s : strategy) (hats : list Hat) :=
  mapIdx (fun i => s (all_but i hats)) hats.

Definition count_hats color hats :=
  length (filter (fun h => h == color) hats).

(* The optimal strategy guesses based on the number of red (or blue equivalently)
   hats it can see. *)
Definition optimal : strategy := fun hats =>
  if Nat.even (count_hats Red hats) then Blue else Red.

Definition count_hats_opp : forall hats color ocolor,
  ocolor = Hat.opp color ->
  count_hats color (ocolor :: hats) = count_hats color hats.
Proof.
  intros; subst; cbn.
  rewrite Hat.eq_sym, Hat.opp_neq; auto.
Qed.

Lemma guess_blue : forall hats,
  optimal (Blue :: hats) = optimal hats.
Proof.
  unfold optimal; intros.
  rewrite count_hats_opp; auto.
Qed.

Lemma guess_red : forall hats,
  optimal (Red :: hats) = Hat.opp (optimal hats).
Proof.
  unfold optimal; intros; cbn.
  unfold count_hats.
  destruct (length _); cbn -[Nat.even]; auto.
  rewrite Nat.even_succ, <- Nat.negb_even.
  destruct (Nat.even _); auto.
Qed.

Lemma apply_guess_blue : forall hats,
  guess optimal (Blue :: hats) = optimal hats :: guess optimal hats.
Proof.
  unfold guess, mapIdx; intros; cbn.
  rewrite <- seq_shift, map_map.
  erewrite map_ext; auto.
Qed.

Lemma apply_guess_red : forall hats,
  guess optimal (Red :: hats) = optimal hats :: map Hat.opp (guess optimal hats).
Proof.
  unfold guess, mapIdx; intros; cbn.
  rewrite <- seq_shift, !map_map.
  erewrite map_ext; auto.
  intros; cbn; rewrite guess_red; auto.
Qed.

(* If the number of red hats is even then the optimal strategy guarantees every
   guess to be correct. Otherwise every guess is wrong. If the distribution of
   hat colors is uniform then results in a win 50% of the time. *)
Theorem guess_wins_half : forall hats,
  let answer := guess optimal hats in
  if Nat.even (count_hats Red hats) then answer = hats
  else answer = map Hat.opp hats.
Proof.
  induction hats as [| h hats]; intros; subst answer; [cbn; auto |].
  destruct h.
  - cbn -[guess Nat.even].
    rewrite Nat.even_succ, <- Nat.negb_even.
    fold (count_hats Red hats).
    rewrite apply_guess_red.
    unfold optimal at 1 3.
    destruct (Nat.even _); try congruence.
    cbn; rewrite IHhats, map_map.
    erewrite map_ext, map_id; auto.
    intros; rewrite Hat.opp_involutive; auto.
  - cbn -[guess Nat.even].
    fold (count_hats Red hats).
    rewrite apply_guess_blue.
    unfold optimal at 1 3.
    destruct (Nat.even _); congruence.
Qed.
