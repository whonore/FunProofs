(*
 * Hat problem.
 * A group of people are all given either a red or blue hat. They cannot communicate
 * with each other and they cannot see their own hat. They are eached asked to guess
 * what color hat they have and if any is wrong then they all lose. What strategy
 * allows them to win exactly 50% of the time?
 *)

From Coq Require Import
  PeanoNat.
From FunProofs.Lib Require Import
  Enumerate
  Util.
Import EqDecNotations.

Module Hat.
  Inductive Hat := Red | Blue.

  Global Instance Hat_eq_dec : EqDec Hat.
  Proof. constructor; decide equality. Defined.

  Definition opp h := match h with Red => Blue | Blue => Red end.

  Lemma opp_involutive : forall h, opp (opp h) = h.
  Proof. now destruct h. Qed.

  Lemma opp_neq : forall h, h <> opp h.
  Proof. now destruct h. Qed.
End Hat.

Notation Hat := Hat.Hat.
Notation Red := Hat.Red.
Notation Blue := Hat.Blue.

(* A strategy guesses a hat color given the visible hats. *)
Definition strategy := list Hat -> Hat.

(* Each person guesses by applying the strategy to all hats but their own. *)
Definition guess (s : strategy) (hats : list Hat) :=
  mapIdx (fun i => s (remove_nth i hats)) hats.

Definition count_hats color hats :=
  length (filter (fun h => h ==? color) hats).

(* The optimal strategy guesses based on the number of red (or blue equivalently)
   hats it can see. *)
Definition optimal : strategy := fun hats =>
  if Nat.even (count_hats Red hats) then Blue else Red.

(* A strategy wins if every person guesses correctly. *)
Definition wins (s : strategy) (hats : list Hat) : bool :=
  (guess s hats) ==? hats.

Lemma count_hats_same : forall hats color,
  count_hats color (color :: hats) = S (count_hats color hats).
Proof.
  unfold count_hats; intros; cbn; simplify; auto.
Qed.

Definition count_hats_opp : forall hats color ocolor,
  ocolor = Hat.opp color ->
  count_hats color (ocolor :: hats) = count_hats color hats.
Proof.
  intros; subst; cbn; rewrite eqb_false; auto using Hat.opp_neq.
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

(* For any set of n hats, the number with an even number of red hats is 2^(n-1). *)
Lemma enumerate_hats_half_even' : forall n,
  let all := enumerate (Red :: Blue :: nil) n in
  let evens := filter (fun hats => Nat.even (count_hats Red hats)) all in
  length evens = 2 ^ (n - 1).
Proof.
  induction n; cbn; auto.
  cbn in IHn.
  rewrite flat_map_concat_map, <- concat_filter_map, map_map.
  erewrite map_ext with (g := fun x => if Nat.even (count_hats Red x) then _ else _).
  2:{
    intros; cbn [filter].
    rewrite count_hats_same, count_hats_opp by auto.
    rewrite Nat.even_succ, <- Nat.negb_even.
    destruct (Nat.even _); cbn; auto.
  }
  erewrite concat_length with (n := 1).
  - rewrite map_length, enumerate_length; cbn.
    rewrite Nat.sub_0_r, Nat.add_0_r; auto.
  - rewrite Forall_forall; intros *.
    rewrite in_map_iff.
    intros (? & ? & ?); subst.
    destruct (Nat.even _); cbn; auto.
Qed.

(* For any set of n hats, exactly half have an even number of red hats. *)
Corollary enumerate_hats_half_even : forall n,
  0 < n ->
  let all := enumerate (Red :: Blue :: nil) n in
  let evens := filter (fun hats => Nat.even (count_hats Red hats)) all in
  2 * length evens = length all.
Proof.
  intros; subst all evens.
  rewrite enumerate_hats_half_even', enumerate_length; cbn [length].
  change 2 with (2 ^ 1) at 1.
  rewrite <- Nat.pow_add_r.
  replace (1 + (n - 1)) with n; lia.
Qed.

(* If the number of red hats is even then the optimal strategy guarantees every
   guess to be correct. Otherwise every guess is wrong. *)
Theorem guess_wins_even : forall hats,
  guess optimal hats = if Nat.even (count_hats Red hats) then hats else map Hat.opp hats.
Proof.
  induction hats as [| h hats]; intros; [cbn; auto |].
  destruct h.
  - cbn -[guess Nat.even].
    rewrite Nat.even_succ, <- Nat.negb_even.
    fold (count_hats Red hats).
    rewrite apply_guess_red, IHhats; unfold optimal.
    destruct (Nat.even _); cbn; auto.
    erewrite map_map, map_ext, map_id; auto.
    intros; rewrite Hat.opp_involutive; auto.
  - cbn -[guess Nat.even].
    fold (count_hats Red hats).
    rewrite apply_guess_blue.
    rewrite IHhats; unfold optimal.
    destruct (Nat.even _); auto.
Qed.

(* For any set of n hats, the optimal strategy guarantees a win for exactly half. *)
Theorem guess_wins_half : forall n,
  0 < n ->
  let all := enumerate (Red :: Blue :: nil) n in
  let win := filter (wins optimal) all in
  2 * length win = length all.
Proof.
  intros; subst all win; unfold wins.
  rewrite <- enumerate_hats_half_even; auto.
  erewrite filter_ext with (g := fun hats => Nat.even (count_hats Red hats)); auto.
  intros hats; rewrite guess_wins_even.
  destruct hats; auto.
  destruct (Nat.even _); simplify; auto.
  pose proof Hat.opp_neq.
  cbn; rewrite eqb_false; congruence.
Qed.

(* enumerate contains all sets of hats. *)
Corollary enumerate_hats : forall hats,
  In hats (enumerate (Red :: Blue :: nil) (length hats)).
Proof.
  intros; apply enumerate_finite.
  intros h; destruct h; cbn; auto.
Qed.
