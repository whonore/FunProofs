(* Hat problem.
   A group of people are all given either a red or blue hat. They cannot communicate
   with each other and they cannot see their own hat. They are eached asked to guess
   what color hat they have and if any is wrong then they all lose. What strategy
   allows them to win exactly 50% of the time?
*)
Require Import Bool.
Require Import Lia.
Require Import List.
Require Import PeanoNat.

(* List facts *)
Lemma filter_ext : forall A (f g : A -> bool),
  (forall a : A, f a = g a) ->
  forall xs, filter f xs = filter g xs.
Proof.
  intros * Heq; induction xs; cbn; auto.
  rewrite Heq, IHxs; auto.
Qed.

Lemma filter_app : forall A xs ys (f : A -> bool),
  filter f (xs ++ ys) = filter f xs ++ filter f ys.
Proof.
  induction xs as [| x xs]; intros; cbn; auto.
  rewrite IHxs.
  destruct (f x); auto.
Qed.

Lemma filter_concat : forall A xs (f : A -> bool),
  filter f (concat xs) = concat (map (filter f) xs).
Proof.
  induction xs as [| x xs]; intros; cbn; auto.
  rewrite filter_app, IHxs; auto.
Qed.

Lemma concat_same_length : forall A (xs : list (list A)) n,
  Forall (fun x => length x = n) xs ->
  length (concat xs) = n * length xs.
Proof.
  induction xs; intros * Hall; cbn; auto.
  inversion Hall; subst; clear Hall.
  erewrite app_length, IHxs; eauto; lia.
Qed.

Module Hat.
  Inductive Hat := Red | Blue.

  Definition eq (h1 h2 : Hat) : bool :=
    match h1, h2 with
    | Red, Red | Blue, Blue => true
    | _, _ => false
    end.
  Infix "==" := eq (at level 70).

  Lemma eq_refl : forall h, (h == h) = true.
  Proof. now destruct h. Qed.

  Lemma eq_sym : forall h1 h2, (h1 == h2) = (h2 == h1).
  Proof. now destruct h1. Qed.

  Lemma eq_correct : forall h1 h2, h1 == h2 = true <-> h1 = h2.
  Proof. now destruct h1, h2. Qed.

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

(* Enumerate all lists of length n using the elements of vals. *)
Fixpoint enumerate {A} (vals : list A) (n : nat) : list (list A) :=
  match n with
  | 0 => nil :: nil
  | S n' =>
      let fs := map cons vals in
      let vs := enumerate vals n' in
      flat_map (fun xs => map (fun f => f xs) fs) vs
  end.

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

(* Lift Hat.eq to lists. *)
Fixpoint hats_eq (h1 h2 : list Hat) : bool :=
  match h1, h2 with
  | nil, nil => true
  | h :: h1', h' :: h2' => (h == h') && hats_eq h1' h2'
  | _, _ => false
  end.

(* A strategy wins if every person guesses correctly. *)
Definition wins (s : strategy) (hats : list Hat) : bool :=
  hats_eq (guess s hats) hats.

Lemma hats_eq_correct : forall h1 h2, hats_eq h1 h2 = true <-> h1 = h2.
Proof.
  induction h1; destruct h2; cbn; try easy.
  rewrite andb_true_iff, Hat.eq_correct.
  split.
  - intros (? & ?); subst; f_equal.
    apply IHh1; auto.
  - inversion 1; subst; split; auto.
    apply IHh1; auto.
Qed.

Lemma count_hats_same : forall hats color,
  count_hats color (color :: hats) = S (count_hats color hats).
Proof.
  unfold count_hats; intros; cbn.
  rewrite Hat.eq_refl; cbn; auto.
Qed.

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

Lemma enumerate_length : forall A n (vals : list A),
  length (enumerate vals n) = length vals ^ n.
Proof.
  induction n; cbn; intros; auto.
  rewrite flat_map_concat_map.
  rewrite concat_same_length with (n := length vals).
  rewrite map_length, IHn; auto.
  rewrite Forall_forall; intros *.
  rewrite in_map_iff; intros (? & ? & ?); subst.
  rewrite !map_length; auto.
Qed.

(* For any finite type, enumerate contains all sets of that type. *)
Lemma enumerate_finite : forall A xs (vals : list A),
  (forall x : A, In x vals) ->
  In xs (enumerate vals (length xs)).
Proof.
  induction xs; cbn; intros * Hfinite; auto.
  rewrite in_flat_map.
  eexists; rewrite map_map, in_map_iff; eauto.
Qed.

(* For any set of n hats, the number with an even number of red hats is 2^(n-1). *)
Lemma enumerate_hats_half_even' : forall n,
  let all := enumerate (Red :: Blue :: nil) n in
  let evens := filter (fun hats => Nat.even (count_hats Red hats)) all in
  length evens = 2 ^ (n - 1).
Proof.
  induction n; cbn; auto.
  cbn in IHn.
  rewrite flat_map_concat_map, filter_concat, map_map.
  erewrite map_ext with (g := fun x => if Nat.even (count_hats Red x) then _ else _).
  2:{
    intros; cbn [filter].
    rewrite count_hats_same, count_hats_opp by auto.
    rewrite Nat.even_succ, <- Nat.negb_even.
    destruct (Nat.even _); cbn; auto.
  }
  erewrite concat_same_length with (n := 1).
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
  destruct (Nat.even _).
  - rewrite hats_eq_correct; auto.
  - cbn; rewrite Hat.eq_sym, Hat.opp_neq; auto.
Qed.

(* enumerate contains all sets of hats. *)
Corollary enumerate_hats : forall hats,
  In hats (enumerate (Red :: Blue :: nil) (length hats)).
Proof.
  intros; apply enumerate_finite.
  intros h; destruct h; cbn; auto.
Qed.
