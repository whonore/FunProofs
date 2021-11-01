From Coq Require Import
  Lia
  List
  ZArith.
From FunProofs.Lib Require Import
  Arith
  Function
  List
  Tactics.
From FunProofs.Lib Require Export
  AltMap.

#[local] Open Scope Z.

Section Maximum.
  Definition maximum min (xs : list Z) : Z :=
    fold_right Z.max min xs.

  Definition maximum0 (xs : list Z) : Z :=
    maximum (hd 0 xs) xs.

  Lemma maximum_case min xs (m := maximum min xs) :
    Forall (fun x => x <= m) xs /\
    (In m xs \/ (m = min /\ Forall (fun x => x < min) xs)).
  Proof.
    induction xs as [| x xs]; cbn in *; auto;
      destruct IHxs as (Hmax & Hin); fold (maximum min xs); split.
    - constructor; auto using Z.le_max_l.
      rewrite Forall_forall in *; intros * Hin'; apply Hmax in Hin'; lia.
    - rewrite Z.max_comm; pattern (Z.max (maximum min xs) x);
        apply Zmax_case_strong_lt; intros; intuition auto.
      right; split; auto; constructor; auto; lia.
  Qed.

  Lemma maximum0_case xs (m := maximum0 xs) :
    xs <> nil -> Forall (fun x => x <= m) xs /\ In m xs.
  Proof.
    intros; pose proof (maximum_case (hd 0 xs) xs).
    repeat intuition auto.
    destruct xs as [| x xs]; cbn in *; [easy |].
    prename (fun _ => _ < _) into Hfalse; inv Hfalse; lia.
  Qed.

  Lemma maximum_lower_bound min xs : min <= maximum min xs.
  Proof. unfold maximum; induction xs as [| x xs]; cbn; intros; lia. Qed.

  Lemma maximum_le_mono min min' xs : min <= min' -> maximum min xs <= maximum min' xs.
  Proof. unfold maximum; induction xs as [| x xs]; cbn; intros; lia. Qed.

  Lemma maximum_cons_le min xs x : maximum min xs <= maximum min (x :: xs).
  Proof. unfold maximum; intros; cbn; lia. Qed.

  Lemma maximum_in min xs (m := maximum min xs) : min < maximum min xs -> In m xs.
  Proof.
    induction xs as [| x xs]; cbn; intros; [lia |].
    fold (maximum min xs) in *.
    destruct (Z.lt_ge_cases x (maximum min xs));
      rewrite ?Z.max_l in * by lia; rewrite ?Z.max_r in * by lia; auto.
  Qed.

  Lemma maximum_weaken_in min min' xs :
    min <= min' -> In (maximum min' xs) xs -> maximum min xs = maximum min' xs.
  Proof.
    induction xs as [| x xs]; cbn; intros Hlt Hin; [easy |].
    pose proof (maximum_le_mono min min' xs); unfold maximum in *.
    destruct Hin as [Heq | Hin]; try lia.
    pattern (Z.max x (fold_right Z.max min' xs)); apply Z.max_case_strong; intros;
      try lia.
    rewrite Z.max_r in Hin by auto; apply IHxs in Hin; auto; lia.
  Qed.

  Corollary maximum_weaken_lt min min' xs :
    min <= min' < maximum min' xs -> maximum min xs = maximum min' xs.
  Proof. intros; apply maximum_weaken_in, maximum_in; lia. Qed.

  Lemma maximum0_unfold x xs : 0 <= x -> maximum0 (x :: xs) = Z.max x (maximum0 xs).
  Proof.
    intros; destruct xs as [| x' xs]; cbn; [lia |].
    fold (maximum x xs); fold (maximum x' xs).
    destruct (Z.lt_ge_cases x x').
    - destruct (maximum_case x' xs) as (? & [? | (? & Hmax)]).
      + rewrite (maximum_weaken_in x x' xs); auto; lia.
      + destruct (maximum_case x xs) as (? & [Hin | (? & ?)]); try lia.
        rewrite Forall_forall in Hmax; apply Hmax in Hin; lia.
    - destruct (maximum_case x xs) as (? & [? | (? & Hmax)]).
      + rewrite (maximum_weaken_in x' x xs); auto; lia.
      + destruct (maximum_case x' xs) as (? & [Hin | (? & ?)]); try lia.
        rewrite Forall_forall in Hmax; apply Hmax in Hin; lia.
  Qed.
End Maximum.

Section Minimum.
  Definition minimum max (xs : list Z) : Z :=
    fold_right Z.min max xs.

  Definition minimum0 (xs : list Z) : Z :=
    minimum (hd 0 xs) xs.

  Lemma minimum_case max xs (m := minimum max xs) :
    Forall (fun x => m <= x) xs /\
    (In m xs \/ (m = max /\ Forall (fun x => max < x) xs)).
  Proof.
    induction xs as [| x xs]; cbn in *; auto;
      destruct IHxs as (Hmin & Hin); fold (minimum max xs); split.
    - constructor; auto using Z.le_min_l.
      rewrite Forall_forall in *; intros * Hin'; apply Hmin in Hin'; lia.
    - pattern (Z.min x (minimum max xs)); apply Zmin_case_strong_lt; intros;
        intuition auto.
      right; split; auto; constructor; auto; lia.
  Qed.

  Lemma minimum0_case xs (m := minimum0 xs) :
    xs <> nil -> Forall (fun x => m <= x) xs /\ In m xs.
  Proof.
    intros; pose proof (minimum_case (hd 0 xs) xs).
    repeat intuition auto.
    destruct xs as [| x xs]; cbn in *; [easy |].
    prename (fun _ => _ < _) into Hfalse; inv Hfalse; lia.
  Qed.

  Lemma minimum_upper_bound max xs : minimum max xs <= max.
  Proof. unfold minimum; induction xs as [| x xs]; cbn; intros; lia. Qed.

  Lemma minimum_le_mono max max' xs : max <= max' -> minimum max xs <= minimum max' xs.
  Proof. unfold minimum; induction xs as [| x xs]; cbn; intros; lia. Qed.

  Lemma minimum_cons_le max xs x : minimum max (x :: xs) <= minimum max xs.
  Proof. unfold minimum; intros; cbn; lia. Qed.

  Lemma minimum_in max xs (m := minimum max xs) : minimum max xs < max -> In m xs.
  Proof.
    induction xs as [| x xs]; cbn; intros; [lia |].
    fold (minimum max xs) in *.
    destruct (Z.lt_ge_cases x (minimum max xs));
      rewrite ?Z.min_l in * by lia; rewrite ?Z.min_r in * by lia; auto.
  Qed.

  Lemma minimum_weaken_in max max' xs :
    max' <= max -> In (minimum max' xs) xs -> minimum max xs = minimum max' xs.
  Proof.
    induction xs as [| x xs]; cbn; intros Hlt Hin; [easy |].
    pose proof (minimum_le_mono max' max xs); unfold minimum in *.
    destruct Hin as [Heq | Hin]; try lia.
    pattern (Z.min x (fold_right Z.min max' xs)); apply Z.min_case_strong; intros;
      try lia.
    rewrite Z.min_r in Hin by auto; apply IHxs in Hin; auto; lia.
  Qed.

  Corollary minimum_weaken_lt max max' xs :
    minimum max' xs < max' <= max -> minimum max xs = minimum max' xs.
  Proof. intros; apply minimum_weaken_in, minimum_in; lia. Qed.
End Minimum.
