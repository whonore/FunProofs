(*
 * FizzBuzz.
 *)

From Coq Require Import
  Ascii
  String.
From FunProofs.Lib Require Import
  NatString
  Util.

Open Scope string.

Definition fizz_buzz (n : nat) : string :=
  match n mod 3, n mod 5 with
  | O, O => "FizzBuzz"
  | O, _ => "Fizz"
  | _, O => "Buzz"
  | _, _ => tostr n
  end.

Compute map fizz_buzz (seq 1 100).

Ltac hd_not_digit n :=
  rewrite <- get_correct; intros Hfalse;
  generalize (tostr_hd_digits n); cbn;
  rewrite Hfalse; cbn; intuition easy.

Ltac tostr_not :=
  match goal with
  | H: tostr ?n = _ |- _ => contradict H; clear; hd_not_digit n
  end.

Lemma fizz_buzz_correct n :
  (n mod 15 = 0 <-> fizz_buzz n = "FizzBuzz") /\
  ((n mod 5 = 0 /\ n mod 15 <> 0) <-> fizz_buzz n = "Buzz") /\
  ((n mod 3 = 0 /\ n mod 15 <> 0) <-> fizz_buzz n = "Fizz").
Proof.
  assert (n mod 15 = 0 <-> n mod 3 = 0 /\ n mod 5 = 0) as ->.
  { intros; now rewrite !Nat.mod_divide, (Nat.lcm_divide_iff 3 5) by auto. }
  unfold fizz_buzz; repeat apply conj; repeat split_case; intros;
    solve [easy | lia | tostr_not].
Qed.
