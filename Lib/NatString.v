From Coq Require Import
  Ascii
  Decimal
  Lia
  List
  String.
From FunProofs.Lib Require Import
  Tactics.
Import ListNotations.

Open Scope string.

Fixpoint tostr' (n : uint) : string :=
  match n with
  | Nil => EmptyString
  | D0 n' => String "0" (tostr' n')
  | D1 n' => String "1" (tostr' n')
  | D2 n' => String "2" (tostr' n')
  | D3 n' => String "3" (tostr' n')
  | D4 n' => String "4" (tostr' n')
  | D5 n' => String "5" (tostr' n')
  | D6 n' => String "6" (tostr' n')
  | D7 n' => String "7" (tostr' n')
  | D8 n' => String "8" (tostr' n')
  | D9 n' => String "9" (tostr' n')
  end%char.
Definition tostr (n : nat) : string := tostr' (Nat.to_uint n).

Definition digits := ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"]%char.

Lemma to_little_uint_not_nil n : forall acc,
  acc <> Nil -> Nat.to_little_uint n acc <> Nil.
Proof.
  induction n; cbn; intros; auto.
  apply IHn; now destruct acc.
Qed.

Lemma revapp_not_nil n : forall m, n <> Nil \/ m <> Nil -> revapp n m <> Nil.
Proof. induction n; cbn; intros; try apply IHn; intuition easy. Qed.

Corollary to_uint_not_nil n : Nat.to_uint n <> Nil.
Proof. now apply revapp_not_nil; left; apply to_little_uint_not_nil. Qed.

Lemma tostr'_length_pos n : n <> Nil -> 0 < String.length (tostr' n).
Proof. induction n; cbn; intros; solve [easy | lia]. Qed.

Corollary tostr_length_pos n : 0 < String.length (tostr n).
Proof. apply tostr'_length_pos, to_uint_not_nil. Qed.

#[local] Definition digits' := Eval cbn in map Some digits.

Lemma tostr'_all_digits n (s := tostr' n) : forall m,
  m < String.length s -> In (get m s) digits'.
Proof.
  subst s; induction n; cbn; intros;
    solve [easy | destruct m; [intuition auto | apply IHn; lia]].
Qed.

Corollary tostr_all_digits n (s := tostr n) : forall m,
  m < String.length s -> In (get m s) digits'.
Proof. apply tostr'_all_digits. Qed.

Corollary tostr_hd_digits n (s := tostr n) : In (get 0 s) digits'.
Proof. apply tostr_all_digits, tostr_length_pos. Qed.
