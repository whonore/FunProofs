From Coq Require Import
  String.

Notation chars := list_ascii_of_string.

Definition empty (s : string) : bool :=
  match s with EmptyString => true | _ => false end.

Lemma chars_app s s' : chars (s ++ s') = (chars s ++ chars s')%list.
Proof. induction s; cbn; congruence. Qed.
