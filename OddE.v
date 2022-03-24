(*
 * All odd numbers have an 'e' in English.
 *)

From Coq Require Import
  Ascii
  Decimal
  String.
From FunProofs.Lib Require Import
  Util.

Open Scope string.

Fixpoint list_of_uint (n : uint) : list nat :=
  match n with
  | Nil => []
  | D0 n => 0 :: list_of_uint n
  | D1 n => 1 :: list_of_uint n
  | D2 n => 2 :: list_of_uint n
  | D3 n => 3 :: list_of_uint n
  | D4 n => 4 :: list_of_uint n
  | D5 n => 5 :: list_of_uint n
  | D6 n => 6 :: list_of_uint n
  | D7 n => 7 :: list_of_uint n
  | D8 n => 8 :: list_of_uint n
  | D9 n => 9 :: list_of_uint n
  end.

Definition nat_of_digits (ds : list nat) : nat := fold_left (fun x d => x * 10 + d) ds 0.

Definition english_0_19 (n : nat) : string :=
  match n with
  | 0 => "zero"
  | 1 => "one"
  | 2 => "two"
  | 3 => "three"
  | 4 => "four"
  | 5 => "five"
  | 6 => "six"
  | 7 => "seven"
  | 8 => "eight"
  | 9 => "nine"
  | 10 => "ten"
  | 11 => "eleven"
  | 12 => "twelve"
  | 13 => "thirteen"
  | 14 => "fourteen"
  | 15 => "fifteen"
  | 16 => "sixteen"
  | 17 => "seventeen"
  | 18 => "eighteen"
  | 19 => "nineteen"
  | _ => ""
  end.

Definition english_10s (n : nat) : string :=
  match n with
  | 2 => "twenty"
  | 3 => "thirty"
  | 4 => "forty"
  | 5 => "fifty"
  | 6 => "sixty"
  | 7 => "seventy"
  | 8 => "eighty"
  | 9 => "ninety"
  | _ => ""
  end.

Definition english_20_99 (n : nat) : string :=
  let tens := english_10s (n / 10) in
  let rest := english_0_19 (n mod 10) in
  if (n mod 10 =? 0)%nat then tens else tens ++ " " ++ rest.

Definition english_0_99 (n : nat) : string :=
  if (n <? 20)%nat then english_0_19 n else english_20_99 n.

Definition english_0_999 (n : nat) : string :=
  let pre := english_0_19 (n / 100) ++ " hundred" in
  let rest := english_0_99 (n mod 100) in
  if (n <? 100)%nat then rest
  else if (n mod 100 =? 0)%nat then pre
  else pre ++ " " ++ rest.

Definition _tens := ["thousand"; "million"].
Definition tens n := (firstn n _tens ++ repeat "unknownion" (n - length _tens))%list.

Definition ten_name (n : nat) (ten : string) : string :=
  if (n =? 0)%nat then "" else (english_0_999 n ++ " " ++ ten).

Definition english (n : nat) : string :=
  (* 1s, 10s, 100s *)
  let rest := english_0_999 (n mod 1000) in
  (* To decimal *)
  let n' := Nat.to_little_uint n Decimal.zero in
  (* Drop everything < 1000 *)
  let digits := skipn 3 (list_of_uint n') in
  (* Group in chunks of 3 *)
  let digits' := map nat_of_digits (map (@rev _) (chunks 3 digits)) in
  (* Combine with thousands, millions, etc *)
  let pre := map (uncurry ten_name) (combine digits' (tens (length digits'))) in
  (* Filter empty and join *)
  let pre' := String.concat " " (filter (empty ∘ negb) (rev pre)) in
  (* Skip empty prefixes or postfixes *)
  if empty pre' then rest
  else if (n mod 1000 =? 0)%nat then pre'
  else pre' ++ " " ++ rest.

Goal english 0 = "zero". Proof. reflexivity. Qed.
Goal english 1 = "one". Proof. reflexivity. Qed.
Goal english 20 = "twenty". Proof. reflexivity. Qed.
Goal english 46 = "forty six". Proof. reflexivity. Qed.
Goal english 99 = "ninety nine". Proof. reflexivity. Qed.
Goal english 100 = "one hundred". Proof. reflexivity. Qed.
Goal english 118 = "one hundred eighteen". Proof. reflexivity. Qed.
Goal english 2000 = "two thousand". Proof. reflexivity. Qed.
Goal english 2467 = "two thousand four hundred sixty seven". Proof. reflexivity. Qed.
Goal english (Nat.of_num_uint 12012%uint) = "twelve thousand twelve".
Proof. reflexivity. Qed.
Goal english (Nat.of_num_uint 1234567%uint) =
     "one million two hundred thirty four thousand five hundred sixty seven".
Proof. vm_compute; reflexivity. Qed.

(* All odds in [0, 20) have 'e'. *)
Lemma odd_e_0_19 n : n < 20 -> Nat.odd n = true -> In "e"%char (chars (english_0_19 n)).
Proof.
  unfold english_0_19; intros Hlt Hodd.
  repeat (destruct n; [solve [easy | cbn; intuition auto] |]); lia.
Qed.

(* All odds in [20, 100) include an odd in [0, 20). *)
Lemma odd_incl_0_19_20_99 n :
  Nat.odd n = true ->
  exists m,
    m < 20 /\ Nat.odd m = true /\
    incl (chars (english_0_19 m)) (chars (english_20_99 n)).
Proof.
  unfold english_20_99; intros Hodd.
  assert (Hodd': Nat.odd (n mod 10) = true) by (rewrite odd_mod_even; auto).
  assert ((n mod 10 =? 0)%nat = false) as ->.
  { rewrite Nat.eqb_neq; intros Heq; rewrite Heq in Hodd'; inv Hodd'. }
  assert (n mod 10 < 20) by (etransitivity; [apply Nat.mod_upper_bound |]; lia).
  rewrite !chars_app; split_all; eauto using incl_appr, incl_refl.
Qed.

(* All odds in [0, 100) include an odd in [0, 20). *)
Lemma odd_incl_0_19_0_99 n :
  Nat.odd n = true ->
  exists m,
    m < 20 /\ Nat.odd m = true /\
    incl (chars (english_0_19 m)) (chars (english_0_99 n)).
Proof.
  unfold english_0_99; intros Hodd.
  destruct (_ <? _)%nat eqn:Hlt; [rewrite Nat.ltb_lt in Hlt |];
    eauto using incl_refl, odd_incl_0_19_20_99.
Qed.

(* All odds in [0, 1000) include an odd in [0, 20). *)
Lemma odd_incl_0_19_0_999 n :
  Nat.odd n = true ->
  exists m,
    m < 20 /\ Nat.odd m = true /\
    incl (chars (english_0_19 m)) (chars (english_0_999 n)).
Proof.
  unfold english_0_999; intros Hodd.
  assert (Hodd': Nat.odd (n mod 100) = true) by (rewrite odd_mod_even; auto).
  split_case; eauto using odd_incl_0_19_0_99.
  assert ((n mod 100 =? 0)%nat = false) as ->.
  { rewrite Nat.eqb_neq; intros Heq; rewrite Heq in Hodd'; inv Hodd'. }
  eapply odd_incl_0_19_0_99 in Hodd'; destr *.
  rewrite !chars_app; split_all; eauto using incl_appr.
Qed.

(* All odds include an odd in [0, 20). *)
Lemma odd_incl_0_19 n :
  Nat.odd n = true ->
  exists m,
    m < 20 /\ Nat.odd m = true /\
    incl (chars (english_0_19 m)) (chars (english n)).
Proof.
  unfold english; intros Hodd.
  assert (Hodd': Nat.odd (n mod 1000) = true) by (rewrite odd_mod_even; auto).
  split_case; auto using odd_incl_0_19_0_999.
  assert ((n mod 1000 =? 0)%nat = false) as ->.
  { rewrite Nat.eqb_neq; intros Heq; rewrite Heq in Hodd'; inv Hodd'. }
  eapply odd_incl_0_19_0_999 in Hodd'; destr *.
  rewrite !chars_app; split_all; eauto using incl_appr.
Qed.

(* All odds have an 'e'. *)
Theorem odd_e n : Nat.odd n = true -> In "e"%char (chars (english n)).
Proof. intros (m & ? & ? & He)%odd_incl_0_19; now apply He, odd_e_0_19. Qed.
