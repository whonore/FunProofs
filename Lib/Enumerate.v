From Coq Require Import
  Arith
  List.
From FunProofs.Lib Require Import
  List.

(* Enumerate all lists of length n using the elements of vals. *)
Fixpoint enumerate {A} (vals : list A) (n : nat) : list (list A) :=
  match n with
  | 0 => nil :: nil
  | S n' =>
    let fs := map cons vals in
    let vs := enumerate vals n' in
    flat_map (fun xs => map (fun f => f xs) fs) vs
  end.

Lemma enumerate_length : forall A n (vals : list A),
  length (enumerate vals n) = length vals ^ n.
Proof.
  induction n; cbn; intros; auto.
  rewrite flat_map_concat_map.
  rewrite concat_length with (n := length vals).
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
