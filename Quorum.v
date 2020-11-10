(*
 * Quorum intersection.
 * Two quorums have a non-empty intersection.
 *)

From FunProofs.Lib Require Import
  Sets
  Util.
Import EqDecNotations.

Section Intersect.
  Variable A : Type.
  Context `{EqDec A}.

  Lemma disjoint_subset_card : forall (s ss1 ss2 : set A),
    subset ss1 s -> subset ss2 s ->
    ~(exists x, Sets.In x ss1 /\ Sets.In x ss2) ->
    card ss1 + card ss2 <= card s.
  Proof.
    induction s using set_ind; intros * Hsub1 Hsub2 Hdisj.
    { prename equiv into Heq; rewrite Heq in Hsub1, Hsub2.
      apply subset_empty in Hsub1; apply subset_empty in Hsub2.
      rewrite Hsub1, Hsub2, Heq; auto.
    }
    prename A into x; prename equiv into Heq; prename (Sets.In _ _) into Hin.
    apply member_in_true in Hin.
    rewrite (card_unroll ss1 x), (card_unroll ss2 x), (card_unroll s1 x), <- Heq, Hin.
    apply member_in_true in Hin.
    destruct (member _ ss1) eqn:Hin1, (member _ ss2) eqn:Hin2;
      rewrite ?member_in_true, ?member_in_false in Hin1;
      rewrite ?member_in_true, ?member_in_false in Hin2; cbn.
    - exfalso; eauto.
    - apply le_n_S, IHs1; rewrite ?Heq; auto using subset_remove_remove.
      intros ?; destr *; eapply Hdisj; eauto using remove_in.
    - rewrite Nat.add_comm; apply le_n_S, IHs1; rewrite ?Heq; auto using subset_remove_remove.
      intros ?; destr *; eapply Hdisj; eauto using remove_in.
    - etransitivity; [eapply IHs1 |]; rewrite ?Heq; auto using subset_remove_remove.
      intros ?; destr *; eapply Hdisj; eauto using remove_in.
  Qed.

  Lemma quorum_intersect : forall (s ss1 ss2 : set A),
    subset ss1 s -> subset ss2 s ->
    card s < card ss1 + card ss2 ->
    exists x, Sets.In x ss1 /\ Sets.In x ss2.
  Proof.
    intros * Hsub1 Hsub2 Hcard.
    enough (Hdisj: ~~(exists x, Sets.In x ss1 /\ Sets.In x ss2)).
    - rewrite <- disjoint_false_correct in Hdisj |- *.
      destruct (disjoint _ _); auto.
      now exfalso; apply Hdisj.
    - intros Hdisj; apply (disjoint_subset_card s) in Hdisj; auto.
      lia.
  Qed.

  Corollary majority_intersect : forall (s ss1 ss2 : set A),
    subset ss1 s -> subset ss2 s ->
    card s < card ss1 * 2 -> card s < card ss2 * 2 ->
    exists x, Sets.In x ss1 /\ Sets.In x ss2.
  Proof.
    intros; eapply quorum_intersect with (s := s); eauto; lia.
  Qed.
End Intersect.
