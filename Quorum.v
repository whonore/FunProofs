(*
 * Quorum intersection.
 * Two quorums have a non-empty intersection.
 *)

From Coq Require Import
  Arith
  Lia
  List
  ListSet.
From FunProofs.Lib Require Import
  Util.
Import EqDecNotations.

Section Intersect.
  Variable A : Type.
  Context `{EqDec A}.

  Lemma set_remove_length_in : forall x s,
    NoDup s -> In x s ->
    length s = S (length (set_remove eq_dec x s)).
  Proof.
    induction s as [| y s]; cbn; intros * Hset Hin; intuition; simplify; auto.
    inv Hset; rewrite eq_dec_false, IHs; cbn; intuition (subst; auto).
  Qed.

  Lemma set_remove_length_not_in : forall x s,
    NoDup s -> ~In x s ->
    length s = length (set_remove eq_dec x s).
  Proof.
    induction s as [| y s]; cbn; intros * Hset Hin; intuition.
    inv Hset; destruct (x == y); subst; cbn; intuition.
  Qed.

  Lemma incl_nil : forall (s : list A),
    incl s nil -> s = nil.
  Proof.
    unfold incl; intros * Hsub; destruct s as [| x ss]; auto.
    now specialize (Hsub _ ltac:(cbn; auto)).
  Qed.

  Lemma incl_remove : forall s ss (x : A),
    NoDup s -> NoDup ss -> incl ss (x :: s) ->
    incl (set_remove eq_dec x ss) s.
  Proof.
    unfold incl; intros * Hset Hset1 Hsub * Hin.
    apply set_remove_2 in Hin as Hneq; auto.
    apply set_remove_1, Hsub in Hin; cbn in Hin.
    now intuition (subst; auto).
  Qed.

  Fixpoint disjoint (s1 s2 : list A) :=
    match s1 with
    | nil => true
    | x :: s1' =>
      if in_dec eq_dec x s2 then false else disjoint s1' s2
    end.

  Lemma disjoint_correct : forall s1 s2,
    disjoint s1 s2 = false <->
    (exists x, In x s1 /\ In x s2).
  Proof.
    induction s1 as [| x s1]; cbn; split; intros Hdisj; try easy.
    - now destruct Hdisj.
    - destruct (in_dec _ _ _); eauto.
      rewrite IHs1 in Hdisj; destruct Hdisj; intuition eauto.
    - destruct (in_dec _ _ _); eauto.
      rewrite IHs1; destruct Hdisj; now intuition (subst; eauto).
  Qed.

  Lemma length_unroll : forall s x,
    NoDup s ->
    length s = (if in_dec eq_dec x s then 1 else 0) + length (set_remove eq_dec x s).
  Proof.
    induction s as [| x s]; intros * Hset; inv Hset; auto.
    destruct (in_dec _ _ _); cbn in *; intuition (simplify; auto).
    - rewrite eq_dec_false; cbn; [| now intros ->].
      rewrite <- set_remove_length_in; auto.
    - cbn; rewrite <- set_remove_length_not_in; auto.
  Qed.

  Lemma disjoint_subset_length : forall (s ss1 ss2 : list A),
    NoDup s -> NoDup ss1 -> NoDup ss2 ->
    incl ss1 s -> incl ss2 s ->
    ~(exists x, In x ss1 /\ In x ss2) ->
    length ss1 + length ss2 <= length s.
  Proof.
    induction s as [| x s];
      intros * Hset Hset1 Hset2 Hsub1 Hsub2 Hdisj; cbn; auto; inv Hset.
    { apply incl_nil in Hsub1; apply incl_nil in Hsub2; subst; auto. }
    rewrite (length_unroll ss1 x), (length_unroll ss2 x); auto.
    repeat destruct (in_dec _ _ _); cbn.
    - exfalso; eauto.
    - apply le_n_S, IHs; auto using set_remove_nodup, incl_remove.
      intros (? & ? & ?).
      eapply Hdisj; eauto using set_remove_1.
    - rewrite Nat.add_comm; apply le_n_S, IHs; auto using set_remove_nodup, incl_remove.
      intros (? & ? & ?).
      eapply Hdisj; eauto using set_remove_1.
    - etransitivity; [eapply IHs |]; auto using set_remove_nodup, incl_remove.
      intros (? & ? & ?).
      eapply Hdisj; eauto using set_remove_1.
  Qed.

  Lemma quorum_intersect : forall (s ss1 ss2 : list A),
    NoDup s -> NoDup ss1 -> NoDup ss2 ->
    incl ss1 s -> incl ss2 s ->
    length s < length ss1 + length ss2 ->
    exists x, In x ss1 /\ In x ss2.
  Proof.
    intros * Hset Hset1 Hset2 Hsub1 Hsub2 Hcard.
    enough (Hdisj: ~~(exists x, In x ss1 /\ In x ss2)).
    - rewrite <- disjoint_correct in Hdisj |- *.
      destruct (disjoint _ _); auto.
      now exfalso; apply Hdisj.
    - intros Hdisj; apply (disjoint_subset_length s) in Hdisj; auto.
      lia.
  Qed.

  Corollary majority_intersect : forall (s ss1 ss2 : list A),
    NoDup s -> NoDup ss1 -> NoDup ss2 ->
    incl ss1 s -> incl ss2 s ->
    length s < length ss1 * 2 -> length s < length ss2 * 2 ->
    exists x, In x ss1 /\ In x ss2.
  Proof.
    intros; eapply quorum_intersect with (s := s); eauto; lia.
  Qed.
End Intersect.
