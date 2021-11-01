From Coq Require Import
  Lia
  List
  ListSet
  Morphisms
  RelationClasses.
From FunProofs.Lib Require Import
  EqDec
  Logic
  Tactics.
Import EqDecNotations.

Section Sets.
  Context {A : Type}.
  Context `{EqDec A}.

  Definition set := {s : list A & NoDup s}.

  Definition empty : set := existT _ nil (NoDup_nil _).

  Definition add (x : A) (s : set) : set :=
    existT _
      (set_add eq_dec x (projT1 s))
      (set_add_nodup _ x (projT2 s)).

  Definition remove (x : A) (s : set) : set :=
    existT _
      (set_remove eq_dec x (projT1 s))
      (set_remove_nodup _ x (projT2 s)).

  Definition union (s u : set) : set :=
    existT _
      (set_union eq_dec (projT1 s) (projT1 u))
      (set_union_nodup _ (projT2 s) (projT2 u)).

  Definition intersect (s u : set) : set :=
    existT _
      (set_inter eq_dec (projT1 s) (projT1 u))
      (set_inter_nodup _ (projT2 s) (projT2 u)).

  Definition subtract (s u : set) : set :=
    existT _
      (set_diff eq_dec (projT1 s) (projT1 u))
      (set_diff_nodup _ (projT2 s) (projT2 u)).

  Definition card (s : set) : nat := length (projT1 s).

  Definition In (x : A) (s : set) : Prop := In x (projT1 s).
  Definition member (x : A) (s : set) : bool := set_mem eq_dec x (projT1 s).

  Definition subset (s u : set) : Prop := incl (projT1 s) (projT1 u).

  #[global] Instance subset_refl : Reflexive subset.
  Proof. red; intros; apply incl_refl. Qed.

  #[global] Instance subset_trans : Transitive subset.
  Proof. red; intros; eapply incl_tran; eauto. Qed.

  Instance subset_preorder : PreOrder subset.
  Proof. constructor; typeclasses eauto. Qed.

  Definition equiv (s u : set) : Prop := subset s u /\ subset u s.
  #[global] Instance equiv_refl : Reflexive equiv.
  Proof. split; reflexivity. Qed.

  #[global] Instance equiv_sym : Symmetric equiv.
  Proof. unfold equiv; split; intuition auto. Qed.

  #[global] Instance equiv_trans : Transitive equiv.
  Proof. unfold equiv; split; etransitivity; intuition eauto. Qed.

  #[global] Instance equiv_preorder : PreOrder equiv.
  Proof. constructor; typeclasses eauto. Qed.

  #[global] Instance equiv_equivalence : Equivalence equiv.
  Proof. constructor; typeclasses eauto. Qed.

  Fixpoint _disjoint (s u : list A) : bool :=
    match s with
    | nil => true
    | x :: s1' =>
      if in_dec eq_dec x u then false else _disjoint s1' u
    end.
  Definition disjoint (s u : set) : bool := _disjoint (projT1 s) (projT1 u).

  Ltac setind s :=
    let Hs := fresh "H" s in
    try intros until s; destruct s as (s & Hs);
    induction s as [| el s]; cbn [projT1 projT2]; [|
      match type of Hs with
      | NoDup (?x :: ?xs) =>
        let H := fresh Hs in
        let Hnin := fresh "Hnin" in
        assert (~List.In x xs /\ NoDup xs) as (Hnin & H) by (now inv Hs)
      end].

  Lemma member_in_true x s : member x s = true <-> In x s.
  Proof. split; [apply set_mem_correct1 | apply set_mem_correct2]. Qed.

  Corollary member_in_false x s : member x s = false <-> ~In x s.
  Proof. intros; apply iff_not_true, member_in_true. Qed.

  Lemma remove_in_card x s : In x s -> card s = S (card (remove x s)).
  Proof.
    setind s; cbn in *; intros Hin; intuition; simplify; auto.
    rewrite eq_dec_false by intuition (subst; auto); auto.
  Qed.

  Lemma remove_not_in_card x s : ~In x s -> card s = card (remove x s).
  Proof.
    setind s; cbn in *; intros Hin; intuition.
    destruct (_ == _); subst; cbn; intuition.
  Qed.

  Corollary card_unroll s x :
    card s = (if member x s then 1 else 0) + card (remove x s).
  Proof.
    destruct (member _ _) eqn:?.
    - now apply remove_in_card, member_in_true.
    - now apply remove_not_in_card, member_in_false.
  Qed.

  Lemma subset_card s u : subset s u -> card s <= card u.
  Proof. intros; destruct s; apply NoDup_incl_length; auto. Qed.

  Lemma equiv_card s u : equiv s u -> card s = card u.
  Proof. intros (?%subset_card & ?%subset_card); lia. Qed.

  Lemma subset_empty_l s : subset empty s.
  Proof. apply incl_nil_l. Qed.

  Lemma subset_empty s : subset s empty -> equiv s empty.
  Proof. intros Hsub; split; auto using subset_empty_l. Qed.

  Lemma equiv_empty_nil s : equiv s empty -> projT1 s = nil.
  Proof.
    destruct s as ([| ? ?] & ?); auto; cbn; intros (Hsub & _).
    now specialize (Hsub _ ltac:(cbn; auto)).
  Qed.

  Lemma subset_alt s u : subset s u <-> forall x, In x s -> In x u.
  Proof. intuition auto. Qed.

  Lemma remove_in s x y : In x (remove y s) -> In x s.
  Proof. destruct s; cbn; intros; eapply set_remove_1; eauto. Qed.

  Lemma remove_not_in s x y : In x (remove y s) -> x <> y.
  Proof. destruct s; cbn; intros; eapply set_remove_2; eauto. Qed.

  Lemma remove_subset s x : subset (remove x s) s.
  Proof.
    destruct s; rewrite subset_alt; intros * Hin.
    eapply set_remove_1; cbn in *; eauto.
  Qed.

  Lemma subset_remove_remove s ss x : subset ss s -> subset (remove x ss) (remove x s).
  Proof.
    rewrite !subset_alt; intros Hsub * Hin.
    apply remove_not_in in Hin as Hneq.
    apply set_remove_1 in Hin.
    apply Hsub in Hin.
    apply set_remove_3; auto.
  Qed.

  Lemma subset_remove s ss x : subset ss s -> subset (remove x ss) s.
  Proof. intros Hsub; transitivity ss; auto using remove_subset. Qed.

  Lemma _disjoint_false_correct s : forall u,
    _disjoint s u = false <-> (exists x, List.In x s /\ List.In x u).
  Proof.
    induction s as [| x s]; cbn; split; intros Hdisj; try easy.
    - now destruct Hdisj.
    - destruct (in_dec _ _ _); eauto.
      rewrite IHs in Hdisj; destruct Hdisj; intuition eauto.
    - destruct (in_dec _ _ _); eauto.
      rewrite IHs; destruct Hdisj; now intuition (subst; eauto).
  Qed.

  Corollary _disjoint_true_correct s u :
    _disjoint s u = true <-> (forall x, ~(List.In x s /\ List.In x u)).
  Proof. rewrite <- not_exist; apply iff_not_false, _disjoint_false_correct. Qed.

  Corollary disjoint_false_correct s u :
    disjoint s u = false <-> (exists x, In x s /\ In x u).
  Proof. apply _disjoint_false_correct. Qed.

  Corollary disjoint_true_correct s u :
    disjoint s u = true <-> (forall x, ~(In x s /\ In x u)).
  Proof. apply _disjoint_true_correct. Qed.

  Lemma set_ind (P : set -> Prop) :
    (forall s, equiv s empty -> P s) ->
    (forall x s u, In x s -> equiv u (remove x s) -> P u -> P s) ->
    forall s, P s.
  Proof.
    intros Hempty IH; setind s.
    - apply Hempty, subset_empty; hnf; auto.
    - eapply IH; cbn; eauto.
      instantiate (1 := ltac:(auto)).
      split; hnf; cbn; intros *; rewrite eq_dec_true by auto; auto.
  Qed.

  Global Instance subset_equiv_morph : Proper (equiv ==> equiv ==> iff) subset.
  Proof.
    unfold equiv; repeat (hnf; intros).
    intuition auto; repeat (etransitivity; eauto).
  Qed.

  Global Instance card_equiv_morph : Proper (equiv ==> eq) card.
  Proof. now repeat (hnf; intros); apply equiv_card. Qed.
End Sets.

#[global] Arguments set _ : clear implicits.
#[global] Opaque
  set
  empty
  add
  remove
  union
  intersect
  subtract
  card
  In
  member
  subset.
