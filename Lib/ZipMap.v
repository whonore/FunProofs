From Coq Require Import
  List.
From FunProofs.Lib Require Import
  List.

Section ZipMap.
  Context {A B C : Type}.

  Definition zipMap (f : A -> B -> C) xs ys : list C :=
    map (fun xy => f (fst xy) (snd xy)) (combine xs ys).

  Lemma zipMap_split {D E} (f : D -> A) (g : E -> B) (h : A -> B -> C) xs : forall ys,
    map (fun xy => h (f (fst xy)) (g (snd xy))) (combine xs ys) =
    zipMap h (map f xs) (map g ys).
  Proof.
    unfold zipMap; induction xs; cbn; intros; auto.
    destruct ys; cbn; auto.
    rewrite IHxs; auto.
  Qed.

  Lemma zipMap_repeat_r (f : A -> B -> C) y xs : forall n,
    n = length xs -> zipMap f xs (repeat y n) = map (fun x => f x y) xs.
  Proof.
    unfold zipMap; induction xs; cbn; intros; subst; auto.
    erewrite <- IHxs; eauto; auto.
  Qed.

  Lemma zipMap_app (f : A -> B -> C) xs xs' ys ys' :
    length xs = length ys ->
    length xs' = length ys' ->
    zipMap f (xs ++ xs') (ys ++ ys') = zipMap f xs ys ++ zipMap f xs' ys'.
  Proof. unfold zipMap; intros; rewrite combine_app, map_app; auto. Qed.

  Lemma zipMap_rev (f : A -> B -> C) xs ys :
    length xs = length ys -> rev (zipMap f xs ys) = zipMap f (rev xs) (rev ys).
  Proof. unfold zipMap; intros; rewrite <- map_rev, combine_rev; auto. Qed.
End ZipMap.
