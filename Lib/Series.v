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

  Lemma maximum_case : forall min xs,
    let m := maximum min xs in
    Forall (fun x => x <= m) xs /\
    (In m xs \/ (m = min /\ Forall (fun x => x < min) xs)).
  Proof.
    induction xs as [| x xs]; cbn in *; auto;
      destruct IHxs as (Hmax & Hin); fold (maximum min xs); split.
    - constructor; auto using Z.le_max_l.
      rewrite Forall_forall in *; intros * Hin'; apply Hmax in Hin'; lia.
    - rewrite Z.max_comm; pattern (Z.max (maximum min xs) x);
        apply Zmax_case_strong_lt; intros; auto.
      intuition auto.
      right; split; auto; constructor; auto; lia.
  Qed.

  Lemma maximum0_case : forall xs,
    let m := maximum0 xs in
    xs <> nil ->
    Forall (fun x => x <= m) xs /\ In m xs.
  Proof.
    intros; pose proof (maximum_case (hd 0 xs) xs).
    repeat intuition auto.
    destruct xs as [| x xs]; cbn in *; [easy |].
    prename (fun _ => _ < _) into Hfalse; inv Hfalse; lia.
  Qed.

  Lemma maximum_lower_bound : forall min xs,
    min <= maximum min xs.
  Proof.
    unfold maximum; induction xs as [| x xs]; cbn; intros; lia.
  Qed.

  Lemma maximum_le_mono : forall min min' xs,
    min <= min' ->
    maximum min xs <= maximum min' xs.
  Proof.
    unfold maximum; induction xs as [| x xs]; cbn; intros; lia.
  Qed.

  Lemma maximum_cons_le : forall min xs x,
    maximum min xs <= maximum min (x :: xs).
  Proof. unfold maximum; intros; cbn; lia. Qed.

  Lemma maximum_in : forall min xs,
    let m := maximum min xs in
    min < maximum min xs ->
    In m xs.
  Proof.
    induction xs as [| x xs]; cbn; intros; [lia |].
    fold (maximum min xs) in *.
    assert (x < maximum min xs \/ maximum min xs <= x) as [|] by lia.
    - rewrite Z.max_r in * by lia; auto.
    - rewrite Z.max_l in * by lia; auto.
  Qed.

  Lemma maximum_weaken_in : forall min min' xs,
    min <= min' ->
    In (maximum min' xs) xs ->
    maximum min xs = maximum min' xs.
  Proof.
    induction xs as [| x xs]; cbn; intros * Hlt Hin; [easy |].
    pose proof (maximum_le_mono min min' xs); unfold maximum in *.
    destruct Hin as [Heq | Hin]; subst; try lia.
    pattern (Z.max x (fold_right Z.max min' xs)); apply Z.max_case_strong; intros; try lia.
    rewrite Z.max_r in Hin by auto; apply IHxs in Hin; auto; lia.
  Qed.

  Corollary maximum_weaken_lt : forall min min' xs,
    min <= min' < maximum min' xs ->
    maximum min xs = maximum min' xs.
  Proof. intros; apply maximum_weaken_in, maximum_in; lia. Qed.

  Lemma maximum0_unfold : forall x xs,
    0 <= x ->
    maximum0 (x :: xs) = Z.max x (maximum0 xs).
  Proof.
    intros; destruct xs as [| x' xs]; cbn; [lia |].
    fold (maximum x xs); fold (maximum x' xs).
    assert (x <= x' \/ x' < x) as [|] by lia.
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

Section Sum.
  Definition zsum' n ns := fold_left Z.add ns n.
  Notation zsum := (zsum' 0%Z).

  Definition nsum' n ns := fold_left Nat.add ns n.
  Notation nsum := (nsum' 0%nat).

  Definition zaltsum (ns : list Z) : Z :=
    zsum (altmap Z.opp ns).

  Ltac fold_sums :=
    repeat match goal with
           | H: context[fold_left Z.add ?ns ?n] |- _ => fold (zsum' n ns)
           | |- context[fold_left Z.add ?ns ?n] => fold (zsum' n ns)
           | H: context[fold_left Nat.add ?ns ?n] |- _ => fold (nsum' n ns)
           | |- context[fold_left Nat.add ?ns ?n] => fold (nsum' n ns)
           end.

  Lemma zsum_shift : forall ns n,
    zsum' n ns = n + zsum ns.
  Proof.
    induction ns as [| m ns]; intros; cbn in *; [lia |]; fold_sums.
    rewrite (IHns (_ + _)), (IHns m); lia.
  Qed.

  Lemma nsum_shift : forall ns n,
    nsum' n ns = (n + nsum ns)%nat.
  Proof.
    induction ns as [| m ns]; intros; cbn in *; [lia |]; fold_sums.
    rewrite (IHns (_ + _)%nat), (IHns m); lia.
  Qed.

  Ltac shift_sums :=
    repeat match goal with
           | H: context[zsum' ?n ?ns] |- _ =>
             lazymatch n with
             | 0%Z => fail
             | _ => rewrite (zsum_shift ns n) in H
             end
           | |- context[zsum' ?n ?ns] =>
             lazymatch n with
             | 0%Z => fail
             | _ => rewrite (zsum_shift ns n)
             end
           | H: context[nsum' ?n ?ns] |- _ =>
             lazymatch n with
             | 0%nat => fail
             | _ => rewrite (nsum_shift ns n) in H
             end
           | |- context[nsum' ?n ?ns] =>
             lazymatch n with
             | 0%nat => fail
             | _ => rewrite (nsum_shift ns n)
             end
           end.

  Ltac norm_sums := fold_sums; shift_sums.

  Lemma zsum_const {A} : forall (ns : list A) n m,
    zsum' n (map (const m) ns) = n + m * Z.of_nat (length ns).
  Proof.
    induction ns; intros; cbn in *; [lia |]; norm_sums.
    rewrite IHns; lia.
  Qed.

  Lemma zsum_repeat : forall p n m,
    zsum' n (repeat m p) = n + m * Z.of_nat p.
  Proof.
    induction p; intros; cbn in *; [lia |]; norm_sums.
    rewrite IHp; lia.
  Qed.

  Lemma zsum_add : forall (f g : Z -> Z) ns n,
    zsum' n (map (fun m => f m + g m) ns) = zsum' n (map f ns) + zsum (map g ns).
  Proof.
    induction ns; intros; cbn in *; [lia |]; norm_sums.
    rewrite IHns; lia.
  Qed.

  Lemma zsum_mul : forall (f : Z -> Z) ns n m,
    zsum' n (map (fun p => m * f p) ns) = n + m * zsum (map f ns).
  Proof.
    induction ns; intros; cbn in *; [lia |]; norm_sums.
    rewrite IHns; lia.
  Qed.

  Lemma zsum_succ : forall ns n,
    zsum' n (map Z.succ ns) = Z.of_nat (length ns) + zsum' n ns.
  Proof.
    intros; erewrite map_ext by (symmetry; apply Z.add_1_r).
    rewrite zsum_add.
    fold (@const _ Z 1); rewrite zsum_const, map_id; lia.
  Qed.

  Lemma zsum_mul_id : forall ns n m,
    zsum' n (map (Z.mul m) ns) = n + m * zsum ns.
  Proof. intros; rewrite zsum_mul, map_id; auto. Qed.

  Lemma zsum_mod : forall ns n m,
    m <> 0 ->
    (zsum' n ns) mod m = zsum' (n mod m) (map (fun x => x mod m) ns) mod m.
  Proof.
    induction ns; intros; cbn; fold_sums; [now rewrite Z.mod_mod |].
    rewrite IHns by auto; norm_sums.
    now rewrite !(Z.add_mod _ (zsum _)), <- (Z.add_mod n _), Z.mod_mod.
  Qed.

  Lemma zsum_rev : forall ns n,
    zsum' n (rev ns) = zsum' n ns.
  Proof.
    induction ns; intros; cbn; auto.
    rewrite fold_left_app; cbn; norm_sums.
    rewrite IHns; lia.
  Qed.

  Lemma zsum_app : forall ns ms n m p,
    n = m + p ->
    zsum' n (ns ++ ms) = zsum' m ns + zsum' p ms.
  Proof.
    unfold zsum'; intros; rewrite fold_left_app; norm_sums; lia.
  Qed.

  Lemma zsum_app0 : forall ns ms,
    zsum (ns ++ ms) = zsum ns + zsum ms.
  Proof. now intros; rewrite (zsum_app _ _ 0 0 0). Qed.

  Lemma zsum_nsum : forall ns n,
    0 <= n ->
    zsum' n (map Z.of_nat ns) = Z.of_nat (nsum' (Z.to_nat n) ns).
  Proof.
    induction ns; intros; cbn; fold_sums; [now rewrite Z2Nat.id |].
    now rewrite IHns, Z2Nat.inj_add, Nat2Z.id by lia.
  Qed.

  Open Scope nat.

  Lemma nsum_zsum : forall ns n,
    nsum' n ns = Z.to_nat (zsum' (Z.of_nat n) (map Z.of_nat ns)).
  Proof. now intros; rewrite zsum_nsum, !Nat2Z.id by lia. Qed.

  Lemma nsum_bound : forall ns n,
    nsum' n ns <= n + length ns * Z.to_nat (maximum0 (map Z.of_nat ns)).
  Proof.
    intros; induction ns; cbn -[maximum0] in *; [lia |]; norm_sums.
    rewrite maximum0_unfold by lia.
    match goal with
    | |- ?n + ?x + ?y <= ?n + (?z + ?w) => enough (x <= z /\ n + y <= n + w) by lia
    end.
    split; [lia | etransitivity; eauto].
    apply Nat.add_le_mono, Nat.mul_le_mono_nonneg_l; lia.
  Qed.

  Lemma nsum_const {A} : forall (ns : list A) n m,
    nsum' n (map (const m) ns) = n + m * length ns.
  Proof.
    induction ns; intros; cbn in *; [lia |]; norm_sums.
    rewrite IHns; lia.
  Qed.

  Lemma nsum_repeat : forall p n m,
    nsum' n (repeat m p) = n + m * p.
  Proof.
    induction p; intros; cbn in *; [lia |]; norm_sums.
    rewrite IHp; lia.
  Qed.

  Lemma nsum_add : forall (f g : nat -> nat) ns n,
    nsum' n (map (fun m => f m + g m) ns) = nsum' n (map f ns) + nsum (map g ns).
  Proof.
    induction ns; intros; cbn in *; [lia |]; norm_sums.
    rewrite IHns; lia.
  Qed.

  Lemma nsum_mul : forall (f : nat -> nat) ns n m,
    nsum' n (map (fun p => m * f p) ns) = n + m * nsum (map f ns).
  Proof.
    induction ns; intros; cbn in *; [lia |]; norm_sums.
    rewrite IHns; lia.
  Qed.

  Lemma nsum_succ : forall ns n,
    nsum' n (map S ns) = length ns + nsum' n ns.
  Proof.
    intros; erewrite map_ext by (symmetry; apply Nat.add_1_r).
    rewrite nsum_add.
    fold (@const _ nat 1); rewrite nsum_const, map_id; lia.
  Qed.

  Lemma nsum_mul_id : forall ns n m,
    nsum' n (map (Nat.mul m) ns) = n + m * nsum ns.
  Proof. intros; rewrite nsum_mul, map_id; auto. Qed.

  Lemma nsum_mod : forall ns n m,
    m <> 0 ->
    (nsum' n ns) mod m = nsum' (n mod m) (map (fun x => x mod m) ns) mod m.
  Proof.
    induction ns; intros; cbn; fold_sums; [now rewrite Nat.mod_mod |].
    rewrite IHns by auto; norm_sums.
    now rewrite !(Nat.add_mod _ (nsum _)), <- (Nat.add_mod n _), Nat.mod_mod.
  Qed.

  Lemma nsum_rev : forall ns n,
    nsum' n (rev ns) = nsum' n ns.
  Proof.
    induction ns; intros; cbn; auto.
    rewrite fold_left_app; cbn; norm_sums.
    rewrite IHns; lia.
  Qed.

  Lemma nsum_app : forall ns ms n m p,
    n = m + p ->
    nsum' n (ns ++ ms) = nsum' m ns + nsum' p ms.
  Proof.
    unfold nsum'; intros; rewrite fold_left_app; norm_sums; lia.
  Qed.

  Lemma nsum_app0 : forall ns ms,
    nsum (ns ++ ms) = nsum ns + nsum ms.
  Proof. now intros; rewrite (nsum_app _ _ 0 0 0). Qed.
End Sum.

(* Re-export notations and Ltac *)
Notation zsum := (zsum' 0%Z).
Notation nsum := (nsum' 0%nat).

Ltac fold_sums :=
  repeat match goal with
         | H: context[fold_left Z.add ?ns ?n] |- _ => fold (zsum' n ns)
         | |- context[fold_left Z.add ?ns ?n] => fold (zsum' n ns)
         | H: context[fold_left Nat.add ?ns ?n] |- _ => fold (nsum' n ns)
         | |- context[fold_left Nat.add ?ns ?n] => fold (nsum' n ns)
         end.
Ltac shift_sums :=
  repeat match goal with
         | H: context[zsum' ?n ?ns] |- _ =>
           lazymatch n with
           | 0%Z => fail
           | _ => rewrite (zsum_shift ns n) in H
           end
         | |- context[zsum' ?n ?ns] =>
           lazymatch n with
           | 0%Z => fail
           | _ => rewrite (zsum_shift ns n)
           end
         | H: context[nsum' ?n ?ns] |- _ =>
           lazymatch n with
           | 0%nat => fail
           | _ => rewrite (nsum_shift ns n) in H
           end
         | |- context[nsum' ?n ?ns] =>
           lazymatch n with
           | 0%nat => fail
           | _ => rewrite (nsum_shift ns n)
           end
         end.
Ltac norm_sums := fold_sums; shift_sums.

Section Geom.
  Definition geom r n := map (fun x => Z.pow r (Z.of_nat x)) (seq 0 n).
  Definition tens := geom 10.

  Lemma geom_length : forall r n,
    length (geom r n) = n.
  Proof. unfold geom; intros; rewrite map_length, seq_length; auto. Qed.

  Lemma geom_mod : forall r r' n b,
    b <> 0 ->
    r mod b = r' mod b ->
    map (fun x => x mod b) (geom r n) = map (fun x => x mod b) (geom r' n).
  Proof.
    unfold geom; intros.
    erewrite !map_map, map_ext; eauto.
    intros; apply pow_mod; lia.
  Qed.

  Lemma geom_one : forall n,
    geom 1 n = repeat 1 n.
  Proof.
    unfold geom; induction n; cbn; auto.
    rewrite <- seq_shift, map_map, <- IHn.
    erewrite map_ext; auto.
    intros; rewrite !Z.pow_1_l; lia.
  Qed.

  Lemma geom_none : forall n,
    geom (-1) n = altmap Z.opp (repeat 1 n).
  Proof.
    unfold geom; induction n; cbn; auto.
    rewrite <- seq_shift, map_map.
    erewrite map_ext with (g := fun x => _).
    2: intros; rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    2: rewrite Z.mul_comm, <- Z.opp_eq_mul_m1; eauto.
    rewrite <- map_map, IHn.
    clear IHn; induction n; cbn; auto.
    rewrite <- IHn; cbn; auto.
    rewrite map_map.
    erewrite map_ext with (g := fun x => x), map_id; auto using Z.opp_involutive.
  Qed.

  Lemma geom_zero' : forall n,
    tl (geom 0 n) = repeat 0 (n - 1).
  Proof.
    unfold geom; induction n; cbn; auto.
    destruct n; auto; cbn -[Z.of_nat].
    replace (S n - 1)%nat with n in IHn by lia.
    rewrite <- seq_shift, map_map, <- IHn; cbn -[Z.of_nat].
    f_equal; apply map_ext_in; intros * Hin.
    apply in_seq in Hin; rewrite !Z.pow_0_l; lia.
  Qed.

  Corollary geom_zero : forall n,
    (0 < n)%nat ->
    geom 0 n = 1 :: repeat 0 (n - 1).
  Proof. intros; rewrite <- geom_zero'; now destruct n. Qed.
End Geom.
