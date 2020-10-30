(*
 * Bounded Buffer Queue implementation using an "array" (finite map).
 *)

From Coq Require Import
  Arith
  Lia
  List.
From FunProofs.Lib Require Import
  KVMap
  Util.
Import EqDecNotations.

Open Scope array.

Section BBQ.
  Record bbq {A} {maxsize : nat} := mkBBQ {
    buf: array A maxsize;
    head: nat;
    size: nat;
  }.
  Global Arguments bbq _ _ : clear implicits.

  Inductive BBQError := BBQFull | BBQEmpty | BBQOOB.

  Notation Res A := (A + BBQError)%type.
  Notation Ok := (@inl _ BBQError).
  Notation Err := (@inr _ BBQError).

  Definition bbq_init A sz : bbq A sz := mkBBQ A sz arrayinit 0 0.

  Definition bbq_empty {A sz} (q : bbq A sz) : bool := q.(size) ==? 0.
  Definition bbq_full {A sz} (q : bbq A sz) : bool := sz ==? q.(size).

  Definition bbq_enqueue {A sz} (q : bbq A sz) (v : A) : Res (bbq A sz) :=
    if bbq_full q then Err BBQFull
    else
      let idx := (q.(head) + q.(size)) mod sz in
      let buf' := q.(buf) ! (idx |-> v) in
      match buf' with
      | Some buf' =>
        Ok {|
          buf := buf';
          head := q.(head);
          size := q.(size) + 1;
        |}
      | None => Err BBQOOB (* Impossible *)
      end.

  Definition bbq_dequeue {A sz} (q : bbq A sz) : Res (bbq A sz * A) :=
    if bbq_empty q then Err BBQEmpty
    else
      let v := q.(buf) @ q.(head) in
      match v with
      | Some v =>
        Ok ({|
          buf := q.(buf);
          head := (q.(head) + 1) mod sz;
          size := q.(size) - 1;
        |}, v)
      | None => Err BBQOOB (* Impossible *)
      end.

  Record bbq_bounds {A sz} (q : bbq A sz) : Prop := {
    bbq_size_bounds : q.(size) <= sz;
    bbq_head_bounds : q.(head) < sz;
  }.

  Lemma bbq_init_bounds {A sz} : 0 < sz -> bbq_bounds (bbq_init A sz).
  Proof. constructor; cbn; lia. Qed.

  Lemma bbq_enqueue_bounds {A sz} : forall (q q' : bbq A sz) v,
    0 < sz -> bbq_bounds q ->
    bbq_enqueue q v = Ok q' ->
    bbq_bounds q'.
  Proof.
    unfold bbq_enqueue, bbq_full, eqb; intros * Hsz Hbounds Hq.
    cases *; inv Hbounds; simplify.
    constructor; cbn; lia.
  Qed.

  Lemma bbq_dequeue_bounds {A sz} : forall (q q' : bbq A sz) v,
    0 < sz -> bbq_bounds q ->
    bbq_dequeue q = Ok (q', v) ->
    bbq_bounds q'.
  Proof.
    unfold bbq_dequeue; intros * Hsz Hbounds Hq.
    cases Hq; inv Hbounds; simplify.
    pose proof (Nat.mod_upper_bound (q.(head) + 1) sz).
    constructor; cbn; lia.
  Qed.

  Record bbq_list_R {A sz} (q : bbq A sz) (lq : list A) : Prop := {
    bbq_list_bounds : bbq_bounds q;
    bbq_list_length : length lq = q.(size);
    bbq_list_nth : forall n, n < q.(size) ->
      q.(buf) @ ((q.(head) + n) mod sz) = nth_error lq n;
  }.

  Lemma bbq_list_refine_init {A sz} : 0 < sz -> bbq_list_R (bbq_init A sz) nil.
  Proof.
    constructor; cbn; intros; auto using bbq_init_bounds.
    now rewrite arrayget_init, nth_error_nil.
  Qed.

  Lemma bbq_list_refine_enqueue {A sz} : forall (q : bbq A sz) lq v,
    0 < sz ->
    bbq_list_R q lq ->
    match bbq_enqueue q v with
    | inl q' => bbq_list_R q' (lq @@ v)
    | inr BBQFull => length lq = sz
    | _ => False
    end.
  Proof.
    intros * Hsz HR; inv HR.
    remember (bbq_enqueue q v) as res eqn:Hq.
    pose proof Hq; unfold bbq_enqueue, bbq_full, eqb in Hq.
    cases *; simplify; auto.
    - constructor; cbn; eauto using bbq_enqueue_bounds; [rewrite app_length; auto |].
      inv bbq_list_bounds0.
      intros n' Hlt.
      assert (n' < q.(size) \/ n' = q.(size)) as [|] by lia; subst.
      + specialize (bbq_list_nth0 n' ltac:(auto)).
        rewrite nth_error_app1, <- bbq_list_nth0 by lia.
        eapply arrayget_set_other; [intros Heq | eauto].
        assert (~((q.(head) + q.(size)) < sz)).
        { intros ?; rewrite !Nat.mod_small in Heq; lia. }
        rewrite Nat.mod_eq, div_range with (n := 1) in Heq by lia.
        assert (~(q.(head) + n') < sz).
        { intros ?; rewrite !Nat.mod_small in Heq; lia. }
        rewrite Nat.mod_eq, div_range with (n := 1) in Heq by lia.
        lia.
      + erewrite arrayget_set_same; eauto.
        rewrite <- bbq_list_length0, nth_error_app2, Nat.sub_diag; auto.
    - pose proof (Nat.mod_upper_bound (q.(head) + q.(size)) sz).
      apply arrayset_oob in Hq_case0; lia.
  Qed.

  Lemma bbq_list_refine_dequeue {A sz} : forall (q : bbq A sz) lq,
    0 < sz ->
    bbq_list_R q lq ->
    match bbq_dequeue q with
    | inl (q', v) =>
      match lq with
      | v' :: lq' => v = v' /\ bbq_list_R q' lq'
      | nil => False
      end
    | inr BBQEmpty => length lq = 0
    | _ => False
    end.
  Proof.
    intros * Hsz HR; inv HR.
    remember (bbq_dequeue q) as res eqn:Hq.
    pose proof Hq; unfold bbq_dequeue, bbq_empty, eqb in Hq.
    cases *; simplify; auto.
    - destruct lq; cbn in bbq_list_length0; [lia | split].
      + inv bbq_list_bounds0.
        specialize (bbq_list_nth0 0 ltac:(lia)).
        rewrite Nat.add_0_r, Nat.mod_small in bbq_list_nth0 by lia; simplify; auto.
      + constructor; cbn; eauto using bbq_dequeue_bounds; [lia |].
        inv bbq_list_bounds0.
        intros n' Hlt.
        specialize (bbq_list_nth0 (1 + n') ltac:(lia)).
        now rewrite Nat.add_assoc, Nat.add_mod, (Nat.mod_small n') in bbq_list_nth0 by lia.
    - inv bbq_list_bounds0.
      specialize (bbq_list_nth0 0 ltac:(lia)).
      rewrite Nat.add_0_r, Nat.mod_small in bbq_list_nth0 by lia.
      destruct lq; cbn in *; congruence.
  Qed.
End BBQ.
