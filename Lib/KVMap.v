From Coq Require Import
  Arith
  List.
From FunProofs.Lib Require Import
  EqDec
  Tactics.
Import EqDecNotations.
Import ListNotations.

Section KVMap.
  Context {key value : Type} `{EqDec key}.

  Definition kvmap := key -> value.

  Definition kvinit (d : value) : kvmap := fun _ => d.
  Definition kvget (k : key) (m : kvmap) : value := m k.
  Definition kvset (kv : key * value) (m : kvmap) : kvmap :=
    fun k' => if fst kv == k' then snd kv else kvget k' m.
  Definition kvsets (kvs : list (key * value)) (m : kvmap) : kvmap :=
    fold_right kvset m kvs.
  Definition kvbuild (d : value) (kvs : list (key * value)) : kvmap :=
    kvsets kvs (kvinit d).
End KVMap.

#[global] Arguments kvmap _ _ : clear implicits.

Declare Scope kvmap.
Delimit Scope kvmap with kvmap.
Notation "k |-> v" := (k, v) (at level 10) : kvmap.
Notation "m @ k" := (kvget k m) (at level 20) : kvmap.
Notation "m ! k" := (kvset k m) (at level 20) : kvmap.
Notation "{ kv1 , .. , kvn } [ d ]" :=
  (kvbuild d (cons kv1%kvmap .. ([kvn%kvmap]) ..)) : kvmap.

Section KVMap.
  Open Scope kvmap.
  Context {key value : Type} `{EqDec key}.

  Lemma kvget_init (k : key) (d : value) : kvinit d @ k = d.
  Proof. auto. Qed.

  Lemma kvget_set_same k v (m : kvmap key value) : m ! (k |-> v) @ k = v.
  Proof. unfold kvget, kvset; intros; cbn; rewrite eq_dec_true; auto. Qed.

  Lemma kvget_set_other k v' v (m : kvmap key value) :
    k <> v' -> m ! (k |-> v) @ v' = m @ v'.
  Proof. unfold kvget, kvset; intros; cbn; rewrite eq_dec_false; auto. Qed.

  Lemma kvsets_correct kvs : forall (m : kvmap key value) k v,
    NoDup (map fst kvs) -> In (k |-> v) kvs -> kvsets kvs m @ k = v.
  Proof.
    induction kvs as [| kv' kvs]; cbn -[kvget]; intros * Huniq Hin;
      inv Huniq; intuition (subst; auto using kvget_set_same).
    destruct kv'; fold (kvsets kvs m); rewrite kvget_set_other; auto.
    intros ->; prename (_ -> False) into Hnin; apply Hnin.
    cbn; rewrite in_map_iff; repeat esplit; eauto; auto.
  Qed.
End KVMap.

Section Array.
  Context {value : Type} {sz : nat}.

  Definition array (sz : nat) := kvmap nat (option value).

  Definition arrayinit : array sz := kvinit None.
  Definition arrayget (k : nat) (a : array sz) : option value :=
    if k <? sz then kvget k a else None.
  Definition arrayset (kv : nat * value) (a : array sz) : option (array sz) :=
    if fst kv <? sz then Some (kvset (fst kv, Some (snd kv)) a) else None.
  Definition arraysets (kvs : list (nat * value)) (a : array sz) : option (array sz) :=
    fold_right
      (fun kv a => match a with Some a => arrayset kv a | None => None end)
      (Some a)
      kvs.
  Definition arraybuild (kvs : list (nat * value)) : option (array sz) :=
    arraysets kvs arrayinit.
End Array.

#[global] Arguments array _ : clear implicits.

Declare Scope array.
Delimit Scope array with array.
Notation "k |-> v" := (k, v) (at level 10) : array.
Notation "m @ k" := (arrayget k m) (at level 20) : array.
Notation "m ! k" := (arrayset k m) (at level 20) : array.
Notation "{ kv1 , .. , kvn } [ d ]" :=
  (arraybuild d (cons kv1%array .. ([kvn%array]) ..)) : array.

Section Array.
  Open Scope array.
  Context {value : Type} {sz : nat}.

  Lemma arrayget_init k : (@arrayinit value sz) @ k = None.
  Proof. unfold arrayget; intros; now destruct (_ <? _). Qed.

  Lemma arrayget_set_same k v (a a' : array value sz) :
    a ! (k |-> v) = Some a' -> a' @ k = Some v.
  Proof.
    unfold arrayget, arrayset; cbn [fst]; intros Hset.
    cases Hset; simplify; now rewrite kvget_set_same.
  Qed.

  Lemma arrayget_set_other k v' v (a a' : array value sz) :
    k <> v' -> a ! (k |-> v) = Some a' -> a' @ v' = a @ v'.
  Proof.
    unfold arrayget, arrayset; cbn [fst]; intros ? Hset.
    cases Hset; simplify; now rewrite kvget_set_other.
  Qed.

  Lemma arrayget_oob (a : array value sz) (idx : nat) : sz <= idx -> a @ idx = None.
  Proof.
    unfold arrayget; intros Hoob.
    apply Nat.leb_le in Hoob.
    rewrite Nat.ltb_antisym, Hoob; auto.
  Qed.

  Lemma arrayget_in (a : array value sz) (idx : nat) v : a @ idx = Some v -> idx < sz.
  Proof.
    unfold arrayget; intros Hget.
    cases Hget; apply Nat.leb_le; auto.
  Qed.

  Lemma arrayset_oob (a : array value sz) (idx : nat) v :
    sz <= idx <-> a ! (idx |-> v) = None.
  Proof.
    unfold arrayset; split; cbn [fst]; [intros Hoob | intros Hset].
    - apply Nat.leb_le in Hoob.
      rewrite Nat.ltb_antisym, Hoob; auto.
    - apply Nat.leb_le; rewrite Nat.leb_antisym.
      cases Hset; auto.
  Qed.

  Corollary arrayset_in (a a' : array value sz) (idx : nat) v :
    a ! (idx |-> v) = Some a' -> idx < sz.
  Proof. intros Hset; now rewrite Nat.lt_nge, arrayset_oob, Hset. Qed.
End Array.
