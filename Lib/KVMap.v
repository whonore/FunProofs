From Coq Require Import
  List.
From FunProofs.Lib Require Import
  EqDec
  Tactics.
Import EqDecNotations.

Section KVMap.
  Context {key value : Type} `{EqDec key}.

  Definition kvmap := key -> value.

  Definition initmap (d : value) : kvmap := fun _ => d.
  Definition getvar (k : key) (m : kvmap) : value := m k.
  Definition setvar (kv : key * value) (m : kvmap) : kvmap :=
    fun k' => if fst kv == k' then snd kv else getvar k' m.
  Definition setvars (kvs : list (key * value)) (m : kvmap) : kvmap :=
    fold_right setvar m kvs.
  Definition buildmap (d : value) (kvs : list (key * value)) : kvmap :=
    setvars kvs (initmap d).
End KVMap.

Arguments kvmap _ _ : clear implicits.

Declare Scope kvmap.
Delimit Scope kvmap with kvmap.
Notation "k |-> v" := (k, v) (at level 10) : kvmap.
Notation "m @ k" := (getvar k m) (at level 20) : kvmap.
Notation "m ! k" := (setvar k m) (at level 20) : kvmap.
Notation "{ kv1 , .. , kvn } [ d ]" :=
  (buildmap d (cons kv1%kvmap .. (cons kvn%kvmap nil) ..)) : kvmap.

Section KVMap.
  Open Scope kvmap.
  Context {key value : Type} `{EqDec key}.

  Lemma get_set_same : forall k v (m : kvmap key value),
    m ! (k, v) @ k = v.
  Proof.
    unfold getvar, setvar; intros; cbn; rewrite eq_dec_true; auto.
  Qed.

  Lemma get_set_other : forall k v' v (m : kvmap key value),
    k <> v' -> m ! (k, v) @ v' = m @ v'.
  Proof.
    unfold getvar, setvar; intros; cbn; rewrite eq_dec_false; auto.
  Qed.

  Lemma setvars_correct : forall kvs (m : kvmap key value) k v,
    NoDup (map fst kvs) -> In (k, v) kvs ->
    setvars kvs m @ k = v.
  Proof.
    induction kvs as [| kv' kvs]; cbn -[getvar]; intros * Huniq Hin;
      inv Huniq; intuition (subst; auto using get_set_same).
    destruct kv'; fold (setvars kvs m); rewrite get_set_other; auto.
    intros ->; prename (_ -> False) into Hnin; apply Hnin.
    cbn; rewrite in_map_iff; repeat esplit; eauto; auto.
  Qed.
End KVMap.
