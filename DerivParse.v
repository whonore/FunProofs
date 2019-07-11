(* Parsing regular expressions with derivatives.
   http://matt.might.net/papers/might2011derivatives.pdf
*)
Require Import Arith.
Require Import List.
Require Import RelationClasses.

Class Alphabet (A : Type) := {
  eq_A (c c' : A) : {c = c'} + {c <> c'};
}.

Lemma eq_A_refl {A} `{Alphabet} : forall c (T E : A),
  (if eq_A c c then T else E) = T.
Proof. intros; now destruct (eq_A _ _). Qed.

Section RegLang.
  Context `{Alphabet}.

  Inductive RLang :=
    | Empty : RLang
    | Null : RLang
    | Single : A -> RLang
    | Alt : RLang -> RLang -> RLang
    | Concat : RLang -> RLang -> RLang
    | Star : RLang -> RLang.

  (* Extensions *)
  Definition Plus (re : RLang) : RLang :=
    Concat re (Star re).

  Definition QMark (re : RLang) : RLang :=
    Alt re Null.

  Definition Class (cs : list A) : RLang :=
    fold_right (fun c => Alt (Single c)) Empty cs.

  Fixpoint nullable (re : RLang) : bool :=
    match re with
    | Empty => false
    | Null => true
    | Single _ => false
    | Alt re1 re2 => nullable re1 || nullable re2
    | Concat re1 re2 => nullable re1 && nullable re2
    | Star _ => true
    end.

  Fixpoint derivative (c : A) (re : RLang) : RLang :=
    match re with
    | Empty => Empty
    | Null => Empty
    | Single c' => if eq_A c c' then Null else Empty
    | Alt re1 re2 => Alt (derivative c re1) (derivative c re2)
    | Concat re1 re2 =>
        let con := Concat (derivative c re1) re2 in
        if nullable re1
          then Alt con (derivative c re2)
          else con
    | Star re => Concat (derivative c re) (Star re)
    end.

  Fixpoint matches (re : RLang) (cs : list A) : bool :=
    match cs with
    | nil => nullable re
    | c :: cs' => matches (derivative c re) cs'
    end.

End RegLang.

Notation "'∅'" := (Empty) : re_scope.
Notation "'ϵ'" := (Null) : re_scope.
Notation "` c `" := (Single c) (at level 10) : re_scope.
Notation "re1 | re2" := (Alt re1 re2) (at level 51, right associativity) : re_scope.
Notation "re1 ;; re2" := (Concat re1 re2) (at level 41, right associativity) : re_scope.
Notation "re *'" := (Star re) (at level 30) : re_scope.
Notation "re +'" := (Plus re) (at level 30) : re_scope.
Notation "re ?" := (QMark re) (at level 30) : re_scope.
Notation "'[r' c1 ; .. ; c2 ]" := (Class (cons c1 .. (cons c2 nil) ..)) : re_scope.
Delimit Scope re_scope with re.
Open Scope re_scope.

Section Facts.
  Context `{alph : Alphabet}.

  Definition re_equiv (re1 re2 : RLang) : Prop :=
    forall cs, matches re1 cs = matches re2 cs.
  Infix "==" := (re_equiv) (at level 70) : re_scope.

  Global Instance re_equiv_refl : Reflexive re_equiv.
  Proof. now red; unfold re_equiv. Qed.

  Global Instance re_equiv_sym : Symmetric re_equiv.
  Proof. now red; unfold re_equiv. Qed.

  Global Instance re_equiv_trans : Transitive re_equiv.
  Proof. red; unfold re_equiv; intros; etransitivity; auto. Qed.

  Global Instance re_equiv_equiv : Equivalence re_equiv.
  Proof. constructor; typeclasses eauto. Qed.

  (* Empty *)
  Lemma empty_no_match : forall cs,
    matches ∅ cs = false.
  Proof.
    induction cs; auto.
  Qed.

  (* Null *)
  Lemma null_one_match : forall cs,
    matches Null cs = true <-> cs = nil.
  Proof.
    split; intros * H; subst; auto.
    destruct cs; auto.
    cbn in H.
    now cbn in H; rewrite empty_no_match in H.
  Qed.

  (* Single *)
  Lemma single_one_match : forall cs c,
    matches (`c`) cs = true <-> cs = (c :: nil).
  Proof.
    split; intros * H; subst; cbn.
    - destruct cs as [| c' cs]; cbn in *; try easy.
      destruct (eq_A c' c).
      + now rewrite null_one_match in H; subst.
      + now rewrite empty_no_match in H.
    - now rewrite eq_A_refl.
  Qed.

  (* Alt *)
  Lemma alt_empty_l re :
    ∅ | re == re.
  Proof.
    red; intros; revert re.
    induction cs; intros; cbn; auto.
  Qed.

  Lemma alt_commute re1 re2 :
    re1 | re2 == re2 | re1.
  Proof.
    red; intros; revert re1 re2.
    induction cs; intros; cbn; auto with bool.
  Qed.

  Corollary alt_empty_r re :
    re | ∅ == re.
  Proof. rewrite alt_commute; apply alt_empty_l. Qed.

  Lemma alt_diag re :
    re | re == re.
  Proof.
    red; intros; revert re.
    induction cs; intros; cbn; auto using Bool.orb_diag.
  Qed.

  Lemma alt_match_true_or : forall cs re1 re2,
    matches (re1 | re2) cs = true <->
    matches re1 cs = true \/ matches re2 cs = true.
  Proof.
    induction cs; intros; cbn; auto using Bool.orb_true_iff.
  Qed.

  Lemma alt_match_false_and : forall cs re1 re2,
    matches (re1 | re2) cs = false <->
    matches re1 cs = false /\ matches re2 cs = false.
  Proof.
    induction cs; intros; cbn; auto using Bool.orb_false_iff.
  Qed.

  (* Concat *)
  Lemma concat_empty_l re :
    ∅;;re == ∅.
  Proof.
    red; intros; induction cs; auto.
  Qed.

  Lemma concat_empty_r re :
    re;;∅ == ∅.
  Proof.
    red; intros; revert re.
    induction cs; intros; cbn; destruct (nullable re); auto.
    rewrite alt_commute, alt_empty_l; auto.
  Qed.

  Lemma concat_match_true_split : forall cs re1 re2,
    matches (re1;;re2) cs = true <->
    exists cs1 cs2,
      cs = cs1 ++ cs2 /\
      matches re1 cs1 = true /\
      matches re2 cs2 = true.
  Proof.
    induction cs; cbn; split; intros H.
    - exists nil, nil; cbn; auto with bool.
    - destruct H as ([] & [] & ? & ? & ?); cbn in *; auto with bool; easy.
    - destruct (nullable re1) eqn:?.
      + rewrite alt_match_true_or, IHcs in H.
        destruct H as [(? & ? & ? & ? & ?) | H]; subst;
          eauto using app_nil_l, app_comm_cons.
      + rewrite IHcs in H.
        destruct H as (? & ? & ? & ? & ?); subst;
          eauto using app_nil_l, app_comm_cons.
    - destruct H as (cs1 & ? & ? & ? & ?).
      destruct (nullable re1) eqn:?.
      + rewrite alt_match_true_or, IHcs.
        destruct cs1; cbn in H; inversion H; subst; eauto.
        left; eauto using app_comm_cons.
      + rewrite IHcs.
        destruct cs1; cbn in H; inversion H; subst; eauto.
        cbn in *; congruence.
  Qed.

  Fact iff_not : forall b P,
    (b = true <-> P) -> (b = false <-> ~P).
  Proof.
    intuition (subst; auto; try easy).
    destruct b; cbn in *; intuition auto.
  Qed.

  Fact not_exist : forall A (P : A -> Prop),
    ~(exists x, P x) <-> (forall x, ~P x).
  Proof.
    intuition eauto.
    destruct H0; eauto.
  Qed.

  Corollary concat_match_false_split' : forall cs re1 re2,
    matches (re1;;re2) cs = false <->
    ~(exists cs1 cs2,
      cs = cs1 ++ cs2 /\
      matches re1 cs1 = true /\
      matches re2 cs2 = true).
  Proof.
    intros; apply iff_not, concat_match_true_split.
  Qed.

  Corollary concat_match_false_split : forall cs re1 re2,
    matches (re1;;re2) cs = false <->
    forall cs1 cs2,
      cs = cs1 ++ cs2 ->
      matches re1 cs1 = false \/
      matches re2 cs2 = false.
  Proof.
    intros.
    rewrite concat_match_false_split'.
    rewrite not_exist.
    setoid_rewrite not_exist.
    intuition auto; subst.
    - specialize (H cs1 cs2).
      destruct (matches _ _); auto.
      destruct (matches _ _); auto.
      exfalso; auto.
    - specialize (H _ _ eq_refl).
      intuition congruence.
  Qed.

  Lemma alt_concat_distr re1 re2 re3 :
    (re1 | re2);;re3 == re1;;re3 | re2;;re3.
  Proof.
    red; intros.
    destruct (matches (_ | _) _) eqn:Halt.
    - rewrite alt_match_true_or in Halt.
      rewrite !concat_match_true_split in *.
      destruct Halt as [(? & ? & ? & ? & ?) | (? & ? & ? & ? & ?)];
        subst; repeat (esplit; eauto).
      all: rewrite alt_match_true_or; auto.
    - rewrite alt_match_false_and in Halt.
      rewrite !concat_match_false_split in *.
      intros; subst.
      rewrite alt_match_false_and.
      destruct Halt as (Halt1 & Halt2).
      specialize (Halt1 _ _ eq_refl); specialize (Halt2 _ _ eq_refl).
      intuition auto.
  Qed.

  (* Star *)
  Lemma star_match_empty : forall re,
    matches (re*') nil = true.
  Proof. auto. Qed.

  Lemma star_match_unfold : forall cs re,
    matches (re*') cs = true <->
    cs = nil \/ matches (re;;re*') cs = true.
  Proof.
    induction cs; cbn; split; intros H; auto.
    - right; destruct (nullable re) eqn:?; auto.
      rewrite alt_diag; auto.
    - destruct H as [| H]; try easy.
      destruct (nullable re) eqn:?; auto.
      rewrite alt_diag in H; auto.
  Qed.

End Facts.

Section Tests.
  Import ListNotations.

  Instance nat_alph : Alphabet nat := { eq_A := Nat.eq_dec }.
  Let a := 0.
  Let b := 1.
  Let c := 2.

  Goal matches (`a`*') [] = true.
  Proof. reflexivity. Qed.
  Goal matches (`a`*') [a] = true.
  Proof. reflexivity. Qed.
  Goal matches (`a`*') [a; a] = true.
  Proof. reflexivity. Qed.
  Goal matches (`a`*') [a; a; b] = false.
  Proof. reflexivity. Qed.

  Goal matches ((`b`|`c`)+') [b] = true.
  Proof. reflexivity. Qed.
  Goal matches ((`b`|`c`)+') [c] = true.
  Proof. reflexivity. Qed.
  Goal matches ((`b`|`c`)+') [] = false.
  Proof. reflexivity. Qed.
  Goal matches ((`b`|`c`)+') [b; b; c; b] = true.
  Proof. reflexivity. Qed.

  Goal matches (`c`?;;`a`*';;(`b`|`c`)+') [a; b] = true.
  Proof. reflexivity. Qed.
  Goal matches (`c`?;;`a`*';;(`b`|`c`)+') [a; c] = true.
  Proof. reflexivity. Qed.
  Goal matches (`c`?;;`a`*';;(`b`|`c`)+') [b; c; b] = true.
  Proof. reflexivity. Qed.
  Goal matches (`c`?;;`a`*';;(`b`|`c`)+') [c; a; c] = true.
  Proof. reflexivity. Qed.
  Goal matches (`c`?;;`a`*';;(`b`|`c`)+') [c; a] = false.
  Proof. reflexivity. Qed.
  Goal matches (`c`?;;`a`*';;(`b`|`c`)+') [c; c] = true.
  Proof. reflexivity. Qed.

  Goal matches ([r a; b; c]?) [] = true.
  Proof. reflexivity. Qed.
  Goal matches ([r a; b; c]?) [a] = true.
  Proof. reflexivity. Qed.
  Goal matches ([r a; b; c]?) [b] = true.
  Proof. reflexivity. Qed.
  Goal matches ([r a; b; c]?) [c] = true.
  Proof. reflexivity. Qed.

End Tests.
