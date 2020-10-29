(*
 * Parsing regular expressions with derivatives.
 * http://matt.might.net/papers/might2011derivatives.pdf
 *)

From Coq Require Import
  Arith
  Bool
  List
  RelationClasses.
From FunProofs.Lib Require Import
  Util.
Import EqDecNotations.

Section RegLang.
  Context {A : Type}.
  Context `{EqDec A}.

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
    fold_right Alt Empty (map Single cs).

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
    | Single c' => if c == c' then Null else Empty
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

  Definition re_equiv (re1 re2 : RLang) : Prop :=
    forall cs, matches re1 cs = matches re2 cs.

  Global Instance re_equiv_refl : Reflexive re_equiv.
  Proof. now red; unfold re_equiv. Qed.

  Global Instance re_equiv_sym : Symmetric re_equiv.
  Proof. now red; unfold re_equiv. Qed.

  Global Instance re_equiv_trans : Transitive re_equiv.
  Proof. red; unfold re_equiv; intros; etransitivity; auto. Qed.

  Global Instance re_equiv_equiv : Equivalence re_equiv.
  Proof. constructor; typeclasses eauto. Qed.

End RegLang.

Declare Scope re_scope.
Delimit Scope re_scope with re.
Notation "'∅'" := (Empty) : re_scope.
Notation "'ϵ'" := (Null) : re_scope.
Notation "` c `" := (Single c) (at level 10) : re_scope.
Notation "re1 | re2" := (Alt re1 re2) (at level 51, right associativity) : re_scope.
Notation "re1 ;; re2" := (Concat re1 re2) (at level 41, right associativity) : re_scope.
Notation "re *'" := (Star re) (at level 30) : re_scope.
Notation "re +'" := (Plus re) (at level 30) : re_scope.
Notation "re ?" := (QMark re) (at level 30) : re_scope.
Notation "'[r' c1 ; .. ; c2 ]" := (Class (cons c1 .. (cons c2 nil) ..)) : re_scope.
Notation "cs =~ re" := (matches re cs = true) (at level 70) : re_scope.
Notation "cs !~ re" := (matches re cs = false) (at level 70) : re_scope.
Infix "~=~" := (re_equiv) (at level 70) : re_scope.
Open Scope re_scope.

Section Facts.
  Context `{alph : EqDec}.

  Lemma nullable_match re1 re2 :
    re1 ~=~ re2 ->
    nullable re1 = nullable re2.
  Proof. intros Hmatch; apply (Hmatch nil). Qed.

  Lemma derivative_match re1 re2 c :
    re1 ~=~ re2 ->
    derivative c re1 ~=~ derivative c re2.
  Proof. red; intros Hmatch *; apply (Hmatch (c :: cs)). Qed.

  (* Empty *)
  Lemma empty_no_match cs :
    cs !~ ∅.
  Proof. induction cs; auto. Qed.

  (* Null *)
  Lemma null_one_match cs :
    cs =~ ϵ <-> cs = nil.
  Proof.
    split; intros H; subst; auto.
    destruct cs; auto; cbn in H.
    now rewrite empty_no_match in H.
  Qed.

  (* Single *)
  Lemma single_one_match cs c :
    cs =~ `c` <-> cs = c :: nil.
  Proof.
    split; intros H; subst; cbn.
    - destruct cs as [| c' cs]; cbn in *; try easy.
      cases H.
      + now rewrite null_one_match in H; subst.
      + now rewrite empty_no_match in H.
    - now rewrite eq_dec_true.
  Qed.

  (* Alt *)
  Lemma alt_empty_l re :
    ∅ | re ~=~ re.
  Proof.
    red; intros; revert re.
    induction cs; intros; cbn; auto.
  Qed.

  Lemma alt_commute re1 re2 :
    re1 | re2 ~=~ re2 | re1.
  Proof.
    red; intros; revert re1 re2.
    induction cs; intros; cbn; auto with bool.
  Qed.

  Lemma alt_assoc re1 re2 re3 :
    re1 | (re2 | re3) ~=~ (re1 | re2) | re3.
  Proof.
    red; intros; revert re1 re2 re3.
    induction cs; intros; cbn; auto with bool.
  Qed.

  Corollary alt_empty_r re :
    re | ∅ ~=~ re.
  Proof. rewrite alt_commute; apply alt_empty_l. Qed.

  Lemma alt_diag re :
    re | re ~=~ re.
  Proof.
    red; intros; revert re.
    induction cs; intros; cbn; auto using Bool.orb_diag.
  Qed.

  Lemma alt_match_or cs : forall re1 re2,
    matches (re1 | re2) cs = matches re1 cs || matches re2 cs.
  Proof. induction cs; intros; cbn; auto. Qed.

  Corollary alt_match_true cs re1 re2 :
    cs =~ (re1 | re2) <-> (cs =~ re1 \/ cs =~ re2).
  Proof. now rewrite alt_match_or, Bool.orb_true_iff. Qed.

  Corollary alt_match_false cs re1 re2 :
    cs !~ (re1 | re2) <-> (cs !~ re1 /\ cs !~ re2).
  Proof. now rewrite alt_match_or, Bool.orb_false_iff. Qed.

  Lemma alt_cancel_l re re1 re2 :
    re1 ~=~ re2 ->
    re | re1 ~=~ re | re2.
  Proof.
    red; intros Hmatch *; revert re re1 re2 Hmatch.
    induction cs; intros; cbn.
    - erewrite (nullable_match re1); eauto.
    - erewrite !alt_match_or, (derivative_match re1); eauto.
  Qed.

  Corollary alt_cancel_r re re1 re2 :
    re1 ~=~ re2 ->
    re1 | re ~=~ re2 | re.
  Proof. rewrite (alt_commute re1), (alt_commute re2); apply alt_cancel_l. Qed.

  (* Concat *)
  Lemma concat_empty_l re :
    ∅;;re ~=~ ∅.
  Proof. red; intros; induction cs; auto. Qed.

  Lemma concat_empty_r re :
    re;;∅ ~=~ ∅.
  Proof.
    red; intros; revert re.
    induction cs; intros; cbn; destruct (nullable _); auto.
    rewrite alt_empty_r; auto.
  Qed.

  Lemma concat_null_l re :
    ϵ;;re ~=~ re.
  Proof.
    red; intros; revert re.
    induction cs; intros; cbn; auto.
    rewrite alt_match_or, concat_empty_l, empty_no_match; auto.
  Qed.

  Lemma concat_null_r re :
    re;;ϵ ~=~ re.
  Proof.
    red; intros; revert re.
    induction cs; intros; cbn; auto using Bool.andb_true_r.
    destruct (nullable _); auto.
    rewrite alt_match_or, IHcs, empty_no_match; auto using Bool.orb_false_r.
  Qed.

  Lemma concat_match_true cs : forall re1 re2,
    cs =~ re1;;re2 <->
    exists cs1 cs2,
      cs = cs1 ++ cs2 /\ cs1 =~ re1 /\ cs2 =~ re2.
  Proof.
    induction cs; cbn; split; intros H.
    - exists nil, nil; cbn; auto with bool.
    - destruct H as ([] & [] & ? & ? & ?); cbn in *; auto with bool; easy.
    - cases H.
      + rewrite alt_match_true, IHcs in H.
        destruct H; destr *; subst; eauto using app_nil_l, app_comm_cons.
      + rewrite IHcs in H; destr *; subst; eauto using app_nil_l, app_comm_cons.
    - destruct H as (cs1 & ? & Heq & ? & ?).
      destruct (nullable _) eqn:?.
      + rewrite alt_match_true, IHcs.
        destruct cs1; cbn in Heq; simplify; eauto.
        left; eauto using app_comm_cons.
      + rewrite IHcs.
        destruct cs1; cbn in Heq; simplify; eauto.
  Qed.

  Corollary concat_match_false' cs re1 re2 :
    cs !~ re1;;re2 <->
    ~(exists cs1 cs2,
      cs = cs1 ++ cs2 /\ cs1 =~ re1 /\ cs2 =~ re2).
  Proof. apply iff_not, concat_match_true. Qed.

  Corollary concat_match_false cs re1 re2 :
    cs !~ re1;;re2 <->
    forall cs1 cs2,
      cs = cs1 ++ cs2 -> cs1 !~ re1 \/ cs2 !~ re2.
  Proof.
    rewrite concat_match_false', not_exist.
    setoid_rewrite not_exist.
    split; intros H; intuition; subst.
    - destruct (matches re1 _) eqn:?; auto.
      destruct (matches re2 _) eqn:?; auto.
      exfalso; eauto.
    - specialize (H _ _ eq_refl).
      intuition congruence.
  Qed.

  Lemma concat_cancel_l re re1 re2 :
    re1 ~=~ re2 ->
    re;;re1 ~=~ re;;re2.
  Proof.
    red; intros Hmatch *; revert re re1 re2 Hmatch.
    induction cs; intros; cbn.
    - erewrite (nullable_match re1); eauto.
    - destruct (nullable _); eauto.
      erewrite !alt_match_or, IHcs, derivative_match; eauto.
  Qed.

  Lemma concat_cancel_r re re1 re2 :
    re1 ~=~ re2 ->
    re1;;re ~=~ re2;;re.
  Proof.
    red; intros Hmatch *; revert re re1 re2 Hmatch.
    induction cs; intros; cbn.
    - erewrite (nullable_match re1); eauto.
    - erewrite nullable_match; eauto.
      destruct (nullable _); eauto using derivative_match.
      erewrite !alt_match_or, IHcs; eauto using derivative_match.
  Qed.

  Lemma alt_concat_distr_l re1 re2 re3 :
    re1;;(re2 | re3) ~=~ re1;;re2 | re1;;re3.
  Proof.
    red; intros; destruct (matches (_ | _) _) eqn:Halt.
    - rewrite alt_match_true in Halt.
      rewrite !concat_match_true in *.
      destruct Halt; destr *; subst; repeat (esplit; eauto).
      all: rewrite alt_match_true; auto.
    - rewrite alt_match_false in Halt.
      rewrite !concat_match_false in *.
      intros; subst.
      rewrite alt_match_false.
      destruct Halt as (Halt1 & Halt2).
      specialize (Halt1 _ _ eq_refl); specialize (Halt2 _ _ eq_refl).
      intuition.
  Qed.

  Lemma alt_concat_distr_r re1 re2 re3 :
    (re1 | re2);;re3 ~=~ re1;;re3 | re2;;re3.
  Proof.
    red; intros; destruct (matches (_ | _) _) eqn:Halt.
    - rewrite alt_match_true in Halt.
      rewrite !concat_match_true in *.
      destruct Halt; destr *; subst; repeat (esplit; eauto).
      all: rewrite alt_match_true; auto.
    - rewrite alt_match_false in Halt.
      rewrite !concat_match_false in *.
      intros; subst.
      rewrite alt_match_false.
      destruct Halt as (Halt1 & Halt2).
      specialize (Halt1 _ _ eq_refl); specialize (Halt2 _ _ eq_refl).
      intuition.
  Qed.

  Lemma concat_assoc re1 re2 re3 :
    re1;;(re2;;re3) ~=~ (re1;;re2);;re3.
  Proof.
    red; intros; revert re1 re2 re3.
    induction cs; intros; cbn; auto with bool.
    destruct (nullable _); cbn; auto.
    destruct (nullable _); cbn.
    - rewrite !alt_match_or, alt_concat_distr_r, !alt_match_or, !IHcs; auto with bool.
    - rewrite alt_concat_distr_r, !alt_match_or, !IHcs; auto.
  Qed.

  (* Star *)
  Lemma star_match_empty re :
    nil =~ re*'.
  Proof. auto. Qed.

  Lemma star_unfold re :
    re*' ~=~ (ϵ | re;;re*').
  Proof.
    red; intros; revert re.
    induction cs; cbn; intros; auto.
    rewrite alt_empty_l.
    destruct (nullable _); cbn; auto.
    rewrite alt_diag; auto.
  Qed.

  (* Plus *)
  Lemma plus_unfold re :
    re+' ~=~ (re | re;;re+').
  Proof.
    unfold Plus; red; intros.
    rewrite alt_match_or, <- (concat_null_r re), <- alt_match_or, <- alt_concat_distr_l.
    erewrite concat_cancel_l; eauto using star_unfold.
  Qed.

  (* Class *)
  Lemma class_match_true cs cs' :
    cs' =~ Class cs <-> exists c, cs' = c :: nil /\ In c cs.
  Proof.
    induction cs; cbn; split; intros H.
    - now rewrite empty_no_match in H.
    - now destr *.
    - rewrite alt_match_or, Bool.orb_true_iff, IHcs, single_one_match in H.
      destruct H; destr *; eauto.
    - rewrite alt_match_or, Bool.orb_true_iff, IHcs, single_one_match.
      destr *; intuition (subst; eauto).
  Qed.

End Facts.

Section KleeneAlgebra.
  Context {A : Type}.
  Variables (kzero kone : A).
  Variables (kplus kmul : A -> A -> A).
  Variable (kstar : A -> A).
  Variable (keq : A -> A -> Prop).

  Notation "0" := kzero.
  Notation "1" := kone.
  Infix "+" := kplus.
  Infix "*" := kmul.
  Notation "x *'" := (kstar x).
  Infix "~=~" := keq.

  Class KleeneAlgebra := {
    kadd_0_l x : 0 + x ~=~ x;
    kadd_comm x y : x + y ~=~ y + x;
    kadd_assoc x y z : x + (y + z) ~=~ (x + y) + z;
    kadd_idem x : x + x ~=~ x;
    kmul_0_l x : 0 * x ~=~ 0;
    kmul_0_r x : x * 0 ~=~ 0;
    kmul_1_l x : 1 * x ~=~ x;
    kmul_1_r x : x * 1 ~=~ x;
    kmul_assoc x y z : x * (y * z) ~=~ (x * y) * z;
    kadd_kmul_distr_l x y z : x * (y + z) ~=~ x * y + x * z;
    kadd_kmul_distr_r x y z : (y + z) * x ~=~ y * x + z * x;
  }.

End KleeneAlgebra.

Instance RLang_KleeneAlgebra `{EqDec} : KleeneAlgebra ∅ ϵ Alt Concat re_equiv.
Proof.
  constructor; intros; [
    apply alt_empty_l |
    apply alt_commute |
    apply alt_assoc |
    apply alt_diag |
    apply concat_empty_l |
    apply concat_empty_r |
    apply concat_null_l |
    apply concat_null_r |
    apply concat_assoc |
    apply alt_concat_distr_l |
    apply alt_concat_distr_r].
Qed.

Section Tests.
  Import ListNotations.

  Instance nat_alph : EqDec nat := { eq_dec := Nat.eq_dec }.
  Let a := 0.
  Let b := 1.
  Let c := 2.

  Goal [] =~ (`a`*').
  Proof. reflexivity. Qed.
  Goal [a] =~ (`a`*').
  Proof. reflexivity. Qed.
  Goal [a; a] =~ (`a`*').
  Proof. reflexivity. Qed.
  Goal [a; a; b] !~ (`a`*').
  Proof. reflexivity. Qed.

  Goal [b] =~ ((`b`|`c`)+').
  Proof. reflexivity. Qed.
  Goal [c] =~ ((`b`|`c`)+').
  Proof. reflexivity. Qed.
  Goal [] !~ ((`b`|`c`)+').
  Proof. reflexivity. Qed.
  Goal [b; b; c; b] =~ ((`b`|`c`)+').
  Proof. reflexivity. Qed.

  Goal [a; b] =~ (`c`?;;`a`*';;(`b`|`c`)+').
  Proof. reflexivity. Qed.
  Goal [a; c] =~ (`c`?;;`a`*';;(`b`|`c`)+').
  Proof. reflexivity. Qed.
  Goal [b; c; b] =~ (`c`?;;`a`*';;(`b`|`c`)+').
  Proof. reflexivity. Qed.
  Goal [c; a; c] =~ (`c`?;;`a`*';;(`b`|`c`)+').
  Proof. reflexivity. Qed.
  Goal [c; a] !~ (`c`?;;`a`*';;(`b`|`c`)+').
  Proof. reflexivity. Qed.
  Goal [c; c] =~ (`c`?;;`a`*';;(`b`|`c`)+').
  Proof. reflexivity. Qed.

  Goal [] =~ ([r a; b; c]?).
  Proof. reflexivity. Qed.
  Goal [a] =~ ([r a; b; c]?).
  Proof. reflexivity. Qed.
  Goal [b] =~ ([r a; b; c]?).
  Proof. reflexivity. Qed.
  Goal [c] =~ ([r a; b; c]?).
  Proof. reflexivity. Qed.

End Tests.
