From Coq Require Import
  Arith
  Bool
  List
  ZArith.

Class EqDec (A : Type) := { eq_dec (x y : A) : {x = y} + {x <> y}; }.

Definition eqb {A} `{EqDec A} (x y : A) : bool :=
  if eq_dec x y then true else false.

Module Import EqDecNotations.
  Infix "==" := eq_dec (at level 70).
  Infix "==?" := eqb (at level 70).
End EqDecNotations.

Fact eq_dec_true A `{EqDec} x y (T E : A) : x = y -> (if x == y then T else E) = T.
Proof. now destruct (_ == _). Qed.

Fact eq_dec_false A `{EqDec} x y (T E : A) : x <> y -> (if x == y then T else E) = E.
Proof. now destruct (_ == _). Qed.

Corollary eqb_true `{EqDec} x y : x = y -> x ==? y = true.
Proof. intros; unfold eqb; rewrite eq_dec_true; auto. Qed.

Corollary eqb_false `{EqDec} x y : x <> y -> x ==? y = false.
Proof. intros; unfold eqb; rewrite eq_dec_false; auto. Qed.

Ltac simplify_eq_dec :=
  repeat match goal with
         | H: context[_ == _] |- _ =>
           first [rewrite eq_dec_true in H by auto
                 | rewrite eq_dec_false in H by auto]
         | |- context[_ == _] =>
           first [rewrite eq_dec_true by auto
                 | rewrite eq_dec_false by auto]
         | H: context[_ ==? _] |- _ =>
           first [rewrite eqb_true in H by auto
                 | rewrite eqb_false in H by auto]
         | |- context[_ ==? _] =>
           first [rewrite eqb_true by auto
                 | rewrite eqb_false by auto]
         end.

#[export] Instance nat_eq_dec : EqDec nat := {| eq_dec := Nat.eq_dec |}.
#[export] Instance Z_eq_dec : EqDec Z := {| eq_dec := Z.eq_dec |}.
#[export] Instance bool_eq_dec : EqDec bool := {| eq_dec := bool_dec |}.
#[export] Instance list_eq_dec {A} `{eq : EqDec A} : EqDec (list A) := {|
  eq_dec := list_eq_dec eq_dec
|}.
#[refine, export] Instance option_eq_dec {A} `{eq : EqDec A} : EqDec (option A) := {|
  eq_dec := fun x y =>
    match x, y with
    | Some x, Some y => if eq_dec x y then left _ else right _
    | None, None => left eq_refl
    | _, _ => right _
    end
|}.
Proof. all: abstract congruence. Defined.
