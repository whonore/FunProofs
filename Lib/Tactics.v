From FunProofs.Lib Require Import
  EqDec.

Tactic Notation "intuition" tactic3(tactic) := intuition tactic.
Tactic Notation "intuition" := intuition auto.

Ltac inv H := inversion H; clear H; subst.

(* Destruct one match case in H and try to solve with tac. *)
Ltac case1 H tac :=
  let H' := fresh H "_case" in
  lazymatch type of H with
  | context[match ?b with _ => _ end] => destruct b eqn:H'; try tac
  end.

(* Repeatedly destruct match cases in H and try to solve with tac. *)
Tactic Notation "cases" hyp(H) "by" tactic3(tac) :=
  repeat case1 H tac.
Tactic Notation "cases" hyp(H) :=
  cases H by discriminate.
Tactic Notation "cases" "*" "by" tactic3(tac) :=
  repeat match goal with
         | H: _ |- _ => progress cases H by tac
         end.
Tactic Notation "cases" "*" :=
  repeat match goal with
         | H: _ |- _ => progress cases H
         end.

(* Destruct match cases in H and solve with tac until it would leave more than one goal. *)
Tactic Notation "cases" "-branch" hyp(H) "by" tactic3(tac) :=
  repeat (solve [case1 H tac] || (case1 H tac; [])).
Tactic Notation "cases" "-branch" hyp(H) :=
  cases -branch H by easy.
Tactic Notation "cases" "-branch" "*" "by" tactic3(tac) :=
  repeat match goal with
         | H: _ |- _ => progress cases -branch H by tac
         end.
Tactic Notation "cases" "-branch" "*" :=
  repeat match goal with
         | H: _ |- _ => progress cases -branch H
         end.

(* Split conjunction and existentials in the goal. *)
Ltac split_and :=
  repeat match goal with
         | |- _ /\ _ => split
         end.
Ltac split_ex :=
  repeat match goal with
         | |- exists _, _ => esplit
         end.
Ltac split_all := repeat (split_and || split_ex).

(* Destruct conjunction and existentials in hypotheses. *)
Ltac _destr_all H and ex and_tac ex_tac :=
  let Hl := fresh H "_l" in
  let Hr := fresh H "_r" in
  lazymatch type of H with
  | _ /\ _ =>
    lazymatch and with
    | true => destruct H as (Hl & Hr); try and_tac Hl; try and_tac Hr
    | _ => idtac
    end
  | exists x, _ =>
    let name := fresh x in
    lazymatch ex with
    | true => destruct H as (name & H); try ex_tac H
    | _ => idtac
    end
  end.
Ltac destr_and H := _destr_all H true false destr_and idtac.
Ltac destr_ex H := _destr_all H false true idtac destr_ex.
Ltac destr H := _destr_all H true true destr destr.
Tactic Notation "destr_and" "*" :=
  repeat match goal with
         | H: _ /\ _ |- _ => destr_and H
         end.
Tactic Notation "destr_ex" "*" :=
  repeat match goal with
         | H: exists _, _ |- _ => destr_ex H
         end.
Tactic Notation "destr" "*" :=
  repeat (destr_and * || destr_ex *).

(* Simplify equalities. *)
Ltac inj H := assert_succeeds (injection H); inv H.
Ltac simplify_eqs :=
  repeat match goal with
         | H: ?x = ?x |- _ => clear dependent H
         | H: ?x <> ?x |- _ => contradict H; reflexivity
         | H: ?x = ?y |- _ => inj H
         | H: ?x = ?y |- _ => discriminate H
         | H: ?x = ?y, H': ?x = ?z |- _ =>
           solve [now exfalso; assert (y = z) by (rewrite <- H, <- H'; auto)]
         | H: ?x = ?y, H': ?z = ?x |- _ =>
           solve [now exfalso; assert (y = z) by (rewrite <- H, <- H'; auto)]
         | _ => subst
         end.

Ltac simplify := repeat (simplify_eqs || simplify_eq_dec).

(* Rename hypotheses by pattern matching. *)
Ltac prename' pat H name :=
  match type of H with
  | context[?pat'] => unify pat pat'; rename H into name
  end.
Tactic Notation "prename" open_constr(pat) "into" ident(name) :=
  lazymatch goal with
  | H: pat, H': pat |- _ =>
    fail 0 "Multiple possible matches for" pat ":" H "and" H'
  | H: pat |- _ => prename' pat H name
  | H: context[pat], H': context[pat] |- _ =>
    fail 0 "Multiple possible matches for" pat ":" H "and" H'
  | H: context[pat] |- _ => prename' pat H name
  | _ => fail 0 "No hypothesis matching" pat
  end.
