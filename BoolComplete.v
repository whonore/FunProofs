From Coq Require Import
  Bool
  List
  PeanoNat
  Permutation
  RelationClasses.
From FunProofs.Lib Require Import
  Util.
Import ListNotations.

Notation "[ x ]  :> T" := (cons (x : T) nil) (at level 0) : list_scope.
Notation "[ x ; y ; .. ; z ]  :> T" :=
  (cons (x : T) (cons (y : T) .. (cons (z : T) nil) ..)) (at level 0) : list_scope.

Declare Scope bexp.
Delimit Scope bexp with bexp.

(* Variables *)
Definition id := nat.
Definition varmap := id -> bool.

Definition initmap : varmap := fun _ => false.
Definition getvar (v: id) (vs: varmap) : bool := vs v.
Definition setvar (val: id * bool) (vs: varmap) : varmap :=
  fun v' => if fst val =? v' then (snd val) else getvar v' vs.
Definition setvars (vals: list (id * bool)) (vs: varmap) : varmap :=
  fold_right setvar vs vals.
Definition buildmap (vals: list (id * bool)) : varmap := setvars vals initmap.

Notation "v |-> b" := (v, b) (at level 10) : bexp.
Notation "vs @ v" := (getvar v vs) (at level 20) : bexp.
Notation "vs ! v" := (setvar v vs) (at level 20) : bexp.
Notation "{ m1 , .. , mn }" := (buildmap (cons m1%bexp .. (cons mn%bexp nil) ..)) : bexp.

Section Vars.
  Open Scope bexp.

  Lemma get_set_same : forall v val vs, vs ! (v, val) @ v = val.
  Proof.
    unfold getvar, setvar; intros; cbn; rewrite Nat.eqb_refl; auto.
  Qed.

  Lemma get_set_other : forall v v' val vs, v <> v' -> vs ! (v, val) @ v' = vs @ v'.
  Proof.
    unfold getvar, setvar; intros * Hneq; cbn.
    apply Nat.eqb_neq in Hneq; rewrite Hneq; auto.
  Qed.

  Lemma setvars_correct : forall vals vs v val,
    NoDup (map fst vals) -> In (v, val) vals ->
    setvars vals vs @ v = val.
  Proof.
    induction vals as [| val' vals]; cbn -[getvar]; intros * Huniq Hin;
      inv Huniq; intuition (subst; auto using get_set_same).
    destruct val'; fold (setvars vals vs); rewrite get_set_other; auto.
    intros ->; prename (_ -> False) into Hnin; apply Hnin.
    cbn; rewrite in_map_iff; repeat esplit; eauto; auto.
  Qed.

End Vars.

(* Boolean Expressions *)
Inductive bunary := BNeg.
Inductive bbin := BAnd | BOr | BXor | BNand | BNor | BImpl | BBij.
Inductive bop := B1 (f: bunary) | B2 (f: bbin).
Inductive bexp :=
  BVar (v: id) | BConst (b: bool) | BUn (f: bunary) (b: bexp) | BBin (f: bbin) (b1 b2: bexp).
Scheme Equality for bbin.

Fixpoint binterp (e: bexp) (vars: varmap) : bool :=
  match e with
  | BVar v => vars @ v
  | BConst b => b
  | BUn f e' =>
    match f with
    | BNeg => negb
    end (binterp e' vars)
  | BBin f e1 e2 =>
    match f with
    | BAnd => andb
    | BOr => orb
    | BXor => xorb
    | BNand => fun x y => negb (andb x y)
    | BNor => fun x y => negb (orb x y)
    | BImpl => implb
    | BBij => fun x y => andb (implb x y) (implb y x)
    end (binterp e1 vars) (binterp e2 vars)
  end%bexp.

Notation "[[ e | v ]]" := (binterp e v) : bexp.
Notation "'T'" := (BConst true) : bexp.
Notation "'F'" := (BConst false) : bexp.
Notation "! e" := (BUn BNeg e) (at level 35, right associativity) : bexp.
Notation "e1 && e2" := (BBin BAnd e1 e2) (at level 40, left associativity) : bexp.
Notation "e1 || e2" := (BBin BOr e1 e2) (at level 50, left associativity) : bexp.
Notation "e1 |^ e2" := (BBin BXor e1 e2) (at level 50, left associativity) : bexp.
Notation "e1 !& e2" := (BBin BNand e1 e2) (at level 40, left associativity) : bexp.
Notation "e1 !| e2" := (BBin BNor e1 e2) (at level 50, left associativity) : bexp.
Notation "e1 --> e2" := (BBin BImpl e1 e2) (at level 55, left associativity) : bexp.
Notation "e1 <--> e2" := (BBin BBij e1 e2) (at level 54, no associativity) : bexp.
Coercion BVar : id >-> bexp.
Coercion BConst : bool >-> bexp.

Coercion B1 : bunary >-> bop.
Coercion B2 : bbin >-> bop.

Fixpoint subexp' (e e': bexp) :=
  match e' with
  | BUn _ e'' => e = e'' \/ subexp' e e''
  | BBin _ e1 e2 => e = e1 \/ e = e2 \/ subexp' e e1 \/ subexp' e e2
  | _ => False
  end.
Definition subexp (e e': bexp) := e = e' \/ subexp' e e'.

Arguments subexp _ _ /.

Fixpoint has_bop (f: bop) (e: bexp) :=
  match e with
  | BUn f' e' => f = f' \/ has_bop f e'
  | BBin f' e1 e2 => f = f' \/ has_bop f e1 \/ has_bop f e2
  | _ => False
  end.

Definition has_only (fs: list bop) (e: bexp) :=
  forall f, has_bop f e -> In f fs.

Definition bcomplete (fs: list bop) :=
  forall f: bool -> bool -> bool,
    exists f': bexp,
      has_only fs f' /\
      (forall b1 b2, f b1 b2 = [[f' | {0 |-> b1, 1 |-> b2}]])%bexp.

Definition bequiv (fs: list bop) (fs': list bop) :=
  forall e: bexp,
    has_only fs e ->
    exists e': bexp,
      has_only fs' e' /\ (forall vs, [[e | vs]] = [[e' | vs]])%bexp.

Instance subexp_refl : Reflexive subexp.
Proof. repeat red; auto. Qed.

Instance subexp'_trans : Transitive subexp'.
Proof.
  intros e1 e2 e3; revert e1 e2; induction e3; cbn; intuition (subst; eauto).
Qed.

Instance subexp_trans : Transitive subexp.
Proof.
  unfold subexp; red; intuition (subst; auto).
  right; etransitivity; eauto.
Qed.

Instance subexp_preorder : PreOrder subexp.
Proof. constructor; typeclasses eauto. Qed.

Instance bequiv_refl : Reflexive bequiv.
Proof. repeat red; intros; eauto. Qed.

Instance bequiv_trans : Transitive bequiv.
Proof.
  red; unfold bequiv; intros * Hequiv1 Hequiv2 * Honly1.
  edestruct Hequiv1 as (? & ? & ?); eauto.
  edestruct Hequiv2 as (? & ? & ?); eauto.
Qed.

Instance bequiv_preorder : PreOrder bequiv.
Proof. constructor; typeclasses eauto. Qed.

Lemma bequiv_bcomplete : forall fs fs',
  bcomplete fs -> bequiv fs fs' -> bcomplete fs'.
Proof.
  unfold bcomplete, bequiv; intros * Hcomplete Hequiv *.
  destruct (Hcomplete f) as (f' & ? & ?).
  destruct (Hequiv f') as (f'' & ? & ?); eauto.
Qed.

Lemma has_only_perm : forall fs fs' e,
  Permutation fs fs' -> has_only fs e -> has_only fs' e.
Proof.
  induction 1; auto; unfold has_only; cbn; intros Honly * Hbop;
    apply Honly in Hbop; intuition eauto using Permutation_in.
Qed.

Lemma bcomplete_perm : forall fs fs',
  Permutation fs fs' -> bcomplete fs -> bcomplete fs'.
Proof.
  unfold bcomplete; intros * Hperm Hcomp *.
  destruct (Hcomp f) as (? & ? & ?); eauto using has_only_perm.
Qed.

Lemma bequiv_perm_l : forall fs fs' fs'',
  Permutation fs fs' -> bequiv fs fs'' -> bequiv fs' fs''.
Proof.
  unfold bequiv; intros * Hperm Hequiv * Honly.
  destruct (Hequiv e) as (? & ? & ?); eauto using has_only_perm, Permutation_sym.
Qed.

Lemma bequiv_perm_r : forall fs fs' fs'',
  Permutation fs' fs'' -> bequiv fs fs' -> bequiv fs fs''.
Proof.
  unfold bequiv; intros * Hperm Hequiv * Honly.
  destruct (Hequiv e) as (? & ? & ?); eauto using has_only_perm.
Qed.

Lemma has_bop_subexp' : forall e' e f,
  subexp' e e' -> has_bop f e -> has_bop f e'.
Proof.
  induction e'; cbn; intros * Hsub Hbop; intuition (subst; eauto).
Qed.

Corollary has_bop_subexp : forall e' e f,
  subexp e e' -> has_bop f e -> has_bop f e'.
Proof.
  intros * [|] **; subst; eauto using has_bop_subexp'.
Qed.

Lemma has_only_subexp' : forall e' e fs,
  subexp' e e' -> has_only fs e' -> has_only fs e.
Proof.
  induction e'; cbn; intros * Hsub Honly; unfold has_only in *;
    cbn in *; intuition (subst; eauto).
Qed.

Corollary has_only_subexp : forall e' e fs,
  subexp e e' -> has_only fs e' -> has_only fs e.
Proof.
  intros * [|] **; subst; eauto using has_only_subexp'.
Qed.

Ltac ttable f :=
  destruct (f true true) eqn:TT,
           (f true false) eqn:TF,
           (f false true) eqn:FT,
           (f false false) eqn:FF.
Ltac complete := split; [red; cbn; intros []; intuition (subst; auto) | intros [] []; cbn; auto].

Lemma neg_and_complete : bcomplete [BNeg; BAnd] :> bop.
Proof.
  set (x := BVar 0); set (y := BVar 1).
  hnf; intros; ttable f.
  - exists (T)%bexp; complete.
  - exists (!(!x && !y))%bexp; complete.
  - exists (!(!x && y))%bexp; complete.
  - exists (x)%bexp; complete.
  - exists (!(x && !y))%bexp; complete.
  - exists (y)%bexp; complete.
  - exists (!(x && !y) && !(y && !x))%bexp; complete.
  - exists (x && y)%bexp; complete.
  - exists (!(x && y))%bexp; complete.
  - exists (!(!x && !y) && !(x && y))%bexp; complete.
  - exists (!y)%bexp; complete.
  - exists (x && !y)%bexp; complete.
  - exists (!x)%bexp; complete.
  - exists (!x && y)%bexp; complete.
  - exists (!x && !y)%bexp; complete.
  - exists (F)%bexp; complete.
Qed.

Lemma neg_and_equiv_nand : bequiv ([BNeg; BAnd] :> bop) ([BNand] :> bop).
Proof.
  hnf; induction e; intros Honly.
  - exists (BVar v); split; [hnf; cbn |]; auto.
  - exists (BConst b); split; [hnf; cbn |]; auto.
  - destruct f.
    destruct IHe as (e' & ? & Heq); try solve [eapply has_only_subexp; eauto; cbn; auto].
    exists (e' !& e')%bexp.
    split; [unfold has_only in *; cbn in *; intros []; intuition (subst; auto) |].
    cbn; intros; rewrite Heq, andb_diag; auto.
  - destruct f;
      try solve [match type of Honly with
                 | has_only _ (BBin ?f _ _) => specialize (Honly f); cbn in Honly; intuition easy
                 end].
    destruct IHe1 as (e1' & ? & Heq1),
             IHe2 as (e2' & ? & Heq2);
      try solve [eapply has_only_subexp; eauto; cbn; auto].
    exists ((e1' !& e2') !& (e1' !& e2'))%bexp.
    split; [unfold has_only in *; cbn in *; intros []; intuition (subst; auto) |].
    cbn; intros; rewrite Heq1, Heq2, andb_diag, negb_involutive; auto.
Qed.

Corollary nand_complete : bcomplete [BNand] :> bop.
Proof. eapply bequiv_bcomplete; eauto using neg_and_equiv_nand, neg_and_complete. Qed.
