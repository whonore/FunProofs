From Coq Require Import
  PeanoNat
  Permutation.
From FunProofs.Lib Require Import
  KVMap
  Util.
Import ListNotations.

Notation "[ x ]  :> T" := (cons (x : T) nil) (at level 0) : list_scope.
Notation "[ x ; y ; .. ; z ]  :> T" :=
  (cons (x : T) (cons (y : T) .. (cons (z : T) nil) ..)) (at level 0) : list_scope.

Declare Scope bexp.
Delimit Scope bexp with bexp.
Open Scope kvmap.

(* Variables *)
Definition id := nat.
Definition varmap := kvmap id bool.

(* Boolean Expressions *)
Inductive bunary := BNeg.
Inductive bbin := BAnd | BOr | BXor | BNand | BNor | BImpl | BBij.
Inductive bop := B1 (f : bunary) | B2 (f : bbin).
Inductive bexp :=
  | BVar (v : id)
  | BConst (b : bool)
  | BUn (f : bunary) (b : bexp)
  | BBin (f : bbin) (b1 b2 : bexp).

Fixpoint binterp (e : bexp) (vars : varmap) : bool :=
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

Fixpoint subexp' (e e' : bexp) :=
  match e' with
  | BUn _ e'' => e = e'' \/ subexp' e e''
  | BBin _ e1 e2 => e = e1 \/ e = e2 \/ subexp' e e1 \/ subexp' e e2
  | _ => False
  end.
Definition subexp (e e' : bexp) := e = e' \/ subexp' e e'.

Arguments subexp _ _ /.

Fixpoint has_bop (f : bop) (e : bexp) :=
  match e with
  | BUn f' e' => f = f' \/ has_bop f e'
  | BBin f' e1 e2 => f = f' \/ has_bop f e1 \/ has_bop f e2
  | _ => False
  end.

Definition has_only (fs : list bop) (e : bexp) :=
  forall f, has_bop f e -> In f fs.

Arguments has_only _ _ /.

Definition bcomplete (fs : list bop) :=
  forall f : bool -> bool -> bool,
    exists f' : bexp,
      has_only fs f' /\
      (forall b1 b2, f b1 b2 = [[f' | {0 |-> b1, 1 |-> b2}[false] ]])%bexp.

Definition bweaker (fs : list bop) (fs' : list bop) :=
  forall e : bexp,
    has_only fs e ->
    exists e' : bexp,
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

Instance bweaker_refl : Reflexive bweaker.
Proof. repeat red; eauto. Qed.

Instance bweaker_trans : Transitive bweaker.
Proof.
  red; unfold bweaker; intros * Hweak1 Hweak2 * Honly1.
  edestruct Hweak1 as (? & ? & ?); eauto.
  edestruct Hweak2 as (? & ? & ?); eauto.
Qed.

Instance bweaker_preorder : PreOrder bweaker.
Proof. constructor; typeclasses eauto. Qed.

Lemma bweaker_bcomplete fs fs' :
  bcomplete fs -> bweaker fs fs' -> bcomplete fs'.
Proof.
  unfold bcomplete, bweaker; intros Hcomplete Hweak *.
  destruct (Hcomplete f) as (f' & ? & ?).
  destruct (Hweak f') as (f'' & ? & ?); eauto.
Qed.

Lemma has_only_perm fs fs' e :
  Permutation fs fs' -> has_only fs e -> has_only fs' e.
Proof.
  induction 1; auto; cbn; intros Honly * Hbop;
    apply Honly in Hbop; intuition eauto using Permutation_in.
Qed.

Lemma bcomplete_perm fs fs' :
  Permutation fs fs' -> bcomplete fs -> bcomplete fs'.
Proof.
  unfold bcomplete; intros Hperm Hcomp *.
  destruct (Hcomp f) as (? & ? & ?); eauto using has_only_perm.
Qed.

Lemma bweaker_perm_l fs fs' fs'' :
  Permutation fs fs' -> bweaker fs fs'' -> bweaker fs' fs''.
Proof.
  unfold bweaker; intros Hperm Hweak * Honly.
  destruct (Hweak e) as (? & ? & ?); eauto using has_only_perm, Permutation_sym.
Qed.

Lemma bweaker_perm_r fs fs' fs'' :
  Permutation fs' fs'' -> bweaker fs fs' -> bweaker fs fs''.
Proof.
  unfold bweaker; intros Hperm Hweak * Honly.
  destruct (Hweak e) as (? & ? & ?); eauto using has_only_perm.
Qed.

Lemma has_bop_subexp' e e' f :
  subexp' e e' -> has_bop f e -> has_bop f e'.
Proof.
  induction e'; cbn; intros * Hsub Hbop; intuition (subst; eauto).
Qed.

Corollary has_bop_subexp e e' f :
  subexp e e' -> has_bop f e -> has_bop f e'.
Proof.
  intros [|] **; subst; eauto using has_bop_subexp'.
Qed.

Lemma has_only_subexp' e e' fs :
  subexp' e e' -> has_only fs e' -> has_only fs e.
Proof.
  induction e'; cbn; intros * Hsub Honly; cbn in *; intuition (subst; eauto).
Qed.

Corollary has_only_subexp e e' fs :
  subexp e e' -> has_only fs e' -> has_only fs e.
Proof.
  intros [|] **; subst; eauto using has_only_subexp'.
Qed.

Ltac ttable f :=
  destruct (f true true) eqn:TT,
           (f true false) eqn:TF,
           (f false true) eqn:FT,
           (f false false) eqn:FF.
Ltac complete := cbv; split; [intros []; intuition (subst; auto) | now intros [] []; auto].

Lemma neg_and_complete : bcomplete [BNeg; BAnd] :> bop.
Proof.
  set (x := BVar 0); set (y := BVar 1).
  intros f; ttable f.
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

Lemma has_only_bbin_inv fs f e1 e2 :
  has_only fs (BBin f e1 e2) -> In (B2 f) fs.
Proof. cbn; intuition auto. Qed.

Lemma neg_and_weaker_nand : bweaker ([BNeg; BAnd] :> bop) ([BNand] :> bop).
Proof.
  hnf; induction e; intros Honly.
  - now exists (v)%bexp.
  - now exists (b)%bexp.
  - destruct f, IHe as (e' & ? & Heq); [eapply has_only_subexp; eauto; cbn; auto |].
    exists (e' !& e')%bexp; cbn in *.
    split; [intros []; intuition (subst; auto) |].
    intros; now rewrite Heq, andb_diag.
  - apply has_only_bbin_inv in Honly as Hin; repeat destruct Hin as [Hin | Hin]; inv Hin.
    destruct IHe1 as (e1' & ? & Heq1), IHe2 as (e2' & ? & Heq2);
      try solve [eapply has_only_subexp; eauto; cbn; auto].
    exists ((e1' !& e2') !& (e1' !& e2'))%bexp; cbn in *.
    split; [intros []; intuition (subst; auto) |].
    intros; now rewrite Heq1, Heq2, andb_diag, negb_involutive.
Qed.

Corollary nand_complete : bcomplete [BNand] :> bop.
Proof. eapply bweaker_bcomplete; eauto using neg_and_weaker_nand, neg_and_complete. Qed.
