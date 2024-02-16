(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List Utf8.

From KruskalFinite
  Require Import finite choice.

Import ListNotations.

Set Implicit Arguments.

Notation decider A := ({A}+{¬A}).
Notation discrete A := (∀ x y : A, decider (x=y)).

Fact decider_swap (A B : Prop) :   {A}+{B} → {B}+{A}.                      Proof. tauto. Qed.
Fact decider_decide (A B : Prop) : {A}+{B} → A ∨ B.                        Proof. tauto. Qed.

Fact decider_equiv (A B : Prop) : (A ↔ B) → decider A → decider B.         Proof. tauto. Qed.
Fact decider_equiv_r (A B : Prop) : (A ↔ B) → decider B → decider A.       Proof. tauto. Qed.
Fact decider_disj (A B : Prop) : decider A → decider B → decider (A ∨ B).  Proof. tauto. Qed.
Fact decider_conj (A B : Prop) : decider A → decider B → decider (A ∧ B).  Proof. tauto. Qed.
Fact decider_imp (A B : Prop) : decider A → decider B → decider (A → B).   Proof. tauto. Qed.

Tactic Notation "decide" "swap" := apply decider_swap.

Tactic Notation "decide" "eq" uconstr(H) :=
    ( apply decider_equiv with (1 := H)
   || apply decider_equiv_r with (1 := H) ).

Fact decider_exists_finite X (P : X → Prop) :
        finite X
      → (∀x, decider (P x))
      → decider (ex P).
Proof.
  intros; destruct finite_choice_t with (P := fun x => ~ P x) (Q := P); firstorder.
Qed.

Fact decider_exists_fin X (P Q : X → Prop) :
       fin P
     → (∀x, P x → decider (Q x))
     → decider (∃x, P x ∧ Q x).
Proof.
  intros; destruct (@fin_choice_t _ P (fun x => ~ Q x) Q); firstorder.
Qed.

Fact decider_forall_finite X (P : X → Prop) :
       finite X
     → (∀x, decider (P x))
     → decider (∀x, P x).
Proof.
  intros.
  destruct finite_choice_t with (Q := fun x => ~ P x) (P := P); firstorder.
Qed.

Fact decider_forall_fin X (P Q : X → Prop) :
       fin P
     → (∀x, P x → decider (Q x))
     → decider (∀x, P x -> Q x).
Proof.
  intros; destruct (@fin_choice_t _ P Q (fun x => ~ Q x)); firstorder.
Qed.

Tactic Notation "decide" "auto" :=
  repeat (apply decider_disj
       || apply decider_conj
       || apply decider_imp
       || apply decider_exists_fin
       || apply decider_exists_finite
       || apply decider_forall_fin
       || apply decider_forall_finite ); auto.
