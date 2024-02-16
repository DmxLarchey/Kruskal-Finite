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

From KruskalTrees
  Require Import list_utils idx vec.

From KruskalFinite
  Require Import finite.

Import ListNotations idx_notations vec_notations.

Set Implicit Arguments.

Fact finite_choice (X : Type) (P Q : X → Prop) :
           finite X
         → (∀x, P x ∨ Q x)
         → (∀x, P x) ∨ ∃x, Q x.
Proof.
  intros (l & Hl) ?.
  destruct (list_choice P Q l); firstorder.
Qed.

Fact finite_choice_t (X : Type) (P Q : X → Prop) :
           finite X
         → (∀x, { P x } + { Q x })
         → (∀x, P x) + { x | Q x }.
Proof.
  intros (l & Hl) ?.
  destruct (@list_choice_t _ P Q l); firstorder.
Qed.

Fact fin_choice X (F P Q : X → Prop) :
          fin F
        → (∀x, F x → P x ∨ Q x)
        → (∀x, F x → P x) ∨ ∃x, F x ∧ Q x.
Proof.
  intros (l & Hl) ?.
  destruct (list_choice P Q l); firstorder.
Qed.

Fact fin_choice_t X (F P Q : X -> Prop) :
         fin F
       → (∀x, F x → { P x } + { Q x })
       → (∀x, F x → P x) + { x | F x ∧ Q x }.
Proof.
  intros (l & Hl) HF.
  destruct (@list_choice_t _ P Q l); firstorder.
Qed.

Fact fin_choice_cst_left (X : Type) (P : Prop) (F Q : X → Prop) :
          fin F
        → (∀x, F x → P ∨ Q x)
        → P ∨ ∀x, F x → Q x.
Proof.
  intros HF HPQ.
  assert (HPQ' : forall x, F x -> Q x \/ P) by firstorder.
  apply fin_choice in HPQ' as [ H | (? & ? & ?) ]; auto.
Qed.

Fact fin_not_forall_exists_not X (P Q : X → Prop) :
      fin P
    → (∀x, P x → Q x ∨ ~ Q x)
    → ¬(∀x, P x → Q x) 
    → ∃x, P x ∧ ¬ Q x.
Proof.
  intros H1 H2 H3.
  destruct (fin_choice _ _ H1 H2); auto; tauto.
Qed.


