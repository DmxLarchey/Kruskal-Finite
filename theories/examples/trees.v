(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Arith List Lia Utf8.

From KruskalTrees
  Require Import list_sum ltree rtree notations tactics.

From KruskalFinite
  Require Import finite.

Import ListNotations ltree_notations rtree_notations.

Set Implicit Arguments.

Section fin_list_sum.

  Variables (X : Type)
            (f : X → nat)
            (Hf : ∀x, 0 < f x)                     (* f is positive *)
            (n : nat)
            (Hn : ∀j, j < n → fin (λ x, f x = j)) (* only finitely many x st f x < n *)
            .

  Hint Resolve eq_nat_dec : core.

  (** If the measure f is positive and only finitely many values
      exists at a given measure below n then there are finitely many
      lists with a given mezasure below n *)
  Lemma fin_list_sum j : j < n → fin (λ l, list_sum f l = j).
  Proof.
    induction j as [ j IHj ] using (well_founded_induction_type lt_wf); intros Hj.
    apply fin_equiv with (P := fun l =>
        j = 0 /\ [] = l
     \/ (exists x, [x] = l /\ f x = j)
     \/ exists c, (exists p, fst p ++ snd p = l
                                                    /\ list_sum f (fst p) = fst c
                                                    /\ list_sum f (snd p) = snd c)
                /\ 0 < fst c /\ 0 < snd c /\ fst c + snd c = j).
    + intros l; split.
      * intros [ (-> & <-) | [ (x & <- & <-)
               | ((a,b) & ((u,v) & <- & H1 & H2) & H3 & H4 & H5) ] ]; simpl in *; auto.
        rewrite list_sum_app; lia.
      * destruct l as [ | x [ | y l ] ]; simpl.
        - intros <-; auto.
        - intros <-; right; left; exists x; auto.
        - intros H; do 2 right.
          exists (f x, list_sum f (y::l)); rsplit 3; simpl; auto; tlia.
          2: generalize (Hf y); lia.
          exists ([x],y::l); simpl; rsplit 2; auto.
    + finite union; [ finite dec left | ].
      fin auto.
      finite compose.
      intros (a,b); simpl; intros (Ha & Hb & H).
      finite compose.
      apply fin_product with (P := fun l => list_sum f l = a)
                             (Q := fun l => list_sum f l = b).
      all: apply IHj; lia.
  Qed.

End fin_list_sum.

Theorem fin_rtree_size_eq n : fin (fun t => ⌊t⌋ᵣ = n).
Proof.
  induction n as [ n IHn ] using (well_founded_induction_type lt_wf).
  apply fin_equiv with (P := fun t => exists l, ⟨l⟩ᵣ = t /\ 1+list_sum (fun t => ⌊t⌋ᵣ) l = n).
  + intros t; split.
    * intros (l & <- & H); rewrite rtree_size_fix; auto.
    * destruct t as [l]; intros <-; exists l; rewrite rtree_size_fix; auto.
  + finite compose.
    destruct n as [ | n ].
    1: finite as (fun _ => False); lia.
    finite as (fun l => list_sum (fun t => ⌊t⌋ᵣ) l = n).
    1: intro; lia.
    apply fin_list_sum with (n := S n); auto.
    apply rtree_size_gt.
Qed.

Section fin_ltree_weight.

  (** We show that given a positive weight to each node value
      such that for a given weight, there are only
      finitely many nodes, then there are finitely many
      trees of any given total weight *)

  Variables (X : Type) (w : X → nat) (Hw : ∀x, 0 < w x)
            (n : nat) (Hn : ∀s, s < n → fin (λ x, w x = s)).

  Hint Resolve ltree_weight_gt : core.

  Theorem fin_ltree_weight s : s < n → fin (λ t, ltree_weight w t = s).
  Proof.
    induction s as [ s IHs ] using (well_founded_induction_type lt_wf); intros Hs.
    apply fin_equiv
      with (P := fun t => exists k, (exists l, (exists x, ⟨x|l⟩ₗ = t /\ w x = S k)
                                     /\ list_sum (ltree_weight w) l = s-S k)
                                   /\ k < s ).
    + intros [ x l ]; split.
      * intros (k & (m & (y & H1 & H2) & H3) & H4).
        inversion H1; subst y m.
        rewrite ltree_weight_fix; lia.
      * intros <-.
        generalize (Hw x); intros Hx.
        exists (w x-1); split.
        - exists l; split.
          ++ exists x; split; auto; lia.
          ++ rewrite ltree_weight_fix; lia.
        - rewrite ltree_weight_fix; lia.
    + finite compose.
      intros k Hk.
      finite compose.
      * intros l Hl.
        finite compose.
        apply Hn; lia.
      * apply fin_list_sum with (n := s); auto; tlia.
        intros; apply IHs; lia.
  Qed.

End fin_ltree_weight.