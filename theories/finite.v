(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

From Coq
  Require Import Arith List Lia Utf8.

From KruskalTrees
  Require Import list_sum idx vec ltree rtree notations tactics.

Import ListNotations idx_notations vec_notations ltree_notations rtree_notations.

Set Implicit Arguments.

#[global] Create HintDb finite_db.

Tactic Notation "fin" "auto" := auto with finite_db.
Tactic Notation "fin" "eauto" := eauto with finite_db.

(** These are all "informative" definitions *)

Definition finite (X : Type) := { l : list X | ∀x, x ∈ l }.

Definition fin {X} (P : X -> Prop) := { l | ∀x, P x ↔ x ∈ l }.
(* Definition fin_inv_at {A B} (f : A -> B) b := fin (fun a => f a = b). *)

Fact fin_equiv X (P Q : X → Prop) : (∀x, P x ↔ Q x) → fin P → fin Q.
Proof. intros H (l & Hl); exists l; intro; rewrite <- H; auto. Qed.

Fact fin_equiv_r X (P Q : X → Prop) : (∀x, Q x ↔ P x) → fin P → fin Q.
Proof. intros H; apply fin_equiv; firstorder. Qed.

Fact finite_empty X : (X → False) → finite X.
Proof. exists []; intros; tauto. Qed.

Fact fin_empty X (P : X → Prop) : (∀x, ¬ P x) → fin P.
Proof. exists []; intros; simpl; firstorder. Qed.

Fact fin_False X : fin (λ _ : X, False).
Proof. exists nil; tauto. Qed.

Fact fin_True X : finite X → fin (λ _ : X, True).
Proof. intros (l & Hl); exists l; firstorder. Qed.

Fact fin_singleton X (x : X) : fin (eq x).
Proof. exists [x]; simpl; split; tauto. Qed.

Fact fin_In_list X (l : list X) : fin (λ x, x ∈ l).
Proof. exists l; tauto. Qed.

Fact fin_union X (P Q : X → Prop) : fin P → fin Q → fin (P ∪₁ Q).
Proof.
  intros (l & Hl) (m & Hm).
  exists (l++m); intros x.
  rewrite Hl, Hm, in_app_iff; tauto.
Qed.

Fact fin_product X Y (P : X → Prop) (Q : Y → Prop) :
       fin P → fin Q → fin (λ p : X * Y, P (fst p) ∧ Q (snd p)).
Proof.
  intros (l & Hl) (m & Hm).
  exists (list_prod l m); intros (x,y).
  rewrite in_prod_iff, Hl, Hm; tauto.
Qed.

#[global] Hint Resolve finite_empty fin_empty fin_False fin_True
                       fin_singleton fin_In_list fin_union : finite_db.

Fact fin_dec X (P : X → Prop) :
        (∀x, {P x}+{¬ P x}) → finite X → fin P.
Proof.
  intros H (l & Hl).
  exists (filter (fun x => if H x then true else false) l).
  intros x; rewrite filter_In.
  destruct (H x); split; try tauto; easy.
Qed.

Fact fin_inter_dec_left X (P Q : X → Prop) :
        (∀x, {P x}+{¬ P x}) → fin Q → fin (P ∩₁ Q).
Proof.
  intros H (l & Hl).
  exists (filter (fun x => if H x then true else false) l).
  intros x; rewrite filter_In, <- Hl.
  destruct (H x); split; try tauto; easy.
Qed.

Fact fin_inter_cst_lft X (P : Prop) (Q : X → Prop) : P → fin Q → fin (λ x, P ∧ Q x).
Proof. intro; apply fin_inter_dec_left; tauto. Qed.

Tactic Notation "finite" "as" uconstr(H) :=
   ( apply fin_equiv with (P := H)
  || apply fin_equiv_r with (P := H)); fin auto.

Tactic Notation "finite" "eq" uconstr(H) :=
   ( apply fin_equiv with (1 := H)
  || apply fin_equiv_r with (1 := H)); fin auto.

Tactic Notation "finite" "using" uconstr(H) :=
   ( apply fin_equiv with (2 := H)
  || apply fin_equiv_r with (2 := H)); fin auto.

Tactic Notation "finite" "dec" :=
  apply fin_dec; auto with finite_db.

Tactic Notation "finite" "dec" "left" :=
  apply fin_inter_dec_left; fin auto.

Tactic Notation "finite" "cst" "left" :=
  apply fin_inter_cst_lft; fin auto.

Tactic Notation "finite" "union" :=
  repeat apply fin_union; fin auto.

Tactic Notation "finite" "product" :=
  repeat apply fin_product; fin auto.

Section fin_compose.

  Variable (X Y : Type) (R : X → Y → Prop) (P : Y → Prop).

  (** A very useful lemma to compose finitary relations *)

  Lemma fin_compose :
             (∀y, P y → fin (λ x, R x y))
           → fin P
           → fin (λ x, ∃ y, R x y ∧ P y).
  Proof.
    intros H (lP & HP).
    finite as (fun x => exists y, R x y /\ In y lP).
    + intros x; split; intros (y & Hy); exists y; revert Hy; rewrite HP; auto.
    + cut (forall y, In y lP -> fin (fun x => R x y)).
      2: intros; apply H, HP; auto.
      clear P HP H.
      induction lP as [ | y lP IHlP ]; intros H.
      * exists nil; intros k; split.
        - intros (? & _ & []).
        - intros [].
      * destruct IHlP as (ll & Hll).
        - intros; apply H; simpl; auto.
        - destruct (H y) as (l & Hl); simpl; auto.
          exists (l++ll); intros x; rewrite in_app_iff, <- Hl, <- Hll.
          split.
          ++ intros (y' & H1 & [ <- | H2 ]); auto.
             right; exists y'; auto.
          ++ intros [ | (y' & ? & ?) ].
             ** exists y; auto.
             ** exists y'; auto.
  Qed.

End fin_compose.

Tactic Notation "finite" "compose" := apply fin_compose; fin auto.

#[global] Hint Resolve fin_compose : finite_db.

Fact fin_finite_union X Y (R : X → Y → Prop) : 
          finite X
        → (∀x, fin (R x))
        → fin (λ y, ∃x, R x y).
Proof.
  intros H1 H2.
  finite as (fun x => exists p, R p x /\ True); auto.
  intros; firstorder.
Qed.

#[global] Hint Resolve fin_finite_union : finite_db.

Section fin_dep_prod.

  Variables (X Y : Type) (P : X → Prop) (R : X → Y → Prop).

  Local Lemma fin_dep_prod_rec l :
          (∀x, x ∈ l → fin (R x))
        → fin (λ p, fst p ∈ l ∧ R (fst p) (snd p)).
  Proof.
    induction l as [ | x l IHl ]; intros Hl.
    + exists []; simpl; tauto.
    + destruct IHl as (m & Hm).
      1: intros; apply Hl; simpl; auto.
      destruct (Hl x (or_introl eq_refl)) as (k & Hk).
      exists (map (fun y => (x,y)) k++m).
      intros (x',y); simpl; rewrite in_app_iff, in_map_iff; split.
      * intros ([<- | H1] & H2).
        - apply Hk in H2; left; eauto.
        - right; apply Hm; auto.
      * intros [ (? & E & H) | H%Hm ].
        - inversion E; subst; split; auto; now apply Hk.
        - simpl in *; tauto.
  Qed.

  Theorem fin_dep_prod : fin P → (∀x, P x → fin (R x)) → fin (λ p, P (fst p) ∧ R (fst p) (snd p)).
  Proof.
    intros (l & Hl) HQ.
    finite as (fun p => In (fst p) l /\ R (fst p) (snd p)).
    + intros []; simpl; rewrite Hl; tauto.
    + apply fin_dep_prod_rec.
      intros ? ?%Hl; auto.
  Qed.

End fin_dep_prod.

Fact finite_dep_prod X Y (R : X → Y → Prop) : finite X → (∀x, fin (R x)) → fin (λ p, R (fst p) (snd p)).
Proof.
  intros H1 H2.
  finite as (fun p => True /\ R (fst p) (snd p)).
  1: intros []; simpl; tauto.
  apply fin_dep_prod with (P := fun _ => True); fin auto.
Qed.

Tactic Notation "finite" "dep" "prod" :=
  (apply finite_dep_prod || apply fin_dep_prod); fin auto.

Fact finite_idx n : finite (idx n).
Proof. exists (idx_list _); apply idx_list_In. Qed.

#[global] Hint Resolve finite_idx : finite_db.

Fact fin_idx_union X n (R : idx n → X → Prop) :
           (∀p, fin (R p)) → fin (λ x, ∃p, R p x).
Proof. fin auto. Qed.

#[global] Hint Resolve fin_idx_union : finite_db.

Fact fin_function_rel X (P : X → Prop) :
         { x | P x }
       → (∀ x y, P x → P y → x = y)
       → fin P.
Proof.
  intros (x & Hx) H.
  exists [x]; intros y; split.
  + intros H1; rewrite (H _ _ Hx H1); simpl; auto.
  + now intros [ <- | [] ].
Qed. 

Fact fin_nat_lt n : fin (λ j, j < n).
Proof.
  finite as (fun j => exists p : idx n, idx2nat p = j).
  intros j; split.
  + intros (? & <-); apply idx2nat_lt.
  + intros Hj; exists (nat2idx Hj); apply idx2nat2idx.
Qed.

Fact fin_nat_le n : fin (λ j, j <= n).
Proof.
  finite as (fun j => j < S n).
  + intro; lia.
  + apply fin_nat_lt.
Qed.

Fact fin_cst_dec X (P : Prop) : finite X → {P} + {~P} → fin (λ _ : X, P).
Proof. intros; finite dec. Qed.

#[global] Hint Resolve fin_nat_le fin_nat_lt fin_cst_dec : finite_db.

Fact fin_direct_image X Y (f : X → Y) P : fin P → fin (λ y, ∃x, f x = y ∧ P x).
Proof. fin auto. Qed.

(** For any n, there are finitely many pairs (a,b) st a+b = n *)
Fact fin_plus n : fin (λ p, fst p + snd p = n).
Proof.
  finite as (λ p, ∃i, (i,n-i) = p ∧ i <= n).
  intros p; split.
  + intros (i & <- & Hi); simpl; lia.
  + exists (fst p); destruct p; simpl in *.
    split; [ f_equal | ]; lia.
Qed.

#[global] Hint Resolve fin_plus : finite_db.

#[local] Hint Resolve lt_dec eq_nat_dec : core.

(** For any j, there are finitely many pairs (0<a,0<b) st a+b = j *)
Fact fin_plus_strict n : fin (λ p, 0 < fst p ∧ 0 < snd p ∧ fst p + snd p = n).
Proof. repeat finite dec left. Qed.

#[global] Hint Resolve fin_plus_strict : finite_db.

Section fin_list_sum.

  Variables (X : Type)
            (f : X → nat)
            (Hf : ∀x, 0 < f x)                     (* f is positive *)
            (n : nat)
            (Hn : ∀j, j < n → fin (λ x, f x = j)) (* only finitely many x st f x < n *)
            .

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
      finite compose.
      intros (a,b); simpl; intros (Ha & Hb & H).
      finite compose.
      apply fin_product with (P := fun l => list_sum f l = a)
                             (Q := fun l => list_sum f l = b).
      all: apply IHj; lia.
  Qed.

End fin_list_sum.

Section fin_idx_rel.

  Variable (n : nat) (X : Type) (R : idx n → X → Prop) (HR : ∀i, fin (R i)).

  Theorem fin_idx_rel : fin (λ v : vec X n, ∀i, R i v⦃i⦄).
  Proof.
    revert R HR.
    induction n as [ | m IHm ].
    + intros R _.
      finite as (eq ∅).
      intros v; split.
      * intros ? ?; idx invert all.
      * vec invert v; auto.
    + intros R HP.
      finite as (fun v => exists x, (exists w, x##w = v /\ forall p, R (idx_nxt p) (w⦃p⦄)) /\ R idx_fst x ).
      * intros v; split.
        - intros (y & (w & <- & H1) & H3); simpl in H1; intros p; idx invert p; auto.
        - vec invert v as x v; intros H; exists x; split.
          ++ exists v; split; auto; intros; apply (H (idx_nxt _)).
          ++ apply (H idx_fst).
      * do 2 (intros; finite compose).
        apply IHm with (R := fun p => R (idx_nxt p)); auto.
  Qed.

End fin_idx_rel.

#[global] Hint Resolve fin_idx_rel : finite_db.

Fact fin_vec_fall2 X Y (R : X → Y → Prop) n (v : vec X n) :
       (∀p, fin (R v⦃p⦄)) → fin (vec_fall2 R v).
Proof. intros H; apply fin_idx_rel with (1 := H). Qed.

#[global] Hint Resolve fin_vec_fall2 : finite_db.

Section fin_measure.

  Variable (X : Type) (m : X → nat) (n : nat) (Hn : ∀i, i < n → fin (λ x, m x = i)).

  Fact fin_measure_le i : i < n → fin (λ x, m x <= i).
  Proof.
    intros Hi.
    finite as (fun x => exists j, m x = j /\ j <= i).
    + intros x; split; eauto.
      intros (? & <- & ?); lia.
    + finite compose; intros; apply Hn; lia.
  Qed.

  Fact fin_measure_lt i : i < n → fin (λ x, m x < i).
  Proof.
    intros Hi.
    finite as (fun x => exists j, m x = j /\ j < i).
    + intros x; split; eauto.
      intros (? & <- & ?); lia.
    + finite compose; intros; apply Hn; lia.
  Qed.

End fin_measure.

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
