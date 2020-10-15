(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Effects HeapEffects.
Require Import HeapDefsPointsTo WellPointed.
Require Import FreeItems.

Implicit Types (Delta : init_ctx) (Sigma : heap) (ℰ : eff_ctx).

Local Hint Resolve
      well_pointed_weaken_inits_middle
      well_pointed_weaken_effs_middle : core.

(** ** Lemmas about Free Heap Items *)
(** Lemmas about domains of Effect Contexts *)
Section Domains.
  (** [heap_defs Delta ℰ y T hds] implies [y] is in [dom ℰ] *)
  Lemma free_heap_defs_in_effs : forall Delta ℰ y hds,
    free_heap_defs Delta ℰ y hds ->
    y \in dom ℰ.
  Proof.
    unfold free_heap_defs. introv [HbiD [HbiE _]].
    eauto using binds_to_dom.
  Qed.

  Lemma free_heap_defs_in_inits : forall Delta ℰ y hds,
      free_heap_defs Delta ℰ y hds ->
      y \in dom Delta.
  Proof.
    unfold free_heap_defs. introv [HbiD [HbiE _]].
    eauto using binds_to_dom.
  Qed.

  Hint Resolve free_heap_defs_in_effs free_heap_defs_in_inits : core.

  (** [heap_defs Delta ℰ y T itm] implies [y] is in [dom ℰ] *)
  Lemma free_heap_item_in_effs : forall Delta ℰ y hds,
      free_heap_defs Delta ℰ y hds ->
      y \in dom ℰ.
  Proof. inversion 1; eauto. Qed.

  Lemma free_heap_item_in_inits : forall Delta ℰ y hds,
      free_heap_item Delta ℰ y hds ->
      y \in dom Delta.
  Proof. inversion 1; eauto. Qed.
End Domains.

(** *** Weakening Lemmas for Free Heaps Definitions *)
Local Hint Resolve binds_push_fresh_middle : core.

Lemma free_heap_defs_weaken_inits_middle : forall Delta1 Delta2 ℰ x hds y i',
    free_heap_defs (Delta1 & Delta2) ℰ x hds ->
    y # Delta1 ->
    free_heap_defs (Delta1 & y ~ i' & Delta2) ℰ x hds.
Proof.
  unfold free_heap_defs; introv [HbiD [HbiE Hcases]] Hfr.
  repeat_split_right; auto.
Qed.
Local Hint Resolve free_heap_defs_weaken_inits_middle : core.

Lemma free_heap_defs_weaken_inits : forall Delta ℰ x hds y i',
    free_heap_defs Delta ℰ x hds ->
    y # Delta ->
    free_heap_defs (Delta & y ~ i') ℰ x hds.
Proof.
  introv Hfhds Hfr.
  rewrite <- (concat_empty_r Delta) in Hfhds.
  rewrite <- (concat_empty_r (Delta & _)).
  eauto.
Qed.
Local Hint Resolve free_heap_defs_weaken_inits : core.

Lemma free_heap_defs_weaken_effs_middle : forall Delta ℰ1 ℰ2 x hds y effs,
    free_heap_defs Delta (ℰ1 & ℰ2) x hds ->
    y # ℰ1 ->
    free_heap_defs Delta (ℰ1 & y ~ effs & ℰ2) x hds.
Proof.
  unfold free_heap_defs; introv [HbiD [HbiE Hcases]] Hfr.
  repeat_split_right; auto.
Qed.
Local Hint Resolve free_heap_defs_weaken_effs_middle : core.

Lemma free_heap_defs_weaken_effs : forall Delta ℰ x hds y effs,
    free_heap_defs Delta ℰ x hds ->
    y # ℰ ->
    free_heap_defs Delta (ℰ & y ~ effs) x hds.
Proof.
  introv Hfhds Hfr.
  rewrite <- (concat_empty_r ℰ) in Hfhds.
  rewrite <- (concat_empty_r (ℰ & _)).
  eauto.
Qed.
Local Hint Resolve free_heap_defs_weaken_effs : core.

Lemma free_heap_defs_push_obj : forall Delta ℰ x ds,
    x # Delta ->
    x # ℰ ->
    free_heap_defs (Delta & x ~ free)
                   (ℰ & x ~ (heap_defs_effs x (heap_defs_of_defs ds)))
                   x
                   (heap_defs_of_defs ds).
Proof.
  introv HfrD HfrE. unfold free_heap_defs; repeat_split_right; auto.
  introv Hpt.
  rewrite heap_defs_of_defs_points_to_empty, in_empty in Hpt.
  destruct Hpt.
Qed.
Local Hint Resolve free_heap_defs_push_obj : core.

Lemma free_heap_defs_first_obj : forall Delta x ds,
    x # Delta ->
    free_heap_defs (Delta & x ~ free)
                   (x ~ (heap_defs_effs x (heap_defs_of_defs ds)))
                   x
                   (heap_defs_of_defs ds).
Proof.
  intros. rewrite <- (concat_empty_l (x ~ (heap_defs_effs _ _))).
  eauto.
Qed.
Local Hint Resolve free_heap_defs_first_obj : core.

(** *** Weakening Lemmas for Free Heap Items *)
Local Ltac defs_to_item := inversion 1; subst; eauto.

Lemma free_heap_item_weaken_inits_middle : forall Delta1 Delta2 ℰ x hds y i',
    free_heap_item (Delta1 & Delta2) ℰ x hds ->
    y # Delta1 ->
    free_heap_item (Delta1 & y ~ i' & Delta2) ℰ x hds.
Proof. defs_to_item. Qed.

Lemma free_heap_item_weaken_inits : forall Delta ℰ x hds y i',
    free_heap_item Delta ℰ x hds ->
    y # Delta ->
    free_heap_item (Delta & y ~ i') ℰ x hds.
Proof. defs_to_item. Qed.

Lemma free_heap_item_weaken_effs_middle : forall Delta ℰ1 ℰ2 x hds y effs,
    free_heap_item Delta (ℰ1 & ℰ2) x hds ->
    y # ℰ1 ->
    free_heap_item Delta (ℰ1 & y ~ effs & ℰ2) x hds.
Proof. defs_to_item. Qed.

Lemma free_heap_item_weaken_effs : forall Delta ℰ x hds y effs,
    free_heap_item Delta ℰ x hds ->
    y # ℰ ->
    free_heap_item Delta (ℰ & y ~ effs) x hds.
Proof. defs_to_item. Qed.

Lemma free_heap_item_push_obj : forall Delta ℰ x T ds,
    x # Delta ->
    x # ℰ ->
    free_heap_item (Delta & x ~ free)
                   (ℰ & x ~ (heap_defs_effs x (heap_defs_of_defs ds)))
                   x
                   (item_obj T (heap_defs_of_defs ds)).
Proof. eauto. Qed.

Lemma free_heap_item_first_obj : forall Delta x T ds,
    x # Delta ->
    free_heap_item (Delta & x ~ free)
                   (x ~ (heap_defs_effs x (heap_defs_of_defs ds)))
                   x
                   (item_obj T (heap_defs_of_defs ds)).
Proof. eauto. Qed.
