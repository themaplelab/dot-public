(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Effects.

Implicit Types (Delta : init_ctx) (Sigma : heap) (ℰ : eff_ctx).

(** * Well-pointed *)
(* Objects in a free subheap are only allowed to point to committed parts of the
   heap, or to objects in the same subheap.
   [well_pointed Delta ℰ x] says that [x] is either committed or part of the subheap
   represented by the effect context [ℰ]. *)
Notation well_pointed Delta ℰ x :=
  ((binds x committed Delta) \/ (x \in dom ℰ /\ binds x free Delta)).

(** *** Simple Lemmas about Well-pointed *)
Lemma well_pointed_weaken_inits_middle : forall Delta1 Delta2 ℰ x y i,
    well_pointed (Delta1 & Delta2) ℰ x ->
    y # Delta1 ->
    well_pointed (Delta1 & y ~ i & Delta2) ℰ x.
Proof.
  intros; destruct_all; eauto using binds_push_fresh_middle.
Qed.

Lemma well_pointed_weaken_effs_middle : forall Delta ℰ1 ℰ2 x y effs,
    well_pointed Delta (ℰ1 & ℰ2) x ->
    y # ℰ1 ->
    well_pointed Delta (ℰ1 & y ~ effs & ℰ2) x.
Proof.
  intros; simpl_dom; rewrite ? in_union in *;
    destruct_all; eauto using binds_push_fresh_middle.
Qed.
