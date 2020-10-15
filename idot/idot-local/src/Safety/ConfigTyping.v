Set Implicit Arguments.

Require Import LibExtra DotTactics List.
Require Import
        AbstractSyntax Typing GeneralTyping
        RecordAndInertTypes
        OperationalSemantics HeapCorrespondence.
Require Import Effects InitVar InitTyping HeapCommit HeapItemFree
        SubHeapFree InitCorrespondence StackTyping.


Inductive ty_config :
  ctx -> init_ctx -> list eff_ctx -> list effects -> config -> typ -> Prop :=
| ty_config_c : forall Gamma Delta Sigma ℰ ℰs s t T i U effs' effs effss,
    inert Gamma ->
    inert_inits Delta ->
    heap_correspond Gamma Sigma ->
    free_sub_heaps Gamma Delta Sigma (ℰ :: ℰs) ->
    ty_stack Gamma Delta (ℰ :: ℰs) s T i (effs :: effss)%list U ->
    Gamma ⊢ t ∶ T ->
    ⊢e t ∶ effs' ->
    Gamma ⸴ Delta ⸴ (dom ℰ) ⊢i t ∶ i ->
    eff_ctx_corr (ℰ :: ℰs) ((effs' ++ effs) :: effss)%list ->
    ty_config Gamma Delta (ℰ :: ℰs) ((effs' ++ effs) :: effss)%list (t; s; Sigma) U.

Hint Constructors ty_config : core.

Lemma initial_config_typed : forall t T,
    empty ⊢ t ∶ T ->
    empty ⸴ empty ⸴ \{} ⊢i t ∶ committed ->
    ty_config empty empty (empty :: nil) (nil :: nil) (t; nil; empty) T.
Proof.
  intros.
  eassert ((nil :: nil)%list =
           ((nil ++ nil) :: nil)%list) by (erewrite app_nil_l; eauto).
  rewrite H1. econstructor; eauto.
  - econstructor; simpl.
    + unfold all_notin.
      simpl_dom; intros; exfalso; eauto using in_empty_inv.
    + unfold free_sub_heap.
      intros; exfalso; eauto using binds_empty_inv.
    + hnf. introv Hcontra. rewrite dom_empty, in_empty in *. destruct Hcontra.
    + constructor.
      * unfold well_committed_heap.
        simpl_dom; repeat_split_right; auto.
        intros; exfalso; eauto using binds_empty_inv.
      * hnf. repeat split; repeat(rewrite dom_empty); auto.
        introv Hcontra. apply binds_to_dom in Hcontra.
        rewrite dom_empty, in_empty in *. destruct Hcontra.
  - simpl_dom; eauto.
  - constructor; eauto.
    + constructor.
    + eauto using eff_ctx_corr_one_empty.
Qed.
