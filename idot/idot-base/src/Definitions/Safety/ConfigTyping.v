Set Implicit Arguments.

Require Import LibExtra DotTactics List.
Require Import
        AbstractSyntax Typing GeneralTyping
        RecordTypes InertTypes DefRecordInertTyping
        HeapCorrespondence.
Require Import Effects.
Require Import HeapDefsPointsTo WellPointed.
Require Import FreeItems.
Require Import Initialization InitTyping CommittedSubHeap.
Require Import FreeSubHeapSingle.
Require Import EffectCorrespondence FreeSubHeapStack StackTyping InertInitContexts.


(** * Configuration Typing *)
(** Configuration is a list of properties that are satisfied by an empty
    configuration of a well-typed program and that continue to hold as the
    prgram executes.
    We denote [ty_config Gamma Delta ℰs Es (t; s; Sigma) U] as
    [Gamma; Delta; ℰs ⊢ (t; s; Sigma) : (Es, U)].
 *)
Inductive ty_config :
  ctx -> init_ctx -> list eff_ctx -> list effects -> config -> typ -> Prop :=
(** [Gamma inert]  #<br>#
    [Delta inert initialization context]  #<br>#
    [Gamma ∼ Sigma]  #<br>#
    [free_sub_heaps Gamma Delta Sigma (ℰ :: ℰs)]  #<br>#
    [Gamma; Delta; (ℰ :: ℰs) ⊢ Fs : (T, i) => (E :: Es, U)]  #<br>#
    [Gamma ⊢ t : T]  #<br>#
    [⊢e t : E']  #<br>#
    [Gamma; Delta | (dom ℰ) ^ free ⊢i t : i]  #<br>#
    [(ℰ :: ℰs) ∼ ((E' ∪ E) :: Es)]  #<br>#
    [――――――――]  #<br>#
    [Gamma; Delta; (ℰ :: ℰs) ⊢ (t; Fs; Sigma) : (((E' ∪ E) :: Es), U)]  *)
| ty_config_c : forall Gamma Delta Sigma ℰ ℰs Fs t T i U effs' effs effss,
    inert Gamma ->
    inert_inits Delta ->
    heap_correspond Gamma Sigma ->
    free_sub_heaps Gamma Delta Sigma (ℰ :: ℰs) ->
    ty_stack Gamma Delta (ℰ :: ℰs) Fs T i (effs :: effss)%list U ->
    Gamma ⊢ t ∶ T ->
    ⊢e t ∶ effs' ->
    Gamma ⸴ Delta ⸴ (dom ℰ) ⊢i t ∶ i ->
    eff_ctx_corr (ℰ :: ℰs) ((effs' ++ effs) :: effss)%list ->
    ty_config Gamma Delta (ℰ :: ℰs) ((effs' ++ effs) :: effss)%list (t; Fs; Sigma) U.

Hint Constructors ty_config : core.

(** Initial configuration is well-typed *)
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
    + econstructor. unfold well_committed_heap.
      simpl_dom; repeat_split_right; auto.
      intros; exfalso; eauto using binds_empty_inv.
  - simpl_dom; eauto.
  - constructor; eauto.
    + constructor.
    + eauto using eff_ctx_corr_one_empty.
Qed.
