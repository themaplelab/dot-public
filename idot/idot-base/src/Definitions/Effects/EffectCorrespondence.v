(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Effects.

(** * Effect Correspondence *)
(** Effect Correspondence relates an effect context [ℰ] to an effect set [E].
    [eff_ctx_corr_one ℰ E] says that performing all the [E] will perform all the
    effects that are mapped to in [ℰ], i.e. [ { (x,a) | (x,a) ∈ ℰ(x) } ⊂ E ]. *)
Definition eff_ctx_corr_one (ℰ : eff_ctx) effs :=
  (forall x effs', binds x effs' ℰ ->
                   forall eff, (eff \in (from_list effs')) ->
                               (eff \in (from_list effs))).

Lemma eff_ctx_corr_one_empty : forall effs,
    eff_ctx_corr_one empty effs.
Proof.
  unfold eff_ctx_corr_one; intros; exfalso.
  eauto using binds_empty_inv.
Qed.

(** * Effects correspondence for Effect Context Stacks *)
(** We lift the [eff_ctx_corr_one] relation to stacks of Effect Contexts [ℰs] and [Es].
    This relation will be used to specify one of the invariants required for
    preservation. *)
Inductive eff_ctx_corr : list eff_ctx -> list effects -> Prop :=
(** [ ε ∼ ε ] *)
| eff_ctx_corr_nil : eff_ctx_corr nil nil
(** [ { (x,a) | (x,a) ∈ ℰ(x) } ⊂ E ]  #<br>#
    [ ℰs ∼ Es ]  #<br>#
    [――――――――]  #<br>#
    [ ℰ :: ℰs ∼ E :: Es ] *)
| eff_ctx_corr_cons : forall ℰ ℰs effs effss,
    eff_ctx_corr ℰs effss ->
    eff_ctx_corr_one ℰ effs ->
    eff_ctx_corr (ℰ :: ℰs) (effs :: effss).
