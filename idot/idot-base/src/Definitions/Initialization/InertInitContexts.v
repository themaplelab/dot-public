(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.

(** * Inertness for Initialization *)
(** Allocated Literals and objects must be either free or committed. *)
Definition inert_inits Delta :=
  forall x init, binds x init Delta ->
            init = free \/ init = committed.

(** *** Simple Lemmas for Initialization Inertness *)
Lemma inert_inits_empty : inert_inits empty.
Proof.
  unfold inert_inits; intros;
    exfalso; eauto using binds_empty_inv.
Qed.
Hint Resolve inert_inits_empty : core.

Lemma inert_inits_push : forall Delta x i,
    inert_inits Delta ->
    x # Delta ->
    i = free \/ i = committed ->
    inert_inits (Delta & x ~ i).
Proof.
  unfold inert_inits; introv Hii Hfr Hi Hbi.
  apply binds_push_inv in Hbi;
    destruct Hbi as [[Heq Heq'] | [Hneq Hbi]]; subst; eauto.
Qed.
Hint Resolve inert_inits_push : core.
