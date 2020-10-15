(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Effects Initialization InitLookup.

Implicit Type (i : init_typ).

Local Hint Constructors init_var init_sub : core.

(** * Weakening Lemmas for Initialization Lookup *)
(** This module contains weakening lemmas for initialization lookup. *)

Lemma init_var_weaken_vars : forall Delta vs x i vs',
    init_var Delta vs x i ->
    init_var Delta (vs \u vs') x i.
Proof.
  intros. assert (forall x, x \in vs -> x \in vs \u vs').
  { intros; rewrite in_union; auto. }
  induction H; subst; eauto.
Qed.

Lemma init_var_weaken_vars_in : forall Delta vs1 vs2 x i,
    init_var Delta vs1 x i ->
    (x \in vs1 -> x \in vs2) ->
    init_var Delta vs2 x i.
Proof.
  induction 1; subst; eauto.
Qed.

Lemma init_var_weaken_D : forall Delta1 Delta2 vs x i,
    init_var Delta1 vs x i ->
    (forall init, binds x init Delta1 -> binds x init Delta2) ->
    init_var Delta2 vs x i.
Proof.
  induction 1; subst; eauto.
Qed.

Lemma init_var_weaken_D_fresh : forall Delta1 Delta2 vs x i,
    init_var Delta1 vs x i ->
    x # Delta2 ->
    init_var (Delta1 & Delta2) vs x i.
Proof.
  intros; eapply init_var_weaken_D; eauto.
Qed.

Lemma init_var_weaken_D_push : forall Delta vs x y i i',
    init_var Delta vs x i ->
    x <> y ->
    init_var (Delta & y ~ i') vs x i.
Proof.
  induction 1; subst; eauto.
Qed.
