(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Effects Initialization InitLookup.

(** This module collects some inversion lemmas for looking up the initialization
    of a variable. *)

Implicit Type (i : init_typ).

Local Hint Constructors init_var init_sub : core.

Lemma init_var_typing_implies_bound : forall Delta vs x i,
    init_var Delta vs x i ->
    exists i', binds x i' Delta.
Proof.
  intros. induction H; subst; eauto.
Qed.

Lemma init_var_typing_implies_bound_sub : forall Delta vs x i,
    init_var Delta vs x i ->
    exists i', init_sub i' i /\ binds x i' Delta.
Proof.
  intros * Hiv.
  induction Hiv; eauto.
  destruct IHHiv as [i1 [?H ?H]]; exists i1; split; auto.
  eauto using init_sub_trans.
Qed.

Lemma init_var_binds_sub : forall Delta vs x i i',
    init_var Delta vs x i ->
    binds x i' Delta ->
    init_sub i' i.
Proof.
  induction 1; intro; try binds_eq; auto.
  specialize (IHinit_var H1).
  induction H0; auto.
  - remember committed as i; induction IHinit_var; subst; auto.
  - remember free as i; induction IHinit_var; subst; auto.
Qed.

Lemma init_var_empty_cases : forall Delta x i,
    init_var Delta \{} x i ->
    i = committed \/ i = unspecified.
Proof.
  remember \{} as vs eqn:HeqV.
  induction 1; subst;
    try solve [exfalso; eauto using in_empty_inv].
  - auto.
  - induction H0; firstorder.
Qed.

Lemma init_var_binds_committed_or_in_vs : forall Delta x vs i,
    init_var Delta vs x i ->
    binds x committed Delta \/ x \in vs.
Proof.
  induction 1; auto.
Qed.

Lemma init_var_binds_committed_or_in_vs_bound : forall Delta x vs i,
    init_var Delta vs x i ->
    binds x committed Delta \/ x \in vs /\ exists i, binds x i Delta.
Proof.
  induction 1; eauto.
Qed.

Lemma init_var_empty_binds : forall Delta x i,
    init_var Delta \{} x i ->
    binds x committed Delta.
Proof.
  remember \{} as vs eqn:HeqV.
  induction 1; subst;
    auto; try solve [exfalso; eauto using in_empty_inv].
Qed.

Lemma init_sub_committed : forall i,
    init_sub i committed ->
    i = committed.
Proof.
  remember committed as i;
    induction 1; congruence.
Qed.

Lemma init_var_committed_binds : forall Delta vs x,
    init_var Delta vs x committed ->
    binds x committed Delta.
Proof.
  remember committed as i; induction 1; subst; auto.
  apply init_sub_committed in H0. subst; auto.
Qed.

Lemma init_sub_free : forall i,
    init_sub i free ->
    i = free.
Proof.
  remember free as i;
    induction 1; congruence.
Qed.

Lemma init_var_free_inv : forall Delta vs x,
    init_var Delta vs x free ->
    x \in vs /\ binds x free Delta.
Proof.
  intros * Hi. remember free as i eqn:HeqI.
  induction Hi; try congruence; subst; auto.
  apply init_sub_free in H; subst; auto.
Qed.

Lemma init_var_unspec_middle : forall Delta1 Delta2 vs x i,
    x # Delta2 ->
    init_var (Delta1 & x ~ unspecified & Delta2) vs x i ->
    x \in vs.
Proof.
  intros * Hfr Hlkup.
  remember (Delta1 & x ~ unspecified & Delta2) as Delta' eqn:HeqD.
  induction Hlkup; subst; auto.
  pose proof (binds_middle_eq_fresh_inv H Hfr); congruence.
Qed.
