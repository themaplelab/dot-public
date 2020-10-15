(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Effects Initialization InitLookup.
Require Import VarsSubst.

Implicit Type (i : init_typ).

Local Hint Constructors init_var init_sub : core.

(** * Strengthening Lemmas for Initialization Lookup *)
(** This module contains strengethening lemmas for initialization lookup. *)

Lemma init_var_strengthen_vars_commit : forall Delta vs x y i,
    init_var Delta (vs \u \{ x}) y i ->
    binds x committed Delta ->
    init_var Delta vs y i.
Proof.
  intros * Hinit Hbi.
  assert (~ binds y committed Delta ->
          y \in (vs \u \{ x}) ->
                y \in vs) as Hvs.
  { rewrite in_union. rewrite in_singleton.
    intros Hnbi [? | ?]; subst; auto.
    exfalso; apply Hnbi; auto. }
  induction Hinit; eauto.
  - apply init_var_free; auto.
    apply Hvs; auto; intro; binds_eq.
  - apply init_var_unspec; auto.
    apply Hvs; auto; intro; binds_eq.
Qed.

Lemma init_var_strengthen_vars_commit_remove : forall Delta vs x y i,
    init_var Delta vs y i ->
    binds x committed Delta ->
    init_var Delta (vs \- \{x}) y i.
Proof.
  intros * Hinit Hbi.
  assert (~ binds y committed Delta ->
          y \in vs ->
                y \in (vs \- \{ x})) as Hvs.
  { rewrite in_remove.
    unfold notin. rewrite in_singleton.
    intros; split; auto.
    intro; subst; auto. }
  induction Hinit; eauto.
  - apply init_var_free; auto.
    apply Hvs; auto; intro; binds_eq.
  - apply init_var_unspec; auto.
    apply Hvs; auto; intro; binds_eq.
Qed.

Lemma init_var_strengthen_D_push : forall Delta vs y x i' i,
    init_var (Delta & y ~ i') vs x i ->
    x <> y ->
    init_var Delta vs x i.
Proof.
  intros * Hin Hneq.
  remember (Delta & y ~ i') as Delta' eqn:HeqD.
  induction Hin; subst;
    try match goal with
        | [ Hb:  binds ?x1 ?i1 (?D & ?x2 ~ ?i2),
                 Hn : ?x1 <> ?x2 |- _ ] =>
          apply (binds_push_neq_inv Hb) in Hn
        end; eauto.
Qed.

Lemma init_var_change_vs : forall Delta vs x i vs',
    init_var Delta vs x i ->
    x \in vs' ->
    init_var Delta vs' x i.
Proof.
  induction 1; eauto.
Qed.

Lemma init_var_strengthen_D : forall Delta1 Delta2 vs x i,
    init_var (Delta1 & Delta2) vs x i ->
    x # Delta2 ->
    init_var Delta1 vs x i.
Proof.
  induction Delta2 as [| Delta2 y v IHDelta2] using env_ind;
    intros vs x i Hiv Hni.
  - rewrite concat_empty_r in *; auto.
  - eapply IHDelta2; auto.
    rewrite concat_assoc in Hiv.
    eapply init_var_strengthen_D_push; eauto.
    simpl_dom; auto.
Qed.

Lemma init_var_subtyp : forall Delta1 Delta2 x vs i i',
    x # Delta2 ->
    init_var (Delta1 & x ~ i & Delta2) vs x i' ->
    forall y vs Delta, init_var Delta vs y i ->
              init_var Delta vs y i'.
Proof.
  intros * Hfr Hinit.
  apply init_var_strengthen_D in Hinit; auto.
  remember (Delta1 & x ~ i) as Delta' eqn:HeqD.
  induction Hinit; subst; eauto;
    match goal with
    | [ Hb:  binds ?x1 ?i1 (?D & ?x2 ~ ?i2) |- _ ] =>
      pose proof (binds_push_eq_inv Hb); subst i2
    end;
    inversion 1; subst; auto.
Qed.

Lemma init_var_remove_middle : forall Delta1 Delta2 vs x z i i',
  init_var (Delta1 & x ~ i' & Delta2) vs z i ->
  z <> x ->
  init_var (Delta1 & Delta2) (vs \- \{ x}) z i.
Proof.
  intros *.
  remember (Delta1 & x ~ i' & Delta2) as D eqn:HeqD.
  induction 1; intro; subst;
    eauto using binds_middle_neq_binds, in_remove_singleton_left.
Qed.
