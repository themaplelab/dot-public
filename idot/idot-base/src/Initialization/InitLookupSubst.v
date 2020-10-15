(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Effects Initialization InitLookup.
Require Import InitLookupBinds VarsSubst.
Require Import InitLookupRestrict InitLookupStrengthen.

Implicit Type (i : init_typ).

Local Hint Constructors init_var init_sub : core.

(** * Substitution Lemmas for Initialization Lookup *)
(** This module contains substitution lemmas for initialization lookup. *)

Lemma init_var_substitution_neq_middle : forall Delta1 x i' Delta2 vs z i,
    init_var (Delta1 & x ~ i' & Delta2) vs z i ->
    z <> x ->
    init_var (Delta1 & Delta2) vs z i.
Proof.
  introv. remember (Delta1 & x ~ i' & Delta2) as Delta' eqn:HeqD.
  induction 1; subst; intros;
    try match goal with
        | [ H : binds ?z ?i (Delta1 & x ~ i' & Delta2), H1 : ?z <> x |- _ ] =>
          pose proof (binds_subst H H1)
        end; eauto.
Qed.

Corollary init_var_substitution_fresh : forall Delta1 x i' Delta2 vs z y i,
    init_var (Delta1 & x ~ i' & Delta2) (vs \u \{ x}) z i ->
    x # Delta2 ->
    init_var (Delta1 & Delta2) vs y i' ->
    init_var (Delta1 & Delta2) vs (z \[ x -> y]) i.
Proof.
  intros. remember (Delta1 & x ~ i' & Delta2) as Delta' eqn:HeqD.
  cases_if; auto.
  - induction H; subst; eauto;
      binds_middle_subst; eauto;
        inversion H1; auto.
  - remember (vs \u \{ x}) as vs' eqn:HeqV.
    induction H; subst;
      repeat match goal with
             | [ H : ?z \in ?vs \u ?vs' |- _ ] =>
               rewrite ? in_union, ? in_singleton in H; destruct H;
                 try congruence
             end; eauto 3 using binds_subst.
Qed.


Lemma init_var_substitution_middle' : forall Delta1 x i' Delta2 vs z y i,
    init_var (Delta1 & x ~ i' & Delta2) vs z i -> x # Delta2 ->
    init_var (Delta1 & Delta2) (If x \in vs then (vs \- \{x}) \u \{y} else vs) y i' ->
    init_var (Delta1 & Delta2) (If x \in vs then (vs \- \{x}) \u \{y} else vs)
             (z \[ x -> y]) i.
Proof.
  intros. repeat cases_if; auto.
  - remember (Delta1 & x ~ i' & Delta2) as Delta' eqn:HeqD.
    induction H; subst;
      try binds_middle_subst; eauto;
        inversion H1; auto.
  - assert (y \in (vs \- \{ x} \u \{ y})) by (apply is_in_union_singleton_l).
    pose proof (init_var_typing_implies_bound H) as [?i ?H].
    assert (z \in vs -> z \in vs \- \{x} \u \{y}).
    { intros. rewrite in_union, in_remove, notin_singleton; auto. }
    assert (z # (x ~ i')) by auto.
    pose proof (binds_not_middle_inv H3 H5).
    remember (Delta1 & x ~ i' & Delta2) as Delta' eqn:HeqD.
    induction H; subst; try binds_eq;
      destruct H6 as [? | [? ?]]; eauto.
  - remember (Delta1 & x ~ i' & Delta2) as Delta' eqn:HeqD.
    induction H; subst; try congruence; eauto 3.
    + binds_middle_subst; auto.
  - assert (z # (x ~ i')) by auto.
    pose proof (init_var_typing_implies_bound H) as [?i ?H].
    pose proof (binds_not_middle_inv H3 H2).
    remember (Delta1 & x ~ i' & Delta2) as Delta' eqn:HeqD.
    induction H; subst; try binds_eq; destruct H4 as [? | [? ?]]; eauto.
Qed.

Lemma init_var_substitution_middle_subst :
  forall Delta1 x i' Delta2 vs z y i,
    init_var (Delta1 & x ~ i' & Delta2) vs z i -> x # Delta2 ->
    (forall vs, init_var (Delta1 & x ~ i' & Delta2) vs x i' -> init_var (Delta1 & Delta2) (vs /[x -> y]) y i') ->
    init_var (Delta1 & Delta2) (vs /[x -> y]) (z \[ x -> y]) i.
Proof.
  unfold subst_var, VarsSubstVar.
  intros. cases_if.
  - pose proof (H1 _ (init_var_middle_init_var Delta1 i' H0 C)).
    clear H1. repeat cases_if.
    + apply (init_var_subtyp H0 H H2).
    + remember (Delta1 & x ~ i' & Delta2) as Delta' eqn:HeqD.
      induction H; subst;
        eauto using binds_middle_neq_binds.
      * apply init_var_free;
          eauto using binds_middle_neq_binds.
        rewrite in_union, in_remove, notin_singleton;
          left; auto.
      * apply init_var_unspec;
          eauto using binds_middle_neq_binds.
        rewrite in_union, in_remove, notin_singleton;
          left; auto.
  - remember (Delta1 & x ~ i' & Delta2) as Delta' eqn:HeqD.
    induction H; subst; eauto.
    + apply init_var_commit;
        cases_if; try binds_middle_subst;
          eauto using binds_middle_neq_binds.
      apply (init_var_commit vs) in H.
      apply H1 in H; cases_if.
      remember (Delta1 & Delta2) as Delta' eqn:HeqD.
      remember committed as i' eqn:HeqI.
      induction H; subst; try congruence; eauto.
      inversions H2; eauto.
    + apply init_var_free;
        cases_if; try binds_middle_subst;
          eauto using binds_middle_neq_binds.
    + apply init_var_unspec;
        cases_if; try binds_middle_subst;
          eauto using binds_middle_neq_binds.
Qed.

Lemma init_var_substitution_middle_empty : forall Delta1 x Delta2 i i' y z,
    init_var (Delta1 & x ~ i & Delta2) \{} z i' ->
    x # (Delta1 & Delta2) ->
    init_var (Delta1 & Delta2) \{} y i ->
    init_var (Delta1 & Delta2) \{} (z \[ x -> y] ) i'.
Proof.
  intros.
  pose proof (init_var_empty_cases H1) as Hi.
  pose proof (init_var_empty_cases H) as Hi'.
  cases_if.
  - apply init_var_empty_binds in H1.
    destruct Hi' as [? | ?]; subst; eauto.
  - apply init_var_empty_binds in H.
    apply binds_middle_neq_binds in H; [|auto].
    destruct Hi' as [? | ?]; subst; eauto.
Qed.

Lemma init_var_substitution_middle_committed_empty :
  forall Delta1 x Delta2 i y z,
    init_var (Delta1 & x ~ committed & Delta2) \{} z i ->
    x # (Delta1 & Delta2) ->
    init_var (Delta1 & Delta2) \{} y committed ->
    init_var (Delta1 & Delta2) \{} (z \[ x -> y] ) i.
Proof.
  eauto using init_var_substitution_middle_empty.
Qed.

Lemma init_var_substitution_middle_remove :
  forall Delta1 x Delta2 vs i i' y z,
    init_var (Delta1 & x ~ i' & Delta2) vs z i ->
    x # (Delta1 & Delta2) ->
    init_var (Delta1 & Delta2) (vs \- \{x}) y i' ->
    init_var (Delta1 & Delta2) (vs \- \{x}) (z \[ x -> y] ) i.
Proof.
  intros. cases_if.
  - rewrite dom_concat, notin_union in H0. destruct H0.
    assert (Hx: binds x i' (Delta1 & x ~ i' & Delta2)) by auto.
    pose proof (init_var_binds_sub H Hx) as Hsub.
    induction Hsub; auto.
    + eapply init_var_sub; eauto.
    + eapply init_var_sub; eauto.
  - assert (z \in vs -> z \in (vs \- \{ x})).
    { intros. rewrite in_remove, notin_singleton; auto. }
    remember (Delta1 & x ~ i' & Delta2) as Delta' eqn:HeqD.
    induction H; subst;
      eauto using binds_middle_neq_binds; congruence.
Qed.

Lemma init_var_substitution_middle_empty_remove :
  forall Delta1 x Delta2 vs i i' y z,
    init_var (Delta1 & x ~ i' & Delta2) vs z i ->
    x # (Delta1 & Delta2) ->
    init_var (Delta1 & Delta2) \{} y i' ->
    init_var (Delta1 & Delta2) (vs \- \{x}) (z \[ x -> y] ) i.
Proof.
  intros.
  pose proof (init_var_empty_cases H1).
  cases_if.
  - assert (Hsub: binds x i' (Delta1 & x ~ i' & Delta2)) by auto.
    apply (init_var_binds_sub H) in Hsub.
    destruct H2 as [? | ?]; subst.
    + apply init_var_sub with (i' := committed); auto.
      pose proof (init_var_empty_binds H1); eauto.
    + apply init_var_sub with (i' := unspecified); auto.
      pose proof (init_var_empty_binds H1); eauto.
  - eauto using init_var_remove_middle.
Qed.

Lemma init_var_substitution_middle_committed_remove : forall Delta1 x Delta2 vs i y z,
    init_var (Delta1 & x ~ committed & Delta2) vs z i ->
    x # (Delta1 & Delta2) ->
    init_var (Delta1 & Delta2) \{} y committed ->
    init_var (Delta1 & Delta2) (vs \- \{x}) (z \[ x -> y] ) i.
Proof.
  eauto using init_var_substitution_middle_empty_remove.
Qed.

Section SubstCond.
  Lemma init_var_subst_cond : forall Delta1 Delta2 x y vs i,
    x # Delta2 ->
    init_var (Delta1 & Delta2) vs y i ->
    (forall vs : vars,
        init_var (Delta1 & x ~ i & Delta2) vs x i ->
        init_var (Delta1 & Delta2) (vs /[ x -> y]) y i).
  Proof.
    intros * Hfr Hinit.
    remember (Delta1 & Delta2) as D eqn:HeqD.
    induction Hinit; subst; eauto 3.
    - remember (Delta1 & x ~ free & Delta2) as D eqn:HeqD.
      remember free as i eqn:HeqI.
      induction 1; subst; eauto using vars_subst_in1.
      apply init_sub_free in H2; subst.
      firstorder.
    - intros.
      pose proof (init_var_unspec_middle Hfr H1).
      apply vars_subst_in1 with (y:=x0) in H2.
      eauto.
    - intros.
      pose proof (init_var_binds_committed_or_in_vs H0) as Hcases.
      destruct Hcases.
      + apply binds_middle_eq_fresh_inv in H1; auto; subst.
        apply init_sub_committed in H; subst.
        apply init_var_committed_binds in Hinit; auto.
      + apply vars_subst_in1 with (y:=x0) in H1.
        apply init_var_sub with (i':=i'); auto.
        eauto using init_var_change_vs.
  Qed.

  (** For let bindings *)
  Lemma init_var_subst_cond_push : forall Delta x y vs i,
    init_var Delta vs y i ->
    (forall vs : vars,
        init_var (Delta & x ~ i) vs x i ->
        init_var Delta (vs /[ x -> y]) y i).
  Proof.
    introv Hni.
    assert (x # (@empty init_typ)) by auto.
    intros vs'.
    replace (Delta & x ~ i) with (Delta & x ~ i & empty) at 1
      by auto using concat_empty_r; intro.
    replace Delta with (Delta & empty) at 1
      by auto using concat_empty_r.
    replace Delta with (Delta & empty) in Hni
      by auto using concat_empty_r.
    eauto using init_var_subst_cond.
  Qed.
End SubstCond.
