(** remove printing ~ *)
Set Implicit Arguments.

Require Import Program.Equality.
Require Import LibExtra DotTactics AbstractSyntax.
Require Import Effects.

Require Export InitVarDefs.

Section InitVar.
  Hint Constructors init_var init_sub : core.

  Lemma init_var_commit_unspec : forall Delta vs x,
      binds x committed Delta ->
      init_var Delta vs x unspecified.
  Proof. intros; eauto. Qed.
  Hint Resolve init_var_commit_unspec : core.

  Lemma init_var_local_free : forall Delta vs x,
      init_var Delta vs x local ->
      init_var Delta vs x free.
  Proof. intros; eauto. Qed.
  Hint Resolve init_var_local_free : core.

  Lemma init_var_free_unspec : forall Delta vs x,
      init_var Delta vs x free ->
      init_var Delta vs x unspecified.
  Proof. intros; eauto. Qed.
  Hint Resolve init_var_free_unspec : core.

  Lemma init_var_sub_comm : forall i, init_sub i committed -> i = committed.
  Proof with (eauto; try(congruence)). introv Hsub. dependent induction Hsub... Qed.
  Hint Resolve init_var_sub_comm : core.

  Lemma init_var_sub_local : forall i, init_sub i local -> i = local.
  Proof with (eauto; try(congruence)). introv Hsub. dependent induction Hsub... Qed.
  Hint Resolve init_var_sub_local : core.

  Lemma init_var_sub_free : forall i, init_sub i free -> (i = local \/ i = free).
  Proof with (eauto; try(congruence)).
    introv Hsub. dependent induction Hsub...
    destruct j; eauto;
      specialize (IHHsub2 eq_refl); destruct IHHsub2;
        inversions H.
  Qed.
  Hint Resolve init_var_sub_free : core.

  Lemma init_var_unspec_sub : forall i, init_sub unspecified i -> i = unspecified.
  Proof with (eauto; try(congruence)). introv Hsub. dependent induction Hsub... Qed.
  Hint Resolve init_var_unspec_sub : core.

  Lemma init_var_local_in_vs : forall Delta vs x,
      init_var Delta vs x local -> x \in vs.
  Proof. introv Hinitx. dependent induction Hinitx; eauto. Qed.

  Lemma init_var_free_in_vs : forall Delta vs x,
      init_var Delta vs x free -> x \in vs.
  Proof.
    introv Hinitx. dependent induction Hinitx; eauto.
    apply init_var_sub_free in H.
    destruct H; subst; eauto using init_var_local_in_vs.
  Qed.

  Lemma init_var_typing_implies_bound : forall Delta vs x i,
      init_var Delta vs x i ->
      exists i', binds x i' Delta.
  Proof.
    intros. induction H; subst; eauto.
  Qed.

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
    intros. induction H; subst; eauto.
  Qed.

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
    - apply init_var_local; auto.
      apply Hvs; auto; intro; binds_eq.
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
    - apply init_var_local; auto.
      apply Hvs; auto; intro; binds_eq.
    - apply init_var_free; auto.
      apply Hvs; auto; intro; binds_eq.
    - apply init_var_unspec; auto.
      apply Hvs; auto; intro; binds_eq.
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

  Lemma init_var_strengthen_D_push : forall Delta vs y x i' i,
      x <> y ->
      init_var (Delta & y ~ i') vs x i ->
      init_var Delta vs x i.
  Proof.
    intros * Hneq. remember (Delta & y ~ i') as Delta' eqn:Heq.
    intros Hin.
    induction Hin; subst;
      try match goal with
      | [ Hb:  binds ?x1 ?i1 (?D & ?x2 ~ ?i2),
               Hn : ?x1 <> ?x2 |- _ ] =>
        apply (binds_push_neq_inv Hb) in Hn
      end; eauto.
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

  Lemma init_var_more_committed : forall Delta1 Delta2 vs x i,
      init_var Delta1 vs x i ->
      (forall x, binds x committed Delta1 -> binds x committed Delta2) ->
      (forall x init, x \in vs -> binds x init Delta1 -> binds x init Delta2) ->
      init_var Delta2 vs x i.
  Proof.
    induction 1; subst; eauto.
  Qed.

  Lemma init_var_more_specified : forall Delta1 Delta2 vs x y i i',
      init_var (Delta1 & y ~ unspecified & Delta2) vs x i ->
      y # Delta2 ->
      (i' = local) \/ (i' = free) \/ (i' = committed) ->
      init_var (Delta1 & y ~ i' & Delta2) vs x i.
  Proof.
    intros *. remember (Delta1 & y ~ unspecified & Delta2) as Delta' eqn:Heq.
    introv H Hfr Hfc. assert (binds y i' (Delta1 & y ~ i' & Delta2)) by auto.
    induction H; subst; eauto.
    - apply binds_middle_change with (v2:=i') in H; try congruence; eauto.
    - apply binds_middle_change with (v2:=i') in H1; try congruence; eauto.
    - apply binds_middle_change with (v2:=i') in H1; try congruence; eauto.
    - apply binds_middle_inv in H1; destruct_all; subst; auto.
  Qed.

  Lemma init_var_substitution_neq_middle : forall Delta1 x i' Delta2 vs z i,
      init_var (Delta1 & x ~ i' & Delta2) vs z i ->
      z <> x ->
      init_var (Delta1 & Delta2) vs z i.
  Proof.
    intros *. remember (Delta1 & x ~ i' & Delta2) as Delta' eqn:Heq.
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
    intros.
    remember (Delta1 & x ~ i' & Delta2) as Delta' eqn:Heq1.
    remember (vs \u \{x}) as vs' eqn:Heq2.
    cases_if; auto.
    - induction H; subst;
        try binds_middle_subst; eauto;
          inversion H1; auto.
    - induction H; subst;
        repeat match goal with
               | [ H : ?z \in ?vs \u ?vs' |- _ ] =>
                 rewrite ? in_union, ? in_singleton in H; destruct H;
                   try congruence
               end; eauto 3 using binds_subst.
  Qed.

  Lemma init_var_substitution_middle' : forall Delta1 x i' Delta2 vs z y i,
      init_var (Delta1 & x ~ i' & Delta2) vs z i -> x # Delta2 ->
      init_var (Delta1 & Delta2)
               (If x \in vs then (vs \- \{x}) \u \{y} else vs)
               y i' ->
      init_var (Delta1 & Delta2)
               (If x \in vs then (vs \- \{x}) \u \{y} else vs)
               (z \[ x -> y]) i.
  Proof.
    intros.
    remember (Delta1 & x ~ i' & Delta2) as Delta' eqn:Heq.
    repeat cases_if; auto.
    - induction H; subst;
        try binds_middle_subst; eauto;
          inversion H1; auto.
    - assert (y \in (vs \- \{ x} \u \{ y})) by (apply is_in_union_singleton_l).
      pose proof (init_var_typing_implies_bound H) as [?i ?H].
      assert (z \in vs -> z \in vs \- \{x} \u \{y}).
      { intros. rewrite in_union, in_remove, notin_singleton; auto. }
      assert (z # (x ~ i')) by auto.
      rewrite Heq in H3. pose proof (binds_not_middle_inv H3 H5).
      induction H; subst; try binds_eq;
        destruct H6 as [? | [? ?]]; eauto 6.
    - induction H; subst; try congruence; auto.
      + binds_middle_subst; auto.
      + inversions H1; eauto.
    - assert (z # (x ~ i')) by auto.
      pose proof (init_var_typing_implies_bound H) as [?i ?H].
      rewrite Heq in H3. pose proof (binds_not_middle_inv H3 H2).
      induction H; subst; try binds_eq; destruct H4 as [? | [? ?]]; eauto 6.
  Qed.

  Lemma init_var_substitution_middle : forall Delta1 x i' Delta2 vs z y i,
      init_var (Delta1 & x ~ i' & Delta2) vs z i -> x # Delta2 ->
      init_var (Delta1 & Delta2)
               (If x \in vs then (vs \- \{x}) \u \{y} else vs \- \{ y}) y i' ->
      init_var (Delta1 & Delta2)
               (If x \in vs then (vs \- \{x}) \u \{y} else vs \- \{ y})
               (z \[ x -> y]) i.
  Proof.
    intros.
    remember (Delta1 & x ~ i' & Delta2) as Delta' eqn:Heq.
    repeat cases_if; auto.
    - induction H; subst; try binds_middle_subst; eauto;
        inversion H1; auto.
    - assert (y \in (vs \- \{ x} \u \{ y})) by (apply is_in_union_singleton_l).
      pose proof (init_var_typing_implies_bound H) as [?i ?H].
      assert (z \in vs -> z \in vs \- \{x} \u \{y}).
      { intros. rewrite in_union, in_remove, notin_singleton; auto. }
      assert (z # (x ~ i')) by auto.
      rewrite Heq in H3. pose proof (binds_not_middle_inv H3 H5).
      induction H; subst; try binds_eq; destruct H6 as [? | [? ?]]; eauto 6.
    - induction H; subst; try congruence; auto.
      + binds_middle_subst; auto.
      + inversions H1; eauto.
    - assert (z # (x ~ i')) by auto.
      pose proof (init_var_typing_implies_bound H) as [?i ?H].
      rewrite Heq in H3. pose proof (binds_not_middle_inv H3 H2).
      assert ((y \notin (vs \- \{ y}))).
      { intro. rewrite in_remove in H5. apply H5, in_singleton_self. }
      assert (binds y committed (Delta1 & Delta2)).
      { remember (Delta1 & Delta2) as Delta''. remember (vs \- \{ y}) as vs''.
        clear Heq. rewrite dom_single in H2.
        induction H1; subst; try congruence; eauto using binds_middle_update. }
      + pose proof (var_decide y z) as [? | ?]; subst.
        * induction H; subst; try binds_eq; destruct H4 as [? | [? ?]]; eauto.
          -- apply (binds_concat_right Delta1) in H3; binds_eq.
          -- apply (binds_concat_left H4) in H3; binds_eq.
          -- apply (binds_concat_right Delta1) in H3; binds_eq.
          -- apply (binds_concat_left H4) in H3; binds_eq.
        * assert (z \in vs -> z \in vs \- \{ y}).
          { intro. rewrite in_remove, notin_singleton; auto. }
          induction H; subst; try binds_eq; destruct H4 as [? | [? ?]]; eauto 6.
  Qed.

  Lemma init_var_binds_in_init_var : forall Delta x vs i,
      binds x i Delta ->
      x \in vs ->
      init_var Delta vs x i.
  Proof.
    induction i; auto.
  Qed.

  Lemma init_var_middle_init_var : forall Delta1 Delta2 x vs i,
      x # Delta2 ->
      x \in vs ->
      init_var (Delta1 & x ~ i & Delta2) vs x i.
  Proof.
    eauto using init_var_binds_in_init_var.
  Qed.

  Lemma init_var_subtyp : forall Delta1 Delta2 x vs i i',
      x # Delta2 ->
      init_var (Delta1 & x ~ i & Delta2) vs x i' ->
      forall y vs Delta, init_var Delta vs y i ->
                init_var Delta vs y i'.
  Proof.
    intros * Hfr Hinit.
    apply init_var_strengthen_D in Hinit; auto.
    remember (Delta1 & x ~ i) as Delta'.
    induction Hinit; subst; eauto;
      match goal with
      | [ Hb:  binds ?x1 ?i1 (?D & ?x2 ~ ?i2) |- _ ] =>
        pose proof (binds_push_eq_inv Hb); subst i2
      end;
      inversion 1; subst; auto.
  Qed.

  Lemma vars_subst_union : forall x y vs1 vs2,
      ((vs1 \u vs2) /[x -> y]) = (vs1 /[x -> y]) \u (vs2 /[x -> y]).
  Proof.
    unfold subst_var, VarsSubstVar.
    intros; apply fset_extens; unfold "\c"; intros z Hin.
    - repeat cases_if;
        rewrite ? in_union, ? in_remove, ? in_union in *;
        destruct_all; auto; try solve [exfalso; auto].
    - repeat cases_if;
        rewrite ? in_union, ? in_remove, ? in_union in *;
        destruct_all; auto; try solve [exfalso; auto].
      + left; split; auto.
        intro Heq. rewrite in_singleton in Heq; subst.
        auto.
      + left; split; auto.
        intro Heq. rewrite in_singleton in Heq; subst.
        auto.
  Qed.

  Lemma vars_subst_singleton_same : forall x y,
      \{ x} = (\{ y} /[y -> x]).
  Proof.
    unfold subst_var, VarsSubstVar.
    intros. cases_if.
    - rewrite fset_remove_same_empty, union_empty_l; auto.
    - exfalso; auto using in_singleton_self.
  Qed.

  Lemma vars_subst_notin : forall x y vs,
      x \notin vs ->
      (vs /[x -> y]) = vs.
  Proof.
    unfold subst_var, VarsSubstVar.
    intros. cases_if; auto.
  Qed.

  Lemma vars_subst_in1 : forall x y vs,
      x \in vs ->
      y \in (vs /[x -> y]).
  Proof.
    unfold subst_var, VarsSubstVar.
    intros; cases_if.
    rewrite in_union; right.
    apply in_singleton_self.
  Qed.

  Lemma vars_subst_in2 : forall x y z vs,
      z \in vs ->
      z <> x ->
      z \in (vs /[x -> y]).
  Proof.
    unfold subst_var, VarsSubstVar.
    intros; cases_if; auto.
    rewrite in_union, in_remove, notin_singleton; auto.
  Qed.

  Lemma vars_subst_in : forall x y z vs,
      z \in vs ->
      (z \[x -> y]) \in (vs /[x -> y]).
  Proof.
    intros; cases_if;
      eauto using vars_subst_in1, vars_subst_in2.
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
      + dependent induction H;
          eauto using binds_middle_neq_binds.
        * apply init_var_local;
            eauto using binds_middle_neq_binds.
          rewrite in_union, in_remove, notin_singleton;
            left; auto.
        * apply init_var_free; eauto using binds_middle_neq_binds.
          rewrite in_union. left. rewrite in_remove. split; auto.
        * apply init_var_unspec; eauto using binds_middle_neq_binds.
          rewrite in_union. left. rewrite in_remove. split; auto.
    - dependent induction H;
        eauto using binds_middle_neq_binds.
      + apply init_var_commit;
          cases_if; try binds_middle_subst;
            eauto using binds_middle_neq_binds.
        specialize (H1 vs (init_var_commit _ H)).
        cases_if. dependent induction H1; eauto.
      + apply init_var_local;
          cases_if; try binds_middle_subst;
            eauto using binds_middle_neq_binds.
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
    intros. cases_if.
    - eapply init_var_sub; eauto 1.
      assert (x # Delta2) by eauto.
      dependent induction H; eauto 2;
        try match goal with
            | [H : binds x ?i (Delta1 & x ~ i & Delta2) |- _] =>
              eapply binds_middle_eq_fresh_inv in H; eauto 3; subst; eauto 2
            end.
      specialize (IHinit_var _ _ _ eq_refl JMeq_refl H1 H2 H3).
      eauto.
    - dependent induction H; subst; eauto using binds_middle_neq_binds;
        try solve [congruence
                  | exfalso; eauto using in_empty_inv].
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
      eapply init_var_sub; eauto 2. clear H1.
      dependent induction H; eauto 3;
        try match goal with
            | [H : binds x ?i (Delta1 & x ~ i' & Delta2) |- _] =>
              eapply binds_middle_eq_fresh_inv in H; eauto 3; subst; eauto 2
            end.
    - assert (z \in vs -> z \in (vs \- \{ x})).
      { intros. rewrite in_remove, notin_singleton; auto. }
      dependent induction H; subst;
        eauto using binds_middle_neq_binds.
  Qed.

  Lemma init_var_substitution_middle_empty_remove :
    forall Delta1 x Delta2 vs i i' y z,
      init_var (Delta1 & x ~ i' & Delta2) vs z i ->
      x # (Delta1 & Delta2) ->
      init_var (Delta1 & Delta2) \{} y i' ->
      init_var (Delta1 & Delta2) (vs \- \{x}) (z \[ x -> y] ) i.
  Proof.
    intros. cases_if.
    - rewrite dom_concat, notin_union in H0. destruct H0.
      replace (vs \- \{x}) with (\{} \u (vs \- \{x}))
        by apply union_empty_l.
      apply init_var_weaken_vars. eapply init_var_sub; eauto 2.
      dependent induction H; eauto 3;
        try match goal with
            | [H : binds x ?i (Delta1 & x ~ ?i' & Delta2) |- _] =>
              eapply binds_middle_eq_fresh_inv in H; eauto 3; subst; eauto 2
            end.
    - assert (z \in vs -> z \in (vs \- \{ x})).
      { intros. rewrite in_remove, notin_singleton; auto. }
      dependent induction H; subst;
        eauto using binds_middle_neq_binds; try(congruence);
          repeat(match goal with
                 | [ H : init_var _ _ _ local |- _ ] => inversions H
                 | [ H : init_var _ _ _ free |- _ ] => inversions H
                 end);
          match goal with
          | [ H : binds _ _ _ |- _ ] => apply binds_middle_neq_binds in H; eauto
          end.
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
      introv HxninD2 Hinity.
      dependent induction Hinity; introv Hinitx.
      - dependent induction Hinitx; eauto 3 using vars_subst_in1.
      - dependent induction Hinitx; eauto 3 using vars_subst_in1.
      - dependent induction Hinitx; eauto 3 using vars_subst_in1.
        apply init_var_sub_free in H1; destruct H1; subst; eauto 3.
        clear IHHinitx. dependent induction Hinitx; eauto 3.
        binds_middle_subst. discriminate.
      - dependent induction Hinitx; eauto 3 using vars_subst_in1.
        clear IHHinitx. dependent induction Hinitx; eauto using vars_subst_in1.
        binds_middle_subst. discriminate.
      - dependent induction Hinitx; eauto 3 using vars_subst_in1.
        + apply init_var_sub_comm in H; subst; eauto 3.
        + apply init_var_sub_local in H; subst; eauto 3.
        + apply init_var_sub_free in H; destruct_all; subst; eauto 3.
          clear IHHinity. dependent induction Hinity; eauto 4 using vars_subst_in1.
        + clear IHHinity. dependent induction Hinity; eauto using vars_subst_in1.
        + clear IHHinitx. eapply init_var_sub with (i' := i'); eauto 2.
          apply IHHinity; eauto. clear IHHinity. clear Hinity.
          dependent induction Hinitx; eauto 3.
          * binds_middle_subst. apply init_var_sub_comm in H1. subst. eauto.
          * binds_middle_subst. apply init_var_sub_local in H2. subst. eauto.
          * binds_middle_subst. apply init_var_sub_free in H2.
            destruct_all; subst; eauto.
          * binds_middle_subst. destruct i'; eauto.
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

End InitVar.
