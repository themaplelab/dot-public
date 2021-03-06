(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import PreTyping Typing GeneralTyping Weakening.
Require Import SubstitutionClass Substitution.
Require Import InitVar InitVarSubtyping InitTyping InitWeakening.
Require Import Effects EffectSubstitution.
Require Import BndIntro.
Require Import HeapCommit.

Implicit Types (i : init_typ) (t : trm) (l : lit) (avs : avars).

Local Hint Resolve
      init_var_weaken_vars init_var_weaken_D
      init_var_weaken_D_push init_var_strengthen_D_push
      init_var_more_committed : core.
Local Hint Extern 2 => simple apply weaken_middle : core.
Local Hint Extern 2 => simple apply weaken : core.
Local Hint Resolve init_var_substitution_middle_empty init_var_substitution_middle_remove : core.

(* For replacements *)
Local Hint Resolve concat_empty_r : core.
Local Hint Extern 2 (?Gamma & (subst_env ?x ?y) empty = ?Gamma) =>
rewrite map_empty; apply concat_empty_r : core.

Local Ltac spec_ty_subst :=
    match goal with
    | [Hfr : ?x # ?G2, Htyt : ?G1 & ?x ~ ?T & ?G2 ⊢ ?t ∶ ?U,
       Hni : ?x \notin (fv_env ?G1), Htyy : ?G1 & (subst_env ?x ?y) ?G2 ⊢ trm_var (avar_f ?y) ∶ (?T /[ ?x -> ?y]) |- _ ] =>
      let H := fresh "H" in
      pose proof (ty_subst_middle _ _ _ Hfr Htyt Hni Htyy) as H; sympl in H
    end.
Local Hint Extern 7 => spec_ty_subst : core.

(** Substitution for initialization *)
Lemma well_init_subst_avars : forall Gamma1 x T' Gamma2 Delta1 i' Delta2 vs avs is' y,
    x # Delta2 ->
    Gamma1 & x ~ T' & Gamma2 ⸴ Delta1 & x ~ i' & Delta2 ⸴ vs ⊢i avs :: is' ->
    (forall vs : vars,
        init_var (Delta1 & x ~ i' & Delta2) vs x i' ->
        init_var (Delta1 & Delta2) (vs /[ x -> y]) y i') ->
    Gamma1 & (subst_env x y) Gamma2 ⸴ Delta1 & Delta2⸴ (vs /[ x -> y]) ⊢i (avs /[ x -> y]) :: is'.
Proof.
  intros * Hfr Hwi Hxy.
  remember (Gamma1 & x ~ T' & Gamma2) as Gamma.
  remember (Delta1 & x ~ i' & Delta2) as Delta.
  induction Hwi; auto.
  apply well_inits_cons; auto. clear IHHwi H0; subst Delta Gamma.
  inversions H.
  - apply init_var_binds.
    eauto using init_var_substitution_middle_subst.
  - apply init_commit. inversions H0.
    constructor. cases_if.
    * binds_middle_subst.
      apply (init_var_commit \{}) in H3.
      apply Hxy in H3. inversions H3; auto.
    * eauto using binds_middle_neq_binds.
Qed.

Lemma well_commit_more_committed_lit : forall Gamma Delta Delta' l,
      Gamma ⸴ Delta ⊢c l ->
      more_committed Delta Delta' ->
      Gamma ⸴ Delta' ⊢c l.
Proof.
  intros. eapply well_init_more_committed_rules; eauto.
Qed.

(* This lemma essentially says that substituting a committed variable for another
   committed variable preserves well-committedness of a term. *)
Lemma well_comm_subst_comm :
  (forall Gamma Delta t,
      Gamma ⸴ Delta ⊢c t ->
      forall Gamma1 x T' Gamma2 y Delta1 i' Delta2,
        Gamma = (Gamma1 & x ~ T' & Gamma2) ->
        x # Gamma2 ->
        x \notin fv_env Gamma1 ->
        Gamma1 & (subst_env x y Gamma2) ⊢ trm_var (avar_f y) ∶ subst_var x y T' ->
        Delta = Delta1 & x ~ i' & Delta2 -> x # (Delta1 & Delta2) ->
        binds y committed (Delta1 & Delta2) ->
        Gamma1 & (subst_env x y Gamma2) ⸴ Delta1 & Delta2 ⊢c subst_var x y t ) /\
  (forall Gamma Delta avs,
      Gamma ⸴ Delta ⊢c avs ->
      forall Gamma1 x T' Gamma2 y Delta1 i' Delta2,
        Gamma = (Gamma1 & x ~ T' & Gamma2) ->
        x # Gamma2 ->
        x \notin fv_env Gamma1 ->
        Gamma1 & (subst_env x y Gamma2) ⊢ trm_var (avar_f y) ∶ subst_var x y T' ->
        Delta = Delta1 & x ~ i' & Delta2 -> x # (Delta1 & Delta2) ->
        binds y committed (Delta1 & Delta2) ->
        Gamma1 & (subst_env x y Gamma2) ⸴ Delta1 & Delta2 ⊢c subst_var x y avs ) /\
  (forall Gamma Delta l,
      Gamma ⸴ Delta ⊢c l ->
      forall Gamma1 x T' Gamma2 y Delta1 i' Delta2,
        Gamma = (Gamma1 & x ~ T' & Gamma2) ->
        x # Gamma2 ->
        x \notin fv_env Gamma1 ->
        Gamma1 & (subst_env x y Gamma2) ⊢ trm_var (avar_f y) ∶ subst_var x y T' ->
        Delta = Delta1 & x ~ i' & Delta2 -> x # (Delta1 & Delta2) ->
        binds y committed (Delta1 & Delta2) ->
        Gamma1 & (subst_env x y Gamma2) ⸴ Delta1 & Delta2 ⊢c subst_var x y l ) /\
  (forall Gamma Delta vs t i,
      Gamma ⸴ Delta ⸴ vs ⊢i t ∶ i ->
      forall Gamma1 x T' Gamma2 y Delta1 i' Delta2,
        Gamma = (Gamma1 & x ~ T' & Gamma2) ->
        x # Gamma2 ->
        x \notin fv_env Gamma1 ->
        Gamma1 & (subst_env x y Gamma2) ⊢ trm_var (avar_f y) ∶ subst_var x y T' ->
        Delta = Delta1 & x ~ i' & Delta2 -> x # (Delta1 & Delta2) ->
        binds y committed (Delta1 & Delta2) ->
        (* The x \notin vs condition is crucial for the proof! *)
        x \notin vs ->
        Gamma1 & (subst_env x y Gamma2) ⸴ Delta1 & Delta2 ⸴ vs ⊢i
                                                          subst_var x y t ∶ i) /\
  (forall Gamma Delta vs avs is',
      Gamma ⸴ Delta ⸴ vs ⊢i avs :: is' ->
      forall Gamma1 x T' Gamma2 y Delta1 i' Delta2,
        Gamma = (Gamma1 & x ~ T' & Gamma2) ->
        x # Gamma2 ->
        x \notin fv_env Gamma1 ->
        Gamma1 & (subst_env x y Gamma2) ⊢ trm_var (avar_f y) ∶ subst_var x y T' ->
        Delta = Delta1 & x ~ i' & Delta2 -> x # (Delta1 & Delta2) ->
        binds y committed (Delta1 & Delta2) ->
        x \notin vs ->
        Gamma1 & (subst_env x y Gamma2) ⸴ Delta1 & Delta2 ⸴ vs ⊢i
                                                          (avs /[x -> y]) :: is').
Proof with eauto.
  apply well_init_mut_ind; intros; subst;
    sympl; try solve [econstructor; eauto 3].
  - (* commit_var *)
    cases_if... constructor. apply binds_middle_neq_binds in b...
  - (* commit_let *)
    init_fresh_constructor_extern...
    assert (Delta1 & Delta2 & z ~ committed = Delta1 & (Delta2 & z ~ committed))
      by eauto. rewrite H1. clear H1.
    assert ((Gamma1 & (subst_env x y) Gamma2 & z ~ (T /[ x -> y])) =
            Gamma1 & ((subst_env x y) Gamma2 & z ~ (T /[ x -> y])))
      by eauto. rewrite H1. clear H1.
    assert (((subst_env x y) Gamma2 & z ~ (T /[ x -> y])) =
            (subst_env x y) (Gamma2 & z ~ T)).
    { rewrite subst_single, map_concat. reflexivity. }
    rewrite H1. clear H1.
    rewrite <- subst_open_commut_single...
    eapply H0...
    + rewrite map_concat, concat_assoc.
      apply weaken_env with (Gamma3 := Gamma1 & (subst_env x y) Gamma2); eauto 2.
      intros. rewrite map_single, dom_single, in_singleton in H1. subst.
      rewrite dom_concat, notin_union. split...
    + rewrite concat_assoc...
  - (* commit_llit *)
    init_fresh_constructor_extern... clear H.
    rewrite <- subst_open_commut_single...
    rewrite <- concat_assoc, <- map_single, <- map_concat.
    rewrite <- concat_assoc.
    eapply H0...
    + rewrite map_concat, map_single, concat_assoc.
      apply weaken_env with (Gamma3 := Gamma1 & (subst_env x y) Gamma2); eauto 2.
      rewrite dom_single. intros. rewrite in_singleton in *; subst...
    + rewrite concat_assoc...
  - (* commit_all_intro *)
    init_fresh_constructor_extern.
    rewrite <- subst_open_commut_single...
    rewrite <- concat_assoc, <- map_single, <- map_concat.
    rewrite <- concat_assoc.
    eapply H...
    + rewrite map_concat, map_single, concat_assoc.
      apply weaken_env with (Gamma3 := Gamma1 & (subst_env x y) Gamma2); eauto 2.
      rewrite dom_single. intros. rewrite in_singleton in *; subst...
    + rewrite concat_assoc...
  - (* commit_con_intro *)
    init_fresh_constructor_extern...
    + rewrite length_s_subst...
    + intros. clear H i0 H6.
      assert (length ys = length_s Ts) as HlTs
          by (rewrite H0, length_s_subst; congruence).
      assert (fresh L (S (length ys)) (x0 :: ys)) by auto.
      specialize (h x0 ys HlTs H). clear H.
      repeat rewrite <- subst_open_vars_commut_fresh_length
        by (simpls; destruct_all; simpl_dom; auto).
      rewrite def_eff_subst1, (@def_eff_subst x0 x y) by auto.
      destruct h as [effs' [h Heq]].
      exists (effs' /[ x -> y]); split.
      * eauto using effs_subst_in_effs_and_trm.
      * eauto using def_eff_from_list_subst.
    + intros x' ys HlTs Hfr.
      assert (length ys = length_s Ts) as HlTs'
       by (rewrite length_s_subst in HlTs; auto).
      specialize (H x' ys HlTs').
      specialize (i0 x' ys HlTs').
      assert (fresh L (S (length ys)) (x' :: ys)) as Hfr' by auto.
      specialize (H Hfr'); specialize (i0 Hfr'); clear Hfr'.
      specialize (H Gamma1 x T').
      specialize (H (Gamma2 & ys ~** to_list Ts & x' ~ open_vars (x' :: ys) T)).
      specialize (H y Delta1 i' (Delta2 & ys ~** is' & x' ~ free)).
      specialize (H concat_assoc_eq5).
      assert (x # (Gamma2 & ys ~** to_list Ts
          & x' ~ open_vars (x' :: ys) T)) as Hfr'.
      { simpl_dom. rewrite ? notin_union.
        repeat split; auto 2.
        apply fresh_notin_dom; auto.
        destruct Hfr; fresh_solve. }
      specialize (H Hfr' H2); clear Hfr'.
      rewrite ? concat_assoc, ? map_concat, <- ? subst_single,
      <- ? subst_singles_rev_to_list in H by auto.
      rewrite ? concat_assoc in H.
      rewrite ? subst_open_vars_commut_fresh_length in H
        by auto.
      eapply H; clear H; eauto 2.
      * rewrite <- concat_assoc.
        apply weaken_env; auto 2.
        intros y'.
        rewrite ? dom_concat, dom_map, in_union,
        dom_single, in_singleton.
        destruct Hfr as [Hfrx' Hfr].
        destruct 1; subst; auto.
        eapply (fresh_list_notin _ _ (length ys) HlTs); eauto.
      * rewrite ? dom_concat, ? notin_union.
        repeat split; auto.
        apply fresh_notin_dom; try congruence; auto.
        destruct (fresh_cons Hfr); auto.
      * rewrite <- concat_assoc.
        eapply binds_concat_left; eauto 2.
        rewrite dom_concat, dom_singles...
        { rewrite <- from_list_rev.
          rewrite dom_single, notin_union, notin_singleton. split...
          destruct Hfr as [_ Hfr].
          eapply fresh_single_notin. eapply fresh_single_in...
          repeat(rewrite in_union). repeat(rewrite in_singleton).
          (* I should learn how to write tactics... *)
          left. left. left. left. left. left. left. left.
          left. left. left. left.  right... }
        { rewrite liblist_length. repeat(rewrite List.rev_length). congruence. }
      * rewrite notin_union, notin_singleton. split...
        destruct Hfr... clear H.
        apply fresh_single_in with (x := x) in H0; eauto using fresh_single_notin.
        repeat(rewrite in_union). rewrite in_singleton.
        (* There has to be an easier way of doing this *)
        left. left. left. left. left. left. left. left.
        left. left. left. left. left. right...
  - (* init_var_binds. This case depends on the x \notin vs condition *)
    case_if.
    + (* x = x0 *) subst. inversions i0... exfalso...
    + (* x <> x0 *)
      unfold subst_var. unfold VarsSubstVar.
      change (map (TypSubstVar x0 y) Gamma2) with ((subst_env x0 y) Gamma2).
      econstructor. intros; subst.
      apply init_var_strengthen_D_middle in i0...
  - (* init_lit_free *)
    init_fresh_constructor_extern...
    + clear H0 i0.
      repeat(rewrite subst_env_fset_vars_distrib_env in *).
      rewrite subst_env_fset_vars_single in *.
      eapply H...
      * rewrite dom_concat. repeat(rewrite subst_env_fset_vars_dom)...
      * rewrite <- subst_env_fset_vars_distrib_env.
        destruct (fv_decide y vs);
          eauto using subst_env_fset_vars_in_vs, subst_env_fset_vars_notin_ignore.
    + clear H i0.
      rewrite <- subst_open_commut_single...
      rewrite <- concat_assoc, <- map_single, <- map_concat.
      rewrite <- concat_assoc.
      eapply H0 with (Delta4 := (Delta2 & z ~ free))...
      * rewrite map_concat, concat_assoc.
        apply weaken_env with (Gamma3 := Gamma1 & (subst_env x y) Gamma2); eauto 2.
        rewrite map_single, dom_single. intros. rewrite in_singleton in *.
        subst. rewrite dom_concat, notin_union. split...
      * rewrite concat_assoc...
  - (* init_let *)
    init_fresh_constructor_extern...
    subst_open_fresh.
    notin_L; notin_apply. clear H1 H.
    specialize (H0 Gamma1 x T' (Gamma2 & z ~ T)).
    specialize (H0 y Delta1 i'0 (Delta2 & z ~ i)).
    rewrite ? concat_assoc in H0.
    rewrite <- map_single, <- concat_assoc, <- map_concat.
    eapply H0; eauto using init_binds_sub_push.
    rewrite map_concat, concat_assoc, map_single.
    apply weaken; auto.
  - (* init_llit *)
    init_fresh_constructor_extern...
    notin_L; notin_apply.
    specialize (H0 Gamma1 x T' (Gamma2 & z ~ T)).
    specialize (H0 y Delta1 i' (Delta2 & z ~ committed)).
    rewrite ? concat_assoc in H0; subst_open_fresh.
    rewrite <- map_single, <- concat_assoc, <- map_concat.
    eapply H0; eauto using init_binds_sub_push.
    + rewrite map_concat, concat_assoc, map_single.
      apply weaken; auto.
Qed.

Lemma well_init_substitution :
  (forall Gamma Delta t,
      Gamma ⸴ Delta ⊢c t ->
      forall Gamma1 x T' Gamma2 y Delta1 i' Delta2,
        Gamma = (Gamma1 & x ~ T' & Gamma2) ->
        x # Gamma2 ->
        x \notin fv_env Gamma1 ->
        Gamma1 & (subst_env x y Gamma2) ⊢ trm_var (avar_f y) ∶ subst_var x y T' ->
        Delta = Delta1 & x ~ i' & Delta2 -> x # (Delta1 & Delta2) ->
        init_binds_sub x (Delta1 & x ~ i' & Delta2) y (Delta1 & Delta2) ->
        Gamma1 & (subst_env x y Gamma2) ⸴ Delta1 & Delta2 ⊢c subst_var x y t ) /\
  (forall Gamma Delta avs,
      Gamma ⸴ Delta ⊢c avs ->
      forall Gamma1 x T' Gamma2 y Delta1 i' Delta2,
        Gamma = (Gamma1 & x ~ T' & Gamma2) ->
        x # Gamma2 ->
        x \notin fv_env Gamma1 ->
        Gamma1 & (subst_env x y Gamma2) ⊢ trm_var (avar_f y) ∶ subst_var x y T' ->
        Delta = Delta1 & x ~ i' & Delta2 -> x # (Delta1 & Delta2) ->
        init_binds_sub x (Delta1 & x ~ i' & Delta2) y (Delta1 & Delta2) ->
        Gamma1 & (subst_env x y Gamma2) ⸴ Delta1 & Delta2 ⊢c subst_var x y avs ) /\
  (forall Gamma Delta l,
      Gamma ⸴ Delta ⊢c l ->
      forall Gamma1 x T' Gamma2 y Delta1 i' Delta2,
        Gamma = (Gamma1 & x ~ T' & Gamma2) ->
        x # Gamma2 ->
        x \notin fv_env Gamma1 ->
        Gamma1 & (subst_env x y Gamma2) ⊢ trm_var (avar_f y) ∶ subst_var x y T' ->
        Delta = Delta1 & x ~ i' & Delta2 -> x # (Delta1 & Delta2) ->
        init_binds_sub x (Delta1 & x ~ i' & Delta2) y (Delta1 & Delta2) ->
        Gamma1 & (subst_env x y Gamma2) ⸴ Delta1 & Delta2 ⊢c subst_var x y l ) /\
  (forall Gamma Delta vs t i,
      Gamma ⸴ Delta ⸴ vs ⊢i t ∶ i ->
      forall Gamma1 x T' Gamma2 y Delta1 i' Delta2,
        Gamma = (Gamma1 & x ~ T' & Gamma2) ->
        x # Gamma2 ->
        x \notin fv_env Gamma1 ->
        Gamma1 & (subst_env x y Gamma2) ⊢ trm_var (avar_f y) ∶ subst_var x y T' ->
        Delta = Delta1 & x ~ i' & Delta2 -> x # (Delta1 & Delta2) ->
        init_binds_sub x (Delta1 & x ~ i' & Delta2) y (Delta1 & Delta2) ->
        Gamma1 & (subst_env x y Gamma2) ⸴ Delta1 & Delta2 ⸴ vs /[x -> y]
                                                          ⊢i subst_var x y t ∶ i) /\
  (forall Gamma Delta vs avs is',
      Gamma ⸴ Delta ⸴ vs ⊢i avs :: is' ->
      forall Gamma1 x T' Gamma2 y Delta1 i' Delta2,
        Gamma = (Gamma1 & x ~ T' & Gamma2) ->
        x # Gamma2 ->
        x \notin fv_env Gamma1 ->
        Gamma1 & (subst_env x y Gamma2) ⊢ trm_var (avar_f y) ∶ subst_var x y T' ->
        Delta = Delta1 & x ~ i' & Delta2 -> x # (Delta1 & Delta2) ->
        init_binds_sub x (Delta1 & x ~ i' & Delta2) y (Delta1 & Delta2) ->
        Gamma1 & (subst_env x y Gamma2) ⸴ Delta1 & Delta2 ⸴ vs /[x -> y]
                                                        ⊢i (avs /[x -> y]) :: is').
Proof.
  apply well_init_mut_ind; intros; subst;
    sympl; try solve [econstructor; eauto 3].
  - cases_if; auto.
    + constructor.
      destruct (binds_middle_eq_fresh_inv b); auto; subst.
      pose proof (H5 _ b) as [i' [Hsub Hbiy]].
      inversions Hsub; auto.
    + apply binds_not_middle_inv in b; auto.
      destruct b as [? | [? ?]]; auto.
  - (* Comm Let *)
    init_fresh_constructor_extern; eauto; subst_open_fresh.
    notin_L; notin_apply.
    specialize (H0 Gamma1 x T' (Gamma2 & z ~ T) y Delta1 i'
                   (Delta2 & z ~ committed) concat_assoc_eq4).
    repeat rewrite ? concat_assoc, ? concat_assoc_map_push in *.
    apply H0; auto using init_binds_sub_push.
  - (* Com term let-lit *)
    init_fresh_constructor_extern; eauto; subst_open_fresh.
    notin_L; notin_apply.
    specialize (H0 Gamma1 x T' (Gamma2 & z ~ T) y Delta1 i'
                   (Delta2 & z ~ committed) concat_assoc_eq4).
    repeat rewrite ? concat_assoc, ? concat_assoc_map_push in *.
    apply H0; auto; eauto 4 using init_binds_sub_push.
  - (* Comm Lit lambda case *)
    init_fresh_constructor_extern; eauto; subst_open_fresh.
    notin_L; notin_apply.
    specialize (H Gamma1 x T' (Gamma2 & z ~ T) y Delta1 i'
                   (Delta2 & z ~ committed) concat_assoc_eq4).
    repeat rewrite ? concat_assoc, ? concat_assoc_map_push in *.
    apply H; auto using init_binds_sub_push.
  - (* Comm Lit constructor case *)
    init_fresh_constructor_extern.
    + rewrite length_s_subst; auto.
    + intros. clear H i0 H6.
      assert (length ys = length_s Ts) as HlTs
          by (rewrite H0, length_s_subst; congruence).
      assert (fresh L (S (length ys)) (x0 :: ys)) by auto.
      specialize (h x0 ys HlTs H). clear H.
      repeat rewrite <- subst_open_vars_commut_fresh_length
        by (simpls; destruct_all; simpl_dom; auto).
      rewrite def_eff_subst1, (@def_eff_subst x0 x y) by auto.
      destruct h as [effs' [h Heq]].
      exists (effs' /[ x -> y]); split.
      * eauto using effs_subst_in_effs_and_trm.
      * eauto using def_eff_from_list_subst.
    + intros x' ys HlTs Hfr.
      assert (length ys = length_s Ts) as HlTs'
       by (rewrite length_s_subst in HlTs; auto).
      specialize (H x' ys HlTs').
      specialize (i0 x' ys HlTs').
      assert (fresh L (S (length ys)) (x' :: ys)) as Hfr' by auto.
      specialize (H Hfr'); specialize (i0 Hfr'); clear Hfr'.
      specialize (H Gamma1 x T').
      specialize (H (Gamma2 & ys ~** to_list Ts & x' ~ open_vars (x' :: ys) T)).
      specialize (H y Delta1 i' (Delta2 & ys ~** is' & x' ~ free)).
      specialize (H concat_assoc_eq5).
      assert (x # (Gamma2 & ys ~** to_list Ts
          & x' ~ open_vars (x' :: ys) T)) as Hfr'.
      { simpl_dom. rewrite ? notin_union.
        repeat split; auto 2.
        apply fresh_notin_dom; auto.
        destruct Hfr; fresh_solve. }
      specialize (H Hfr' H2); clear Hfr'.
      assert ((from_list ys \u \{ x'} /[ x -> y]) =
              (from_list ys \u \{ x'})) as Hrm.
      { assert (x \notin from_list (x' :: ys)) as Hfl
          by (eapply fresh_single_notin with (n:=S (length ys)); eauto).
        rewrite from_list_cons, union_comm in Hfl.
        unfold subst_var, VarsSubstVar; cases_if; auto. }
      fold vars in Hrm; rewrite Hrm in H; clear Hrm.
      rewrite ? concat_assoc,
      ? map_concat,
      <- ? subst_single,
      <- ? subst_singles_rev_to_list in H by auto.
      rewrite ? concat_assoc in H.
      rewrite ? subst_open_vars_commut_fresh_length in H
        by auto.
      eapply H; clear H; auto.
      * rewrite <- concat_assoc.
        apply weaken_env; auto 2.
        intros y'.
        rewrite ? dom_concat, dom_map, in_union,
        dom_single, in_singleton.
        destruct Hfr as [Hfrx' Hfr].
        destruct 1; subst; auto.
        eapply (fresh_list_notin _ _ (length ys) HlTs); eauto.
      * rewrite ? dom_concat, ? notin_union.
        repeat split; auto.
        apply fresh_notin_dom; try congruence; auto.
        destruct (fresh_cons Hfr); auto.
      * apply init_binds_sub_push_fresh_cons; try congruence; auto.
        simpl_dom; auto.
  - (* init-var *)
    apply init_var_binds.
    assert (x0 # Delta2) as Hfr by auto.
    eapply init_binds_sub_substitution_middle_subst; eauto.
  - (* init-free-lit *)
    init_fresh_constructor_extern.
    + clear H0 i0.
      rewrite ? subst_env_fset_vars_distrib_env in *.
      rewrite subst_env_fset_vars_single in *.
      unfold subst_var. unfold VarsSubstVar.
      change (LitSubstVar x y l) with (l /[ x -> y]).
      change (map (TypSubstVar x y) Gamma2) with (subst_env x y Gamma2).
      cases_if.
      { (* x \in vs *)
        (* One must reason about the inclusion between y and vs in this case. *)
        destruct (fv_decide y vs).
        { (* y \in vs *)
          (* In this case, H cannot be used directly. A reason similar to the
             x \notin vs but y \in vs case leads to this conclusion. *)
          pose proof well_comm_subst_comm as [_ [_ [? _]]].
          eapply H0; eauto 2.
          - destruct (fv_decide y \{x}).
            + (* y = x \in vs. In this case vs \- \{x} \u \{y} = vs *)
              rewrite in_singleton in m0. subst.
              replace (vs \- \{ x} \u \{ x}) with vs; eauto.
              (* A rare case where replace leaving the proof of the equality last
                 is actually useful. *)
              apply fset_extens.
              * hnf. intros. rewrite in_union.
                destruct (fv_decide x0 \{x}); eauto.
                left. rewrite in_remove. split; eauto.
              * hnf. intros. rewrite in_union in H1. destruct H1.
                { rewrite in_remove in H1. destruct H1; eauto. }
                { rewrite in_singleton in H1. subst. assumption. }
            + (* y <> x. But then y \in vs. So y \in vs \- \{x} so vs \- \{x} \u
                 \{y} = vs \- \{x} *)
              assert (\{y} \c vs \- \{x}).
              { hnf. intros. rewrite in_singleton in *; subst.
                rewrite in_remove; eauto. }
              assert (vs \- \{x} \u \{y} = vs \- \{x}).
              { apply fset_extens.
                - hnf. intros. rewrite in_union, in_singleton in *.
                  destruct H5; eauto. subst.
                  hnf in H1. apply H1. rewrite in_singleton; eauto.
                - apply subset_union_weak_l. }
              rewrite H5. clear H1 H5.
              rewrite subst_env_fset_vars_notin_remove with (E := Delta1) (x := x);
                eauto.
              rewrite subst_env_fset_vars_notin_remove with (E := Delta2) (x := x);
                eauto.
          - rewrite dom_concat. repeat(rewrite subst_env_fset_vars_dom). eauto.
          - (* Observe that the init_binds_sub condition implies
               y \in (dom Delta1) \u (dom Delta2) *)
            specialize (H7 i').
            destruct H7; eauto. destruct H1 as [_ ?]. rename x0 into iy.
            rewrite <- subst_env_fset_vars_distrib_env.
            eapply subst_env_fset_vars_in_vs; eauto.
            rewrite in_union. right. rewrite in_singleton. reflexivity. }
        { (* y \notin vs *)
          rewrite dom_concat, notin_union in H6. destruct H6.
          rewrite subst_env_fset_vars_notin_remove with (E := Delta1) (x := x) in c;
            try assumption.
          rewrite subst_env_fset_vars_notin_remove with (E := Delta2) (x := x) in c;
            try assumption.
          pose proof well_comm_subst_comm as [_ [_ [? _]]].
          eapply H5 with
              (Delta :=
                 subst_env_fset_vars Delta1 (vs \- \{ x} \u \{ y}) committed &
                 x ~ committed &
                 subst_env_fset_vars Delta2 (vs \- \{ x} \u \{ y}) committed);
            eauto 2.
          - rewrite concat_empty_r.
            eapply well_commit_more_committed_lit with
                (Delta := subst_env_fset_vars Delta1 (vs \- \{ x}) committed &
                          x ~ committed &
                          subst_env_fset_vars Delta2 (vs \- \{ x}) committed);
              eauto 2.
            hnf. intros.
            repeat(match goal with
                   | [Hbin : binds ?x0 ?i (?D1 & ?D2) |- _] =>
                     apply binds_concat_inv in Hbin as [? | ?]; destruct_ands
                   end).
            + eauto using binds_concat_right,
              subst_env_fset_vars_more, subset_union_weak_l.
            + rewrite subst_env_fset_vars_dom in H6.
              eapply binds_single_inv in H8. destruct H8; subst.
              eapply binds_concat_left; eauto 2.
              rewrite subst_env_fset_vars_dom. assumption.
            + rewrite subst_env_fset_vars_dom in H6.
              apply binds_concat_left;
                eauto 3 using binds_concat_left, subst_env_fset_vars_more,
                subset_union_weak_l.
              rewrite subst_env_fset_vars_dom. assumption.
          - rewrite dom_concat. repeat(rewrite subst_env_fset_vars_dom). eauto.
          - rewrite <- subst_env_fset_vars_distrib_env.
            specialize (H7 i').
            destruct H7; eauto. destruct H6 as [_ ?]. rename x0 into iy.
            eapply subst_env_fset_vars_in_vs; eauto.
            rewrite in_union, in_singleton; eauto. } }
      { (* x \notin vs *)
        destruct (fv_decide y vs).
        { (* y \in vs *)
          (* In this case, H cannot be used directly, because: *)
          specialize (H Gamma1 x T' Gamma2 y).
          specialize (H (subst_env_fset_vars Delta1 vs committed)
                        i'
                        (subst_env_fset_vars Delta2 vs committed)
                        eq_refl H2 H3 H4 eq_refl).
          rewrite dom_concat, ? subst_env_fset_vars_dom, <- dom_concat in H.
          specialize (H H6).
          (* In particular, y \in vs means that
             (Delta1 [vs = committed]) & (Delta2 [vs = committed]) may
             substitute (y ~ iy) to (y ~ committed). But in H7 the init_binds_sub
             condition only ensures that iy <: i'. Indeed, this is not necessarily
             true if iy = free. However, substituting in a committed variable
             still preserves the fact that a term is well-committed. *)
          pose proof well_comm_subst_comm as [_ [_ [? _]]].
          eapply H0; eauto 2.
          - rewrite dom_concat. repeat(rewrite subst_env_fset_vars_dom). eauto.
          - (* Observe that the init_binds_sub condition implies
               y \in (dom Delta1) \u (dom Delta2) *)
            specialize (H7 i').
            destruct H7; eauto. destruct H1 as [_ ?]. rename x0 into iy.
            rewrite <- subst_env_fset_vars_distrib_env.
            eapply subst_env_fset_vars_in_vs; eauto. }
        { (* y \notin vs *)
          (* This is a case where the induction hypothesis H can be used directly. *)
          eapply H; eauto 2.
          - rewrite dom_concat. repeat(rewrite subst_env_fset_vars_dom).
            rewrite notin_union. auto.
          - hnf. intros.
            assert (i0 = i').
            { assert (binds x i'
                            (subst_env_fset_vars Delta1 vs committed & x ~ i' &
                             subst_env_fset_vars Delta2 vs committed))
                by (eapply binds_middle_eq; rewrite subst_env_fset_vars_dom;
                    rewrite dom_concat, notin_union in *; destruct_all; eauto).
              binds_eq. reflexivity. } subst.
            specialize (H7 i'). destruct H7; auto. rename x0 into j. destruct H1.
            exists j. split; auto.
            rewrite <- subst_env_fset_vars_distrib_env.
            eapply subst_env_fset_vars_notin_ignore; eauto. } }
    + assert (z \notin L) as Hfr by auto.
      specialize (H0 z Hfr); clear Hfr H.
      specialize (H0 Gamma1 x T' (Gamma2 & z ~ T)).
      specialize (H0 y Delta1 i' (Delta2 & z ~ free)).
      rewrite ? concat_assoc in H0; subst_open_fresh.
      rewrite <- map_single, <- concat_assoc, <- map_concat.
      assert (vs \u \{ z} /[ x -> y] = (vs /[ x -> y]) \u \{ z}).
      { unfold subst_var, VarsSubstVar.
        assert (z \notin \{ x}) as Hxz by auto.
        apply notin_singleton_swap in Hxz.
        cases_if.
        + rewrite in_union in C; destruct C;
            [|exfalso ; apply Hxz; auto].
          cases_if.
          apply fset_extens; unfold "\c";
            intros d;
            rewrite ? in_union, ? in_remove, ? in_union in *.
          * intros [[[Hin1 | Hin1] Hin2] | Hin]; auto.
          * intros [[[Hin1 Hin2] | Hin3] | Hin]; auto.
            rewrite in_singleton in Hin; subst d.
            left; split; auto.
            right; rewrite in_singleton; auto.
        + cases_if; auto. exfalso.
          change (~ x \in vs \u \{z}) with (x \notin vs \u \{z}) in C.
          rewrite notin_union in C. destruct C. eauto. }
      replace ((vs /[ x -> y]) \u \{ z}) with (vs \u \{ z} /[ x -> y])
        by eauto.
      eapply H0; eauto.
      * rewrite map_concat, concat_assoc, map_single.
        apply weaken; auto.
      * hnf. intros. apply binds_concat_inv in H1.
        destruct H1.
        { exfalso. apply binds_single_inv in H1. destruct H1; subst.
          repeat(rewrite notin_union in Frz); rewrite notin_singleton in Frz;
            destruct_ands; eauto. }
        { destruct H1. specialize (H7 _ H5). destruct_all. rename x0 into j.
          exists j. split; eauto. }
  - (* init-let *)
    init_fresh_constructor_extern; eauto; subst_open_fresh.
    notin_L; notin_apply. clear H1 H.
    specialize (H0 Gamma1 x T' (Gamma2 & z ~ T)).
    specialize (H0 y Delta1 i'0 (Delta2 & z ~ i)).
    rewrite ? concat_assoc in H0.
    assert (vs \u \{ z} /[ x -> y] = (vs /[ x -> y]) \u \{ z}).
    { unfold subst_var, VarsSubstVar.
      assert (z \notin \{ x}) as Hxz by auto.
      apply notin_singleton_swap in Hxz.
      cases_if.
      + rewrite in_union in C; destruct C;
          [|exfalso ; apply Hxz; auto].
        cases_if.
        apply fset_extens; unfold "\c";
          intros c;
          rewrite ? in_union, ? in_remove, ? in_union in *.
        * intros [[[Hin1 | Hin1] Hin2] | Hin]; auto.
        * intros [[[Hin1 Hin2] | Hin3] | Hin]; auto.
          rewrite in_singleton in Hin; subst c.
          left; split; auto.
          right; rewrite in_singleton; auto.
      + cases_if; auto.
        exfalso. apply C.
        rewrite in_union. left; auto. }
    rewrite <- H; clear H.
    rewrite <- map_single, <- concat_assoc, <- map_concat.
    eapply H0; eauto using init_binds_sub_push.
    + rewrite map_concat, concat_assoc, map_single.
      apply weaken; auto.
  - (* init-llit *)
    init_fresh_constructor_extern; eauto.
    notin_L; notin_apply.
    specialize (H0 Gamma1 x T' (Gamma2 & z ~ T)).
    specialize (H0 y Delta1 i' (Delta2 & z ~ committed)).
    rewrite ? concat_assoc in H0; subst_open_fresh.
    rewrite <- map_single, <- concat_assoc, <- map_concat.
    eapply H0; eauto using init_binds_sub_push.
    + rewrite map_concat, concat_assoc, map_single.
      apply weaken; auto.
Qed.

(** Substitution for terms *)
Lemma well_init_subst_term : forall Gamma1 x y T' Gamma2 Delta1 i' Delta2 vs t i,
      Gamma1 & x ~ T' & Gamma2 ⸴ Delta1 & x ~ i' & Delta2 ⸴ vs ⊢i t ∶ i ->
      x # Gamma2 ->
      x \notin (fv_env Gamma1 \u dom Delta1 \u dom Delta2) ->
      Gamma1 & (subst_env x y Gamma2) ⊢ trm_var (avar_f y) ∶ subst_var x y T' ->
      init_binds_sub x (Delta1 & x ~ i' & Delta2) y (Delta1 & Delta2) ->
      Gamma1 & (subst_env x y Gamma2) ⸴ Delta1 & Delta2 ⸴ vs /[x -> y] ⊢i subst_var x y t ∶ i.
Proof.
  intros. eapply well_init_substitution; eauto.
Qed.

Lemma well_init_subst_term_push : forall Gamma x y T' Delta i' vs t i,
      Gamma & x ~ T' ⸴ Delta & x ~ i' ⸴ vs ⊢i t ∶ i ->
      x \notin (fv_env Gamma \u dom Delta) ->
      Gamma ⊢ trm_var (avar_f y) ∶ subst_var x y T' ->
      init_binds_sub x (Delta & x ~ i') y Delta ->
      Gamma ⸴ Delta ⸴ vs /[x -> y] ⊢i subst_var x y t ∶ i.
Proof.
  intros.
  replace Gamma with (Gamma & (subst_env x y) empty) by auto.
  replace Delta with (Delta & empty) by auto.
  replace (Delta & x ~ i') with (Delta & x ~ i' & empty) in * by auto.
  replace (Gamma & x ~ T') with (Gamma & x ~ T' & empty) in * by auto.
  eapply well_init_subst_term; eauto.
  - rewrite map_empty, concat_empty_r; eauto.
  - rewrite ? concat_empty_r in *; auto.
Qed.

(** Substitution for commited terms *)
Lemma well_comm_subst_term : forall Gamma1 x y T' Gamma2 Delta1 i' Delta2 t,
    Gamma1 & x ~ T' & Gamma2 ⸴ Delta1 & x ~ i' & Delta2 ⊢c t ->
    x # Gamma2 ->
    x \notin fv_env Gamma1 ->
    Gamma1 & (subst_env x y Gamma2) ⊢ trm_var (avar_f y) ∶ subst_var x y T' ->
    x # (Delta1 & Delta2) ->
    init_binds_sub x (Delta1 & x ~ i' & Delta2) y (Delta1 & Delta2) ->
    Gamma1 & (subst_env x y Gamma2) ⸴ Delta1 & Delta2 ⊢c subst_var x y t.
Proof.
  intros. eapply well_init_substitution; eauto.
Qed.

Lemma well_comm_subst_term_push : forall Gamma x y T' Delta i' t,
    Gamma & x ~ T' ⸴ Delta & x ~ i' ⊢c t ->
    x \notin (fv_env Gamma \u dom Delta) ->
    Gamma ⊢ trm_var (avar_f y) ∶ subst_var x y T' ->
    init_binds_sub x (Delta & x ~ i') y Delta ->
    Gamma ⸴ Delta ⊢c subst_var x y t.
Proof.
  intros.
  replace Gamma with (Gamma & (subst_env x y) empty) by auto.
  replace Delta with (Delta & empty) by auto.
  replace (Delta & x ~ i') with (Delta & x ~ i' & empty) in * by auto.
  replace (Gamma & x ~ T') with (Gamma & x ~ T' & empty) in * by auto.
  eapply well_comm_subst_term; eauto.
  - rewrite map_empty, concat_empty_r; eauto.
  - rewrite ? concat_empty_r in *; auto.
Qed.

(** Strengthening committed var *)
Lemma init_var_strengthen_commit : forall Gamma Delta vs x y i,
    init_var Delta (vs \u \{ x}) y i ->
    binds x committed Delta ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_var (avar_f y) ∶ i.
Proof.
  intros. constructor.
  eauto using init_var_strengthen_vars_commit.
Qed.

Lemma init_strengthen_vs_commit_ind :
  (forall Gamma Delta t,   Gamma ⸴ Delta ⊢c t   -> Gamma ⸴ Delta ⊢c t)   /\
  (forall Gamma Delta avs, Gamma ⸴ Delta ⊢c avs -> Gamma ⸴ Delta ⊢c avs) /\
  (forall Gamma Delta l,   Gamma ⸴ Delta ⊢c l   -> Gamma ⸴ Delta ⊢c l)   /\
  (forall Gamma Delta vs_x t i,
      Gamma ⸴ Delta ⸴ vs_x ⊢i t ∶ i ->
      forall vs x,
        vs_x = vs \u \{x} ->
        binds x committed Delta ->
        Gamma ⸴  Delta ⸴ vs ⊢i t ∶ i) /\
  (forall Gamma Delta vs_x avs is,
      Gamma ⸴ Delta ⸴ vs_x ⊢i avs :: is ->
      forall vs x,
        vs_x = vs \u \{x} ->
        binds x committed Delta ->
        Gamma ⸴ Delta ⸴ vs ⊢i avs :: is).
Proof with eauto.
  apply well_init_mut_ind; intros; subst;
    sympl; eauto 4.
  - eapply init_var_strengthen_commit...
  - eapply init_lit_free...
    + eapply well_commit_more_committed_lit...
      hnf. intros.
      apply binds_to_dom in H1 as ?.
      rewrite subst_env_fset_vars_dom in H3.
      eapply dom_to_binds in H3. destruct H3.
      destruct (fv_decide x0 (vs0 \u \{x}));
        try(rewrite in_union in m; destruct m).
      * eapply subst_env_fset_vars_in_vs...
      * rewrite in_singleton in H4. subst. clear H1.
        destruct (fv_decide x vs0);
          eauto using subst_env_fset_vars_in_vs, subst_env_fset_vars_notin_ignore.
      * apply (subst_env_fset_vars_notin_vs_inv _ _ n) in H1.
        clear H3. eauto using subst_env_fset_vars_notin_ignore.
    + intros. assert (x0 \notin \{x} \u L) by eauto. clear H3.
      rewrite notin_union in H1. destruct_ands.
      eapply H0...
      rewrite <- union_assoc. rewrite <- union_assoc.
      rewrite (union_comm \{x} \{x0}). reflexivity.
  - econstructor...
    intros. assert (x0 \notin L \u \{x}) as x0_fresh by eauto.
    clear H1. repeat (rewrite notin_union in x0_fresh).
    destruct x0_fresh as [x0_notin_L x0_neq_x].
    specialize (H0 x0 x0_notin_L
                   (vs0 \u \{ x0}) x).
    apply H0... apply union_comm_comm_assoc_assoc.
Qed.

Lemma init_strengethen_vs_commit : forall Gamma Delta vs t x i,
    Gamma ⸴ Delta ⸴ vs \u \{ x} ⊢i t ∶ i ->
    binds x committed Delta ->
    Gamma ⸴ Delta ⸴ vs ⊢i t ∶ i.
Proof.
  introv t_init_with_x x_commit.
  pose proof init_strengthen_vs_commit_ind.
  destruct H as [_ [_ [_ [init_weaken_commit _]]]].
  specialize (init_weaken_commit Gamma Delta (vs \u \{x})
                                 t i t_init_with_x
                                 vs x eq_refl x_commit).
  assumption.
Qed.

Lemma init_strengethen_vs : forall Gamma Delta vs x i t i',
    (Gamma ⸴ Delta ⸴ vs         ⊢i trm_var (avar_f x) ∶ i) ->
    (Gamma ⸴ Delta ⸴ vs \u \{x} ⊢i t                  ∶ i') ->
    (Gamma ⸴ Delta ⸴ vs         ⊢i t                  ∶ i').
Proof with eauto.
  introv x_init t_init_with_x.
  inversions x_init.
  - inversions H3.
    + eapply init_strengethen_vs_commit; eauto.
    + eapply init_strengethen_vs_commit; eauto.
    + rewrite member_union_same in t_init_with_x...
    + rewrite member_union_same in t_init_with_x...
    + rewrite member_union_same in t_init_with_x...
  - inversions H.
    eapply init_strengethen_vs_commit; eauto.
Qed.

Lemma well_init_ty_bnd :
  (forall Gamma Delta t,
      Gamma ⸴ Delta ⊢c t ->
      forall G1 x T G2,
        Gamma = (G1 & x ~ (open x T) & G2) ->
        G1 & x ~ typ_bnd T & G2 ⸴ Delta ⊢c t) /\

  (forall Gamma Delta avs,
      Gamma ⸴ Delta ⊢c avs ->
      forall G1 x T G2,
        Gamma = (G1 & x ~ (open x T) & G2) ->
        G1 & x ~ typ_bnd T & G2 ⸴ Delta ⊢c avs) /\

  (forall Gamma Delta l,
      Gamma ⸴ Delta ⊢c l ->
      forall G1 x T G2,
        Gamma = (G1 & x ~ (open x T) & G2) ->
        G1 & x ~ typ_bnd T & G2 ⸴ Delta ⊢c l) /\

  (forall Gamma Delta vs t i,
      Gamma ⸴ Delta ⸴ vs ⊢i t ∶ i ->
      forall G1 x T G2,
        Gamma = (G1 & x ~ (open x T) & G2) ->
        G1 & x ~ typ_bnd T & G2 ⸴ Delta ⸴ vs ⊢i t ∶ i) /\

    (forall Gamma Delta vs avs is,
      Gamma ⸴ Delta ⸴ vs ⊢i avs :: is ->
      forall G1 x T G2,
        Gamma = (G1 & x ~ (open x T) & G2) ->
        G1 & x ~ typ_bnd T & G2 ⸴ Delta ⸴ vs ⊢i avs :: is).

Proof with eauto.
  apply well_init_mut_ind; intros; subst; sympl; eauto 4;
    try(solve[econstructor; eauto; intros; rewrite <- concat_assoc; eauto]).
  - econstructor...
    pose proof ty_open_implies_ty_bnd as [? _].
    eapply H1...
  - econstructor... intros.
    rewrite <- concat_assoc. rewrite <- concat_assoc. apply H...
  - econstructor...
    pose proof ty_open_implies_ty_bnd as [? _].
    eapply H1...
Qed.

Corollary ty_open_implies_ty_bnd_init : forall Gamma Delta vs t i x T,
      Gamma & x ~ (open x T) ⸴ Delta ⸴ vs ⊢i t ∶ i ->
      Gamma & x ~ typ_bnd T  ⸴ Delta ⸴ vs ⊢i t ∶ i.
Proof.
  intros.
  pose proof well_init_ty_bnd as [_ [_ [_ [? _]]]].
  rewrite <- (concat_empty_r (Gamma & x ~ typ_bnd T)); eauto.
Qed.
