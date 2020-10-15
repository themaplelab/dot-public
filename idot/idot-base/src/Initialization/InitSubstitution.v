(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import PreTyping Typing GeneralTyping Weakening.
Require Import SubstitutionClass Substitution.
Require Import Initialization InitLookup InitLookupLemmas InitVarSubtyping InitTyping InitWeakening.
Require Import Effects EffectSubstitution.
Require Import BndIntro.

Implicit Types (i : init_typ) (t : trm) (l : lit) (avs : avars).

(** * Infrastructure for Substitution Lemma for Initialization System *)

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

(** * Substitution Lemma for Initialization System *)
(** Substitution for initialization for list of variables.
    This following lifts the substitution lemma for initailization lookup to
    lists of variables. *)
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
      apply Hxy in H3.
      eauto using init_var_committed_binds.
    * eauto using binds_middle_neq_binds.
Qed.

(** We prove the substitution lemma for the initailization system via a mutual
    induction on the initailization typing for terms, initialization typing for
    lists of variables, and committed typing for terms and literals, *)
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
        Gamma1 & (subst_env x y Gamma2) ⸴ Delta1 & Delta2 ⸴ vs /[x -> y] ⊢i subst_var x y t ∶ i) /\
  (forall Gamma Delta vs avs is',
      Gamma ⸴ Delta ⸴ vs ⊢i avs :: is' ->
      forall Gamma1 x T' Gamma2 y Delta1 i' Delta2,
        Gamma = (Gamma1 & x ~ T' & Gamma2) ->
        x # Gamma2 ->
        x \notin fv_env Gamma1 ->
        Gamma1 & (subst_env x y Gamma2) ⊢ trm_var (avar_f y) ∶ subst_var x y T' ->
        Delta = Delta1 & x ~ i' & Delta2 -> x # (Delta1 & Delta2) ->
        init_binds_sub x (Delta1 & x ~ i' & Delta2) y (Delta1 & Delta2) ->
        Gamma1 & (subst_env x y Gamma2) ⸴ Delta1 & Delta2 ⸴ vs /[x -> y] ⊢i (avs /[x -> y]) :: is').
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
    + clear h.
      intros x' ys HlTs Hfr.
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
        unfold subst_var, VarsSubstVar; cases_if; auto.
      }
      fold vars in Hrm; rewrite Hrm in H; clear Hrm.
      rewrite ? concat_assoc,
      ? map_concat,
      <- ? subst_single,
      <- ? subst_singles_rev_to_list in H by auto.
      rewrite ? concat_assoc in H.
      rewrite ? subst_open_vars_commut_fresh_length in H
        by auto.
      eapply H; clear H i0; auto.
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
        rewrite in_union. left; auto.
    }
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

(** Specialize Initailization Substitution for terms *)
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
        Gamma ⸴ Delta ⸴ vs ⊢i t ∶ i) /\
  (forall Gamma Delta vs_x avs is,
      Gamma ⸴ Delta ⸴ vs_x ⊢i avs :: is ->
      forall vs x,
        vs_x = vs \u \{x} ->
        binds x committed Delta ->
        Gamma ⸴ Delta ⸴ vs ⊢i avs :: is).
Proof with eauto.
  apply well_init_mut_ind; intros; subst;
    sympl; eauto 4.
  + eapply init_var_strengthen_commit...
  + econstructor...
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
  - induction H3; eauto.
    + eapply init_strengethen_vs_commit; eauto.
    + rewrite member_union_same in t_init_with_x...
    + rewrite member_union_same in t_init_with_x...
  - inversions H.
    eapply init_strengethen_vs_commit; eauto.
Qed.

(** [BndIntro] lemmas for the initailization system *)
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
