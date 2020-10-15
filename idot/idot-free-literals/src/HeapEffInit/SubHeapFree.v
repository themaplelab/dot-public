(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Typing Effects InitVar InitTyping InitWeakening GeneralTyping.
Require Import HeapCorrespondence HeapUpdate.
Require Import HeapCommit WellPointed HeapEffects HeapItemFree.

Implicit Types (Delta : init_ctx) (Sigma : heap) (ℰ : eff_ctx).

(** * Free Sub heaps *)
(* Denotes a valid free topmost heap as ℰ captures only the effects for one
   object *)
Definition free_sub_heap (Gamma : ctx) (ℰ : eff_ctx) (Sigma : heap)
           (Delta : init_ctx) :=
  forall x effs,
    (* The next two lines simply say that ℰ only contains effects for a single
       variable x *)
    binds x effs ℰ ->
    (forall y a, (y,a) \in (from_list effs) -> y = x) /\
    (* For that single variable x, the heap Sigma bounds x to some item itm *)
    exists itm, binds x itm Sigma /\
                (* And this heap item itm is free with relation to x. That is,
                   (by inverting the definitions of free_heap_item)
                   - x is free
                   - ℰ states that the null fields of x, (i.e. the defs in itm
                     must be assigned
                   - If x.a = z for some z then either z is committed
                     according to Delta or it's free but will be assigned according
                     to ℰ. This should be equivalent to pointing to a free object
                     in the same free sub-heap *)
                free_heap_item Gamma Delta ℰ x itm.

(** * Effect Correspondence *)
(** This is needed for preservation *)
Definition eff_ctx_corr_one (ℰ : eff_ctx) effs :=
  (* effs corresponds with ℰ means that for each (x, effs') \in ℰ,
     one has that effs' \subseteq effs. In essence effs says that at least
     as many fields in effs' should be assigned *)
  (forall x effs', binds x effs' ℰ ->
                   forall eff, (eff \in (from_list effs')) ->
                               (eff \in (from_list effs))).

Lemma eff_ctx_corr_one_empty : forall effs,
    eff_ctx_corr_one empty effs.
Proof.
  unfold eff_ctx_corr_one; intros; exfalso.
  eauto using binds_empty_inv.
Qed.

Lemma eff_ctx_corr_one_push_nil : forall ℰ effs x,
    eff_ctx_corr_one ℰ effs ->
    eff_ctx_corr_one (ℰ & x ~ nil) effs.
Proof.
  unfold eff_ctx_corr_one.
  intros * Heff.
  intros y effs' Hbix.
  pose proof (binds_push_inv Hbix) as [[Heq Hnil] | [Hneq Hbix']]; subst; eauto.
  intros eff.
  rewrite from_list_nil, in_empty; contradiction.
Qed.

Section Domains.
  Hint Resolve free_heap_item_in_effs free_heap_item_in_inits : core.
  Hint Resolve binds_to_dom : core.

  Lemma free_sub_heap_effs_dom_inits : forall Gamma ℰ Delta Sigma x,
      free_sub_heap Gamma ℰ Sigma Delta ->
      x \in dom ℰ -> x \in dom Delta.
  Proof.
    unfold free_sub_heap; introv Hfsh Hin.
    apply dom_to_binds in Hin. destruct Hin as [v HbiE].
    specialize (Hfsh _ _ HbiE) as [_ [itm [HbiS Hfhi]]].
    destruct Hfhi.
    - hnf in H. destruct_ands. eauto.
    - destruct_ands. eauto.
  Qed.

  Lemma free_sub_heap_effs_dom_inits' : forall Gamma ℰ Delta Sigma,
      free_sub_heap Gamma ℰ Sigma Delta ->
      forall x, x \in dom ℰ -> x \in dom Delta.
  Proof.
    eauto using free_sub_heap_effs_dom_inits.
  Qed.

  Lemma free_sub_heap_effs_dom_heap : forall Gamma ℰ Delta Sigma x,
      free_sub_heap Gamma ℰ Sigma Delta ->
      x \in dom ℰ -> x \in dom Sigma.
  Proof.
    unfold free_sub_heap; introv Hfsh Hin.
    apply dom_to_binds in Hin. destruct Hin as [v HbiE].
    specialize (Hfsh _ _ HbiE) as [_ [itm [HbiS Hfhi]]].
    eauto.
  Qed.

  Hint Resolve free_sub_heap_effs_dom_inits : core.

  Lemma free_sub_heap_fresh_inits : forall Gamma ℰ Delta Sigma x,
      free_sub_heap Gamma ℰ Sigma Delta ->
      x # Delta ->
      x # ℰ.
  Proof. intros. intro Contra; eauto. Qed.

  Hint Resolve free_sub_heap_effs_dom_heap : core.

  Lemma free_sub_heap_fresh_heap : forall Gamma ℰ Delta Sigma x,
      free_sub_heap Gamma ℰ Sigma Delta ->
      x # Sigma ->
      x # ℰ.
  Proof. intros. intro Contra; eauto. Qed.
End Domains.
Local Hint Resolve
      free_sub_heap_fresh_heap
      free_sub_heap_fresh_inits : core.

(** ** Weakening Lemmas for [free_sub_heap] *)
Lemma free_sub_heap_empty : forall Gamma Sigma Delta,
    free_sub_heap Gamma empty Sigma Delta.
Proof.
  unfold free_sub_heap.
  intros; exfalso; eauto using binds_empty_inv.
Qed.
Local Hint Resolve free_sub_heap_empty : core.

(** ** Pushing Lemmas for [free_sub_heap] *)
Local Hint Resolve
      free_heap_item_weaken_inits free_heap_item_weaken_effs
      free_heap_item_weaken_ctx
      free_heap_item_push_obj free_heap_item_first_obj
      binds_push_fresh binds_push_neq : core.

Lemma free_sub_heap_push_fresh : forall Gamma ℰ Sigma Delta x T itm i,
    free_sub_heap Gamma ℰ Sigma Delta ->
    x # Gamma ->
    x # Sigma ->
    x # Delta ->
    free_sub_heap (Gamma & x ~ T) ℰ (Sigma & x ~ itm) (Delta & x ~ i).
Proof.
  unfold free_sub_heap.
  introv Hfsh HfrG HfrS HfrD HbiE.
  specialize (Hfsh _ _ HbiE) as [Heqs [itm' [HbiD Hfhi]]].
  split; auto. exists itm'. split; eauto.
Qed.

Lemma free_sub_heap_push_lit : forall Gamma ℰ Sigma Delta x T l,
    free_sub_heap Gamma ℰ Sigma Delta ->
    x # Gamma ->
    x # Sigma ->
    x # Delta ->
    Gamma ⸴ subst_env_fset_vars Delta (dom ℰ) committed ⊢c l ->
    free_sub_heap (Gamma & x ~ T)
                  (ℰ & x ~ nil)
                  (Sigma & x ~ item_lit l)
                  (Delta & x ~ free).
Proof.
  unfold free_sub_heap.
  introv Hfsh HfrG HfrS HfrD Hcom HbiE.
  apply binds_push_inv in HbiE.
  assert ((forall (y : var) (a : trm_label), (y, a) \in from_list nil -> y = x)) as Hnil.
  { intros; rewrite from_list_nil, in_empty in *; contradiction. }
  destruct HbiE as [[Heq Heq'] | [Hneq HbiE]]; subst.
  - split; eauto.
    exists (item_lit l); split; auto.
    apply free_heap_lit; repeat_split_right; auto.
    + rewrite empty_def; auto.
    + rewrite dom_concat, dom_single.
      rewrite subst_env_fset_vars_distrib_env.
      rewrite subst_env_fset_vars_in_vs_single
        by (rewrite in_union, in_singleton; auto).
      rewrite subst_env_fset_vars_ignore_fresh by auto.
      apply commit_weaken; auto.
      rewrite subst_env_fset_vars_dom; auto.
  - split; eauto.
    + apply Hfsh; auto.
    + apply Hfsh in HbiE. destruct HbiE as [_ [itm [Hbi Hfhi]]].
      exists itm; split.
      * apply binds_push_neq; eauto.
      * apply free_heap_item_weaken_ctx; auto 2.
        apply free_heap_item_weaken_inits; auto 2.
        apply free_heap_item_weaken_effs; auto 2.
        eauto using free_sub_heap_fresh_heap.
Qed.

Lemma free_sub_heap_push_obj : forall Gamma ℰ Sigma Delta x T ds,
    free_sub_heap Gamma ℰ Sigma Delta ->
    x # Gamma ->
    x # Sigma ->
    x # Delta ->
    free_sub_heap (Gamma & x ~ typ_bnd T)
                  (ℰ & x ~ heap_defs_effs x (heap_defs_of_defs ds))
                  (Sigma & x ~ item_obj T (heap_defs_of_defs ds))
                  (Delta & x ~ free).
Proof.
  unfold free_sub_heap.
  introv Hfsh HfrG HfrS HfrD HbiE.
  apply binds_push_inv in HbiE.
  destruct HbiE as [[Heq Heq'] | [Hneq HbiE]]; subst;
    split; eauto; try solve [eexists; eauto];
      pose proof (Hfsh _ _ HbiE) as [?H [itm [?H ?H]]]; eauto;
        exists itm; split; eauto.
Qed.
Local Hint Resolve free_sub_heap_push_obj : core.

Lemma free_sub_heap_first_obj : forall Gamma ℰ Sigma Delta x T ds,
    free_sub_heap Gamma ℰ Sigma Delta ->
    x # Gamma ->
    x # Sigma ->
    x # Delta ->
    free_sub_heap (Gamma & x ~ typ_bnd T)
                  (x ~ (heap_defs_effs x (heap_defs_of_defs ds)))
                  (Sigma & x ~ item_obj T (heap_defs_of_defs ds))
                  (Delta & x ~ free).
Proof.
  intros. rewrite <- (concat_empty_l (x ~ (heap_defs_effs _ _))).
  eauto.
Qed.

(** * Update Lemmas *)
Lemma free_sub_heap_correspondence_other : forall Gamma Sigma ℰ Delta x a y Sigma',
    free_sub_heap Gamma ℰ Sigma Delta ->
    heap_update Sigma x a y Sigma' ->
    x # ℰ ->
    free_sub_heap Gamma ℰ Sigma' Delta.
Proof.
  unfold heap_update, free_sub_heap.
  intros * Hfsh.
  intros [T [hds [hds' [Sigma1 [Sigma2 [?Heq [HfrS2 [Hup ?Heq]]]]]]]];
    subst.
  intros Hfr x' effs Hbi.
  assert (x' <> x) as Hneq
      by (intro contra; subst; eauto using binds_to_dom).
  specialize (Hfsh _ _ Hbi) as [Heqs [itm [HbiS Hfhi]]];
    split; auto.
  exists itm; split; eauto using binds_middle_update.
Qed.

Lemma free_sub_heap_commited_other : forall Gamma ℰ Sigma Delta x,
    free_sub_heap Gamma ℰ Sigma Delta ->
    binds x committed Delta ->
    x # ℰ.
Proof.
  intros. intro Contra.
  unfold free_sub_heap in H.
  pose proof (dom_to_binds Contra) as [itm Hbic].
  pose proof (H _ _ Hbic) as [Heqs [itm' [Hbi Hfhi]]].
  inversions Hfhi. inversions H1; destruct_ands.
  repeat binds_eq.
  destruct_ands. repeat binds_eq.
Qed.

Lemma free_sub_heap_correspondence_committed : forall Gamma
                                                      Sigma ℰ Delta x a y Sigma',
    free_sub_heap Gamma ℰ Sigma Delta ->
    heap_update Sigma x a y Sigma' ->
    binds x committed Delta ->
    free_sub_heap Gamma ℰ Sigma' Delta.
Proof.
  eauto using free_sub_heap_commited_other,
  free_sub_heap_correspondence_other.
Qed.

Lemma free_sub_heap_correspondence : forall Gamma Sigma ℰ Delta x a y Sigma' effs,
    heap_correspond Gamma Sigma ->
    free_sub_heap Gamma ℰ Sigma Delta ->
    heap_update Sigma x a y Sigma' ->
    binds x effs ℰ ->
    well_pointed Delta ℰ y ->
    exists ℰ' effs',
      eff_update ℰ x effs' ℰ' /\
      eff_remove effs x a effs' /\
      free_sub_heap Gamma ℰ' Sigma' Delta.
Proof.
  unfold heap_update, free_sub_heap.
  intros * Hcorr Hfsh.
  intros [T [hds [hds' [Sigma1 [Sigma2 [?Heq [HfrS2 [Hup ?Heq]]]]]]]];
    subst.
  intros HxEEp Hwp.

  pose proof (eff_update_exists (heap_defs_effs x hds') (binds_to_dom HxEEp))
    as [ℰ' Heup].
  exists ℰ' (heap_defs_effs x hds'); repeat_split_right; auto.
  - specialize (Hfsh _ _ HxEEp) as [_ [?itm [?HbiS ?Hfhi]]].
    assert (binds x (item_obj T hds)
                  (Sigma1 & x ~ item_obj T hds & Sigma2)) by auto.
    binds_eq; clear H0.
    unfold heap_correspond in Hcorr.
    destruct Hcorr as [?H ?Htis].
    pose proof (binds_to_dom HbiS) as HdinS.
    assert (HdinG: x \in dom Gamma) by congruence; clear HdinS.
    specialize (Htis _ HdinG); clear HdinG.
    inversions Htis; repeat binds_eq.
    inversions Hfhi. unfold free_heap_defs in H7.
    destruct H7 as [?HbiD [?HbiE _]]; repeat binds_eq.
    eapply defs_update_eff_remove; eauto.
  - intros. pose proof (var_decide x0 x) as [Heq | Hneq]; subst; auto.
    + pose proof (proj32 Heup).
      pose proof (Hfsh _ _ HxEEp) as [Heqs [itm' [HbiS1 Hfhi]]].
      assert (binds x (item_obj T hds)
                    (Sigma1 & x ~ item_obj T hds & Sigma2)) by auto.
      repeat binds_eq. split; eauto.
      exists (item_obj T hds'); split;
        eauto using free_heap_item_update.
    + pose proof Heup as Heup''.
      unfold eff_update in Heup.
      destruct Heup as [HEE' [Hbi' Heup']].
      pose proof (dom_update_binds_inv (x:=x) HEE' Heup')
        as Hdmup.
      pose proof (Hfsh _ _ (Hdmup _ _ Hneq H)) as
          [?Heqs [itm' [HbiS1 Hfhi]]]; split; auto.
      exists itm'; split;
        eauto using free_heap_item_update_other,
        binds_middle_update.
Qed.

Lemma free_sub_heap_commit_other : forall Gamma ℰ Sigma Delta Delta',
    free_sub_heap Gamma ℰ Sigma Delta ->
    (forall x init, x \in dom ℰ -> binds x init Delta -> binds x init Delta') ->
    more_committed Delta Delta' ->
    free_sub_heap Gamma ℰ Sigma Delta'.
Proof.
  unfold free_sub_heap; intros.
  apply H in H2. destruct H2 as [Heqs [itm [Hbi Hfhi]]]. split; auto.
  exists itm; split; eauto using free_heap_item_commit_other.
Qed.
