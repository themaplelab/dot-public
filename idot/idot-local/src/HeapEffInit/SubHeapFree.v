(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Typing Effects
        InitVar InitVarSubtyping InitTyping InitWeakening
        GeneralTyping.
Require Import HeapCorrespondence HeapUpdate.
Require Import HeapCommit WellPointed HeapItemFree.

Implicit Types (Delta : init_ctx) (Sigma : heap) (ℰ : eff_ctx).

(** * Free Sub heaps *)
(* Denotes a valid free topmost heap as ℰ captures only the effects for one
   object *)
Definition free_sub_heap (ℰ : eff_ctx) (Sigma : heap) (Delta : init_ctx) :=
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
                free_heap_item Delta ℰ x itm.

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

Section Domains.
  Hint Resolve free_heap_item_in_effs free_heap_item_in_inits : core.
  Hint Resolve binds_to_dom : core.

  Lemma free_sub_heap_effs_dom_inits : forall ℰ Delta Sigma x,
      free_sub_heap ℰ Sigma Delta ->
      x \in dom ℰ -> x \in dom Delta.
  Proof.
    unfold free_sub_heap; introv Hfsh Hin.
    apply dom_to_binds in Hin. destruct Hin as [v HbiE].
    specialize (Hfsh _ _ HbiE) as [_ [itm [HbiS Hfhi]]].
    eauto.
  Qed.

  Lemma free_sub_heap_effs_dom_inits' : forall ℰ Delta Sigma,
      free_sub_heap ℰ Sigma Delta ->
      forall x, x \in dom ℰ -> x \in dom Delta.
  Proof.
    eauto using free_sub_heap_effs_dom_inits.
  Qed.

  Lemma free_sub_heap_effs_dom_heap : forall ℰ Delta Sigma x,
      free_sub_heap ℰ Sigma Delta ->
      x \in dom ℰ -> x \in dom Sigma.
  Proof.
    unfold free_sub_heap; introv Hfsh Hin.
    apply dom_to_binds in Hin. destruct Hin as [v HbiE].
    specialize (Hfsh _ _ HbiE) as [_ [itm [HbiS Hfhi]]].
    eauto.
  Qed.

  Hint Resolve free_sub_heap_effs_dom_inits : core.

  Lemma free_sub_heap_fresh_inits : forall ℰ Delta Sigma x,
      free_sub_heap ℰ Sigma Delta ->
      x # Delta ->
      x # ℰ.
  Proof. intros. intro Contra; eauto. Qed.

  Hint Resolve free_sub_heap_effs_dom_heap : core.

  Lemma free_sub_heap_fresh_heap : forall ℰ Delta Sigma x,
      free_sub_heap ℰ Sigma Delta ->
      x # Sigma ->
      x # ℰ.
  Proof. intros. intro Contra; eauto. Qed.
End Domains.
Local Hint Resolve
      free_sub_heap_fresh_heap
      free_sub_heap_fresh_inits : core.

(** ** Weakening Lemmas for [free_sub_heap] *)
Lemma free_sub_heap_empty : forall Sigma Delta,
    free_sub_heap empty Sigma Delta.
Proof.
  unfold free_sub_heap.
  intros; exfalso; eauto using binds_empty_inv.
Qed.
Local Hint Resolve free_sub_heap_empty : core.

(** ** Pushing Lemmas for [free_sub_heap] *)
Local Hint Resolve
      free_heap_item_weaken_inits free_heap_item_weaken_effs
      free_heap_item_push_obj free_heap_item_first_obj
      binds_push_fresh binds_push_neq : core.

Lemma free_sub_heap_push_fresh : forall ℰ Sigma Delta x itm i,
    free_sub_heap ℰ Sigma Delta ->
    x # Sigma ->
    x # Delta ->
    free_sub_heap ℰ (Sigma & x ~ itm) (Delta & x ~ i).
Proof.
  unfold free_sub_heap.
  introv Hfsh HfrS HfrD HbiE.
  specialize (Hfsh _ _ HbiE) as [Heqs [itm' [HbiD Hfhi]]].
  split; auto. exists itm'; eauto.
Qed.

Lemma free_sub_heap_push_obj : forall ℰ Sigma Delta x T ds,
    free_sub_heap ℰ Sigma Delta ->
    x # Sigma ->
    x # Delta ->
    free_sub_heap (ℰ & x ~ heap_defs_effs x (heap_defs_of_defs ds))
                  (Sigma & x ~ item_obj T (heap_defs_of_defs ds))
                  (Delta & x ~ free).
Proof.
  unfold free_sub_heap.
  introv Hfsh HfrS HfrD HbiE.
  apply binds_push_inv in HbiE.
  destruct HbiE as [[Heq Heq'] | [Hneq HbiE]]; subst;
    split; eauto; try solve [eexists; eauto];
      pose proof (Hfsh _ _ HbiE) as [?H [itm [?H ?H]]]; eauto.
  exists itm; split; eauto.
Qed.
Local Hint Resolve free_sub_heap_push_obj : core.

Lemma free_sub_heap_first_obj : forall ℰ Sigma Delta x T ds,
    free_sub_heap ℰ Sigma Delta ->
    x # Sigma ->
    x # Delta ->
    free_sub_heap (x ~ (heap_defs_effs x (heap_defs_of_defs ds)))
                  (Sigma & x ~ item_obj T (heap_defs_of_defs ds))
                  (Delta & x ~ free).
Proof.
  intros. rewrite <- (concat_empty_l (x ~ (heap_defs_effs _ _))).
  eauto.
Qed.

(** * Update Lemmas *)
Lemma free_sub_heap_correspondence_other : forall Sigma ℰ Delta x a y Sigma',
    free_sub_heap ℰ Sigma Delta ->
    heap_update Sigma x a y Sigma' ->
    x # ℰ ->
    free_sub_heap ℰ Sigma' Delta.
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

Lemma free_sub_heap_commited_other : forall ℰ Sigma Delta x,
    free_sub_heap ℰ Sigma Delta ->
    binds x committed Delta ->
    x # ℰ.
Proof.
  intros. intro Contra.
  unfold free_sub_heap in H.
  pose proof (dom_to_binds Contra) as [itm Hbic].
  pose proof (H _ _ Hbic) as [Heqs [itm' [Hbi Hfhi]]].
  inversions Hfhi. inversions H1; destruct_ands.
  destruct_all.
  apply (binds_functional H2) in H0. subst.
  apply init_var_sub_free in H4. destruct H4; congruence.
Qed.

Lemma free_sub_heap_correspondence_committed : forall Sigma ℰ Delta x a y Sigma',
    free_sub_heap ℰ Sigma Delta ->
    heap_update Sigma x a y Sigma' ->
    binds x committed Delta ->
    free_sub_heap ℰ Sigma' Delta.
Proof.
  eauto using free_sub_heap_commited_other,
  free_sub_heap_correspondence_other.
Qed.

Lemma free_sub_heap_correspondence : forall Gamma Sigma ℰ Delta x a y Sigma' effs,
    heap_correspond Gamma Sigma ->
    free_sub_heap ℰ Sigma Delta ->
    heap_update Sigma x a y Sigma' ->
    binds x effs ℰ ->
    well_pointed Delta ℰ y ->
    exists ℰ' effs',
      eff_update ℰ x effs' ℰ' /\
      eff_remove effs x a effs' /\
      free_sub_heap ℰ' Sigma' Delta.
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
    inversions Hfhi. unfold free_heap_defs in H6.
    destruct H6 as [?HbiD [?HbiE _]]; repeat binds_eq.
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

Lemma free_sub_heap_commit_other : forall ℰ Sigma Delta Delta',
    free_sub_heap ℰ Sigma Delta ->
    (forall x init, x \in dom ℰ -> binds x init Delta -> binds x init Delta') ->
    more_committed Delta Delta' ->
    free_sub_heap ℰ Sigma Delta'.
Proof.
  unfold free_sub_heap; intros.
  apply H in H2. destruct H2 as [Heqs [itm [Hbi Hfhi]]]. split; auto.
  exists itm; split; eauto using free_heap_item_commit_other.
Qed.

Lemma free_sub_heap_commit_sub_other : forall ℰ Sigma Delta Delta',
    free_sub_heap ℰ Sigma Delta ->
    (forall (x : var), x \in dom ℰ ->
                        forall (i : init_typ),
                          binds x i Delta ->
                          exists i', binds x i' Delta' /\ init_sub i' i) ->
    more_committed Delta Delta' ->
    free_sub_heap ℰ Sigma Delta'.
Proof.
  introv Hfsh Hinitsub Hmc. hnf.
  introv Hbin. hnf in Hfsh.
  apply Hfsh in Hbin as [Hsame [itm [Hbin Hfhi]]].
  split; auto. exists itm. split; eauto using free_heap_item_sub_other.
Qed.

Lemma eff_ctx_corr_one_notin : forall ℰ effs x Sigma Delta,
    x \notin dom effs ->
    free_sub_heap ℰ Sigma Delta ->
    eff_ctx_corr_one ℰ effs ->
    not (binds x nil ℰ) ->
    x \notin dom ℰ.
Proof.
    (* If x ∈ dom ℰ then x binds to some effs' in ℰ. Since effs' ≠ nil, by Hfsh,
     (x, a) ∈ effs' and so by Hcorr, (x, a) ∈ effs. But this would mean that
     x ∈ dom effs. A contradiction. *)
  introv Hxnineffs Hfsh Hcorr Hxnnil. hnf in Hcorr.
  unfold notin. unfold not. introv Hxinℰ.
  apply dom_to_binds in Hxinℰ as [effs' Hxbinℰ].
  specialize (Hcorr _ _ Hxbinℰ).
  hnf in Hfsh. specialize (Hfsh _ _ Hxbinℰ) as [Hlblsame _].
  destruct effs'; eauto.
  destruct p as [x' a].
  assert ((x', a) \in from_list ((x', a) :: effs')) as Hxain by
      (rewrite from_list_cons, in_union, in_singleton; auto).
    specialize (Hlblsame _ _ Hxain); subst.
    specialize (Hcorr _ Hxain).
    eauto using from_list_dom.
Qed.
