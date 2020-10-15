(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Typing Effects Initialization InitLookupLemmas InitTyping InitWeakening GeneralTyping.
Require Import HeapCorrespondence HeapUpdate.
Require Import CommittedSubHeap CommittedSubHeapLemmas.
Require Import EffectUpdate HeapEffects.
Require Import HeapDefsPointsTo WellPointed.
Require Import FreeItems FreeItemLemmas HeapItemUpdateLemmas.
Require Import FreeSubHeapSingle EffectCorrespondence FreeSubHeapSingleLemmas.
Require Import FreeSubHeapStack InertInitContexts.

Implicit Types (Delta : init_ctx) (Sigma : heap) (ℰ : eff_ctx).

Local Hint Constructors free_sub_heaps : core.

(** * Lemmas about Stacks of Free Subheaps *)
(** Freshness lemmas *)
Lemma free_sub_heaps_effs_to_inits : forall Gamma Delta Sigma ℰs x,
    free_sub_heaps Gamma Delta Sigma ℰs ->
    x \in (list_dom_union ℰs) ->
    x \in dom Delta.
Proof.
  induction 1; simpl; intros.
  - rewrite in_empty in *; exfalso; auto.
  - rewrite in_union in *; destruct_ors;
      eauto using free_sub_heap_effs_dom_inits.
Qed.
Local Hint Resolve free_sub_heaps_effs_to_inits : core.

Lemma free_sub_heaps_fresh_var : forall Gamma Delta Sigma ℰs x,
    free_sub_heaps Gamma Delta Sigma ℰs ->
    x # Delta ->
    x \notin (list_dom_union ℰs).
Proof.
  introv Hfsh Hfr HContra.
  apply Hfr; eauto.
Qed.
Local Hint Resolve free_sub_heaps_fresh_var : core.

Lemma free_sub_heaps_fresh_var_all_notin : forall Gamma Delta Sigma ℰ ℰs x v,
    free_sub_heaps Gamma Delta Sigma ℰs ->
    all_notin (dom ℰ) (list_dom_union ℰs) ->
    x # Delta ->
    all_notin (dom (ℰ & x ~ v)) (list_dom_union ℰs).
Proof.
  intros. unfold all_notin.
  intros x' Hxs. rewrite dom_push, in_union, in_singleton in Hxs.
  destruct Hxs; subst; eauto.
Qed.
Hint Resolve free_sub_heaps_fresh_var_all_notin : core.

(** Pushing lemmas *)
(** *** Lemma: Allocating Literals *)
Lemma free_sub_heaps_committed_push : forall Gamma Delta Sigma ℰs x l T,
    free_sub_heaps Gamma Delta Sigma ℰs ->
    x # Gamma ->
    x # Delta ->
    x # Sigma ->
    Gamma ⸴ Delta ⊢c l ->
    free_sub_heaps (Gamma & x ~ T)
                   (Delta & x ~ committed)
                   (Sigma & x ~ (item_lit l)) ℰs.
Proof.
  induction 1; intros; constructor;
    eauto using well_committed_lit_push, free_sub_heap_push_fresh.
Qed.

Lemma free_sub_heaps_free_push : forall Gamma Delta Sigma ℰs x itm T,
    free_sub_heaps Gamma Delta Sigma ℰs ->
    x # Gamma ->
    x # Delta ->
    x # Sigma ->
    free_sub_heaps (Gamma & x ~ T)
                   (Delta & x ~ free)
                   (Sigma & x ~ itm) ℰs.
Proof.
  induction 1; intros; constructor;
    eauto using well_committed_free_push, free_sub_heap_push_fresh.
Qed.

(** *** Lemma: Allocating Free Objects *)
Lemma free_sub_heaps_obj_push : forall Gamma Delta Sigma ℰ ℰs x ds T,
    free_sub_heaps Gamma Delta Sigma (ℰ :: ℰs) ->
    x # Gamma ->
    x # Delta ->
    x # Sigma ->
    free_sub_heaps (Gamma & x ~ typ_bnd T)
                   (Delta & x ~ free)
                   (Sigma & x ~ (item_obj T (heap_defs_of_defs ds)))
                   (ℰ & x ~ (heap_defs_effs x (heap_defs_of_defs ds)) :: ℰs).
Proof.
  inversion 1; subst; intros.
  eauto using free_sub_heaps_free_push,
  free_sub_heap_push_obj, free_sub_heap_fresh_inits.
Qed.

(** *** Lemma: Allocating a New Free Subheap *)
Lemma free_sub_heaps_new_obj_push : forall Gamma Delta Sigma ℰs x ds T,
    free_sub_heaps Gamma Delta Sigma ℰs ->
    x # Gamma ->
    x # Delta ->
    x # Sigma ->
    free_sub_heaps (Gamma & x ~ typ_bnd T)
                   (Delta & x ~ free)
                   (Sigma & x ~ (item_obj T (heap_defs_of_defs ds)))
                   ((x ~ heap_defs_effs x (heap_defs_of_defs ds)) :: ℰs).
Proof.
  induction 1; intros;
    constructor;
    eauto using well_committed_free_push,
    free_sub_heap_push_obj,
    free_sub_heap_first_obj,
    free_sub_heap_empty,
    free_sub_heaps_nil,
    free_sub_heaps_cons,
    free_sub_heaps_free_push,
    all_notin_nil, all_notin_single,
    free_sub_heap_fresh_inits.
Qed.

(** * Init Correspondence for Heap Updates *)
(** Inversion Lemmas for [free_sub_heaps] *)
Lemma free_sub_heaps_well_committed : forall Gamma Sigma ℰs Delta,
    free_sub_heaps Gamma Delta Sigma ℰs ->
    well_committed_heap Gamma Delta Sigma.
Proof.
  induction 1; eauto.
Qed.

Lemma free_sub_heaps_dom_eq_ty_init : forall Gamma Sigma ℰs Delta,
    free_sub_heaps Gamma Delta Sigma ℰs ->
    dom Gamma = dom Delta.
Proof.
  intros * Hfshs.
  apply free_sub_heaps_well_committed in Hfshs.
  unfold well_committed_heap in *;
    destruct_all; auto.
Qed.

Lemma free_sub_heaps_dom_eq_init_heap : forall Gamma Sigma ℰs Delta,
    free_sub_heaps Gamma Delta Sigma ℰs ->
    dom Delta = dom Sigma.
Proof.
  intros * Hfshs.
  apply free_sub_heaps_well_committed in Hfshs.
  unfold well_committed_heap in *;
    destruct_all; auto.
Qed.

Lemma free_sub_heaps_dom_eq_ty_heap : forall Gamma Sigma ℰs Delta,
    free_sub_heaps Gamma Delta Sigma ℰs ->
    dom Gamma = dom Sigma.
Proof.
  intros * Hfshs.
  apply free_sub_heaps_well_committed in Hfshs.
  unfold well_committed_heap in *;
    destruct_all; congruence.
Qed.

(** Update Lemmas for free_sub_heaps *)
(** *** Lemma: Assigning to Committed Objects *)
Lemma free_sub_heaps_write_committed_other : forall Gamma Sigma ℰs Delta x a y Sigma',
    free_sub_heaps Gamma Delta Sigma ℰs ->
    heap_update Sigma x a y Sigma' ->
    binds x committed Delta ->
    binds y committed Delta ->
    free_sub_heaps Gamma Delta Sigma' ℰs.
Proof.
  induction 1; intros;
    eauto using well_committed_heap_update_committed,
    free_sub_heap_correspondence_committed.
Qed.

Lemma free_sub_heaps_write_other : forall Gamma Sigma ℰs Delta x a y Sigma',
    free_sub_heaps Gamma Delta Sigma ℰs ->
    heap_update Sigma x a y Sigma' ->
    x \notin (list_dom_union ℰs) ->
    well_committed_heap Gamma Delta Sigma' ->
    free_sub_heaps Gamma Delta Sigma' ℰs.
Proof.
  intros Gamma Sigma ℰs Delta x a y Sigma'.
  induction 1; intros; eauto.
  rewrite notin_cons_list_dom_union in H3.
  destruct H3. eauto using free_sub_heap_correspondence_other.
Qed.

(** *** Lemma: Assigning to Free Objects *)
(** We need heap correspondence in the following lemma to ensure definitons are
    well-formed. Otherwise, an object can have both [{a = Some y}] and [{a =
    None}] as fields after an update, and the [eff_remove] condition would not
    hold. *)
Lemma free_sub_heaps_write_top : forall Gamma Delta Sigma ℰ ℰs x a y Sigma' effs,
    heap_correspond Gamma Sigma ->
    free_sub_heaps Gamma Delta Sigma (ℰ :: ℰs) ->
    well_pointed Delta ℰ y ->
    heap_update Sigma x a y Sigma' ->
    binds x effs ℰ ->
    exists ℰ' effs',
      eff_update ℰ x effs' ℰ' /\
      eff_remove effs x a effs' /\
      free_sub_heaps Gamma Delta Sigma' (ℰ' :: ℰs).
Proof.
  intros * Hhc Hfshs Hwp Hhup HbiE.
  pose proof (free_sub_heaps_well_committed Hfshs) as Hwc.
  inversion Hfshs as [| ?G ?D ?S ?E ?Es ?Hani ?Hfsh ?Hfshs']; subst.
  pose proof (free_sub_heap_correspondence Hhc Hfsh Hhup HbiE Hwp)
    as [ℰ' [effs' [Heup [Her Hfsh']]]].
  exists ℰ' effs'.
  repeat_split_right; auto 1.
  constructor.
  - pose proof Heup as [HdeqE _].
    rewrite HdeqE in Hani; auto.
  - auto.
  - pose proof (Hfsh _ _ HbiE) as [_ [?itm [_ Hfhi]]].
    inversion Hfhi as [? ? ? ? ? [Hbif _]]; subst.
    pose proof (well_committed_heap_update_free Hwc Hbif Hhup) as Hwc'.
    pose proof (all_notin_fresh _ HbiE Hani) as Hnil.
    eauto using free_sub_heaps_write_other.
Qed.

(** Lemmas for comitting entire subheaps *)
Lemma committed_delta_exists : forall ℰ Delta,
    (forall x, x \in dom ℰ -> x \in dom Delta) ->
    exists Delta', dom Delta = dom Delta' /\
          (forall x, x \in dom ℰ -> binds x committed Delta') /\
          (forall x init, x \notin dom ℰ -> binds x init Delta -> binds x init Delta').
Proof.
  induction ℰ using env_ind.
  - intros; exists Delta; repeat_split_right; auto.
    intros; rewrite dom_empty in *; exfalso; eauto using in_empty_inv.
  - intros.
    assert (H' : forall x' : var, x' \in dom ℰ -> x' \in dom Delta).
    { rewrite dom_push in H. intros.
      assert (x' \in \{ x} \/ x' \in dom ℰ) by auto.
      rewrite <- in_union in H1. eauto. }
    specialize (IHℰ _ H') as [Delta' [Heq [HED' HDE]]].
    pose proof (in_dom_decide x ℰ) as [Hin | Hnin].
    + exists Delta'; repeat_split_right; auto.
      intros; rewrite dom_push, in_union, in_singleton in *.
      destruct H0; subst; auto.
    + assert (x \in dom Delta)
        by (apply H; rewrite dom_push, in_union, in_singleton; auto).
      rewrite Heq in H0. apply dom_to_binds in H0. destruct H0 as [v' Hbi].
      apply binds_to_middle in Hbi as [Delta1 [Delta2 [Heq' Hfr]]]; subst.
      exists (Delta1 & x ~ committed & Delta2); repeat_split_right.
      * simpl_dom; auto.
      * intros. rewrite dom_push, in_union, in_singleton in H0.
        destruct H0; subst; auto. apply HED' in H0.
        apply binds_middle_inv in H0; destruct_ors; destruct_ands; subst; auto.
      * intros. rewrite dom_push, notin_union, notin_singleton in H0.
        destruct H0 as [Hneq HfrE]. specialize (HDE _ _ HfrE H1).
        apply binds_middle_inv in HDE;
          destruct_ors; destruct_ands; subst; auto; congruence.
Qed.

Lemma committed_delta_is_more_committed : forall ℰ Delta Delta',
    (forall x, x \in dom ℰ -> binds x committed Delta') ->
    (forall x init, x \notin dom ℰ -> binds x init Delta -> binds x init Delta') ->
    more_committed Delta Delta'.
Proof.
  intros. unfold more_committed. intros.
  pose proof (in_dom_decide x ℰ) as [Hin | Hfr]; eauto.
Qed.

Lemma special_dom_keep : forall (ℰ : eff_ctx) (ℰs : list eff_ctx) Delta Delta',
    all_notin (dom ℰ) (list_dom_union ℰs) ->
    (forall x init, x # ℰ -> binds x init Delta -> binds x init Delta') ->
    (forall x init, x \in (list_dom_union ℰs) -> binds x init Delta -> binds x init Delta').
Proof.
  intros. eapply H0; eauto 2 using all_notin_inv.
Qed.

Lemma free_sub_heaps_commit_other : forall Gamma Delta Delta' Sigma ℰs,
  free_sub_heaps Gamma Delta Sigma ℰs ->
  (forall x init, x \in (list_dom_union ℰs) -> binds x init Delta -> binds x init Delta') ->
  more_committed Delta Delta' ->
  well_committed_heap Gamma Delta' Sigma ->
  free_sub_heaps Gamma Delta' Sigma ℰs.
Proof.
  induction 1; intros; constructor; auto.
  - apply free_sub_heap_commit_other with (Delta:=Delta) (Delta':=Delta'); auto.
    intros; apply H2; eauto. simpl. rewrite in_union; auto.
  - apply IHfree_sub_heaps; auto.
    intros; apply H2; eauto. simpl. rewrite in_union; auto.
Qed.

(* TODO : Typeclassify this *)
Lemma committed_delta_is_inert : forall ℰ Delta Delta',
    inert_inits Delta ->
    dom Delta = dom Delta' ->
    (forall x, x \in dom ℰ -> binds x committed Delta') ->
    (forall x init, x \notin dom ℰ -> binds x init Delta -> binds x init Delta') ->
    inert_inits Delta'.
Proof.
  unfold inert_inits. intros.
  pose proof (in_dom_decide x ℰ) as [Hin | Hfr].
  - specialize (H1 _ Hin); binds_eq; auto.
  - pose proof (binds_to_dom H3) as Hin'.
    rewrite <- H0 in Hin'. apply dom_to_binds in Hin'.
    destruct Hin' as [?v Hbi'].
    pose proof (H _ _ Hbi'). pose proof (H2 _ _ Hfr Hbi').
    binds_eq; auto.
Qed.

(** Effect Correspondence for committing *)
Lemma eff_ctx_corr_empty_heap_def_effs : forall Delta Sigma ℰ x effs,
    free_sub_heap ℰ Sigma Delta ->
    eff_ctx_corr_one ℰ nil ->
    binds x effs ℰ ->
    binds x free Delta ->
    exists T hds, binds x (item_obj T hds) Sigma /\
             heap_defs_effs x hds = nil.
Proof.
  unfold free_sub_heap, eff_ctx_corr_one. intros.
  specialize (H _ _ H1) as [Heq [itm [HbiS Hfhi]]].
  inversion Hfhi; subst. unfold free_heap_defs in H.
  destruct_ands. binds_eq. clear H5. exists T hds; split; auto.
  pose proof (fset_cases (from_list (heap_defs_effs x hds)))
    as [?H | [?x ?Contra]].
  - destruct (heap_defs_effs x hds); eauto.
    exfalso. rewrite from_list_cons in H3.
    rewrite <- in_empty with (A := effect) (x := p).
    rewrite <- H3. rewrite in_union. left. apply in_singleton_self.
  - destruct (in_empty_inv (H0 _ _ H1 _ Contra)).
Qed.

Lemma empty_eff_corr_delta_well_commited : forall Gamma Delta Sigma ℰ Delta',
    well_committed_heap Gamma Delta Sigma ->
    free_sub_heap ℰ Sigma Delta ->
    eff_ctx_corr_one ℰ nil ->
    dom Delta = dom Delta' ->
    (forall x, x \in dom ℰ -> binds x committed Delta') ->
    (forall x init, x \notin dom ℰ -> binds x init Delta -> binds x init Delta') ->
    well_committed_heap Gamma Delta' Sigma.
Proof.
  intros. eapply more_committed_sub_heap; eauto.
  unfold free_sub_heap, eff_ctx_corr_one in *.
  intros. pose proof (committed_delta_is_more_committed H3 H4) as Hmc.
  pose proof (in_dom_decide x ℰ) as [Hin | Hfr].
  - apply dom_to_binds in Hin. destruct Hin as [eff Hbi].
    pose proof (H1 _ _ Hbi). pose proof (H0 _ _ Hbi) as [?H ?H].
    destruct H9 as [itm' [HbiS Hfhi]]. binds_eq; clear H9.
    inversions Hfhi. econstructor.
    destruct H9 as [Hbif [HbiE Hpt]].
    assert (forall x, x \in heap_defs_points_to hds -> binds x committed Delta').
    { intros. apply Hpt in H9. destruct H9; auto 2. destruct H9; auto 2. }
    pose proof (eff_ctx_corr_empty_heap_def_effs H0 H1 Hbi Hbif) as [? [? [? ?]]].
    binds_eq. eapply committed_defs_inv; eauto.
  - clear H1. pose proof (binds_to_dom H5) as Hin. rewrite <- H2 in Hin.
    apply dom_to_binds in Hin. destruct Hin as [?i ?Hbi].
    pose proof (H4 _ _ Hfr Hbi). binds_eq.
    unfold well_committed_heap in H; destruct_ands.
    eapply more_committed_item; eauto.
Qed.

(** *** Lemma Promoting A Free Subheap *)
Lemma free_sub_heaps_promote : forall Gamma Delta Sigma ℰ ℰs,
  free_sub_heaps Gamma Delta Sigma (ℰ :: ℰs) ->
  eff_ctx_corr_one ℰ nil ->
  exists Delta', dom Delta = dom Delta' /\
        (forall x, x \in dom ℰ -> binds x committed Delta') /\
        (forall x init, x \notin dom ℰ -> binds x init Delta -> binds x init Delta') /\
        free_sub_heaps Gamma Delta' Sigma ℰs.
Proof.
  intros * Hfshs Hecco.
  inversion Hfshs as [| ?Gamma ?Delta ?Sigma ?ℰ ?ℰs Hani Hfsh Hfshs']; subst.
  pose proof (committed_delta_exists (free_sub_heap_effs_dom_inits' Hfsh))
       as [Delta' [Hdeq [Hcomm Hkits]]].
  pose proof (committed_delta_is_more_committed Hcomm Hkits) as Hmc.
  exists Delta'; repeat_split_right; auto.
  pose proof (free_sub_heaps_well_committed Hfshs) as Hwc.
  pose proof (empty_eff_corr_delta_well_commited
                Hwc Hfsh Hecco Hdeq Hcomm Hkits) as Hwc'.
  pose proof (special_dom_keep _ Hani Hkits) as Hkits'.
  eauto using free_sub_heaps_commit_other.
Qed.

(* Note that [eff_ctx_corr_one ℰ nil] is the same as all the bindings being
   empty. *)
Lemma eff_ctx_corr_empty_map : forall ℰ,
    eff_ctx_corr_one ℰ nil <->
    (forall x effs, binds x effs ℰ -> effs = nil).
Proof.
  unfold eff_ctx_corr_one.
  intros; split.
  - intros Hecco x E Hbi.
    induction E as [| [y a] E _]; [auto|].
    pose proof (Hecco x _ Hbi (y, a)) as Contra.
    rewrite from_list_nil, from_list_cons in Contra.
    exfalso; eapply in_empty_inv, Contra, is_in_union_singleton_r.
  - intros Hbe x effs Hbi.
    pose proof (Hbe _ _ Hbi); subst; auto.
Qed.


(** Effect Correspondence for updates *)
Lemma free_sub_heap_eff_corr_update_other : forall Delta Sigma ℰ x a y effs' effs,
  free_sub_heap ℰ Sigma Delta ->
  ⊢e trm_asn (avar_f x) a (avar_f y) ∶ effs' ->
  x # ℰ ->
  eff_ctx_corr_one ℰ (effs' ++ effs) ->
  eff_ctx_corr_one ℰ effs.
Proof.
  introv Hfsh Hef Hfr Heco. inversions Hef; auto.
  simpl in Heco.
  unfold eff_ctx_corr_one in *. intros x' effs' HbiE eff Hin.
  pose proof (Heco x' effs' HbiE eff Hin) as Hin'.
  rewrite from_list_cons in *.
  rewrite in_union, in_singleton in Hin'.
  destruct Hin' as [Heq | Hin']; subst; auto.
  exfalso. unfold free_sub_heap in Hfsh.
  pose proof (Hfsh _ _ HbiE) as [Heq _].
  apply Heq in Hin; subst. apply binds_to_dom in HbiE. auto.
Qed.

Lemma free_sub_heaps_eff_corr_update_other : forall Gamma Delta Sigma ℰ ℰs x a y effs' effs effss,
  free_sub_heaps Gamma Delta Sigma (ℰ :: ℰs) ->
  ⊢e trm_asn (avar_f x) a (avar_f y) ∶ effs' ->
  x # ℰ ->
  eff_ctx_corr (ℰ :: ℰs) ((effs' ++ effs) :: effss)%list ->
  eff_ctx_corr (ℰ :: ℰs) (effs :: effss)%list.
Proof.
  inversion 1; subst; inversion 3; subst; constructor; auto.
  eauto using free_sub_heap_eff_corr_update_other.
Qed.

Lemma free_sub_heaps_eff_corr_update_committed :
  forall Gamma Delta Sigma ℰ ℰs x a y effs' effs effss,
  free_sub_heaps Gamma Delta Sigma (ℰ :: ℰs) ->
  ⊢e trm_asn (avar_f x) a (avar_f y) ∶ effs' ->
  binds x committed Delta ->
  eff_ctx_corr (ℰ :: ℰs) ((effs' ++ effs) :: effss)%list ->
  eff_ctx_corr (ℰ :: ℰs) (effs :: effss)%list.
Proof.
  inversion 1; subst.
  eauto 3 using free_sub_heap_commited_other,
  free_sub_heaps_eff_corr_update_other.
Qed.

Lemma free_sub_heap_eff_corr_update : forall Delta Sigma ℰ ℰ' x a y effs effs' effs1 effs2,
  free_sub_heap ℰ Sigma Delta ->
  ⊢e trm_asn (avar_f x) a (avar_f y) ∶ effs1 ->
  binds x effs ℰ ->
  eff_update ℰ x effs' ℰ' ->
  eff_remove effs x a effs' ->
  eff_ctx_corr_one ℰ (effs1 ++ effs2) ->
  eff_ctx_corr_one ℰ' effs2.
Proof.
  introv Hfsh Hef HbiE Heup Her Heco.
  unfold eff_ctx_corr_one in *. intros x3 effs3 HbiE3 eff3 Hin3.
  unfold eff_update in Heup. destruct Heup as [Hdeq [Hbi' Hbin]].
  pose proof  (var_decide x3 x) as [Heq3 | Hneq3]; subst.
  - pose proof (binds_functional HbiE3 Hbi'); subst.
    clear Hbin. specialize (Heco _ _ HbiE).
    unfold eff_remove in Her. destruct Her as [Hnin [_ Hsb]].
    assert (Hneq: eff3 <> (x,a)) by congruence.
    pose proof (Heco _ (Hsb _ Hin3)) as Hinu. inversions Hef.
    * rewrite from_list_concat, from_list_nil in Heco.
      rewrite union_empty_l in *; auto.
    * rewrite from_list_concat, from_list_cons, from_list_nil in Heco, Hinu.
      rewrite union_empty_r in Heco, Hinu.
      rewrite in_union, in_singleton in Hinu. destruct Hinu; auto; congruence.
  - clear Her HbiE Hbi'.
    pose proof (dom_update_binds_inv Hdeq Hbin) as Hbin'.
    specialize (Hbin' _ _ Hneq3 HbiE3). specialize (Heco _ _ Hbin' _ Hin3).
    inversions Hef; rewrite ? union_empty_l, ? in_union, ?in_singleton in *;
      auto.
    rewrite from_list_concat, from_list_cons, from_list_nil, union_empty_r in Heco.
    rewrite in_union, in_singleton in Heco.
    destruct Heco; auto. subst.
    unfold free_sub_heap in Hfsh. specialize (Hfsh _ _ Hbin').
    destruct Hfsh as [Hfsh _]. specialize (Hfsh _ _ Hin3); congruence.
Qed.

Lemma free_sub_heaps_eff_corr_update :
  forall Gamma Delta Sigma ℰ ℰ' ℰs x a y effs effs' effs1 effs2 effss,
  free_sub_heaps Gamma Delta Sigma (ℰ :: ℰs) ->
  ⊢e trm_asn (avar_f x) a (avar_f y) ∶ effs1 ->
  binds x effs ℰ ->
  eff_update ℰ x effs' ℰ' ->
  eff_remove effs x a effs' ->
  eff_ctx_corr (ℰ :: ℰs) ((effs1 ++ effs2) :: effss)%list ->
  eff_ctx_corr (ℰ' :: ℰs) (effs2 :: effss).
Proof.
  inversion 1; subst; inversion 5; subst; constructor; auto.
  eauto using free_sub_heap_eff_corr_update.
Qed.

Lemma notin_sub_heaps_effs : forall ℰs G Delta Sigma x,
    free_sub_heaps G Delta Sigma ℰs ->
    x # Sigma ->
    x \notin list_dom_union ℰs.
Proof with eauto 3.
  induction ℰs; intros; simpl...
  inversions H. rename H0 into Hfrx. rename H3 into Hnin.
  rename H7 into Hfrsh. rename H8 into Hfrshs. rename a into ℰ.
  rewrite notin_union; split...
  unfold free_sub_heap in Hfrsh. hnf.
  intros Hxbin. apply dom_to_binds in Hxbin.
  destruct Hxbin as [effs Hxbin].
  specialize (Hfrsh x effs Hxbin).
  destruct Hfrsh as [_ Hcontra].
  destruct Hcontra as [itm [Hcontra _]].
  apply binds_to_dom in Hcontra...
Qed.
