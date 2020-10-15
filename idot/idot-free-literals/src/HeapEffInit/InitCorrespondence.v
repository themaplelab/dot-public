(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Typing Effects InitVar InitTyping InitWeakening GeneralTyping.
Require Import HeapCorrespondence HeapUpdate.
Require Import HeapCommit HeapEffects HeapItemFree SubHeapFree.

Implicit Types (Delta : init_ctx) (Sigma : heap) (ℰ : eff_ctx).

(** * Unions of lists and list notin *)
Definition all_notin {A} (xs ys : fset A) :=
  forall x, x \in xs -> x \notin ys.

Fixpoint list_dom_union {A} (Es : list (env A)) :=
  match Es with
  | nil => \{}
  | (E :: Es)%list => dom E \u list_dom_union Es
  end.

(** * Stacks of Free Sub heaps *)
(* The effect context for a free_sub-heaps indicate which fields should be
   assigned in the sub-heaps *)
Inductive free_sub_heaps :
  ctx -> init_ctx -> heap -> list eff_ctx -> Prop :=
(* If everything is well-committed then there needs to be no effects *)
| free_sub_heaps_nil : forall Gamma Delta Sigma,
    well_committed_heap Gamma Delta Sigma ->
    free_sub_heaps Gamma Delta Sigma nil
(* Otherwise,  *)
| free_sub_heaps_cons : forall Gamma Delta Sigma ℰ ℰs,
    all_notin (dom ℰ) (list_dom_union ℰs) ->
    (* Recall that free_sub_heap ℰ Sigma Delta essentially says that
       ℰ marks all the effects and points-to relationship of a single variable x
       in the heap Sigma.
       Inlining rules for free_sub_heap:
       - x is free according to Delta
       - ℰ states that the null fields of x must be assigned
       - If x.a = z for some z then either z is committed according to Delta or
         it's free but will be assigned according to ℰ (pointing to something
         in the same free topmost subheap)
       Basically this should say that ℰ contains effect information for the
       topmost subheap of Sigma *)
    free_sub_heap Gamma ℰ Sigma Delta ->
    (* This just says that ℰs allows you to add more free subheaps to the
       bottom *)
    free_sub_heaps Gamma Delta Sigma ℰs ->
    free_sub_heaps Gamma Delta Sigma (ℰ :: ℰs).
Local Hint Constructors free_sub_heaps : core.

(** * Effects correspondence for Free Sub heaps *)
(** This is required for preservation *)
Inductive eff_ctx_corr : list eff_ctx -> list effects -> Prop :=
| eff_ctx_corr_nil : eff_ctx_corr nil nil
(* Essentially this says that the list of effects (effs :: effs) assigns at least as
   many things in the effect context (ℰ :: ℰs) *)
| eff_ctx_corr_cons : forall ℰ ℰs effs effss,
    eff_ctx_corr ℰs effss ->
    eff_ctx_corr_one ℰ effs ->
    eff_ctx_corr (ℰ :: ℰs) (effs :: effss).

(** Freshness lemmas *)
Lemma all_notin_nil : forall {A} xs,
  all_notin xs (list_dom_union (A:=A) nil).
Proof.
  unfold all_notin, list_dom_union.
  intros. intro Contra. rewrite in_empty in Contra.
  auto.
Qed.

Lemma in_cons_list_dom_union : forall {A} x (E : env A) Es,
    x \in dom E \/ x \in (list_dom_union Es) <->
    x \in (list_dom_union (E :: Es)).
Proof.
  intros. split; simpl; rewrite in_union; auto.
Qed.

Lemma notin_cons_list_dom_union : forall {A} x (E : env A) Es,
    x \notin (list_dom_union (E :: Es)) <->
    x \notin dom E /\ x \notin (list_dom_union Es).
Proof.
  unfold notin; intros. split; intros.
  - rewrite <- in_cons_list_dom_union in H; auto.
  - rewrite <- in_cons_list_dom_union.
    destruct H; intro Contra; destruct Contra; auto.
Qed.

Lemma all_notin_single : forall {A} x (v : A) (E : env A) Es,
  x # E ->
  x \notin (list_dom_union Es) ->
  all_notin (dom (x ~ v)) (list_dom_union (E :: Es)).
Proof.
  intros. unfold all_notin; intros x' Heq.
  rewrite dom_single, in_singleton in Heq; subst.
  intro Contra. rewrite <- in_cons_list_dom_union in Contra.
  destruct Contra; auto.
Qed.

Lemma all_notin_fresh : forall {A} x (v : A) (E : env A) (Es : list (env A)),
    binds x v E ->
    all_notin (dom E) (list_dom_union Es) ->
    x \notin (list_dom_union Es).
Proof.
  unfold all_notin; introv Hbi Hni.
  apply Hni. apply (binds_to_dom Hbi).
Qed.

Lemma all_notin_inv : forall {A} (xs ys : fset A) y,
    all_notin xs ys ->
    y \in ys ->
    y \notin xs.
Proof.
  unfold all_notin. intros. intro Contra.
  apply H in Contra; eauto.
Qed.

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

Lemma free_sub_heaps_free_lit_push : forall Gamma Delta Sigma ℰ ℰs x l T,
    free_sub_heaps Gamma Delta Sigma (ℰ :: ℰs) ->
    Gamma ⸴ subst_env_fset_vars Delta (dom ℰ) committed ⊢c l ->
    x # Gamma ->
    x # Delta ->
    x # Sigma ->
    free_sub_heaps (Gamma & x ~ T)
                   (Delta & x ~ free)
                   (Sigma & x ~ (item_lit l))
                   (ℰ & (x ~ nil) :: ℰs).
Proof.
  intros * Hfshs Hcoml HfrG HfrD HfrS.
  inversion Hfshs as [| ? ? ? ? ? Hani Hfsh Hfshs']; subst.
  apply free_sub_heaps_cons.
  - eauto using free_sub_heaps_fresh_var_all_notin.
  - eauto using free_sub_heap_push_lit.
  - eauto using free_sub_heaps_free_push.
Qed.

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
Lemma free_sub_heaps_write_committed_other : forall Gamma Sigma ℰs Delta x a y Sigma',
    heap_correspond Gamma Sigma ->
    free_sub_heaps Gamma Delta Sigma ℰs ->
    heap_update Sigma x a y Sigma' ->
    binds x committed Delta ->
    binds y committed Delta ->
    free_sub_heaps Gamma Delta Sigma' ℰs.
Proof.
  induction 2; intros;
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
(** Inertness for Initialization *)
Definition inert_inits Delta :=
  forall x init, binds x init Delta ->
            init = free \/ init = committed.

Lemma inert_inits_empty : inert_inits empty.
Proof.
  unfold inert_inits; intros;
    exfalso; eauto using binds_empty_inv.
Qed.
Hint Resolve inert_inits_empty : core.

Lemma inert_inits_push : forall Delta x i,
    inert_inits Delta ->
    x # Delta ->
    i = free \/ i = committed ->
    inert_inits (Delta & x ~ i).
Proof.
  unfold inert_inits; introv Hii Hfr Hi Hbi.
  apply binds_push_inv in Hbi;
    destruct Hbi as [[Heq Heq'] | [Hneq Hbi]]; subst; eauto.
Qed.
Hint Resolve inert_inits_push : core.

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
Lemma eff_ctx_corr_empty_heap_def_effs : forall Gamma Delta Sigma ℰ x effs,
    free_sub_heap Gamma ℰ Sigma Delta ->
    eff_ctx_corr_one ℰ nil ->
    binds x effs ℰ ->
    binds x free Delta ->
    (exists T hds, binds x (item_obj T hds) Sigma /\
                   heap_defs_effs x hds = nil) \/
    (exists l, binds x (item_lit l) Sigma).
Proof.
  unfold free_sub_heap, eff_ctx_corr_one. intros.
  specialize (H _ _ H1) as [Heq [itm [HbiS Hfhi]]].
  inversion Hfhi; subst. unfold free_heap_defs in H.
  destruct_ands. binds_eq. clear H5.
  pose proof (fset_cases (from_list (heap_defs_effs x hds)))
    as [?H | [?x ?Contra]].
  - left; exists T hds; split; auto.
    destruct (heap_defs_effs x hds); eauto.
    exfalso. rewrite from_list_cons in H3.
    rewrite <- in_empty with (A := effect) (x := p).
    rewrite <- H3. rewrite in_union. left. apply in_singleton_self.
  - left; exists T hds; split; auto. destruct (in_empty_inv (H0 _ _ H1 _ Contra)).
  - right. exists l; auto.
Qed.

Lemma empty_eff_corr_delta_well_commited : forall Gamma Delta Sigma ℰ Delta',
    well_committed_heap Gamma Delta Sigma ->
    free_sub_heap Gamma ℰ Sigma Delta ->
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
    inversions Hfhi.
    + econstructor.
      destruct H9 as [Hbif [HbiE Hpt]].
      assert (forall x, x \in heap_defs_points_to hds -> binds x committed Delta').
      { intros. apply Hpt in H9. destruct H9; auto 2. destruct H9; auto 2. }
      pose proof (eff_ctx_corr_empty_heap_def_effs H0 H1 Hbi Hbif) as
          [[? [? [? ?]]] | [? ?]].
      * binds_eq. eapply committed_defs_inv; eauto.
      * binds_eq.
    + econstructor.
      destruct H9 as [Hbif [HbiE Hpt]].
      pose proof (eff_ctx_corr_empty_heap_def_effs H0 H1 Hbi Hbif) as
          [[? [? [? ?]]] | [? ?]].
      * binds_eq.
      * binds_eq.
        apply more_committed_lit with
            (Delta := subst_env_fset_vars Delta (dom ℰ) committed); eauto.
        hnf. intros. eauto using subst_env_fset_vars_already_subst.
  - clear H1. pose proof (binds_to_dom H5) as Hin. rewrite <- H2 in Hin.
    apply dom_to_binds in Hin. destruct Hin as [?i ?Hbi].
    pose proof (H4 _ _ Hfr Hbi). binds_eq.
    unfold well_committed_heap in H; destruct_ands.
    eapply more_committed_item; eauto.
Qed.

(** Effect Correspondence for updates *)
Lemma free_sub_heap_eff_corr_update_other : forall Gamma
                                                   Delta Sigma ℰ x a y effs' effs,
  free_sub_heap Gamma ℰ Sigma Delta ->
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

Lemma free_sub_heap_eff_corr_update : forall Gamma Delta Sigma
                                             ℰ ℰ' x a y effs effs' effs1 effs2,
  free_sub_heap Gamma ℰ Sigma Delta ->
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
