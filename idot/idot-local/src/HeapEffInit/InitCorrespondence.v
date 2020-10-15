(** remove printing ~ *)
Set Implicit Arguments.

Require Import Program.Equality.
Require Import LibExtra DotTactics AbstractSyntax.
Require Import
        GeneralTyping Typing Effects
        InitVar InitVarSubtyping InitTyping InitWeakening.
Require Import HeapCorrespondence HeapUpdate.
Require Import HeapCommit WellPointed HeapItemFree SubHeapFree.

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
(* | free_sub_heaps_nil : forall Gamma Delta Sigma, *)
(*     well_committed_heap Gamma Delta Sigma -> *)
(*     free_sub_heaps Gamma Delta Sigma nil *)
| free_sub_heaps_nil : forall Gamma Delta Sigma,
    well_committed_heap Gamma Delta Sigma ->
    well_localised_heap Gamma Delta Sigma ->
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
    free_sub_heap ℰ Sigma Delta ->
    localised_sub_heap (dom ℰ) Sigma Gamma Delta ->
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

Lemma well_localised_lit_push_committed : forall Gamma Delta Sigma x l T,
    x # Gamma ->
    x # Delta ->
    Gamma ⸴ Delta ⊢c l ->
    well_localised_heap Gamma Delta Sigma ->
    well_localised_heap
      (Gamma & x ~ T) (Delta & x ~ committed) (Sigma & x ~ (item_lit l)).
Proof.
  introv HxninG HxninD Hcomm [HGD [HDS Hwl]].
  unfold well_localised_heap; destruct_ands.
  repeat split; try(simpl_dom; congruence).
  introv Hbininit Hbinitm.
  pose proof (binds_push_inv Hbininit)
    as [[? ?] | [Hneq HbinD]]; try(exfalso ;congruence).
  pose proof (binds_push_inv Hbinitm)
    as [[? ?] | [_ HbinS]]; try(exfalso; congruence).
  eauto using localised_heap_item_push_fresh.
Qed.

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
  induction 1;
    try(solve[intros; constructor;
              eauto using well_committed_lit_push, localised_sub_heap_push_wc_lit,
              well_localised_lit_push_committed, free_sub_heap_push_fresh]).
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
  induction 1;
    try(solve[intros; constructor;
              eauto using well_committed_free_push,
              localised_sub_heap_push_free,
              free_sub_heap_push_fresh,
              localised_sub_heap_weaken_vs,
              well_localised_free_push]).
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
  constructor;
    eauto using free_sub_heaps_free_push,
    free_sub_heap_push_obj, free_sub_heap_fresh_inits.
  rewrite dom_concat, dom_single.
  eauto using localised_sub_heap_push_free_obj.
Qed.

Lemma singleton_free_localised : forall Gamma Delta Sigma x,
    not (binds x local Delta) ->
    localised_sub_heap \{x} Sigma Gamma Delta.
Proof.
  introv Hxnloc Hxeq Hxloc. rewrite in_singleton in Hxeq; subst. tauto.
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
    free_sub_heap_fresh_inits,
    localised_sub_heap_push_free,
    well_localised_heap_is_localised_subheap;
    try(rewrite dom_single); eapply singleton_free_localised;
      unfold not; intros.
  - assert (binds x free (Delta & x ~ free)) by eauto. binds_eq.
  - assert (binds x free (Delta & x ~ free)) by eauto. binds_eq.
Qed.

(** * Init Correspondence for Heap Updates *)
(** Inversion Lemmas for [free_sub_heaps] *)
Lemma free_sub_heaps_well_committed : forall Gamma Sigma ℰs Delta,
    free_sub_heaps Gamma Delta Sigma ℰs ->
    well_committed_heap Gamma Delta Sigma.
Proof.
  induction 1; eauto.
Qed.

Lemma free_sub_heaps_well_localised : forall Gamma Sigma ℰs Delta,
    free_sub_heaps Gamma Delta Sigma ℰs ->
    well_localised_heap Gamma Delta Sigma.
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
    well_localised_heap_update,
    localised_sub_heap_correspondence_committed,
    free_sub_heap_correspondence_committed.
Qed.

Lemma free_sub_heaps_write_other : forall Gamma Sigma ℰs Delta x a y i Sigma',
    free_sub_heaps Gamma Delta Sigma ℰs ->
    heap_update Sigma x a y Sigma' ->
    binds y i Delta ->
    x \notin (list_dom_union ℰs) ->
    well_committed_heap Gamma Delta Sigma' ->
    well_localised_heap Gamma Delta Sigma' ->
    free_sub_heaps Gamma Delta Sigma' ℰs.
Proof.
  intros Gamma Sigma ℰs Delta x a y Sigma'.
  induction 1; intros; eauto.
  rewrite notin_cons_list_dom_union in H5.
  destruct H5.
  eauto using
        free_sub_heap_correspondence_other,
  localised_sub_heap_correspondence_other.
Qed.

(* TODO : Typeclassify this *)
(** Inertness for Initialization. Definition changed to use subtyping so as to
    avoid having to enumerate possibilities *)
Definition inert_inits Delta :=
  forall x i, binds x i Delta ->
            init_sub i free \/ init_sub i committed.

Lemma inert_inits_empty : inert_inits empty.
Proof.
  unfold inert_inits; intros;
    exfalso; eauto using binds_empty_inv.
Qed.
Hint Resolve inert_inits_empty : core.

Lemma inert_inits_push : forall Delta x i,
    inert_inits Delta ->
    x # Delta ->
    init_sub i free \/ init_sub i committed ->
    inert_inits (Delta & x ~ i).
Proof.
  unfold inert_inits; introv Hii Hfr Hi Hbi.
  apply binds_push_inv in Hbi;
    destruct Hbi as [[Heq Heq'] | [Hneq Hbi]]; subst; eauto.
Qed.
Hint Resolve inert_inits_push : core.

(* A backwards compatibility lemma. *)
Corollary inert_inits_push_free_or_comm : forall Delta x i,
    inert_inits Delta ->
    x # Delta ->
    i = free \/ i = committed ->
    inert_inits (Delta & x ~ i).
Proof. intros. destruct_all; subst; eauto. Qed.

Corollary inert_inits_push_cases : forall Delta x i,
    inert_inits Delta ->
    x # Delta ->
    i = local \/ i = free \/ i = committed ->
    inert_inits (Delta & x ~ i).
Proof. intros. destruct_all; subst; eauto. Qed.

Hint Resolve inert_inits_push_free_or_comm inert_inits_push_cases : core.

(** Lemmas for comitting entire subheaps *)
Section PromoteToCommit.
  Lemma committed_delta_exists : forall ℰ Delta,
    (forall x, x \in dom ℰ -> x \in dom Delta) ->
    exists Delta', dom Delta = dom Delta' /\
              (forall x, x \in dom ℰ -> binds x committed Delta') /\
              (forall x init, x \notin dom ℰ ->
                         binds x init Delta -> binds x init Delta').
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
      (forall x init, x \in (list_dom_union ℰs) ->
                       binds x init Delta -> binds x init Delta').
  Proof.
    intros. eapply H0; eauto 2 using all_notin_inv.
  Qed.

  Lemma localised_sub_heap_commit_other : forall ℰ Sigma Gamma Delta Delta',
      localised_sub_heap (dom ℰ) Sigma Gamma Delta ->
      (forall x i, x \in dom ℰ -> binds x i Delta -> binds x i Delta') ->
      more_committed Delta Delta' ->
      dom Delta = dom Delta' ->
      localised_sub_heap (dom ℰ) Sigma Gamma Delta'.
  Proof.
    introv Hlsh Hsame Hmc Hdomeq. hnf.
    introv Hxinℰ HxlocD'. hnf in Hlsh.
    apply binds_to_dom in HxlocD' as HxinD. rewrite <- Hdomeq in HxinD.
    apply dom_to_binds in HxinD. destruct HxinD as [v HxbinD].
    destruct (init_decide v local) as [? | Hcontra]; subst.
    - specialize (Hlsh _ Hxinℰ HxbinD). destruct Hlsh as
          [itm [HbinxS HlhiD]]. exists itm. split; auto.
      eapply localised_heap_item_more_committed_ctx; eauto. rewrite Hdomeq.
      apply subset_refl.
    - exfalso. specialize (Hsame _ _   Hxinℰ HxbinD). binds_eq. congruence.
  Qed.

  Lemma free_sub_heaps_commit_other : forall Gamma Delta Delta' Sigma ℰs,
      free_sub_heaps Gamma Delta Sigma ℰs ->
      (forall x init, x \in (list_dom_union ℰs) ->
                       binds x init Delta -> binds x init Delta') ->
      more_committed Delta Delta' ->
      dom Delta = dom Delta' ->
      well_committed_heap Gamma Delta' Sigma ->
      well_localised_heap Gamma Delta' Sigma ->
      free_sub_heaps Gamma Delta' Sigma ℰs.
  Proof.
    induction 1; introv Hkits Hmc Hdomeq Hwc' Hwl'; try(solve[constructor; eauto]).
    rename H into Hani, H0 into Hfsh, H1 into Hlsh, H2 into Hfshs.
    constructor; eauto.
    - eapply free_sub_heap_commit_sub_other; eauto. introv Hxinℰ HbixD.
      exists i. split; auto. eapply Hkits; auto. simpl. rewrite in_union; auto.
    - eapply localised_sub_heap_commit_other; eauto.
      introv Hxinℰ HbinxiD. apply Hkits; auto. simpl. rewrite in_union. auto.
    - eapply IHfree_sub_heaps; eauto.
      introv Hxinℰs HbinxiD. apply Hkits; auto. simpl. rewrite in_union. auto.
  Qed.

  Lemma empty_eff_corr_delta_well_localised : forall Gamma Delta Delta' Sigma vs,
      well_localised_heap Gamma Delta Sigma ->
      (forall x, x \in vs -> binds x committed Delta') ->
      (forall x init,
          x \notin vs -> binds x init Delta -> binds x init Delta') ->
      dom Delta = dom Delta' ->
      more_committed Delta Delta' ->
      well_localised_heap Gamma Delta' Sigma.
  Proof.
    introv Hwlh Hcomm Hkits HdomDD' Hmc.
    hnf in Hwlh. hnf. destruct Hwlh as [HdomGD [HdomDS Hwlh]].
    destruct_all; repeat split; try solve[congruence].
    introv HxlocD' HxitmS. destruct (fv_decide x vs) as [Hxinvs | Hxninvs].
    - exfalso. specialize (Hcomm _ Hxinvs). binds_eq.
    - apply binds_to_dom in HxlocD' as HxinD'.
      rewrite <- HdomDD' in HxinD'. apply dom_to_binds in HxinD'.
      destruct HxinD' as [i HxiD]. specialize (Hkits _ _ Hxninvs HxiD).
      binds_eq; subst. clear H. rename HxiD into HxlocD.
      specialize (Hwlh _ _ HxlocD HxitmS).
      eapply localised_heap_item_more_committed_ctx; eauto.
      rewrite HdomDD'. apply subset_refl.
  Qed.

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

End PromoteToCommit.

(* Lemmas for promoting free to local *)
Section PromoteToLocal.

  (* We can promote x to local once all its effects are fulfilled *)
  Lemma removed_eff_corr_delta_localised :
    forall (Gamma : ctx) (Delta : init_ctx) (Sigma : heap) (x : var)
      (ℰ : eff_ctx) (Delta' : init_ctx) (effs : effects),
      localised_sub_heap (dom ℰ) Sigma Gamma Delta ->
      free_sub_heap ℰ Sigma Delta ->
      (* Effects for x fulfilled *)
      x \notin dom effs ->
      eff_ctx_corr_one ℰ effs ->
      (* Delta' is just Delta but with x promoted to local *)
      dom Delta = dom Delta' ->
      (forall y i, y <> x -> binds y i Delta -> binds y i Delta') ->
      more_committed Delta Delta' ->
      binds x local Delta' ->
      localised_sub_heap (dom ℰ) Sigma Gamma Delta'.
  Proof.
    introv Hlsh Hfsh Hxnin Heffcor Hdomeq Hbinsame Hmc Hxloc.
    unfold localised_sub_heap in *. intros y Hyinℰ Hyloc.
    unfold eff_ctx_corr_one in *. hnf in Hfsh.
    apply dom_to_binds in Hyinℰ as [effy Hbinyℰ].
    destruct effy.
    + (* Suppose y is bound to nil in ℰ. By Hfsh, exists heap item itm such that
       y is bound to itm in Sigma to which y is bound, and itm is a free heap
       item under Delta and ℰ. *)
      specialize (Hfsh _ _ Hbinyℰ); destruct Hfsh as [_ [itm [HbinyS Hfhi]]].
      exists itm. split; auto.
      (* That is, itm = item_obj T hds where
       free_heap_defs Delta ℰ y hds. By definition, this means that y is
       bound to heap_defs_effs y hds in ℰ. *)
      inversions Hfhi. rename H into Hfhds. hnf in Hfhds.
      destruct Hfhds as [_ [Hbinyℰ' Hwp]].
      (* But y is also bound to nil in ℰ, so by functionality of binding,
       heap_defs_effs y hds = nil. *)
      binds_eq. rename H0 into Hhdsnil.
      (* This would only be possible because hds contains
       no null fields (i.e. heap_def_trm l None) and so y is bound to
       item_obj T hds in Sigma where hds has no null fields. In this case, hds
       has no Nones, and each entry in hds is either a type annotation or a
       Some, which by Hwp, is well pointed *)
      eapply localised_heap_obj. eapply nil_effs_in_D_hds_non_null; eauto.
      rewrite <- Hdomeq. eapply well_pointed_in_D; eauto.
    + (* Otherwise, y is bound to something non-nil in ℰ. *)
      specialize (Hfsh _ _ Hbinyℰ); destruct Hfsh as [Heffsyeq [itm [HbinyS Hfhi]]].
      destruct p.
      (* By Heffcor, since x # effs, x \notin dom ℰ and so y = x is impossible. And
       so Hbinsame applies to y and then by Hlsh the result follows. *)
      specialize (Heffcor _ _ Hbinyℰ (v, t)). rewrite from_list_cons in *.
      assert (Hin : (v, t) \in \{ (v, t)} \u from_list effy)
        by (rewrite in_union, in_singleton; auto).
      specialize (Heffsyeq _ _ Hin); subst.
      specialize (Heffcor Hin).
      destruct (fv_decide x \{y}) as [Heq | Hneq];
        try rewrite in_singleton in *; subst.
      * rename Hxnin into Hynin. exfalso. eauto using from_list_dom.
      * rewrite notin_singleton in *.
        assert (HyinD : y \in dom Delta)
          by (rewrite Hdomeq; eauto using binds_to_dom).
        apply dom_to_binds in HyinD as [i HbinyD].
        destruct i;
          try solve[match goal with
                    | [HbinyD : binds y ?i Delta |- _] =>
                      assert (HbinyD' : binds y i Delta') by eauto; binds_eq
                    end].
        assert (Hydomℰ : y \in dom ℰ) by eauto using binds_to_dom.
        specialize (Hlsh _ Hydomℰ HbinyD).
        destruct Hlsh as [itm' [HbinyS' Hlhi]]; binds_eq; subst. clear H.
        exists itm; split; auto.
        eapply localised_heap_item_more_committed_ctx; eauto.
        rewrite Hdomeq. eapply subset_refl.
  Qed.

  (* Promote a particular variable y from free to local *)
  Lemma localised_delta_exists : forall Gamma Delta ℰ x,
      Gamma ⸴ Delta ⸴ dom ℰ ⊢i trm_var (avar_f x) ∶ free ->
      exists Delta', dom Delta = dom Delta' /\
                (forall y i, y <> x -> binds y i Delta -> binds y i Delta') /\
                more_committed Delta Delta' /\
                binds x local Delta'.
  Proof.
    induction Delta using env_ind.
    - introv Hxfr. exists (empty : init_ctx). repeat split; auto.
      inversions Hxfr. rename H3 into Hcontra. exfalso.
      apply init_var_typing_implies_bound in Hcontra. destruct Hcontra.
      erewrite <- in_empty, <- dom_empty in *; eauto using binds_to_dom.
    - introv Hxfr. rename x into y. rename x0 into x.
      destruct (fv_decide x \{y}) as [? | Hneq];
        try(rewrite in_singleton in *; subst; rename y into x; rename v into i);
        try(rewrite notin_singleton in *).
        + (* x = y. Promotion happens *)
          destruct i.
          { (* i = committed *)
            exfalso. assert (Hcontra : binds x committed (Delta & x ~ committed))
              by eauto.
            inversions Hxfr.
            rename H3 into Hinit. dependent induction Hinit; try binds_eq.
            clear Hcontra.
            apply init_var_sub_free in H; destruct_all; subst; eauto.
            clear IHHinit IHDelta. dependent induction Hinit.
            - apply binds_push_inv in H0. destruct_all; congruence.
            - eapply IHHinit; eauto using init_var_sub_local. }
          (* i ≠ local / free *)
          { exists (Delta & x ~ local); repeat split;
            auto using more_committed_refl. }
          { exists (Delta & x ~ local). repeat split;
                                     try(repeat(rewrite dom_concat, dom_single));
                                     eauto.
            - introv Hneq HbinDx.
              apply binds_push_inv in HbinDx.
              destruct HbinDx as [[? ?] | [_ HbinD]]; subst;
                try(solve[exfalso; auto]); eauto.
            - eapply more_committed_push_non_committed; congruence. }
          (* i = unspecified *)
          { exfalso.
            assert (Hcontra : binds x unspecified (Delta & x ~ unspecified))
              by eauto. inversions Hxfr. dependent induction H3; try binds_eq.
            clear Hcontra. clear IHDelta IHinit_var.
            dependent induction H3; eauto 3.
            - eapply init_var_sub_free in H0; destruct_all; congruence.
            - apply binds_push_inv in H0; destruct_all; congruence.
            - apply binds_push_inv in H0; destruct_all; congruence.
            - eapply init_var_sub_free in H1; destruct_all; congruence. }
        + (* x ≠ y. Use induction *)
          rename Hxfr into HxfrDx.
          assert (Hxfr : Gamma ⸴ Delta ⸴ dom ℰ ⊢i trm_var (avar_f x) ∶ free)
            by (inversions HxfrDx; eauto using init_var_strengthen_D_push).
          specialize (IHDelta _ _ Hxfr).
          destruct IHDelta as [Delta' [Heq [Hsame [Hmc Hxloc]]]].
          exists (Delta' & y ~ v); repeat split; eauto.
          * repeat(rewrite dom_concat, dom_single). congruence.
          * intros z i Hzneqx Hbinz.
            apply binds_push_inv in Hbinz as [[? ?] | [Hzneqy Hbinz]];
              subst; auto.
  Qed.

  Lemma localised_delta_is_inert : forall Delta Delta' x,
      inert_inits Delta ->
      dom Delta = dom Delta' ->
      (forall y i, y <> x -> binds y i Delta -> binds y i Delta') ->
      binds x local Delta' ->
      inert_inits Delta'.
  Proof.
    introv Hinert Hdomeq Hneqxsame Hxloc.
    hnf. hnf in Hinert.
    intros y i HbinyD'.
    destruct (fv_decide y \{x}) as [? | Hneq];
      try(rewrite in_singleton in *; subst; rename Hxloc into Hyloc);
      try(rewrite notin_singleton in *); try(binds_eq; auto).
    apply binds_to_dom in HbinyD' as HyinD.
    rewrite <- Hdomeq in HyinD. apply dom_to_binds in HyinD.
    destruct HyinD as [j HbinyD].
    destruct (init_decide i j) as [? | Hcontra]; subst; eauto.
    exfalso. specialize (Hneqxsame _ _ Hneq HbinyD). binds_eq. congruence.
  Qed.

  Lemma removed_eff_corr_delta_well_localised : forall Gamma Delta Delta' Sigma x itmx,
      well_localised_heap Gamma Delta Sigma ->

      (* x promoted to local *)
      dom Delta = dom Delta' ->
      (forall y i, y <> x -> binds y i Delta -> binds y i Delta') ->
      more_committed Delta Delta' ->
      binds x local Delta' ->

      (* and x is properly localised *)
      binds x itmx Sigma ->
      localised_heap_item Gamma Delta' itmx ->

      well_localised_heap Gamma Delta' Sigma.
  Proof.
    introv Hwlh HdomDD' Hnxsame Hmc HxlocD' HxitmS Hlhix.
    hnf. hnf in Hwlh. destruct Hwlh as [HdomGD [HdomDS Hwlh]].
    repeat split; try congruence. introv HylocD' HyitmS. rename x0 into y.
    destruct (fv_decide y \{x}) as [? | Hneq];
      try(rewrite in_singleton in *; subst; clear HylocD');
      try(rewrite notin_singleton in *).
    - binds_eq. auto.
    - apply binds_to_dom in HylocD' as HyinD'. rewrite <- HdomDD' in HyinD'.
      apply dom_to_binds in HyinD'. destruct HyinD' as [i HyiD].
      specialize (Hnxsame _ _ Hneq HyiD). binds_eq; subst.
      specialize (Hwlh _ _ HyiD HyitmS).
      eapply localised_heap_item_more_committed_ctx; eauto.
      rewrite HdomDD'. apply subset_refl.
  Qed.

  Lemma removed_eff_corr_delta_well_committed : forall Gamma Delta Delta' Sigma x,
      well_committed_heap Gamma Delta Sigma ->

      (* x promoted to local: doesn't affect committed bindings *)
      dom Delta = dom Delta' ->
      (forall y i, y <> x -> binds y i Delta -> binds y i Delta') ->
      more_committed Delta Delta' ->
      binds x local Delta' ->

      well_committed_heap Gamma Delta' Sigma.
  Proof.
    introv Hwc HdomDD' Hnxsame Hmc HxlocD'.
    hnf. hnf in Hwc. destruct Hwc as [HdomGD [HdomDS Hwc]].
    repeat split; try congruence. introv HycomD' HyitmS. rename x0 into y.
    destruct (fv_decide y \{x}) as [? | Hneq];
      try(rewrite in_singleton in *; subst; binds_eq);
      try(rewrite notin_singleton in *).
    apply binds_to_dom in HycomD' as HyinD'. rewrite <- HdomDD' in HyinD'.
    apply dom_to_binds in HyinD'. destruct HyinD' as [i HyiD].
    specialize (Hnxsame _ _ Hneq HyiD). binds_eq; subst.
    specialize (Hwc _ _ HyiD HyitmS). eauto using more_committed_item.
  Qed.

  Lemma localised_delta_is_more_specialized : forall Delta Delta' x vs,
      dom Delta = dom Delta' ->
      (forall y i, y <> x -> binds y i Delta -> binds y i Delta') ->
      binds x local Delta' ->
      init_var Delta vs x free ->
      (forall y i, binds y i Delta -> exists i', binds y i' Delta' /\ init_sub i' i).
  Proof.
    introv Hdomeq Hnxsame HxlocD' HxfreeD HbiyD.
    destruct (fv_decide y \{x}) as [? | Hneq];
      try(rewrite in_singleton in *; subst; rename HbiyD into HbixD);
      try(rewrite notin_singleton in *); eauto.
    dependent induction HxfreeD; try binds_eq; eauto.
    apply init_var_sub_free in H as [? | ?]; subst; eauto.
    exists local; repeat split; eauto. clear IHHxfreeD.
    rename HxfreeD into HxlocD.
    dependent induction HxlocD; try binds_eq; eauto.
    apply init_var_sub_local in H; eauto.
  Qed.

End PromoteToLocal.

(** Effect Correspondence for committing *)
Lemma eff_ctx_corr_empty_heap_def_effs : forall Delta Sigma ℰ x effs,
    free_sub_heap ℰ Sigma Delta ->
    eff_ctx_corr_one ℰ nil ->
    binds x effs ℰ ->
    (exists i, binds x i Delta /\ init_sub i free) ->
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
    { intros. apply Hpt in H9. destruct H9; auto 2.
      destruct H9; auto 2; destruct H9; auto 2. }
    pose proof (eff_ctx_corr_empty_heap_def_effs H0 H1 Hbi Hbif) as [? [? [? ?]]].
    binds_eq. eapply committed_defs_inv; eauto.
  - clear H1. pose proof (binds_to_dom H5) as Hin. rewrite <- H2 in Hin.
    apply dom_to_binds in Hin. destruct Hin as [?i ?Hbi].
    pose proof (H4 _ _ Hfr Hbi). binds_eq.
    unfold well_committed_heap in H; destruct_ands.
    eapply more_committed_item; eauto.
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
  rename H4 into Hfrsh. rename H9 into Hfrshs. rename a into ℰ.
  rewrite notin_union; split...
  unfold free_sub_heap in Hfrsh. hnf.
  intros Hxbin. apply dom_to_binds in Hxbin.
  destruct Hxbin as [effs Hxbin].
  specialize (Hfrsh x effs Hxbin).
  destruct Hfrsh as [_ Hcontra].
  destruct Hcontra as [itm [Hcontra _]].
  apply binds_to_dom in Hcontra...
Qed.

Lemma well_committed_heap_sub : forall Gamma Delta Delta' Sigma,
    inert_inits Delta ->
    well_committed_heap Gamma Delta Sigma ->
    dom Delta = dom Delta' ->
    (forall x init, binds x init Delta ->
               exists i', binds x i' Delta' /\ init_sub i' init) ->
    well_committed_heap Gamma Delta' Sigma.
Proof.
  introv Hinert Hwc Hdomeq' Hinitsub.
  destruct Hwc as [HdomeqGD [HdomeqDS Hwc]].
  hnf. repeat(split); try(congruence).
  introv HbinD' HbinS.
  pose proof (binds_to_dom HbinD') as Hbin. rewrite <- Hdomeq' in Hbin.
  apply dom_to_binds in Hbin. destruct Hbin as [?v HbinD].
  specialize (Hinitsub _ _ HbinD) as Hbin. destruct Hbin as [i' [HbinD'' Hsub]].
  apply (binds_functional HbinD') in HbinD''. subst.
  hnf in Hinert. specialize (Hinert _ _ HbinD).
  destruct Hinert as [Hvfree | Hvcom].
  - assert (Hcontra : init_sub committed free) by eauto.
    apply init_var_sub_free in Hcontra. destruct Hcontra; congruence.
  - apply init_var_sub_comm in Hvcom. subst.
    assert (Hchi : committed_heap_item Gamma Delta itm) by eauto.
    eapply more_committed_item with (Delta := Delta); eauto.
    hnf. introv Hbin.
    apply Hinitsub in Hbin. destruct Hbin as [i' [Hbin'  Hsub']].
    apply init_var_sub_comm in Hsub'. congruence.
Qed.

Lemma well_pointed_commit_other : forall Delta Delta' ℰ z,
    well_pointed Delta ℰ z ->
    more_committed Delta Delta' ->
    dom Delta = dom Delta' ->
    inert_inits Delta' ->
    well_pointed Delta' ℰ z.
Proof.
  introv Hwp Hmc Hdomeq Hinert. repeat(destruct Hwp as [Hwp | Hwp]); auto.
  - destruct Hwp as [Hzinℰ Hzfree]. apply binds_to_dom in Hzfree.
    rewrite Hdomeq in Hzfree. apply dom_to_binds in Hzfree.
    destruct Hzfree as [i Hzfree]. destruct i; auto.
    exfalso. specialize (Hinert _ _ Hzfree).
    destruct Hinert.
    + apply init_var_sub_free in H; destruct H; congruence.
    + apply init_var_sub_comm in H. congruence.
  - destruct Hwp as [Hzinℰ Hzloc]. apply binds_to_dom in Hzloc.
    rewrite Hdomeq in Hzloc. apply dom_to_binds in Hzloc.
    destruct Hzloc as [i Hzloc]. destruct i; auto.
    exfalso. specialize (Hinert _ _ Hzloc).
    destruct Hinert.
    + apply init_var_sub_free in H; destruct H; congruence.
    + apply init_var_sub_comm in H. congruence.
Qed.

Lemma free_heap_defs_localise_other : forall Delta Delta' ℰ x y hds,
    free_heap_defs Delta ℰ y hds ->
    dom Delta = dom Delta' ->
    (forall y i, y <> x -> binds y i Delta -> binds y i Delta') ->
    binds x local Delta' ->
    more_committed Delta Delta' ->
    inert_inits Delta' ->
    free_heap_defs Delta' ℰ y hds.
Proof.
  induction hds; introv Hfhds HdomDD' Hnxsame HxlocD' Hmc Hinert;
    hnf in Hfhds; hnf; destruct Hfhds as [[i [HbiyD Hinitsub]] [Hbiyℰ Hwp]];
      repeat split;
      try(solve[destruct (fv_decide y \{x}) as [? | Hxneq];
                try(rewrite in_singleton in *; subst);
                try(rewrite notin_singleton in *); eauto
              | intros; simpl in *; exfalso;
                rewrite in_empty in *; congruence]).
  intros z Hzpt; destruct a; simpl in *; auto; specialize (Hwp _ Hzpt);
    eauto using well_pointed_commit_other.
Qed.

Lemma free_heap_item_localise_other : forall Delta Delta' ℰ x y itm,
    free_heap_item Delta ℰ y itm ->
    dom Delta = dom Delta' ->
    (forall y i, y <> x -> binds y i Delta -> binds y i Delta') ->
    binds x local Delta' ->
    more_committed Delta Delta' ->
    inert_inits Delta' ->
    free_heap_item Delta' ℰ y itm.
Proof.
  introv Hfhi HdomDD' Hnxsame HxlocD' Hmc Hinert.
  inversions Hfhi. rename H into Hfhds.
  eauto using free_heap_defs_localise_other.
Qed.

Lemma free_sub_heap_localise_other : forall Delta Delta' Sigma ℰ x,
    free_sub_heap ℰ Sigma Delta ->
    dom Delta = dom Delta' ->
    (forall y i, y <> x -> binds y i Delta -> binds y i Delta') ->
    binds x local Delta' ->
    more_committed Delta Delta' ->
    inert_inits Delta' ->
    free_sub_heap ℰ Sigma Delta'.
Proof.
  introv Hfsh HdomDD' Hnxsame HxlocD Hmc Hinert.
  hnf. hnf in Hfsh. introv Hybinℰ. rename x0 into y.
  specialize (Hfsh _ _ Hybinℰ). destruct Hfsh as [Heffsy [itm [HbinyS Hfhi]]].
  split; auto. exists itm. split; eauto using free_heap_item_localise_other.
Qed.

Lemma free_sub_heaps_localise_other : forall Gamma Delta Delta' Sigma ℰs x,
    free_sub_heaps Gamma Delta Sigma ℰs ->
    dom Delta = dom Delta' ->
    (forall y i, y <> x -> binds y i Delta -> binds y i Delta') ->
    binds x local Delta' ->
    more_committed Delta Delta' ->
    well_committed_heap Gamma Delta' Sigma ->
    well_localised_heap Gamma Delta' Sigma ->
    inert_inits Delta' ->
    free_sub_heaps Gamma Delta' Sigma ℰs.
Proof.
  induction 1; introv HdomDD' Hnxsame HxlocD' Hmc Hwch' Hwlh' Hinert;
                 try solve[constructor; auto].
  rename  H into Hani, H0 into Hfsh, H1 into Hlsh, H2 into Hfshs.
  constructor; eauto using free_sub_heap_localise_other.
  hnf. hnf in Hwlh'. intros y Hyinℰ HylocD'.
  destruct Hwlh' as [HdomGD' [HdomD'S Hwlh']].
  apply binds_to_dom in HylocD' as HyinD'. rewrite HdomD'S in HyinD'.
  apply dom_to_binds in HyinD'. destruct HyinD' as [itm HyitmS].
  specialize (Hwlh' _ _ HylocD' HyitmS). eauto.
Qed.
