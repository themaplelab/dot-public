(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Typing GeneralTyping HeapCorrespondence.
Require Import Effects EffectUpdate HeapEffects.
Require Import HeapDefsPointsTo WellPointed.
Require Import CommittedSubHeap FreeItems HeapUpdate.

(** * Update Lemmas *)
Lemma defs_update_points_to : forall hds a y hds',
    defs_update hds a y hds' ->
    forall x : var,
      x \in heap_defs_points_to hds' ->
      x = y \/ (x \in heap_defs_points_to hds).
Proof.
  induction 1; simpl;
    intros; rewrite ? in_union, ? in_singleton in *;
      try destruct d; try destruct o; rewrite ? in_union in *;
        destruct_ors; eauto.
  apply IHdefs_update in H0; destruct_ors; eauto.
Qed.

Lemma well_pointed_update : forall Delta ℰ x y effs' ℰ',
    well_pointed Delta ℰ x ->
    eff_update ℰ y effs' ℰ' ->
    well_pointed Delta ℰ' x.
Proof.
  unfold eff_update.
  intros; destruct_ands; congruence.
Qed.

Local Hint Resolve well_pointed_update : core.

Lemma free_heap_defs_update : forall Delta ℰ x hds a y hds' ℰ',
    free_heap_defs Delta ℰ x hds ->
    well_pointed Delta ℰ y ->
    defs_update hds a y hds' ->
    eff_update ℰ x (heap_defs_effs x hds') ℰ' ->
    free_heap_defs Delta ℰ' x hds'.
Proof.
  unfold free_heap_defs.
  intros; destruct_ands; repeat_split_right;
    try solve [unfold eff_update in *; destruct_ands; auto];
    auto.
  intros x' Hdpt. eapply defs_update_points_to in Hdpt; eauto.
  destruct Hdpt; subst; eauto.
Qed.

Lemma free_heap_defs_update_other : forall Delta ℰ x hds y effs' ℰ',
    free_heap_defs Delta ℰ x hds ->
    eff_update ℰ y effs' ℰ' ->
    x <> y ->
    free_heap_defs Delta ℰ' x hds.
Proof.
  unfold free_heap_defs, eff_update; intros; destruct_ands.
  repeat_split_right; eauto.
  rewrite H0 in H5. auto.
Qed.

(** We use typing to ensure that there are no repeated labels *)
Lemma free_heap_defs_removes : forall Gamma hds Ts x a y hds',
    Gamma ⊢ hds ∶ Ts ->
    defs_update hds a y hds' ->
    (x, a) \notin from_list (heap_defs_effs x hds').
Proof.
  introv Hty. gen hds'.
  induction Hty; intros.
  - inversions H0.
    + simpl. rewrite from_list_nil. auto.
    + inversion H6.
  - inversions H2.
    + simpl in *. eauto using heap_defs_effs_labels_hasnt.
    + specialize (IHHty _ H8).
      destruct d; simpl; auto.
      destruct o; simpl; auto.
      apply notin_union; split; auto.
      intro Contra. rewrite in_singleton in Contra.
      inversions Contra.
      eapply defs_update_hasnt_inv; eauto.
Qed.

Lemma defs_update_has : forall Gamma Ts hds a x hds',
    Gamma ⊢ hds ∶ Ts ->
    defs_update hds a x hds' ->
    labels_has hds' (heap_def_trm a (Some x)).
Proof.
  introv Hty; gen a x hds'.
  induction Hty; intros.
  - inversion H0; subst.
    + apply labels_has_cons.
    + inversion H6.
  - inversions H2.
    + apply labels_has_cons.
    + specialize (IHHty _ _ _ H8).
      pose proof (defs_update_hasnt H8 H1).
      pose proof (labels_has_hasnt_neq _ IHHty H2). simpl in H3.
      unfold labels_has; simpl; cases_if; auto.
Qed.

Lemma defs_update_effects_cases : forall Gamma hds Ts x a y hds',
    Gamma ⊢ hds ∶ Ts ->
    defs_update hds a y hds' ->
    (((x, a) \in from_list (heap_defs_effs x hds)) /\
     from_list (heap_defs_effs x hds) =
     from_list ((x,a) :: (heap_defs_effs x hds'))%list) \/
    (((x, a) \notin from_list (heap_defs_effs x hds)) /\
     from_list (heap_defs_effs x hds) =
     from_list (heap_defs_effs x hds')).
Proof.
  introv Hty. gen hds'.
  induction Hty; intros.
  - inversions H0.
    + simpl; destruct o.
      * rewrite from_list_nil. right. split; auto.
      * left.
        rewrite from_list_cons. rewrite from_list_nil.
        rewrite union_empty_r, in_singleton. split; auto.
    + inversion H6.
  - inversions H2.
    + simpl in * |-. pose proof (heap_defs_effs_labels_hasnt (x:=x) H1).
      clear IHHty. destruct o; simpl.
      * right; auto.
      * left.
        rewrite from_list_cons.
        rewrite in_union. split; auto using in_singleton_self.
    + specialize (IHHty _ H8).
      pose proof (defs_update_hasnt H8 H1).
      pose proof (defs_update_has H H8).
      pose proof (labels_has_hasnt_neq _ H3 H2). simpl in H4.
      destruct d; try destruct o; simpl; auto.
      simpl in H4. assert (a <> t) by congruence.
      destruct IHHty.
      * left. destruct H6.
        rewrite from_list_cons.
        rewrite in_union; split; auto.
        rewrite H7.
        repeat(rewrite from_list_cons).
        rewrite union_comm_assoc; auto.
      * right. destruct H6; split; auto. apply notin_union.
        split; auto. apply notin_singleton; congruence.
        repeat(rewrite from_list_cons).
        congruence.
Qed.

Lemma defs_update_eff_subset : forall Gamma hds Ts x a y hds',
    Gamma ⊢ hds ∶ Ts ->
    defs_update hds a y hds' ->
    (from_list (heap_defs_effs x hds')) \c (from_list (heap_defs_effs x hds)).
Proof.
  intros Gamma hds Ts x a y hds' Hty Hdup.
  pose proof (defs_update_effects_cases x Hty Hdup) as Hc.
  destruct Hc as [[Hin Heq] | [Hnin Heq]]; subst.
  - rewrite Heq.
    repeat(rewrite from_list_cons).
    rewrite union_comm. auto using subset_union_weak_l.
  - rewrite Heq. auto using subset_refl.
Qed.

Lemma defs_update_eff_remove : forall Gamma hds Ts x a y hds',
    Gamma ⊢ hds ∶ Ts ->
    defs_update hds a y hds' ->
    eff_remove (heap_defs_effs x hds) x a (heap_defs_effs x hds').
Proof.
  intros Gamma hds Ts x a y hds' Hty Hdup.
  pose proof (defs_update_effects_cases x Hty Hdup) as Hc.
  unfold eff_remove. split; eauto using free_heap_defs_removes.
  split.
  - repeat (rewrite from_list_cons in *).
    destruct Hc as [[Hin Heq] | [Hnin Heq]].
    + introv eff_neq eff_in_hds.
      rewrite Heq in eff_in_hds.
      rewrite in_union in eff_in_hds.
      destruct eff_in_hds; auto. exfalso.
      rewrite in_singleton in *; auto.
    + introv eff_neq eff_in_hds. rewrite Heq in eff_in_hds. assumption.
  - repeat (rewrite from_list_cons in *).
    eauto using defs_update_eff_subset.
Qed.

Lemma free_heap_defs_keeps : forall hds x a y hds',
    defs_update hds a y hds' ->
    (forall eff, eff <> (x,a) ->
            eff \in from_list (heap_defs_effs x hds) ->
            eff \in from_list (heap_defs_effs x hds')).
Proof with eauto.
  induction 1; intros.
  - destruct o... simpl in *. rewrite from_list_cons in H0.
    rewrite in_union in H0... destruct H0 as [contra | ?H]...
    exfalso. rewrite in_singleton in contra...
  - destruct d... destruct o... simpl in *.
    rewrite from_list_cons in *. rewrite in_union in *.
    destruct H1...
Qed.

Lemma free_heap_item_update : forall Delta ℰ x T hds a y hds' ℰ',
    free_heap_item Delta ℰ x (item_obj T hds) ->
    well_pointed Delta ℰ y ->
    defs_update hds a y hds' ->
    eff_update ℰ x (heap_defs_effs x hds') ℰ' ->
    free_heap_item Delta ℰ' x (item_obj T hds').
Proof.
  inversion 1; eauto using free_heap_defs_update.
Qed.

Lemma free_heap_item_update_other : forall Delta ℰ x itm y effs' ℰ',
    free_heap_item Delta ℰ x itm ->
    eff_update ℰ y effs' ℰ' ->
    x <> y ->
    free_heap_item Delta ℰ' x itm.
Proof.
  inversion 1; eauto using free_heap_defs_update_other.
Qed.

(** Committing sub_heaps *)
Lemma free_heap_defs_commit_other : forall Delta ℰ x hds Delta',
    free_heap_defs Delta ℰ x hds ->
    (forall x init, x \in dom ℰ -> binds x init Delta -> binds x init Delta') ->
    more_committed Delta Delta' ->
    free_heap_defs Delta' ℰ x hds.
Proof.
  inversion 1; subst; intros; destruct_all; eauto; constructor.
  - inversions H; eauto using binds_to_dom.
  - split; auto. intros. specialize (H4 _ H5).
    destruct H4 as [Hcom | [Hdom Hbi]]; auto.
Qed.

Lemma free_heap_item_commit_other : forall Delta ℰ x itm Delta',
    free_heap_item Delta ℰ x itm ->
    (forall x init, x \in dom ℰ -> binds x init Delta -> binds x init Delta') ->
    more_committed Delta Delta' ->
    free_heap_item Delta' ℰ x itm.
Proof.
  inversion 1; eauto using free_heap_defs_commit_other.
Qed.

Lemma committed_defs_inv : forall Delta y hds,
    heap_defs_effs y hds = nil ->
    (forall x : var, x \in heap_defs_points_to hds -> binds x committed Delta) ->
    committed_heap_defs Delta hds.
Proof.
  induction hds; intros; constructor.
  - assert (heap_defs_effs y hds = nil).
    { destruct a; try destruct o; simpl in *; auto.
      exfalso.
      assert ((y,t) \in \{ (y,t)} \u from_list (heap_defs_effs y hds))
        by (rewrite in_union, in_singleton; auto).
      inversion H. }
    specialize (IHhds H1); clear H1. apply IHhds; intros.
    apply H0. destruct a; try destruct o; simpl; rewrite ? in_union; auto.
  - destruct a; try destruct o; simpl in *; try constructor.
    + apply H0; rewrite in_union, in_singleton; auto.
    + assert ((y,t) \in \{ (y,t)} \u from_list (heap_defs_effs y hds))
        by (rewrite in_union, in_singleton; auto).
      exfalso. inversion H.
Qed.

Lemma var_of_eff_defs : forall (y x : var) (a : trm_label) (ds : defs),
    (y, a) \in from_list (def_eff x ds) -> y = x.
Proof with eauto.
  induction ds.
  - simpl. rewrite from_list_nil. introv Hc. exfalso. rewrite in_empty in Hc...
  - destruct a0; simpl...
    rewrite from_list_cons. rewrite in_union. rewrite in_singleton.
    intros Hin. destruct Hin... inversions H...
Qed.

Lemma heap_defs_open_eq : forall (a x : var) (n : nat) (hds : heap_defs),
    heap_defs_effs a (open_rec n x hds) =
    heap_defs_effs a hds.
Proof with eauto.
  induction hds...
  destruct a0; simpl...
  destruct o; simpl...
  induction hds... destruct a0...
  destruct o; simpl...
  simpl in IHhds. inversions IHhds.
  rewrite H0...
Qed.

Lemma heap_defs_open_vars_eq : forall (a : var) (xs : list var) (n : nat)
                                      (ds : defs),
    heap_defs_effs a (open_rec_vars n xs (heap_defs_of_defs ds)) =
    heap_defs_effs a (heap_defs_of_defs ds).
Proof with eauto.
  induction xs; simpl...
  intros n ds.
  rewrite heap_defs_of_defs_open_commut.
  specialize (IHxs (S n) (open_rec n a0 ds)). rewrite IHxs.
  rewrite <- heap_defs_of_defs_open_commut.
  rewrite heap_defs_open_eq...
Qed.

Lemma def_eff_eq_open_heap_defs_of_defs : forall ds x l,
    (heap_defs_effs x (open_vars l (heap_defs_of_defs ds))) =
    def_eff x ds.
Proof with eauto.
  induction l.
  - simpl. induction ds; try(solve[simpl; eauto]).
    destruct a; simpl... rewrite IHds...
  - rewrite heap_defs_open_vars_eq in *...
Qed.

Lemma def_eff_eq_hds : forall (x : var) (ds : defs),
    (def_eff x ds) = (heap_defs_effs x (heap_defs_of_defs ds)).
Proof with eauto.
  induction ds; try(solve[simpl; eauto]).
  destruct a; simpl...
  rewrite IHds...
Qed.

Lemma hds_effs_map_open_eq : forall (ds : defs) (x : var) (n : nat) (y : var),
    heap_defs_effs x (heap_defs_of_defs ds) =
    heap_defs_effs x (heap_defs_of_defs (List.map (open_rec n y) ds)).
Proof with eauto.
  induction ds; try(solve[simpl; eauto]).
  destruct a; simpl...
  intros. erewrite IHds. reflexivity.
Qed.

Lemma hds_effs_open_var_eq : forall (ds : defs) (x : var) (n : nat) (y : var),
    heap_defs_effs x (heap_defs_of_defs ds) =
    heap_defs_effs x (heap_defs_of_defs (open_rec n y ds)).
Proof with eauto.
  induction ds; try(solve[simpl; eauto]). simpl.
  destruct a; simpl; intros...
  unfold open_rec_list. erewrite hds_effs_map_open_eq. reflexivity.
Qed.

Lemma hds_effs_open_vars_eq : forall (ys : list var) (ds : defs) (x : var) (n : nat),
    heap_defs_effs x (heap_defs_of_defs ds) =
    heap_defs_effs x (heap_defs_of_defs (open_rec_vars n ys ds)).
Proof with eauto.
  induction ys; simpl...
  intros. erewrite hds_effs_open_var_eq.
  erewrite IHys. reflexivity.
Qed.
