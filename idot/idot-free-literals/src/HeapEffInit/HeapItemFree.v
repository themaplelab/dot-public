(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Typing Effects InitVar InitTyping InitWeakening GeneralTyping.
Require Import HeapEffects HeapCorrespondence HeapUpdate HeapCommit WellPointed.

Implicit Types (Delta : init_ctx) (Sigma : heap) (ℰ : eff_ctx).

Hint Resolve heap_defs_effs_var_eq heap_defs_effs_var_eq' : core.

(* This essentially extracts all non-null defs of an object. Opposite of heap_defs_effs *)
 Fixpoint heap_defs_points_to (hds : heap_defs) :=
  match hds with
  | nil => \{}
  | (heap_def_typ _ _) :: ds => heap_defs_points_to ds
  | (heap_def_trm l (Some x)) :: ds => \{ x} \u heap_defs_points_to ds
  | (heap_def_trm l None) :: ds => heap_defs_points_to ds
  end%list.

Lemma heap_defs_of_defs_points_to_empty : forall ds,
    (heap_defs_points_to (heap_defs_of_defs ds)) = \{}.
Proof.
  induction ds as [| d ds IHds];
    try destruct d; simpl; auto.
Qed.

Local Hint Resolve
      well_pointed_weaken_inits_middle
      well_pointed_weaken_effs_middle : core.

(** * Free Sub heap items *)
(* The heap definitions hds inside object y are free according to Delta
   and ℰ *)
Definition free_heap_defs (Delta : init_ctx) (ℰ : eff_ctx)
           (y : var) (hds : heap_defs) :=
  (* y is free in Delta *)
  binds y free Delta /\
  (* ℰ  states that the null fields of y must be assigned *)
  binds y (heap_defs_effs y hds)  ℰ /\
  (* For all fields of y of the form a = x (a field name), x is
     well pointed: x is either committed according to Delta or
     x is some item in the effects context ℰ that's free *)
  forall x, (x \in heap_defs_points_to hds) ->
       well_pointed Delta ℰ x.

Inductive free_heap_item : ctx -> init_ctx -> eff_ctx -> var -> item -> Prop :=
(* A item y that bounds to an object with type T and heap definitions hds
   are free if the hds are free *)
| free_heap_obj : forall Gamma Delta ℰ y T hds,
    (* By hds free, it is meant that
       - y is free in Delta
       - ℰ states that the null fields of y must be assigned
       - If y.a = x then x is either committed or is free but has to be
         assigned according to ℰ *)
    free_heap_defs Delta ℰ y hds ->
    free_heap_item Gamma Delta ℰ y (item_obj T hds)
(* (* Free lambda extension *) *)
| free_heap_lit : forall Gamma Delta ℰ y l,
    binds y free Delta /\
    (* Literals are lambdas or constructors and have no effects *)
    binds y empty ℰ /\
    (* The literal is well-committed assuming that everything in the
       current subheap is committed *)
    Gamma ⸴ subst_env_fset_vars Delta (dom ℰ) committed
          ⊢c l ->
    free_heap_item Gamma Delta ℰ y (item_lit l).
Hint Constructors free_heap_item : core.

Section Domains.
  (** [heap_defs Delta ℰ y T hds] implies [y] is in [dom ℰ] *)
  Lemma free_heap_defs_in_effs : forall Delta ℰ y hds,
    free_heap_defs Delta ℰ y hds ->
    y \in dom ℰ.
  Proof.
    unfold free_heap_defs. introv [HbiD [HbiE _]].
    eauto using binds_to_dom.
  Qed.

  Lemma free_heap_defs_in_inits : forall Delta ℰ y hds,
      free_heap_defs Delta ℰ y hds ->
      y \in dom Delta.
  Proof.
    unfold free_heap_defs. introv [HbiD [HbiE _]].
    eauto using binds_to_dom.
  Qed.

  Hint Resolve free_heap_defs_in_effs free_heap_defs_in_inits : core.

  (** [heap_defs Delta ℰ y T itm] implies [y] is in [dom ℰ] *)
  Lemma free_heap_item_in_effs : forall Delta ℰ y hds,
      free_heap_defs Delta ℰ y hds ->
      y \in dom ℰ.
  Proof. inversion 1; eauto. Qed.

  Lemma free_heap_item_in_inits : forall Gamma Delta ℰ y hds,
      free_heap_item Gamma Delta ℰ y hds ->
      y \in dom Delta.
  Proof. inversion 1; subst; destruct_ands; eauto using binds_to_dom. Qed.
End Domains.

(** * Weakening Lemmas for free heaps items *)
Local Hint Resolve binds_push_fresh_middle : core.

Lemma free_heap_defs_weaken_inits_middle : forall Delta1 Delta2 ℰ x hds y i',
    free_heap_defs (Delta1 & Delta2) ℰ x hds ->
    y # Delta1 ->
    free_heap_defs (Delta1 & y ~ i' & Delta2) ℰ x hds.
Proof.
  unfold free_heap_defs; introv [HbiD [HbiE Hcases]] Hfr.
  repeat_split_right; auto.
Qed.
Local Hint Resolve free_heap_defs_weaken_inits_middle : core.

Lemma free_heap_defs_weaken_inits : forall Delta ℰ x hds y i',
    free_heap_defs Delta ℰ x hds ->
    y # Delta ->
    free_heap_defs (Delta & y ~ i') ℰ x hds.
Proof.
  introv Hfhds Hfr.
  rewrite <- (concat_empty_r Delta) in Hfhds.
  rewrite <- (concat_empty_r (Delta & _)).
  eauto.
Qed.
Local Hint Resolve free_heap_defs_weaken_inits : core.

Lemma free_heap_defs_weaken_effs_middle : forall Delta ℰ1 ℰ2 x hds y effs,
    free_heap_defs Delta (ℰ1 & ℰ2) x hds ->
    y # ℰ1 ->
    free_heap_defs Delta (ℰ1 & y ~ effs & ℰ2) x hds.
Proof.
  unfold free_heap_defs; introv [HbiD [HbiE Hcases]] Hfr.
  repeat_split_right; auto.
Qed.
Local Hint Resolve free_heap_defs_weaken_effs_middle : core.

Lemma free_heap_defs_weaken_effs : forall Delta ℰ x hds y effs,
    free_heap_defs Delta ℰ x hds ->
    y # ℰ ->
    free_heap_defs Delta (ℰ & y ~ effs) x hds.
Proof.
  introv Hfhds Hfr.
  rewrite <- (concat_empty_r ℰ) in Hfhds.
  rewrite <- (concat_empty_r (ℰ & _)).
  eauto.
Qed.
Local Hint Resolve free_heap_defs_weaken_effs : core.

Lemma free_heap_defs_push_obj : forall Delta ℰ x ds,
    x # Delta ->
    x # ℰ ->
    free_heap_defs (Delta & x ~ free)
                   (ℰ & x ~ (heap_defs_effs x (heap_defs_of_defs ds)))
                   x
                   (heap_defs_of_defs ds).
Proof.
  introv HfrD HfrE. unfold free_heap_defs; repeat_split_right; auto.
  introv Hpt.
  rewrite heap_defs_of_defs_points_to_empty, in_empty in Hpt.
  destruct Hpt.
Qed.
Local Hint Resolve free_heap_defs_push_obj : core.

Lemma free_heap_defs_first_obj : forall Delta x ds,
    x # Delta ->
    free_heap_defs (Delta & x ~ free)
                   (x ~ (heap_defs_effs x (heap_defs_of_defs ds)))
                   x
                   (heap_defs_of_defs ds).
Proof.
  intros. rewrite <- (concat_empty_l (x ~ (heap_defs_effs _ _))).
  eauto.
Qed.
Local Hint Resolve free_heap_defs_first_obj : core.

(** * Weakening Lemmas for free heap items *)
Local Ltac defs_to_item := inversion 1; subst; eauto.

Lemma free_heap_item_weaken_ctx_middle : forall Gamma1 Gamma2 Delta ℰ x hds y T,
    free_heap_item (Gamma1 & Gamma2) Delta ℰ x hds ->
    y # Gamma1 ->
    free_heap_item (Gamma1 & y ~ T & Gamma2) Delta ℰ x hds.
Proof.
  defs_to_item.
  intros. econstructor... destruct_ands.
  split; try(split);
    eauto using binds_push_fresh_middle.
  repeat(rewrite subst_env_fset_vars_distrib_env).
  apply commit_weaken_middle_G; eauto.
Qed.

Lemma free_heap_item_weaken_ctx : forall Gamma Delta ℰ x hds y T,
    free_heap_item Gamma Delta ℰ x hds ->
    y # Gamma ->
    free_heap_item (Gamma & y ~ T) Delta ℰ x hds.
Proof.
  defs_to_item.
  intros. rewrite <- (concat_empty_r (Gamma & y ~ T)).
  eapply free_heap_item_weaken_ctx_middle; eauto.
  rewrite concat_empty_r; eauto.
Qed.

Lemma free_heap_item_weaken_inits_middle : forall Gamma Delta1 Delta2 ℰ x hds y i',
    free_heap_item Gamma (Delta1 & Delta2) ℰ x hds ->
    y # Delta1 ->
    free_heap_item Gamma (Delta1 & y ~ i' & Delta2) ℰ x hds.
Proof.
  defs_to_item.
  intros. econstructor... destruct_ands.
  split; try(split);
    eauto using binds_push_fresh_middle.
  repeat(rewrite subst_env_fset_vars_distrib_env).
  rewrite subst_env_fset_vars_single.
  apply commit_weaken_middle_D; eauto.
  + rewrite <- subst_env_fset_vars_distrib_env; eauto.
  + rewrite subst_env_fset_vars_dom; eauto.
Qed.

Lemma free_heap_item_weaken_inits : forall Gamma Delta ℰ x hds y i',
    free_heap_item Gamma Delta ℰ x hds ->
    y # Delta ->
    free_heap_item Gamma (Delta & y ~ i') ℰ x hds.
Proof.
  defs_to_item.
  intros. rewrite <- (concat_empty_r (Delta & y ~ i')).
  eapply free_heap_item_weaken_inits_middle; eauto.
  rewrite concat_empty_r; eauto.
Qed.

Lemma free_heap_item_weaken_effs_middle : forall Gamma Delta ℰ1 ℰ2 x hds y effs,
    free_heap_item Gamma Delta (ℰ1 & ℰ2) x hds ->
    y # ℰ1 ->
    free_heap_item Gamma Delta (ℰ1 & y ~ effs & ℰ2) x hds.
Proof.
  defs_to_item.
  intros. econstructor... destruct_ands.
  split; try(split);
    eauto using binds_push_fresh_middle.
  eapply more_committed_lit; eauto.
  hnf. intros. eapply subst_env_fset_vars_more; eauto.
  hnf. intros.
  repeat(rewrite dom_concat in *; rewrite in_union in *).
  destruct H2; eauto.
  destruct H5; eauto.
Qed.

Lemma free_heap_item_weaken_effs : forall Gamma Delta ℰ x hds y effs,
    free_heap_item Gamma Delta ℰ x hds ->
    y # ℰ ->
    free_heap_item Gamma Delta (ℰ & y ~ effs) x hds.
Proof.
  defs_to_item.
  intros. rewrite <- (concat_empty_r (ℰ & y ~ effs)).
  eapply free_heap_item_weaken_effs_middle; eauto.
  rewrite concat_empty_r; eauto.
Qed.

Lemma free_heap_item_push_obj : forall Gamma Delta ℰ x T' T ds,
    x # Delta ->
    x # ℰ ->
    free_heap_item (Gamma & x ~ T') (Delta & x ~ free)
                   (ℰ & x ~ (heap_defs_effs x (heap_defs_of_defs ds)))
                   x
                   (item_obj T (heap_defs_of_defs ds)).
Proof. eauto. Qed.

Lemma free_heap_item_first_obj : forall Gamma Delta x T' T ds,
    x # Delta ->
    free_heap_item (Gamma & x ~ T') (Delta & x ~ free)
                   (x ~ (heap_defs_effs x (heap_defs_of_defs ds)))
                   x
                   (item_obj T (heap_defs_of_defs ds)).
Proof. eauto. Qed.

(** * Update Lemmas *)
Definition eff_update ℰ x effs' ℰ' :=
  dom ℰ = dom ℰ' /\
  binds x effs' ℰ' /\
  forall y effs,
            y <> x ->
            binds y effs ℰ ->
            binds y effs ℰ'.

Definition eff_remove (effs : effects) x a effs' :=
  (x,a) \notin (from_list effs') /\
  (forall eff, eff <> (x,a) ->
               eff \in (from_list effs) -> eff \in (from_list effs')) /\
  (from_list effs') \c (from_list effs).

Section EffUpdateExists.
  Lemma eff_update_exists : forall ℰ x effs',
    x \in dom ℰ ->
          (exists ℰ', eff_update ℰ x effs' ℰ').
  Proof.
    intros. exists (ℰ & x ~ effs').
    unfold eff_update; repeat_split_right; auto.
    induction ℰ using env_ind; simpl_dom.
    - exfalso; rewrite in_empty in *; auto.
    - rewrite in_union, in_singleton in *.
      destruct H; subst.
      + rewrite union_assoc, union_same; auto.
      + apply IHℰ in H; auto. rewrite H at 1.
        rewrite union_comm_assoc at 1; auto.
  Qed.

  Lemma eff_update_ok_exists : forall ℰ x effs',
      ok ℰ ->
      x \in dom ℰ ->
            (exists ℰ', ok ℰ /\ eff_update ℰ x effs' ℰ').
  Proof.
    induction ℰ using env_ind; intros.
    - rewrite dom_empty, in_empty in *; exfalso; auto.
    - rewrite dom_push, in_union, in_singleton in *.
      destruct_ors; subst.
      + exists (ℰ & x ~ effs'); unfold eff_update;
          repeat_split_right; simpl_dom; auto.
        introv Hneq Hbi.
        apply binds_push_neq_inv in Hbi;
          eauto using binds_push_neq.
      + apply ok_push_inv in H. destruct_ands.
        specialize (IHℰ _ effs' H H0) as [ℰ' [Hok Heu]].
        exists (ℰ' & x ~ v). split; auto. unfold eff_update in *.
        destruct_ands; repeat_split_right; simpl_dom; try congruence.
        * assert (x <> x0) by congruence.
          apply binds_push_neq; eauto.
        * intros.
          apply binds_push_inv in H6; destruct_ors; destruct_ands; subst; auto.
  Qed.
End EffUpdateExists.

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

Lemma free_heap_item_update : forall Gamma Delta ℰ x T hds a y hds' ℰ',
    free_heap_item Gamma Delta ℰ x (item_obj T hds) ->
    well_pointed Delta ℰ y ->
    defs_update hds a y hds' ->
    eff_update ℰ x (heap_defs_effs x hds') ℰ' ->
    free_heap_item Gamma Delta ℰ' x (item_obj T hds').
Proof.
  inversion 1; eauto using free_heap_defs_update.
Qed.

Lemma free_heap_item_update_other : forall Gamma Delta ℰ x itm y effs' ℰ',
    free_heap_item Gamma Delta ℰ x itm ->
    eff_update ℰ y effs' ℰ' ->
    x <> y ->
    free_heap_item Gamma Delta ℰ' x itm.
Proof.
  inversion 1; eauto using free_heap_defs_update_other.
  subst. intros. destruct_ands. econstructor.
  split; eauto.
  hnf in H1. destruct_ands.
  split; eauto. rewrite <- H1. eauto.
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

Lemma free_heap_item_commit_other : forall Gamma Delta ℰ x itm Delta',
    free_heap_item Gamma Delta ℰ x itm ->
    (forall x init, x \in dom ℰ -> binds x init Delta -> binds x init Delta') ->
    more_committed Delta Delta' ->
    free_heap_item Gamma Delta' ℰ x itm.
Proof.
  inversion 1; eauto using free_heap_defs_commit_other.
  subst. intros. destruct_ands. hnf in H2.
  econstructor. split; try(split); eauto.
  - apply binds_to_dom in H3. eapply H1 in H3; eauto.
  - eapply more_committed_lit; eauto. hnf.
    intros. eapply subst_env_fset_vars_more_env; eauto.
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
