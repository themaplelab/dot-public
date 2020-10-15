Set Implicit Arguments.

Require Import LibExtra DotTactics Program.Equality List.
Require Import
        AbstractSyntax PreTyping Typing GeneralTyping
        RecordAndInertTypes
        OperationalSemantics Substitution Weakening
        HeapCorrespondence HeapUpdate
        Subenvironments Narrowing.
Require Import
        Effects InitVar InitTyping InitVarSubtyping
        InitWeakening HeapCommit HeapItemFree SubHeapFree
        InitCorrespondence InitNarrowing.

Fixpoint effects_remove (effs : effects) (x : var) : effects :=
  match effs with
  | nil => nil
  | ((y, l) :: ys)%list
    => If y = x then (effects_remove ys x) else ((y, l) :: effects_remove ys x)%list
end.

Lemma notin_effects_remove : forall x effs,
    x # effects_remove effs x.
Proof.
  induction effs.
  - simpl. rewrite <- empty_def, dom_empty. apply notin_empty.
  - destruct a. rename v into y.
    destruct (fv_decide x \{y}) as [? | Hxneqy];
      try(rewrite in_singleton in *; subst);
      try(rewrite notin_singleton in *); simpl; cases_if; auto.
    clear C. rewrite cons_to_push, dom_concat,
             dom_single, notin_union, notin_singleton; split; auto.
Qed.

Lemma effects_remove_distrib : forall effs1 effs2 x,
    effects_remove (effs1 ++ effs2)%list x =
    (effects_remove effs1 x ++ effects_remove effs2 x)%list.
Proof.
  induction effs1; eauto; intros.
  specialize (IHeffs1 effs2 x). destruct a. simpl. cases_if; eauto.
  rewrite <- app_comm_cons. rewrite IHeffs1. auto.
Qed.

Lemma effects_remove_untouched : forall effs x y t,
    ((y, t) \in from_list effs) ->
    x <> y ->
    ((y, t) \in from_list (effects_remove effs x)).
Proof.
  induction effs; introv Hyin Hneq; eauto.
  destruct a. simpl. cases_if.
  - eapply IHeffs; eauto. rewrite from_list_cons, in_union, in_singleton in Hyin.
    destruct Hyin as [? | Hyin]; subst; congruence.
  - rewrite from_list_cons, in_union, in_singleton in Hyin.
    destruct Hyin as [? | Hyin]; rewrite from_list_cons, in_union, in_singleton;
      eauto.
Qed.

Lemma effs_remove_dom_subset : forall effs x,
    dom (effects_remove effs x) \c dom effs.
Proof.
  induction effs; introv; eauto using subset_refl.
  destruct a; simpl; cases_if.
  - rewrite cons_to_push, dom_concat, dom_single; hnf; intros.
    specialize (IHeffs x). hnf in IHeffs. specialize (IHeffs _ H).
    rewrite in_union. left; eauto.
  - repeat(rewrite cons_to_push, dom_concat, dom_single); hnf; intros.
    rewrite in_union in H; destruct H; eauto.
    + specialize (IHeffs x). hnf in IHeffs. specialize (IHeffs _ H).
      rewrite in_union. left; eauto.
    + rewrite in_union. right; eauto.
Qed.

Lemma effs_remove_effs : forall t effs x,
    ⊢e t ∶ effs ->
    ⊢e t ∶ effects_remove effs x.
Proof.
  induction 1; eauto.
  - simpl in *. cases_if; eauto.
  - rewrite effects_remove_distrib. eauto.
Qed.

(** The typing of a term with a stack *)
(* ty_stack (Gamma : ctx) (Delta : init_ctx) (ℰs : list eff_ctx)
            (s : stack) (T : typ) (i : init_typ)
            (Es : list effects) (U : typ)
   says that if the current hole has type T and initialisation type i under:
   - the given typing context Gamma
   - initialisation context Delta
   - and only has access to free variables in the topmost eff_ctx of ℰs
   then the overall stack s (hole + awaiting continuations) will end up performing
   effects Es and having type U *)
Inductive ty_stack :
  ctx -> init_ctx -> list eff_ctx -> stack ->
  typ -> init_typ -> list effects -> typ -> Prop :=
  | ty_stack_nil : forall Gamma Delta T U ℰ i,
      Gamma ⊢ T <: U ->
              ty_stack Gamma Delta (ℰ :: nil)
                       nil T i
                       (nil :: nil)%list U
  | ty_stack_let : forall L Gamma Delta ℰ ℰs s t S i i' T effs effss effs' U,
      ty_stack Gamma Delta (ℰ :: ℰs)
               s T i'
               (effs :: effss) U ->
      (forall x, x \notin L -> Gamma & x ~ S ⊢ open x t ∶ T) ->
      (forall x,
          x \notin L ->
          Gamma & x ~ S ⸴ Delta & x ~ i ⸴ dom ℰ \u \{ x} ⊢i open x t ∶ i') ->
      (forall x, x \notin L -> ⊢e open x t ∶ effs') ->
      ty_stack Gamma Delta (ℰ :: ℰs)
               (frame_let t :: s)%list S i
               ((effs' ++ effs) :: effss)%list U
  | ty_stack_ret_local : forall Gamma Delta ℰ ℰs s x S i effs effss T U,
      ty_stack Gamma Delta (ℰ :: ℰs)
               s T local
               (effs :: effss) U ->
      x # effs ->
      Gamma ⊢ trm_var (avar_f x) ∶ T ->
      Gamma ⸴ Delta ⸴ (dom ℰ) ⊢i trm_var (avar_f x) ∶ free ->
      ty_stack Gamma Delta (ℰ :: ℰs)
               (frame_ret x :: s)%list S i
               (effs :: effss)%list U
  | ty_stack_ret_committed : forall Gamma Delta ℰ ℰs s x S i effss T U,
      ty_stack Gamma Delta ℰs
               s T committed
               effss U ->
      Gamma ⊢ trm_var (avar_f x) ∶ T ->
      Gamma ⸴ Delta ⸴ (dom ℰ) ⊢i trm_var (avar_f x) ∶ free ->
      ty_stack Gamma Delta (ℰ :: ℰs)
               (frame_ret x :: s)%list S i
               (nil :: effss)%list U.
Hint Constructors ty_stack : core.

Lemma ty_stack_push : forall Gamma Delta ℰs effs s T i U x T' i',
    x # Gamma ->
    x # Delta ->
    ty_stack Gamma Delta ℰs effs T i s U ->
    ty_stack (Gamma & x ~ T') (Delta & x ~ i') ℰs effs T i s U.
Proof.
  introv HfrG HfrD Hts.
  induction Hts.
  - apply ty_stack_nil.
    apply weaken; auto.
  - specialize (IHHts HfrG HfrD).
    eapply (@ty_stack_let (L \u dom Gamma)); eauto 2.
    + intros. eapply weaken_middle; eauto.
    + intros. eapply init_weaken_middle_same_vars; eauto.
  - specialize (IHHts HfrG HfrD).
    eapply ty_stack_ret_local; eauto.
    + eapply weaken; auto.
    + apply init_weaken_same_vars; auto.
  - specialize (IHHts HfrG HfrD).
    eapply ty_stack_ret_committed; eauto.
    + apply weaken; auto.
    + apply init_weaken_same_vars; auto.
Qed.
Hint Resolve ty_stack_push : core.

Lemma ty_stack_sub : forall Gamma Delta ℰs effs T i s U T',
    ty_stack Gamma Delta ℰs effs T i s U ->
    Gamma ⊢ T' <: T ->
    ok Gamma ->
    ty_stack Gamma Delta ℰs effs T' i s U.
Proof.
  introv Hts Hsub Hok.
  inversions Hts; eauto.
  eapply (@ty_stack_let (L \u (dom Gamma))); eauto 3.
  + intros. eauto using narrow_typing.
  + intros. eapply well_init_narrow_rules; eauto.
Qed.

Lemma ty_stack_eff_ctx_change' : forall Gamma Delta ℰs s T i effss U,
    ty_stack Gamma Delta ℰs s T i effss U ->
    forall ℰ1 ℰs1 ℰ2, dom ℰ1 = dom ℰ2 ->
                 (ℰs = (ℰ1 :: ℰs1)%list ->
                  ty_stack Gamma Delta (ℰ2 :: ℰs1) s T i effss U) /\
                 (ℰs = ℰs1 ->
                  ty_stack Gamma Delta ℰs1 s T i effss U).
Proof.
  introv.
  induction 1; intros; split; intros.
  - inversions H1. econstructor. assumption.
  - inversions H1; auto.
  - pose proof (IHty_stack ℰ1 ℰs1 ℰ2 H3) as [? ?].
    inversions H4. rewrite H3 in *. eauto.
  - pose proof (IHty_stack ℰ1 ℰs1 ℰ2 H3) as [? ?].
    inversions H4. eauto.
  - pose proof (IHty_stack ℰ1 ℰs1 ℰ2 H3) as [? ?].
    inversions H4. rewrite H3 in *. eauto.
  - pose proof (IHty_stack ℰ1 ℰs1 ℰ2 H3) as [? ?].
    inversions H4. eauto.
  - pose proof (IHty_stack ℰ1 ℰs1 ℰ2 H2) as [? ?].
    inversions H3. specialize (H5 eq_refl).
    eapply ty_stack_ret_committed; eauto. congruence.
  - apply eq_sym in H3. subst.
    eapply ty_stack_ret_committed; eauto.
Qed.

Lemma ty_stack_eff_ctx_change : forall Gamma Delta ℰ ℰs s T i effss U ℰ',
    ty_stack Gamma Delta (ℰ :: ℰs) s T i effss U ->
    dom ℰ = dom ℰ' ->
    ty_stack Gamma Delta (ℰ' :: ℰs) s T i effss U.
Proof.
  introv Hts Heq.
  pose proof (ty_stack_eff_ctx_change' Hts (ℰ1:=ℰ) ℰs Heq)
    as [?Hts' _]; eauto.
Qed.

Lemma ty_stack_effs_inv : forall Gamma Delta ℰs s T i effss U,
    ty_stack Gamma Delta ℰs s T i effss U ->
    exists effs effss', effss = (effs :: effss')%list.
Proof.
  inversion 1; eauto.
Qed.

Lemma ty_stack_eff_ctxs_inv : forall Gamma Delta ℰs s T i effss U,
    ty_stack Gamma Delta ℰs s T i effss U ->
    exists ℰ' ℰs', ℰs = (ℰ' :: ℰs')%list.
Proof.
  inversion 1; eauto.
Qed.

Lemma ty_stack_push_ℰ : forall Gamma Delta ℰ ℰs eff effs s T U i x,
    ty_stack Gamma Delta (ℰ           :: ℰs) effs T i s U ->
    ty_stack Gamma Delta (ℰ & x ~ eff :: ℰs) effs T i s U.
Proof with eauto.
  introv Hts.
  remember (ℰ :: ℰs)%list as efts.
  generalize dependent ℰs. generalize dependent ℰ.
  induction Hts; subst.
  - intros. inversions Heqefts...
  - intros. econstructor...
    inversion Heqefts; subst.
    rewrite dom_concat. intros.
    rewrite dom_single. rewrite union_comm. rewrite union_assoc.
    rewrite (union_comm \{x0} (dom ℰ0)).
    pose proof well_init_weaken_vs_rules as [_ [_ [_ [? _]]]]...
  - intros. econstructor...
    inversion Heqefts; subst.
    rewrite dom_concat. rewrite dom_single.
    pose proof well_init_weaken_vs_rules as [_ [_ [_ [? _]]]]...
  - intros.
    inversion Heqefts; subst.
    eapply ty_stack_ret_committed...
    rewrite dom_concat. rewrite dom_single.
    pose proof well_init_weaken_vs_rules as [_ [_ [_ [? _]]]]...
Qed.

Lemma ty_stack_init_ctx_change_sub : forall Gamma Delta ℰs s T i effss U Delta',
    ty_stack Gamma Delta ℰs s T i effss U ->
    more_committed Delta Delta' ->
    (forall x init, (x \in (list_dom_union ℰs)) ->
               binds x init Delta ->
               exists i', binds x i' Delta' /\ init_sub i' init) ->
    ty_stack Gamma Delta' ℰs s T i effss U.
Proof.
  induction 1; intros; auto.
  - assert (forall x init, x \in dom ℰ -> binds x init Delta ->
                            exists i', binds x i' Delta' /\ init_sub i' init).
    { intros. simpl in *.
      assert (x \in dom ℰ \u list_dom_union ℰs) by
          (rewrite in_union; left; auto).
      specialize (H4 _ _ H7 H6). destruct_all. rename x0 into i0.
      exists i0. split; auto. }
    pose proof (well_init_more_committed_renaming_sub _ H1 H3 H5) as [?L ?H].
    clear H1. apply_fresh ty_stack_let as z; eauto.
  - assert (forall x init, x \in dom ℰ -> binds x init Delta ->
                            exists i', binds x i' Delta' /\ init_sub i' init).
    { intros. simpl in *.
      assert (x0 \in dom ℰ \u list_dom_union ℰs) by
          (rewrite in_union; left; auto).
      specialize (H4 _ _ H7 H6). destruct_all. rename x1 into i0.
      exists i0. split; auto. }
    pose proof ((proj54 well_init_more_committed_rules_sub) _ _ _ _ _ H2).
    eapply ty_stack_ret_local; eauto.
  - assert (forall x init, x \in dom ℰ -> binds x init Delta ->
                            exists i', binds x i' Delta' /\ init_sub i' init).
    { intros. simpl in *.
      assert (x0 \in dom ℰ \u list_dom_union ℰs) by
          (rewrite in_union; left; auto).
      specialize (H3 _ _ H6 H5). destruct_all. rename x1 into i0.
      exists i0. split; auto. }
    assert (forall x init, (x \in list_dom_union ℰs) ->
                      binds x init Delta ->
                      exists i', binds x i' Delta' /\ init_sub i' init).
    {intros. simpl in *.
      assert (x0 \in dom ℰ \u list_dom_union ℰs) by
          (rewrite in_union; right; auto).
      specialize (H3 _ _ H7 H6). destruct_all. rename x1 into i0.
      exists i0. split; auto. }
    pose proof ((proj54 well_init_more_committed_rules_sub) _ _ _ _ _ H1).
    eapply ty_stack_ret_committed; eauto.
Qed.

Corollary ty_stack_init_ctx_change : forall Gamma Delta ℰs s T i effss U Delta',
    ty_stack Gamma Delta ℰs s T i effss U ->
    more_committed Delta Delta' ->
    (forall x init, (x \in (list_dom_union ℰs)) ->
               binds x init Delta ->
               binds x init Delta') ->
    ty_stack Gamma Delta' ℰs s T i effss U.
Proof. eauto using ty_stack_init_ctx_change_sub. Qed.

Lemma ty_stack_less_effs_top : forall Gamma Delta ℰs s T i effs0 effss0 U x,
    ty_stack Gamma Delta ℰs s T i (effs0 :: effss0) U ->
    ty_stack Gamma Delta ℰs s T i (effects_remove effs0 x :: effss0) U.
Proof.
  intros. rename H into Hty. dependent induction Hty; simpl; eauto.
  - rename H1 into Hteffs'. clear Hty.
    specialize (IHHty effs effss0 eq_refl).
    rewrite effects_remove_distrib.
    econstructor; eauto using effs_remove_effs; clear H H0.
  - eapply ty_stack_ret_local; eauto 3. unfold notin, not.
    introv Hcontra. apply H. eapply effs_remove_dom_subset. eauto.
Qed.
