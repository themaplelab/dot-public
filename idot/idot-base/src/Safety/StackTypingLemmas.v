Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import
        AbstractSyntax PreTyping Typing GeneralTyping
        RecordTypes InertTypes DefRecordInertTyping
        StackTyping Substitution Weakening
        HeapCorrespondence HeapUpdate
        Subenvironments Narrowing.
Require Import Effects InitLookupLemmas InitWeakening
        CommittedSubHeap CommittedSubHeapLemmas
        FreeSubHeapStack FreeSubHeapStackLemmas InitNarrowing.

(** * Stack Typing Lemmas *)
(** This module collects lemmas about stack typing. *)

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
    eapply ty_stack_ret_free; eauto.
    + apply weaken; auto.
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
    (* rewrite dom_empty in H0; symmetry in H0. *)
    (* apply empty_dom_eq_empty in H0; subst; auto. *)
  - inversions H1; auto.
  - pose proof (IHty_stack ℰ1 ℰs1 ℰ2 H3) as [? ?].
    inversions H4. rewrite H3 in *. eauto.
  - pose proof (IHty_stack ℰ1 ℰs1 ℰ2 H3) as [? ?].
    inversions H4. eauto.
  - pose proof (IHty_stack ℰ1 ℰs1 ℰ2 H2) as [? ?].
    inversions H3. rewrite H2 in *. eauto.
  - pose proof (IHty_stack ℰ1 ℰs1 ℰ2 H2) as [? ?].
    inversions H3. eauto.
  - pose proof (IHty_stack ℰ1 ℰs1 ℰ2 H2) as [? ?].
    inversions H3. rewrite H2 in *. eauto.
  - pose proof (IHty_stack ℰ1 ℰs1 ℰ2 H2) as [? ?].
    inversions H3. eauto.
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

Lemma ty_stack_init_ctx_change : forall Gamma Delta ℰs s T i effss U Delta',
    ty_stack Gamma Delta ℰs s T i effss U ->
    more_committed Delta Delta' ->
    (forall x init, (x \in (list_dom_union ℰs)) ->
               binds x init Delta ->
               binds x init Delta') ->
    ty_stack Gamma Delta' ℰs s T i effss U.
Proof.
  induction 1; intros; auto.
  - assert (forall x init, x \in dom ℰ -> binds x init Delta -> binds x init Delta').
    { intros. simpl in H4. apply H4; auto. rewrite in_union; auto. }
    pose proof (well_init_more_committed_renaming _ H1 H3 H5) as [?L ?H].
    clear H1. apply_fresh ty_stack_let as z; eauto.
  - assert (forall x init, x \in dom ℰ -> binds x init Delta -> binds x init Delta').
    { intros. simpl in *. apply H3; auto. rewrite in_union; auto. }
    pose proof ((proj54 well_init_more_committed_rules) _ _ _ _ _ H1).
    eapply ty_stack_ret_free; eauto.
  - assert (forall x init, x \in dom ℰ -> binds x init Delta -> binds x init Delta').
    { intros. simpl in *. apply H3; auto. rewrite in_union; auto. }
    assert (forall x init, (x \in list_dom_union ℰs) ->
                      binds x init Delta -> binds x init Delta').
    { intros. simpl in *. apply H3; auto. rewrite in_union; auto. }
    pose proof ((proj54 well_init_more_committed_rules) _ _ _ _ _ H1).
    eapply ty_stack_ret_committed; eauto.
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
