Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import
        AbstractSyntax PreTyping Typing GeneralTyping
        RecordAndInertTypes
        OperationalSemantics Substitution Weakening
        HeapCorrespondence HeapUpdate
        Subenvironments Narrowing.
Require Import Effects InitVar InitTyping InitWeakening HeapCommit HeapItemFree SubHeapFree
        InitCorrespondence InitNarrowing.

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
              ty_stack Gamma Delta (ℰ :: nil) (* (empty :: nil) *)
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
  (* In the two return rules we say specify that x in frame_ret x has free
     type because free is the most general type (in init_var_binds, the
     premise init_var Delta vs x i basically gives that anything has type free) *)
  | ty_stack_ret_free : forall Gamma Delta ℰ ℰs s x S i effs effss T U,
      ty_stack Gamma Delta (ℰ :: ℰs)
               s T free
               (effs :: effss) U ->
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
    eapply ty_stack_ret_free; eauto.
    + apply weaken; auto.
    + apply init_weaken_same_vars; auto.
  - eapply ty_stack_ret_committed; eauto.
    + apply weaken; auto.
    + apply init_weaken_same_vars; auto.
Qed.
Hint Resolve ty_stack_push : core.

Lemma ty_stack_push_nil : forall Gamma Delta ℰ ℰs effs s T i U x T' i',
    x # Gamma ->
    x # Delta ->
    ty_stack Gamma Delta (ℰ :: ℰs) effs T i s U ->
    ty_stack (Gamma & x ~ T') (Delta & x ~ i') (ℰ & x ~ nil :: ℰs) effs T i s U.
Proof.
  introv HfrG HfrD. remember (ℰ :: ℰs)%list as ℰs' eqn:Heq.
  intros Hts; induction Hts; inversion Heq; subst.
  - apply ty_stack_nil.
    apply weaken; auto.
  - eapply (@ty_stack_let (L \u dom Gamma)); eauto 2.
    + intros. eapply weaken_middle; eauto.
    + intros.
      rewrite dom_concat, dom_single, <- union_assoc, (union_comm (\{ x})), union_assoc.
      eapply init_weaken_middle; eauto.
  - eapply ty_stack_ret_free; eauto.
    + apply weaken; auto.
    + rewrite dom_concat, dom_single.
      apply init_weaken; auto.
  - eapply ty_stack_ret_committed; eauto.
    + apply weaken; auto.
    + rewrite dom_concat, dom_single.
      apply init_weaken; auto.
Qed.
Hint Resolve ty_stack_push_nil : core.

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
