Set Implicit Arguments.

Require Import List LibExtra DotTactics Program.Equality.
Require Import
        AbstractSyntax PreTyping Typing GeneralTyping
        InertTightSubtyping
        GeneralToTight TightTyping InvertibleTyping
        RecordAndInertTypes PreciseTyping
        OperationalSemantics
        SubstitutionClass Substitution RenameConstructors
        EffectSubstitution InitSubstitution InitRenaming
        Weakening
        HeapCorrespondence CanonicalForms
        HeapUpdate HeapUpdateCorrespondence
        InertGeneralSubtyping Subenvironments Narrowing
        StackTyping ConfigTyping.
Require Import Effects
        InitVar InitTyping InitTypingLemmas InitVarSubtyping InitWeakening
        HeapCommit WellPointed HeapItemFree SubHeapFree
        InitCorrespondence.

Implicit Types (Gamma : ctx) (Delta : init_ctx) (Sigma : heap) (ℰ : eff_ctx).

Ltac not_inert_init :=
    match goal with
    | [Hin: forall x init, binds x init ?Delta -> _, H: binds ?x ?u ?Delta |- _] =>
      specialize (Hin _ _ H)
    end; destruct_ors; try congruence.

Ltac invert_local :=
  match goal with
  | [Hloc : init_var _ _ ?x local |- _ ] => inversions Hloc
  end.

Lemma inert_init_well_pointed : forall Gamma Delta ℰ x i,
    inert_inits Delta ->
    Gamma ⸴ Delta ⸴ dom ℰ ⊢i trm_var (avar_f x) ∶ i ->
    well_pointed Delta ℰ x.
Proof.
  unfold inert_inits.
  intros * Hin.
  inversion 1; subst.
  - induction H4; subst; auto; try(not_inert_init);
      try(invert_local; not_inert_init; eauto).
    + apply init_var_unspec_sub in H2. discriminate.
    + apply init_var_unspec_sub in H2. discriminate.
  - inversion H0; subst; auto.
Qed.

Local Ltac invert_inits_for_binds :=
  match goal with
  | [ Hloc : init_var ?D (dom ?ℰ) ?x local |- _ ] => inversions Hloc
  | [ Hfr  : init_var ?D (dom ?ℰ) ?x free  |- _ ] => inversions Hfr;
                                                   invert_inits_for_binds
  | _ => idtac
  end.

Lemma inert_init_var_cases : forall Gamma Delta ℰ x i,
    inert_inits Delta ->
    Gamma ⸴ Delta ⸴ dom ℰ ⊢i trm_var (avar_f x) ∶ i ->
    (binds x committed Delta) \/
    (binds x free Delta /\ exists effs, binds x effs ℰ) \/
    (binds x local Delta /\ exists effs, binds x effs ℰ).
Proof.
  unfold inert_inits. inversion 2; subst.
  - dependent induction H5; subst; eauto using dom_to_binds;
      invert_inits_for_binds;
      match goal with
      | [ Hbin : binds ?x ?i ?D |- _] => apply H in Hbin as ?Hiniteq;
                                         destruct Hiniteq;
                                         try(congruence);
                                         eauto using dom_to_binds
      | _ => idtac
      end;
      match goal with
      | [Hc : init_sub unspecified _ |- _]  =>
        apply init_var_unspec_sub in Hc; discriminate
      end.
  - left. eauto using init_typing_committed_inv.
Qed.

Lemma init_var_not_comm_in_vs : forall x vs i Delta,
    init_sub i free ->
    init_var Delta vs x i ->
    x \in vs.
Proof with eauto.
  introv Hisub Hinit. induction Hinit...
  apply init_var_sub_free in Hisub. destruct_all; discriminate.
Qed.

Section Read.
  Lemma preservation_read : forall Gamma Delta ℰs effs effss x a s Sigma c' U,
    ty_config Gamma Delta ℰs (effs :: effss) (trm_sel (avar_f x) a; s; Sigma) U ->
    (trm_sel (avar_f x) a; s; Sigma) ↦ c' ->
    ty_config Gamma Delta ℰs (effs :: effss) c' U.
  Proof.
    inversion 1
      as [?Gamma ?Delta ?Sigma ?ℰ ?ℰs ?s ?t ?T ?i ?U ?effs' ?effs ?effss
           ?Hin ?HinD ?Hhc ?Hfshs ?Hts ?Hty ?Hef ?Hit ?Hecc];
      subst.
    inversion 1; subst.
    rename H6 into HbiS, H7 into Hlhs.
    inversions Hef. inversion Hit; subst.
    { rename H1 into Hcommxa.
      inversion Hcommxa; subst. rename H4 into Hcommx.
      pose proof (commit_typing_implies_bound Hcommx) as Hbixc.
      pose proof (free_sub_heaps_well_committed Hfshs) as Hwc.
      econstructor; eauto using committed_read_inv.
      clear Hwc Hbixc Hcommx Hcommxa H0 Hecc Hit Hts Hfshs HinD H effs0
            ℰs0 ℰ U s effss Delta.
      remember (trm_sel (avar_f x) a) as t eqn:Heq.
      induction Hty; inversions Heq.
      - pose proof (canonical_forms_obj Hin Hhc H) as [? [? [? ?]]];
          binds_eq.
        destruct H1 as [Hlhs' | [y' [Hlhs' Hty']]];
          pose proof (heap_defs_has_inv Hlhs Hlhs'); congruence.
      - eauto using ty_sub. }
    { (* Reading from local case. We can read local, but what's read is unspecified.
         No restrictions on writing. *)
      rename H7 into Hcommxa.
      inversion Hcommxa; subst. rename H5 into Hlocx.
      pose proof (free_sub_heaps_well_committed Hfshs) as Hwc.
      econstructor; eauto.
      - clear Hwc Hlocx Hcommxa H0 Hecc Hit Hts Hfshs HinD H effs0
              ℰs0 ℰ U s effss Delta.
        remember (trm_sel (avar_f x) a) as t eqn:Heq.
        induction Hty; inversions Heq.
        + pose proof (canonical_forms_obj Hin Hhc H) as [? [? [? ?]]];
            binds_eq.
          destruct H1 as [Hlhs' | [y' [Hlhs' Hty']]];
            pose proof (heap_defs_has_inv Hlhs Hlhs'); congruence.
        + eauto using ty_sub.
      - (* Use an equivalent lemma of committed_read_inv *)
        inversion Hfshs; subst. clear H3; clear H8.
        rename H4 into Hfsh. hnf in Hfsh.
        assert (Hbiℰ : exists effs, binds x effs ℰ)
          by eauto using dom_to_binds, init_var_not_comm_in_vs.
        destruct Hbiℰ as [effs Hbiℰ].
        specialize (Hfsh _ _ Hbiℰ) as [_ [itm [HbiS' Hfhi]]].
        apply (binds_functional HbiS) in HbiS'. subst.
        inversions Hfhi. rename H5 into Hfhds.
        hnf in Hfhds. destruct Hfhds as [_ [_ Hwp]].
        apply heap_defs_has_some_points_to in Hlhs as Hyin.
        specialize (Hwp _ Hyin).
        destruct Hwp as [Hycomm | [Hyfree | Hyloc]]; destruct_all; eauto. }
  Qed.
End Read.

Section Write.
  Lemma preservation_write_to_committed : forall Gamma Delta ℰs effs effss x a y s Sigma c' U,
    ty_config Gamma Delta ℰs (effs :: effss) (trm_asn (avar_f x) a (avar_f y); s; Sigma) U ->
    (trm_asn (avar_f x) a (avar_f y); s; Sigma) ↦ c' ->
    binds x committed Delta ->
    binds y committed Delta ->
    exists effs', ty_config Gamma Delta ℰs (effs' :: effss) c' U.
  Proof.
    inversion 1; subst. inversion 1; subst. intros Hbix Hbiy.
    rename H5 into Hin, H6 into HinD, H7 into Hhc, H8 into Hfshs.
    rename H12 into Hts, H13 into Hty, H16 into Hef, H17 into Hec, H11 into Hhup.
    pose proof (free_sub_heaps_well_committed Hfshs) as Hwc.
    pose proof (free_sub_heaps_write_committed_other
                  Hhc Hfshs Hhup Hbix Hbiy) as Hfshs'.
    pose proof (heap_update_inert Hin Hhc Hty Hhup).
    pose proof (inert_assgn_typing Hin Hty).
    econstructor; econstructor;
      eauto using free_sub_heaps_eff_corr_update_committed.
    inversions Hef; auto.
  Qed.

  Lemma preservation_write_well_pointed : forall Gamma Delta ℰ ℰs effs effss x a y s Sigma c' U,
      ty_config Gamma Delta (ℰ :: ℰs) (effs :: effss)
                (trm_asn (avar_f x) a (avar_f y); s; Sigma) U ->
      (trm_asn (avar_f x) a (avar_f y); s; Sigma) ↦ c' ->
      (x \in dom ℰ) ->
      well_pointed Delta ℰ y ->
      exists ℰ' effs', ty_config Gamma Delta (ℰ' :: ℰs) (effs' :: effss) c' U.
  Proof.
    inversion 1
      as [?Gamma ?Delta ?Sigma ?ℰ ?ℰs ?s ?t ?T ?i ?U ?effs' ?effs ?effss
           ?Hin ?HinD ?Hhc ?Hfshs ?Hts ?Hty ?Hef ?Hit ?Hecc]; subst.
    inversion 1; subst. rename H0 into Hred. rename H7 into Hhup.
    intros HinE Hwp.
    pose proof (free_sub_heaps_well_committed Hfshs) as Hwc.
    pose proof (free_sub_heaps_well_localised Hfshs) as Hwl.
    inversion Hfshs; subst.
    rename H7 into Hlsh. rename H3 into Hfsh, H8 into Hfshs'.
    rename H2 into Hani. pose proof (dom_to_binds HinE) as [?eff HbiE].
    pose proof (free_sub_heap_correspondence Hhc Hfsh Hhup HbiE Hwp)
      as [ℰ' [effs1 [Heup [Her ?H]]]].
    pose proof (free_sub_heaps_eff_corr_update
                  effs0 Hfshs Hef HbiE Heup Her Hecc).
    exists ℰ'. exists (nil ++ effs0)%list.
    pose proof (inert_assgn_typing Hin Hty).
    pose proof (heap_update_inert Hin Hhc Hty Hhup).
    pose proof Heup as [HdeqE _].
    assert (all_notin (dom ℰ') (list_dom_union ℰs)) by (rewrite <- HdeqE; auto).
    pose proof (all_notin_fresh _ HbiE Hani) as Hnil.
    pose proof (Hfsh _ _ HbiE) as [_ [?itm [_ Hfhi]]].
    inversion Hfhi as [? ? ? ? ? [Hbif _]]; subst.
    destruct Hbif as [i' Hbif].
    assert (exists iy, binds y iy Delta) as Hbiy by
          (destruct Hwp as [Hbiyc | [[_ Hbiyf] | [_ Hbiyl]]]; eauto).
    pose proof (well_committed_heap_update_free
                  Hwc (proj1 Hbif) (proj2 Hbif) Hhup) as Hwc'.
    destruct Hbiy as [iy Hbiy].
    pose proof (well_localised_heap_update
                  Hwl Hbiy Hhup) as Hwl'.
    pose proof (free_sub_heaps_write_other Hfshs' Hhup Hbiy Hnil Hwc' Hwl').
    assert (free_sub_heaps Gamma Delta Sigma' (ℰ' :: ℰs)).
    { constructor; auto. rewrite <- HdeqE.
      eauto using localised_sub_heap_correspondence_other. }
    assert (Gamma ⸴ Delta ⸴ dom ℰ' ⊢i trm_var (avar_f y) ∶ i).
    { rewrite <- HdeqE; destruct Hwp as [Hwp | Hwp]; inversions Hit; eauto.
      inversions H7; eauto. }
    pose proof (ty_stack_eff_ctx_change Hts HdeqE).
    eauto.
  Qed.

  Lemma preservation_writes : forall Gamma Delta ℰs effss x a y s Sigma c' U,
      ty_config Gamma Delta ℰs effss (trm_asn (avar_f x) a (avar_f y); s; Sigma) U ->
      (trm_asn (avar_f x) a (avar_f y); s; Sigma) ↦ c' ->
      exists ℰs effss', ty_config Gamma Delta ℰs effss' c' U.
  Proof.
    inversion 1; subst; intro Hred.
    rename H into Htc, H3 into Hin, H4 into HinD.
    inversions H15.
    - (* Writing inside committed context *)
      inversions H.
      rename H4 into Hinx, H10 into Hiny.
      inversions Hiny. rename H2 into Hcommy.
      inversions Hinx. rename H2 into Hcommx.
      pose proof (preservation_write_to_committed Htc Hred Hcommx Hcommy)
        as [eff' Htc']; eauto.
    - (* Writing a Committed *)
      rename H10 into Hinx, H11 into Hiny.
      apply init_typing_committed_inv in Hiny as Hcommy.
      pose proof (inert_init_var_cases HinD Hinx)
        as [Hcommx | [[Hfree [xeffs Heffsx]] | [Hloc [xeffs Heffsx]]]].
      + pose proof (preservation_write_to_committed Htc Hred Hcommx Hcommy)
          as [eff' Htc']; eauto.
      + assert (Hwp: well_pointed Delta ℰ y) by auto.
        pose proof (binds_to_dom Heffsx) as HdomEx.
        pose proof (preservation_write_well_pointed Htc Hred HdomEx Hwp)
          as [? [? ?]]; eauto.
      + assert (Hwp: well_pointed Delta ℰ y) by auto.
        pose proof (binds_to_dom Heffsx) as HdomEx.
        pose proof (preservation_write_well_pointed Htc Hred HdomEx Hwp)
          as [? [? ?]]; eauto.
    - (* Writing a free *)
      rename H10 into Hinx, H11 into Hiny.
      assert (Hwp: well_pointed Delta ℰ y) by eauto using inert_init_well_pointed.
      inversions Hinx. inversions H3.
      (* Now there are two cases: free being free and local being free *)
      + (* Local being free *)
        rename H into HdomEx.
        pose proof (preservation_write_well_pointed Htc Hred HdomEx Hwp)
          as [? [? ?]]; eauto.
      + (* The old case *)
        assert (HdomEx : x \in dom ℰ).
        { dependent induction H; eauto.
          apply init_var_sub_free in H0; destruct_all; discriminate. }
        pose proof (preservation_write_well_pointed Htc Hred HdomEx Hwp)
          as [? [? ?]]; eauto.
  Qed.
End Write.

Lemma preservation_return : forall Gamma Delta ℰs effss x y s Sigma c' U,
    ty_config Gamma Delta ℰs effss (trm_var (avar_f x); (frame_ret y :: s)%list; Sigma) U ->
    (trm_var (avar_f x); (frame_ret y :: s)%list; Sigma) ↦ c' ->
    exists Delta' ℰs effss', ty_config Gamma Delta' ℰs effss' c' U.
Proof.
  inversion 1; subst. rename H3 into Hin, H4 into HinD, H5 into Hhc.
  rename H6 into Hfshs, H7 into Hts, H8 into Hty, H13 into Hef.
  rename H15 into Hit, H16 into Hecc. inversion 1; subst. rename H0 into Hred.
  inversion Hef; subst. inversion Hts; subst; eauto.

  (* Returning from a committed frame is dispatched by auto. *)

  - (* Returning from a local *)
    rename H10 into Hts0, H13 into Htyy, H14 into Hiy, H12 into Hynineffs.
    inversion Hecc; subst. rename H3 into Hecc', H5 into Hecco.
    inversion Hfshs; subst. rename Hfshs into Hfshs0.
    rename H2 into Hani, H3 into Hfsh, H8 into Hfshs.
    rename H7 into Hlsh. inversion Hiy; subst.
    rename H4 into Hinitvary.

    (* The effects of y are fulfilled, so we promote only y to local *)
    pose proof (localised_delta_exists Hiy)
      as [Delta' [Hdeq [Hsame [Hmc Hyloc]]]].
    assert (Hyinit : Gamma ⸴ Delta' ⸴ dom ℰ ⊢i trm_var (avar_f y) ∶ local).
    { inversions Hinitvary; eauto 4.
      apply init_var_sub_free in H1; destruct_all; subst; econstructor;
        rename H0 into Hinityloc.
      - apply init_var_local_in_vs in Hinityloc. eauto.
      - apply init_var_free_in_vs in Hinityloc. eauto. }

    exists Delta' (ℰ :: ℰs0) ((nil ++ effs)%list :: effss0).

    pose proof (free_sub_heaps_well_committed Hfshs) as Hwc.
    pose proof (free_sub_heaps_well_localised Hfshs) as Hwl.
    assert (Hlsh' : localised_sub_heap (dom ℰ) Sigma Gamma Delta') by
        (apply removed_eff_corr_delta_localised with
             (Delta := Delta) (x := y) (effs := effs);
         auto using notin_effects_remove).
    assert (exists itmy, binds y itmy Sigma /\
                    localised_heap_item Gamma Delta' itmy) as
        [itmy [HbiyS Hlhiy]].
    { eapply Hlsh'; eauto.
      inversions Hyinit. eauto using init_var_local_in_vs. }

    assert (Hwlh' : well_localised_heap Gamma Delta' Sigma) by
        eauto using removed_eff_corr_delta_well_localised.
    assert (Hwc' : well_committed_heap Gamma Delta' Sigma) by
        eauto using removed_eff_corr_delta_well_committed.
    assert (Hinert' : inert_inits Delta') by
        eauto using localised_delta_is_inert.
    assert (Hfshs' : free_sub_heaps Gamma Delta' Sigma (ℰ :: ℰs0))
      by eauto using free_sub_heaps_localise_other.
    assert (Hts' : ty_stack Gamma Delta' (ℰ :: ℰs0) s T0 local (effs :: effss0) U)
      by (eauto using ty_stack_init_ctx_change_sub,
          localised_delta_is_more_specialized).

    econstructor; eauto.

  - (* Returning from a committed *)
    rename H11 into Hts', H12 into Htyy, H13 into Hiy.
    inversion Hecc; subst. rename H3 into Hecc', H5 into Hecco.
    inversion Hfshs; subst.
    rename H2 into Hani, H3 into Hfsh, H8 into Hfshs', H7 into Hlsh.
    pose proof (committed_delta_exists (free_sub_heap_effs_dom_inits' Hfsh))
      as [Delta' [Hdeq [Hcomm Hkits]]].
    assert (Hef': ⊢e trm_var (avar_f y) ∶ nil) by auto. exists Delta' ℰs0.
    pose proof (committed_delta_is_more_committed Hcomm Hkits) as Hmc.
    pose proof (special_dom_keep _ Hani Hkits) as Hkits'.
    pose proof (ty_stack_init_ctx_change Hts' Hmc Hkits').
    pose proof (committed_delta_is_inert HinD Hdeq Hcomm Hkits) as HinD'.
    pose proof (ty_stack_effs_inv Hts') as [effs' [effss' Heqefs]]; subst.
    pose proof (ty_stack_eff_ctxs_inv Hts') as [ℰ' [ℰs' Heqℰs]]; subst.
    pose proof (free_sub_heaps_well_committed Hfshs) as Hwc.
    pose proof (free_sub_heaps_well_localised Hfshs) as Hwl.
    pose proof (empty_eff_corr_delta_well_commited
                  Hwc Hfsh Hecco Hdeq Hcomm Hkits) as Hwc'.
    pose proof (empty_eff_corr_delta_well_localised
                  Hwl Hcomm Hkits Hdeq Hmc) as Hwl'.
    pose proof (free_sub_heaps_commit_other Hfshs' Hkits' Hmc Hdeq Hwc' Hwl').
    exists ((nil ++ effs') :: effss')%list.
    econstructor; eauto 2.
    inversions Hiy.
    assert (Hyinℰ : y \in dom ℰ) by eauto using init_var_free_in_vs.
    constructor. eauto.
Qed.

Section PreservationApp.
  Lemma preservation_app : forall Gamma Delta ℰs effss f x s Sigma c' U,
    ty_config Gamma Delta ℰs effss
              (trm_app (avar_f f) (avar_f x); s; Sigma) U ->
    (trm_app (avar_f f) (avar_f x); s; Sigma) ↦ c' ->
    ty_config Gamma Delta ℰs effss c' U.
  Proof with eauto.
    inversion 1
      as [?Gamma ?Delta ?Sigma ?ℰ ?ℰs ?s ?t ?T ?i ?U ?effs' ?effs ?effss
           ?Hin ?HinD ?Hhc ?Hfshs ?Hts ?Hty ?Hef ?Hit ?Hecc]; subst.

    (* Invert reduction *)
    inversion 1; subst. rename H0 into Hred. rename H6 into Hbinf.

    remember (trm_app (avar_f f) (avar_f x)) as trm eqn:Heqtrm.
    induction Hty; inversions Heqtrm; eauto using ty_stack_sub.
    clear IHHty IHHty0.
    rename H0 into Hftyp. rename H1 into Hxtyp.
    destruct (canonical_forms_fun Hin Hhc Hftyp)
      as [L [T' [t' [Hbinf' [Hsub Htyop]]]]]; binds_eq.

    econstructor...
    - (* Function body well-typed *)
      eauto using renaming_fun_app.
    - (* Function body effects *)
      inversion Hef; subst...
    - (* Function body init type *)
      pose proof (free_sub_heaps_well_committed Hfshs) as Hwc.
      destruct Hwc as [HGD [HDS Hwc]].
      inversions Hit. econstructor.
      hnf in Hhc. inversion H0; subst. rename H0 into Happ.
      rename H5 into Hcomf. rename H6 into Hcomx.
      inversion Hcomf; subst. rename H3 into HbinfG.
      specialize (Hwc f (item_lit (lit_fun T' t')) HbinfG Hbinf).
      inversions Hwc. rename H3 into Hwc.
      inversions Hwc. rename H3 into Hop.
      eapply renaming_init_fun_app_commit with (L:=L0) (T:=T');
        eauto.
  Qed.
End PreservationApp.

Section PreservationLet.

  Lemma preservation_let_lit : forall Gamma Delta ℰs effss T l t s Sigma c' U,
    ty_config Gamma Delta ℰs effss (trm_lit T l t; s; Sigma) U ->
    (trm_lit T l t; s; Sigma) ↦ c' ->
    exists Gamma' Delta', ty_config (Gamma & Gamma') (Delta & Delta') ℰs effss c' U.
  Proof with eauto.

    inversion 1
      as [?Gamma ?Delta ?Sigma ?ℰ ?ℰs ?s ?t ?T ?i ?U ?effs' ?effs ?effss
           ?Hin ?HinD ?Hhc ?Hfshs ?Hts ?Hty ?Hef ?Hit ?Hecc]; subst.

    (* Invert reduction *)
    inversion 1; subst.
    rename H0 into Hred, H7 into HfrxS.

    pose proof (free_sub_heaps_well_committed Hfshs) as Hwc.
    pose proof Hwc as [HGD [HDS Hci]].

    remember (trm_lit T l t) as trm.
    induction Hty; inversions Heqtrm;
      try(solve[eauto using ty_stack_sub]); clear H2.

    rename H1 into Hop. rename H0 into Htyl.
    exists (x ~ T) (x ~ committed).
    hnf in Hhc. destruct Hhc as [HGS Hstr].
    assert (x # G) as HfrxG by eauto.

    econstructor; eauto 3 using ty_lit_inert_type, renaming_init_lit.
    - eapply heap_correspond_push...
      eapply ty_item_lit_s...
      pose proof weaken_rules as [_ [Hwk _]].
      specialize (Hwk G l T Htyl G x T empty (eq_sym (concat_empty_r G)) HfrxG).
      rewrite concat_empty_r in Hwk...
    - (* Free subheaps *)
      inversion Hit; subst;
        eapply free_sub_heaps_committed_push; eauto 2.
      rename H0 into Hlitcom. inversion Hlitcom...
    - (* Body well-typed *)
      eapply renaming_fresh; eauto using TrmTypingWeakenMiddle.
    - (* Effects *)
      inversion Hef; subst... rename H4 into Hopef.
      eapply renaming_fresh_effs...
  Qed.

  Lemma preservation_let_trm : forall Gamma Delta ℰs effss T t t' s Sigma c' U,
      ty_config Gamma Delta ℰs effss (trm_let T t t'; s; Sigma) U ->
      (trm_let T t t'; s; Sigma) ↦ c' ->
      ty_config Gamma Delta ℰs effss c' U.
  Proof.
    inversion 1
      as [?Gamma ?Delta ?Sigma ?ℰ ?ℰs ?s ?t ?T ?i ?U ?effs' ?effs ?effss
           ?Hin ?HinD ?Hhc ?Hfshs ?Hts ?Hty ?Hef ?Hit ?Hecc]; subst.

    inversion 1; subst. rename H0 into Hred.

    remember (trm_let T t t') as t'' eqn:Heq.
    induction Hty; inversions Heq; subst;
      eauto 4 using ty_stack_sub.
    clear H2 IHHty.
    rename H0 into Htyt. rename H1 into HtyOpen.
    rename U0 into T'. rename G into Gamma.

    pose proof Hhc as [HdomEq Hty_item].

    inversion Hit; subst.
    - rename H0 into HletComm.
      inversion HletComm; subst.
      rename L0 into L'.
      rename H4 into HtComm.
      rename H6 into HOpenComm.
      inversion Hef; subst.
      + econstructor; eauto 3.
        rewrite <- (List.app_nil_l effs).
        eapply (ty_stack_let) with (L:=(L \u L')); eauto.
      + rename L0 into L''.
        rename H4 into Heft. rename H5 into Heft'.
        rewrite <- List.app_assoc in *.
        econstructor; eauto.
        eapply (ty_stack_let) with (L:=(L \u L' \u L'')); eauto.
    - rename L0 into L'. rename i0 into i'.
      rename H7 into HtInit. rename H8 into HOpenInit.
      inversion Hef; subst.
      + econstructor; eauto 3.
        rewrite <- (List.app_nil_l effs).
        eapply (ty_stack_let) with (L:=(L \u L')); eauto.
      + rename L0 into L''.
        rename H4 into Heft. rename H5 into Heft'.
        rewrite <- List.app_assoc in *.
        econstructor; eauto.
        eapply (ty_stack_let) with (L:=(L \u L' \u L'')); eauto.
  Qed.

  (* Preservation for let statements *)
  Lemma preservation_let_var : forall Gamma Delta ℰs effss x t s Sigma c' U,
      ty_config Gamma Delta ℰs effss
                (trm_var (avar_f x); (frame_let t :: s)%list; Sigma) U ->
      (trm_var (avar_f x); (frame_let t :: s)%list; Sigma) ↦ c' ->
      exists effss', ty_config Gamma Delta ℰs effss' c' U.
  Proof with eauto.
    inversion 1; subst.
    rename H3 into G_inert, H4 into D_inert, H5 into G_corresp_S.
    rename H6 into ℰ_subheaps, H7 into let_cont_typ.
    rename H8 into hole_typ, H13 into hole_eff, H15 into hole_init.
    rename H16 into ℰ_corresp_effs.
    inversion 1; subst.
    rename H0 into let_loc_red.
    (* A single variable x has no effects, so effs' = {} *)
    inversions hole_eff. inversions let_cont_typ.
    rename H10 into cont_typ.
    rename H12 into hole_open_typ.
    rename H13 into hole_open_init.
    rename H14 into hole_open_eff.
    exists ((effs' ++ effs0) :: effss0)%list.
    econstructor...
    - eapply renaming_fresh...
    - (* Use a renaming lemma for effects *)
      eapply renaming_fresh_effs...
    - (* Use a renaming lemma for init *)
      eapply renaming_fresh_init...
  Qed.
End PreservationLet.

Section PreservationKon.
  Local Ltac item_inv :=
    match goal with
    | [H : ty_stack ?G ?D ?Es _ ?T _ _ _, _ : ?x # ?S
       |- (exists G' D' ℰs' effss', ty_config _ _ _ _ (_ ; _ ; ?S & ?x ~ ?v) _)] =>
      exists (x ~ T);
      try assert (x # G) by (eauto 3 using heap_correspond_notin_dom);
      pose proof (binds_push_eq x T G);
      pose proof (binds_push_eq x v S);
      try assert (ty_item_s (G & x ~ T) (S & x ~ v) x)
        by (try solve_ty_item_push; eauto using ty_item_s_push);
      try assert (heap_correspond (G & x ~ T) (S & x ~ v))
        by (eauto 3 using heap_correspond_push, heap_correspond_push_obj)
    end.

  (** Well-typedness of constructor applications *)
  Lemma preservation_kon_ty_ds : forall Gamma Sigma k Ts is' T xs avs x ds t,
      inert Gamma ->
      heap_correspond Gamma Sigma ->
      Gamma ⊢ trm_var (avar_f k) ∶ typ_con Ts is' T ->
      length xs = length_s Ts ->
      vars_of_avars xs avs ->
      Gamma ⊢ avs :: Ts ->
      x # Gamma ->
      binds k (item_lit (lit_con Ts is' T ds t)) Sigma ->
      Gamma & x ~ open_vars (x :: xs) T
            ⊢ open_vars (x :: xs) ds ∶ open_vars (x :: xs) T.
  Proof.
    intros * Hin Hhc Htyk Hlen Hxsavs HavsTs HxfrS.
    pose proof (canonical_forms_con Hin Hhc Htyk) as
        [L [?ds [?t [_ [?HbikS [?HbikG [?Hds _]]]]]]].
    intros ?HbikS; binds_eq.
    eapply rename_con_vars_open_push; eauto.
  Qed.

  Lemma preservation_kon_heap_corr :
    forall Gamma Sigma k Ts is' T xs avs x ds t,
      inert Gamma ->
      heap_correspond Gamma Sigma ->
      Gamma ⊢ trm_var (avar_f k) ∶ typ_con Ts is' T ->
      length xs = length_s Ts ->
      vars_of_avars xs avs ->
      Gamma ⊢ avs :: Ts ->
      x # Gamma ->
      binds k (item_lit (lit_con Ts is' T ds t)) Sigma ->
      heap_correspond
        (Gamma & x ~ typ_bnd (open_rec_vars 1 xs T))
        (Sigma & x ~
               item_obj
               (open_rec_vars 1 xs T)
               (open_vars (x :: xs) (heap_defs_of_defs ds))).
  Proof.
    intros * Hin Hhc Htyk Hlen Hxsavs HavsTs HxfrS HbikS.
    apply heap_correspond_push; auto.
    eapply ty_item_obj_s; eauto.
    apply bnd_intro.
    rewrite <- open_vars_S_commut.
    rewrite heap_defs_of_defs_open_vars_commut.
    eapply heap_defs_same_typ.
    eapply preservation_kon_ty_ds; eauto.
  Qed.

  Lemma preservation_kon_ty_body : forall Gamma Sigma k Ts is' T xs avs x ds t,
      inert Gamma ->
      heap_correspond Gamma Sigma ->
      Gamma ⊢ trm_var (avar_f k) ∶ typ_con Ts is' T ->
      length xs = length_s Ts ->
      vars_of_avars xs avs ->
      Gamma ⊢ avs :: Ts ->
      x # Gamma ->
      binds k (item_lit (lit_con Ts is' T ds t)) Sigma ->
      exists T',
      Gamma & x ~ typ_bnd (open_rec_vars 1 xs T)
            ⊢ open_vars (x :: xs) t ∶ open_vars (x :: xs) T'.
  Proof.
    intros * Hin Hhc Htyk Hlen Hxsavs HavsTs HxfrS.
    pose proof (canonical_forms_con Hin Hhc Htyk) as
        [L [?ds [?t [T' [?HbikS [?HbikG [_ ?Htyt]]]]]]];
      intros ?HbikS; binds_eq.
    exists T'.
    apply bnd_intro.
    rewrite <- open_vars_S_commut.
    eapply rename_con_vars_open_push; eauto.
  Qed.

  (** Preservation for constructor applications *)
  Lemma preservation_kon_elim : forall Gamma Delta ℰs effss k avs s Sigma c' U,
      ty_config Gamma Delta ℰs effss (trm_new (avar_f k) avs; s; Sigma) U ->
      (trm_new (avar_f k) avs; s; Sigma) ↦ c' ->
      exists Gamma' Delta' ℰs effss', ty_config (Gamma & Gamma')
                                   Delta' ℰs effss' c' U.
  Proof.
    inversion 1
      as [?Gamma ?Delta ?Sigma ?ℰ ?ℰs ?s ?t ?T ?i ?U ?effs' ?effs ?effss
           ?Hin ?HinD ?Hhc ?Hfshs ?Hts ?Hty ?Hef ?Hit ?Hecc];
      subst.

    (* Invert reduction *)
    inversion 1; subst. rename H0 into Hred, H5 into Hfr, H6 into Hninds.
    rename H8 into Hbik, H9 into Hlen, H10 into Hvavs.

    (* Invert free sub_heaps *)
    pose proof (free_sub_heaps_well_committed Hfshs) as Hwc.
    pose proof Hwc as [HGD [HDS _]].

    (* Induct/Invert on typing *)
    remember (trm_new (avar_f k) avs) as z eqn:Heq.
    induction Hty; inversion Heq; subst;
      eauto 4 using ty_stack_sub.
    clear Heq. clear IHHty. item_inv. clear H4.
    rename H0 into Ht. rename H3 into HfrxG.
    rename Hfr into HfrxS. rename H5 into Hbix.
    rename G into Gamma.

    pose proof (var_typ_con_to_binds Hin Ht) as Hk.
    pose proof (binds_to_dom Hk) as HtyItm; apply Hhc in HtyItm.
    assert (xs = ys) by eauto using vars_of_avars_eq; subst xs.


    (* Canonical forms *)
    pose proof (canonical_forms_con Hin Hhc Ht)
      as [_ [?ds [?t [_ [?H [?H _]]]]]]; repeat binds_eq.
    rename ds0 into ds. rename t0 into t.
    rename Ts0 into Ts. rename is'0 into is'.

    exists (Delta & x ~ free).

    assert (Gamma ⸴ Delta ⊢c trm_var (avar_f k)) as Hcommk.
    { inversion Hit; subst; auto.
      rename H0 into Hnew.
      inversion Hnew; subst; auto. }

    assert (committed_heap_item Gamma Delta
                                (item_lit (lit_con Ts is' T ds t)))
      as HcomItm.
    { inversion Hcommk; subst.
      hnf in Hwc. destruct Hwc as [_ [_ HcomItm]].
      eauto. }
    assert (has_effs (open_vars (x :: ys) t) (def_eff x ds))
      as Hheffs.
    { inversion HcomItm; subst. inversion H5; subst.
      rewrite <- Hlen in H11.
      eauto using renaming_has_eff_con. }
    destruct Hheffs as [beff [Hbeff Hbfl]].

    inversion Hit; subst. (* Case split i *)

    - (* Committed case *)
      exists (x ~ (def_eff x ds) :: ℰ :: ℰs0)%list.
      exists ((beff ++ nil) :: (effs' ++ effs) :: effss0)%list.
      rename H0 into Htypk.
      inversion HcomItm; subst. inversions H5; subst.
      rename H8 into HisTs.
      rename H11 into Hteff. rename H12 into Htinit.
      clear Hbix. econstructor.
      + (* Inert typing context *)
        clear Hteff. clear Htinit.
        eapply inert_all; eauto using heap_correspond_notin_dom.
        constructor.
        apply open_vars_record_type.
        inversion HtyItm; subst; repeat binds_eq.
        eauto using inert_trm_con_record_type.
      + (* Inert init context *)
        eauto using inert_inits_push.
      + (* Heap correspondence *)
        eauto using preservation_kon_heap_corr.
      + (* Free sub heaps *)
        clear Hteff. clear Htinit.
        rewrite def_eff_eq_hds.
        rewrite heap_defs_of_defs_open_vars_commut.
        rewrite hds_effs_open_vars_eq with (n:=0) (ys:=(x::ys)).
        apply free_sub_heaps_new_obj_push with (Gamma:=Gamma); auto.
      + (* Stack typing *)
        clear Hteff. clear Htinit.
        eapply ty_stack_ret_committed; eauto 2.
        * inversions Hef. simpl. eauto.
        * rewrite dom_single. apply init_var_binds.
          apply init_var_free; eauto 2 using in_singleton_self.
      + (* Constructor body well-typed *)
        pose proof (preservation_kon_ty_body
                      Hin Hhc Ht Hlen Hvavs H1 HfrxG Hbik)
          as [? ?]; eauto.
      + (* open_vars version of renaming_fresh_effs *)
        eauto.
      + (* Renaming init. for constructors *)
        clear Hteff.
        inversion Htypk; subst.
        assert (forall y, y \in from_list ys -> binds y committed Delta) as
            Hyscom by (eapply well_committed_vars_of_avars; eauto).
        rename H9 into Hwcavs. rename H8 into Hac. rename H4 into Hwck.
        rename H5 into Hktyp.
        replace is'0 with is' in * by
            (apply var_typ_con_to_binds in Hktyp; repeat binds_eq;
             auto).
        rewrite dom_single. rewrite <- (union_empty_l \{x}).
        apply ty_open_implies_ty_bnd_init.
        rewrite <- open_vars_S_commut.
        eapply renaming_con; eauto 3.
        apply all_comm_unspec_inits; eauto 3.
        apply length_vars_of_avars in Hvavs. congruence.
      + (* Effects correspondence *)
        econstructor; eauto 3. rewrite app_nil_r.
        hnf. introv Hx0bin.
        apply binds_to_dom in Hx0bin as Hx0eq.
        rewrite dom_single in Hx0eq.
        rewrite in_singleton in Hx0eq. subst.
        apply binds_single_eq_inv in Hx0bin as Heffs'0eq. subst. clear Hx0bin.
        rewrite Hbfl; auto.

    - (* Local case *)
      exists (ℰ & x ~ (def_eff x ds) :: ℰs0)%list.
      exists ((beff ++ (effs' ++ effects_remove effs x) ++ nil) :: effss0)%list.
      rename H8 into Htypk. rename H10 into Havin.
      rename H4 into Hkcom.
      inversion HcomItm; subst. inversions H5; subst.
      rename H11 into Hteff. rename H12 into Htinit.
      rename H8 into Hlenis'.
      clear Hbix. econstructor.
      + (* Inert typing context *)
        eapply inert_all; eauto using heap_correspond_notin_dom. constructor.
        apply open_vars_record_type.
        inversion HtyItm; subst; repeat binds_eq.
        eauto using inert_trm_con_record_type.
      + (* Inert init context *)
        eauto using inert_inits_push.
      + (* Heap correspondence *)
        eauto using preservation_kon_heap_corr.
      + (* Free sub heaps *)
        clear Hteff. clear Htinit.
        rewrite def_eff_eq_hds.
        rewrite heap_defs_of_defs_open_vars_commut.
        rewrite hds_effs_open_vars_eq with (n:=0) (ys:=(x::ys)).
        apply free_sub_heaps_obj_push; eauto.
      + (* Stack typing *)
        clear Hteff. clear Htinit.
        eapply ty_stack_ret_local; eauto 2.
        * inversions Hef. simpl. rewrite app_nil_r.
          eapply ty_stack_push in Hts; eauto 1.
          eapply ty_stack_push_ℰ; eauto 2 using ty_stack_less_effs_top.
        * inversions Hef. simpl. rewrite app_nil_r.
          eauto 2 using notin_effects_remove.
        * apply init_var_binds. apply init_var_free; eauto using binds_push_eq.
          rewrite dom_concat. rewrite in_union. right.
          rewrite dom_single. rewrite in_singleton. congruence.
      + (* Constructor body well-typed *)
        pose proof (preservation_kon_ty_body
                      Hin Hhc Ht Hlen Hvavs H1 HfrxG Hbik)
          as [? ?]; eauto.
      + (* open_vars version of renaming_fresh_effs *)
        auto.
      + (* open_vars version of renaming_fresh_init *)
        clear Hteff.
        apply ty_open_implies_ty_bnd_init.
        replace (open x (open_rec_vars 1 ys T)) with (open_vars (x :: ys) T)
          by (simpl; rewrite open_vars_S_commut; congruence).
        rewrite dom_concat, dom_single.
        eapply renaming_con; eauto 3.
        assert (typ_con Ts0 is'0 T0 = typ_con Ts is' T)
          as Heq by
              (apply var_typ_con_to_binds in Htypk;
               repeat binds_eq; auto);
          inversion Heq; subst; clear Heq; auto.
      + (* Effects correspondence *)
        inversions Hef. simpl. rewrite app_nil_r.
        simpl in Hecc. econstructor.
        * inversions Hecc. assumption.
        * hnf. introv Hx0bin. introv Heffin.
          rewrite from_list_concat.
          apply binds_concat_inv in Hx0bin as Hx0.
          destruct Hx0.
          { apply binds_single_inv in H0. destruct H0. subst.
              rewrite in_union. left.
              rewrite <- Hbfl.
              assumption. }
          { destruct H0. inversions Hecc. rename H9 into Heffscor. clear H7.
            hnf in Heffscor. rewrite in_union. right.
            specialize (Heffscor _ _ H3 _ Heffin).
            inversions Hfshs. clear H6. clear H11. clear H12. rename H7 into Hfsh.
            hnf in Hfsh. specialize (Hfsh _ _ H3).
            destruct Hfsh as [Hlblsame _]. destruct eff.
            specialize (Hlblsame _ _ Heffin). subst. clear H3.
            rewrite dom_single, notin_singleton in H0. rename H0 into Hneq.
            eauto 2 using effects_remove_untouched. }
  Qed.
End PreservationKon.

Lemma preservation_var :  forall Gamma Delta ℰs effss x s Sigma c U,
    ty_config Gamma Delta ℰs effss (trm_var (avar_f x); s; Sigma) U ->
    (trm_var (avar_f x); s; Sigma) ↦ c ->
    exists Gamma' Delta' ℰs' effss', ty_config (Gamma & Gamma') Delta' ℰs' effss' c U.
Proof.
  inversion 1
    as [?Gamma ?Delta ?Sigma ?ℰ ?ℰs ?s ?t ?T ?i ?U ?effs' ?effs ?effss
         ?Hin ?HinD ?Hhc ?Hfshs ?Hts ?Hty ?Hef ?Hit ?Hecc]; subst.
  inversion 1; subst.
  - (* Return from constructor *)
    eexists empty. rewrite concat_empty_r.
    eauto using preservation_return.
  - (* Let continuation awaiting *)
    eexists empty. rewrite concat_empty_r.
    eauto using preservation_let_var.
Qed.

Local Ltac empty_exists :=
  eexists empty; rewrite concat_empty_r;
  match goal with
  | [ D : init_ctx |- _] => exists D
  end.

Local Ltac same_effs :=
  match goal with
  | [H : eff_ctx_corr ?ℰ ?effss |- _ ] =>
    exists ℰ effss
  end.

Theorem preservation : forall Gamma Delta ℰs effss c c' U,
    ty_config Gamma Delta ℰs effss c U ->
    c ↦ c' ->
    exists
      Gamma' Delta' ℰs' effss', ty_config (Gamma & Gamma') Delta' ℰs' effss' c' U.
Proof with eauto.
  inversion 1
    as [?Gamma ?Delta ?Sigma ?ℰ ?ℰs ?s ?t ?T ?i ?U ?effs' ?effs ?effss
         ?Hin ?HinD ?Hhc ?Hfshs ?Hts ?Hty ?Hef ?Hit ?Hecc]; subst.
  intros Hred.
  induction Hty; eauto 2 using preservation_var.
  - (* Application *)
    empty_exists; same_effs.
    eauto using preservation_app.
  - (* Constructor *)
    eauto using preservation_kon_elim.
  - (* Read *)
    empty_exists; same_effs.
    eauto using preservation_read.
  - (* Write *)
    empty_exists.
    eauto using preservation_writes.
  - (* Term let *)
    empty_exists; same_effs.
    eauto using preservation_let_trm.
  - (* Let literals *)
    pose proof (@preservation_let_lit G Delta
                                      (ℰ :: ℰs0)
                                      ((effs' ++ effs)%list :: effss0)
                                      T l u s Sigma c' U
                                      H Hred) as Hpl.
    destruct Hpl as [Gamma' [Delta' Hpl]]...
  - (* Subtyping *)
    eauto using ty_stack_sub.
Qed.
