Set Implicit Arguments.

Require Import DotTactics LibExtra AbstractSyntax.
Require Import Typing GeneralTyping.
Require Import RecordAndInertTypes PreciseTyping HeapCorrespondence CanonicalForms.
Require Import HeapUpdate.

Lemma defs_update_typing: forall G hds U hds' a x T,
    defs_update hds a x hds' ->
    record_type U ->
    G ⊢ hds ∶ U ->
    record_has U (dec_trm a T T) ->
    G ⊢ trm_var (avar_f x) ∶ T ->
    G ⊢ hds' ∶ U.
Proof.
  introv H; gen U T. induction H; intros.
  - inversions H0.
    + inversions H7.
      * inversions H1. eauto.
      * inversions H1. eauto.
    + constructor; eauto.
      inversions H7.
      * assert (T1 = T) by (eapply (unique_rcd_trm H); eauto); subst.
        eauto.
      * assert (T1 = T) by (eapply (unique_rcd_trm H); eauto); subst.
        eauto.
  - inversions H1.
    + inversions H.
    + assert (record_type T0).
      { destruct H0 as [ls ?H]. inversions H0.
        exists ls0; auto. }
      inversion H2; subst T0 U D0.
      * constructor; eauto using defs_update_hasnt.
      * inversions H9. inversions H8; simpl in *.
        -- exfalso. eapply defs_update_hasnt_inv; eauto.
        -- exfalso. eapply defs_update_hasnt_inv; eauto.
Qed.

Lemma heap_update_correspond : forall Gamma Sigma1 x T hds hds' Sigma2,
    x # Sigma2 ->
    heap_correspond Gamma (Sigma1 & x ~ item_obj T hds & Sigma2) ->
    Gamma ⊢ hds' ∶ open x T ->
    heap_correspond Gamma (Sigma1 & x ~ item_obj T hds' & Sigma2).
Proof.
  intros * Hfr [Hdomeq Hitms] Hty.
  split.
  - rewrite ? dom_concat, ? dom_single in *; congruence.
  - intros x' Hindom.
    pose proof (Hitms x' Hindom) as Htyitem.
    inversion Htyitem as [ ?Gamma ?s ?x ?l ?T' ?HbiG ?HbiS ?Htylit
                         | ?Gamma ?s ?x ?T' ?hds ?HbiG ?HbiS ?Htydefs];
      subst.
    + eapply ty_item_lit_s; eauto.
      eapply binds_middle_change; eauto; congruence.
    + assert (binds x (item_obj T hds)
                    (Sigma1 & x ~ item_obj T hds & Sigma2)) by auto.
      assert (binds x (item_obj T hds')
                    (Sigma1 & x ~ item_obj T hds' & Sigma2)) by auto.
      destruct (var_decide x' x); subst;
        repeat binds_eq;
          eauto using binds_middle_update.
Qed.

Lemma heap_update_inert: forall G s s' x y a T,
    inert G ->
    heap_correspond G s ->
    G ⊢ trm_asn (avar_f x) a (avar_f y) ∶ T ->
    heap_update s x a y s' ->
    heap_correspond G s'.
Proof.
  introv Hin Hst Hty Hsto.
  remember (trm_asn (avar_f x) a (avar_f y)) as t eqn:Heqt.
  induction Hty; inversions Heqt; eauto. clear IHHty IHHty0.
  pose proof (var_typ_rcd_to_binds Hin H)
    as [U' [ST [HxG [Hrhs [Hsub1 Hsub2]]]]].
  pose proof (canonical_forms_obj Hin Hst H) as [?S [?ds [?H ?H]]].
  unfold heap_update in Hsto.
  destruct Hsto as
      [T' [hds [hds' [Sigma1 [Sigma2 [Heq [Hfr [Hup Hs]]]]]]]]; subst.
  assert (binds x (item_obj T' hds) (Sigma1 & x ~ item_obj T' hds & Sigma2)) as Hbi
      by auto; binds_eq.
  eapply heap_update_correspond; eauto.

  destruct Hst as [?Hdomeq ?Htyitms].
  assert (x \in dom (Sigma1 & x ~ item_obj T' hds & Sigma2)) as HGSx
      by eauto using binds_to_dom.
  rewrite <- Hdomeq in HGSx. apply Htyitms in HGSx.
  inversion HGSx as [|?Gamma ?s ?x ?U ?hds ?HxG ?Hxs ?Hty];
    repeat binds_eq.

  eapply defs_update_typing with (T:=ST); eauto.
  eapply ty_defs_record_type with (ds:=hds0); eauto.
Qed.

Lemma defs_update_exists: forall hds a o x,
  labels_has hds (heap_def_trm a o) ->
  exists hds', defs_update hds a x hds'.
Proof.
  intros hds; induction hds as [| d hds IHds]; intros.
  - inversion H.
  - inversion H. cases_if.
    + inversions H1.
      exists (cons (heap_def_trm a (Some x)) hds); constructor.
    + apply (IHds a o x) in H1.
      destruct H1 as [ds' ?H].
      exists (cons d ds'). constructor; auto.
Qed.

Lemma heap_updateable: forall s x U hds a o y,
    binds x (item_obj U hds) s ->
    labels_has hds (heap_def_trm a o) ->
    exists s' hds',
      dom s = dom s' /\
      (forall z v, z <> x ->
              binds z v s ->
              binds z v s') /\
      defs_update hds a y hds' /\
      binds x (item_obj U hds') s'.
Proof.
  intros s; induction s using env_ind; intros.
  - exfalso. eauto using binds_empty_inv.
  - pose proof (defs_update_exists y H0) as [?ds' ?H].
    pose proof (binds_push_inv H) as [[?H ?H] | [?H ?H]]; subst.
    + exists (s & x ~ item_obj U (ds')) ds'.
      repeat_split_right; auto.
      * simpl_dom; auto.
      * intros.
        pose proof (binds_push_inv H3) as [[?H ?H] | [?H ?H]];
          try congruence.
        auto.
    + pose proof (IHs x0 _ _ _ _ y H3 H0) as
          [?s' [?ds' [?Hdeq [?H [?H ?H]]]]].
      exists (s' & x ~ v) (ds'0). repeat_split_right; auto.
      * simpl_dom. rewrite Hdeq; auto.
      * intros.
        pose proof (binds_push_inv H8) as [[?H ?H] | [?H ?H]]; subst; auto.
Qed.

Lemma heap_update_exists: forall G s x y a S T,
    inert G ->
    heap_correspond G s ->
    G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T) ->
    G ⊢ trm_var (avar_f y) ∶ S ->
    exists s', heap_update s x a y s'.
Proof.
  introv Hin Hst Hty HTy.
  pose proof (canonical_forms_obj Hin Hst Hty) as [?S [?ds [?Hbi ?Hdef]]].
  unfold heap_correspond in Hst.
  destruct Hst as [?H ?H].
  destruct Hdef as [Hdef | [?y [Hdef _]]].
  - pose proof (heap_updateable y Hbi Hdef)
      as [?s' [?ds' [?H [?H [?H HxS]]]]].
    pose proof (binds_to_middle Hbi)
      as [Sigma1 [Sigma2 [Heq Hfr]]]; subst.
    eexists. unfold heap_update.
    repeat eexists; eauto.
  - pose proof (heap_updateable y Hbi Hdef)
      as [?s' [?ds' [?H [?H [?H HxS]]]]].
    pose proof (binds_to_middle Hbi)
      as [Sigma1 [Sigma2 [Heq Hfr]]]; subst.
    eexists. unfold heap_update.
    repeat eexists; eauto.
Qed.
