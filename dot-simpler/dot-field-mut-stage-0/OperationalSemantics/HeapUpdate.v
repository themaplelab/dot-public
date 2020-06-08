(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import AbstractSyntax GeneralTyping.

(** * Updating the Heap *)
Inductive defs_update : defs -> trm_label -> var -> defs -> Prop :=
| defs_update_var : forall ds a t x,
    defs_update (defs_cons ds (def_trm a t)) a x (defs_cons ds (def_trm a (trm_var (avar_f x))))
| defs_update_push : forall ds d a x ds',
    defs_update ds a x ds' ->
    defs_update (defs_cons ds d) a x (defs_cons ds' d).

Definition heap_update (s : heap) (x : var) (a : trm_label) (y : var) (s' : heap) :=
  ok s /\
  ok s' /\
  (dom s) = (dom s') /\
  (forall z v, z <> x ->
          binds z v s ->
          binds z v s') /\
  exists T ds ds', binds x (item_obj T ds) s /\
              defs_update ds a y ds' /\
              binds x (item_obj T ds') s'.

Lemma defs_update_open : forall x ds a y ds',
    defs_update ds a y ds' ->
    forall ds1, ds = (open x ds1) ->
           exists ds1', ds' = (open x ds1').
Proof.
  introv H. induction H; intros.
  - destruct ds1; inversions H.
    exists (defs_cons ds1 (def_trm a (trm_var (avar_f x0)))).
    reflexivity.
  - destruct ds1; inversion H0.
    pose proof (IHdefs_update _ H2) as [?ds ?].
    subst ds'. exists (defs_cons ds0 d0).
    reflexivity.
Qed.

Lemma defs_update_hasnt: forall ds a x ds' l,
    defs_update ds a x ds' ->
    defs_hasnt ds l ->
    defs_hasnt ds' l.
Proof.
  introv H; gen l; induction H; intros.
  - unfold defs_hasnt; simpl.
    inversion H; cases_if.
    auto.
  - unfold defs_hasnt; simpl.
    assert (label_of d <> l).
    { inversion H0. cases_if. auto. }
    cases_if.
    assert (defs_hasnt ds l).
    { inversion H0. cases_if. auto. }
    apply IHdefs_update; auto.
Qed.

Lemma defs_update_hasnt_inv: forall ds a x ds',
    defs_update ds a x ds' ->
    defs_hasnt ds (label_trm a) -> False.
Proof.
  introv H. induction H; intros.
  - inversion H; cases_if; congruence.
  - assert (defs_hasnt ds (label_trm a)).
    { inversion H0; cases_if. }
    auto.
Qed.

Require Import RecordAndInertTypes PreciseTyping HeapCorrespondence CanonicalForms.

Lemma defs_update_typing: forall G (ds : defs) U (ds' : defs) a x T,
    defs_update ds a x ds' ->
    record_type U ->
    G ⊢ ds ∶ U ->
    record_has U (dec_trm a T T) ->
    G ⊢ trm_var (avar_f x) ∶ T ->
    G ⊢ ds' ∶ U.
Proof.
  introv H; gen U T. induction H; intros.
  - inversions H0. inversions H7.
    inversions H1. eauto.
    constructor; eauto.
    inversions H7.
    assert (T1 = T) by (eapply (unique_rcd_trm H); eauto); subst.
    eauto.
  - inversions H1. inversions H.
    assert (record_type T0).
    { destruct H0 as [ls ?H]. inversions H0.
      exists ls0; auto. }
    inversion H2; subst T0 U D0.
    + constructor; eauto using defs_update_hasnt.
    + inversions H9. inversions H8; simpl in *.
      exfalso. eapply defs_update_hasnt_inv; eauto.
Qed.

Lemma heap_update_inert: forall G s s' x y a T,
    inert G ->
    heap_correspond G s ->
    G ⊢ trm_asn (avar_f x) a (avar_f y) ∶ T ->
    heap_update s x a y s' ->
    heap_correspond G s'.
Proof.
  introv Hin Hst Hty Hsto.
  remember (trm_asn (avar_f x) a (avar_f y)) as t.
  induction Hty; inversions Heqt; eauto. clear IHHty IHHty0.
  pose proof (canonical_forms_obj Hin Hst H) as [?S [?ds [?t [?H [?H ?H]]]]].
  unfold heap_update in Hsto.
  destruct Hsto as
      [?Hoks [?Hoks' [?Hdom [?Hbi [?T [?ds [?ds' [?H [?Hdefup ?Hbis']]]]]]]]].
  pose proof (binds_functional H4 H1) as Hveq; inversions Hveq; clear H1.
  destruct Hst as [?H [?H [?H ?H]]].
  unfold heap_correspond; repeat_split_right; try congruence; auto.
  intros. clear H5 H1.
  pose proof (dom_to_binds H8) as [?T ?H].
  pose proof (H7 _ H8) as Htyv.
  rewrite H6 in H8.
  pose proof (dom_to_binds H8) as [?v ?H].
  pose proof (defs_update_open x Hdefup ds eq_refl) as [?ds' ?Hds'].
  destruct (var_decide x0 x).
  - subst.
    eapply ty_item_obj_s; eauto.
    + pose proof (var_typ_rcd_to_binds Hin H) as [?S [?T [?Hbi ?H]]].
      pose proof (binds_functional Hbi0 H1); subst T0; clear Hbi0.
      inversions Htyv;
        match goal with
        | [ H : binds ?x ?T ?G, H' : binds ?x ?T' ?G |- _] =>
          pose proof (binds_functional H H'); congruence
        end.
    + inversions Htyv; repeat binds_eq. rewrite H14 in *. clear H10 H11.
      pose proof (var_typ_rcd_to_binds Hin H)
        as [?S [?T [?Hbi [?Hrh [?H ?H]]]]]. binds_eq.
      eapply defs_update_typing; eauto.
      pose proof (binds_inert H1 Hin). inversions H10.
      apply open_record_type; auto.
  - apply (Hbi _ _ n) in H5. rename n into Hneq.
    inversions Htyv; eauto.
Qed.

Lemma defs_update_exists: forall ds a t x,
  defs_has ds (def_trm a t) ->
  exists ds', defs_update ds a x ds'.
Proof.
  intros ds; induction ds; intros.
  - inversion H.
  - inversion H. cases_if.
    + inversions H1.
      exists (defs_cons ds (def_trm a (trm_var (avar_f x)))); constructor.
    + apply (IHds a t x) in H1.
      destruct H1 as [ds' ?H].
      exists (defs_cons ds' d). constructor; auto.
Qed.

Lemma heap_updateable: forall s x U ds a t y,
    ok s ->
    binds x (item_obj U (open x ds)) s ->
    defs_has (open x ds) (def_trm a t) ->
    exists s' ds',
      ok s' /\
      dom s = dom s' /\
      (forall z v, z <> x ->
              binds z v s ->
              binds z v s') /\
      defs_update (open x ds) a y ds' /\
      binds x (item_obj U ds') s'.
Proof.
  intros s; induction s using env_ind; intros.
  - exfalso. apply (binds_empty_inv H0).
  - pose proof (defs_update_exists y H1) as [?ds' ?H].
    pose proof (binds_push_inv H0) as [[?H ?H] | [?H ?H]]; subst.
    + exists (s & x ~ item_obj U (ds')) ds'.
      repeat_split_right; auto.
      * simpl_dom; auto.
      * intros.
        pose proof (binds_push_inv H4) as [[?H ?H] | [?H ?H]]; try congruence.
        auto.
    + assert (Hoks: ok s) by auto.
      pose proof (IHs x0 _ _ _ _ y Hoks H4 H1) as
          [?s' [?ds' [?Hoks' [?Hdeq [?H [?H ?H]]]]]].
      exists (s' & x ~ v) (ds'0). repeat_split_right; auto.
      * apply ok_push; auto 1.
        pose proof (ok_push_inv H) as [_ ?H].
        rewrite <- Hdeq; auto.
      * simpl_dom. rewrite Hdeq; auto.
      * intros.
        pose proof (binds_push_inv H9) as [[?H ?H] | [?H ?H]]; subst; auto.
Qed.

Lemma heap_update_exists: forall G s x y a S T,
    inert G ->
    heap_correspond G s ->
    G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T) ->
    G ⊢ trm_var (avar_f y) ∶ S ->
    exists s', heap_update s x a y s'.
Proof.
  introv Hin Hst Hty HTy.
  pose proof (canonical_forms_obj).
  pose proof (canonical_forms_obj Hin Hst Hty) as [?S [?ds [?t [?Hbi [?Hdef _]]]]].
  unfold heap_correspond in Hst.
  destruct Hst as [?H [Hok ?H]].
  pose proof (heap_updateable ds y Hok Hbi Hdef) as [?s' [?ds' [?H ?H]]]; destruct_all.
  exists s'; unfold heap_update; repeat_split_right; auto.
  exists S0 (open x ds) ds'; repeat_split_right; auto.
Qed.
