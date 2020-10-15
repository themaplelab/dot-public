(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Typing
        InitVar InitTyping InitVarSubtyping InitWeakening
        GeneralTyping.
Require Import HeapUpdate.

(** * Commited part of heaps *)
(* Heap definitions (in objects) being committed given an initialisation context *)
Inductive committed_heap_def : init_ctx -> heap_def -> Prop :=
(* Committed when it's a type declaration *)
| committed_heap_def_typ : forall Delta A T,
    committed_heap_def Delta (heap_def_typ A T)

(* If it's a term and Delta says the term is committed then the heap def is committed *)
| committed_heap_def_trm : forall Delta a x,
    binds x committed Delta ->
    committed_heap_def Delta (heap_def_trm a (Some x)).

Inductive committed_heap_defs : init_ctx -> heap_defs -> Prop :=
| committed_heap_defs_nil : forall Delta,
    committed_heap_defs Delta nil

| committed_heap_defs_cons : forall Delta hd hds,
    committed_heap_defs Delta hds ->
    committed_heap_def Delta hd ->
    committed_heap_defs Delta (cons hd hds).

(* Heap items being committed *)
Inductive committed_heap_item :
  ctx -> init_ctx -> item -> Prop :=
(* Literals are committed if they're committed according to Gamma and Delta *)
| committed_heap_lit : forall Gamma Delta l,
    Gamma ⸴ Delta ⊢c l ->
    committed_heap_item Gamma Delta (item_lit l)
(* An object is committed when all its definitions are committed *)
| committed_heap_obj : forall Gamma Delta T hds,
    committed_heap_defs Delta hds ->
    committed_heap_item Gamma Delta (item_obj T hds).

(* A heap Sigma is well committed with respect to a typing context Gamma and an initialisation context
   Delta provided that the domains match up and all items in Sigma that are marked as committed by
   Delta are indeed committed heap items *)
Definition well_committed_heap (Gamma : ctx) (Delta : init_ctx) (Sigma : heap) :=
  dom Gamma = dom Delta /\
  dom Delta = dom Sigma /\
  forall x itm,
    binds x committed Delta ->
    binds x itm Sigma ->
    committed_heap_item Gamma Delta itm.

(** ** Lemmas for committed heaps *)
(** Weakening Lemmas for committed heaps *)
Lemma committed_heap_def_weaken_middle : forall Delta1 Delta2 Delta3 hd,
    committed_heap_def (Delta1 & Delta3) hd ->
    ok (Delta1 & Delta2) ->
    committed_heap_def (Delta1 & Delta2 & Delta3) hd.
Proof.
  inversion 1; subst;
    intros; econstructor; eauto using binds_weaken.
Qed.

Lemma committed_heap_def_push_fresh : forall Delta x i hd,
    committed_heap_def Delta hd ->
    x # Delta ->
    committed_heap_def (Delta & x ~ i) hd.
Proof.
  inversion 1; subst; constructor; auto using binds_push_fresh.
Qed.

Lemma committed_heap_def_weaken : forall Delta1 Delta2 hd,
    committed_heap_def Delta1 hd ->
    ok (Delta1 & Delta2) ->
    committed_heap_def (Delta1 & Delta2) hd.
Proof.
  introv H; intros.
  rewrite <- (concat_empty_r Delta1) in H.
  rewrite <- (concat_empty_r (Delta1 & Delta2)) in *.
  eauto using committed_heap_def_weaken_middle.
Qed.

Lemma committed_heap_defs_push_fresh : forall Delta x i hds,
    committed_heap_defs Delta hds ->
    x # Delta ->
    committed_heap_defs (Delta & x ~ i) hds.
Proof.
  induction 1;
    econstructor; eauto using committed_heap_def_push_fresh.
Qed.

Lemma committed_heap_defs_weaken : forall Delta1 Delta2 hds,
    committed_heap_defs Delta1 hds ->
    ok (Delta1 & Delta2) ->
    committed_heap_defs (Delta1 & Delta2) hds.
Proof.
  induction 1;
    econstructor; eauto using committed_heap_def_weaken.
Qed.

Local Hint Extern 2 => simple apply init_weaken_same_vars : core.
Local Hint Extern 2 => simple apply init_weaken_ok_same_vars : core.
Local Hint Extern 2 => simple apply commit_weaken_ok : core.
Local Hint Extern 2 => simple apply commit_weaken : core.

Lemma committed_heap_item_push_fresh : forall Gamma x T' Delta i' itm,
    committed_heap_item Gamma Delta itm ->
    x # Gamma ->
    x # Delta ->
    committed_heap_item (Gamma & x ~ T') (Delta & x ~ i') itm.
Proof.
  induction 1; intros; econstructor;
    eauto using committed_heap_defs_push_fresh.
Qed.

Lemma committed_heap_item_weaken : forall Gamma1 Gamma2 Delta1 Delta2 itm,
    committed_heap_item Gamma1 Delta1 itm ->
    ok (Gamma1 & Gamma2) ->
    ok (Delta1 & Delta2) ->
    committed_heap_item (Gamma1 & Gamma2) (Delta1 & Delta2) itm.
Proof.
  induction 1; intros; econstructor;
    eauto using committed_heap_defs_weaken.
Qed.

(** Pushing Lemmas *)
Lemma well_committed_free_push : forall Gamma Delta Sigma x T itm,
    x # Gamma ->
    x # Delta ->
    well_committed_heap Gamma Delta Sigma ->
    well_committed_heap
      (Gamma & x ~ T) (Delta & x ~ free) (Sigma & x ~ itm).
Proof.
  unfold well_committed_heap; intros; destruct_ands.
  repeat_split_right; try (simpl_dom; congruence).
  intros.
  pose proof (binds_push_inv H4) as [[Heq _] | [?H ?H]]; subst.
  - apply binds_push_eq_inv in H4; congruence.
  - apply binds_push_neq_inv in H5; auto.
    eauto using committed_heap_item_push_fresh.
Qed.

Lemma well_committed_lit_push : forall Gamma Delta Sigma x l T,
    x # Gamma ->
    x # Delta ->
    Gamma ⸴ Delta ⊢c l ->
    well_committed_heap Gamma Delta Sigma ->
    well_committed_heap
      (Gamma & x ~ T) (Delta & x ~ committed) (Sigma & x ~ (item_lit l)).
Proof.
  unfold well_committed_heap. intros; destruct_ands.
  repeat_split_right; try (simpl_dom; congruence).
  intros.
  pose proof (binds_push_inv H5) as [[Heq _] | [?H ?H]]; subst.
  - apply binds_push_eq_inv in H6; subst.
    econstructor; eauto.
  - apply binds_push_neq_inv in H6; auto.
    eauto using committed_heap_item_push_fresh.
Qed.

Lemma well_committed_free_push_ok : forall Gamma Delta Sigma x T itm,
    ok (Gamma & x ~ T) ->
    ok (Delta & x ~ free) ->
    well_committed_heap Gamma Delta Sigma ->
    well_committed_heap
      (Gamma & x ~ T) (Delta & x ~ free) (Sigma & x ~ itm).
Proof.
  unfold well_committed_heap; intros; destruct_ands.
  repeat_split_right; try (simpl_dom; congruence).
  intros.
  pose proof (binds_push_inv H4) as [[Heq _] | [?H ?H]]; subst.
  - apply binds_push_eq_inv in H4; congruence.
  - apply binds_push_neq_inv in H5; auto.
    eauto using committed_heap_item_weaken.
Qed.

Lemma well_committed_lit_push_ok : forall Gamma Delta Sigma x l T,
    ok (Gamma & x ~ T) ->
    ok (Delta & x ~ committed) ->
    Gamma ⸴ Delta ⊢c l ->
    well_committed_heap Gamma Delta Sigma ->
    well_committed_heap
      (Gamma & x ~ T) (Delta & x ~ committed) (Sigma & x ~ (item_lit l)).
Proof.
  unfold well_committed_heap. intros; destruct_ands.
  repeat_split_right; try (simpl_dom; congruence).
  intros.
  pose proof (binds_push_inv H5) as [[Heq _] | [?H ?H]]; subst.
  - apply binds_push_eq_inv in H6; subst.
    econstructor; eauto.
  - apply binds_push_neq_inv in H6; auto.
    eauto using committed_heap_item_weaken.
Qed.

(** Update Lemmas for committed heaps *)
Section Update.
  Hint Constructors committed_heap_def committed_heap_defs committed_heap_item : core.

  Lemma committed_heap_defs_update_committed : forall Delta hds x a hds',
      committed_heap_defs Delta hds ->
      binds x committed Delta ->
      defs_update hds a x hds' ->
      committed_heap_defs Delta hds'.
  Proof.
    introv Hcom Hbi Hup.
    induction Hup; inversion Hcom; eauto.
  Qed.

  Hint Resolve committed_heap_defs_update_committed : core.
  Lemma committed_heap_item_update_committed : forall Gamma Delta T hds x a hds',
      committed_heap_item Gamma Delta (item_obj T hds) ->
      binds x committed Delta ->
      defs_update hds a x hds' ->
      committed_heap_item Gamma Delta (item_obj T hds').
  Proof.
    inversion 1; eauto.
  Qed.

  Hint Resolve committed_heap_item_update_committed : core.
  Lemma well_committed_heap_update_committed : forall Gamma Delta Sigma x a y Sigma',
      well_committed_heap Gamma Delta Sigma ->
      binds y committed Delta ->
      heap_update Sigma x a y Sigma' ->
      well_committed_heap Gamma Delta Sigma'.
  Proof.
    unfold heap_update.
    introv [HGDeq [HDSeq Hcom]] Hbi.
    introv [T [hds [hds' [Sigma1 [Sigma2 [HeqS [Hfr [Hup HeqS']]]]]]]].
    subst.
    unfold well_committed_heap; repeat_split_right;
      try congruence.
    - rewrite ? dom_concat, dom_single in *; congruence.
    - intros x'. destruct (var_decide x' x); subst; intros.
      + assert (binds x (item_obj T hds')
                      (Sigma1 & x ~ item_obj T hds' & Sigma2)) by auto.
        binds_eq; eauto.
      + eauto using binds_middle_update.
  Qed.

  Lemma well_committed_heap_update_free : forall Gamma Delta Sigma x a y Sigma' i,
      well_committed_heap Gamma Delta Sigma ->
      binds x i Delta -> init_sub i free ->
      heap_update Sigma x a y Sigma' ->
      well_committed_heap Gamma Delta Sigma'.
  Proof.
    unfold heap_update.

    introv [HGDeq [HDSeq Hcom]] Hbi.
    introv [T [hds [hds' [Sigma1 [Sigma2 [HeqS [Hfr [Hup HeqS']]]]]]]].
    subst.

    unfold well_committed_heap; repeat_split_right;
      try congruence.
    - rewrite ? dom_concat, dom_single in *; congruence.
    - intros x'. destruct (var_decide x' x); subst; intros.
      + apply init_var_sub_free in H. destruct_all; repeat binds_eq; congruence.
      + eauto using binds_middle_update.
  Qed.
End Update.

(** Committing a subheap *)
Definition more_committed Delta Delta' :=
  (forall x, binds x committed Delta -> binds x committed Delta').

Lemma more_committed_refl : forall Delta, more_committed Delta Delta.
Proof. intros; hnf; intros; auto. Qed.
Hint Resolve more_committed_refl : core.

Lemma more_committed_push_non_committed : forall Delta x i j,
    i <> committed -> j <> committed ->
    more_committed (Delta & x ~ i) (Delta & x ~ j).
Proof.
  introv Hineq Hjneq. hnf. introv Hbin. rename x0 into y.
  apply binds_push_inv in Hbin.
  destruct Hbin as [[? ?] | [Hneq Hbin]]; subst;
    try(solve[exfalso; auto]); eauto.
Qed.
Hint Resolve more_committed_push_non_committed : core.

Lemma more_committed_push_same : forall Delta Delta' x i,
    more_committed Delta Delta' ->
    more_committed (Delta & x ~ i) (Delta' & x ~ i).
Proof.
  introv Hmc. hnf. introv Hbin. rename x0 into y.
  apply binds_push_inv in Hbin.
  destruct Hbin as [[? ?] | [Hneq Hbin]]; subst;
    try(solve[exfalso; auto]); eauto.
Qed.
Hint Resolve more_committed_push_same : core.

(* Localising part of a subheap *)
Definition more_localised Delta Delta' :=
  (forall x, binds x local Delta -> binds x local Delta').

Lemma more_committed_def : forall Delta Delta' hd,
    more_committed Delta Delta' ->
    committed_heap_def Delta hd ->
    committed_heap_def Delta' hd.
Proof.
  inversion 2; subst; constructor; auto.
Qed.

Lemma more_committed_defs : forall Delta Delta' hds,
    more_committed Delta Delta' ->
    committed_heap_defs Delta hds ->
    committed_heap_defs Delta' hds.
Proof.
  induction 2; constructor; eauto using more_committed_def.
Qed.

Lemma more_committed_lit : forall Gamma Delta Delta' l,
    more_committed Delta Delta' ->
    Gamma ⸴ Delta ⊢c l ->
    Gamma ⸴ Delta' ⊢c l.
Proof.
  intros. eapply well_init_more_committed_rules; eauto.
Qed.

Lemma more_committed_item : forall Gamma Delta Delta' itm,
    more_committed Delta Delta' ->
    committed_heap_item Gamma Delta itm ->
    committed_heap_item Gamma Delta' itm.
Proof.
  inversion 2; subst; constructor;
    eauto using more_committed_defs, more_committed_lit.
Qed.

Lemma more_committed_sub_heap : forall Gamma Sigma Delta Delta',
    well_committed_heap Gamma Delta Sigma ->
    dom Delta = dom Delta' ->
    (forall x itm, binds x committed Delta' -> binds x itm Sigma ->
              committed_heap_item Gamma Delta' itm) ->
    well_committed_heap Gamma Delta' Sigma.
Proof.
  unfold well_committed_heap; intros; destruct_ands.
  repeat_split_right; try congruence; auto.
Qed.

(** Read Lemmas for committed heaps *)
Lemma committed_heap_defs_exists_None_inv: forall Delta hds,
    committed_heap_defs Delta hds ->
    (exists a, labels_has hds (heap_def_trm a None)) ->
    False.
Proof.
  unfold labels_has; simpl.
  induction 1 as [| Delta hd hds Hhds IH Hhd].
  - destruct 1 as [a Contra]; simpl in *. congruence.
  - destruct 1 as [a Cases]. simpl in Cases.
    cases_if; eauto.
    inversion Hhd; subst; congruence.
Qed.

Lemma committed_heap_defs_labels_has_None_inv : forall Delta hds a,
    committed_heap_defs Delta hds ->
    labels_has hds (heap_def_trm a None) ->
    False.
Proof.
  eauto using committed_heap_defs_exists_None_inv.
Qed.

Lemma committed_heap_defs_labels_has_inv: forall Delta hds a y,
    committed_heap_defs Delta hds ->
    labels_has hds (heap_def_trm a (Some y)) ->
    binds y committed Delta.
Proof.
  induction hds; intros.
  - inversions H. inversion H0.
  - destruct a.
    + inversions H. apply IHhds with (a:=a0); auto.
      apply labels_has_rest in H0; auto. sympl; congruence.
    + unfold labels_has in H0; sympl in H0; cases_if.
      * inversion H0; subst. inversions H. inversion H5; auto.
      * apply IHhds with (a:=a0); auto. inversion H; auto.
Qed.

Lemma committed_read_inv : forall Gamma Delta Sigma x T hds a y,
    well_committed_heap Gamma Delta Sigma ->
    binds x (item_obj T hds) Sigma ->
    binds x committed Delta ->
    labels_has hds (heap_def_trm a (Some y)) ->
    binds y committed Delta.
Proof.
  introv Hwc HbixS HbixD Hlhs.
  destruct Hwc as [?HGD [?HDS ?Hcom]].
  pose proof (Hcom _ _ HbixD HbixS) as Hcomi.
  inversions Hcomi.
  eauto using committed_heap_defs_labels_has_inv.
Qed.

(* TODO: Move this to HeapLocalise *)

Section HeapLocalise.

  Inductive non_null_heap_def : init_ctx -> heap_def -> Prop :=
  (* Not null when it's a type declaration *)
  | non_null_heap_def_typ : forall Delta A T,
      non_null_heap_def Delta (heap_def_typ A T)

  (* If a field a is assigned to some x in Delta then the heap def is not null *)
  | non_null_heap_def_trm : forall Delta a x,
      x \in dom Delta ->
            non_null_heap_def Delta (heap_def_trm a (Some x)).
  Hint Constructors non_null_heap_def : core.

  Inductive non_null_heap_defs : init_ctx -> heap_defs -> Prop :=
  | non_null_heap_heap_defs_nil : forall Delta,
      non_null_heap_defs Delta nil

  | non_null_heap_defs_cons : forall Delta hd hds,
      non_null_heap_defs Delta hds ->
      non_null_heap_def Delta hd ->
      non_null_heap_defs Delta (cons hd hds).
  Hint Constructors non_null_heap_defs : core.

  Lemma non_null_heap_defs_no_null : forall Delta a hds,
      non_null_heap_defs Delta hds ->
      ~ (labels_has hds (heap_def_trm a None)).
  Proof.
    induction hds; unfold not; introv Hnnhds Hnull; eauto; try solve[inversions Hnull].
    inversions Hnnhds. rename H2 into Hnnhds. rename H3 into Hnnhd.
    specialize (IHhds Hnnhds). unfold not in IHhds.
    inversions Hnull. cases_if; eauto.
    inversions H0. inversions Hnnhd.
  Qed.

  (* Heap items being committed *)
  Inductive localised_heap_item :
    ctx -> init_ctx -> item -> Prop :=
  (* A committed item is certainly localised *)
  | commit_is_localised : forall Gamma Delta itm,
      committed_heap_item Gamma Delta itm ->
      localised_heap_item Gamma Delta itm
  (* Otherwise an object is localised if all of its fields have something (but not
   necessarily well-initialised) *)
  | localised_heap_obj : forall Gamma Delta T hds,
      non_null_heap_defs Delta hds ->
      localised_heap_item Gamma Delta (item_obj T hds).
  Hint Constructors localised_heap_item : core.

  (* A heap Sigma is well localised with respect to a typing context Gamma and an
   initialisation context Delta provided that the domains match up and all items
   in Sigma that are marked as committed by Delta are indeed localised heap items *)
  Definition well_localised_heap (Gamma : ctx) (Delta : init_ctx) (Sigma : heap) :=
    dom Gamma = dom Delta /\
    dom Delta = dom Sigma /\
    forall x itm,
      binds x local Delta ->
      binds x itm Sigma ->
      localised_heap_item Gamma Delta itm.

  Definition localised_sub_heap
             (vs : vars) (Sigma : heap) (Gamma : ctx) (Delta : init_ctx) :=
    forall x, x \in vs -> binds x local Delta ->
               exists itm, binds x itm Sigma /\ localised_heap_item Gamma Delta itm.

  Lemma non_null_heap_def_push : forall Delta x i hd,
      non_null_heap_def Delta hd ->
      non_null_heap_def (Delta & x ~ i) hd.
  Proof.
    induction 1; auto.
    rename x0 into y.
    econstructor. rewrite dom_push, in_union. auto.
  Qed.

  Lemma non_null_heap_defs_push : forall Delta x i hds,
      non_null_heap_defs Delta hds ->
      non_null_heap_defs (Delta & x ~ i) hds.
  Proof.
    induction 1; auto using non_null_heap_def_push.
  Qed.

  Lemma localised_heap_item_push_fresh : forall Gamma x T' Delta i' itm,
      localised_heap_item Gamma Delta itm ->
      x # Gamma ->
      x # Delta ->
      localised_heap_item (Gamma & x ~ T') (Delta & x ~ i') itm.
  Proof.
    induction 1;
      try(solve[intros;
                eauto using committed_heap_item_push_fresh,
                non_null_heap_defs_push]).
  Qed.

  Lemma well_localised_free_push : forall Gamma Delta Sigma x T itm,
      x # Gamma ->
      x # Delta ->
      well_localised_heap Gamma Delta Sigma ->
      well_localised_heap
        (Gamma & x ~ T) (Delta & x ~ free) (Sigma & x ~ itm).
  Proof.
    introv HxninG HxninD [HGD [HDS Hwl]].
    unfold well_localised_heap; destruct_ands.
    repeat split; try(simpl_dom; congruence).
    introv Hbininit Hbinitm.
    pose proof (binds_push_inv Hbininit)
      as [[? ?] | [Hneq HbinD]]; try(exfalso ;congruence).
    pose proof (binds_push_inv Hbinitm)
      as [[? ?] | [_ HbinS]]; try(exfalso; congruence).
    eauto using localised_heap_item_push_fresh.
  Qed.

  Lemma non_null_hds_update_in_D : forall Delta hds a x hds' i,
      non_null_heap_defs Delta hds ->
      binds x i Delta ->
      defs_update hds a x hds' ->
      non_null_heap_defs Delta hds'.
  Proof.
    induction hds; introv Hnnhds Hxcomm Hupd.
    - inversions Hupd.
    - rename a into hd. rename a0 into a.
      inversions Hnnhds. rename H2 into Hnnhds. rename H3 into Hnnhd.
      inversions Hupd; eauto using binds_to_dom.
  Qed.

  Lemma committed_heap_def_non_null : forall Delta hd,
      committed_heap_def Delta hd ->
      non_null_heap_def Delta hd.
  Proof. inversion 1; eauto using binds_to_dom. Qed.

  Lemma committed_heap_defs_non_null : forall Delta hds,
      committed_heap_defs Delta hds ->
      non_null_heap_defs Delta hds.
  Proof. induction 1; eauto using committed_heap_def_non_null. Qed.

  Lemma commmitted_heap_item_hds_non_null : forall Gamma Delta T hds,
      committed_heap_item Gamma Delta (item_obj T hds) ->
      non_null_heap_defs Delta hds.
  Proof.
    introv Hchi. inversions Hchi. auto using committed_heap_defs_non_null.
  Qed.

  Lemma localised_heap_item_hds_non_null : forall Gamma Delta T hds,
      localised_heap_item Gamma Delta (item_obj T hds) ->
      non_null_heap_defs Delta hds.
  Proof.
    inversion 1; eauto using commmitted_heap_item_hds_non_null.
  Qed.

  Lemma localised_heap_item_update : forall Gamma Delta T a x hds hds' i,
      localised_heap_item Gamma Delta (item_obj T hds) ->
      binds x i Delta ->
      defs_update hds a x hds' ->
      localised_heap_item Gamma Delta (item_obj T hds').
  Proof.
    inversion 1; subst; introv Hxcomm Hupd.
    - eauto using localised_heap_item_hds_non_null,
      non_null_hds_update_in_D.
    - eauto using non_null_hds_update_in_D.
  Qed.

  Lemma well_localised_heap_update : forall Gamma Delta Sigma x a y Sigma' i,
      well_localised_heap Gamma Delta Sigma ->
      binds y i Delta ->
      heap_update Sigma x a y Sigma' ->
      well_localised_heap Gamma Delta Sigma'.
  Proof.
    introv [HGDeq [HDSeq Hloc]] Hbi
           [T [hds [hds' [Sigma1 [Sigma2 [HeqS [Hfr [Hup HeqS']]]]]]]]; subst.
    unfold well_localised_heap; repeat split; try congruence.
    - rewrite ? dom_concat, dom_single in *; congruence.
    - intros x' itm Hbix'D Hbix'S.
      destruct (var_decide x' x); subst; intros.
      + assert (binds x (item_obj T hds')
                      (Sigma1 & x ~ item_obj T hds' & Sigma2)) by auto;
          binds_eq; clear H0.
        assert (localised_heap_item Gamma Delta (item_obj T hds)) as Hlocitm
            by eauto.
        eapply localised_heap_item_update.
        * eassumption. * apply Hbi. * eauto.
      + eauto using binds_middle_update.
  Qed.

  Lemma localised_sub_heap_push_wc_lit : forall vs Sigma Gamma Delta x l i T,
      localised_sub_heap vs Sigma Gamma Delta ->
      x # Gamma ->
      x # Sigma ->
      x # Delta ->
      Gamma ⸴ Delta ⊢c l ->
      localised_sub_heap vs (Sigma & x ~ item_lit l) (Gamma & x ~ T) (Delta & x ~ i).
  Proof.
    unfold localised_sub_heap.
    introv Hlsh HxniG HxniS HxniD Hlwc Hx'invs Hbix'l . rename x0 into x'.
    apply binds_push_inv in Hbix'l as [[? ?] | [Hneq Hbix'l]]; subst.
    + exists (item_lit l). split; eauto. constructor. constructor.
      eauto using commit_weaken_D, commit_weaken_G.
    + specialize (Hlsh _ Hx'invs Hbix'l) as [itm [HbixS Hlhi]].
      exists itm. split; eauto using localised_heap_item_push_fresh.
  Qed.

  Lemma localised_sub_heap_push_free : forall Gamma vs Sigma Delta x itm T,
      localised_sub_heap vs Sigma Gamma Delta ->
      x # Gamma ->
      x # Sigma ->
      x # Delta ->
      localised_sub_heap
        (vs \u \{x})
        (Sigma & x ~ itm) (Gamma & x ~ T) (Delta & x ~ free).
  Proof.
    unfold localised_sub_heap.
    introv Hlsh HxniG HxniS HxniD Hx'invs Hbix'l . rename x0 into x'.
    apply binds_push_inv in Hbix'l as [[? ?] | [Hneq Hbix'l]];
      subst; try discriminate.
    rewrite in_union, in_singleton in Hx'invs.
    destruct Hx'invs as [Hx'invs | ?]; try congruence.
    specialize (Hlsh _ Hx'invs Hbix'l) as [itm' [HbixS Hlhi]].
    exists itm'. split; eauto using localised_heap_item_push_fresh.
  Qed.

  Lemma localised_sub_heap_push_free_obj : forall Gamma vs Sigma Delta x T ds,
      localised_sub_heap vs Sigma Gamma Delta ->
      x # Gamma ->
      x # Sigma ->
      x # Delta ->
      localised_sub_heap
        (vs \u \{x})
        (Sigma & x ~ item_obj T (heap_defs_of_defs ds))
        (Gamma & x ~ typ_bnd T)
        (Delta & x ~ free).
  Proof.
    unfold localised_sub_heap.
    introv Hlsh HxniG HxniS HxniD Hx'invs Hbix'l . rename x0 into x'.
    apply binds_push_inv in Hbix'l as [[? ?] | [Hneq Hbix'l]];
      subst; try discriminate.
    rewrite in_union, in_singleton in Hx'invs.
    destruct Hx'invs as [Hx'invs | ?]; try congruence.
    specialize (Hlsh _ Hx'invs Hbix'l) as [itm [HbixS Hlhi]].
    exists itm. split; eauto using localised_heap_item_push_fresh.
  Qed.

  Lemma well_localised_heap_is_localised_subheap : forall Gamma Delta Sigma vs,
      well_localised_heap Gamma Delta Sigma ->
      localised_sub_heap vs Sigma Gamma Delta.
  Proof.
    introv [HGD [HDS Hwl]] Hxinvs HxlocD.
    assert (HxitmS : exists itm, binds x itm Sigma).
    { apply binds_to_dom in HxlocD. rewrite HDS in HxlocD.
      apply dom_to_binds in HxlocD. auto. }
    destruct HxitmS as [itm HxitmS].
    exists itm. split; eauto.
  Qed.

  Lemma localised_sub_heap_correspondence_other : forall Gamma vs Sigma Delta
                                                    x a y i Sigma',
      localised_sub_heap vs Sigma Gamma Delta ->
      binds y i Delta ->
      heap_update Sigma x a y Sigma' ->
      localised_sub_heap vs Sigma' Gamma Delta.
  Proof.
    introv Hlsh HbiyD. unfold heap_update.
    intros [T [hds [hds' [Sigma1 [Sigma2 [?Heq [HfrS2 [Hup ?Heq]]]]]]]]; subst.
    intros x' Hx'invs Hbix'D.
    unfold localised_sub_heap in Hlsh.
    specialize (Hlsh _ Hx'invs Hbix'D) as [itm [Hix'S Hlhi]].
    destruct (var_decide x' x); subst; intros.
    + exists (item_obj T hds'); split; auto.
      assert (itm = item_obj T hds) by eauto using binds_middle_eq_fresh_inv; subst.
      clear Hix'S.
      eapply localised_heap_obj.
      eapply localised_heap_item_hds_non_null in Hlhi.
      eapply non_null_hds_update_in_D with (x := y); eauto.
    + rename n into Hneq. exists itm. split; eauto using binds_middle_update.
  Qed.

  Lemma localised_sub_heap_correspondence_committed : forall Sigma vs Gamma Delta
                                                        x a y i Sigma',
      localised_sub_heap vs Sigma Gamma Delta ->
      heap_update Sigma x a y Sigma' ->
      binds x committed Delta ->
      binds y i Delta ->
      localised_sub_heap vs Sigma' Gamma Delta.
  Proof. eauto using localised_sub_heap_correspondence_other. Qed.

  Lemma localised_sub_heap_weaken_vs : forall Gamma vs Sigma Delta x,
    localised_sub_heap (vs \u \{x}) Sigma Gamma Delta ->
    localised_sub_heap vs Sigma Gamma Delta.
  Proof.
    unfold localised_sub_heap. introv Hlsh Hxinvs Hxloc.
    assert (x0 \in vs \u \{x}) by (rewrite in_union; auto); eauto.
  Qed.
  Hint Resolve localised_sub_heap_weaken_vs : core.

End HeapLocalise.
