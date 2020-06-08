(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra.
Require Import AbstractSyntax GeneralTyping Weakening.

Lemma closed_let_let : forall s t u,
    closed (trm_let (trm_let s t) u) ->
    closed (trm_let s (trm_let t u)).
Proof.
  unfold closed. intros s t u H n x.
  pose proof (H n x) as H1;
    pose proof (H (S n) x) as H2;
    inversion H1; inversion H2.
  simpls; congruence.
Qed.

Lemma ty_let_inv : forall s t G U,
    ok G ->
    G ⊢ trm_let s t ∶ U ->
    exists T L, (G ⊢ s ∶ T) /\
           (forall x : var, x \notin L -> G & x ~ T ⊢ open x t ∶ U).
Proof.
  intros. remember (trm_let s t) as t' eqn:Heq.
  induction H0; inversions Heq.
  + exists T L. split; auto.
  + specialize (IHty_trm H H2).
    destruct IHty_trm as [T0 [L [?H ?H]]].
    exists T0 (L \u dom G); split; auto.
    intros. eapply ty_sub; auto.
    eapply weaken_subtyp; auto.
Qed.

Lemma ty_let_let : forall G s t u U,
    ok G ->
    closed (trm_let (trm_let s t) u) ->
    G ⊢ (trm_let (trm_let s t) u) ∶ U ->
    G ⊢ trm_let s (trm_let t u) ∶ U.
Proof.
  intros. remember (trm_let (trm_let s t) u) as t' eqn:Heq.
  induction H1; inversions Heq; eauto.
  clear H3.
  pose proof (ty_let_inv H H1) as [T' [L' [?H ?H]]].
  eapply (@ty_let (L' \u dom G)); eauto; intros.
  sympl. eapply ty_let; eauto; intros.
  assert (open_rec 1 x u = u).
  { unfold closed in H0. simpls.
    specialize (H0 0 x). inversion H0.
    rewrite ? H10. auto. }
  rewrite H7. eapply weaken_rules; eauto.
Qed.
