(** remove printing ~ *)
Set Implicit Arguments.

Require Import Program.Equality.
Require Import LibExtra DotTactics AbstractSyntax.
Require Import PreTyping Typing GeneralTyping Weakening.
Require Import InitVar InitTyping InitTypingLemmas InitVarSubtyping.

Implicit Types (i : init_typ) (t : trm) (l : lit) (avs : avars).

Local Hint Resolve init_var_weaken_vars init_var_weaken_D init_var_more_committed : core.
Local Hint Extern 2 => simple apply weaken_ok_middle : core.
Local Hint Extern 2 => simple apply weaken_middle : core.
Local Hint Resolve init_var_substitution_middle : core.

(** Weakening for initialization *)
Lemma well_init_weaken_G_rules :
  (forall Gamma Delta t,
      Gamma ⸴ Delta ⊢c t ->
      forall Gamma1 x T' Gamma2,
        Gamma = Gamma1 & Gamma2 -> x # Gamma1 ->
        Gamma1 & x ~ T' & Gamma2 ⸴ Delta ⊢c t ) /\
  (forall Gamma Delta avs,
      Gamma ⸴ Delta ⊢c avs ->
      forall Gamma1 x T' Gamma2,
        Gamma = Gamma1 & Gamma2 -> x # Gamma1 ->
        Gamma1 & x ~ T' & Gamma2 ⸴ Delta ⊢c avs) /\
  (forall Gamma Delta l,
      Gamma ⸴ Delta ⊢c l ->
      forall Gamma1 x T' Gamma2,
        Gamma = Gamma1 & Gamma2 -> x # Gamma1 ->
        Gamma1 & x ~ T' & Gamma2 ⸴ Delta ⊢c l) /\
  (forall Gamma Delta vs t i,
      Gamma ⸴ Delta ⸴ vs ⊢i t ∶ i ->
      forall Gamma1 x T' Gamma2,
        Gamma = Gamma1 & Gamma2 -> x # Gamma1 ->
        Gamma1 & x ~ T' & Gamma2 ⸴ Delta ⸴ vs ⊢i t ∶ i) /\
  (forall Gamma Delta vs avs is',
      Gamma ⸴ Delta ⸴ vs ⊢i avs :: is' ->
      forall Gamma1 x T' Gamma2,
        Gamma = Gamma1 & Gamma2 -> x # Gamma1 ->
        Gamma1 & x ~ T' & Gamma2 ⸴ Delta ⸴ vs ⊢i avs :: is').
Proof.
  apply well_init_mut_ind; intros; subst; eauto.
  - init_fresh_constructor_extern; eauto. assert (z \notin L) by auto.
    specialize (H0 z H1 Gamma1 x T' (Gamma2 & z ~ T)); repeat rewrite concat_assoc in *.
    auto.
  - init_fresh_constructor_extern; eauto. assert (z \notin L) by auto.
    specialize (H0 z H1 Gamma1 x T' (Gamma2 & z ~ T)); repeat rewrite concat_assoc in *.
    auto.
  - init_fresh_constructor_extern; eauto. assert (z \notin L) by auto.
    specialize (H z H0 Gamma1 x T' (Gamma2 & z ~ T)); repeat rewrite concat_assoc in *.
    auto.
  - init_fresh_constructor_extern; eauto. intros.
    specialize (H x0 ys H0).
    assert (fresh L (S (length ys)) (x0 :: ys)) by auto.
    specialize (H H3 Gamma1 x T' (Gamma2 & ys ~** to_list Ts & x0 ~ open_vars (x0 :: ys) T)).
    repeat rewrite concat_assoc in * |-. apply H; eauto.
  - init_fresh_constructor_extern; eauto. assert (z \notin L) by auto.
    specialize (H0 z H1 Gamma1 x T' (Gamma2 & z ~ T)); repeat rewrite concat_assoc in *.
    auto.
  - init_fresh_constructor_extern; eauto. assert (z \notin L) by auto.
    specialize (H0 z H1 Gamma1 x T' (Gamma2 & z ~ T)); repeat rewrite concat_assoc in *.
    auto.
Qed.

Lemma well_init_weaken_D_rules :
  (forall Gamma Delta t,
      Gamma ⸴ Delta ⊢c t ->
      forall Delta1 x i' Delta2,
        Delta = Delta1 & Delta2 -> x # Delta1 ->
        Gamma ⸴ Delta1 & x ~ i' & Delta2 ⊢c t ) /\
  (forall Gamma Delta avs,
      Gamma ⸴ Delta ⊢c avs ->
      forall Delta1 x i' Delta2,
        Delta = Delta1 & Delta2 -> x # Delta1 ->
        Gamma ⸴ Delta1 & x ~ i' & Delta2 ⊢c avs) /\
  (forall Gamma Delta l,
      Gamma ⸴ Delta ⊢c l ->
      forall Delta1 x i' Delta2,
        Delta = Delta1 & Delta2 -> x # Delta1 ->
        Gamma ⸴ Delta1 & x ~ i' & Delta2 ⊢c l) /\
  (forall Gamma Delta vs t i,
      Gamma ⸴ Delta ⸴ vs ⊢i t ∶ i ->
      forall Delta1 x i' Delta2,
        Delta = Delta1 & Delta2 -> x # Delta1 ->
        Gamma ⸴ Delta1 & x ~ i' & Delta2 ⸴ vs ⊢i t ∶ i) /\
  (forall Gamma Delta vs avs is',
      Gamma ⸴ Delta ⸴ vs ⊢i avs :: is' ->
      forall Delta1 x i' Delta2,
        Delta = Delta1 & Delta2 -> x # Delta1 ->
        Gamma ⸴ Delta1 & x ~ i' & Delta2 ⸴ vs ⊢i avs :: is').
Proof.
  apply well_init_mut_ind; intros; subst;
    eauto 4 using binds_push_fresh_middle.
  - init_fresh_constructor_extern; eauto. assert (z \notin L) by auto.
    specialize (H0 z H1 Delta1 x i' (Delta2 & z ~ committed)); repeat rewrite concat_assoc in *.
    auto.
  - init_fresh_constructor_extern; eauto. assert (z \notin L) by auto.
    specialize (H0 z H1 Delta1 x i' (Delta2 & z ~ committed)); repeat rewrite concat_assoc in *.
    auto.
  - init_fresh_constructor_extern; eauto. assert (z \notin L) by auto.
    specialize (H z H0 Delta1 x i' (Delta2 & z ~ committed)); repeat rewrite concat_assoc in *.
    auto.
  - init_fresh_constructor_extern; eauto. intros.
    specialize (H x0 ys H0). assert (fresh L (S (length ys)) (x0 :: ys)) by auto.
    specialize (H H3 Delta1 x i' (Delta2 & ys ~** is' & x0 ~ free)).
    repeat rewrite concat_assoc in * |-. apply H; eauto.
  - init_fresh_constructor_extern; eauto. assert (z \notin L) by auto.
    specialize (H0 z H1 Delta1 x i'0 (Delta2 & z ~ i)); repeat rewrite concat_assoc in *.
    auto.
  - init_fresh_constructor_extern; eauto. assert (z \notin L) by auto.
    specialize (H0 z H1 Delta1 x i' (Delta2 & z ~ committed)); repeat rewrite concat_assoc in *.
    auto.
Qed.

Lemma well_init_weaken_vs_rules :
  (forall Gamma Delta t,
      Gamma ⸴ Delta ⊢c t ->
      Gamma ⸴ Delta ⊢c t) /\
  (forall Gamma Delta avs,
      Gamma ⸴ Delta ⊢c avs ->
      Gamma ⸴ Delta ⊢c avs) /\
  (forall Gamma Delta l,
      Gamma ⸴ Delta ⊢c l ->
      Gamma ⸴ Delta ⊢c l) /\
  (forall Gamma Delta vs t i,
      Gamma ⸴ Delta ⸴ vs ⊢i t ∶ i ->
      forall vs', Gamma ⸴ Delta ⸴ vs \u vs' ⊢i t ∶ i) /\
  (forall Gamma Delta vs avs is',
      Gamma ⸴ Delta ⸴ vs ⊢i avs :: is' ->
      forall vs', Gamma ⸴ Delta ⸴ vs \u vs' ⊢i avs :: is').
Proof.
  apply well_init_mut_ind; eauto; intros.
  init_fresh_constructor_extern; eauto. assert (z \notin L) by auto.
  specialize (H0 _ H1 vs'). rewrite union_comm_comm_assoc_assoc.
  auto.
Qed.

Class InitTypingWeakenMiddle {A : Set} `(InitTyping A) :=
  init_weaken_middle : forall Gamma1 x T' Gamma3 Delta1 i' Delta3 vs vs' (t : A) i,
    Gamma1 & Gamma3 ⸴ Delta1 & Delta3 ⸴ vs ⊢i t ∶ i ->
    x # Gamma1 ->
    x # Delta1 ->
    Gamma1 & x ~ T' & Gamma3 ⸴ Delta1 & x ~ i' & Delta3 ⸴ vs \u vs' ⊢i t ∶ i.

Class InitTypingWeakenOkMiddle {A : Set} `(InitTyping A) :=
  init_weaken_ok_middle : forall Gamma1 Gamma2 Gamma3 Delta1 Delta2 Delta3 vs vs' (t : A) i,
    Gamma1 & Gamma3 ⸴ Delta1 & Delta3 ⸴ vs ⊢i t ∶ i ->
    ok (Gamma1 & Gamma2) ->
    ok (Delta1 & Delta2) ->
    Gamma1 & Gamma2 & Gamma3 ⸴ Delta1 & Delta2 & Delta3 ⸴ vs \u vs' ⊢i t ∶ i.

Section InitWeaken.
  Context {A : Set} `{ITyA : InitTyping A}.
  Section Weaken.
    Context {ITyWM : InitTypingWeakenMiddle ITyA}.

    Lemma init_weaken : forall Gamma1 x T' Delta1 i' vs vs' (t : A) i,
        Gamma1 ⸴ Delta1 ⸴ vs ⊢i t ∶ i ->
        x # Gamma1 ->
        x # Delta1 ->
        Gamma1 & x ~ T' ⸴ Delta1 & x ~ i' ⸴ vs \u vs' ⊢i t ∶ i.
    Proof.
      intros.
      rewrite <- (concat_empty_r Gamma1) in H.
      rewrite <- (concat_empty_r Delta1) in H.
      rewrite <- (concat_empty_r (Gamma1 & _)).
      rewrite <- (concat_empty_r (Delta1 & _)).
      auto.
    Qed.

    Lemma init_weaken_middle_same_vars : forall Gamma1 x T' Gamma3 Delta1 i' Delta3 vs (t : A) i,
        Gamma1 & Gamma3 ⸴ Delta1 & Delta3 ⸴ vs ⊢i t ∶ i ->
        x # Gamma1 ->
        x # Delta1 ->
        Gamma1 & x ~ T' & Gamma3 ⸴ Delta1 & x ~ i' & Delta3 ⸴ vs ⊢i t ∶ i.
    Proof.
      intros; rewrite <- (union_empty_r vs).
      auto.
    Qed.

    Lemma init_weaken_same_vars : forall Gamma1 x T' Delta1 i' vs (t : A) i,
        Gamma1 ⸴ Delta1 ⸴ vs ⊢i t ∶ i ->
        x # Gamma1 ->
        x # Delta1 ->
        Gamma1 & x ~ T' ⸴ Delta1 & x ~ i' ⸴ vs ⊢i t ∶ i.
    Proof.
      intros. rewrite <- (union_empty_r vs).
      eapply init_weaken; eauto.
    Qed.
  End Weaken.

  Section WeakenOk.
    Context {ITyWM : InitTypingWeakenOkMiddle ITyA}.

    Lemma init_weaken_ok : forall Gamma1 Gamma2 Delta1 Delta2 vs vs' (t : A) i,
        Gamma1 ⸴ Delta1 ⸴ vs ⊢i t ∶ i ->
        ok (Gamma1 & Gamma2) ->
        ok (Delta1 & Delta2) ->
        Gamma1 & Gamma2 ⸴ Delta1 & Delta2 ⸴ vs \u vs' ⊢i t ∶ i.
    Proof.
      introv H; intros.
      rewrite <- (concat_empty_r Gamma1), <- (concat_empty_r Delta1) in H.
      rewrite <- (concat_empty_r (Gamma1 & _)).
      rewrite <- (concat_empty_r (Delta1 & _)).
      eauto.
    Qed.

    Lemma init_weaken_ok_same_vars : forall Gamma1 Gamma2 Delta1 Delta2 vs (t : A) i,
        Gamma1 ⸴ Delta1 ⸴ vs ⊢i t ∶ i ->
        ok (Gamma1 & Gamma2) ->
        ok (Delta1 & Delta2) ->
        Gamma1 & Gamma2 ⸴ Delta1 & Delta2 ⸴ vs ⊢i t ∶ i.
    Proof.
      intros. rewrite <- (union_empty_r vs).
      eapply init_weaken_ok; eauto.
    Qed.
  End WeakenOk.
End InitWeaken.

Instance TrmInitTypingWeakenMiddle : InitTypingWeakenMiddle well_init.
Proof.
  hnf. intros.
  eapply well_init_weaken_G_rules; eauto.
  eapply well_init_weaken_D_rules; eauto.
  eapply well_init_weaken_vs_rules; eauto.
Qed.

Instance TrmInitTypingWeakenOkMiddle : InitTypingWeakenOkMiddle well_init.
Proof.
  hnf. intros.
  eapply well_init_weaken_vs_rules.
  gen Delta2.
  induction Gamma2 using env_ind; induction Delta2 using env_ind;
    rewrite ? concat_empty_r, ? concat_assoc in *; intros; auto.
  - apply ok_push_inv in H1; destruct H1; eauto.
    eapply well_init_weaken_D_rules; try reflexivity; eauto.
  - apply ok_push_inv in H0; destruct H0.
    eapply well_init_weaken_G_rules; try reflexivity; eauto.
    rewrite <- concat_empty_r in H1.
    rewrite <- (concat_empty_r Delta1). apply IHGamma2; auto.
  - apply ok_push_inv in H0. destruct H0.
    specialize (IHGamma2 H0 (Delta2 & x0 ~ v0)).
    rewrite concat_assoc in *.
    eapply (proj54 well_init_weaken_G_rules); try reflexivity; eauto.
Qed.

Class CommitTypingWeakenMiddleG {A : Set} `(CommitTyping A) :=
  commit_weaken_middle_G : forall Gamma1 x T' Gamma3 Delta (t : A),
    Gamma1 & Gamma3 ⸴ Delta ⊢c t ->
    x # Gamma1 ->
    Gamma1 & x ~ T' & Gamma3 ⸴ Delta ⊢c t.

Class CommitTypingWeakenMiddleD {A : Set} `(CommitTyping A) :=
  commit_weaken_middle_D : forall Gamma Delta1 x i' Delta3 (t : A),
    Gamma ⸴ Delta1 & Delta3 ⊢c t ->
    x # Delta1 ->
    Gamma ⸴ Delta1 & x ~ i' & Delta3 ⊢c t.

Section CommitWeaken.
  Context {A : Set} `{ITyA : CommitTyping A}.
  Section Weaken.
    Context {ITyWMG : CommitTypingWeakenMiddleG ITyA}.
    Context {ITyWMD : CommitTypingWeakenMiddleD ITyA}.

    Lemma commit_weaken_G : forall Gamma1 x T' Delta (t : A),
        Gamma1 ⸴ Delta ⊢c t ->
        x # Gamma1 ->
        Gamma1 & x ~ T' ⸴ Delta ⊢c t.
    Proof.
      intros.
      rewrite <- (concat_empty_r Gamma1) in H.
      rewrite <- (concat_empty_r (Gamma1 & _)).
      auto.
    Qed.

    Lemma commit_weaken_D : forall Gamma Delta1 x i' (t : A),
        Gamma ⸴ Delta1 ⊢c t ->
        x # Delta1 ->
        Gamma ⸴ Delta1 & x ~ i' ⊢c t.
    Proof.
      intros.
      rewrite <- (concat_empty_r Delta1) in H.
      rewrite <- (concat_empty_r (Delta1 & _)).
      auto.
    Qed.

    Lemma commit_weaken : forall Gamma1 x T' Delta1 i' (t : A),
        Gamma1 ⸴ Delta1 ⊢c t ->
        x # Gamma1 ->
        x # Delta1 ->
        Gamma1 & x ~ T' ⸴ Delta1 & x ~ i' ⊢c t.
    Proof.
      intros. eauto using commit_weaken_G, commit_weaken_D.
    Qed.

    Lemma commit_weaken_ok_G_middle : forall Gamma1 Gamma2 Gamma3 Delta (t : A),
        Gamma1 & Gamma3 ⸴ Delta ⊢c t ->
        ok (Gamma1 & Gamma2) ->
        Gamma1 & Gamma2 & Gamma3 ⸴ Delta ⊢c t.
    Proof.
      induction Gamma2 using env_ind; intros;
        rewrite ? concat_empty_r, ? concat_assoc in *; eauto.
      apply ok_push_inv in H0; destruct H0; auto.
    Qed.

    Lemma commit_weaken_ok_D_middle : forall Gamma Delta1 Delta2 Delta3 (t : A),
        Gamma ⸴ Delta1 & Delta3 ⊢c t ->
        ok (Delta1 & Delta2) ->
        Gamma ⸴ Delta1 & Delta2 & Delta3 ⊢c t.
    Proof.
      induction Delta2 using env_ind; intros;
        rewrite ? concat_empty_r, ? concat_assoc in *; eauto.
      apply ok_push_inv in H0; destruct H0; auto.
    Qed.

    Lemma commit_weaken_ok_middle : forall Gamma1 Gamma2 Gamma3 Delta1 Delta2 Delta3 (t : A),
        Gamma1 & Gamma3 ⸴ Delta1 & Delta3 ⊢c t ->
        ok (Gamma1 & Gamma2) ->
        ok (Delta1 & Delta2) ->
        Gamma1 & Gamma2 & Gamma3 ⸴ Delta1 & Delta2 & Delta3 ⊢c t.
    Proof.
      eauto using commit_weaken_ok_G_middle, commit_weaken_ok_D_middle.
    Qed.

    Lemma commit_weaken_G_ok : forall Gamma1 Gamma2 Delta (t : A),
        Gamma1 ⸴ Delta ⊢c t ->
        ok (Gamma1 & Gamma2) ->
        Gamma1 & Gamma2 ⸴ Delta ⊢c t .
    Proof.
      induction Gamma2 using env_ind;
        intros; rewrite ? concat_empty_r, ? concat_assoc in *; auto.
      apply ok_push_inv in H0; destruct H0; eauto using commit_weaken_G.
    Qed.

    Lemma commit_weaken_D_ok : forall Gamma Delta1 Delta2 (t : A),
        Gamma ⸴ Delta1 ⊢c t ->
        ok (Delta1 & Delta2) ->
        Gamma ⸴ Delta1 & Delta2 ⊢c t .
    Proof.
      induction Delta2 using env_ind;
        intros; rewrite ? concat_empty_r, ? concat_assoc in *; auto.
      apply ok_push_inv in H0; destruct H0; eauto using commit_weaken_D.
    Qed.

    Lemma commit_weaken_ok : forall Gamma1 Gamma2 Delta1 Delta2 (t : A),
        Gamma1 ⸴ Delta1 ⊢c t ->
        ok (Gamma1 & Gamma2) ->
        ok (Delta1 & Delta2) ->
        Gamma1 & Gamma2 ⸴ Delta1 & Delta2 ⊢c t.
    Proof.
      eauto using commit_weaken_D_ok, commit_weaken_G_ok.
    Qed.

  End Weaken.
End CommitWeaken.

Instance LitCommitTypingWeakenMiddleG : CommitTypingWeakenMiddleG well_committed_lit.
Proof.
  hnf; intros. eapply well_init_weaken_G_rules; try reflexivity; eauto.
Qed.

Instance LitCommitTypingWeakenMiddleD : CommitTypingWeakenMiddleD well_committed_lit.
Proof.
  hnf; intros. eapply well_init_weaken_D_rules; try reflexivity; eauto.
Qed.

Instance WellCommitTypingWeakenMiddleG : CommitTypingWeakenMiddleG well_committed.
Proof.
  hnf; intros. eapply well_init_weaken_G_rules; try reflexivity; eauto.
Qed.

Instance WellCommitTypingWeakenMiddleD : CommitTypingWeakenMiddleD well_committed.
Proof.
  hnf; intros. eapply well_init_weaken_D_rules; try reflexivity; eauto.
Qed.

Lemma well_init_weaken_set_rules_D :
  (forall Gamma Delta t,
      Gamma ⸴ Delta ⊢c t ->
      forall Delta', (forall x init, binds x init Delta -> binds x init Delta') ->
        Gamma ⸴ Delta' ⊢c t ) /\
  (forall Gamma Delta avs,
      Gamma ⸴ Delta ⊢c avs ->
      forall Delta', (forall x init, binds x init Delta -> binds x init Delta') ->
        Gamma ⸴ Delta' ⊢c avs) /\
  (forall Gamma Delta l,
      Gamma ⸴ Delta ⊢c l ->
      forall Delta', (forall x init, binds x init Delta -> binds x init Delta') ->
        Gamma ⸴ Delta' ⊢c l) /\
  (forall Gamma Delta vs t i,
      Gamma ⸴ Delta ⸴ vs ⊢i t ∶ i ->
      forall Delta', (forall x init, binds x init Delta -> binds x init Delta') ->
        Gamma ⸴ Delta' ⸴ vs ⊢i t ∶ i) /\
  (forall Gamma Delta vs avs is',
      Gamma ⸴ Delta ⸴ vs ⊢i avs :: is' ->
      forall Delta', (forall x init, binds x init Delta -> binds x init Delta') ->
        Gamma ⸴ Delta' ⸴ vs ⊢i avs :: is').
Proof.
  apply well_init_mut_ind; intros; subst; eauto.
  - init_fresh_constructor_extern; eauto.
    apply H0; auto. intros.
    apply binds_push_inv in H2; destruct_ors; destruct_ands; subst; auto.
  - init_fresh_constructor_extern; eauto.
    apply H0; auto. intros.
    apply binds_push_inv in H2; destruct_ors; destruct_ands; subst; auto.
  - init_fresh_constructor_extern; eauto.
    apply H; auto. intros.
    apply binds_push_inv in H1; destruct_ors; destruct_ands; subst; auto.
  - init_fresh_constructor_extern; eauto.
    intros. eapply H; eauto. intros.
    apply binds_push_inv in H3; destruct_ors; destruct_ands; subst; auto.
    apply binds_push_neq; auto.
    apply binds_concat_cases in H4; destruct_all; auto.
  - init_fresh_constructor_extern; eauto.
    apply H0; auto. intros.
    apply binds_push_inv in H2; destruct_ors; destruct_ands; subst; auto.
  - init_fresh_constructor_extern; eauto.
    apply H0; auto. intros.
    apply binds_push_inv in H2; destruct_ors; destruct_ands; subst; auto.
Qed.

Lemma init_var_sub_ctx_change : forall Delta Delta' vs x i,
    init_var Delta vs x i ->
    (forall x, binds x committed Delta -> binds x committed Delta') ->
    (forall (x : var) (init : init_typ),
        x \in vs -> binds x init Delta
              -> exists i, init_sub i init /\ binds x i Delta') ->
    init_var Delta' vs x i.
Proof.
  induction 1; introv Hinitcom Hinitsub; eauto 3.
  - specialize (Hinitsub _ _ H H0). destruct Hinitsub as [i [Hinitsub HbinxD']].
    apply init_var_sub_local in Hinitsub. subst. auto.
  - specialize (Hinitsub _ _ H H0). destruct Hinitsub as [i [Hinitsub HbinxD']].
    apply init_var_sub_free in Hinitsub. destruct Hinitsub; subst; eauto 3.
  - specialize (Hinitsub _ _ H H0). destruct Hinitsub as [i [Hinitsub HbinxD']].
    destruct i; eauto 3.
Qed.

Lemma well_init_more_committed_rules :
  (forall Gamma Delta t,
      Gamma ⸴ Delta ⊢c t ->
      forall Delta', (forall x, binds x committed Delta -> binds x committed Delta') ->
        Gamma ⸴ Delta' ⊢c t ) /\
  (forall Gamma Delta avs,
      Gamma ⸴ Delta ⊢c avs ->
      forall Delta', (forall x, binds x committed Delta -> binds x committed Delta') ->
        Gamma ⸴ Delta' ⊢c avs) /\
  (forall Gamma Delta l,
      Gamma ⸴ Delta ⊢c l ->
      forall Delta', (forall x, binds x committed Delta -> binds x committed Delta') ->
        Gamma ⸴ Delta' ⊢c l) /\
  (forall Gamma Delta vs t i,
      Gamma ⸴ Delta ⸴ vs ⊢i t ∶ i ->
      forall Delta', (forall x, binds x committed Delta -> binds x committed Delta') ->
                (forall x init, x \in vs
                                 -> binds x init Delta
                                 -> exists i, init_sub i init /\ binds x i Delta') ->
        Gamma ⸴ Delta' ⸴ vs ⊢i t ∶ i) /\
  (forall Gamma Delta vs avs is',
      Gamma ⸴ Delta ⸴ vs ⊢i avs :: is' ->
      forall Delta', (forall x, binds x committed Delta -> binds x committed Delta') ->
                (forall x init, x \in vs
                                 -> binds x init Delta
                                 -> exists i, init_sub i init /\ binds x i Delta') ->
        Gamma ⸴ Delta' ⸴ vs ⊢i avs :: is').
Proof.
  apply well_init_mut_ind; intros; subst; eauto 4.
  - init_fresh_constructor_extern; eauto.
    apply H0; intros; auto.
    apply binds_push_inv in H2; destruct_ors; destruct_ands; subst; auto.
  - init_fresh_constructor_extern; eauto.
    apply H0; intros; auto.
    apply binds_push_inv in H2; destruct_ors; destruct_ands; subst; auto.
  - init_fresh_constructor_extern; eauto.
    apply H; intros; auto.
    apply binds_push_inv in H1; destruct_ors; destruct_ands; subst; auto.
  - init_fresh_constructor_extern; eauto.
    intros. apply H; auto.
    + intros. rewrite <- concat_assoc in H3 |- *. apply binds_concat_inv in H3.
      destruct H3 as [? | [? ?]]; auto.
    + intros. rewrite <- concat_assoc in H4 |- *. exists init. split; auto.
      apply binds_concat_right.
      assert (from_list ys \u \{ x} = dom (ys ~** is' & x ~ free)).
      { simpl_dom; rewrite dom_singles, union_comm, from_list_rev; auto.
        rewrite liblist_length, ? List.rev_length; congruence. }
      rewrite H5 in H3.
      apply dom_to_binds in H3. destruct H3 as [?init H3].
      pose proof (binds_concat_right Delta H3); binds_eq; auto.
  - constructor. eauto 3 using init_var_sub_ctx_change.
  - init_fresh_constructor_extern; eauto.
    apply H0; intros; auto.
    apply binds_push_inv in H3; destruct_ors; destruct_ands; subst; auto.
    rewrite in_union_singleton_r in H3; destruct H3; subst.
    + apply binds_push_inv in H4. destruct H4 as [[? ?] | [Hxneqz HxbinD]]; subst;
                                    eauto 3.
      specialize (H2 _ _ H3 HxbinD). destruct H2 as [ix [Hxinitsub HbixD']].
      exists ix. split; auto.
    + apply binds_push_inv in H4. destruct H4 as [[? ?] | [Hxneqz HxbinD]]; subst;
                                    eauto 3. congruence.
  - init_fresh_constructor_extern; eauto.
    apply H0; intros; auto.
    apply binds_push_inv in H3; destruct_ors; destruct_ands; subst; auto.
    apply binds_push_inv in H4. destruct H4 as [[? ?] | [Hxneqz HxbinD]]; subst;
                                  eauto 3.
    specialize (H2 _ _ H3 HxbinD). destruct H2 as [ix [Hxinitsub HbixD']].
    exists ix. split; auto.
Qed.

Lemma well_init_more_committed_renaming : forall L Gamma Delta vs S i t i' Delta',
    (forall x : var, x \notin L
                -> Gamma & x ~ S ⸴ Delta & x ~ i ⸴ vs \u \{ x} ⊢i open x t ∶ i') ->
    (forall x, binds x committed Delta -> binds x committed Delta') ->
    (forall x init, x \in vs
                     -> binds x init Delta
                     -> exists i, init_sub i init /\ binds x i Delta') ->
    exists L', (forall x : var, x \notin L' ->
                      Gamma & x ~ S ⸴ Delta' & x ~ i ⸴ vs \u \{ x} ⊢i open x t ∶ i').
Proof.
  intros. exists (L \u vs \u dom Delta).
  intros. assert (x \notin L) by auto. assert (x # Delta) by auto.
  assert (x \notin vs) by auto.
  pose proof (H _ H3). eapply well_init_more_committed_rules; eauto.
  - intros. apply binds_push_inv in H7 as [[Heq Heq'] | [Hneq Hbi]]; subst; auto.
  - intros. apply binds_push_inv in H8. rewrite in_union, in_singleton in H7.
    destruct_all; subst; try congruence; eauto 3.
    specialize (H1 _ _ H7 H9). destruct H1 as [ix [Hinisub HbixD']]. eauto.
Qed.

Lemma well_init_more_specified_rules :
  (forall Gamma Delta t,
      Gamma ⸴ Delta ⊢c t ->
      forall Delta1 x Delta2 i',
        Delta = Delta1 & x ~ unspecified & Delta2 -> x # Delta2 ->
        (i' = free) \/ (i' = committed) ->
        Gamma ⸴ Delta1 & x ~ i' & Delta2 ⊢c t ) /\
  (forall Gamma Delta avs,
      Gamma ⸴ Delta ⊢c avs ->
      forall Delta1 x Delta2 i',
        Delta = Delta1 & x ~ unspecified & Delta2 -> x # Delta2 ->
        (i' = free) \/ (i' = committed) ->
        Gamma ⸴ Delta1 & x ~ i' & Delta2 ⊢c avs) /\
  (forall Gamma Delta l,
      Gamma ⸴ Delta ⊢c l ->
      forall Delta1 x Delta2 i',
        Delta = Delta1 & x ~ unspecified & Delta2 -> x # Delta2 ->
        (i' = free) \/ (i' = committed) ->
        Gamma ⸴ Delta1 & x ~ i' & Delta2 ⊢c l) /\
  (forall Gamma Delta vs t i,
      Gamma ⸴ Delta ⸴ vs ⊢i t ∶ i ->
      forall Delta1 x Delta2 i',
        Delta = Delta1 & x ~ unspecified & Delta2 -> x # Delta2 ->
        (i' = free) \/ (i' = committed) ->
        Gamma ⸴ Delta1 & x ~ i' & Delta2 ⸴ vs ⊢i t ∶ i) /\
  (forall Gamma Delta vs avs is',
      Gamma ⸴ Delta ⸴ vs ⊢i avs :: is' ->
      forall Delta1 x Delta2 i',
        Delta = Delta1 & x ~ unspecified & Delta2 -> x # Delta2 ->
        (i' = free) \/ (i' = committed) ->
        Gamma ⸴ Delta1 & x ~ i' & Delta2 ⸴ vs ⊢i avs :: is').
Proof.
  apply well_init_mut_ind; intros; subst;
    eauto 4 using init_var_more_specified.
  - pose proof (binds_middle_inv b) as [? | [ [? [? ?]] | [? [? ?]]]];
      try congruence; auto.
  - init_fresh_constructor_extern. eapply H; eauto.
    intros. rewrite <- (concat_assoc (Delta1 & _)).
    apply H0; auto.
  - init_fresh_constructor_extern. apply H; eauto.
    intros. rewrite <- (concat_assoc (Delta1 & _)).
    apply H0; eauto.
  - init_fresh_constructor_extern.
    intros. rewrite <- (concat_assoc (Delta1 & _)).
    apply H; eauto.
  - init_fresh_constructor_extern; eauto. intros.
    rewrite <- ? (concat_assoc (Delta1 & _)).
    apply H; try eassumption. fresh_solve.
    rewrite ? concat_assoc; auto.
    simpl_dom; notin_solve. rewrite dom_singles; auto.
    rewrite <- from_list_rev.
    apply fresh_single_notin with (n:=length ys); auto.
    rewrite liblist_length, ? List.rev_length; congruence.
  - init_fresh_constructor_extern. eapply H; eauto.
    intros. rewrite <- (concat_assoc (Delta1 & _)).
    apply H0; auto.
  - init_fresh_constructor_extern. apply H; eauto.
    intros. rewrite <- (concat_assoc (Delta1 & _)).
    apply H0; eauto.
Qed.

Lemma init_avar_sub_free : forall Gamma Delta vs i x,
    x \in vs -> binds x i Delta -> init_sub i free ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_var (avar_f x) ∶ free.
Proof with eauto.
  introv Hxin Hxbin Hsub.
  apply init_var_sub_free in Hsub. destruct_all; subst; eauto 4.
Qed.
Hint Resolve init_avar_sub_free : core.

Lemma init_avar_binds_unspec : forall Gamma Delta vs i x,
    x \in vs -> binds x i Delta ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_var (avar_f x) ∶ unspecified.
Proof. introv Hxin Hxbin. destruct i; eauto 4. econstructor.
       eapply init_var_sub with (i' := local); eauto.
Qed.
Hint Resolve init_avar_binds_unspec : core.

Lemma well_init_more_committed_rules_sub :
  (forall Gamma Delta t,
      Gamma ⸴ Delta ⊢c t ->
      forall Delta', (forall x, binds x committed Delta -> binds x committed Delta') ->
        Gamma ⸴ Delta' ⊢c t ) /\
  (forall Gamma Delta avs,
      Gamma ⸴ Delta ⊢c avs ->
      forall Delta', (forall x, binds x committed Delta -> binds x committed Delta') ->
        Gamma ⸴ Delta' ⊢c avs) /\
  (forall Gamma Delta l,
      Gamma ⸴ Delta ⊢c l ->
      forall Delta', (forall x, binds x committed Delta -> binds x committed Delta') ->
        Gamma ⸴ Delta' ⊢c l) /\
  (forall Gamma Delta vs t i,
      Gamma ⸴ Delta ⸴ vs ⊢i t ∶ i ->
      forall Delta',
        (forall x, binds x committed Delta -> binds x committed Delta') ->
        (forall x init, x \in vs -> binds x init Delta ->
                         exists i', binds x i' Delta' /\ init_sub i' init) ->
        Gamma ⸴ Delta' ⸴ vs ⊢i t ∶ i) /\
  (forall Gamma Delta vs avs is',
      Gamma ⸴ Delta ⸴ vs ⊢i avs :: is' ->
      forall Delta',
        (forall x, binds x committed Delta -> binds x committed Delta') ->
        (forall x init, x \in vs -> binds x init Delta ->
                         exists i', binds x i' Delta' /\ init_sub i' init) ->
        Gamma ⸴ Delta' ⸴ vs ⊢i avs :: is').
Proof.
  apply well_init_mut_ind; intros; subst; eauto 4.
  - init_fresh_constructor_extern; eauto.
    apply H0; intros; auto.
    apply binds_push_inv in H2; destruct_ors; destruct_ands; subst; auto.
  - init_fresh_constructor_extern; eauto.
    apply H0; intros; auto.
    apply binds_push_inv in H2; destruct_ors; destruct_ands; subst; auto.
  - init_fresh_constructor_extern; eauto.
    apply H; intros; auto.
    apply binds_push_inv in H1; destruct_ors; destruct_ands; subst; auto.
  - init_fresh_constructor_extern; eauto.
    intros. apply H; auto.
    + intros. rewrite <- concat_assoc in H3 |- *. apply binds_concat_inv in H3.
      destruct H3 as [? | [? ?]]; auto.
    + intros. rewrite <- concat_assoc in H4 |- *. exists init.
      split; auto.
      apply binds_concat_right.
      assert (from_list ys \u \{ x} = dom (ys ~** is' & x ~ free)).
      { simpl_dom; rewrite dom_singles, union_comm, from_list_rev; auto.
        rewrite liblist_length, ? List.rev_length; congruence. }
      rewrite H5 in H3.
      apply dom_to_binds in H3. destruct H3 as [?init H3].
      pose proof (binds_concat_right Delta H3); binds_eq; auto.
  - induction i0; eauto 4;
      try(match goal with
          | [ Hin : x \in vs, Hbin : binds x ?i Delta,
              Hbinsub : forall (x : var) (init : init_typ),
                x \in vs ->
                binds x init Delta ->
                exists i', binds x i' Delta' /\ init_sub i' init |- _ ] =>
            specialize (Hbinsub _ _ Hin Hbin); destruct_all; rename x0 into i'
          end).
    + apply init_var_sub_local in H3. subst. eauto 3.
    + apply init_var_sub_free in H3. destruct_all; subst; eauto 3.
    + destruct i'; eauto 3.
    + specialize (IHi0 H H0). inversions IHi0; eauto 3.
      econstructor. dependent induction i0; eauto 4.
      eapply IHi0; eauto using init_var_sub_comm.
  - init_fresh_constructor_extern; eauto.
    apply H0; intros; auto.
    apply binds_push_inv in H3; destruct_ors; destruct_ands; subst; auto.
    rewrite in_union_singleton_r in H3; destruct H3; subst.
    + specialize (H2 _ init H3).
      apply binds_concat_inv in H4 as [Hxeqz | [Hxneqz HinD]].
      * apply binds_single_inv in Hxeqz as [? ?]; subst.
        exists i. split; auto.
      * specialize (H2 HinD). destruct H2 as [i'0 [Hbinx Hsub]].
        exists i'0. split; auto.
    + apply binds_push_eq_inv in H4; subst. exists i. split; auto.
  - init_fresh_constructor_extern; eauto.
    apply H0; intros; auto.
    apply binds_push_inv in H3; destruct_ors; destruct_ands; subst; auto.
    apply binds_concat_inv in H4 as [Hxeqz | [Hxneqz HinD]].
    * apply binds_single_inv in Hxeqz as [? ?]; subst.
      exists committed. split; auto.
    * specialize (H2 _ _ H3 HinD). destruct H2 as [i'0 [Hbinx Hsub]].
      exists i'0. split; auto.
Qed.

Corollary well_init_more_committed_renaming_sub : forall L Gamma Delta vs S i t i' Delta',
    (forall x : var, x \notin L ->
                Gamma & x ~ S ⸴ Delta & x ~ i ⸴ vs \u \{ x} ⊢i open x t ∶ i') ->
    (forall x, binds x committed Delta -> binds x committed Delta') ->
    (forall x init, x \in vs -> binds x init Delta ->
                     exists i', binds x i' Delta' /\ init_sub i' init) ->
    exists L', (forall x : var, x \notin L' ->
                      Gamma & x ~ S ⸴ Delta' & x ~ i ⸴ vs \u \{ x} ⊢i open x t ∶ i').
Proof.
  intros. exists (L \u vs \u dom Delta).
  intros. assert (x \notin L) by auto. assert (x # Delta) by auto.
  assert (x \notin vs) by auto.
  pose proof (H _ H3). eapply well_init_more_committed_rules_sub; eauto.
  - intros. apply binds_push_inv in H7 as [[Heq Heq'] | [Hneq Hbi]]; subst; auto.
  - intros. apply binds_push_inv in H8. rewrite in_union, in_singleton in H7.
    destruct_all; subst; try congruence; auto.
    + exists i. auto.
    + specialize (H1 _ _ H7 H9). destruct_all. rename x1 into i0. exists i0. split; auto.
Qed.
