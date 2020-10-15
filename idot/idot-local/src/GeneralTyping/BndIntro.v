(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import AbstractSyntax PreTyping Typing GeneralTyping.

Instance DefDecTypingBndIntroMiddle : PreTypingBndIntroMiddle (DecPreTyping ty_def).
Proof.
  hnf. inversion 1; subst; auto.
Qed.

Local Hint Extern 7 (_ ⊢ _ ∶ _) => apply bnd_intro4 : core.

Lemma ty_open_implies_ty_bnd: forall G1 y T1,
    (forall G (t : trm) T,
        G ⊢ t ∶ T ->
        (forall G2, G = G1 & y ~ open y T1 & G2 ->
               G1 & y ~ typ_bnd T1 & G2 ⊢ t ∶ T)) /\
    (forall G (l : lit) T,
        G ⊢ l ∶ T ->
        (forall G2, G = G1 & y ~ open y T1 & G2 ->
               G1 & y ~ typ_bnd T1 & G2 ⊢ l ∶ T)) /\
    (forall G T T',
        G ⊢ T <: T' ->
        (forall G2, G = G1 & y ~ open y T1 & G2 ->
               G1 & y ~ typ_bnd T1 & G2 ⊢ T <: T')) /\
    (forall G avs Ts,
        G ⊢ avs :: Ts ->
        (forall G2, G = G1 & y ~ open y T1 & G2 ->
               G1 & y ~ typ_bnd T1 & G2 ⊢ avs :: Ts)).
Proof.
  intros.
  apply rules_mutind; intros; subst;
    try solve [fresh_constructor || econstructor; auto].
  - pose proof (binds_middle_inv b) as Bi.
    destruct Bi as [ Bi | [ [Fr [ Eqx ExT ]] | [Fr [Neqx Bi]]]];
      subst; auto.
Qed.

Instance TyTrmBndIntroMiddle : PreTypingBndIntroMiddle (TyPreTyping ty_trm).
Proof.
  hnf; intros; eapply ty_open_implies_ty_bnd; eauto.
Qed.

Instance TyLitBndIntroMiddle : PreTypingBndIntroMiddle (TyPreTyping ty_lit).
Proof.
  hnf; intros; eapply ty_open_implies_ty_bnd; eauto.
Qed.

Instance TyAvarsBndIntroMiddle : PreTypingBndIntroMiddle (TysPreTyping ty_avars).
Proof.
  hnf; intros; eapply ty_open_implies_ty_bnd; eauto.
Qed.
