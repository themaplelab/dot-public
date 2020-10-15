(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra.
Require Import AbstractSyntax PreTyping Typing GeneralTyping.

(** * Weakening Lemma *)
(** Weakening states that typing is preserved in extended environments.
    The weakening lemmas are automatically derived via the typeclass mechanism
    by providing instances of [PreTypingWeakenMiddle].
 *)
Instance DefDecTypingWeakenMiddle : PreTypingWeakenMiddle (DecPreTyping ty_def).
Proof.
  hnf; introv H. inversions H; auto.
Qed.

Local Hint Extern 7 (_ & _ ⊢ _ ∶ _) => apply weaken4 : core.

Lemma weaken_rules:
  (forall Gamma (t : trm) T, Gamma ⊢ t ∶ T -> forall Gamma1 x T' Gamma3,
    Gamma = Gamma1 & Gamma3 ->
    x # Gamma1 ->
    Gamma1 & x ~ T' & Gamma3 ⊢ t ∶ T) /\
  (forall Gamma (l : lit) T, Gamma ⊢ l ∶ T -> forall Gamma1 x T' Gamma3,
    Gamma = Gamma1 & Gamma3 ->
    x # Gamma1 ->
    Gamma1 & x ~ T' & Gamma3 ⊢ l ∶ T) /\
  (forall Gamma T U, Gamma ⊢ T <: U -> forall Gamma1 x T' Gamma3,
    Gamma = Gamma1 & Gamma3 ->
    x # Gamma1 ->
    Gamma1 & x ~ T' & Gamma3 ⊢ T <: U) /\
  (forall Gamma avs Ts, Gamma ⊢ avs :: Ts -> forall Gamma1 x T' Gamma3,
    Gamma = Gamma1 & Gamma3 ->
    x # Gamma1 ->
    Gamma1 & x ~ T' & Gamma3 ⊢ avs :: Ts).
Proof.
  apply rules_mutind; intros; subst;
    match goal with
    | |- context[lit_con] =>
      eauto 7
    | _ => auto using binds_push_fresh_middle; eauto
    end.
Qed.

Instance TrmTypingWeakenMiddle : PreTypingWeakenMiddle (TyPreTyping ty_trm).
Proof.
  hnf; intros; eapply weaken_rules; eauto.
Qed.

Instance LitTypingWeakenMiddle : PreTypingWeakenMiddle (TyPreTyping ty_lit).
Proof.
  hnf; intros; eapply weaken_rules; eauto.
Qed.

Instance SubTypingWeakenMiddle : PreTypingWeakenMiddle SubPreTyping.
Proof.
  hnf; intros; eapply weaken_rules; eauto.
Qed.

Instance AvarsTypingWeakenMiddle : PreTypingWeakenMiddle (TysPreTyping ty_avars).
Proof.
  hnf; intros; eapply weaken_rules; eauto.
Qed.
