(** remove printing ~ *)

(** This module contains lemmas related to invertible typing
    ([ty_var_inv], [⊢##] and [ty_item_inv], [⊢##v]). *)

Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import Coq.Program.Equality.
Require Import AbstractSyntax Typing GeneralTyping
        InertTypes InertTightSubtyping
        TightTyping PreciseTyping PreciseTypingLemmas InvertibleTyping.

(** ** Invertible Subtyping Closure *)

(** Invertible typing is closed under tight subtyping. *)
Lemma invertible_typing_closure_tight: forall G x T U,
  inert G ->
  G ⊢## x ∶ T ->
  G ⊢# T <: U ->
  G ⊢## x ∶ U.
Proof.
  intros G x T U Hi HT Hsub.
  dependent induction Hsub; eauto.
  - inversion HT.
    destruct (pf_bot_false Hi H).
  - inversion HT; auto. apply pf_and1 in H. apply* ty_precise_inv.
  - inversion HT; auto. apply pf_and2 in H. apply* ty_precise_inv.
  - inversions HT.
    + false* pf_psel_false.
    + lets Hu: (x_bound_unique H H5). subst.
      pose proof (pf_inert_unique_tight_bounds Hi H H5) as Hu. subst. assumption.
Qed.

(** ** Tight-to-Invertible Lemma for Variables [|-# to |-##]

       [inert G]            #<br>#
       [G ⊢# x∶ U]         #<br>#
       [―――――――――――――――]    #<br>#
       [G ⊢## x∶ U] *)
Lemma tight_to_invertible :
  forall G U x,
    inert G ->
    G ⊢# trm_var (avar_f x) ∶ U ->
    G ⊢## x ∶ U.
Proof.
  intros G U x Hgd Hty.
  remember (trm_var (avar_f x)) as t eqn:Heq.
  induction Hty; try congruence; inversions Heq; eauto.
  - specialize (IHHty Hgd eq_refl).
    inversion IHHty; subst; eauto using ty_precise_inv.
  - eapply invertible_typing_closure_tight; auto.
Qed.
