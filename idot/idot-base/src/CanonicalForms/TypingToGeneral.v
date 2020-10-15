(** remove printing ~ *)

(** This module contains the various *_to_general lemmas. These lemmas show that
the types given to terms by the special typing relations can also be derived via
general typing. *)

Set Implicit Arguments.

Require Import LibExtra.
Require Import AbstractSyntax Typing.
Require Import GeneralTyping.
Require Import RecordTypes InertTypes.
Require Import PreciseTyping TightTyping InvertibleTyping.

(** Precise typing implies general typing. *)
(** - for variables *)
Lemma precise_to_general: forall G x T U,
    G ⊢! x ∶ T ⪼ U ->
    G ⊢ trm_var (avar_f x) ∶ U.
Proof.
  intros. induction H; intros; subst; eauto.
Qed.

(** Tight typing implies general typing. *)
Lemma tight_to_general:
  (forall G t T,
     G ⊢# t ∶ T ->
     G ⊢ t ∶ T) /\
  (forall G S U,
     G ⊢# S <: U ->
     G ⊢ S <: U) /\
  (forall G avs Ts,
     G ⊢# avs :: Ts ->
     G ⊢ avs :: Ts).
Proof.
  apply ts_t_mutind; intros; subst; eauto using precise_to_general.
Qed.
