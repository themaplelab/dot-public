Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import
        AbstractSyntax PreTyping Typing GeneralTyping
        RecordAndInertTypes
        OperationalSemantics
        Effects InitVar InitTyping
        ConfigTyping.

Require Preservation Progress.

(** * Initial Configuration is well-typed *)
(** [⊢ t : T]                  #<br>#
    [⊢i t : committed]         #<br>#
    [―――――――――――――――――――――――]  #<br>#
    [⊢ (t; ε; ⋅) : (ε :: nil, T)]         *)
Lemma initial_config_typed : forall t T,
    empty ⊢ t ∶ T ->
    empty ⸴ empty ⸴ \{} ⊢i t ∶ committed ->
    ty_config empty empty (empty :: nil) (nil :: nil) (t; nil; empty) T.
Proof.
  eauto using ConfigTyping.initial_config_typed.
Qed.

(** * Preservation Theorem *)

(** [Gamma; Delta; ℰs ⊢ c : (Es, U)]  #<br>#
    [c |-> c']                 #<br>#
    [―――――――――――――――――――――――]  #<br>#
    [exists Gamma' Delta' ℰs' Es']         #<br>#
    such that [Gamma; Delta; ℰs ⊢ c' : (Es', U)]         *)
Theorem preservation : forall Gamma Delta ℰs effss c c' U,
    ty_config Gamma Delta ℰs effss c U ->
    c ↦ c' ->
    exists Gamma' Delta' ℰs' effss', ty_config (Gamma & Gamma') Delta' ℰs' effss' c' U.
Proof.
  eauto using Preservation.preservation.
Qed.

(** * Progress Theorem *)
(** [Gamma; Delta; ℰs ⊢ c : (Es, U)]   #<br>#
    [―――――――――――――――――――――――]   #<br>#
    [c] is an answer   #<br>#
    or [exists c'] such that [(s, t) |-> (s', t')] *)
Theorem progress: forall Gamma Delta ℰs Es t s Sigma T,
    ty_config Gamma Delta ℰs Es (t ; s; Sigma) T ->
    answer (t; s; Sigma) \/
    exists s' Sigma' t', (t; s; Sigma) ↦ (t'; s'; Sigma').
Proof.
  eauto using Progress.progress.
Qed.
