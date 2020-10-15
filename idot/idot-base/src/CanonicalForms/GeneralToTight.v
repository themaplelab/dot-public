(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra.
Require Import Coq.Program.Equality.
Require Import AbstractSyntax Typing.
Require Import GeneralTyping
        RecordTypes InertTypes DefRecordInertTyping PreciseTyping
        TightTyping InvertibleTyping SelReplacement.

(** * General to Tight [⊢ to ⊢#] *)
(** The following lemma says that in an inert environment, general typing
    ([ty_trm] [⊢]) can be reduced to tight typing ([ty_trm_t] [⊢#]).
    The proof is by mutual induction on the typing and subtyping judgements.

    [inert G]           #<br>#
    [G ⊢ t∶ T]          #<br>#
    [――――――――――――――]    #<br>#
    [G ⊢# t∶ T] #<br># #<br>#

    and                 #<br># #<br>#
    [inert G]           #<br>#
    [G ⊢ S <: U]        #<br>#
    [――――――――――――――――]  #<br>#
    [G ⊢# S <: U]         *)
Lemma general_to_tight: forall G0,
  inert G0 ->
  (forall G t T,
     G ⊢ t ∶ T ->
     G = G0 ->
     G ⊢# t ∶ T) /\
  (forall G S U,
     G ⊢ S <: U ->
     G = G0 ->
     G ⊢# S <: U) /\
  (forall G avs Ts,
     G ⊢ avs :: Ts ->
     G = G0 ->
     G ⊢# avs :: Ts).
Proof.
  intros G0 HG.
  apply ts_mutind; intros; subst;
    try solve [eapply sel_replacement; auto]; eauto.
Qed.

(** The general-to-tight lemma, formulated for term typing. *)
Lemma general_to_tight_typing: forall G t T,
  inert G ->
  G ⊢ t ∶ T ->
  G ⊢# t ∶ T.
Proof.
  intros. apply* general_to_tight.
Qed.
