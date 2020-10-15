(** remove printing ~ *)

(** This module contains lemmas related to invertible typing
    ([ty_var_inv], [⊢##] and [ty_item_inv], [⊢##v]). *)

Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import Coq.Program.Equality.
Require Import AbstractSyntax Typing
        PreciseTyping TightTyping InvertibleTyping
        Subenvironments Narrowing TypingToGeneral.

(** ** Invertible to Precise Typing [|-## to |-!] *)

(** Invertible-to-precise typing for field declarations: #<br>#
    [G ⊢## x∶ {a: T}]            #<br>#
    [――――――――――――――――――――――]      #<br>#
    [exists T', G ⊢! x∶ {a: T'}]      #<br>#
    [G ⊢# T' <: T]. *)
Lemma invertible_to_precise_trm_dec: forall G x a S T,
  G ⊢## x ∶ typ_rcd (dec_trm a S T) ->
  exists S' T' U,
    G ⊢! x ∶ U ⪼ typ_rcd (dec_trm a S' T') /\
    G ⊢# T' <: T /\
    G ⊢# S <: S'.
Proof.
  introv Hinv.
  dependent induction Hinv.
  - exists S T T0. auto.
  - specialize (IHHinv _ _ _ eq_refl). destruct IHHinv as [V [V' [V'' [Hx [Hs1 Hs2]]]]].
    exists V V' V''.
    repeat_split_right; auto; eapply subtyp_trans_t; eassumption.
Qed.

(** Invertible-to-precise typing for function types: #<br>#
    [ok G]                        #<br>#
    [G ⊢## x∶ forall(S)T]             #<br>#
    [――――――――――――――――――――――――――]  #<br>#
    [exists S', T'. G ⊢! x∶ forall(S')T']  #<br>#
    [G ⊢# S <: S']               #<br>#
    [G ⊢# T'^y <: T^y], where [y] is fresh. *)
Lemma invertible_to_precise_typ_all: forall G x S T,
  ok G ->
  G ⊢## x ∶ typ_all S T ->
  exists S' T' U L,
    G ⊢! x ∶ U ⪼ typ_all S' T' /\
    G ⊢# S <: S' /\
    (forall y,
        y \notin L ->
            G & y ~ S ⊢ open y T' <: open y T).
Proof.
  introv HG Hinv.
  dependent induction Hinv.
  - exists S T T0 (dom G); auto.
  - specialize (IHHinv _ _ HG eq_refl).
    destruct IHHinv as [S' [T' [V' [L' [Hpt [HSsub HTsub]]]]]].
    exists S' T' V' (dom G \u L \u L').
    split; auto.
    assert (Hsub2 : G ⊢# typ_all S0 T0 <: typ_all S T).
    { apply subtyp_all_t with (L:=L); assumption. }
    split.
    + eapply subtyp_trans_t; eauto.
    + intros y Fr.
      apply tight_to_general in H; auto.
      assert (Hnarrow: G & y ~ S ⊢ open y T' <: open y T0).
      { eapply narrow_subtyping; auto using subenv_last. }
      eauto.
Qed.
