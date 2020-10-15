(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra.
Require Import Coq.Program.Equality.
Require Import AbstractSyntax Typing.
Require Import
        RecordTypes InertTypes PreciseTyping PreciseTypingLemmas
        TightTyping InvertibleTyping TightToInvertible.

(** In this module we prove some lemmas about type selection. *)

(** * Sel-<: Premise

    [inert G]                    #<br>#
    [G ⊢## x∶ {A: S..U}]        #<br>#
    [――――――――――――――――――――――――――――]   #<br>#
    [exists T. G ⊢## x∶ {A: T..T}]   #<br>#
    [G ⊢# T <: U]               #<br>#
    [G ⊢# S <: T]                    *)
Lemma sel_premise: forall G x A S U,
  inert G ->
  G ⊢## x ∶ typ_rcd (dec_typ A S U) ->
  exists T V,
    G ⊢! x ∶ V ⪼ typ_rcd (dec_typ A T T) /\
    G ⊢# T <: U /\
    G ⊢# S <: T.
Proof.
  introv HG Hinv.
  dependent induction Hinv.
  - lets Hp: (pf_dec_typ_inv HG H). subst.
    exists U T. split*.
  - specialize (IHHinv A T U0 HG eq_refl).
    destruct IHHinv as [V [V' [Hx [Hs1 Hs2]]]].
    exists V V'. split*.
Qed.

(** * Sel-<: Replacement

    [inert G]              #<br>#
    [G ⊢# x∶ {A: S..U}]   #<br>#
    [――――――――――――――――――――――]   #<br>#
    [G ⊢# x.A <: U]       #<br>#
    [G ⊢# S <: x.A]            *)
Lemma sel_replacement: forall G x A S U,
    inert G ->
    G ⊢# trm_var (avar_f x) ∶ typ_rcd (dec_typ A S U) ->
    (G ⊢# typ_sel (avar_f x) A <: U /\
     G ⊢# S <: typ_sel (avar_f x) A).
Proof.
  introv HG Hty.
  pose proof (tight_to_invertible HG Hty) as Hinv.
  pose proof (sel_premise HG Hinv) as [T [V [Ht [Hs1 Hs2]]]].
  split.
  - apply subtyp_sel1_t in Ht. apply subtyp_trans_t with (T:=T); auto.
  - apply subtyp_sel2_t in Ht. apply subtyp_trans_t with (T:=T); auto.
Qed.
