(** remove printing ~ *)

(** This module contains lemmas related to invertible typing
    ([ty_var_inv], [⊢##] and [ty_item_inv], [⊢##v]). *)

Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import Coq.Program.Equality.
Require Import AbstractSyntax GeneralTyping
        PreciseTyping RecordAndInertTypes
        TightTyping Subenvironments Narrowing
        InertTightSubtyping.

(** ** Invertible typing *)

(** The invertible-typing relation describes the possible types that a variable or value
can be typed with in an inert context. For example, if [G] is inert, [G ⊢! x: {a: T}],
and [G ⊢ T <: T'], then [G ⊢## x: {a: T'}].

The purpose of invertible typing is to be easily invertible into a precise typing relation.
To achieve that, invertible typing avoids typing cycles that could result from, for example,
repeated applications of recursion introduction and elimination.
For this case, invertible typing defines only recursion introduction (whereas precise typing
defines only recursion elimination). *)

(** ** Invertible typing of variables [G ⊢## x: T] *)

Reserved Notation "G '⊢##' x '∶' T" (at level 40, x at level 59).

Inductive ty_var_inv : ctx -> var -> typ -> Prop :=

(** [G ⊢! x∶ T]  #<br>#
    [―――――――――――] #<br>#
    [G ⊢## x∶ T]     *)
| ty_precise_inv : forall G x T U,
  G ⊢! x ∶ T ⪼ U ->
  G ⊢## x ∶ U

(** [G ⊢## x∶ {a: T}] #<br>#
    [G ⊢# T <: U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢## x∶ {a: U}]     *)
| ty_dec_trm_inv : forall G x a T1 T2 U1 U2,
  G ⊢## x ∶ typ_rcd (dec_trm a T2 U1) ->
  G ⊢# T1 <: T2 ->
  G ⊢# U1 <: U2 ->
  G ⊢## x ∶ typ_rcd (dec_trm a T1 U2)

(** [G ⊢## x∶ {A: T..U}]   #<br>#
    [G ⊢# T' <: T]         #<br>#
    [G ⊢# U <: U']         #<br>#
    [―――――――――――――――――――――] #<br>#
    [G ⊢## x∶ {A: T'..U'}]     *)
| ty_dec_typ_inv : forall G x A T T' U' U,
  G ⊢## x ∶ typ_rcd (dec_typ A T U) ->
  G ⊢# T' <: T ->
  G ⊢# U <: U' ->
  G ⊢## x ∶ typ_rcd (dec_typ A T' U')

(** [G ⊢## x∶ T^x]   #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢## x∶ mu(T)] *)
| ty_bnd_inv : forall G x T,
  G ⊢## x ∶ open x T ->
  G ⊢## x ∶ typ_bnd T

(** [G ⊢## x∶ forall(S)T]          #<br>#
    [G ⊢# S' <: S]            #<br>#
    [G, y: S' ⊢ T^y <: T'^y]   #<br>#
    [y fresh]                  #<br>#
    [――――――――――――――――――――――]   #<br>#
    [G ⊢## x∶ forall(S')T']            *)
| ty_all_inv : forall L G x S T S' T',
  G ⊢## x ∶ typ_all S T ->
  G ⊢# S' <: S ->
  (forall y, y \notin L ->
   G & y ~ S' ⊢ open y T <: open y T') ->
  G ⊢## x ∶ typ_all S' T'

(** [G ⊢## x ∶ T]     #<br>#
    [G ⊢## x ∶ U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢## x ∶ T /\ U]      *)
| ty_and_inv : forall G x S1 S2,
  G ⊢## x ∶ S1 ->
  G ⊢## x ∶ S2 ->
  G ⊢## x ∶ typ_and S1 S2

(** [G ⊢## x∶ S]        #<br>#
    [G ⊢! y∶ {A: S..S}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢## x∶ y.A           *)
| ty_sel_inv : forall G x y A S U,
  G ⊢## x ∶ S ->
  G ⊢! y ∶ U ⪼ typ_rcd (dec_typ A S S) ->
  G ⊢## x ∶ typ_sel (avar_f y) A

(** [G ⊢## x∶ T]   #<br>#
    [―――――――――――――] #<br>#
    [G ⊢## x∶ top]     *)
| ty_top_inv : forall G x T,
  G ⊢## x ∶ T ->
  G ⊢## x ∶ typ_top
where "G '⊢##' x '∶' T" := (ty_var_inv G x T).

Hint Constructors ty_var_inv : core.

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
      assert (Hok: ok (G & y ~ S)) by auto using ok_push.
      apply tight_to_general in H; auto.
      assert (Hnarrow: G & y ~ S ⊢ open y T' <: open y T0).
      { eapply narrow_subtyping; auto using subenv_last. }
      eauto.
Qed.

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
    G ⊢# x ∶ U ->
    G ⊢## x ∶ U.
Proof.
  intros G U x Hgd Hty.
  remember (trm_var (avar_f x)) as t eqn:Heq.
  induction Hty; try congruence; inversions Heq; eauto.
  - specialize (IHHty Hgd eq_refl).
    inversion IHHty; subst; eauto using ty_precise_inv.
  - eapply invertible_typing_closure_tight; auto.
Qed.
