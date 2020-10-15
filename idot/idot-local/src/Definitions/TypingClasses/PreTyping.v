(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra AbstractSyntax.

(** * PreTyping *)
(** We define a pretyping class so that we can share the weakening lemmas
    between different types of typing and subtyping.

   Pretyping relates a typing context and two abstract [Set]s, [A] and [B]. The
   Typing typeclasses will later sepecialize [B] for better error messages in
   case typeclasse resolution fails.

   Every implementation of [PreTyping] is expected to provide implementations of
   [PreTypingWeakenMiddle] and [PreTypingBndIntroMiddle].
 *)

Class PreTyping {B : Set} {A : Set} (ty_rel : ctx -> A -> B -> Prop).

(** In DOT for [PreTyping]s we are interested in the following types of
    weakening lemmas:

    1. Adding fresh bindings to the context should not change what terms can be
    typed.

    2. Changing a binding from [x : μ(z : T)] to [x : (open x T)] should not
    change what terms can be typed.

 *)

(** Typing is preserved in extended environments. *)
Class PreTypingWeakenMiddle {A : Set} {B : Set}
      {ty_rel : ctx -> A -> B -> Prop} (PTy : PreTyping ty_rel) :=
  weaken_middle : forall Gamma1 x T' Gamma2 t T,
      ty_rel (Gamma1 & Gamma2) t T ->
      x # Gamma1 ->
      ty_rel (Gamma1 & x ~ T' & Gamma2) t T.

(** Closing a type does not change typing *)
Class PreTypingBndIntroMiddle {A : Set} {B : Set}
      {ty_rel : ctx -> A -> B -> Prop} (PTy : PreTyping ty_rel) :=
  bnd_intro_middle : forall Gamma1 Gamma2 y T1 t T,
    ty_rel (Gamma1 & y ~ open y T1 & Gamma2) t T ->
    ty_rel (Gamma1 & y ~ typ_bnd T1 & Gamma2) t T.

(** In this section we lift weakening *)
Section Weakening.
  Context {B : Set} {A : Set} {ty_rel : ctx -> A -> B -> Prop}.
  Context {PTy : PreTyping ty_rel} {PTyWM : PreTypingWeakenMiddle PTy}.

  Lemma weaken : forall Gamma x T' t T,
      ty_rel Gamma t T ->
      x # Gamma ->
      ty_rel (Gamma & x ~ T') t T.
  Proof.
    introv H. rewrite <- (concat_empty_r Gamma) in H.
    intros. rewrite <- (concat_empty_r (Gamma & x ~ T')).
    auto.
  Qed.

  Lemma weaken_env : forall Gamma1 Gamma2 t T,
      ty_rel Gamma1 t T ->
      (forall x, x \in dom Gamma2 -> x # Gamma1) ->
      ty_rel (Gamma1 & Gamma2) t T.
  Proof.
    intro Gamma1.
    induction Gamma2 as [| Gamma2 x T' IH] using env_ind_rev;
      intros * Hty Hfr.
    - rewrite concat_empty_r; auto.
    - assert (x \in dom (x ~ T' & Gamma2)) as Hdom.
      { simpl_dom; rewrite in_union, in_singleton; auto. }
      rewrite concat_assoc.
      apply weaken_middle; auto.
      apply IH; auto.
      intros x' Hdom'; apply Hfr.
      simpl_dom; rewrite in_union; auto.
  Qed.

  Lemma weaken3 : forall Gamma1 x T' Gamma2 Gamma3 t T,
      ty_rel (Gamma1 & Gamma2 & Gamma3) t T ->
      x # Gamma1 ->
      ty_rel (Gamma1 & x ~ T' & Gamma2 & Gamma3) t T.
  Proof.
    introv.
    rewrite <- (concat_assoc Gamma1), <- (concat_assoc (Gamma1 & _)).
    auto.
  Qed.

  Lemma weaken4 : forall Gamma1 x T' Gamma2 Gamma3 Gamma4 t T,
      ty_rel (Gamma1 & Gamma2 & Gamma3 & Gamma4) t T ->
      x # Gamma1 ->
      ty_rel (Gamma1 & x ~ T' & Gamma2 & Gamma3 & Gamma4) t T.
  Proof.
    introv.
    rewrite <- 2 (concat_assoc Gamma1), <- 2 (concat_assoc (Gamma1 & _)).
    auto.
  Qed.

  Lemma weaken5 : forall Gamma1 x T' Gamma2 Gamma3 Gamma4 Gamma5 t T,
      ty_rel (Gamma1 & Gamma2 & Gamma3 & Gamma4 & Gamma5) t T ->
      x # Gamma1 ->
      ty_rel (Gamma1 & x ~ T' & Gamma2 & Gamma3 & Gamma4 & Gamma5) t T.
  Proof.
    introv.
    rewrite <- 3 (concat_assoc Gamma1), <- 3 (concat_assoc (Gamma1 & _)).
    auto.
  Qed.

  Lemma weaken_fresh_list : forall ys Ts Gamma t T,
      ty_rel Gamma t T ->
      fresh (dom Gamma) (length ys) ys ->
      length ys = length Ts ->
      ty_rel (Gamma & ys ~** Ts) t T.
  Proof.
    induction ys as [| y ys IHys].
    - induction Ts; intro; simpl;
        rewrite ? singles_nil, ? concat_empty_r; auto.
      inversion 3.
    - induction Ts; intros * Hty Hfr; inversion 1.
      rewrite singles_rev_push by auto.
      rewrite ? concat_assoc.
      apply IHys; auto.
      + apply weaken; auto.
      + destruct Hfr.
        rewrite dom_concat, dom_single; auto.
  Qed.

  Lemma weaken_fresh_list_cons : forall x T' ys Ts Gamma t T,
      ty_rel Gamma t T ->
      fresh (dom Gamma) (S (length ys)) (x :: ys) ->
      length ys = length Ts ->
      ty_rel (Gamma & ys ~** Ts & x ~ T') t T.
  Proof.
    intros * ? [? ?] ?.
    apply weaken;
      eauto 3 using weaken_fresh_list, fresh_cons_notin_rev.
  Qed.

  Lemma weaken_ok_middle : forall Gamma1 Gamma2 Gamma3 t T,
      ty_rel (Gamma1 & Gamma3) t T ->
      ok (Gamma1 & Gamma2) ->
      ty_rel (Gamma1 & Gamma2 & Gamma3) t T.
  Proof.
    induction Gamma2 as [| Gamma2 x T IHG2] using env_ind;
      rewrite ? concat_empty_r; auto.
    introv HTy Hok. rewrite concat_assoc in *.
    destruct (ok_push_inv Hok) as [Hok' Hfr].
    eauto.
  Qed.
  Local Hint Resolve weaken_ok_middle : core.

  Lemma weaken_ok : forall Gamma1 Gamma2 t T,
      ty_rel (Gamma1) t T ->
      ok (Gamma1 & Gamma2) ->
      ty_rel (Gamma1 & Gamma2) t T.
  Proof.
    introv H. rewrite <- (concat_empty_r Gamma1) in H.
    intros. rewrite <- (concat_empty_r (Gamma1 & _)).
    auto.
  Qed.

  Lemma weaken_ok4 : forall Gamma1 Gamma2 Gamma3 Gamma4 t T,
      ty_rel (Gamma1 & Gamma3 & Gamma4) t T ->
      ok (Gamma1 & Gamma2) ->
      ty_rel (Gamma1 & Gamma2 & Gamma3 & Gamma4) t T.
  Proof.
    introv H' Hok.
    rewrite <- concat_assoc in H'.
    rewrite <- concat_assoc.
    auto.
  Qed.

  Lemma weaken_ok5 : forall Gamma1 Gamma2 Gamma3 Gamma4 Gamma5 t T,
      ty_rel (Gamma1 & Gamma3 & Gamma4 & Gamma5) t T ->
      ok (Gamma1 & Gamma2) ->
      ty_rel (Gamma1 & Gamma2 & Gamma3 & Gamma4 & Gamma5) t T.
  Proof.
    introv H' Hok.
    rewrite <- 2 concat_assoc in H'.
    rewrite <- 2 concat_assoc.
    auto.
  Qed.
End Weakening.

(** In this section we lift bnd_intro *)
Section BndIntro.
  Context {B : Set} {A : Set} {ty_rel : ctx -> A -> B -> Prop}.
  Context {PTy : PreTyping ty_rel} {PTyWM : PreTypingBndIntroMiddle PTy}.

  Lemma bnd_intro : forall Gamma y T' t T,
      ty_rel (Gamma & y ~ open y T') t T ->
      ty_rel (Gamma & y ~ typ_bnd T') t T.
  Proof.
    introv H; intros.
    rewrite <- (concat_empty_r (Gamma & _)) in H.
    rewrite <- (concat_empty_r (Gamma & _)).
    auto.
  Qed.

  Lemma bnd_intro3 : forall Gamma1 y T' Gamma2 Gamma3 t T,
      ty_rel (Gamma1 & y ~ open y T' & Gamma2 & Gamma3) t T ->
      ty_rel (Gamma1 & y ~ typ_bnd T' & Gamma2 & Gamma3) t T.
  Proof.
    introv H; intros.
    rewrite <- (concat_assoc (Gamma1 & _)) in H.
    rewrite <- (concat_assoc (Gamma1 & _)).
    auto.
  Qed.

  Lemma bnd_intro4 : forall Gamma1 y T' Gamma2 Gamma3 Gamma4 t T,
      ty_rel (Gamma1 & y ~ open y T' & Gamma2 & Gamma3 & Gamma4) t T ->
      ty_rel (Gamma1 & y ~ typ_bnd T' & Gamma2 & Gamma3 & Gamma4) t T.
  Proof.
    introv H; intros.
    rewrite <- 2 (concat_assoc (Gamma1 & _)) in H.
    rewrite <- 2 (concat_assoc (Gamma1 & _)).
    auto.
  Qed.

  Lemma bnd_intro5 : forall Gamma1 y T' Gamma2 Gamma3 Gamma4 Gamma5 t T,
      ty_rel (Gamma1 & y ~ open y T' & Gamma2 & Gamma3 & Gamma4 & Gamma5) t T ->
      ty_rel (Gamma1 & y ~ typ_bnd T' & Gamma2 & Gamma3 & Gamma4 & Gamma5) t T.
  Proof.
    introv H; intros.
    rewrite <- 3 (concat_assoc (Gamma1 & _)) in H.
    rewrite <- 3 (concat_assoc (Gamma1 & _)).
    auto.
  Qed.
End BndIntro.
