(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax PreTyping.

(** * Typeclasses for Typing *)

(** In this module we list out the type classes for general DOT typing and
    subtyping.

    We directly use typing contexts, declarations, and types to define the
    typeclasses rather than using abstract environments and terms because we
    found that it gives better error messages when typeclass resolution fails.

    We use [Gamma ⊢ d ∶d D] (∶d is "\mathratio d") for typing definitions [d] with a declaration [D].
    We use [Gamma ⊢ t ∶ T] (∶ is "\mathratio") for typing terms [t] with a type [T].
    We use [Gamma ⊢ t :: T] for typing list-like terms [t] with a list-like type [Ts].
    We use [Gamma ⊢ T <: U] for for subtyping.

    We use [Gamma ⊢ ds ∶d D] (∶d is "\mathratio d") for typing a list of definitions
    [ds] with a declaration [D]. This typing will be automatically lifted from
    definition typing, so this does not need to be manually implemented.

   Implementations of [DecTyping], [Typing], [Tyings], and [Subtyping] are
   expected to provide implementations of [PreTypingWeakenMiddle] and
   [PreTypingBndIntroMiddle].

   Implementations of [DecTyping] is expected to provide an inpmeletation of
   [DecTypingLabels].
*)

Class DecTyping (A : Set) := dec_typing : ctx -> A -> dec -> Prop.
Notation "Gamma ⊢ d '∶d' D" := (dec_typing Gamma d D) (at level 40, d at level 59).
Class Typing (A : Set) := typing : ctx -> A -> typ -> Prop.
Notation "Gamma ⊢ t '∶' T" := (typing Gamma t T) (at level 40, t at level 59).
Class Typings (A : Set) := typings : ctx -> A -> typs -> Prop.
Notation "Gamma ⊢ t '::' Ts" := (typings Gamma t Ts) (at level 40, t at level 59).
Class Subtyping := subtyping : ctx -> typ -> typ -> Prop.
Notation "Gamma ⊢ T '<:' U" := (subtyping Gamma T U) (at level 40, T at level 59).

(** ** Labels for Definition Typing *)
(** Definitions are typed with a declaration of the same type. *)
Section DecTypingLabels.
  Context {A : Set} `{LabelOf A}.
  Class DecTypingLabels `(DecTyping A) :=
    ty_def_label_eq :
      forall Gamma d D,
        Gamma ⊢ d ∶d D ->
        label_of D = label_of d.
End DecTypingLabels.

(** ** Typing and Subtyping imply Pretyping *)
Section DecPreTyping.
  Context {A : Set} (TyA : DecTyping A).
  Instance DecPreTyping : PreTyping dec_typing := {}.
End DecPreTyping.
Existing Instance DecPreTyping.

Section TyPreTyping.
  Context {A : Set} (TyA : Typing A).
  Instance TyPreTyping : PreTyping typing := {}.
End TyPreTyping.
Existing Instance TyPreTyping.

Section TysPreTyping.
  Context {A : Set} (TysA : Typings A).
  Instance TysPreTyping : PreTyping typings := {}.
End TysPreTyping.

Section SubPreTyping.
  Context {A : Set} {TysA : Subtyping}.
  Instance SubPreTyping : PreTyping subtyping := {}.
End SubPreTyping.
Existing Instance SubPreTyping.

(** * Lemmas about contexts *)
Lemma union_assoc_fun_prop {A : Set} :
  forall (P: env A -> env A -> Prop) (G1 : env A),
  (forall (G2 : env A), P G1 G2) ->
  forall (G2 G3 : env A), P G1 (G2 & G3).
Proof.
  intros. apply H.
Qed.

Lemma union_assoc_prop {A : Set} :
  forall (P: env A -> Prop)
    (G1 G2 G3 : env A),
    P (G1 & (G2 & G3)) ->
    P (G1 & G2 & G3).
Proof.
  intros; rewrite <- concat_assoc; auto.
Qed.

(** * Lemmas about typing *)
Lemma ty_ctx_assoc {A : Set} `{Typing A} : forall G1 G2 G3 t T,
   G1 & (G2 & G3) ⊢ t ∶ T ->
   G1 & G2 & G3 ⊢ t ∶ T.
Proof.
  intros; apply union_assoc_prop; auto.
Qed.
Hint Resolve ty_ctx_assoc | 7 : core.

Lemma tys_ctx_assoc {A : Set} `{Typings A} : forall G1 G2 G3 ts Ts,
   G1 & (G2 & G3) ⊢ ts :: Ts ->
   G1 & G2 & G3 ⊢ ts :: Ts.
Proof.
  intros; apply union_assoc_prop; auto.
Qed.
Hint Resolve tys_ctx_assoc | 7 : core.

Lemma subtyp_ctx_assoc `{Subtyping} : forall G1 G2 G3 T U,
   G1 & (G2 & G3) ⊢ T <: U ->
   G1 & G2 & G3 ⊢ T <: U.
Proof.
  intros; apply union_assoc_prop; auto.
Qed.
Hint Resolve subtyp_ctx_assoc | 7 : core.

(** * DecTyping to Defs *)
Inductive ty_defs {A : Set} `{LabelOf A} `{DecTyping A} : Typing (list A) :=
(** [G ⊢ d: D]              #<br>#
    [―――――――――――――――――――――] #<br>#
    [G ⊢ d ++ defs_nil : D] *)
| ty_defs_one : forall Gamma d D,
    Gamma ⊢ d ∶d D ->
    Gamma ⊢ cons d nil ∶ typ_rcd D

(** [G ⊢ ds :: T]         #<br>#
    [G ⊢ d: D]            #<br>#
    [d \notin ds]         #<br>#
    [―――――――――――――――――――] #<br>#
    [G ⊢ ds ++ d : T /\ D] *)
| ty_defs_cons : forall Gamma ds d T D,
    Gamma ⊢ ds ∶ T ->
    Gamma ⊢ d ∶d D ->
    labels_hasnt ds (label_of d) ->
    Gamma ⊢ cons d ds ∶ typ_and T (typ_rcd D).
Existing Instance ty_defs | 1.
Hint Constructors ty_defs : core.

(** PreTyping lemmas about single definitions imply pretyping lemmas of list of definitions *)
Section DefsWeaken.
  Context {A : Set} {TyA: DecTyping A}
          (TyWM: PreTypingWeakenMiddle (DecPreTyping TyA)).

  Context `{LabelOf A}.

  Instance DefsWeakenMiddle : PreTypingWeakenMiddle (TyPreTyping ty_defs).
  Proof.
    hnf; introv. remember (Gamma1 & Gamma2) as Gamma' eqn:Heq.
    introv H'; induction H'; subst; auto.
  Qed.
End DefsWeaken.
Existing Instances DefsWeakenMiddle.


Section DefsBndIntro.
  Context {A : Set} `{TyA : DecTyping A}
          (TyBIM: PreTypingBndIntroMiddle (DecPreTyping TyA)).

  Context `{LabelOf A}.

  Instance DefsBndIntroMiddle : PreTypingBndIntroMiddle (TyPreTyping ty_defs).
  Proof.
    hnf; introv. remember (Gamma1 & y ~ open y T1 & Gamma2) as Gamma' eqn:Heq.
    introv H'; induction H'; subst; auto.
  Qed.
End DefsBndIntro.
Existing Instances DefsBndIntroMiddle.
