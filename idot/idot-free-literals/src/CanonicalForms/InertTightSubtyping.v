(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import AbstractSyntax Typing.
Require Import GeneralTyping RecordAndInertTypes
        PreciseTyping TightTyping Narrowing.

(** * Super Types of Objects *)
Inductive bnd_sup : ctx -> typ -> typ -> Prop :=
| bnd_sup_top : forall G T,
    bnd_sup G T typ_top
| bnd_sup_and : forall G T T1 T2,
    bnd_sup G T T1 ->
    bnd_sup G T T2 ->
    bnd_sup G T (typ_and T1 T2)
| bnd_sup_sel : forall G T x A U S,
    G ⊢! x ∶ U ⪼ typ_rcd (dec_typ A S S) ->
    bnd_sup G T S ->
    bnd_sup G T (typ_sel (avar_f x) A)
| bnd_sup_rec : forall G T,
    bnd_sup G (typ_bnd T) (typ_bnd T).
Local Hint Constructors bnd_sup : core.


Ltac unique_bind_bounds :=
  match goal with
  | [ Hin : inert ?G,
      H : ?G ⊢! ?x ∶ ?U ⪼ typ_rcd (dec_typ ?A ?S ?S),
      H' : ?G ⊢! ?x ∶ ?U' ⪼ typ_rcd (dec_typ ?A ?S' ?S') |- _ ] =>
    pose proof (x_bound_unique H H'); subst;
    pose proof (pf_inert_unique_tight_bounds Hin H H'); subst
  end.

Local Hint Extern 1 => unique_bind_bounds : core.

Lemma tight_bnd_sup: forall G S T U,
    inert G ->
    G ⊢# T <: U ->
    bnd_sup G (typ_bnd S) T ->
    bnd_sup G (typ_bnd S) U.
Proof.
  introv Hi H.
  induction H; intros;
    match goal with
    | [ H : bnd_sup _ _ _ |- _ ] =>
      try solve [inversions H; auto]
    end; eauto.
Qed.
Local Hint Resolve tight_bnd_sup : core.

(** * Super Types of Functions *)
Inductive all_sup : ctx -> typ -> typ -> Prop :=
| all_sup_top : forall G T,
    all_sup G T typ_top
| all_sup_and : forall G T T1 T2,
    all_sup G T T1 ->
    all_sup G T T2 ->
    all_sup G T (typ_and T1 T2)
| all_sup_sel : forall G T x A U S,
    G ⊢! x ∶ U ⪼ typ_rcd (dec_typ A S S) ->
    all_sup G T S ->
    all_sup G T (typ_sel (avar_f x) A)
| all_sup_all : forall L G S1 T1 S2 T2,
    G ⊢# S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 ⊢ open x T1 <: open x T2) ->
    all_sup G (typ_all S1 T1) (typ_all S2 T2).
Local Hint Constructors all_sup : core.

Lemma all_sup_refl: forall G S T,
    all_sup G (typ_all S T) (typ_all S T).
Proof.
  intros. apply_fresh all_sup_all as z; auto.
Qed.
Local Hint Resolve all_sup_refl : core.

Lemma tight_all_sup: forall G S T U1 U2,
    inert G ->
    G ⊢# U1 <: U2 ->
    all_sup G (typ_all S T) U1 ->
    all_sup G (typ_all S T) U2.
Proof.
  introv Hi H.
  induction H; intros; auto;
    match goal with
    | |- all_sup _ _ (typ_sel (avar_f _) _) =>
      eauto
    | [ H : all_sup _ _ _ |- _ ] =>
      try solve [inversions H; auto]
    end.
  pose proof ((proj32 tight_to_general) _ _ _ H);
    inversions H1; apply_fresh all_sup_all as z.
  - eauto.
  - assert (G & z ~ S2 ⊢ open z T <: open z T1)
      by apply* narrow_subtyping; eauto.
Qed.
Local Hint Resolve tight_all_sup : core.

Lemma inert_tight_lambda_typing : forall G S t U,
    inert G ->
    G ⊢ lit_fun S t ∶ U ->
    exists T, all_sup G (typ_all S T) U.
Proof.
  introv Hi Hty.
  inversions Hty; eauto.
Qed.

Lemma inert_tight_lambda_typing_precise : forall G S t U,
    inert G ->
    G ⊢ lit_fun S t ∶ U ->
    exists T L,
      (forall x, x \notin L -> G & x ~ S ⊢ open x t ∶ open x T) /\
      all_sup G (typ_all S T) U.
Proof.
  introv Hi Hty. inversion Hty; eauto.
Qed.

(** * Super Types of Constructors *)
Inductive con_sup : ctx -> typ -> typ -> Prop :=
| con_sup_top : forall G T,
    con_sup G T typ_top
| con_sup_and : forall G T T1 T2,
    con_sup G T T1 ->
    con_sup G T T2 ->
    con_sup G T (typ_and T1 T2)
| con_sup_sel : forall G T x A U S,
    G ⊢! x ∶ U ⪼ typ_rcd (dec_typ A S S) ->
    con_sup G T S ->
    con_sup G T (typ_sel (avar_f x) A)
| con_sup_refl : forall G Ts is' T,
    con_sup G (typ_con Ts is' T) (typ_con Ts is' T).
Local Hint Constructors con_sup : core.

Lemma tight_con_sup: forall G Ts T is' U1 U2,
    inert G ->
    G ⊢# U1 <: U2 ->
    con_sup G (typ_con Ts is' T) U1 ->
    con_sup G (typ_con Ts is' T) U2.
Proof.
  introv Hi H.
  induction H; intros;
    match goal with
    | [ H : con_sup _ _ _ |- _ ] =>
      try solve [inversions H; auto]
    end; eauto.
Qed.
Local Hint Resolve tight_con_sup : core.

Lemma inert_con_typing : forall G Ts is' T ds t U,
    inert G ->
    G ⊢ lit_con Ts is' T ds t ∶ U ->
    con_sup G (typ_con Ts is' T) U.
Proof.
  introv Hi Hty.
  inversion Hty; eauto.
Qed.

(** * Tight SubTyping Contradictions *)
Lemma inert_tight_subtyping: forall G,
  inert G ->
  (forall T S U, ~ G ⊢# (typ_bnd T) <: (typ_all S U)) /\
  (forall T Ts is' U, ~ G ⊢# (typ_bnd T) <: (typ_con Ts is' U)) /\
  (forall S U T, ~ G ⊢# (typ_all S U) <: (typ_bnd T)) /\
  (forall S U Ts is' T, ~ G ⊢# (typ_all S U) <: (typ_con Ts is' T)) /\
  (forall Ts is' T S U, ~ G ⊢# (typ_con Ts is' T) <: (typ_all S U)) /\
  (forall Ts is' T U, ~ G ⊢# (typ_con is' Ts T) <: (typ_bnd U)).
Proof.
  introv Hi; repeat_split_right; introv H; try
  match goal with
  | [ H : ?G ⊢# (typ_all ?T ?S) <: ?U |- _ ] =>
    assert (Contra: all_sup G (typ_all T S) U) by eauto; inversion Contra
  | [ H : ?G ⊢# (typ_con ?Ts ?is' ?T) <: ?U |- _ ] =>
    assert (Contra: con_sup G (typ_con Ts is' T) U) by eauto; inversion Contra
  | [ H : ?G ⊢# (typ_bnd ?T) <: ?U |- _ ] =>
    assert (Contra: bnd_sup G (typ_bnd T) U) by eauto; inversion Contra
  end.
Qed.
