(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra.
Require Import AbstractSyntax GeneralTyping.

(** * Weakening Lemma *)
(** Weakening states that typing is preserved in extended environments. *)

(** [G1, G3 ⊢ t: T]                    #<br>#
    [ok(G1, G2, G3)]                   #<br>#
    [――――――――――――――――――――]             #<br>#
    [G1, G2, G3 ⊢ t: T] #<br># #<br>#

    and

    [G1, G3 ⊢ d: D]                    #<br>#
    [ok(G1, G2, G3)]                   #<br>#
    [――――――――――――――――――――]             #<br>#
    [G1, G2, G3 ⊢ d: D] #<br># #<br>#

    and

    [G1, G3 ⊢ ds :: T]                 #<br>#
    [ok(G1, G2, G3)]                   #<br>#
    [――――――――――――――――――――]             #<br>#
    [G1, G2, G3 ⊢ ds :: T] #<br># #<br>#

    and

    [G1, G3 ⊢ T <: U]                  #<br>#
    [ok(G1, G2, G3)]                   #<br>#
    [――――――――――――――――――――]             #<br>#
    [G1, G2, G3 ⊢ T <: U] #<br># #<br>#

    The proof is by mutual induction on term typing, definition typing, and subtyping. *)
Lemma weaken_rules:
  (forall G (t : trm) T, G ⊢ t ∶ T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2) ->
    G1 & G2 & G3 ⊢ t ∶ T) /\
  (forall G (l : lit) T, G ⊢ l ∶ T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2) ->
    G1 & G2 & G3 ⊢ l ∶ T) /\
  (forall G d D, G ⊢ d ∶d D -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2) ->
    G1 & G2 & G3 ⊢ d ∶d D) /\
  (forall G (ds : defs) T, G ⊢ ds ∶ T -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2) ->
    G1 & G2 & G3 ⊢ ds ∶ T) /\
  (forall G T U, G ⊢ T <: U -> forall G1 G2 G3,
    G = G1 & G3 ->
    ok (G1 & G2) ->
    G1 & G2 & G3 ⊢ T <: U).
Proof.
  apply rules_mutind; intros; subst;
    auto using binds_weaken; eauto.
Qed.

Ltac weaken_specialize :=
  intros;
  match goal with
  | [ Hok: ok (?G1 & ?G2) |- _ ] =>
    assert (G1 & G2 = G1 & G2 & empty) as EqG by rewrite~ concat_empty_r;
    rewrite EqG; apply~ weaken_rules;
    (rewrite concat_empty_r || rewrite <- EqG); assumption
  end.

(** Weakening lemma specialized to term typing. *)
Lemma weaken_ty_trm: forall G1 G2 (t : trm) T,
    G1 ⊢ t ∶ T ->
    ok (G1 & G2) ->
    G1 & G2 ⊢ t ∶ T.
Proof.
  weaken_specialize.
Qed.

(** Weakening lemma specialized to subtyping. *)
Lemma weaken_subtyp: forall G1 G2 S U,
  G1 ⊢ S <: U ->
  ok (G1 & G2) ->
  G1 & G2 ⊢ S <: U.
Proof.
  weaken_specialize.
Qed.

(** Weakening lemma specialized to definitions. *)
Lemma weaken_ty_defs: forall G1 G2 (ds : defs) T,
  G1 ⊢ ds ∶ T ->
  ok (G1 & G2) ->
  G1 & G2 ⊢ ds ∶ T.
Proof.
  weaken_specialize.
Qed.
