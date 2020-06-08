(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import AbstractSyntax GeneralTyping.
Require Import Coq.Program.Equality.

(** * Subenvironments [G1 ⪯ G2] *)
(** [G1] is a subenvironment of [G2], denoted [G1 ⪯ G2],
    if [dom(G1) = dom(G2)] and for each [x],
    [G1 ⊢ G1(x) <: G2(x)]. *)
Reserved Notation "G1 ⪯ G2" (at level 35).

Inductive subenv: ctx -> ctx -> Prop :=
| subenv_empty : empty ⪯ empty
| subenv_grow: forall G G' x T T',
    G ⪯ G' ->
    ok (G & x ~ T) ->
    G ⊢ T <: T' ->
    G & x ~ T ⪯ G' & x ~ T'
where "G1 ⪯ G2" := (subenv G1 G2).

Local Hint Constructors subenv : core.

(** If [ok G], then [G ⪯ G].
    Note: [ok(G)] means that [G]'s domain consists of distinct variables.
    [ok] is defined in [TLC.LibEnv.v] *)
Lemma subenv_refl : forall G, ok G -> G ⪯ G.
Proof.
  intros G H. induction H; auto.
Qed.
Hint Resolve subenv_refl : core.


Lemma subenv_concat : forall G1 G2 G3,
    G1 ⪯ G2 ->
    ok (G1 & G3) -> ok (G2 & G3) ->
    (G1 & G3) ⪯ (G2 & G3).
Proof.
  intros. induction G3 using env_ind; rewrite ?concat_empty_r, ?concat_assoc in *; auto.
Qed.
Hint Resolve subenv_concat : core.

Lemma subenv_concat2 : forall G1 G2 G3 G4,
    G1 ⪯ G2 ->
    ok (G1 & G3 & G4) -> ok (G2 & G3 & G4) ->
    (G1 & G3 & G4) ⪯ (G2 & G3 & G4).
Proof.
  auto using subenv_concat.
Qed.
Hint Resolve subenv_concat2 : core.

(** [G ⊢ S <: U]                      #<br>#
    [ok(G, x: S)] (see [subenv_push]) #<br>#
    [――――――――――――――――――――――――――――――――――]  #<br>#
    [G', x: T subG G, x: T] *)
Lemma subenv_last: forall G x S U,
  G ⊢ S <: U ->
  ok (G & x ~ S) ->
  (G & x ~ S) ⪯ (G & x ~ U).
Proof. auto. Qed.
Hint Resolve subenv_last : core.

Lemma subenv_ok_fresh : forall G G',
    G ⪯ G' ->
    ok G' /\ (forall x, x # G -> x # G').
Proof.
  introv H.
  induction H;
    destruct_all;
    match goal with
    | [H : ok (?G & ?x ~ _) |- _] =>
      pose proof (ok_push_inv H0) as [? ?]; split; auto
    | _ => split; auto
    end.
Qed.

Lemma subenv_ok_l : forall G1 G2,
    G1 ⪯ G2 -> ok G1.
Proof.
  introv H. induction H; auto.
Qed.

Lemma subenv_ok_r: forall G1 G2,
    G1 ⪯ G2 -> ok G2.
Proof.
  apply subenv_ok_fresh.
Qed.

Hint Extern 1 (ok _) =>
match goal with
| [ H : ?G1 ⪯ ?G2 |- ok ?G1 ] => apply (subenv_ok_l H)
| [ H : ?G1 ⪯ ?G2 |- ok ?G2 ] => apply (subenv_ok_r H)
end : core.
