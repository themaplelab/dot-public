(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Bool.Bool.

Lemma or_orb_iff_left : forall P Q b1 b2,
    P <-> b1 = true ->
    Q <-> b2 = true ->
    P \/ Q <-> b1 || b2 = true.
Proof.
  intros. destruct H, H0. split; destruct b1, b2; simpl; auto.
  intros. destruct H3; auto.
Qed.

Lemma Is_true_iff_eq_true : forall bl,
    Is_true bl <-> bl = true.
Proof.
  intros; split; auto using Is_true_eq_true, Is_true_eq_left.
Qed.
