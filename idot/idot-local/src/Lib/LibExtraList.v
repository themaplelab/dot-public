(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Lists.List.
From TLC Require Import LibAxioms.
From TLC Require LibList.

Lemma length_eq_implies_rev_length_eq : forall A B (l1 : list A) (l2 : list B),
    length l1 = length l2 ->
    length (List.rev l1) = length (List.rev l2).
Proof.
  intros. rewrite ? List.rev_length. auto.
Qed.

Lemma rev_length_eq_implies_length_eq : forall A B (l1 : list A) (l2 : list B),
    length (List.rev l1) = length (List.rev l2) ->
    length l1 = length l2.
Proof.
  intros. rewrite ? List.rev_length in *. auto.
Qed.
Hint Resolve length_eq_implies_rev_length_eq : core.

Lemma liblist_length :
  LibList.length = length.
Proof.
  apply fun_ext_dep. intros A.
  apply fun_ext_dep. intros xs.
  induction xs as [ | x xs IHxs].
  - unfold LibList.length. simpl. auto.
  - simpl. rewrite <- IHxs. unfold LibList.length. auto.
Qed.

Lemma liblist_app : LibList.app = app.
Proof.
  apply fun_ext_dep. intros A.
  apply fun_ext_dep. intros xs.
  induction xs as [ | x xs IHxs].
  - reflexivity.
  - apply fun_ext_dep. intros ys.
    simpl. rewrite <- IHxs.
    reflexivity.
Qed.

Lemma liblist_rev :
  LibList.rev = List.rev.
Proof.
  apply fun_ext_dep. intros A.
  apply fun_ext_dep. intros xs.
  induction xs as [ | x xs IHxs].
  - reflexivity.
  - simpl. rewrite <- IHxs.
    rewrite LibList.rev_cons. rewrite liblist_app.
    reflexivity.
Qed.

Lemma liblist_fold_right: forall A B,
    @LibList.fold_right B A = @List.fold_right A B.
Proof.
  intros.
  apply fun_ext_dep. intros f.
  apply fun_ext_dep. intros acc.
  apply fun_ext_dep. intros xs.
  induction xs as [ | x xs IHxs].
  - reflexivity.
  - simpl. rewrite <- IHxs.
    reflexivity.
Qed.

Lemma liblist_map : LibList.map = List.map.
Proof.
  apply fun_ext_dep. intros A.
  apply fun_ext_dep. intros B.
  apply fun_ext_dep. intros f.
  apply fun_ext_dep. intros xs.
  induction xs as [ | x xs IHxs].
  - reflexivity.
  - simpl. rewrite <- IHxs.
    reflexivity.
Qed.
