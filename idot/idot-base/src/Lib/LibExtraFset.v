(** remove printing ~ *)

Set Implicit Arguments.

From TLC Require Import LibFset.

Lemma is_in_union_singleton_l : forall {A} v (E : fset A),
    v \in E \u \{ v}.
Proof.
  intros. rewrite in_union, in_singleton; auto.
Qed.

Lemma is_in_union_singleton_r : forall {A} v (E : fset A),
    v \in \{v} \u E.
Proof.
  intros. rewrite in_union, in_singleton; auto.
Qed.

Lemma in_union_singleton_l : forall {A} v1 v2 (E : fset A),
    v1 \in \{v2} \u E <-> v1 = v2 \/ v1 \in E.
Proof.
  intros. rewrite in_union, in_singleton; split; auto.
Qed.

Lemma in_union_singleton_r : forall {A} v1 v2 (E : fset A),
    v1 \in E \u \{ v2} <-> v1 \in E \/ v1 = v2.
Proof.
  intros. rewrite in_union, in_singleton; split; auto.
Qed.

Lemma member_union_same : forall (A : Type) (s : fset A) (a : A),
    a \in s -> s \u \{a} = s.
Proof with eauto.
  intros * a_in_s.
  apply fset_extens.
  - unfold subset. intros.
    rewrite in_union in H. destruct H...
    rewrite in_singleton in H. subst...
  - apply subset_union_weak_l...
Qed.

Lemma fset_cases : forall {A} (E : fset A),
    E = \{} \/ exists x, x \in E.
Proof.
  intros. pose proof (fset_finite E) as [L Heq].
  destruct L; subst; rewrite ? from_list_nil, ? from_list_cons; auto.
  right; exists a. rewrite ? in_union, ? in_singleton; auto.
Qed.

Lemma fset_empty_remove : forall {A} (E : fset A),
    \{} \- E = \{}.
Proof.
  intros.
  pose proof (fset_cases (\{} \- E)) as [Heq | [eff' Contra]];
    try congruence; exfalso; rewrite in_remove in Contra;
      destruct Contra; eauto using in_empty_inv.
Qed.

Lemma fset_single_neq_remove : forall {A} (v1 v2 : A),
    v1 <> v2 <-> \{v1} \- \{v2} = \{v1}.
Proof.
  intros; split; intros.
  - apply fset_extens; unfold "\c"; intros x Hin.
    + rewrite in_remove in Hin. destruct Hin; auto.
    + rewrite in_singleton in Hin; subst.
      rewrite in_remove, in_singleton, notin_singleton; split; auto.
  - pose proof (in_singleton_self v1) as Hin. rewrite <- H in Hin.
    rewrite in_remove, notin_singleton in Hin. destruct Hin; auto.
Qed.

Lemma fset_remove_same_empty : forall {A} (E : fset A),
    E \- E = \{}.
Proof.
  intros.
  pose proof (fset_cases (E \- E)) as [Heq | [eff' Contra]];
    try congruence; exfalso; rewrite in_remove in Contra;
      destruct Contra; eauto.
Qed.

Lemma fset_notin_remove : forall {A} (E : fset A) x,
    x \notin E ->
    E \- \{ x} = E.
Proof.
  intros.
  apply fset_extens; unfold "\c";
    intros y; rewrite in_remove.
  + intros [?H ?H]; auto.
  + intros ?H; split; auto.
    rewrite notin_singleton.
    intro Contra; apply H; subst; auto.
Qed.

Lemma union_comm_comm_assoc_assoc : forall {A} (E1 E2 E3 : fset A),
    (E1 \u E2) \u E3 = (E1 \u E3) \u E2.
Proof.
  intros.
  rewrite union_comm, union_comm_assoc, union_assoc.
  auto.
Qed.

Lemma from_list_concat : forall {A} (L1 L2 : list A),
    from_list (L1 ++ L2) = from_list L1 \u from_list L2.
Proof.
  induction L1; simpl; intros;
    rewrite ? from_list_nil, ? from_list_cons, ? union_empty_l; auto.
  rewrite <- union_assoc, <- IHL1; auto.
Qed.

Lemma from_list_rev : forall {A} (L : list A),
    from_list L = from_list (List.rev L).
Proof.
  induction L; simpl; auto.
  rewrite from_list_concat, ? from_list_cons, from_list_nil, IHL.
  rewrite ? union_empty_l, ? union_empty_r.
  rewrite union_comm at 1; auto.
Qed.

Lemma from_list_in : forall {A} (L : list A) x,
    x \in from_list L <->
    List.In x L.
Proof.
  induction L; rewrite ? from_list_nil, ? from_list_cons; simpl.
  - intros x. rewrite in_empty; split; auto.
  - intros x. rewrite in_union, in_singleton.
    rewrite IHL.
    split; intros [? | ?]; auto.
Qed.
