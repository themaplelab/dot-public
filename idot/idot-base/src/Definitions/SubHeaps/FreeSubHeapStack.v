(** remove printing ~ *)
Set Implicit Arguments.

(** This module defines stacks of free subheaps *)

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Effects CommittedSubHeap FreeSubHeapSingle.

(** * Unions of Domains of Map Stacks *)
(** Use the following definitions to ensure that the free subheaps are
disjoint *)
Definition all_notin {A} (xs ys : fset A) :=
  forall x, x \in xs -> x \notin ys.

Fixpoint list_dom_union {A} (Es : list (env A)) :=
  match Es with
  | nil => \{}
  | (E :: Es)%list => dom E \u list_dom_union Es
  end.

(** *** Freshness lemmas *)
Lemma all_notin_nil : forall {A} xs,
  all_notin xs (list_dom_union (A:=A) nil).
Proof.
  unfold all_notin, list_dom_union.
  intros. intro Contra. rewrite in_empty in Contra.
  auto.
Qed.

Lemma in_cons_list_dom_union : forall {A} x (E : env A) Es,
    x \in dom E \/ x \in (list_dom_union Es) <->
    x \in (list_dom_union (E :: Es)).
Proof.
  intros. split; simpl; rewrite in_union; auto.
Qed.

Lemma notin_cons_list_dom_union : forall {A} x (E : env A) Es,
    x \notin (list_dom_union (E :: Es)) <->
    x \notin dom E /\ x \notin (list_dom_union Es).
Proof.
  unfold notin; intros. split; intros.
  - rewrite <- in_cons_list_dom_union in H; auto.
  - rewrite <- in_cons_list_dom_union.
    destruct H; intro Contra; destruct Contra; auto.
Qed.

Lemma all_notin_single : forall {A} x (v : A) (E : env A) Es,
  x # E ->
  x \notin (list_dom_union Es) ->
  all_notin (dom (x ~ v)) (list_dom_union (E :: Es)).
Proof.
  intros. unfold all_notin; intros x' Heq.
  rewrite dom_single, in_singleton in Heq; subst.
  intro Contra. rewrite <- in_cons_list_dom_union in Contra.
  destruct Contra; auto.
Qed.

Lemma all_notin_fresh : forall {A} x (v : A) (E : env A) (Es : list (env A)),
    binds x v E ->
    all_notin (dom E) (list_dom_union Es) ->
    x \notin (list_dom_union Es).
Proof.
  unfold all_notin; introv Hbi Hni.
  apply Hni. apply (binds_to_dom Hbi).
Qed.

Lemma all_notin_inv : forall {A} (xs ys : fset A) y,
    all_notin xs ys ->
    y \in ys ->
    y \notin xs.
Proof.
  unfold all_notin. intros. intro Contra.
  apply H in Contra; eauto.
Qed.

(** * Stacks of Free Subheaps *)
(* The effect context for a free subheap indicate which fields should be
   assigned in the sub-heaps *)
(** [free_sub_heaps Gamma Delta Sigma ℰs] says that
    1. The bindings that are commited according to [Delta] represent the committed
       subheap.
    2. The effects contexts in the stack ℰs all have disjoint domains.
    3. Each ℰ in the stack ℰs represents a single free subheap.
 *)
Inductive free_sub_heaps :
  ctx -> init_ctx -> heap -> list eff_ctx -> Prop :=
(** When building up a stack of free subheaps, we start with a comitted subheap
    and an empty stack of free_subhaps, and define free subheaps on top of it. *)
| free_sub_heaps_nil : forall Gamma Delta Sigma,
    well_committed_heap Gamma Delta Sigma ->
    free_sub_heaps Gamma Delta Sigma nil
(** Given an existing stack of free subheaps, we can extend it with another free
sub heap if the new subheap is disjoint for the subheaps in the stack. *)
| free_sub_heaps_cons : forall Gamma Delta Sigma ℰ ℰs,
    all_notin (dom ℰ) (list_dom_union ℰs) ->
    free_sub_heap ℰ Sigma Delta ->
    free_sub_heaps Gamma Delta Sigma ℰs ->
    free_sub_heaps Gamma Delta Sigma (ℰ :: ℰs).
