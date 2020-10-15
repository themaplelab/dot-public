Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.

(** This module collects some lemmas about substituting in sets of variables. *)

Lemma vars_subst_union : forall x y vs1 vs2,
    ((vs1 \u vs2) /[x -> y]) = (vs1 /[x -> y]) \u (vs2 /[x -> y]).
Proof.
  unfold subst_var, VarsSubstVar.
  intros; apply fset_extens; unfold "\c"; intros z Hin.
  - repeat cases_if;
      rewrite ? in_union, ? in_remove, ? in_union in *;
      destruct_all; auto; try solve [exfalso; auto].
  - repeat cases_if;
      rewrite ? in_union, ? in_remove, ? in_union in *;
      destruct_all; auto; try solve [exfalso; auto].
    + left; split; auto.
      intro Heq. rewrite in_singleton in Heq; subst.
      auto.
    + left; split; auto.
      intro Heq. rewrite in_singleton in Heq; subst.
      auto.
Qed.

Lemma vars_subst_singleton_same : forall x y,
    \{ x} = (\{ y} /[y -> x]).
Proof.
  unfold subst_var, VarsSubstVar.
  intros. cases_if.
  - rewrite fset_remove_same_empty, union_empty_l; auto.
  - exfalso; auto using in_singleton_self.
Qed.

Lemma vars_subst_notin : forall x y vs,
    x \notin vs ->
    (vs /[x -> y]) = vs.
Proof.
  unfold subst_var, VarsSubstVar.
  intros. cases_if; auto.
Qed.

Lemma vars_subst_in1 : forall x y vs,
    x \in vs ->
    y \in (vs /[x -> y]).
Proof.
  unfold subst_var, VarsSubstVar.
  intros; cases_if.
  rewrite in_union; right.
  apply in_singleton_self.
Qed.

Lemma vars_subst_in2 : forall x y z vs,
    z \in vs ->
    z <> x ->
    z \in (vs /[x -> y]).
Proof.
  unfold subst_var, VarsSubstVar.
  intros; cases_if; auto.
  rewrite in_union, in_remove, notin_singleton; auto.
Qed.

Lemma in_remove_singleton_left : forall (z x : var) vs,
  z \in vs ->
  z <> x ->
  z \in vs \- \{ x }.
Proof.
  intros * H1 H2. rewrite in_remove, notin_singleton; auto.
Qed.

Lemma in_remove_singleton_right : forall (z x : var) vs,
  z \in vs \- \{ x } ->
  z \in vs /\ z <> x.
Proof.
  intros * H. rewrite <- notin_singleton, <- in_remove; auto.
Qed.

Lemma vars_subst_in : forall x y z vs,
    z \in vs ->
    (z \[x -> y]) \in (vs /[x -> y]).
Proof.
  intros; cases_if;
    eauto using vars_subst_in1, vars_subst_in2.
Qed.
