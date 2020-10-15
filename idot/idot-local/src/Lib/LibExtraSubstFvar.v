(** remove printing ~ *)

Set Implicit Arguments.

From TLC Require Import LibLN.
Require Import LibExtraEnv.

Notation "z '\[' x '->' y ']'" := (If z = x then y else z) (x at level 69, at level 70).
Definition subst_fvar (x y z: var): var := If z = x then y else z.

Lemma binds_rename_middle : forall {A} (E1 E2 : env A) x y z v v1 v2,
    binds z v (E1 & x ~ v1 & E2) ->
    x # E2 -> y # E1 & E2 ->
    binds (z \[ x -> y]) (If z = x then v2 else v) (E1 & y ~ v2 & E2).
Proof.
  introv Hbi Hfrx Hfry.
  pose proof (binds_middle_inv Hbi) as [? | [[? [? ?]] | [? [? ?]]]];
    cases_if; auto 3.
  assert (z <> y) by (intro; subst; eauto using binds_to_dom).
  auto.
Qed.

Lemma fresh_vars_map : forall x y ys,
    fresh \{ x} (length ys) ys ->
    List.map (subst_fvar x y) ys = ys.
Proof.
  intros. induction ys.
  - auto.
  - simpls. destruct H. f_equal.
    + unfold subst_fvar; cases_if.
      * exfalso. apply H. rewrite in_singleton. auto.
      * auto.
    + apply IHys; auto.
Qed.
