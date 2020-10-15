(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Effects Initialization InitLookup.

Implicit Type (i : init_typ).

Local Hint Constructors init_var init_sub : core.

(** This module contains some simple lemmas about looking up initialization in
    restricted initialization contexts. *)

Lemma init_var_binds_in_init_var : forall Delta x vs i,
    binds x i Delta ->
    x \in vs ->
    init_var Delta vs x i.
Proof.
  induction i; auto.
Qed.


Lemma init_var_middle_init_var : forall Delta1 Delta2 x vs i,
    x # Delta2 ->
    x \in vs ->
    init_var (Delta1 & x ~ i & Delta2) vs x i.
Proof.
  eauto using init_var_binds_in_init_var.
Qed.
