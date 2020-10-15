(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Effects Initialization InitLookup.

(** * Narrowing Lemmas for Initialization Lookup *)
(** We have two ways of narrowing the initialization context. Firstly, the
    context can become more committed if a free subheap in promoted to be part
    of the committed subheap. Secondly, a binding can be changed from being
    unspecified to free or committed. The following lemma show that
    initialization typing is preserved under these conditions. *)

Implicit Type (i : init_typ).

Local Hint Constructors init_var init_sub : core.

Lemma init_var_more_committed : forall Delta1 Delta2 vs x i,
    init_var Delta1 vs x i ->
    (forall x, binds x committed Delta1 -> binds x committed Delta2) ->
    (forall x init, x \in vs -> binds x init Delta1 -> binds x init Delta2) ->
    init_var Delta2 vs x i.
Proof.
  induction 1; subst; eauto.
Qed.

Lemma init_var_more_specified : forall Delta1 Delta2 vs x y i i',
    init_var (Delta1 & y ~ unspecified & Delta2) vs x i ->
    y # Delta2 ->
    (i' = free) \/ (i' = committed) ->
    init_var (Delta1 & y ~ i' & Delta2) vs x i.
Proof.
  introv H Hfr Hfc. assert (binds y i' (Delta1 & y ~ i' & Delta2)) by auto.
  remember (Delta1 & y ~ unspecified & Delta2) as Delta' eqn:HeqD.
  induction H; subst; eauto.
  - (* init_var_commit *)
    apply binds_middle_change with (v2:=i') in H; try congruence; eauto.
  - (* init_var_free *)
    apply binds_middle_change with (v2:=i') in H1; try congruence; eauto.
  - (* init_var_unspec *)
    apply binds_middle_inv in H1; destruct_all; subst; eauto.
Qed.
