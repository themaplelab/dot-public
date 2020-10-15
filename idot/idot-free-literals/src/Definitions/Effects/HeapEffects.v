(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Effects.

(** * Heap Effects *)
(** [heap_defs_effs] extracts the null fields of a list of definitions. Here [x]
    is the "name" of the object the definitions [hds] belong to. Compared to
    [def_eff], we have an additional case when a field is non-null. *)
Fixpoint heap_defs_effs (x : var) (hds : heap_defs) : effects :=
  match hds with
  | nil                             => nil
  | (heap_def_typ _ _)        :: ds => heap_defs_effs x ds
  | (heap_def_trm l (Some _)) :: ds => heap_defs_effs x ds
  | (heap_def_trm l None)     :: ds => (x,l) :: (heap_defs_effs x ds)
  end%list.

(** ** Simple Lemmas about Heap Effects  *)
Lemma heap_defs_effs_labels_hasnt : forall x a hds,
    labels_hasnt hds (label_trm a) ->
    (x, a) \notin from_list (heap_defs_effs x hds).
Proof.
  induction hds; intros.
  - simpl.  rewrite from_list_nil. auto.
  - apply labels_hasnt_cons_inv in H. destruct_ands.
    destruct a0.
    + simpl in *; auto.
    + destruct o; simpl in *; auto.
      apply notin_union; split; auto.
      intro Contra; apply H.
      rewrite in_singleton in Contra; inversion Contra.
      auto.
Qed.

Lemma heap_defs_effs_var_eq : forall x a y hds,
    (x, a) \in from_list (heap_defs_effs y hds) -> y = x.
Proof.
  intros. induction hds.
  - exfalso; simpl in *; rewrite in_empty in *; auto.
  - destruct a0; simpl in *; auto.
    destruct o; simpl in *; auto.
    rewrite from_list_cons in H.
    rewrite in_union, in_singleton in *.
    destruct H; eauto.
    congruence.
Qed.

Lemma heap_defs_effs_var_eq' : forall x a y hds,
    (x, a) \in from_list (heap_defs_effs y hds) -> x = y.
Proof.
  intros; symmetry; eauto using heap_defs_effs_var_eq.
Qed.
Hint Resolve heap_defs_effs_var_eq heap_defs_effs_var_eq' : core.
