(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.

(** * Updating the Heap *)
Inductive defs_update : heap_defs -> trm_label -> var -> heap_defs -> Prop :=
(* Field a is updated to store s *)
| defs_update_var : forall hds a o x,
    defs_update (cons (heap_def_trm a o) hds)
                a x
                (cons (heap_def_trm a (Some x)) hds)
| defs_update_push : forall hds d a x hds',
    defs_update hds a x hds' ->
    defs_update (cons d hds) a x (cons d hds').

(* In heap s, the field a of x is updated by y to give new heap s' *)
Definition heap_update (Sigma : heap) (x : var) (a : trm_label) (y : var) (Sigma' : heap) :=
  exists T hds hds' Sigma1 Sigma2,
    (Sigma = Sigma1 & x ~ (item_obj T hds) & Sigma2) /\
    (x # Sigma2) /\
    (defs_update hds a y hds') /\
    (Sigma' = Sigma1 & x ~ (item_obj T hds') & Sigma2).

Lemma defs_update_open : forall x hds a y hds',
    defs_update hds a y hds' ->
    forall hds1, hds = (open x hds1) ->
           exists hds1', hds' = (open x hds1').
Proof.
  introv H. induction H; intros.
  - destruct hds1; inversions H.
    exists (cons (heap_def_trm a (Some x0)) hds1).
    reflexivity.
  - destruct hds1; inversion H0.
    pose proof (IHdefs_update _ H3) as [?hds ?].
    subst. exists (h :: hds0)%list; reflexivity.
Qed.

Lemma defs_update_hasnt: forall hds a x hds' l,
    defs_update hds a x hds' ->
    labels_hasnt hds l ->
    labels_hasnt hds' l.
Proof.
  introv H; gen l; induction H; intros.
  - unfold labels_hasnt; simpl.
    inversion H; cases_if.
    auto.
  - unfold labels_hasnt; simpl.
    assert (label_of d <> l).
    { inversion H0. cases_if. auto. }
    cases_if.
    assert (labels_hasnt hds l).
    { inversion H0. cases_if. auto. }
    apply IHdefs_update; auto.
Qed.

Lemma defs_update_hasnt_inv: forall hds a x hds',
    defs_update hds a x hds' ->
    labels_hasnt hds (label_trm a) -> False.
Proof.
  introv H. induction H; intros.
  - inversion H; cases_if; congruence.
  - assert (labels_hasnt hds (label_trm a)).
    { inversion H0; unfold labels_hasnt, get_labeld; cases_if; auto. }
    auto.
Qed.
