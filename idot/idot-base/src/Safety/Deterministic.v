(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import AbstractSyntax Typing GeneralTyping.
Require Import HeapUpdate HeapCorrespondence.

(** * Updates are deterministic *)
(** Well typed definitions have deterministic updates *)
Lemma def_update_deterministic_last : forall d a y hds1 hds2,
    defs_update (d :: nil) a y hds1 ->
    defs_update (d :: nil) a y hds2 ->
    hds1 = hds2.
Proof.
  intros * Hup1 Hup2.
  inversion Hup1 as [?hds ?a ?o ?x|?hds ?d ?a ?x ?hds' Hup]; subst.
  - inversion Hup2 as [?hds ?a ?o ?x|?hds ?d ?a ?x ?hds' Hup]; subst; auto.
    inversions Hup; auto.
  - inversions Hup; auto.
Qed.

Lemma typed_def_update_deterministic : forall Gamma hds D a y hds1 hds2,
    Gamma ⊢ hds ∶ D ->
    defs_update hds a y hds1 ->
    defs_update hds a y hds2 ->
    hds1 = hds2.
Proof.
  intros * Hty. gen hds1 hds2.
  induction Hty.
  - eauto using def_update_deterministic_last.
  - inversion 1 as [?hds ?a ?o ?x|?hds ?d ?a ?x ?hds' Hup1]; subst;
      inversion 1 as [?hds ?a ?o ?x|?hds ?d ?a ?x ?hds' Hup2]; subst;
        try solve [auto|exfalso; eauto using defs_update_hasnt_inv].
    pose proof (IHHty _ _ Hup1 Hup2); subst; auto.
Qed.
