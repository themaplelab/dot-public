(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Effects.

(** * Heap Definitions Points To *)
(** [heap_defs_points_to] extracts all the referenses in the non-null fields of
    [hds]. This is, in a sense, a dual to [heap_defs_effs]. *)
Fixpoint heap_defs_points_to (hds : heap_defs) :=
  match hds with
  | nil => \{}
  | (heap_def_typ _ _) :: ds => heap_defs_points_to ds
  | (heap_def_trm l (Some x)) :: ds => \{ x} \u heap_defs_points_to ds
  | (heap_def_trm l None) :: ds => heap_defs_points_to ds
  end%list.

Lemma heap_defs_of_defs_points_to_empty : forall ds,
    (heap_defs_points_to (heap_defs_of_defs ds)) = \{}.
Proof.
  induction ds as [| d ds IHds];
    try destruct d; simpl; auto.
Qed.
