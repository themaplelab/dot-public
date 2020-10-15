(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Effects HeapEffects.
Require Import HeapDefsPointsTo WellPointed.

(** * Free Subheap items *)
(** ** Heap Definitions in Free Subheaps *)
(* If the object with reference [y] has the definitions [hds] and belongs to a
   free subheap represented by [Delta] and [ℰ], the references in [hds] must be
   well-pointed with respect to [Delta] and [ℰ]. *)
Definition free_heap_defs (Delta : init_ctx) (ℰ : eff_ctx)
           (y : var) (hds : heap_defs) :=
  (* y is free in Delta *)
  binds y free Delta /\
  (* ℰ  tracks the null fields of y *)
  binds y (heap_defs_effs y hds)  ℰ /\
  (* For all fields of y of the form a = x (a field name), x is
     well pointed: x is either committed according to Delta or
     x is some item in the effects context ℰ that's free *)
  forall x, (x \in heap_defs_points_to hds) ->
       well_pointed Delta ℰ x.

(** ** Heap Items in Free Subheaps *)
Inductive free_heap_item : init_ctx -> eff_ctx -> var -> item -> Prop :=
(** A item [y] that bounds to an object with type [T] and heap definitions [hds]
    is free if the [hds] are free. *)
| free_heap_obj : forall Delta ℰ y T hds,
    free_heap_defs Delta ℰ y hds ->
    free_heap_item Delta ℰ y (item_obj T hds).
Hint Constructors free_heap_item : core.
