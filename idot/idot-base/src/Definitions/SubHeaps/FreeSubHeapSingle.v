(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Effects.
Require Import FreeItems.

(** * Free Subheaps *)
(** [free_sub_heap ℰ Sigma Delta] says that [ℰ] and [Delta] represent a valid free subheap
    of [Sigma].
    Each mapping in [ℰ] must track effects required for a single object, and the
    object must be a free heap item according to [Delta] and [ℰ].
 *)
Definition free_sub_heap (ℰ : eff_ctx) (Sigma : heap) (Delta : init_ctx) :=
  forall x effs,
    (* The next two lines simply say that ℰ only contains effects for a single
       object represented by variable x *)
    binds x effs ℰ ->
    (forall y a, (y,a) \in (from_list effs) -> y = x) /\
    (* For that single variable x, the heap Sigma bounds x to some item itm *)
    exists itm, binds x itm Sigma /\
                (* And this heap item itm is free with relation to x. That is,
                   (by inverting the definitions of free_heap_item)
                   - x is free
                   - ℰ tracks the null fields of x, (i.e. the defs in itm)
                   - If x.a = z for some z then either z is committed
                     according to Delta or it's free but will be assigned according
                     to ℰ. This should be equivalent to pointing to a free object
                     in the same free sub-heap *)
                free_heap_item Delta ℰ x itm.
