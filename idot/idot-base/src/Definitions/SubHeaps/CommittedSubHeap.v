(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Typing Initialization InitLookupLemmas InitTyping InitWeakening GeneralTyping.

(** * Commited part of the heap *)
(** ** Heap Definitions in the Committed Subheap *)
Inductive committed_heap_def : init_ctx -> heap_def -> Prop :=
(* Type definitions can be part of the committed subheap *)
| committed_heap_def_typ : forall Delta A T,
    committed_heap_def Delta (heap_def_typ A T)

(** Initialized definitions pointing to committed parts of the subheap can be
    part of the committed subheap *)
| committed_heap_def_trm : forall Delta a x,
    binds x committed Delta ->
    committed_heap_def Delta (heap_def_trm a (Some x)).

(** List of definitons in the Committed Subheap *)
Inductive committed_heap_defs : init_ctx -> heap_defs -> Prop :=
| committed_heap_defs_nil : forall Delta,
    committed_heap_defs Delta nil

| committed_heap_defs_cons : forall Delta hd hds,
    committed_heap_defs Delta hds ->
    committed_heap_def Delta hd ->
    committed_heap_defs Delta (cons hd hds).

(** ** Committed Heap Items *)
(** Only literals and objects with committed definitions can be part of the
    committed subheap. *)
Inductive committed_heap_item :
  ctx -> init_ctx -> item -> Prop :=
(** Literals are committed if they're committed according to Gamma and Delta *)
| committed_heap_lit : forall Gamma Delta l,
    Gamma ⸴ Delta ⊢c l ->
    committed_heap_item Gamma Delta (item_lit l)
(** An object is committed when all its definitions are committed *)
| committed_heap_obj : forall Gamma Delta T hds,
    committed_heap_defs Delta hds ->
    committed_heap_item Gamma Delta (item_obj T hds).

(** ** Committed Subheap *)
(** A heap Sigma is well committed with respect to a typing context Gamma and an initialisation context
    Delta provided that the domains match up and all items in Sigma that are marked as committed by
    Delta are indeed committed heap items.
    The objects marked as committed by Delta form the committed subheap. *)
Definition well_committed_heap (Gamma : ctx) (Delta : init_ctx) (Sigma : heap) :=
  dom Gamma = dom Delta /\
  dom Delta = dom Sigma /\
  forall x itm,
    binds x committed Delta ->
    binds x itm Sigma ->
    committed_heap_item Gamma Delta itm.

(** More Committed Initialization Contexts *)
(** When an free subheap is becomes part of the committed subheap, the initialization context becomes more committed. *)
Definition more_committed Delta Delta' :=
  (forall x, binds x committed Delta -> binds x committed Delta').
