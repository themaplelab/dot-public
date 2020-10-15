(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.

Class CommitTyping (A : Set) :=
  commit_typing : ctx -> init_ctx -> A -> Prop.
(* This says that t has committed type if t only uses variables considered free by
   Delta, which approximates the topmost sub-heap. *)
Notation "Gamma ⸴ Delta '⊢c' t " :=
  (commit_typing Gamma Delta t) (at level 40, Delta at level 39, t at level 59).

Class InitTyping (A : Set) :=
  init_typing : ctx -> init_ctx -> vars -> A -> init_typ -> Prop.
Notation "Gamma ⸴ Delta ⸴ vs '⊢i' t '∶' i" :=
  (init_typing Gamma Delta vs t i)
    (at level 40, Delta at level 39, vs at level 39, t at level 59).
Class InitTypings (A : Set) :=
  init_typings : ctx -> init_ctx -> vars -> A -> inits -> Prop.
Notation "Gamma  ⸴ Delta ⸴ vs '⊢i' t '::' Ts" :=
  (init_typings Gamma Delta vs t Ts)
    (at level 40, Delta at level 39, vs at level 39, t at level 59).

Implicit Types (i : init_typ) (t : trm) (l : lit).

Inductive init_sub : init_typ -> init_typ -> Prop :=
| init_sub_refl : forall i, init_sub i i
| init_sub_trans : forall i j k, init_sub i j -> init_sub j k -> init_sub i k
| init_sub_comm_unspec : init_sub committed unspecified
| init_sub_local_free : init_sub local free
| init_sub_free_unspec : init_sub free unspecified.

(** * Initialization Typing *)
Inductive init_var : init_ctx -> vars -> var -> init_typ -> Prop :=
| init_var_commit : forall Delta vs x,
    binds x committed Delta ->
    init_var Delta vs x committed
| init_var_local : forall Delta vs x,
    x \in vs ->
    binds x local Delta ->
    init_var Delta vs x local
| init_var_free : forall Delta vs x,
    x \in vs ->
    binds x free Delta ->
    init_var Delta vs x free
| init_var_unspec : forall Delta vs x,
    x \in vs ->
    binds x unspecified Delta ->
    init_var Delta vs x unspecified
| init_var_sub : forall Delta vs x i i',
    init_var Delta vs x i' ->
    init_sub i' i ->
    init_var Delta vs x i.

Hint Constructors init_var init_sub : core.
