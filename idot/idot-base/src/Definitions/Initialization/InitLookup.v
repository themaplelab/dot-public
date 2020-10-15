(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Effects Initialization.

(** This modules contains the initiailaization subtyping relation and the
initialization lookup relation. *)

Implicit Type (i : init_typ).

(** * Initialization Subtyping *)
Inductive init_sub : init_typ -> init_typ -> Prop :=
| init_sub_refl : forall i, init_sub i i
| init_sub_comm_unspec : init_sub committed unspecified
| init_sub_free_unspec : init_sub free unspecified.

(** Initialization Subtyping is transitive *)
Lemma init_sub_trans : forall i1 i2 i3,
    init_sub i1 i2 ->
    init_sub i2 i3 ->
    init_sub i1 i3.
Proof.
  induction 1; auto.
  - remember unspecified as i; induction 1;
      subst; try congruence; auto using init_sub_comm_unspec.
  - remember unspecified as i; induction 1;
      subst; try congruence; auto using init_sub_free_unspec.
Qed.


(** * Initialization Lookup *)
(** The following relation looks up the initiailaization type of variables in an
    initialization context, but takes subtyping into account.
    [init_var Delta vs x i] says that [x] has the initialization type [i] in the
    restricted initialization context [Delta | vs ^ free]. [Delta | vs ^ free] is the
    restriction of [Delta] that contains all committed variables from [Delta], but only
    the [free] and [unclassified] variables that are also in [vs]. *)
Inductive init_var : init_ctx -> vars -> var -> init_typ -> Prop :=
(** [Delta (x) = committed ]  #<br>#
    [――――――――]  #<br>#
    [(Delta | vs ^ free) (x) = committed ]  #<br># *)
| init_var_commit : forall Delta vs x,
    binds x committed Delta ->
    init_var Delta vs x committed
(** [Delta (x) = free ]  #<br>#
    [ x ∈ vs ]  #<br>#
    [――――――――]  #<br>#
    [(Delta | vs ^ free) (x) = free ]  #<br># *)
| init_var_free : forall Delta vs x,
    x \in vs ->
    binds x free Delta ->
    init_var Delta vs x free
(** [Delta (x) = unspecified ]  #<br>#
    [ x ∈ vs ]  #<br>#
    [――――――――]  #<br>#
    [(Delta | vs ^ free) (x) = unspecified ]  #<br># *)
| init_var_unspec : forall Delta vs x,
    x \in vs ->
    binds x unspecified Delta ->
    init_var Delta vs x unspecified
(** [(Delta | vs ^ free) (x) = i' ]  #<br>#
    [ i' <: i ]  #<br>#
    [――――――――]  #<br>#
    [(Delta | vs ^ free) (x) = i ]  #<br># *)
| init_var_sub : forall Delta vs x i i',
    init_var Delta vs x i' ->
    init_sub i' i ->
    init_var Delta vs x i.
