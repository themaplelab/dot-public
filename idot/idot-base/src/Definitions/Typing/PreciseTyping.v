(** remove printing ~ *)

(** This module reasons about the precise types of variables in inert contexts. *)

Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import Coq.Program.Equality.
Require Import AbstractSyntax.

(** * Precise Typing

    Precise typing is used to reason about the types of variables.
    Precise typing does not "modify" a variable's type through subtyping.
    We start out with a type [T=G(x)] (the type to which the variable is
    bound in [G]). Then we use precise typing to additionally deconstruct [T]
    by using recursion elimination and intersection elimination. #<br>#
    For example, if [G(x)=mu(x: {a: T} /\ {B: S..U})], then we can derive the following
    precise types for [x]:               #<br>#
    [G ⊢! x: mu(x: {a: T} /\ {B: S..U})] #<br>#
    [G ⊢! x: {a: T} /\ {B: S..U}]        #<br>#
    [G ⊢! x: {a: T}]                    #<br>#
    [G ⊢! x: {B: S..U}].                *)

Opaque open_rec fv.


(** * Precise Flow *)
(** We use the precise flow relation to reason about the relations between
    the precise type of a variable [G ⊢! x: T] and the type that the variable
    is bound to in the context [G(x)=T'].#<br>#
    If [G(x) = T], the [precise_flow] relation describes all the types [U] that [x] can
    derive through precise typing ([⊢!]).
    If [precise_flow x G T U], denoted as [G ⊢ x: T ⪼ U],
    then [G(x) = T] and [G ⊢! x: U].   #<br>#
    For example, if [G(x) = mu(x: {a: T} /\ {B: S..U})], then we can derive the following
    precise flows for [x]:                                                  #<br>#
    [G ⊢! x: mu(x: {a: T} /\ {B: S..U}) ⪼ mu(x: {a: T} /\ {B: S..U}]         #<br>#
    [G ⊢! x: mu(x: {a: T} /\ {B: S..U}) ⪼ {a: T} /\ {B: S..U}]               #<br>#
    [G ⊢! x: mu(x: {a: T} /\ {B: S..U}) ⪼ {a: T}]                           #<br>#
    [G ⊢! x: mu(x: {a: T} /\ {B: S..U}) ⪼ {B: S..U}]. *)

Reserved Notation "G '⊢!' x '∶' T '⪼' U" (at level 40, x at level 59).

Inductive precise_flow : var -> ctx -> typ -> typ -> Prop :=

(** [G(x) = T]       #<br>#
    [――――――――――――――] #<br>#
    [G ⊢! x: T ⪼ T] *)
  | pf_bind : forall x G T,
      binds x T G ->
      G ⊢! x ∶ T ⪼ T

(** [G ⊢! x: T ⪼ mu(U)] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢! x: T ⪼ U^x]       *)
  | pf_open : forall x G T U,
      G ⊢! x ∶ T ⪼ typ_bnd U ->
      G ⊢! x ∶ T ⪼ open x U

(** [G ⊢! x: T ⪼ U1 /\ U2]   #<br>#
    [――――――――――――――――――――]   #<br>#
    [G ⊢! x: T ⪼ U1]        *)
  | pf_and1 : forall x G T U1 U2,
      G ⊢! x ∶ T ⪼ typ_and U1 U2 ->
      G ⊢! x ∶ T ⪼ U1

(** [G ⊢! x: T ⪼ U1 /\ U2]   #<br>#
    [――――――――――――――――――――]   #<br>#
    [G ⊢! x: T ⪼ U2]        *)
  | pf_and2 : forall x G T U1 U2,
      G ⊢! x ∶ T ⪼ typ_and U1 U2 ->
      G ⊢! x ∶ T ⪼ U2

where "G '⊢!' x '∶' T '⪼' U" := (precise_flow x G T U).

Hint Constructors precise_flow : core.
