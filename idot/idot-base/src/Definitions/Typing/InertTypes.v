(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import Coq.Program.Equality.
Require Import AbstractSyntax RecordTypes.

Implicit Type (ds : defs).

(** * Inert types
       A type is inert if it is either a dependent function type, a dependent
       constructor type whose output type's declarations have equal bounds, or a
       recursive type whose type declarations have equal bounds (enforced
       through [record_type]). #<br>#
       For example, the following types are inert:
       - [lambda(x: S)T]
       - [K(){a: T..T}]
       - [mu(x: {a: T..T} /\ {B: U..U})]
       - [mu(x: {C: {A: T..U}..{A: T..U}})]
       And the following types are not inert:
       - [{a: T}]
       - [{B: U..U}]
       - [top]
       - [x.A]
       - [mu(x: {B: S..T})], where [S <> T]. *)
Inductive inert_typ : typ -> Prop :=
  | inert_typ_all : forall S T, inert_typ (typ_all S T)
  | inert_typ_con :
      forall Ts is' T,
        record_type T ->
        inert_typ (typ_con Ts is' T)
  | inert_typ_bnd : forall T,
      record_type T ->
      inert_typ (typ_bnd T).

(** An inert context is a typing context whose range consists only of inert types. *)
Inductive inert : ctx -> Prop :=
  | inert_empty : inert empty
  | inert_all : forall G x T,
      inert G ->
      inert_typ T ->
      x # G ->
      inert (G & x ~ T).

(** In the proof, it is useful to be able to distinguish record types from
    other types. A record type is a concatenation of type declarations with equal
    bounds [{A: T..T}] and field declarations [{a: T}]. *)

Hint Constructors inert_typ inert : core.
