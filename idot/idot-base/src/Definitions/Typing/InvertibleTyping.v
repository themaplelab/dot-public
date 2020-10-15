(** remove printing ~ *)

(** This module contains the definition of invertible typing for variables
    ([ty_var_inv]). *)

Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import Coq.Program.Equality.
Require Import AbstractSyntax Typing
        PreciseTyping TightTyping.

(** ** Invertible typing *)

(** The invertible-typing relation describes the possible types that a variable or value
can be typed with in an inert context. For example, if [G] is inert, [G ⊢! x: {a: T}],
and [G ⊢ T <: T'], then [G ⊢## x: {a: T'}].

The purpose of invertible typing is to be easily invertible into a precise typing relation.
To achieve that, invertible typing avoids typing cycles that could result from, for example,
repeated applications of recursion introduction and elimination.
For this case, invertible typing defines only recursion introduction (whereas precise typing
defines only recursion elimination). *)

(** ** Invertible typing of variables [G ⊢## x: T] *)

Reserved Notation "G '⊢##' x '∶' T" (at level 40, x at level 59).

Inductive ty_var_inv : ctx -> var -> typ -> Prop :=

(** [G ⊢! x∶ T]  #<br>#
    [―――――――――――] #<br>#
    [G ⊢## x∶ T]     *)
| ty_precise_inv : forall G x T U,
  G ⊢! x ∶ T ⪼ U ->
  G ⊢## x ∶ U

(** [G ⊢## x∶ {a: T1 .. U1}] #<br>#
    [G ⊢# T2 <: T1]     #<br>#
    [G ⊢# U1 <: U2]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢## x∶ {a: T2 .. U2}]     *)
| ty_dec_trm_inv : forall G x a T1 T2 U1 U2,
  G ⊢## x ∶ typ_rcd (dec_trm a T2 U1) ->
  G ⊢# T1 <: T2 ->
  G ⊢# U1 <: U2 ->
  G ⊢## x ∶ typ_rcd (dec_trm a T1 U2)

(** [G ⊢## x∶ {A: T..U}]   #<br>#
    [G ⊢# T' <: T]         #<br>#
    [G ⊢# U <: U']         #<br>#
    [―――――――――――――――――――――] #<br>#
    [G ⊢## x∶ {A: T'..U'}]     *)
| ty_dec_typ_inv : forall G x A T T' U' U,
  G ⊢## x ∶ typ_rcd (dec_typ A T U) ->
  G ⊢# T' <: T ->
  G ⊢# U <: U' ->
  G ⊢## x ∶ typ_rcd (dec_typ A T' U')

(** [G ⊢## x∶ T^x]   #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢## x∶ mu(T)] *)
| ty_bnd_inv : forall G x T,
  G ⊢## x ∶ open x T ->
  G ⊢## x ∶ typ_bnd T

(** [G ⊢## x∶ forall(S)T]          #<br>#
    [G ⊢# S' <: S]            #<br>#
    [G, y: S' ⊢ T^y <: T'^y]   #<br>#
    [y fresh]                  #<br>#
    [――――――――――――――――――――――]   #<br>#
    [G ⊢## x∶ forall(S')T']            *)
| ty_all_inv : forall L G x S T S' T',
  G ⊢## x ∶ typ_all S T ->
  G ⊢# S' <: S ->
  (forall y, y \notin L ->
   G & y ~ S' ⊢ open y T <: open y T') ->
  G ⊢## x ∶ typ_all S' T'

(** [G ⊢## x ∶ T]     #<br>#
    [G ⊢## x ∶ U]     #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢## x ∶ T /\ U]      *)
| ty_and_inv : forall G x S1 S2,
  G ⊢## x ∶ S1 ->
  G ⊢## x ∶ S2 ->
  G ⊢## x ∶ typ_and S1 S2

(** [G ⊢## x∶ S]        #<br>#
    [G ⊢! y∶ {A: S..S}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢## x∶ y.A           *)
| ty_sel_inv : forall G x y A S U,
  G ⊢## x ∶ S ->
  G ⊢! y ∶ U ⪼ typ_rcd (dec_typ A S S) ->
  G ⊢## x ∶ typ_sel (avar_f y) A

(** [G ⊢## x∶ T]   #<br>#
    [―――――――――――――] #<br>#
    [G ⊢## x∶ top]     *)
| ty_top_inv : forall G x T,
  G ⊢## x ∶ T ->
  G ⊢## x ∶ typ_top
where "G '⊢##' x '∶' T" := (ty_var_inv G x T).

Hint Constructors ty_var_inv : core.
