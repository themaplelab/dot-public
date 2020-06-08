(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.

(** * Typing Rules *)
Class Typing (A : Set) := typing : ctx -> A -> typ -> Prop.
Notation "G ⊢ t '∶' T" := (typing G t T) (at level 40, t at level 59).
Class DecTyping (A : Set) := dec_typing : ctx -> A -> dec -> Prop.
Notation "G ⊢ t '∶d' T" := (dec_typing G t T) (at level 40, t at level 59).
Reserved Notation "G ⊢ t '<:' T" (at level 40, t at level 59).

(** ** Term typing [G ⊢ t: T] *)
Inductive ty_trm : Typing trm :=

(** [G(x) = T]  #<br>#
    [――――――――]  #<br>#
    [G ⊢ x: T]  *)
| ty_var : forall G x T,
    binds x T G ->
    G ⊢ trm_var (avar_f x) ∶ T

(** [G ⊢ x: forall(S)T] #<br>#
    [G ⊢ z: S]     #<br>#
    [――――――――――――] #<br>#
    [G ⊢ x z: T^z]     *)
| ty_all_elim : forall G x z S T,
    G ⊢ trm_var (avar_f x) ∶ typ_all S T ->
    G ⊢ trm_var (avar_f z) ∶ S ->
    G ⊢ trm_app (avar_f x) (avar_f z) ∶ open z T

(** [G ⊢ x: {a: T}] #<br>#
    [―――――――――――――] #<br>#
    [G ⊢ x.a: T]        *)
| ty_rcd_elim : forall G x a S T,
    G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T) ->
    G ⊢ trm_sel (avar_f x) a ∶ T

| ty_fld_asn : forall G x y a S T,
    G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T) ->
    G ⊢ trm_var (avar_f y) ∶ S ->
    G ⊢ trm_asn (avar_f x) a (avar_f y) ∶ T

(** [G ⊢ t: T]          #<br>#
    [G, x: T ⊢ u^x: U]  #<br>#
    [x fresh]           #<br>#
    [―――――――――――――――――] #<br>#
    [G ⊢ let t in u: U]     *)
| ty_let : forall L G t u T U,
    G ⊢ t ∶ T ->
    (forall x, x \notin L ->
      G & x ~ T ⊢ open x u ∶ U) ->
    G ⊢ trm_let t u ∶ U

| ty_llit : forall L G l u T U,
    G ⊢ l ∶ T ->
    (forall x, x \notin L ->
      G & x ~ T ⊢ open x u ∶ U) ->
    G ⊢ trm_lit l u ∶ U

(** [G ⊢ x: T^x]   #<br>#
    [――――――――――――] #<br>#
    [G ⊢ x: mu(T)]     *)
| ty_rec_intro : forall G x T,
    G ⊢ trm_var (avar_f x) ∶ open x T ->
    G ⊢ trm_var (avar_f x) ∶ typ_bnd T

(** [G ⊢ x: mu(T)] #<br>#
    [――――――――――――] #<br>#
    [G ⊢ x: T^x]   *)
| ty_rec_elim : forall G x T,
    G ⊢ trm_var (avar_f x) ∶ typ_bnd T ->
    G ⊢ trm_var (avar_f x) ∶ open x T

(** [G ⊢ x: T]     #<br>#
    [G ⊢ x: U]     #<br>#
    [――――――――――――] #<br>#
    [G ⊢ x: T /\ U]     *)
| ty_and_intro : forall G x T U,
    G ⊢ trm_var (avar_f x) ∶ T ->
    G ⊢ trm_var (avar_f x) ∶ U ->
    G ⊢ trm_var (avar_f x) ∶ typ_and T U

(** [G ⊢ t: T]   #<br>#
    [G ⊢ T <: U] #<br>#
    [――――――――――] #<br>#
    [G ⊢ t: U]   *)
| ty_sub : forall G (t : trm) T U,
    G ⊢ t ∶ T ->
    G ⊢ T <: U ->
    G ⊢ t ∶ U

with ty_lit : Typing lit :=
(** [G, x: T ⊢ t^x: U^x]     #<br>#
    [x fresh]                #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ lambda(T)t: forall(T)U]      *)
| ty_all_intro : forall L G T t U,
    (forall x, x \notin L ->
      G & x ~ T ⊢ open x t ∶ open x U) ->
    G ⊢ lit_fun T t ∶ typ_all T U

| ty_obj_intro : forall L G T ds,
    (forall x, x \notin L -> G & (x ~ open x T) ⊢ (open x ds) ∶ (open x T)) ->
    G ⊢ lit_obj T ds ∶ typ_bnd T

(** ** Single-definition typing [G ⊢ d: D] *)
with ty_def : DecTyping def :=
(** [G ⊢ {A = T}: {A: T..T}]   *)
| ty_def_typ : forall G A T,
    G ⊢ def_typ A T ∶d dec_typ A T T

(** [G ⊢ t: T]            #<br>#
    [―――――――――――――――――――] #<br>#
    [G ⊢ {a = t}: {a: T}] *)
| ty_def_trm : forall G a t T,
    G ⊢ t ∶ T ->
    G ⊢ def_trm a t ∶d dec_trm a T T

(** ** Multiple-definition typing [G ⊢ ds :: T] *)
with ty_defs : Typing defs :=
(** [G ⊢ d: D]              #<br>#
    [―――――――――――――――――――――] #<br>#
    [G ⊢ d ++ defs_nil : D] *)
| ty_defs_one : forall G d D,
    G ⊢ d ∶d D ->
    G ⊢ defs_cons defs_nil d ∶ typ_rcd D

(** [G ⊢ ds :: T]         #<br>#
    [G ⊢ d: D]            #<br>#
    [d \notin ds]         #<br>#
    [―――――――――――――――――――] #<br>#
    [G ⊢ ds ++ d : T /\ D] *)
| ty_defs_cons : forall G ds d T D,
    G ⊢ ds ∶ T ->
    G ⊢ d ∶d D ->
    defs_hasnt ds (label_of d) ->
    G ⊢ defs_cons ds d ∶ typ_and T (typ_rcd D)

(** ** Subtyping [G ⊢ T <: U] *)
with subtyp : ctx -> typ -> typ -> Prop :=

(** [G ⊢ T <: top] *)
| subtyp_top: forall G T,
    G ⊢ T <: typ_top

(** [G ⊢ bot <: T] *)
| subtyp_bot: forall G T,
    G ⊢ typ_bot <: T

(** [G ⊢ T <: T] *)
| subtyp_refl: forall G T,
    G ⊢ T <: T

(** [G ⊢ S <: T]     #<br>#
    [G ⊢ T <: U]     #<br>#
    [――――――――――]     #<br>#
    [G ⊢ S <: U]         *)
| subtyp_trans: forall G S T U,
    G ⊢ S <: T ->
    G ⊢ T <: U ->
    G ⊢ S <: U

(** [G ⊢ T /\ U <: T] *)
| subtyp_and11: forall G T U,
    G ⊢ typ_and T U <: T

(** [G ⊢ T /\ U <: U] *)
| subtyp_and12: forall G T U,
    G ⊢ typ_and T U <: U

(** [G ⊢ S <: T]       #<br>#
    [G ⊢ S <: U]       #<br>#
    [――――――――――――――]   #<br>#
    [G ⊢ S <: T /\ U]          *)
| subtyp_and2: forall G S T U,
    G ⊢ S <: T ->
    G ⊢ S <: U ->
    G ⊢ S <: typ_and T U

(** [G ⊢ T <: U]           #<br>#
    [――――――――――――――――――――] #<br>#
    [G ⊢ {a: T} <: {a: U}] *)
| subtyp_fld: forall G a T1 T2 U1 U2,
    G ⊢ T1 <: T2 ->
    G ⊢ U1 <: U2 ->
    G ⊢ typ_rcd (dec_trm a T2 U1) <: typ_rcd (dec_trm a T1 U2)

(** [G ⊢ S2 <: S1]                   #<br>#
    [G ⊢ T1 <: T2]                   #<br>#
    [――――――――――――――――――――――――――――――] #<br>#
    [G ⊢ {A: S1..T1} <: {A: S2..T2}]     *)
| subtyp_typ: forall G A S1 T1 S2 T2,
    G ⊢ S2 <: S1 ->
    G ⊢ T1 <: T2 ->
    G ⊢ typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)

(** [G ⊢ x: {A: S..T}] #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢ S <: x.A]     *)
| subtyp_sel2: forall G x A S T,
    G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_typ A S T) ->
    G ⊢ S <: typ_sel (avar_f x) A

(** [G ⊢ x: {A: S..T}] #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢ x.A <: T]     *)
| subtyp_sel1: forall G x A S T,
    G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_typ A S T) ->
    G ⊢ typ_sel (avar_f x) A <: T

(** [G ⊢ S2 <: S1]                #<br>#
    [G, x: S2 ⊢ T1^x <: T2^x]     #<br>#
    [x fresh]                     #<br>#
    [―――――――――――――――――――――――]     #<br>#
    [G ⊢ forall(S1)T1 <: forall(S2)T2]      *)
| subtyp_all: forall L G S1 T1 S2 T2,
    G ⊢ S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 ⊢ open x T1 <: open x T2) ->
    G ⊢ typ_all S1 T1 <: typ_all S2 T2
where "G '⊢' T '<:' U" := (subtyp G T U).
Existing Instances ty_trm ty_def.
Existing Instances ty_lit ty_defs | 1.

Hint Constructors ty_trm ty_lit ty_def ty_defs subtyp : core.
Remove Hints subtyp_trans ty_sub : core.
Hint Resolve subtyp_trans ty_sub | 10 : core.

(** ** Mutual Induction Principles *)

Scheme ts_ty_trm_mut := Induction for ty_trm Sort Prop
with   ts_subtyp     := Induction for subtyp Sort Prop.
Combined Scheme ts_mutind from ts_ty_trm_mut, ts_subtyp.

Scheme rules_trm_mut    := Induction for ty_trm Sort Prop
with   rules_lit_mut    := Induction for ty_lit Sort Prop
with   rules_def_mut    := Induction for ty_def Sort Prop
with   rules_defs_mut   := Induction for ty_defs Sort Prop
with   rules_subtyp     := Induction for subtyp Sort Prop.
Combined Scheme rules_mutind from rules_trm_mut, rules_lit_mut,
rules_def_mut, rules_defs_mut, rules_subtyp.

(** ** Tactics *)

Ltac fresh_constructor_extern :=
  match goal with
  | [ |- _ ⊢ lit_obj _ _ ∶ typ_bnd _ ] =>
    let z := fresh "z" in
    apply_fresh ty_obj_intro as z
  | [ |- _ ⊢ lit_fun _ _ ∶ typ_all _ _ ] =>
    let z := fresh "z" in
    apply_fresh ty_all_intro as z
  | [ |- _ ⊢ trm_let _ _ ∶ _ ] =>
    let z := fresh "z" in
    apply_fresh ty_let as z
  | [ |- _ ⊢ typ_all _ _ <: typ_all _ _ ] =>
    let z := fresh "z" in
    apply_fresh subtyp_all as z
  | [ |- _ ⊢ trm_lit _ _ ∶ _ ] =>
    let z := fresh "z" in
    apply_fresh ty_llit as z
  end.

Hint Extern 4 (_ ⊢ _ ∶ _) => fresh_constructor_extern : core.

Ltac fresh_constructor :=
  fresh_constructor_extern; auto.

(** * Lemmas *)

(** If a variable can be typed in an environment,
    then it is bound in that environment. *)
Lemma typing_implies_bound: forall G x T,
  G ⊢ trm_var (avar_f x) ∶ T ->
  exists S, binds x S G.
Proof.
  introv Ht. remember (trm_var (avar_f x)).
  induction Ht; try congruence;
    match goal with
    | [ H : _ = _ |- _ ] => inversions H
    end; eauto.
Qed.

Lemma var_typing_implies_avar_f: forall G a T,
    G ⊢ trm_var a ∶ T ->
    exists x, a = avar_f x.
Proof.
  intros G a T H.
  remember (trm_var a) as t eqn:Heqt.
  induction H; inversion Heqt; eauto.
Qed.

(** Some simple lemmas for automation *)
Lemma ty_trm_ctx_assoc : forall G1 G2 G3 (t : trm) T,
   G1 & (G2 & G3) ⊢ t ∶ T ->
   G1 & G2 & G3 ⊢ t ∶ T.
Proof.
  intros; rewrite <- concat_assoc; auto.
Qed.
Hint Resolve ty_trm_ctx_assoc | 7 : core.

Lemma ty_lit_ctx_assoc : forall G1 G2 G3 (l : lit) T,
   G1 & (G2 & G3) ⊢ l ∶ T ->
   G1 & G2 & G3 ⊢ l ∶ T.
Proof.
  intros; rewrite <- concat_assoc; auto.
Qed.
Hint Resolve ty_lit_ctx_assoc | 7 : core.

Lemma ty_defs_ctx_assoc : forall G1 G2 G3 (ds : defs) D,
   G1 & (G2 & G3) ⊢ ds ∶ D ->
   G1 & G2 & G3 ⊢ ds ∶ D.
Proof.
  intros; rewrite <- concat_assoc; auto.
Qed.
Hint Resolve ty_defs_ctx_assoc | 7 : core.

Lemma subtyp_ctx_assoc : forall G1 G2 G3 T U,
   G1 & (G2 & G3) ⊢ T <: U ->
   G1 & G2 & G3 ⊢ T <: U.
Proof.
  intros; rewrite <- concat_assoc; auto.
Qed.
Hint Resolve subtyp_ctx_assoc | 7 : core.
