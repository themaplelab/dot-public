(** remove printing ~ *)

(** This module contains lemmas related to tight typing [G ⊢# t: T] *)

Set Implicit Arguments.

Require Import LibExtra.
Require Import AbstractSyntax Typing.
Require Import GeneralTyping PreciseTyping.

(** * Tight typing [G |-# t: T] *)

Class TightTyping (A : Set) := tight_typing : ctx -> A -> typ -> Prop.
Notation "G ⊢# t '∶' T" := (tight_typing G t T) (at level 40, t at level 59).
Class DecTightTyping (A : Set) := dec_typing : ctx -> A -> dec -> Prop.
Notation "G ⊢# t '∶d' T" := (dec_typing G t T) (at level 40, t at level 59).
Class TightTypings (A : Set) := typings : ctx -> A -> typs -> Prop.
Notation "G ⊢# t '::' T" := (typings G t T) (at level 40, t at level 59).
Reserved Notation "G ⊢# t '<:' T" (at level 40, t at level 59).

(** *** Tight term typing [G ⊢# t: T] *)
(** Tight typing is very similar to general typing, and could be obtained by replacing
    all occurrences of [⊢] with [⊢#], except for the following:
    - in the type selection subtyping rules Sel-<: and <:-Sel ([subtyp_sel1] and [subtyp_sel2]),
      the premise is precise typing of a type declaration with equal bounds;
    - whenever a typing judgement in a premise extends the environment (for example, [ty_all_intro_t]),
      it is typed under general typing [⊢] and not tight typing [⊢#]. *)

Inductive ty_trm_t : TightTyping trm :=

(** [G(x) = T]   #<br>#
    [――――――――――] #<br>#
    [G ⊢# x: T]  *)
| ty_var_t : forall G x T,
    binds x T G ->
    G ⊢# trm_var (avar_f x) ∶ T

(** [G ⊢# x: forall(S)T] #<br>#
    [G ⊢# z: S]     #<br>#
    [――――――――――――――] #<br>#
    [G ⊢# x z: T^z]     *)
| ty_all_elim_t : forall G x z S T,
    G ⊢# trm_var (avar_f x) ∶ typ_all S T ->
    G ⊢# trm_var (avar_f z) ∶ S ->
    G ⊢# trm_app (avar_f x) (avar_f z) ∶ open z T

(** [G ⊢# k : K(is Ts)U]  #<br>#
    [G ⊢# xs :: Ts]                  #<br>#
    [―――――――――――――――――――――――]  #<br>#
    [G ⊢# new k(xs) :: mu(U^Ts)]          *)
| ty_new_t : forall G x avs xs Ts is' T,
    G ⊢# trm_var (avar_f x) ∶ typ_con Ts is' T ->
    G ⊢# avs :: Ts ->
    vars_of_avars xs avs ->
    G ⊢# trm_new (avar_f x) avs ∶ typ_bnd (open_rec_vars 1 xs T)

(** [G ⊢# x: {a: T}] #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢# x.a: T]        *)
| ty_rcd_elim_t : forall G x a S T,
    G ⊢# trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T) ->
    G ⊢# trm_sel (avar_f x) a ∶ T

(** [G ⊢# x: {a: S .. T}] #<br>#
    [G ⊢# y: S] #<br>#
    [―――――――――――――] #<br>#
    [G ⊢# x.a := y : T]        *)
| ty_fld_asn : forall G x y a S T,
    G ⊢# trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T) ->
    G ⊢# trm_var (avar_f y) ∶ S ->
    G ⊢# trm_asn (avar_f x) a (avar_f y) ∶ T

(** [G ⊢# t: T]             #<br>#
    [G, x: T ⊢ u^x: U]       #<br>#
    [x fresh]                #<br>#
    [――――――――――――――――]       #<br>#
    [G ⊢# let t in u: U]        *)
| ty_let_t : forall L G t u T U,
    G ⊢# t ∶ T ->
    (forall x, x \notin L ->
      G & x ~ T ⊢ open x u ∶ U) ->
    G ⊢# trm_let T t u ∶ U

(** [G ⊢ l: T]             #<br>#
    [G, x: T ⊢ u^x: U]       #<br>#
    [x fresh]                #<br>#
    [――――――――――――――――]       #<br>#
    [G ⊢# let l in u: U]        *)
| ty_llit_t : forall L G l u T U,
    G ⊢ l ∶ T ->
    (forall x, x \notin L ->
      G & x ~ T ⊢ open x u ∶ U) ->
    G ⊢# trm_lit T l u ∶ U

(** [G ⊢# x: T^x]   #<br>#
    [――――――――――――――] #<br>#
    [G ⊢# x: mu(T)] *)
| ty_rec_intro_t : forall G x T,
    G ⊢# trm_var (avar_f x) ∶ open x T ->
    G ⊢# trm_var (avar_f x) ∶ typ_bnd T

(** [G ⊢# x: mu(T)] #<br>#
    [――――――――――――――] #<br>#
    [G ⊢# x: T^x]       *)
| ty_rec_elim_t : forall G x T,
    G ⊢# trm_var (avar_f x) ∶ typ_bnd T ->
    G ⊢# trm_var (avar_f x) ∶ open x T

(** [G ⊢# x: T]      #<br>#
    [G ⊢# x: U]      #<br>#
    [―――――――――――――]   #<br>#
    [G ⊢# x: T /\ U]      *)
| ty_and_intro_t : forall G x T U,
    G ⊢# trm_var (avar_f x) ∶ T ->
    G ⊢# trm_var (avar_f x) ∶ U ->
    G ⊢# trm_var (avar_f x) ∶ typ_and T U

(** [G ⊢# t: T]    #<br>#
    [G ⊢# T <: U]  #<br>#
    [―――――――――――――] #<br>#
    [G ⊢# t: U]        *)
| ty_sub_t : forall G (t : trm) T U,
    G ⊢# t ∶ T ->
    G ⊢# T <: U ->
    G ⊢# t ∶ U

(** *** Tight subtyping [G ⊢# T <: U] *)
with subtyp_t : ctx -> typ -> typ -> Prop :=

(** [G ⊢# T <: top] *)
| subtyp_top_t: forall G T,
    G ⊢# T <: typ_top

(** [G ⊢# bot <: T] *)
| subtyp_bot_t: forall G T,
    G ⊢# typ_bot <: T

(** [G ⊢# T <: T] *)
| subtyp_refl_t: forall G T,
    G ⊢# T <: T

(** [G ⊢# S <: T]     #<br>#
    [G ⊢# T <: U]     #<br>#
    [―――――――――――――]    #<br>#
    [G ⊢# S <: U]         *)
| subtyp_trans_t: forall G S T U,
    G ⊢# S <: T ->
    G ⊢# T <: U ->
    G ⊢# S <: U

(** [G ⊢# T /\ U <: T] *)
| subtyp_and11_t: forall G T U,
    G ⊢# typ_and T U <: T

(** [G ⊢# T /\ U <: U] *)
| subtyp_and12_t: forall G T U,
    G ⊢# typ_and T U <: U

(** [G ⊢# S <: T]       #<br>#
    [G ⊢# S <: U]       #<br>#
    [――――――――――――――――]   #<br>#
    [G ⊢# S <: T /\ U]       *)
| subtyp_and2_t: forall G S T U,
    G ⊢# S <: T ->
    G ⊢# S <: U ->
    G ⊢# S <: typ_and T U

(** [G ⊢# T <: U]           #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢# {a: T} <: {a: U}]     *)
| subtyp_fld_t: forall G a T1 T2 U1 U2,
    G ⊢# T1 <: T2 ->
    G ⊢# U1 <: U2 ->
    G ⊢# typ_rcd (dec_trm a T2 U1) <: typ_rcd (dec_trm a T1 U2)

(** [G ⊢# S2 <: S1]                   #<br>#
    [G ⊢# T1 <: T2]                   #<br>#
    [――――――――――――――――――――――――――――――――] #<br>#
    [G ⊢# {A: S1..T1} <: {A: S2..T2}]     *)
| subtyp_typ_t: forall G A S1 T1 S2 T2,
    G ⊢# S2 <: S1 ->
    G ⊢# T1 <: T2 ->
    G ⊢# typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)

(** [G ⊢! x: {A: T..T}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢# T <: x.A]         *)
| subtyp_sel2_t: forall G x A T U,
    G ⊢! x ∶ U ⪼ typ_rcd (dec_typ A T T) ->
    G ⊢# T <: typ_sel (avar_f x) A

(** [G ⊢! x: {A: T..T}] #<br>#
    [――――――――――――――――――] #<br>#
    [G ⊢# x.A <: T]         *)
| subtyp_sel1_t: forall G x A T U,
    G ⊢! x ∶ U ⪼ typ_rcd (dec_typ A T T) ->
    G ⊢# typ_sel (avar_f x) A <: T

(** [G ⊢# S2 <: S1]                #<br>#
    [G, x: S2 ⊢ T1^x <: T2^x]       #<br>#
    [x fresh]                       #<br>#
    [――――――――――――――――――――――――]      #<br>#
    [G ⊢# forall(S1)T1 <: forall(S2)T2]          *)
| subtyp_all_t: forall L G S1 T1 S2 T2,
    G ⊢# S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 ⊢ open x T1 <: open x T2) ->
    G ⊢# typ_all S1 T1 <: typ_all S2 T2
where "G '⊢#' T '<:' U" := (subtyp_t G T U)

with ty_avars_t : TightTypings avars :=
     | typ_avars_nil : forall G,
         G ⊢# nil :: typs_nil

     | typ_avars_cons : forall G x T avs Ts,
         G ⊢# (trm_var (avar_f x)) ∶ T ->
         G ⊢# avs :: Ts ->
         G ⊢# (cons (avar_f x) avs) :: (typs_cons T Ts).

Existing Instances ty_trm_t ty_avars_t.

Hint Constructors ty_trm_t subtyp_t ty_avars_t : core.

Scheme ts_ty_trm_t_mut := Induction for ty_trm_t Sort Prop
with   ts_subtyp_t     := Induction for subtyp_t Sort Prop
with   ts_ty_avars_t     := Induction for ty_avars_t Sort Prop.
Combined Scheme ts_t_mutind from ts_ty_trm_t_mut, ts_subtyp_t, ts_ty_avars_t.
