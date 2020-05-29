(** printing ⊢#    %\vdash_{\#}%    #&vdash;<sub>&#35;</sub>#     *)
(** printing ⊢##   %\vdash_{\#\#}%  #&vdash;<sub>&#35&#35</sub>#  *)
(** printing ⊢##v  %\vdash_{\#\#v}% #&vdash;<sub>&#35&#35v</sub># *)
(** printing ⊢!    %\vdash_!%       #&vdash;<sub>!</sub>#         *)
(** remove printing ~ *)

(** * Tight typing ⊢#] *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import Definitions PreciseTyping.

Reserved Notation "G '⊢#' t ':' T" (at level 40, t at level 59).
Reserved Notation "G '⊢#' T '<:' U" (at level 40, T at level 59).
Reserved Notation "G '⊢#v' v ':' T" (at level 40, v at level 59).

(** Tight typing is very similar to general typing, and could be obtained by replacing
    all occurrences of [⊢] with [⊢#], except for the following:
    - in the type selection subtyping rules Sel-<: and <:-Sel ([subtyp_sel1], [subtyp_sel2])
      the premise is precise typing of a type declaration with equal bounds;
    - in the singleton subtyping rules Sngl-<: and <:-Sngl ([subtyp_sngl_pq], and [subtyp_sngl_qp])
      the premise is precise typing;
    - whenever a typing judgement in a premise extends the environment (for example, [ty_all_intro_t]),
      it is typed under general typing [⊢] and not tight typing [⊢#]. *)

Inductive ty_path_t : ctx -> path -> typ -> Prop :=

(** [G(x) = T]   #<br>#
    [――――――――――] #<br>#
    [G ⊢# x: T]  *)
| ty_var_t : forall G x T,
    binds x T G ->
    G ⊢# pvar x : T

(** [G ⊢# p: {a: T}] #<br>#
    [―――――――――――――]   #<br>#
    [G ⊢# p.a: T]        *)
| ty_new_elim_t : forall G p a T,
    G ⊢# p : typ_rcd {a ⦂ T} ->
    G ⊢# p • a : T

(** [G ⊢# p.a: T]      #<br>#
    [――――――――――――――]   #<br>#
    [G ⊢# p: {a: T}]        *)
| ty_rec_intro_t : forall G p a T,
    G ⊢# p•a : T ->
    G ⊢# p : typ_rcd { a ⦂ T }

(** [G ⊢# p: q.type]  #<br>#
    [G ⊢# q]          #<br>#
    [―――――――――――――――] #<br>#
    [G ⊢# p: T]            *)
| ty_sngl_t : forall G p q T,
    G ⊢# p : {{ q }} ->
    G ⊢# q : T ->
    G ⊢# p : T

(** [G ⊢# p.: T]       #<br>#
    [――――――――――――――]   #<br>#
    [G ⊢# p: {a: T}]        *)
| ty_path_elim_t : forall G p q a T,
    G ⊢# p : {{ q }} ->
    G ⊢# q • a : T ->
    G ⊢# p • a : {{ q•a }}

(** [G ⊢# p: T^p]   #<br>#
    [――――――――――――] #<br>#
    [G ⊢# p: mu(T)]     *)
| ty_rcd_intro_t : forall G p T,
    G ⊢# p : open_typ_p p T ->
    G ⊢# p : μ T

(** [G ⊢# p: mu(T)] #<br>#
    [――――――――――――] #<br>#
    [G ⊢# p: T^p]   *)
| ty_rec_elim_t : forall G p T,
    G ⊢# p : μ T ->
    G ⊢# p : open_typ_p p T

(** [G ⊢# p: T]     #<br>#
    [G ⊢# p: U]     #<br>#
    [――――――――――――] #<br>#
    [G ⊢# p: T /\ U]     *)
| ty_and_intro_t : forall G p T U,
    G ⊢# p : T ->
    G ⊢# p : U ->
    G ⊢# p : T ∧ U

(** [G ⊢# t: T]    #<br>#
    [G ⊢# T <: U]  #<br>#
    [―――――――――――――] #<br>#
    [G ⊢# t: U]        *)
| ty_sub_t : forall G p T U,
    G ⊢# p : T ->
    G ⊢# T <: U ->
    G ⊢# p : U
where "G '⊢#' p ':' T" := (ty_path_t G p T)

(** *** Tight subtyping [G ⊢# T <: U] *)
with subtyp_t : ctx -> typ -> typ -> Prop :=

(** [G ⊢# T <: top] *)
| subtyp_top_t: forall G T,
    G ⊢# T <: ⊤

(** [G ⊢# bot <: T] *)
| subtyp_bot_t: forall G T,
    G ⊢# ⊥ <: T

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
    G ⊢# T ∧ U <: T

(** [G ⊢# T /\ U <: U] *)
| subtyp_and12_t: forall G T U,
    G ⊢# T ∧ U <: U

(** [G ⊢# S <: T]       #<br>#
    [G ⊢# S <: U]       #<br>#
    [――――――――――――――――]   #<br>#
    [G ⊢# S <: T /\ U]       *)
| subtyp_and2_t: forall G S T U,
    G ⊢# S <: T ->
    G ⊢# S <: U ->
    G ⊢# S <: T ∧ U

(** [G ⊢# T <: U]           #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢# {a: T} <: {a: U}]     *)
| subtyp_fld_t: forall G T U a,
    G ⊢# T <: U ->
    G ⊢# typ_rcd {a ⦂ T} <: typ_rcd {a ⦂ U}

(** [G ⊢# S2 <: S1]                   #<br>#
    [G ⊢# T1 <: T2]                   #<br>#
    [――――――――――――――――――――――――――――――――] #<br>#
    [G ⊢# {A: S1..T1} <: {A: S2..T2}]     *)
| subtyp_typ_t: forall G S1 S2 T1 T2 A,
    G ⊢# S2 <: S1 ->
    G ⊢# T1 <: T2 ->
    G ⊢# typ_rcd { A >: S1 <: T1 } <: typ_rcd { A >: S2 <: T2 }

(** [G ⊢!!! p: q.type]                 #<br>#
    [G ⊢!!! q: U]                      #<br>#
    [――――――――――――――――――――――――――――――――] #<br>#
    [G ⊢# T <: [T[q/p,n]]              *)
| subtyp_sngl_pq_t : forall G p q T T' U,
    G ⊢!!! p : {{ q }} ->
    G ⊢!!! q : U ->
    repl_typ p q T T' ->
    G ⊢# T <: T'

(** [G ⊢!!! p: q.type]                 #<br>#
    [G ⊢!!! q: U]                      #<br>#
    [――――――――――――――――――――――――――――――――] #<br>#
    [G ⊢# T <: [T[p/q,n]]              *)
| subtyp_sngl_qp_t : forall G p q T T' U,
    G ⊢!!! p : {{ q }} ->
    G ⊢!!! q : U ->
    repl_typ q p T T' ->
    G ⊢# T <: T'

(** [G ⊢!!! p: {A: T..T}] #<br>#
    [―――――――――――――――――――] #<br>#
    [G ⊢# T <: p.A]         *)
| subtyp_sel2_t: forall G p A T ,
    G ⊢!!! p : typ_rcd { A >: T <: T } ->
    G ⊢# T <: p ↓ A

(** [G ⊢!!! p: {A: T..T}] #<br>#
    [―――――――――――――――――――] #<br>#
    [G ⊢# p.A <: T]         *)
| subtyp_sel1_t: forall G p A T,
    G ⊢!!! p : typ_rcd { A >: T <: T } ->
    G ⊢# p↓A <: T

(** [G ⊢# S2 <: S1]                #<br>#
    [G, x: S2 ⊢ T1^x <: T2^x]       #<br>#
    [x fresh]                       #<br>#
    [――――――――――――――――――――――――]      #<br>#
    [G ⊢# forall(S1)T1 <: forall(S2)T2]          *)
| subtyp_all_t: forall G S1 S2 T1 T2 L,
    G ⊢# S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 ⊢ open_typ x T1 <: open_typ x T2) ->
    G ⊢# ∀(S1) T1 <: ∀(S2) T2
where "G '⊢#' T '<:' U" := (subtyp_t G T U).

Inductive ty_val_t : ctx -> val -> typ -> Prop :=

(** [G, x: T ⊢ t^x: U^x]       #<br>#
    [x fresh]                  #<br>#
    [――――――――――――――――――――――――] #<br>#
    [G ⊢# lambda(T)t: forall(T)U]     *)
| ty_all_intro_t : forall G t T U L,
    (forall x, x \notin L ->
      G & x ~ T ⊢ open_trm x t : open_typ x U) ->
    G ⊢#v (λ(T) t) : ∀(T) U

(** [z; G, z: T^z ⊢ ds^z :: T^z]    #<br>#
    [z fresh]                          #<br>#
    [―――――――――――――――――――――――――――――――]  #<br>#
    [G ⊢# nu(T)ds :: mu(T)]             *)
| ty_new_intro_t : forall G ds T L,
    (forall z, z \notin L ->
      z; nil; G & (z ~ open_typ z T) ⊢ open_defs z ds :: open_typ z T) ->
    G ⊢#v (ν(T) ds) : μ T

(** [G ⊢# t: T]    #<br>#
    [G ⊢# T <: U]  #<br>#
    [―――――――――――――] #<br>#
    [G ⊢# t: U]        *)
| ty_sub_val_t : forall G v T U,
    G ⊢#v v : T ->
    G ⊢# T <: U ->
    G ⊢#v v : U

where "G '⊢#v' v ':' T" := (ty_val_t G v T).

Hint Constructors ty_path_t subtyp_t ty_val_t : core.

Scheme ts_ty_trm_mut_ts  := Induction for ty_path_t    Sort Prop
with   ts_subtyp_ts      := Induction for subtyp_t    Sort Prop.
Combined Scheme ts_mutind_ts from ts_ty_trm_mut_ts, ts_subtyp_ts.

(** Tight typing for paths implies general typing for paths. *)
Lemma tight_to_general:
  (forall G p T,
     G ⊢# p : T ->
     G ⊢ trm_path p : T) /\
  (forall G S U,
     G ⊢# S <: U ->
     G ⊢ S <: U).
Proof.
  apply ts_mutind_ts; intros; subst; eauto using precise_to_general3.
Qed.
