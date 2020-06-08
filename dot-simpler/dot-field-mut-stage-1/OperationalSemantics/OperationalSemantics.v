Set Implicit Arguments.

Require Import LibExtra.
Require Import AbstractSyntax HeapUpdate.

(** * Operational Semantics *)

Reserved Notation "t1 ↦ t2" (at level 40, t2 at level 39).

Inductive red : config -> config -> Prop :=
(** [s(x) = nu(T)...{a = t}...]  #<br>#
    [―――――――――――――――――――――――――]  #<br>#
    [(s, x.a) |-> (s, t)      ]  *)
| red_sel : forall x m Sigma t T ds fs,
    binds x (item_obj T (open x ds)) Sigma ->
    defs_has (open x ds) (def_trm m t) ->
    (trm_sel (avar_f x) m; fs ; Sigma)
      ↦ (t; fs ; Sigma)

| red_asn : forall x m Sigma y Sigma' fs,
    heap_update Sigma x m y Sigma' ->
    (trm_asn (avar_f x) m (avar_f y); fs; Sigma)
      ↦ (trm_var (avar_f y); fs; Sigma')

(** [s(x) = lambda(T)t]      #<br>#
    [―――――――――――――――――――――]  #<br>#
    [(s, x y) |-> (s, t^y)]  *)
| red_app : forall f a Sigma T t fs,
    binds f (item_fun T t) Sigma ->
    (trm_app (avar_f f) (avar_f a); fs; Sigma)
      ↦ (open a t; fs; Sigma)

| red_let_lambda : forall T t1 t2 Sigma x fs,
    x # Sigma ->
    (trm_lit (lit_fun T t1) t2 ; fs; Sigma)
      ↦ (open x t2 ; fs; Sigma & x ~ (item_fun T t1))

| red_let_obj : forall T ds t Sigma x fs,
    x # Sigma ->
    x \notin fv ds ->
    (trm_lit (lit_obj T ds) t ; fs; Sigma)
      ↦ (open x t ; fs; Sigma & x ~ (item_obj T (open x ds)))

(** [(s, let y = x in t) |-> (s, t^x)] *)
| red_let_var : forall t Sigma x fs,
    (trm_var (avar_f x); (frame_let t :: fs)%list; Sigma)
      ↦ (open x t; fs; Sigma)

| red_let_sta : forall s t fs Sigma,
    (trm_let s t; fs; Sigma)
      ↦ (s; (frame_let t :: fs)%list; Sigma)

where "t1 ↦ t2" := (red t1 t2).

(** ** Normal forms *)
(** A configuration with a location and an empty stack are considered to be
    answers. *)
Inductive answer: config -> Prop :=
| nf_loc: forall x Sigma, answer (trm_var (avar_f x); nil; Sigma).

Hint Constructors red answer : core.
