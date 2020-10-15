Set Implicit Arguments.

Require Import LibExtra.
Require Import AbstractSyntax HeapUpdate.

(** * Operational Semantics *)

Reserved Notation "t1 ↦ t2" (at level 40, t2 at level 39).

Inductive red : config -> config -> Prop :=
(** [Sigma(x) = nu(T)...{a = y}...]  #<br>#
    [―――――――――――――――――――――――――]  #<br>#
    [(x.a; Fs; Sigma) |-> (y; Fs; Sigma)      ]  *)
| red_sel : forall x a Sigma y T hds fs,
    binds x (item_obj T hds) Sigma ->
    labels_has hds (heap_def_trm a (Some y)) ->
    (trm_sel (avar_f x) a; fs ; Sigma)
      ↦ (trm_var (avar_f y); fs ; Sigma)

(** [Sigma(x) = nu(T)...{a = _}...]  #<br>#
    [Sigma'[x := nu(T)...{a = y}...]]  #<br>#
    [―――――――――――――――――――――――――]  #<br>#
    [(x.a := y; Fs; Sigma) |-> (y; Fs; Sigma')      ]  *)
| red_asn : forall x a Sigma y Sigma' fs,
    heap_update Sigma x a y Sigma' ->
    (trm_asn (avar_f x) a (avar_f y); fs; Sigma)
      ↦ (trm_var (avar_f y); fs; Sigma')

(** [Sigma(f) = lambda(T)t]  #<br>#
    [―――――――――――――――――――――――――]  #<br>#
    [(f y; Fs; Sigma) |-> (t^y; Fs; Sigma)      ]  *)
| red_app : forall f a Sigma T t fs,
    binds f (item_lit (lit_fun T t)) Sigma ->
    (trm_app (avar_f f) (avar_f a); fs; Sigma)
      ↦ (open a t; fs; Sigma)

(** [x fresh in Sigma]  #<br>#
    [―――――――――――――――――――――――――]  #<br>#
    [(let x = l in t; Fs; Sigma) |-> (t^x; Fs; Sigma[x := l])      ]  *)
| red_let_lit : forall T l t Sigma x fs,
    x # Sigma ->
    (trm_lit T l t ; fs; Sigma)
      ↦ (open x t ; fs; Sigma & x ~ (item_lit l))

(** [x fresh in Sigma]  #<br>#
    [Sigma(k)=kappa(z1: is Ts, ... -> U){ds}t]  #<br>#
    [―――――――――――――――――――――――――]  #<br>#
    [(new k(x1,...); Fs; Sigma) |-> (t^(x,x1,...); return x :: Fs; Sigma[x := nu(x:T^(x1,...))ds^(x,x1,...)])      ]  *)
| red_new : forall Ts is' T ds t Sigma x c ys avs fs,
    x # Sigma ->
    x \notin fv (open_rec_vars 1 ys ds) ->
    binds c (item_lit (lit_con Ts is' T ds t)) Sigma ->
    length ys = length_s Ts ->
    vars_of_avars ys avs ->
    (trm_new (avar_f c) avs; fs; Sigma)
      ↦ ((open_vars (cons x ys) t)
           ; (frame_ret x :: fs)%list
           ; Sigma & x ~ (item_obj
                        (open_rec_vars 1 ys T)
                        (open_vars (cons x ys) (heap_defs_of_defs ds))))

(** [(y; return x :: Fs; Sigma) |-> (x; Fs; Sigma)      ]  *)
| red_return : forall Sigma x y fs,
    (trm_var (avar_f y); (frame_ret x :: fs)%list; Sigma)
      ↦ (trm_var (avar_f x); fs; Sigma)

(** [(x; let y = [] in t :: Fs; Sigma) |-> (t^x; Fs; Sigma)] *)
| red_let_var : forall t Sigma x fs,
    (trm_var (avar_f x); (frame_let t :: fs)%list; Sigma)
      ↦ (open x t; fs; Sigma)

(** [(let y:T = s in t; Fs; Sigma) |-> (s; let y = [] in t :: Fs; Sigma)] *)
| red_let_sta : forall T s t fs Sigma,
    (trm_let T s t; fs; Sigma)
      ↦ (s; (frame_let t :: fs)%list; Sigma)

where "t1 ↦ t2" := (red t1 t2).

(** ** Normal forms *)
(** A configuration with a location and an empty stack are considered to be
    answers: [(x; ε; Sigma)] *)
Inductive answer: config -> Prop :=
| nf_loc: forall x Sigma, answer (trm_var (avar_f x); nil; Sigma).

Hint Constructors red answer : core.
