(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import PreTyping Typing GeneralTyping.
Require Import Effects InitVarDefs.

Implicit Types (i : init_typ) (t : trm) (l : lit).

(** * Initialization System *)
(* To allocate a new free subheap, the arguments to a constructor must not be free. *)
Inductive all_comm_unspec : inits -> Prop :=
| all_comm_unspec_nil : all_comm_unspec nil
| all_comm_unspec_cons : forall i is',
    (i = committed) \/ (i = unspecified) ->
    all_comm_unspec is' ->
    all_comm_unspec (cons i is').
Hint Constructors all_comm_unspec : core.

(** ** Committed Terms [Gamma; Delta ⊢c t] *)
Inductive well_committed : CommitTyping trm :=
(** [ Delta(x) = committed ] #<br>#
    [――――――――――――] #<br>#
    [ Gamma; Delta ⊢c x ]     *)
| commit_var : forall Gamma Delta x,
    binds x committed Delta ->
    Gamma ⸴ Delta ⊢c (trm_var (avar_f x))

(** [ Gamma; Delta ⊢c f ]     #<br>#
    [ Gamma; Delta ⊢c x ]     #<br>#
    [――――――――――――] #<br>#
    [ Gamma; Delta ⊢c f x ]     *)
| commit_all_elim : forall Gamma Delta x z,
    Gamma ⸴ Delta ⊢c trm_var (avar_f x) ->
    Gamma ⸴ Delta ⊢c trm_var (avar_f z) ->
    Gamma ⸴ Delta ⊢c trm_app (avar_f x) (avar_f z)

(** [ Gamma; Delta ⊢c k ]     #<br>#
    [ Gamma ⊢ k : K(i1 T1,...)T ]     #<br>#
    [ i1,... committed or unspecified ]     #<br>#
    [ Gamma; Delta ⊢c x1,... ]     #<br>#
    [――――――――――――] #<br>#
    [ Gamma; Delta ⊢c new k(x1,...) ]     *)
| commit_new : forall Gamma Delta x avs Ts is' T,
    Gamma ⸴ Delta ⊢c trm_var (avar_f x) ->
    Gamma ⊢ trm_var (avar_f x) ∶ typ_con Ts is' T ->
    all_comm_unspec is' ->
    Gamma ⸴ Delta ⊢c avs ->
    Gamma ⸴ Delta ⊢c trm_new (avar_f x) avs

(** [ Gamma; Delta ⊢c x ]     #<br>#
    [――――――――――――] #<br>#
    [ Gamma; Delta ⊢c x.a ]     *)
| commit_rcd_elim : forall Gamma Delta x a,
    Gamma ⸴ Delta ⊢c trm_var (avar_f x) ->
    Gamma ⸴ Delta ⊢c trm_sel (avar_f x) a

(** [ Gamma; Delta ⊢c x ]     #<br>#
    [ Gamma; Delta ⊢c y ]     #<br>#
    [――――――――――――] #<br>#
    [ Gamma; Delta ⊢c x.a := y ]     *)
| commit_fld_asn : forall Gamma Delta x i y a,
    Gamma ⸴ Delta ⊢c trm_var (avar_f x) ->
    Gamma ⸴ Delta ⊢c trm_var (avar_f y) ->
    Gamma ⸴ Delta ⊢c trm_asn (avar_f x) a (avar_f y)

(** [ Gamma; Delta ⊢c t ]     #<br>#
    [ Gamma,x:T; Delta,x:committed ⊢c u ]     #<br>#
    [ x fresh ]     #<br>#
    [――――――――――――] #<br>#
    [ Gamma; Delta ⊢c let (x:T) = t in u ]     *)
| commit_let : forall L Gamma Delta t u T,
    Gamma ⸴ Delta ⊢c t -> (* non free writing *)
    (forall x, x \notin L -> Gamma & x ~ T ⸴ Delta & x ~ committed ⊢c open x u) ->
    Gamma ⸴ Delta ⊢c trm_let T t u

(** [ Gamma; Delta ⊢c l ]     #<br>#
    [ Gamma,x:T; Delta,x:committed ⊢c u ]     #<br>#
    [ x fresh ]     #<br>#
    [――――――――――――] #<br>#
    [ Gamma; Delta ⊢c let (x:T) = l in u ]     *)
| commit_llit : forall L Gamma Delta l u T,
    Gamma ⸴ Delta ⊢c l ->
    (forall x, x \notin L -> Gamma & x ~ T ⸴ Delta & x ~ committed ⊢c open x u) ->
    Gamma ⸴ Delta ⊢c trm_lit T l u

(** *** Committed List of Variables [Gamma; Delta ⊢c x1,... ] *)
with well_committed_avars : CommitTyping avars :=
     | committed_nil : forall Gamma Delta,
         Gamma ⸴ Delta ⊢c nil

     | committed_cons : forall Gamma Delta x avs,
         Gamma ⸴ Delta ⊢c (trm_var (avar_f x)) ->
         Gamma ⸴ Delta ⊢c avs ->
         Gamma ⸴ Delta ⊢c (cons (avar_f x) avs)

(** ** Committed Literals [Gamma; Delta ⊢c l] *)
with well_committed_lit : CommitTyping lit :=
(** [ Gamma,x:T; Delta,x:committed ⊢c t ]     #<br>#
    [ x fresh ]     #<br>#
    [――――――――――――] #<br>#
    [ Gamma; Delta ⊢c λ(T)t ]     *)
     | commit_all_intro : forall L Gamma Delta T t,
         (forall x, x \notin L ->
               Gamma & x ~ T ⸴ Delta & x ~ committed ⊢c open x t) ->
         Gamma ⸴ Delta ⊢c lit_fun T t

(** [ ⊢e t^(x,x1,...) : (def_eff x ds) ]     #<br>#
    [ Gamma,x1:T1,...,x:U; Delta,x1:i,...,x:free ⊢i t : i ]     #<br>#
    [ x fresh ]     #<br>#
    [――――――――――――] #<br>#
    [ Gamma; Delta ⊢c kappa(x1:i1 T1,...->U){ds}t ]     *)
     | commit_con_intro : forall L Gamma Delta Ts is' T i ds t,
         length is' = length_s Ts ->
         (forall x ys,
             length ys = length_s Ts ->
             fresh L (S (length ys)) (cons x ys) ->
             has_effs (open_vars (cons x ys) t) (def_eff x ds)) ->
         (forall x ys,
             length ys = length_s Ts ->
             fresh L (S (length ys)) (cons x ys) ->
             (Gamma & (ys ~** (to_list Ts))
              & (x ~ open_vars (cons x ys) T) ⸴ Delta
              & (ys ~** is') & (x ~ free) ⸴ (from_list ys) \u \{ x}
                                          ⊢i (open_vars (cons x ys) t) ∶ i)) ->
         Gamma ⸴ Delta ⊢c lit_con Ts is' T ds t

(** ** Well-initialized Terms [Gamma; (Delta | vs ^ free) ⊢i t : i] *)
with well_init : InitTyping trm :=

| init_var_binds : forall Gamma Delta vs x i,
(** [(Delta | vs ^ free) (x) = i ]     #<br>#
    [――――――――――――――――――――――――――――] #<br>#
    [Gamma; (Delta | vs ^ free) ⊢i x : i]     *)
    init_var Delta vs x i ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_var (avar_f x) ∶ i

(** [Gamma; Delta ⊢c t ]     #<br>#
    [――――――――――――――――――――――――――――――――――――] #<br>#
    [Gamma; (Delta | vs ^ free) ⊢i t : committed]     *)
| init_commit : forall Gamma Delta t vs,
    Gamma ⸴ Delta ⊢c t ->
    Gamma ⸴ Delta ⸴ vs ⊢i t ∶ committed

(** We modify the constructor call rule so that we can assume that references
    returned from constructors are locally initailzed *)

(** [Gamma; Delta ⊢c k ]                            #<br>#
    [Gamma ⊢c x : K(i1 T1,...)U ]               #<br>#
    [Gamma; (Delta | vs ^ free) ⊢i y1,... : i1,...] #<br>#
    [――――――――――――――――――――――――――――――――――――――] #<br>#
    [Gamma; (Delta | vs ^ free) ⊢i new k(y1,...) : local]     *)
| init_new_local : forall Gamma Delta vs x avs Ts is' T,
    Gamma ⸴ Delta ⊢c trm_var (avar_f x) ->
    Gamma ⊢ trm_var (avar_f x) ∶ typ_con Ts is' T ->
    Gamma ⸴ Delta ⸴ vs ⊢i avs :: is' ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_new (avar_f x) avs ∶ local

(** [Gamma; (Delta | vs ^ free) ⊢i x : i ]     #<br>#
    [Gamma; (Delta | vs ^ free) ⊢i y : committed ]     #<br>#
    [―――――――――――――――――――――――――――――――――――――――――――] #<br>#
    [Gamma; (Delta | vs ^ free) ⊢i x.a := y : committed]     *)
| init_fld_asn_ac : forall Gamma Delta vs x i y a,
    Gamma ⸴ Delta ⸴ vs ⊢i trm_var (avar_f x) ∶ i ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_var (avar_f y) ∶ committed ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_asn (avar_f x) a (avar_f y) ∶ committed

(** We modify the assignment rule from the base calculus to allow more writes *)

(** [Gamma; (Delta | vs ^ free) ⊢i x : free ]     #<br>#
    [Gamma; (Delta | vs ^ free) ⊢i y : i ]     #<br>#
    [――――――――――――――――――――――――――――――――――――――] #<br>#
    [Gamma; (Delta | vs ^ free) ⊢i x.a := y : i]     *)
| init_fld_asn_fa : forall Gamma Delta vs x i y a,
    Gamma ⸴ Delta ⸴ vs ⊢i trm_var (avar_f x) ∶ free ->
    (* i can be local, free, committed, unspec *)
    Gamma ⸴ Delta ⸴ vs ⊢i trm_var (avar_f y) ∶ i ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_asn (avar_f x) a (avar_f y) ∶ i

(** This following rule is new for the extension *)

(** [Gamma; (Delta | vs ^ free) ⊢i x : local ]     #<br>#
    [――――――――――――――――――――――――――――――――――――――] #<br>#
    [Gamma; (Delta | vs ^ free) ⊢i x.a : unspecified ]     *)
| init_rcd_elim : forall Gamma Delta vs x a,
    Gamma ⸴ Delta ⸴ vs ⊢i trm_var (avar_f x) ∶ local ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_sel (avar_f x) a ∶ unspecified

(** [Gamma; (Delta | vs ^ free) ⊢i t : i ]     #<br>#
    [Gamma,x:T ; (Delta | vs ^ free),x:i ⊢i u : i' ]     #<br>#
    [x fresh ]     #<br>#
    [――――――――――――――――――――――――――――――――――――――――――――――] #<br>#
    [Gamma; (Delta | vs ^ free) ⊢i let (x:T) = t in u : i']     *)
| init_let : forall L Gamma Delta vs t u T i i',
    Gamma ⸴ Delta ⸴ vs ⊢i t ∶ i ->
    (forall x, x \notin L -> Gamma & x ~ T ⸴ Delta & x ~ i ⸴ vs \u \{ x} ⊢i open x u ∶ i') ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_let T t u ∶ i'

(** [Gamma; Delta ⊢c l ]     #<br>#
    [Gamma,x:T ; (Delta | vs ^ free),x:committed ⊢i u : i' ]     #<br>#
    [x fresh ]     #<br>#
    [―――――――――――――――――――――――――――――――――――――――――――――――] #<br>#
    [Gamma; (Delta | vs ^ free) ⊢i let (x:T) = l in u : i']     *)
| init_llit : forall L Gamma Delta vs l u T i,
    Gamma ⸴ Delta ⊢c l ->
    (forall x, x \notin L -> Gamma & x ~ T ⸴ Delta & x ~ committed ⸴ vs ⊢i open x u ∶ i) ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_lit T l u ∶ i

(** *** Well-typed List of Variables [Gamma; Delta ⊢c x1,... ] *)
with well_inits : InitTypings avars :=
     | well_inits_nil : forall Gamma Delta vs,
         Gamma ⸴ Delta ⸴ vs ⊢i nil :: nil

     | well_inits_cons : forall Gamma Delta vs x i avs is',
         Gamma ⸴ Delta ⸴ vs ⊢i (trm_var (avar_f x)) ∶ i ->
         Gamma ⸴ Delta ⸴ vs ⊢i avs :: is' ->
         Gamma ⸴ Delta ⸴ vs ⊢i (cons (avar_f x) avs) :: (cons i is').


(** *** Infrastructure for Initialization System *)
Hint Constructors well_committed well_committed_avars
     well_init well_inits well_committed_lit : core.
Existing Instances well_committed well_committed_avars
     well_init well_inits well_committed_lit.

Scheme well_committed_mut        := Induction for well_committed Sort Prop
with   well_committed_avars_mut  := Induction for well_committed_avars Sort Prop
with   well_committed_lit_mut    := Induction for well_committed_lit Sort Prop
with   well_init_mut             := Induction for well_init Sort Prop
with   well_inits_mut            := Induction for well_inits Sort Prop.
Combined Scheme well_init_mut_ind from
         well_committed_mut, well_committed_avars_mut, well_committed_lit_mut,
         well_init_mut, well_inits_mut.

(** Tactics for generating fresh variables. *)

Ltac init_gather_vars :=
  let A := gather_vars_with (fun x : vars      => x                ) in
  let B := gather_vars_with (fun x : var       => \{ x }           ) in
  let C := gather_vars_with (fun x : ctx       => dom x \u fv_env x) in
  let D := gather_vars_with (fun x : heap      => dom x \u fv_env x) in
  let E := gather_vars_with (fun x : avar      => fv x             ) in
  let F := gather_vars_with (fun x : trm       => fv x             ) in
  let G := gather_vars_with (fun x : item      => fv x             ) in
  let H := gather_vars_with (fun x : def       => fv x             ) in
  let I := gather_vars_with (fun x : defs      => fv x             ) in
  let J := gather_vars_with (fun x : typ       => fv x             ) in
  let K := gather_vars_with (fun x : typs      => fv x             ) in
  let L := gather_vars_with (fun x : lit       => fv x             ) in
  let M := gather_vars_with (fun x : init_ctx  => dom x            ) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J \u K \u L \u M).

Ltac init_pick_fresh x :=
  let L := init_gather_vars in
  (pick_fresh_gen L x); sympl in *.

Tactic Notation "init_apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T init_gather_vars x.

Ltac init_fresh_constructor_extern :=
  match goal with
  | [ |- _ ⸴ _ ⊢c lit_fun _ _ ] =>
    let z := fresh "z" in
    init_apply_fresh commit_all_intro as z
  | [ |- _ ⸴ _ ⊢c lit_con _ _ _ _ _ ] =>
    let z := fresh "z" in
    init_apply_fresh commit_con_intro as z
  | [ |- _ ⸴ _ ⊢c trm_let _ _ _ ] =>
    let z := fresh "z" in
    init_apply_fresh commit_let as z
  | [ |- _ ⸴ _ ⊢c trm_lit _ _ _ ] =>
    let z := fresh "z" in
    init_apply_fresh commit_llit as z
  | [ |- _ ⸴ _ ⸴ _ ⊢i trm_let _ _ _ ∶ _ ] =>
    let z := fresh "z" in
    init_apply_fresh init_let as z
  | [ |- _ ⸴ _ ⸴ _ ⊢i trm_lit _ _ _ ∶ _ ] =>
    let z := fresh "z" in
    init_apply_fresh init_llit as z
  end.

Ltac notin_L :=
  match goal with
  | [ L : fset var, H : ?z \notin _ |- _ ] =>
    match goal with
    | [ HL : z \notin L |- _ ] => fail
    | _ => assert (z \notin L) by auto
    end
  end.

Ltac notin_apply :=
  repeat
    match goal with
    | [ H : forall (x : var), x \notin ?L -> _,
          Hz : ?z \notin ?L |- _ ] => specialize (H z Hz)
    end.

Hint Extern 6 (_ ⸴ _ ⸴ _ ⊢i _ ∶ _) => init_fresh_constructor_extern : core.
