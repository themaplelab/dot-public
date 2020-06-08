(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Bool.Bool.
Require Import LibExtra DotTactics SyntaxClasses.
Require Import Vars TransformCollect Types.

(* ************************************************************************** *)
(** * Terms
  Terms ([trm], [t], [u]), member definitions ([def], [d] and [defs], [ds]):
  - [trm_var x] represents a variable [x];
  - [lit_fun T t] represents a function defintion [lambda(x: T)t];
  - [trm_sel x a] represents a field selection [x.a];
  - [trm_app x y] represents a function application [x y];
  - [trm_let t u] represents a let binding [let x = t in u]; since x is bound in [u],
    it is referred to in [u] using the de Bruijn index 0, and is therefore omitted from
    the let-term representation; we will denote let terms as [let t in u];
  - [trm_asn x a y] represents a field assignment [x.a := y];
  - [lit_con Ts U ds] represents a constructor definition [kappa(x1:T1,...->U)ds];
 *)
Inductive trm : Set :=
  | trm_var  : avar -> trm
  | trm_sel  : avar -> trm_label -> trm
  | trm_app  : avar -> avar -> trm
  | trm_let  : trm -> trm -> trm
  | trm_lit  : lit -> trm -> trm
  | trm_asn  : avar -> trm_label -> avar -> trm
with lit : Set :=
  | lit_fun : typ -> trm -> lit
  | lit_obj  : typ -> defs -> lit
(**
  - [def_typ A T] represents a type-member definition [{A = T}];
  - [def_trm a t] represents a field definition [{a = t}]; *)
with def : Set :=
  | def_typ  : typ_label -> typ -> def
  | def_trm  : trm_label -> trm -> def
(**
  [defs] represents a list of definitions that are part of an intersection
  - [defs_nil] represents the empty list;
  - [defs_cons d ds] represents a concatenation of the definition [d] to the definitions [ds]. *)
with defs : Set :=
  | defs_nil : defs
  | defs_cons : defs -> def -> defs.
Hint Constructors trm def defs : core.

(** *** Mutual Induction Principles *)
Scheme trm_mut  := Induction for trm  Sort Prop
with   lit_mut  := Induction for lit  Sort Prop
with   def_mut  := Induction for def  Sort Prop
with   defs_mut := Induction for defs Sort Prop.
Combined Scheme trm_mutind from trm_mut, lit_mut, def_mut, defs_mut.


(* ************************************************************************** *)
(** ** Terms are Abstract Syntax *)
Fixpoint open_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_var a      => trm_var (open_rec k u a)
  | trm_sel v m    => trm_sel (open_rec k u v) m
  | trm_app f a    => trm_app (open_rec k u f) (open_rec k u a)
  | trm_let t1 t2  => trm_let (open_rec_trm k u t1) (open_rec_trm (S k) u t2)
  | trm_lit l t => trm_lit (open_rec_lit k u l) (open_rec_trm (S k) u t)
  | trm_asn v m v2 => trm_asn (open_rec k u v) m (open_rec k u v2)
  end with
open_rec_lit (k: nat) (u: var) (l: lit): lit :=
  match l with
  | lit_fun T t => lit_fun (open_rec k u T) (open_rec_trm (S k) u t)
  | lit_obj T ds =>
    lit_obj
      (open_rec (S k) u T)
      (open_rec_defs (S k) u ds)
      (* avar_n 0 refers to self/this *)
  end with
open_rec_def (k: nat) (u: var) (d: def): def :=
  match d with
  | def_typ L T => def_typ L (open_rec k u T)
  | def_trm m e => def_trm m (open_rec_trm k u e)
  end with
open_rec_defs (k: nat) (u: var) (ds: defs): defs :=
  match ds with
  | defs_nil       => defs_nil
  | defs_cons tl d => defs_cons (open_rec_defs k u tl) (open_rec_def k u d)
  end.
Instance TrmOpenable : Openable trm := open_rec_trm.
Instance LitOpenable : Openable lit := open_rec_lit.
Instance DefOpenable : Openable def := open_rec_def.
Instance DefsOpenable : Openable defs := open_rec_defs.
Ltac fold_trm_open_rec :=
  change (open_rec_trm) with (@open_rec trm TrmOpenable);
  change (open_rec_lit) with (@open_rec lit LitOpenable);
  change (open_rec_def) with (@open_rec def DefOpenable);
  change (open_rec_defs) with (@open_rec defs DefsOpenable).

Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_var a         => (fv a)
  | trm_sel x m       => (fv x)
  | trm_app f a       => (fv f) \u (fv a)
  | trm_let t1 t2     => (fv_trm t1) \u (fv_trm t2)
  | trm_lit l t       => (fv_lit l) \u (fv_trm t)
  | trm_asn x m y     => (fv x) \u (fv y)
  end with
fv_lit (l: lit) : vars :=
  match l with
  | lit_fun T e    => (fv T) \u (fv_trm e)
  | lit_obj T ds => (fv T) \u (fv_defs ds)
  end with
fv_def (d: def) : vars :=
  match d with
  | def_typ _ T     => (fv T)
  | def_trm _ t     => (fv_trm t)
  end with
fv_defs(ds: defs) : vars :=
  match ds with
  | defs_nil         => \{}
  | defs_cons tl d   => (fv_defs tl) \u (fv_def d)
  end.
Instance TrmFreeVar : FreeVar trm := fv_trm.
Instance LitFreeVar : FreeVar lit := fv_lit.
Instance DefFreeVar : FreeVar def := fv_def.
Instance DefsFreeVar : FreeVar defs := fv_defs.
Ltac fold_trm_fv :=
  change (fv_trm) with (@fv trm TrmFreeVar);
  change (fv_lit) with (@fv lit LitFreeVar);
  change (fv_def) with (@fv def DefFreeVar);
  change (fv_defs) with (@fv defs DefsFreeVar).

Fixpoint subst_trm (z: var) (u: var) (t: trm) : trm :=
  match t with
  | trm_var x        => trm_var (subst_var z u x)
  | trm_sel x1 L     => trm_sel (subst_var z u x1) L
  | trm_app x1 x2    => trm_app (subst_var z u x1) (subst_var z u x2)
  | trm_let t1 t2    => trm_let (subst_trm z u t1) (subst_trm z u t2)
  | trm_lit l t      => trm_lit (subst_lit z u l) (subst_trm z u t)
  | trm_asn x1 L x2  => trm_asn (subst_var z u x1) L (subst_var z u x2)
  end with
subst_lit (z: var) (u: var) (l: lit) : lit :=
  match l with
  | lit_fun T t   => lit_fun (subst_var z u T) (subst_trm z u t)
  | lit_obj T ds =>
    lit_obj (subst_var z u T)
            (subst_defs z u ds)
  end with
subst_def (z: var) (u: var) (d: def) : def :=
  match d with
  | def_typ l t => def_typ l (subst_var z u t)
  | def_trm l t => def_trm l (subst_trm z u t)
  end with
subst_defs (z: var) (u: var) (ds: defs) : defs :=
  match ds with
  | defs_nil => defs_nil
  | defs_cons rest d => defs_cons (subst_defs z u rest) (subst_def z u d)
  end.
Instance TrmSubstVar : SubstVar trm := subst_trm.
Instance LitSubstVar : SubstVar lit := subst_lit.
Instance DefSubstVar : SubstVar def := subst_def.
Instance DefsSubstVar : SubstVar defs := subst_defs.
Ltac fold_trm_subst :=
  change (subst_trm) with (@subst_var trm TrmSubstVar);
  change (subst_lit) with (@subst_var lit LitSubstVar);
  change (subst_def) with (@subst_var def DefSubstVar);
  change (subst_defs) with (@subst_var defs DefsSubstVar).

Instance TrmAbstractSyntax :
  AbstractSyntax TrmOpenable TrmFreeVar TrmSubstVar := {}.
Instance LitAbstractSyntax :
  AbstractSyntax LitOpenable LitFreeVar LitSubstVar := {}.
Instance DefAbstractSyntax :
  AbstractSyntax DefOpenable DefFreeVar DefSubstVar := {}.
Instance DefsAbstractSyntax :
  AbstractSyntax DefsOpenable DefsFreeVar DefsSubstVar := {}.
Ltac fold_trm_abs :=
  fold_trm_open_rec; fold_trm_fv; fold_trm_subst.


(* ************************************************************************** *)
(** ** Definitions are labeled *)
Instance DefLabelOf : LabelOf def :=
  fun D =>
      match D with
      | def_typ L _ => label_typ L
      | def_trm m _ => label_trm m
      end.


(* ************************************************************************** *)
(** ** Terms Satisfy Syntax Lemmas *)
(** We will prove that the operations on Terms, Defintions and Definition Lists
    are lifted from locally nameless variables. The syntax lemmas will then by
    automatically lifted from the syntax lemmas of locally nameless variables
    through the type class mechanism *)

(** *** Collect Variables in Terms *)
Fixpoint collect_trm {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (t: trm) : C :=
  match t with
  | trm_var a       => (f a)
  | trm_sel x m      => (f x)
  | trm_app f' a      => comb (f f') (f a)
  | trm_let t1 t2    => comb (collect_trm df f comb t1) (collect_trm df f comb t2)
  | trm_lit l t      => comb (collect_lit df f comb l) (collect_trm df f comb t)
  | trm_asn x m y    => comb (f x) (f y)
  end with
collect_lit {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (l: lit) : C :=
  match l with
  | lit_fun T e  => comb (collect df f comb T) (collect_trm df f comb e)
  | lit_obj T ds => comb (collect df f comb T) (collect_defs df f comb ds)
  end with
collect_def {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (d: def) : C :=
  match d with
  | def_typ _ T     => (collect df f comb T)
  | def_trm _ t     => (collect_trm df f comb t)
  end with
collect_defs {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (ds : defs) : C  :=
  match ds with
  | defs_nil         => df
  | defs_cons tl d   => comb (collect_defs df f comb tl) (collect_def df f comb d)
  end.

Instance TrmCollect : Collect AvarAbstractSyntax TrmAbstractSyntax :=
  @collect_trm.

Instance LitCollect : Collect AvarAbstractSyntax LitAbstractSyntax :=
  @collect_lit.

Instance DefCollect : Collect AvarAbstractSyntax DefAbstractSyntax :=
  @collect_def.

Instance DefsCollect : Collect AvarAbstractSyntax DefsAbstractSyntax :=
  @collect_defs.

Ltac fold_trm_collect :=
  change (@collect_trm) with (@collect
            avar AvarOpenable AvarFreeVar AvarSubstVar AvarAbstractSyntax
            trm TrmOpenable TrmFreeVar TrmSubstVar TrmAbstractSyntax
            TrmCollect);
  change (@collect_lit) with (@collect
            avar AvarOpenable AvarFreeVar AvarSubstVar AvarAbstractSyntax
            lit LitOpenable LitFreeVar LitSubstVar LitAbstractSyntax
            LitCollect);
  change (@collect_def) with (@collect
            avar AvarOpenable AvarFreeVar AvarSubstVar AvarAbstractSyntax
            def DefOpenable DefFreeVar DefSubstVar DefAbstractSyntax
            DefCollect);
  change (@collect_defs) with (@collect
            avar AvarOpenable AvarFreeVar AvarSubstVar AvarAbstractSyntax
            defs DefsOpenable DefsFreeVar DefsSubstVar DefsAbstractSyntax
            DefsCollect).
Local Ltac sympl_trm_collect :=
  simpl; fold_trm_collect; fold_trm_abs.

(** *** Sanity for Collecting Variables in Terms *)
Lemma collect_compose_trm_def_defs :
  forall {C D} (f : C -> D) g comb1 comb2 i,
    (forall x y, f (comb1 x y) = comb2 (f x) (f y)) ->
    (forall (t : trm),
        (f ∘ collect i g comb1) t = collect (f i) (f ∘ g) comb2 t) /\
    (forall (l : lit),
        (f ∘ collect i g comb1) l = collect (f i) (f ∘ g) comb2 l) /\
    (forall (d : def),
        (f ∘ collect i g comb1) d = collect (f i) (f ∘ g) comb2 d) /\
    (forall (ds : defs),
        (f ∘ collect i g comb1) ds = collect (f i) (f ∘ g) comb2 ds).
Proof.
  intros; apply trm_mutind; unfold "∘";
    sympl_trm_collect;
      try congruence;
      intros; rewrite ? H,
              ? (fold_compose f (collect (C:=C) _ _ _)),
              ? (collect_compose _ _ _ _ _ H);
      repeat match goal with
             | [ H : _ = _ |- _] => rewrite <- ? H; clear H
             end; auto.
Qed.

Local Hint Resolve collect_reflect : core.

Lemma collect_reflect_trm_def_defs :
  forall P p,
    (forall b, (P b) <-> (p b) = true) ->
    forall bl,
      (forall (t : trm),
          ((collect (Is_true bl) P or t) <-> (collect bl p orb t) = true)) /\
      (forall (l : lit),
          ((collect (Is_true bl) P or l) <-> (collect bl p orb l) = true)) /\
      (forall (d : def),
          ((collect (Is_true bl) P or d) <-> (collect bl p orb d) = true)) /\
      (forall (ds : defs),
          ((collect (Is_true bl) P or ds) <-> (collect bl p orb ds) = true)).
Proof.
  intros P p H bl.
  apply trm_mutind; sympl_trm_collect;
    auto 3 using Is_true_iff_eq_true; intros;
      repeat apply or_orb_iff_left; try apply collect_reflect; auto.
Qed.

Local Ltac solve_collect_compose :=
  unfold compose; apply fun_ext_dep;
  apply collect_compose_trm_def_defs; auto.

Local Ltac solve_collect_reflect :=
  apply collect_reflect_trm_def_defs; auto.

Local Ltac solve_collect_sanity :=
  hnf; intros; solve [solve_collect_compose || solve_collect_reflect].

Instance TrmCollectCompose : CollectCompose TrmCollect.
Proof. solve_collect_sanity. Qed.

Instance LitCollectCompose : CollectCompose LitCollect.
Proof. solve_collect_sanity. Qed.

Instance DefCollectCompose : CollectCompose DefCollect.
Proof. solve_collect_sanity. Qed.

Instance DefsCollectCompose : CollectCompose DefsCollect.
Proof. solve_collect_sanity. Qed.

Instance TrmCollectReflect : CollectReflect TrmCollect.
Proof. solve_collect_sanity. Qed.

Instance LitCollectReflect : CollectReflect LitCollect.
Proof. solve_collect_sanity. Qed.

Instance DefCollectReflect : CollectReflect DefCollect.
Proof. solve_collect_sanity. Qed.

Instance DefsCollectReflect : CollectReflect DefsCollect.
Proof. solve_collect_sanity. Qed.

(** *** Transforming Variables in Terms *)
Fixpoint transform_trm (f : avar -> nat -> avar) (t : trm) (n : nat) : trm :=
  match t with
  | trm_var a      => trm_var (f a n)
  | trm_sel v m    => trm_sel (f v n) m
  | trm_app f' a    => trm_app (f f' n) (f a n)
  | trm_let t1 t2  => trm_let (transform_trm f t1 n) (transform_trm f t2 (S n))
  | trm_lit l t    => trm_lit (transform_lit f l n) (transform_trm f t (S n))
  | trm_asn v m v2 => trm_asn (f v n) m (f v2 n)
  end with
transform_lit (f : avar -> nat -> avar) (l : lit) (n : nat) : lit :=
  match l with
  | lit_fun T t => lit_fun (transform f T n) (transform_trm f t (S n))
  | lit_obj T ds =>
    lit_obj
      (transform f T (S n))
      (transform_defs f ds (S n))
      (* avar_n (0) refers to self/this *)
  end with
transform_def (f : avar -> nat -> avar) (d : def) (n : nat) : def :=
  match d with
  | def_typ L T => def_typ L (transform f T n)
  | def_trm m e => def_trm m (transform_trm f e n)
  end with
transform_defs (f : avar -> nat -> avar) (ds : defs) (n : nat) : defs :=
  match ds with
  | defs_nil       => defs_nil
  | defs_cons tl d => defs_cons (transform_defs f tl n) (transform_def f d n)
  end.

Instance TrmTransform : Transform AvarAbstractSyntax TrmAbstractSyntax :=
  @transform_trm.

Instance LitTransform : Transform AvarAbstractSyntax LitAbstractSyntax :=
  @transform_lit.

Instance DefTransform : Transform AvarAbstractSyntax DefAbstractSyntax :=
  @transform_def.

Instance DefsTransform : Transform AvarAbstractSyntax DefsAbstractSyntax :=
  @transform_defs.

Ltac fold_trm_transform :=
  change (@transform_trm) with (@transform
            avar AvarOpenable AvarFreeVar AvarSubstVar AvarAbstractSyntax
            trm TrmOpenable TrmFreeVar TrmSubstVar TrmAbstractSyntax
            TrmTransform);
  change (@transform_lit) with (@transform
            avar AvarOpenable AvarFreeVar AvarSubstVar AvarAbstractSyntax
            lit LitOpenable LitFreeVar LitSubstVar LitAbstractSyntax
            LitTransform);
  change (@transform_def) with (@transform
            avar AvarOpenable AvarFreeVar AvarSubstVar AvarAbstractSyntax
            def DefOpenable DefFreeVar DefSubstVar DefAbstractSyntax
            DefTransform);
  change (@transform_defs) with (@transform
            avar AvarOpenable AvarFreeVar AvarSubstVar AvarAbstractSyntax
            defs DefsOpenable DefsFreeVar DefsSubstVar DefsAbstractSyntax
            DefsTransform).
Local Ltac sympl_trm_transform :=
  simpl; fold_trm_transform; fold_trm_collect; fold_trm_abs.

(** *** Sanity for Transforming Variables in Terms *)
Lemma transform_id_trm_def_defs :
  (forall (t : trm) n, transform (ignore_second id) t n = t) /\
  (forall (l : lit) n, transform (ignore_second id) l n = l) /\
  (forall (d : def) n, transform (ignore_second id) d n = d) /\
  (forall (ds : defs) n, transform (ignore_second id) ds n = ds).
Proof.
  apply trm_mutind; sympl_trm_transform; intros; try f_equal;
    try rewrite transform_id; auto.
Qed.

Lemma transform_compose_trm_def_defs :
  (forall (t : trm) n f g,
      ((transform f) ∘∘ (transform g)) t n = transform (f ∘∘ g) t n) /\
  (forall (l : lit) n f g,
      ((transform f) ∘∘ (transform g)) l n = transform (f ∘∘ g) l n) /\
  (forall (d : def) n f g,
      ((transform f) ∘∘ (transform g)) d n = transform (f ∘∘ g) d n) /\
  (forall (ds : defs) n f g,
      ((transform f) ∘∘ (transform g)) ds n = transform (f ∘∘ g) ds n).
Proof.
  unfold "∘∘".
  apply trm_mutind; sympl_trm_transform; intros; try rewrite ? transform_length_s;
    repeat
      match goal with
      | [ H : forall n f g, _ = _ |- _] => rewrite <- H
      end; auto;
      f_equal;
      rewrite ? (fold_compose12 (transform f));
      rewrite ? transform_compose; auto.
Qed.

Local Ltac solve_transform_sanity :=
  hnf; try apply transform_id_trm_def_defs;
  intros; intros_fun_ext; apply transform_compose_trm_def_defs.

Instance TrmTransformId : TransformId TrmTransform.
Proof. solve_transform_sanity. Qed.

Instance LitTransformId : TransformId LitTransform.
Proof. solve_transform_sanity. Qed.

Instance DefTransformId : TransformId DefTransform.
Proof. solve_transform_sanity. Qed.

Instance DefsTransformId : TransformId DefsTransform.
Proof. solve_transform_sanity. Qed.

Instance TrmTransformCompose : TransformCompose TrmTransform.
Proof. solve_transform_sanity. Qed.

Instance LitTransformCompose : TransformCompose LitTransform.
Proof. solve_transform_sanity. Qed.

Instance DefTransformCompose : TransformCompose DefTransform.
Proof. solve_transform_sanity. Qed.

Instance DefsTransformCompose : TransformCompose DefsTransform.
Proof. solve_transform_sanity. Qed.

Lemma collect_transform_term :
  (forall (t : trm) bl p f g,
      (collect bl p andb t) = true ->
      transform (dec_apply p f g) t = transform f t) /\
  (forall (l : lit) bl p f g,
      (collect bl p andb l) = true ->
      transform (dec_apply p f g) l = transform f l) /\
  (forall (d : def) bl p f g,
      (collect bl p andb d) = true ->
      transform (dec_apply p f g) d = transform f d) /\
  (forall (ds : defs) bl p f g,
      (collect bl p andb ds) = true ->
      transform (dec_apply p f g) ds = transform f ds).
Proof.
  apply trm_mutind; sympl_trm_transform; auto 2; intros;
    repeat (destruct_andbs; destruct_ands);
    repeat erewrite collect_transform by eauto;
    repeat
      match goal with
      | [ H : forall bl p f g,
            _ = true ->
            ?transform (dec_apply p f g) ?t = ?transform f ?t |- _] =>
        erewrite H by eauto
      end;
    repeat match goal with
           | [ H : _ = true |- _ ] => try unfold dec_apply; rewrite H
           end; auto.
Qed.

Instance TrmCollectTransform :
  CollectTransform TrmCollect TrmTransform.
Proof. hnf; intros; eapply collect_transform_term; eauto. Qed.

Instance LitCollectTransform :
  CollectTransform LitCollect LitTransform.
Proof. hnf; intros; eapply collect_transform_term; eauto. Qed.

Instance DefCollectTransform :
  CollectTransform DefCollect DefTransform.
Proof. hnf; intros; eapply collect_transform_term; eauto. Qed.

Instance DefsCollectTransform :
  CollectTransform DefsCollect DefsTransform.
Proof. hnf; intros; eapply collect_transform_term; eauto. Qed.

(** *** Sanity for Collecting and Transforming Variables *)
Lemma fv_collect_trm_def_defs :
  (forall (t : trm), fv t = collect (\{}) fv (@union var) t) /\
  (forall (l : lit), fv l = collect (\{}) fv (@union var) l) /\
  (forall (d : def), fv d = collect (\{}) fv (@union var) d) /\
  (forall (ds : defs), fv ds = collect (\{}) fv (@union var) ds).
Proof.
  apply trm_mutind; sympl_trm_transform; intros;
    repeat match goal with
    | [ H : _ = _ |- _ ] => rewrite <- ? H; clear H
    end; rewrite <- ? fv_collect; auto.
Qed.

Lemma open_transform_trm_def_defs :
  (forall (t : trm) n x, (open_depth_rec n x) t = transform (open_depth_rec n x) t) /\
  (forall (l : lit) n x, (open_depth_rec n x) l = transform (open_depth_rec n x) l) /\
  (forall (d : def) n x, (open_depth_rec n x) d = transform (open_depth_rec n x) d) /\
  (forall (ds : defs) n x, (open_depth_rec n x) ds = transform (open_depth_rec n x) ds).
Proof.
  unfold open_depth_rec.
  apply trm_mutind; sympl_trm_transform; intros; intros_fun_ext;
    repeat match goal with
           | [ H : forall _ _, _ = _ |- _] => rewrite <- H
           end;
    rewrite ? Nat.add_succ_r;
    repeat match goal with
           | [ |- context[open_rec (?n + ?m) ?x ?t] ] =>
             change (open_rec (n + m) x t) with (open_depth_rec n x t m)
           end;
    rewrite ? open_transform;
    auto.
  fequal.
  - assert (R: (fun (a : avar) (d0 : nat) => open_rec (n + d0) x a) = open_depth_rec n x)
      by auto; rewrite R; clear R. rewrite <- open_transform.
    unfold open_depth_rec. rewrite plus_n_Sm; auto.
Qed.

Lemma subst_transform_trm_def_defs :
  (forall (t : trm) x y, (ignore_second (subst_var x y)) t
                = transform (ignore_second (subst_var x y)) t) /\
  (forall (l : lit) x y, (ignore_second (subst_var x y)) l
                = transform (ignore_second (subst_var x y)) l) /\
  (forall (d : def) x y, (ignore_second (subst_var x y)) d
                = transform (ignore_second (subst_var x y)) d) /\
  (forall (ds : defs) x y, (ignore_second (subst_var x y)) ds
                = transform (ignore_second (subst_var x y)) ds).
Proof.
  apply trm_mutind; sympl_trm_transform; intros; intros_fun_ext;
    repeat match goal with
           | [ H : forall _ _, _ = _ |- _] => rewrite <- H
           end;
    rewrite <- ? subst_transform;
    unfold ignore_second; simpl; auto.
Qed.

Local Ltac solve_transform_syntax :=
  hnf; intros; (apply fun_ext_dep; intro);
    try apply fv_collect_trm_def_defs;
    try apply open_transform_trm_def_defs;
    try apply subst_transform_trm_def_defs.

Instance TrmFvCollect : FvCollect TrmCollect.
Proof. solve_transform_syntax. Qed.

Instance LitFvCollect : FvCollect LitCollect.
Proof. solve_transform_syntax. Qed.

Instance DefFvCollect : FvCollect DefCollect.
Proof. solve_transform_syntax. Qed.

Instance DefsFvCollect : FvCollect DefsCollect.
Proof. solve_transform_syntax. Qed.

Instance TrmOpenTransform : OpenTransform TrmTransform.
Proof. solve_transform_syntax. Qed.

Instance DefOpenTransform : OpenTransform DefTransform.
Proof. solve_transform_syntax. Qed.

Instance DefsOpenTransform : OpenTransform DefsTransform.
Proof. solve_transform_syntax. Qed.

Instance TrmSubstTransform : SubstTransform TrmTransform.
Proof. solve_transform_syntax. Qed.

Instance DefSubstTransform : SubstTransform DefTransform.
Proof. solve_transform_syntax. Qed.

Instance DefsSubstTransform : SubstTransform DefsTransform.
Proof. solve_transform_syntax. Qed.

(** Additional Lemmas that are not lifted automatically *)
Lemma fv_open_term_cases : forall x,
    (forall (t : trm) n,
        fv (open_rec n x t) = fv t \/
        fv (open_rec n x t) = \{ x} \u fv t) /\
    (forall (l : lit) n,
        fv (open_rec n x l) = fv l \/
        fv (open_rec n x l) = \{ x} \u fv l) /\
    (forall (d : def) n,
        fv (open_rec n x d) = fv d \/
        fv (open_rec n x d) = \{ x} \u fv d) /\
    (forall (ds : defs) n,
        fv (open_rec n x ds) = fv ds
        \/ fv (open_rec n x ds) = \{ x} \u fv ds).
Proof.
  intros x.
  apply trm_mutind; sympl_trm_transform; auto; intros;
    repeat apply union_eq_cases; auto; apply fv_open_cases.
Qed.

Instance TrmFvOpenCases : FvOpenCases TrmAbstractSyntax.
Proof.
  hnf; apply fv_open_term_cases.
Qed.

Instance LitFvOpenCases : FvOpenCases LitAbstractSyntax.
Proof.
  hnf; apply fv_open_term_cases.
Qed.

Instance DefFvOpenCases : FvOpenCases DefAbstractSyntax.
Proof.
  hnf; apply fv_open_term_cases.
Qed.

Instance DefsFvOpenCases : FvOpenCases DefsAbstractSyntax.
Proof.
  hnf; apply fv_open_term_cases.
Qed.


(* ************************************************************************** *)
(** * Heap Items
  - [item_new T ds] represents the object [nu(x:T)ds]; the variable [x] is free
    in [T] and [ds] and is interpreted as a pointer to the object itself;
  - [item_con Ts U ds] represents a constructor [kappa(x1:T1,...->(x:U))ds];
    the variable [x] is bound in [U] and [ds] and is omitted; we will denote
    constructor itemues as [kappa(x1:T1,...->U)ds].
  - [item_fun T t] represents a function [lambda(x: T)t]; again, [x] is bound in
    [t] and is omitted; we will denote lambda terms as [lambda(T)t]. *)
Inductive item : Set :=
  | item_obj : typ -> defs -> item
  | item_fun : typ -> trm -> item.


(* ************************************************************************** *)
(** ** Heap Items are Abstract Syntax *)
Definition fv_item (v: item) : vars :=
  match v with
  | item_obj T ds    => (fv T) \u (fv ds)
  | item_fun T t     => (fv T) \u (fv t)
  end.
Instance ItemFreeVar : FreeVar item := fv_item.

Definition open_rec_item (n: nat) (x: var) (v: item) : item :=
  match v with
  | item_obj T ds    => item_obj (open_rec n x T)
                              (open_rec (S n) x ds)
  | item_fun T t     => item_fun (open_rec n x T)
                              (open_rec (S n) x t)
  end.
Instance ItemOpenable : Openable item := open_rec_item.

Definition subst_item x y (v: item) : item :=
  match v with
  | item_obj T ds    => item_obj (subst_var x y T) (subst_var x y ds)
  | item_fun T t     => item_fun (subst_var x y T) (subst_var x y t)
  end.
Instance ItemSubstVar : SubstVar item := subst_item.

Instance ItemAbstractSyntax :
  AbstractSyntax ItemOpenable ItemFreeVar ItemSubstVar := {}.
