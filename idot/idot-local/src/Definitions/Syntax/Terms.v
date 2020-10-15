(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Bool.Bool.
Require Import LibExtra DotTactics SyntaxClasses.
Require Import Vars TransformCollect Types.

(* ************************************************************************** *)
(** * Definitions
Member definitions ([def], [d] and [defs], [ds]):
  - [def_typ A T] represents a type-member definition [{A = T}];
  - [def_trm a] represents a field definition [{a = null}]; *)
Inductive def : Set :=
  | def_typ  : typ_label -> typ -> def
  | def_trm  : trm_label -> def.

(**
  [defs] represents a list of definitions that are part of an intersection
  - [nil] represents the empty list;
  - [cons d ds] represents a concatenation of the definition [d] to the definitions [ds]. *)
Notation defs := (list def).

(* ************************************************************************** *)
(** * Terms
  Terms ([trm], [t], [u]) and literals ([lit], [l]):
  - [trm_var x] represents a variable [x];
  - [trm_sel x a] represents a field selection [x.a];
  - [trm_app x y] represents a function application [x y];
  - [trm_let t u] represents a let binding [let x = t in u]; since x is bound in [u],
    it is referred to in [u] using the de Bruijn index 0, and is therefore omitted from
    the let-term representation; we will denote let terms as [let t in u];
  - [trm_lit l u] represents a literal binding [lit x = l in u]; since x is bound in [u],
    it is referred to in [u] using the de Bruijn index 0, and is therefore omitted from
    the let-term representation; we will denote let terms as [let l in u];
  - [trm_asn x a y] represents a field assignment [x.a := y];
  - [trm_new k ys] represents a call to a constructor [new k(ys)];
  - [lit_fun T t] represents a function defintion [lambda(x: T)t];
  - [lit_con Ts is U ds t] represents a constructor definition [kappa(x1:i1 T1,...->U){ds}t];
 *)
Inductive trm : Set :=
  | trm_var  : avar -> trm
  | trm_sel  : avar -> trm_label -> trm
  | trm_app  : avar -> avar -> trm
  | trm_let  : typ -> trm -> trm -> trm
  | trm_lit  : typ -> lit -> trm -> trm
  | trm_asn  : avar -> trm_label -> avar -> trm
  | trm_new  : avar -> list avar -> trm
with lit : Set :=
  | lit_fun : typ -> trm -> lit
  | lit_con  : typs -> inits -> typ -> defs -> trm -> lit.
Hint Constructors trm lit : core.

(** *** Mutual Induction Principles *)
Scheme trm_mut  := Induction for trm  Sort Prop
with   lit_mut  := Induction for lit  Sort Prop.
Combined Scheme trm_mutind from trm_mut, lit_mut.


(* ************************************************************************** *)
(** ** Terms are Abstract Syntax *)
Definition open_rec_def (k: nat) (u: var) (d: def) : def :=
  match d with
  | def_typ L T => def_typ L (open_rec k u T)
  | def_trm m   => def_trm m
  end.

Instance DefOpenable : Openable def := open_rec_def.

Fixpoint open_rec_trm (k: nat) (u: var) (t: trm): trm :=
  match t with
  | trm_var a      => trm_var (open_rec k u a)
  | trm_sel v m    => trm_sel (open_rec k u v) m
  | trm_app f a    => trm_app (open_rec k u f) (open_rec k u a)
  | trm_let T t1 t2 =>
    trm_let (open_rec k u T) (open_rec_trm k u t1) (open_rec_trm (S k) u t2)
  | trm_lit T l t =>
    trm_lit (open_rec k u T) (open_rec_lit k u l) (open_rec_trm (S k) u t)
  | trm_asn v m v2 => trm_asn (open_rec k u v) m (open_rec k u v2)
  | trm_new a avs  => trm_new (open_rec k u a) (open_rec k u avs)
  end with
open_rec_lit (k: nat) (u: var) (l: lit): lit :=
  match l with
  | lit_fun T t => lit_fun (open_rec k u T) (open_rec_trm (S k) u t)
  | lit_con Ts is' T ds t =>
    lit_con
      (open_rec k u Ts)
      is'
      (open_rec (S (length_s Ts) + k) u T)
      (open_rec (S (length_s Ts) + k) u ds)
      (open_rec_trm (S (length_s Ts) + k) u t)
      (* avar_n 0 refers to self/this,
         avar_n 1 ... length Ts refers to arguments *)
  end.

Instance TrmOpenable : Openable trm := open_rec_trm.
Instance LitOpenable : Openable lit := open_rec_lit.
Ltac fold_trm_open_rec :=
  change (open_rec_trm) with (@open_rec trm TrmOpenable);
  change (open_rec_lit) with (@open_rec lit LitOpenable);
  change (open_rec_def) with (@open_rec def DefOpenable);
  fold_list.

Definition fv_def (d: def) : vars :=
  match d with
  | def_typ _ T     => (fv T)
  | def_trm _       => \{}
  end.
Instance DefFreeVar : FreeVar def := fv_def.

Fixpoint fv_trm (t: trm) : vars :=
  match t with
  | trm_var a         => (fv a)
  | trm_sel x m       => (fv x)
  | trm_app f a       => (fv f) \u (fv a)
  | trm_let T t1 t2   => (fv T) \u (fv_trm t1) \u (fv_trm t2)
  | trm_lit T l t     => (fv T) \u (fv_lit l) \u (fv_trm t)
  | trm_asn x m y     => (fv x) \u (fv y)
  | trm_new a avs     => (fv a) \u (fv avs)
  end with
fv_lit (l: lit) : vars :=
  match l with
  | lit_fun T e    => (fv T) \u (fv_trm e)
  | lit_con Ts is' T ds t => (fv Ts) \u (fv T) \u (fv ds) \u (fv_trm t)
  end.
Instance TrmFreeVar : FreeVar trm := fv_trm.
Instance LitFreeVar : FreeVar lit := fv_lit.
Ltac fold_trm_fv :=
  change (fv_trm) with (@fv trm TrmFreeVar);
  change (fv_lit) with (@fv lit LitFreeVar);
  change (fv_def) with (@fv def DefFreeVar);
  fold_list.

Definition subst_def (z: var) (u: var) (d: def) : def :=
  match d with
  | def_typ l t => def_typ l (subst_var z u t)
  | def_trm l   => def_trm l
  end.

Instance DefSubstVar : SubstVar def := subst_def.

Fixpoint subst_trm (z: var) (u: var) (t: trm) : trm :=
  match t with
  | trm_var x        => trm_var (subst_var z u x)
  | trm_sel x1 L     => trm_sel (subst_var z u x1) L
  | trm_app x1 x2    => trm_app (subst_var z u x1) (subst_var z u x2)
  | trm_let T t1 t2  =>
    trm_let (subst_var z u T) (subst_trm z u t1) (subst_trm z u t2)
  | trm_lit T l t    =>
    trm_lit (subst_var z u T) (subst_lit z u l) (subst_trm z u t)
  | trm_asn x1 L x2  => trm_asn (subst_var z u x1) L (subst_var z u x2)
  | trm_new x xs     =>
    trm_new (subst_var z u x) (subst_var z u xs)
  end with
subst_lit (z: var) (u: var) (l: lit) : lit :=
  match l with
  | lit_fun T t   => lit_fun (subst_var z u T) (subst_trm z u t)
  | lit_con Ts is' T ds t =>
    lit_con (subst_var z u Ts)
            is'
            (subst_var z u T)
            (subst_var z u ds)
            (subst_trm z u t)
  end.
Instance TrmSubstVar : SubstVar trm := subst_trm.
Instance LitSubstVar : SubstVar lit := subst_lit.
Ltac fold_trm_subst :=
  change (subst_trm) with (@subst_var trm TrmSubstVar);
  change (subst_lit) with (@subst_var lit LitSubstVar);
  change (subst_def) with (@subst_var def DefSubstVar);
  change (@subst_var_list def DefSubstVar)
    with (@subst_var defs (@ListSubstVar def DefSubstVar));
  fold_list.

Instance TrmAbstractSyntax :
  AbstractSyntax TrmOpenable TrmFreeVar TrmSubstVar := {}.
Instance LitAbstractSyntax :
  AbstractSyntax LitOpenable LitFreeVar LitSubstVar := {}.
Instance DefAbstractSyntax :
  AbstractSyntax DefOpenable DefFreeVar DefSubstVar := {}.
Ltac fold_trm_abs :=
  fold_trm_open_rec; fold_trm_fv; fold_trm_subst.


(* ************************************************************************** *)
(** ** Definitions are labeled *)
Instance DefLabelOf : LabelOf def :=
  fun D =>
      match D with
      | def_typ L _ => label_typ L
      | def_trm m   => label_trm m
      end.

Instance DefSubstLabel : SubstLabel DefSubstVar DefLabelOf.
Proof.
  hnf; intros. destruct d; reflexivity.
Qed.

(* ************************************************************************** *)
(** ** Terms Satisfy Syntax Lemmas *)
(** We will prove that the operations on Terms, Defintions and Definition Lists
    are lifted from locally nameless variables. The syntax lemmas will then by
    automatically lifted from the syntax lemmas of locally nameless variables
    through the type class mechanism *)

Definition collect_def {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (d: def) : C :=
  match d with
  | def_typ _ T     => (collect df f comb T)
  | def_trm _       => df
  end.

Instance DefCollect : Collect AvarAbstractSyntax DefAbstractSyntax :=
  @collect_def.

(** *** Collect Variables in Terms *)
Fixpoint collect_trm {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (t: trm) : C :=
  match t with
  | trm_var a        => (f a)
  | trm_sel x m      => (f x)
  | trm_app f' a     => comb (f f') (f a)
  | trm_let T t1 t2  =>
    comb (collect df f comb T)
         (comb (collect_trm df f comb t1) (collect_trm df f comb t2))
  | trm_lit T l t    =>
    comb (collect df f comb T)
         (comb (collect_lit df f comb l) (collect_trm df f comb t))
  | trm_asn x m y    => comb (f x) (f y)
  | trm_new a avs    => comb (f a) (collect df f comb avs)
  end with
collect_lit {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (l: lit) : C :=
  match l with
  | lit_fun T e  => comb (collect df f comb T) (collect_trm df f comb e)
  | lit_con Ts is' T ds t =>
    comb (collect df f comb Ts)
         (comb (collect df f comb T)
               (comb (collect df f comb ds) (collect_trm df f comb t)))
  end.

Instance TrmCollect : Collect AvarAbstractSyntax TrmAbstractSyntax :=
  @collect_trm.

Instance LitCollect : Collect AvarAbstractSyntax LitAbstractSyntax :=
  @collect_lit.

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
            DefCollect).
Local Ltac sympl_trm_collect :=
  simpl; fold_trm_collect; fold_trm_abs.

(** *** Sanity for Collecting Variables in Terms *)
Instance DefCollectCompose : CollectCompose DefCollect.
Proof.
  hnf; intros.
  unfold compose; apply fun_ext_dep; intros d.
  destruct d; simpl; auto.
  rewrite (fold_compose f), (collect_compose _ _ _ _ _ H).
  auto.
Qed.

Lemma collect_compose_trm_def_defs :
  forall {C D} (f : C -> D) g comb1 comb2 i,
    (forall x y, f (comb1 x y) = comb2 (f x) (f y)) ->
    (forall (t : trm),
        (f ∘ collect i g comb1) t = collect (f i) (f ∘ g) comb2 t) /\
    (forall (l : lit),
        (f ∘ collect i g comb1) l = collect (f i) (f ∘ g) comb2 l).
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

Instance DefCollectReflect : CollectReflect DefCollect.
Proof.
  hnf. intros; destruct a; simpl;
         auto using Is_true_iff_eq_true.
  apply collect_reflect; assumption.
Qed.

Lemma collect_reflect_trm_def_defs :
  forall P p,
    (forall b, (P b) <-> (p b) = true) ->
    forall bl,
      (forall (t : trm),
          ((collect (Is_true bl) P or t) <-> (collect bl p orb t) = true)) /\
      (forall (l : lit),
          ((collect (Is_true bl) P or l) <-> (collect bl p orb l) = true)).
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

Instance TrmCollectReflect : CollectReflect TrmCollect.
Proof. solve_collect_sanity. Qed.

Instance LitCollectReflect : CollectReflect LitCollect.
Proof. solve_collect_sanity. Qed.

(** *** Transforming Variables in Terms *)
Definition transform_def (f : avar -> nat -> avar) (d : def) (n : nat) : def :=
  match d with
  | def_typ L T => def_typ L (transform f T n)
  | def_trm m   => def_trm m
  end.

Instance DefTransform : Transform AvarAbstractSyntax DefAbstractSyntax :=
  @transform_def.

Fixpoint transform_trm (f : avar -> nat -> avar) (t : trm) (n : nat) : trm :=
  match t with
  | trm_var a      => trm_var (f a n)
  | trm_sel v m    => trm_sel (f v n) m
  | trm_app f' a    => trm_app (f f' n) (f a n)
  | trm_let T t1 t2 =>
    trm_let (transform f T n) (transform_trm f t1 n) (transform_trm f t2 (S n))
  | trm_lit T l t  =>
    trm_lit (transform f T n) (transform_lit f l n) (transform_trm f t (S n))
  | trm_asn v m v2 => trm_asn (f v n) m (f v2 n)
  | trm_new a avs  => trm_new (f a n) (transform f avs n)
  end with
transform_lit (f : avar -> nat -> avar) (l : lit) (n : nat) : lit :=
  match l with
  | lit_fun T t => lit_fun (transform f T n) (transform_trm f t (S n))
  | lit_con Ts is' T ds t =>
    lit_con
      (transform f Ts n)
      is'
      (transform f T (S (length_s Ts) + n))
      (transform f ds (S (length_s Ts) + n))
      (transform_trm f t (S (length_s Ts) + n))
      (* avar_n (0) refers to self/this *)
  end.

Instance TrmTransform : Transform AvarAbstractSyntax TrmAbstractSyntax :=
  @transform_trm.

Instance LitTransform : Transform AvarAbstractSyntax LitAbstractSyntax :=
  @transform_lit.

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
            DefTransform).

Local Ltac sympl_trm_transform :=
  simpl; fold_trm_transform; fold_trm_collect; fold_trm_abs.

(** *** Sanity for Transforming Variables in Terms *)
Instance DefTransformId : TransformId DefTransform.
Proof.
  hnf. intros d.
  destruct d; intros; simpl;
    rewrite ? transform_id; auto.
Qed.

Lemma transform_id_trm_def_defs :
  (forall (t : trm) n, transform (ignore_second id) t n = t) /\
  (forall (l : lit) n, transform (ignore_second id) l n = l).
Proof.
  apply trm_mutind; sympl_trm_transform; intros; try f_equal;
    try rewrite transform_id; auto.
Qed.

Instance DefTransformCompose : TransformCompose DefTransform.
Proof.
  hnf. unfold "∘∘". intros f g.
  apply fun_ext_dep. intros d.
  destruct d; auto.
  apply fun_ext_dep. intros n.
  simpl.
  rewrite (fold_compose12 (transform f)).
  rewrite transform_compose. auto.
Qed.

Lemma transform_compose_trm_def_defs :
  (forall (t : trm) n f g,
      ((transform f) ∘∘ (transform g)) t n = transform (f ∘∘ g) t n) /\
  (forall (l : lit) n f g,
      ((transform f) ∘∘ (transform g)) l n = transform (f ∘∘ g) l n).
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

Instance TrmTransformCompose : TransformCompose TrmTransform.
Proof. solve_transform_sanity. Qed.

Instance LitTransformCompose : TransformCompose LitTransform.
Proof. solve_transform_sanity. Qed.

Instance DefCollectTransform :
  CollectTransform DefCollect DefTransform.
Proof.
  hnf; intros. destruct a; auto.
  apply fun_ext_dep. intros n.
  sympl_trm_transform.
  erewrite collect_transform by eauto.
  auto.
Qed.

Lemma collect_transform_term :
  (forall (t : trm) bl p f g,
      (collect bl p andb t) = true ->
      transform (dec_apply p f g) t = transform f t) /\
  (forall (l : lit) bl p f g,
      (collect bl p andb l) = true ->
      transform (dec_apply p f g) l = transform f l).
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

(** *** Sanity for Collecting and Transforming Variables *)
Instance DefFvCollect : FvCollect DefCollect.
Proof.
  hnf. apply fun_ext_dep. intros d.
  destruct d; simpl; rewrite ? fv_collect; auto.
Qed.

Instance DefOpenTransform : OpenTransform DefTransform.
Proof.
  hnf.
  intros.
  apply fun_ext_dep. intros d.
  apply fun_ext_dep. intros dp.
  destruct d; simpl; auto.
  f_equal. rewrite <- open_transform. auto.
Qed.

Instance DefSubstTransform : SubstTransform DefTransform.
Proof.
  hnf.
  intros.
  apply fun_ext_dep. intros d.
  apply fun_ext_dep. intros dp.
  destruct d; simpl; auto.
  rewrite <- subst_transform.
  unfold ignore_second; auto.
Qed.

Lemma fv_collect_trm_def_defs :
  (forall (t : trm), fv t = collect (\{}) fv (@union var) t) /\
  (forall (l : lit), fv l = collect (\{}) fv (@union var) l).
Proof.
  apply trm_mutind; sympl_trm_transform; intros;
    repeat match goal with
    | [ H : _ = _ |- _ ] => rewrite <- ? H; clear H
    end; rewrite <- ? fv_collect; auto.
Qed.

Lemma open_transform_trm_def_defs :
  (forall (t : trm) n x, (open_depth_rec n x) t = transform (open_depth_rec n x) t) /\
  (forall (l : lit) n x, (open_depth_rec n x) l = transform (open_depth_rec n x) l).
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
  assert (R: (fun (a : avar) (d0 : nat) => open_rec (n + d0) x a) = open_depth_rec n x)
    by auto; rewrite R; clear R.
  rewrite <- ? open_transform; unfold open_depth_rec.
  do 2 fequal; rewrite Nat.add_shuffle3; auto.
Qed.

Lemma subst_transform_trm_def_defs :
  (forall (t : trm) x y, (ignore_second (subst_var x y)) t
                = transform (ignore_second (subst_var x y)) t) /\
  (forall (l : lit) x y, (ignore_second (subst_var x y)) l
                = transform (ignore_second (subst_var x y)) l).
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

Instance TrmOpenTransform : OpenTransform TrmTransform.
Proof. solve_transform_syntax. Qed.

Instance TrmSubstTransform : SubstTransform TrmTransform.
Proof. solve_transform_syntax. Qed.

Instance DefFvOpenCases : FvOpenCases DefAbstractSyntax.
Proof.
  hnf. intros x d.
  destruct d; intros; simpl; auto.
  apply fv_open_cases.
Qed.

(** Additional Lemmas that are not lifted automatically *)
Lemma fv_open_term_cases : forall x,
    (forall (t : trm) n,
        fv (open_rec n x t) = fv t \/
        fv (open_rec n x t) = \{ x} \u fv t) /\
    (forall (l : lit) n,
        fv (open_rec n x l) = fv l \/
        fv (open_rec n x l) = \{ x} \u fv l).
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
