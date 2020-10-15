(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Bool.Bool.
Require Import LibExtra DotTactics SyntaxClasses.
Require Import Vars TransformCollect.

(* ************************************************************************** *)
(** * Initialization Types *)
(** We define initialization types early on so that we can type constructors
with them *)
Inductive init_typ : Set :=
  | committed : init_typ
  | local : init_typ
  | free : init_typ
  | unspecified : init_typ.

Notation inits := (list init_typ).

Notation init_ctx := (env init_typ).

(* ************************************************************************** *)
(** * Types
    Types ([typ], [S], [T], [U]), type lists ([typs], [Ts]) and type
    declarations ([dec], [D]):
    - [typ_top] represents [top];
    - [typ_bot] represents [bottom];
    - [typ_rcd d] represents a record type [d], where [d] is either a type or
      field declaration;
    - [typ_and T U] represents an intersection type [T /\ U];
    - [typ_sel x A] represents type selection [x.A];
    - [typ_bnd T] represents a recursive type [mu(x: T)]; however, since [x] is
      bound in the recursive type, it is referred to in [T] using the de Bruijn
      index 0, and is therefore omitted from the type representation; we will
      denote recursive types as [mu(T)];
    - [typ_all T U] represents the dependent function type [forall(x: T)U]; as
      in the previous case, [x] represents a variable bound in [U], and is
      therefore omitted from the representation; we will denote function types
      as [forall(T)U];
    - [typ_con Ts is U] represents the dependent constructor [K(ys: i Ts)mu(x: U)];
      as in the previous case, [x] represents a variable bound in [U], and [ys]
      represent arguments to the constructor that are free in [U]; we will
      denote constructor types as [K(is Ts)U] or [K(i1 T1, ...)U].
 *)
Inductive typ : Set :=
  | typ_top  : typ
  | typ_bot  : typ
  | typ_rcd  : dec -> typ
  | typ_and  : typ -> typ -> typ
  | typ_sel  : avar -> typ_label -> typ
  | typ_bnd  : typ -> typ
  | typ_all  : typ -> typ -> typ
  | typ_con  : typs -> inits -> typ -> typ
(** We define a specialized version of lists to generate nicer induction
    principles
  - [typs_nil] represents a type declaraion [{A: S..T}];
  - [dec_trm a T] represents a field declaration [{a: T}] . *)
with typs : Set :=
  | typs_nil : typs
  | typs_cons : typ -> typs -> typs
(**
  - [dec_typ A S T] represents a type declaraion [{A: S..T}];
  - [dec_trm a T] represents a field declaration [{a: T}] . *)
with dec : Set :=
  | dec_typ  : typ_label -> typ -> typ -> dec
  | dec_trm  : trm_label -> typ -> typ -> dec.
Hint Constructors typ typs dec : core.

(** *** Mutual Induction Principles *)
Scheme typ_mut  := Induction for typ Sort Prop
with   typs_mut := Induction for typs Sort Prop
with   dec_mut  := Induction for dec Sort Prop.
Combined Scheme typ_mutind from typ_mut, typs_mut, dec_mut.


(* ************************************************************************** *)
(** ** Type Lists are List Like *)
Fixpoint typs_to_list (Ts : typs) : list typ :=
  match Ts with
  | typs_nil => nil
  | typs_cons T Ts' => (T :: typs_to_list Ts')%list
  end.

Instance TypsToList : ToList typ typs := typs_to_list.
Arguments TypsToList _ /.

Fixpoint typs_of_list (xs : list typ) : typs :=
  match xs with
  | nil => typs_nil
  | (T :: Ts')%list => typs_cons T (typs_of_list Ts')
  end.

Instance TypsOfList : OfList typ typs := typs_of_list.
Arguments TypsOfList _ /.

Instance TypsListLike : ListLike TypsToList TypsOfList.
Proof.
  split; unfold to_list, of_list.
  - intros Ts. induction Ts; simpl in *; congruence.
  - intros xs. induction xs; simpl in *; congruence.
Defined.

(** *** Autorewrite lemmas *)
Lemma rewrite_typs_to_list : TypsToList = to_list.
Proof. trivial. Qed.
Lemma rewrite_typs_of_list : TypsOfList = of_list.
Proof. trivial. Qed.
Hint Rewrite
     rewrite_typs_to_list rewrite_typs_of_list : typ_db.

Ltac fold_typ_list_like :=
  repeat change typs_to_list with (@to_list typ typs TypsToList);
  repeat change typs_of_list with (@of_list typ typs TypsOfList).


(* ************************************************************************** *)
(** ** Types, Type Lists and Declarations are Abstract Syntax *)
Fixpoint open_rec_typ (k: nat) (u: var) (T: typ) {struct T} : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (open_rec_dec k u D)
  | typ_and T1 T2  => typ_and (open_rec_typ k u T1)
                             (open_rec_typ k u T2)
  | typ_sel x L    => typ_sel (open_rec k u x) L
  | typ_bnd T      => typ_bnd (open_rec_typ (S k) u T)
  | typ_all T1 T2  => typ_all (open_rec_typ k u T1)
                             (open_rec_typ (S k) u T2)
  | typ_con Ts is' T =>
    typ_con
      (open_rec_typs k u Ts)
      is'
      (open_rec_typ (S (length_s Ts) + k) u T)
  (* avar_n 0 refers to self/this,
     avar_n 1 ... length Ts refers to arguments *)
  end with
open_rec_typs (k : nat) (u : var) (Ts : typs) : typs :=
  match Ts with
  | typs_nil => typs_nil
  | typs_cons T Ts =>
    typs_cons (open_rec_typ k u T)
              (open_rec_typs k u Ts)
  end with
open_rec_dec (k: nat) (u: var) (D: dec): dec :=
  match D with
  | dec_typ L T U => dec_typ L (open_rec_typ k u T)
                            (open_rec_typ k u U)
  | dec_trm m T U => dec_trm m (open_rec_typ k u T)
                            (open_rec_typ k u U)
  end.
Instance TypOpenable : Openable typ := open_rec_typ.
Instance TypsOpenable : Openable typs := open_rec_typs.
Instance DecOpenable : Openable dec := open_rec_dec.
Ltac fold_typ_open_rec :=
  change (open_rec_dec) with (@open_rec dec DecOpenable);
  change (open_rec_typs) with (@open_rec typs TypsOpenable);
  change (open_rec_typ) with (@open_rec typ TypOpenable).

Fixpoint fv_typ (T: typ) : vars :=
  match T with
  | typ_top        => \{}
  | typ_bot        => \{}
  | typ_rcd D      => (fv_dec D)
  | typ_and T U    => (fv_typ T) \u (fv_typ U)
  | typ_sel x L    => (fv x)
  | typ_bnd T      => (fv_typ T)
  | typ_all T1 T2  => (fv_typ T1) \u (fv_typ T2)
  | typ_con Ts is' T   => (fv_typs Ts) \u (fv_typ T)
  end with
fv_typs (Ts : typs) : vars :=
  match Ts with
  | typs_nil => \{}
  | typs_cons T Ts => (fv_typ T) \u (fv_typs Ts)
  end with
fv_dec (D: dec) : vars :=
  match D with
  | dec_typ L T U => (fv_typ T) \u (fv_typ U)
  | dec_trm m T U => (fv_typ T) \u (fv_typ U)
  end.
Instance TypFreeVar : FreeVar typ := fv_typ.
Instance TypsFreeVar : FreeVar typs := fv_typs.
Instance DecFreeVar : FreeVar dec := fv_dec.
Ltac fold_typ_fv :=
  change (fv_dec) with (@fv dec DecFreeVar);
  change (fv_typs) with (@fv typs TypsFreeVar);
  change (fv_typ) with (@fv typ TypFreeVar).

Fixpoint subst_typ (z: var) (u: var) (T: typ) { struct T } : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (subst_dec z u D)
  | typ_and T1 T2  => typ_and (subst_typ z u T1) (subst_typ z u T2)
  | typ_sel x L    => typ_sel (subst_var z u x) L
  | typ_bnd T      => typ_bnd (subst_typ z u T)
  | typ_all T U    => typ_all (subst_typ z u T) (subst_typ z u U)
  | typ_con Ts is' T   => typ_con (subst_typs z u Ts) is' (subst_typ z u T)
  end with
subst_typs (z: var) (u: var) (Ts: typs) { struct Ts } : typs :=
  match Ts with
  | typs_nil => typs_nil
  | typs_cons T Ts => typs_cons (subst_typ z u T) (subst_typs z u Ts)
  end with
subst_dec (z: var) (u: var) (D: dec) { struct D } : dec :=
  match D with
  | dec_typ L T U => dec_typ L (subst_typ z u T) (subst_typ z u U)
  | dec_trm L T U => dec_trm L (subst_typ z u T) (subst_typ z u U)
  end.
Instance TypSubstVar : SubstVar typ := subst_typ.
Instance TypsSubstVar : SubstVar typs := subst_typs.
Instance DecSubstVar : SubstVar dec := subst_dec.
Ltac fold_typ_subst :=
  change (subst_dec) with (@subst_var dec DecSubstVar);
  change (subst_typs) with (@subst_var typs TypsSubstVar);
  change (subst_typ) with (@subst_var typ TypSubstVar).

Instance TypAbstractSyntax :
  AbstractSyntax TypOpenable TypFreeVar TypSubstVar := {}.
Instance TypsAbstractSyntax :
  AbstractSyntax TypsOpenable TypsFreeVar TypsSubstVar := {}.
Instance DecAbstractSyntax :
  AbstractSyntax DecOpenable DecFreeVar DecSubstVar := {}.
Ltac fold_typ_abs :=
  fold_typ_list_like;
  fold_typ_open_rec; fold_typ_fv; fold_typ_subst.

(** *** Autorewrite lemmas *)
Lemma rewrite_open_rec_typ : open_rec_typ = open_rec.
Proof. trivial. Qed.
Lemma rewrite_open_rec_typs : open_rec_typs = open_rec.
Proof. trivial. Qed.
Lemma rewrite_open_rec_dec : open_rec_dec = open_rec.
Proof. trivial. Qed.
Lemma rewrite_fv_typ : fv_typ = fv.
Proof. trivial. Qed.
Lemma rewrite_fv_typs : fv_typs = fv.
Proof. trivial. Qed.
Lemma rewrite_fv_dec : fv_dec = fv.
Proof. trivial. Qed.
Lemma rewrite_subst_typ : subst_typ = subst_var.
Proof. trivial. Qed.
Lemma rewrite_subst_typs : subst_typs = subst_var.
Proof. trivial. Qed.
Lemma rewrite_subst_dec : subst_dec = subst_var.
Proof. trivial. Qed.
Hint Rewrite
     rewrite_open_rec_typ rewrite_fv_typ rewrite_subst_typ
     rewrite_open_rec_typs rewrite_fv_typs rewrite_subst_typs
     rewrite_open_rec_dec rewrite_fv_dec rewrite_subst_dec : typ_db.

(* ************************************************************************** *)
(** ** Declarations are labeled *)
Instance DecLabelOf : LabelOf dec :=
  fun D =>
      match D with
      | dec_typ L _ _ => label_typ L
      | dec_trm m _ _ => label_trm m
      end.


(* ************************************************************************** *)
(** ** Types, Type Lists and Declarations Satisfy Syntax Lemmas *)
(** We will prove that the operations on Types, Type Lists and Declarations are
    lifted from locally nameless variables. The syntax lemmas will then by
    automatically lifted from the syntax lemmas of locally nameless variables
    through the type class mechanism *)

(** *** Collect Variables in Types *)
Fixpoint collect_typ {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (T: typ) : C :=
  match T with
  | typ_top        => df
  | typ_bot        => df
  | typ_rcd D      => (collect_dec df f comb D)
  | typ_and T U    => comb (collect_typ df f comb T) (collect_typ df f comb U)
  | typ_sel x L    => (f x)
  | typ_bnd T      => (collect_typ df f comb T)
  | typ_all T1 T2  => comb (collect_typ df f comb T1) (collect_typ df f comb T2)
  | typ_con Ts is' T => comb (collect_typs df f comb Ts) (collect_typ df f comb T)
  end with
collect_typs {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (Ts: typs) : C :=
  match Ts with
  | typs_nil => df
  | typs_cons T Ts => comb (collect_typ df f comb T) (collect_typs df f comb Ts)
  end with
collect_dec {C: Type} (df : C) (f : avar -> C) (comb: C -> C -> C) (D: dec) : C :=
  match D with
  | dec_typ L T U => comb (collect_typ df f comb T) (collect_typ df f comb U)
  | dec_trm m T U => comb (collect_typ df f comb T) (collect_typ df f comb U)
  end.

Instance TypCollect : Collect AvarAbstractSyntax TypAbstractSyntax
  := @collect_typ.

Instance TypsCollect : Collect AvarAbstractSyntax TypsAbstractSyntax :=
  @collect_typs.

Instance DecCollect : Collect AvarAbstractSyntax DecAbstractSyntax :=
  @collect_dec.

Ltac fold_typ_collect :=
  change (@collect_typ) with (@collect
            avar AvarOpenable AvarFreeVar AvarSubstVar AvarAbstractSyntax
            typ TypOpenable TypFreeVar TypSubstVar TypAbstractSyntax
            TypCollect);
  change (@collect_typs) with (@collect
            avar AvarOpenable AvarFreeVar AvarSubstVar AvarAbstractSyntax
            typs TypsOpenable TypsFreeVar TypsSubstVar TypsAbstractSyntax
            TypsCollect);
  change (@collect_dec) with (@collect
            avar AvarOpenable AvarFreeVar AvarSubstVar AvarAbstractSyntax
            dec DecOpenable DecFreeVar DecSubstVar DecAbstractSyntax
            DecCollect).

(** *** Autorewrite lemmas *)
Lemma rewrite_collect_typ : forall C, @collect_typ C = collect.
Proof. trivial. Qed.
Lemma rewrite_collect_typs : forall C, @collect_typs C = collect.
Proof. trivial. Qed.
Lemma rewrite_collect_dec : forall C, @collect_dec C = collect.
Proof. trivial. Qed.
Hint Rewrite
     rewrite_collect_typ rewrite_collect_typs rewrite_collect_dec : typ_db.

(** *** Sanity for Collecting Variables in Types, Type Lists and Declarations *)
Instance TypsListLikeCollect : ListLikeCollect TypCollect TypsCollect.
Proof.
  hnf. intros. induction a; auto.
  change (collect df f comb (typs_cons t a))
    with (comb (collect df f comb t) (collect df f comb a)).
  rewrite IHa; auto.
Qed.

Lemma collect_compose_typ_typs_dec :
  forall {C D} (f : C -> D) g comb1 comb2 i,
    (forall x y, f (comb1 x y) = comb2 (f x) (f y)) ->
    (forall (T : typ),
        (f ∘ collect i g comb1) T = collect (f i) (f ∘ g) comb2 T) /\
    (forall (Ts : typs),
        (f ∘ collect i g comb1) Ts = collect (f i) (f ∘ g) comb2 Ts) /\
    (forall (D : dec),
        (f ∘ collect i g comb1) D = collect (f i) (f ∘ g) comb2 D).
Proof.
  intros.
  apply typ_mutind;
    unfold compose, collect, DecCollect, TypCollect, TypsCollect;
    simpls; try congruence.
Qed.

Lemma collect_reflect_typ_typs_dec :
  forall P p,
    (forall b, (P b) <-> (p b) = true) ->
    forall bl,
      (forall T, ((collect_typ (Is_true bl) P or T)
             <-> (collect_typ bl p orb T) = true)) /\
      (forall Ts, ((collect_typs (Is_true bl) P or Ts)
              <-> (collect_typs bl p orb Ts) = true)) /\
      (forall D, ((collect_dec (Is_true bl) P or D)
             <-> (collect_dec bl p orb D) = true)).
Proof.
  intros P p H bl.
  apply typ_mutind; simpl; auto 2 using reflect_iff; unfold iff;
    auto 3 using Is_true_eq_left, Is_true_eq_true; split;
      destruct_ands; intros;
        destruct_orbs; destruct_ors; auto.
Qed.

Local Ltac solve_collect_compose :=
  unfold compose; apply fun_ext_dep;
  apply collect_compose_typ_typs_dec; auto.

Local Ltac solve_collect_reflect :=
  apply collect_reflect_typ_typs_dec; auto.

Local Ltac solve_collect_sanity :=
  hnf; intros; solve [solve_collect_compose || solve_collect_reflect].

Instance TypCollectCompose : CollectCompose TypCollect.
Proof. solve_collect_sanity. Qed.

Instance TypCollectReflect : CollectReflect TypCollect.
Proof. solve_collect_sanity. Qed.

Instance TypsCollectCompose : CollectCompose TypsCollect.
Proof. solve_collect_sanity. Qed.

Instance TypsCollectReflect : CollectReflect TypsCollect.
Proof. solve_collect_sanity. Qed.

Instance DecCollectCompose : CollectCompose DecCollect.
Proof. solve_collect_sanity. Qed.

Instance DecCollectReflect : CollectReflect DecCollect.
Proof. solve_collect_sanity. Qed.

(** *** Transform Variables in Types *)
Fixpoint transform_typ (f : avar -> nat -> avar) (T : typ) (n : nat) : typ :=
  match T with
  | typ_top        => typ_top
  | typ_bot        => typ_bot
  | typ_rcd D      => typ_rcd (transform_dec f D n)
  | typ_and T1 T2  => typ_and (transform_typ f T1 n) (transform_typ f T2 n)
  | typ_sel x L    => typ_sel (f x n) L
  | typ_bnd T      => typ_bnd (transform_typ f T (S n))
  | typ_all T1 T2  => typ_all (transform_typ f T1 n) (transform_typ f T2 (S n))
  | typ_con Ts is' T   => typ_con
                       (transform_typs f Ts n) is'
                       (transform_typ f T (S (length_s Ts) + n))
  end with
transform_typs (f : avar -> nat -> avar) (Ts : typs) (n : nat) : typs :=
  match Ts with
  | typs_nil => typs_nil
  | typs_cons T Ts =>
    typs_cons (transform_typ f T n) (transform_typs f Ts n)
  end with
transform_dec (f : avar -> nat -> avar) (D : dec) (n : nat) : dec :=
  match D with
  | dec_typ L T U => dec_typ L (transform_typ f T n) (transform_typ f U n)
  | dec_trm m T U => dec_trm m (transform_typ f T n) (transform_typ f U n)
  end.

Instance TypTransform : Transform AvarAbstractSyntax TypAbstractSyntax :=
  @transform_typ.

Instance TypsTransform : Transform AvarAbstractSyntax TypsAbstractSyntax :=
  @transform_typs.

Instance DecTransform : Transform AvarAbstractSyntax DecAbstractSyntax :=
  @transform_dec.
Ltac fold_typ_transform :=
  change (@transform_typ) with (@transform
            avar AvarOpenable AvarFreeVar AvarSubstVar AvarAbstractSyntax
            typ TypOpenable TypFreeVar TypSubstVar TypAbstractSyntax
            TypTransform);
  change (@transform_typs) with (@transform
            avar AvarOpenable AvarFreeVar AvarSubstVar AvarAbstractSyntax
            typs TypsOpenable TypsFreeVar TypsSubstVar TypsAbstractSyntax
            TypsTransform);
  change (@transform_dec) with (@transform
            avar AvarOpenable AvarFreeVar AvarSubstVar AvarAbstractSyntax
            dec DecOpenable DecFreeVar DecSubstVar DecAbstractSyntax
            DecTransform).
Local Ltac fold_typ_all :=
  repeat (fold_typ_abs; fold_typ_collect; fold_typ_transform).
Local Ltac sympl_typ :=
  simpls; fold_typ_all.

(** *** Autorewrite lemmas *)
Lemma rewrite_transform_typ : transform_typ = transform.
Proof. trivial. Qed.
Lemma rewrite_transform_typs : transform_typs = transform.
Proof. trivial. Qed.
Lemma rewrite_transform_dec : transform_dec = transform.
Proof. trivial. Qed.
Hint Rewrite
     rewrite_transform_typ rewrite_transform_typs rewrite_transform_dec : typ_db.

(** *** Sanity for Transforming Variables *)
Lemma transform_id_typ_typs_dec :
  (forall (T : typ) n, transform (ignore_second id) T n = T) /\
  (forall (Ts : typs) n, transform (ignore_second id) Ts n = Ts) /\
  (forall (D : dec) n, transform (ignore_second id) D n = D).
Proof.
  unfold ignore_second, id, transform; simpls.
  apply typ_mutind; simpl; intros; try f_equal; auto.
Qed.

Instance TypsListLikeTransform : ListLikeTransform TypTransform TypsTransform.
Proof.
  hnf. unfold map_f.
  intros. induction a; auto.
  sympl_typ. rewrite <- IHa. auto.
Qed.

Lemma transform_compose_typ_typs_dec :
  (forall (T : typ) n f g, ((transform f) ∘∘ (transform g)) T n = transform (f ∘∘ g) T n) /\
  (forall (Ts : typs) n f g, ((transform f) ∘∘ (transform g)) Ts n = transform (f ∘∘ g) Ts n) /\
  (forall (D : dec) n f g, ((transform f) ∘∘ (transform g)) D n = transform (f ∘∘ g) D n).
Proof.
  unfold compose12, transform; simpls.
  apply typ_mutind; simpl; intros;
  repeat
    match goal with
    | [ H : forall n f g, _ = _ |- _] => rewrite <- H
    end; auto.
  pose proof transform_length_s. simpl in H1.
  rewrite ? H1; auto.
Qed.

Local Ltac solve_transform_sanity :=
  hnf; try apply transform_id_typ_typs_dec;
    intros; intros_fun_ext; apply transform_compose_typ_typs_dec.

Instance TypTransformId : TransformId TypTransform.
Proof. solve_transform_sanity. Qed.

Instance TypsTransformId : TransformId TypsTransform.
Proof. solve_transform_sanity. Qed.

Instance DecTransformId : TransformId DecTransform.
Proof. solve_transform_sanity. Qed.

Instance TypTransformCompose : TransformCompose TypTransform.
Proof. solve_transform_sanity. Qed.

Instance TypsTransformCompose : TransformCompose TypsTransform.
Proof. solve_transform_sanity. Qed.

Instance DecTransformCompose : TransformCompose DecTransform.
Proof. solve_transform_sanity. Qed.


(** *** Sanity for Collecting and Transforming Variables *)
Lemma collect_transform_typ_typs_dec :
  (forall (T : typ) bl p f g,
      (collect bl p andb T) = true -> transform (dec_apply p f g) T = transform f T) /\
  (forall (Ts : typs) bl p f g,
      (collect bl p andb Ts) = true -> transform (dec_apply p f g) Ts = transform f Ts) /\
  (forall (D : dec) bl p f g,
      (collect bl p andb D) = true -> transform (dec_apply p f g) D = transform f D).
Proof.
  apply typ_mutind; simpl; auto 2; intros; destruct_andbs; destruct_ands;
    repeat
      match goal with
      | [ H : forall bl p f g,
            _ = true ->
            ?transform (dec_apply p f g) ?t = ?transform f ?t |- _] =>
        erewrite H by eauto
      end; auto.
  unfold dec_apply; rewrite H; auto.
Qed.

Instance TypCollectTransform :
  CollectTransform TypCollect TypTransform.
Proof. hnf; intros; eapply collect_transform_typ_typs_dec; eauto. Qed.

Instance TypsCollectTransform :
  CollectTransform TypsCollect TypsTransform.
Proof. hnf; intros; eapply collect_transform_typ_typs_dec; eauto. Qed.

Instance DecCollectTransform :
  CollectTransform DecCollect DecTransform.
Proof. hnf; intros; eapply collect_transform_typ_typs_dec; eauto. Qed.


(** *** Operations are lifted from operations on Variables *)
Lemma fv_collect_typ_typs_dec :
  (forall (T : typ), fv T = collect (\{}) fv (@union var) T) /\
  (forall (Ts : typs), fv Ts = collect (\{}) fv (@union var) Ts) /\
  (forall (D : dec), fv D = collect (\{}) fv (@union var) D).
Proof.
  apply typ_mutind; sympl_typ; try congruence.
Qed.

Lemma open_transform_typ_typs_dec :
  (forall (T : typ) n x, (open_depth_rec n x) T = transform (open_depth_rec n x) T) /\
  (forall (Ts : typs) n x, (open_depth_rec n x) Ts = transform (open_depth_rec n x) Ts) /\
  (forall (D : dec) n x, (open_depth_rec n x) D = transform (open_depth_rec n x) D).
Proof.
  unfold open_depth_rec.
  apply typ_mutind; sympl_typ; intros; repeat (apply fun_ext_dep; intro);
    repeat match goal with
           | [ H : forall _ _, _ = _ |- _] => rewrite <- H
           end;
    rewrite ? Nat.add_succ_r;
    auto.
  rewrite Nat.add_shuffle3; auto.
Qed.

Lemma subst_transform_typ_typs_dec :
  (forall (T : typ) x y, (ignore_second (subst_var x y)) T
                = transform (ignore_second (subst_var x y)) T) /\
  (forall (Ts : typs) x y, (ignore_second (subst_var x y)) Ts
                = transform (ignore_second (subst_var x y)) Ts) /\
  (forall (D : dec) x y, (ignore_second (subst_var x y)) D
                = transform (ignore_second (subst_var x y)) D).
Proof.
  unfold ignore_second.
  apply typ_mutind; sympl_typ; intros; intros_fun_ext;
    repeat match goal with
           | [ H : forall _ _, _ = _ |- _] => rewrite <- H
           end;
    unfold ignore_second; simpl; auto.
Qed.

Local Ltac solve_transform_syntax :=
  hnf; intros; (apply fun_ext_dep; intro);
    try apply fv_collect_typ_typs_dec;
    try apply open_transform_typ_typs_dec;
    try apply subst_transform_typ_typs_dec.

Instance TypFvCollect : FvCollect TypCollect.
Proof. solve_transform_syntax. Qed.

Instance TypsFvCollect : FvCollect TypsCollect.
Proof. solve_transform_syntax. Qed.

Instance DecFvCollect : FvCollect DecCollect.
Proof. solve_transform_syntax. Qed.

Instance TypOpenTransform : OpenTransform TypTransform.
Proof. solve_transform_syntax. Qed.

Instance TypsOpenTransform : OpenTransform TypsTransform.
Proof. solve_transform_syntax. Qed.

Instance DecOpenTransform : OpenTransform DecTransform.
Proof. solve_transform_syntax. Qed.

Instance TypSubstTransform : SubstTransform TypTransform.
Proof. solve_transform_syntax. Qed.

Instance TypsSubstTransform : SubstTransform TypsTransform.
Proof. solve_transform_syntax. Qed.

Instance DecSubstTransform : SubstTransform DecTransform.
Proof. solve_transform_syntax. Qed.

(** Additional Lemmas that are not lifted automatically *)
Lemma fv_open_typ_dec_cases : forall x,
    (forall (T : typ) n,
        fv (open_rec n x T) = fv T \/
        fv (open_rec n x T) = \{ x} \u fv T) /\
    (forall (Ts : typs) n,
        fv (open_rec n x Ts) = fv Ts \/
        fv (open_rec n x Ts) = \{ x} \u fv Ts) /\
    (forall (D : dec) n,
        fv (open_rec n x D) = fv D
        \/ fv (open_rec n x D) = \{ x} \u fv D).
Proof.
  intros x.
  apply typ_mutind; sympl_typ; auto; intros;
    repeat apply union_eq_cases; auto using fv_open_cases.
Qed.

Instance TypFvOpenCases : FvOpenCases TypAbstractSyntax.
Proof.
  hnf. apply fv_open_typ_dec_cases.
Qed.

Instance TypsFvOpenCases : FvOpenCases TypsAbstractSyntax.
Proof.
  hnf. apply fv_open_typ_dec_cases.
Qed.

Instance DecFvOpenCases : FvOpenCases DecAbstractSyntax.
Proof.
  hnf. apply fv_open_typ_dec_cases.
Qed.

Lemma fv_typs_app_distr: forall (Ts Ts' : typs),
    fv (Ts ++ Ts') = fv Ts \u fv Ts'.
Proof.
  induction Ts as [ | T Ts IHTs]; intros; unfold app_s; sympl_typ; auto.
  - rewrite union_empty_l. rewrite to_list_of_list. auto.
  - rewrite <- union_assoc. rewrite <- IHTs. auto.
Qed.

Lemma init_decide : forall (i j : init_typ), i = j \/ i <> j.
Proof.
  destruct i; destruct j; try(solve[left; congruence | right; congruence]).
Qed.
