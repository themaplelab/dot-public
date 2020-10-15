(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Bool.Bool.
Require Import LibExtra DotTactics SyntaxClasses.
Require Import Vars TransformCollect Types Terms.

(* ************************************************************************** *)
(** * Heap Definitions
Heap definitions ([heap_def], [hd] and [heap_defs], [hds]):
  - [def_typ A T] represents a type-member definition [{A = T}];
  - [def_trm a] represents a field definition [{a = null}]; *)
Inductive heap_def : Set :=
  | heap_def_typ  : typ_label -> typ -> heap_def
  | heap_def_trm  : trm_label -> option var -> heap_def.

(**
  [heap_defs] represents a list of heap definitions that are part of an intersection
  - [nil] represents the empty list;
  - [cons hd hds] represents a concatenation of the definition [hd] to the definitions [hds]. *)
Notation heap_defs := (list heap_def).

(* ************************************************************************** *)
(** * Heap Items
Heap Items ([items] [h]):
  - [item_obj T hds] represents the object [nu(x:T)hds]; the variable [x] is free
    in [T] and [ds] and is interpreted as a pointer to the object itself;
  - [item_lit l] represents a literal allocated on the heap. *)

Inductive item : Set :=
  | item_obj : typ -> heap_defs -> item
  | item_lit : lit -> item.

(* ************************************************************************** *)
(** ** Converting Definitions To HeapDefinitions *)
Definition heap_def_of_def (d : def) : heap_def :=
  match d with
  | def_typ A T => heap_def_typ A T
  | def_trm a   => heap_def_trm a None
  end.

Definition heap_defs_of_defs (ds : defs) : heap_defs :=
  List.map heap_def_of_def ds.

(* ************************************************************************** *)
(** ** Heap Items are Abstract Syntax *)
Instance HeapDefLabelOf : LabelOf heap_def | 1 :=
  fun hd =>
      match hd with
      | heap_def_typ L _ => label_typ L
      | heap_def_trm m _ => label_trm m
      end.

(** *** Heap Definitions are Abstract Syntax *)
Definition fv_heap_def (hd: heap_def) : vars :=
  match hd with
  | heap_def_typ _ T        => (fv T)
  | heap_def_trm _ None     => \{}
  | heap_def_trm _ (Some x) => \{ x}
  end.
Instance HeapDefFreeVar : FreeVar heap_def := fv_heap_def.

Fixpoint open_rec_heap_def (k: nat) (u: var) (hd: heap_def)
         {struct hd} : heap_def :=
  match hd with
  | heap_def_typ L T     => heap_def_typ L (open_rec k u T)
  | heap_def_trm m opt_x => heap_def_trm m opt_x
  end.
Instance HeapDefOpenable : Openable heap_def := open_rec_heap_def.

Definition fv_item (v: item) : vars :=
  match v with
  | item_obj T hds    => (fv T) \u (fv hds)
  | item_lit l => (fv l)
  end.
Instance ItemFreeVar : FreeVar item := fv_item.

Definition subst_heap_def (z: var) (u: var) (hd: heap_def)
  : heap_def :=
  match hd with
  | heap_def_typ l t        => heap_def_typ l (subst_var z u t)
  | heap_def_trm l None     => heap_def_trm l None
  | heap_def_trm l (Some x) =>
    heap_def_trm l (Some (subst_fvar z u x))
  end.
Instance HeapDefSubstVar : SubstVar heap_def := subst_heap_def.

Instance HeapDefAbstractSyntax :
  AbstractSyntax HeapDefOpenable HeapDefFreeVar HeapDefSubstVar := {}.

(* TODO : is transform collect for heap_def worth it? *)
Instance HeapDefSubstLabel : SubstLabel HeapDefSubstVar HeapDefLabelOf.
Proof.
  hnf; intros. destruct d; try reflexivity.
  destruct o; simpl; reflexivity.
Qed.

Instance HeapDefSubstIntro : SubstIntro HeapDefAbstractSyntax.
Proof.
  hnf. destruct X; intros.
  - simpl in *. f_equal. apply subst_intro; auto.
  - destruct o; simpl in *; auto.
    f_equal. f_equal. unfold subst_fvar.
    cases_if; auto. exfalso. apply H.
    rewrite in_singleton; auto.
Qed.

Instance HeapDefsSubstIntro : SubstIntro (A:=heap_defs) ListAbstractSyntax.
Proof.
  hnf. induction X; intros; auto.
  simpl in H. apply notin_union in H. destruct H.
  change (fv_list X) with (fv X) in H0.
  specialize (IHX H0); clear H0.
  change (open_rec n y (a :: X)%list)
    with (open_rec n y a :: open_rec n y X)%list.
  change (open_rec n x (a :: X)%list /[ x -> y]) with
      ((open_rec n x a /[ x -> y]) :: ((open_rec n x X) /[ x -> y]))%list.
  rewrite IHX; f_equal.
  auto using subst_intro.
Qed.

Definition open_rec_item (n: nat) (x: var) (v: item) : item :=
  match v with
  | item_obj T ds    => item_obj (open_rec n x T)
                              (open_rec (S n) x ds)
  | item_lit l => item_lit (open_rec n x l)
  end.
Instance ItemOpenable : Openable item := open_rec_item.

Definition subst_item x y (v: item) : item :=
  match v with
  | item_obj T ds    => item_obj (subst_var x y T) (subst_var x y ds)
  | item_lit l => item_lit (subst_var x y l)
  end.
Instance ItemSubstVar : SubstVar item := subst_item.

Instance ItemAbstractSyntax :
  AbstractSyntax ItemOpenable ItemFreeVar ItemSubstVar := {}.

(** heap_def_of_def commutes with opening *)
Lemma heap_def_of_def_open_commut : forall n x d,
    open_rec n x (heap_def_of_def d)
    = heap_def_of_def (open_rec n x d).
Proof.
  destruct d; simpl; auto.
Qed.

Lemma heap_defs_of_defs_open_commut : forall n x ds,
    open_rec n x (heap_defs_of_defs ds)
    = heap_defs_of_defs (open_rec n x ds).
Proof.
  intros n x ds; gen n x; induction ds; auto.
  intros; simpl; fold_trm_abs;
    rewrite <- IHds, heap_def_of_def_open_commut; auto.
Qed.

Lemma heap_def_of_def_open_vars_commut : forall n xs d,
    open_rec_vars n xs (heap_def_of_def d)
    = heap_def_of_def (open_rec_vars n xs d).
Proof.
  intros n xs; gen n.
  induction xs as [| x xs IHxs]; intros; auto.
  simpl. rewrite <- IHxs, heap_def_of_def_open_commut.
  auto.
Qed.

Lemma heap_defs_of_defs_open_vars_commut : forall n xs d,
    open_rec_vars n xs (heap_defs_of_defs d)
    = heap_defs_of_defs (open_rec_vars n xs d).
Proof.
  intros n xs; gen n.
  induction xs as [| x xs IHxs]; intros; auto.
  simpl. rewrite <- IHxs, heap_defs_of_defs_open_commut.
  auto.
Qed.

Lemma label_neq_hds_label_neq : forall (lb : label) (a : def),
    lb <> label_of a ->
    label_of (heap_def_of_def a) <> lb.
Proof.
  unfold not. intros.
  apply H. destruct a.
  - simpl. simpl in H0. congruence.
  - simpl. simpl in H0. congruence.
Qed.

Lemma ds_labels_hasnt_hds_labels_hasnt : forall (ds : defs) (lb : label),
    labels_hasnt ds lb ->
    labels_hasnt (heap_defs_of_defs ds) lb.
Proof with eauto.
  induction ds.
  - intros. simpl. hnf. simpl...
  - intros. simpl in *.
    apply labels_hasnt_cons_inv in H. destruct_all.
    specialize (IHds lb H0).
    hnf. hnf in H0. simpl. hnf in IHds. unfold get_labeld in IHds.
    apply label_neq_hds_label_neq in H.
    case_if...
Qed.

Instance HeapDefOpenCommut : OpenCommut HeapDefOpenable.
Proof with eauto.
  hnf. intros.
  apply fun_ext_dep.
  intro hd.
  induction hd as [ l T| l t].
  - unfold "∘"; simpl.
    change (open_rec m x (open_rec n y T)) with
    (((open_rec m x) ∘ (open_rec n y)) T).
    rewrite open_commut by auto; auto.
  - unfold "∘". simpl.
    auto.
Qed.
