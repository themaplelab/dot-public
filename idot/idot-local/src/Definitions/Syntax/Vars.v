(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra DotTactics SyntaxClasses.

(* ************************************************************************** *)
(** * Locally Nameless Variables
    The proof represents variables using the
    #<a href="http://www.chargueraud.org/softs/ln/">locally nameless representation</a>#:
    - [avar_b n] represents a variable using the de Bruijn index [n];
    - [avar_f x] represents a free variable with name [x].
    de Bruijn-indexed variables represent bound variables, whereas named variables represent free variables
    that are in the evaluation context/type environment.  *)

Inductive avar : Set :=
  | avar_b : nat -> avar
  | avar_f : var -> avar.
Hint Constructors avar : core.
Notation avars := (list avar).


(* ************************************************************************** *)
(** ** Locally Nameless Variables are Abstract Syntax *)

Instance AvarOpenable : Openable avar :=
  fun n x a =>
    match a with
    | avar_b i => If n = i then avar_f x else avar_b i
    | avar_f y => avar_f y
    end.

Instance AvarFreeVar : FreeVar avar :=
  fun a =>
    match a with
    | avar_b i => \{}
    | avar_f x => \{x}
    end.

Instance AvarSubstVar : SubstVar avar :=
  fun (x: var) (y: var) (a: avar) =>
    match a with
    | avar_b i => avar_b i
    | avar_f z => (avar_f (If z = x then y else z))
    end.

Instance AvarAbstractSyntax :
  AbstractSyntax AvarOpenable AvarFreeVar AvarSubstVar := {}.

Instance AvarDecideFv : DecideFv AvarAbstractSyntax :=
  fun x a =>
    match a with
    | avar_b i => false
    | avar_f y => (If x = y then true else false)
    end.

Instance AvarClosing : Closing AvarAbstractSyntax :=
  fun (n : nat) (x : var) (a : avar) =>
    match a with
    | avar_b i => avar_b i
    | avar_f y => (If y = x then avar_b n else avar_f y)
    end.


(* ************************************************************************** *)
(** ** Tactics for Locally Nameless Variables *)
Local Ltac unfold_avar_syntax :=
  unfold AvarOpenable, AvarFreeVar, AvarSubstVar, AvarDecideFv, AvarClosing.

Local Ltac avar_unfold :=
  intros; unfold_syntax; unfold compose;
  unfold_avar_syntax; cbn in *.

Ltac destruct_avars :=
  repeat match goal with
         | [H : avar |- _ ] => destruct H
         end; cbn in *; repeat cases_if.

Ltac var_notin :=
  match goal with
  | [ H : ?x \notin \{ ?x} |- _ ] => exfalso; apply H; rewrite in_singleton; auto
  end.

Local Ltac unfold_rest :=
  unfold dec_apply, dec_notin_fv, ignore_second, id;
  cbn in *; repeat cases_if; cbn in *.

Local Ltac destruct_solve :=
  destruct_avars; unfold_rest; auto; try var_notin.

Local Ltac avar_solver :=
  avar_unfold; destruct_solve.

Local Ltac avar_fun_ext_solver :=
  avar_unfold;
  apply fun_ext_dep; intros a;
  destruct_solve.

Local Ltac avar_fun_ext_2_solver :=
  avar_unfold;
  apply fun_ext_dep; intros a;
  apply fun_ext_dep; intros m;
  destruct_solve.


(* ************************************************************************** *)
(** ** Locally Nameless Variables Satisfies Syntax Lemmas *)
Instance AvarReflectFv : ReflectFv AvarDecideFv.
Proof.
  hnf; avar_solver; constructor;
    try rewrite ? in_empty, ? in_singleton;
    intros; try congruence; contradiction.
Qed.

Instance AvarOpenClose : OpenClose AvarClosing.
Proof.
  hnf; avar_fun_ext_solver.
Qed.

Instance AvarCloseOpen : CloseOpen AvarClosing.
Proof.
  hnf; avar_fun_ext_solver.
Qed.

Instance AvarSubstOpenClose : SubstOpenClose AvarClosing.
Proof.
  hnf; avar_fun_ext_solver.
Qed.

Instance AvarOpenTwice : OpenTwice AvarOpenable.
Proof.
  hnf; avar_fun_ext_solver.
Qed.

Instance AvarOpenCommut : OpenCommut AvarOpenable.
Proof.
  hnf; avar_fun_ext_solver.
Qed.

Lemma avar_open_commut : forall (m n : nat) (x y : var) (a : avar),
    m <> n ->
    open_rec m x (open_rec n y a) = open_rec n y (open_rec m x a).
Proof.
  intros. destruct_solve.
Qed.

Instance AvarSubstFresh : SubstFresh AvarAbstractSyntax.
Proof.
  hnf; avar_solver.
Qed.

Instance AvarSubstOpenCommut : SubstOpenCommut AvarAbstractSyntax.
Proof.
  hnf; avar_solver.
Qed.

Instance AvarFvOpenCases : FvOpenCases AvarAbstractSyntax.
Proof.
  hnf; avar_solver.
Qed.

Instance AvarCloseUnbound : CloseUnbound AvarClosing.
Proof.
  hnf; avar_solver.
Qed.

Instance AvarClosingInner : ClosingInner AvarReflectFv AvarClosing.
Proof.
  hnf; avar_fun_ext_2_solver.
Qed.

Instance AvarSubstitutionInner : SubstitutionInner AvarReflectFv.
Proof.
  hnf; avar_fun_ext_2_solver.
Qed.

(** The rest of the lemmas are automatically satisfied as a consequence of
    [AvarClosingUnbound] *)


(* ************************************************************************** *)
(** ** Named Variables Corresponding to Locally Nameless Variables *)
Inductive vars_of_avars : list var -> list avar -> Prop :=
| vars_of_avars_nil : vars_of_avars nil nil
| vars_of_avars_cons : forall x vs avs,
    vars_of_avars vs avs ->
    vars_of_avars (cons x vs) (cons (avar_f x) avs).


(* ************************************************************************** *)
(** ** Lemmas about Variable Correspondence *)
Lemma vars_of_avars_app_l : forall xs ys avs,
    vars_of_avars (xs ++ ys) avs ->
    exists avs1 avs2,
      avs = (avs1 ++ avs2)%list /\
      vars_of_avars xs avs1 /\
      vars_of_avars ys avs2.
Proof.
  induction xs; intros; simpl in *.
  - exists (@nil avar) avs; simpl; repeat_split_right; auto; constructor.
  - inversions H. apply IHxs in H3. destruct H3 as [avs1 [avs2 H]].
    destruct_all; subst. exists (avar_f a :: avs1)%list avs2.
    repeat_split_right; auto; try constructor; trivial.
Qed.

Lemma vars_of_avars_app_r : forall avs1 avs2 xs,
    vars_of_avars xs (avs1 ++ avs2) ->
    exists ys zs,
      xs = (ys ++ zs)%list /\
      vars_of_avars ys avs1 /\
      vars_of_avars zs avs2.
Proof.
  induction avs1; intros; simpl in *.
  - exists (@nil var) xs; simpl; repeat_split_right; auto; constructor.
  - inversions H. apply IHavs1 in H2. destruct H2 as [ys [zs H]].
    destruct_all; subst. exists (x :: ys)%list zs.
    repeat_split_right; auto; try constructor; trivial.
Qed.

Lemma length_vars_of_avars : forall xs avs,
    vars_of_avars xs avs ->
    length xs = length avs.
Proof.
  intros xs avs H; induction H; simpls; eauto.
Qed.

Lemma subst_vars_of_avars: forall x y zs avs,
  vars_of_avars zs avs ->
  vars_of_avars (List.map (subst_fvar x y) zs) (subst_var x y avs).
Proof.
  intros x y zs avs H. induction H.
  - constructor.
  - simpls. constructor. auto.
Qed.

Lemma vars_of_avars_eq : forall avs xs ys,
    vars_of_avars xs avs ->
    vars_of_avars ys avs ->
    xs = ys.
Proof.
  induction avs; intros xs ys H H1;
    inversions H; inversions H1; auto using f_equal.
Qed.

(* ************************************************************************** *)
(** We can collect and transform variables in lists of Locally Nameless
    Variables *)
Require Import TransformCollect.
Instance AvarsCollect : Collect AvarAbstractSyntax ListAbstractSyntax :=
  fun {C} df f comb => List.fold_right (fun a acc => comb (f a) acc) df.

Instance AvarsCollectCompose : CollectCompose AvarsCollect.
Proof.
  hnf.
  intros. unfold compose, collect; simpl.
  apply fun_ext_dep; intro xs. induction xs; auto.
  simpl. rewrite <- IHxs, H; auto.
Qed.

Instance AvarsCollectReflect : CollectReflect AvarsCollect.
Proof.
  hnf.
  intros. unfold collect, AvarsCollect; simpl. induction a.
  - intros. split; simpl; auto using Bool.Is_true_eq_true, Bool.Is_true_eq_left.
  - simpl.
    assert (P a <-> p a = true) by auto.
    split; intros; destruct_iffs; destruct_orbs; destruct_ors; auto.
Qed.

Instance AvarsFvCollect : FvCollect AvarsCollect.
Proof. reflexivity. Qed.

Instance AvarsTransform : Transform AvarAbstractSyntax ListAbstractSyntax :=
  fun f a n => List.map (fun b => (f b n)) a.

Instance AvarsOpenTransform : OpenTransform AvarsTransform.
Proof.
  hnf; intros; reflexivity.
Qed.

Instance AvarsSubstTransform : SubstTransform AvarsTransform.
Proof.
  hnf; intros; reflexivity.
Qed.

Instance AvarsTransformId : TransformId AvarsTransform.
Proof.
  hnf; unfold compose12, transform, ignore_second, id; simpl; intros.
  induction x; simpl; congruence.
Qed.

Instance AvarsTransformCompose : TransformCompose AvarsTransform.
Proof.
  hnf; unfold compose12, transform, ignore_second, id; simpl; intros.
  intros_fun_ext. induction x; simpl; congruence.
Qed.

Instance AvarsCollectTransform :
  CollectTransform AvarsCollect AvarsTransform.
Proof.
  hnf; unfold collect, dec_apply; simpl.
  intros. intros_fun_ext.
  induction a; cbn in *; destruct_andbs; destruct_ands; auto.
  unfold transform, AvarsTransform in IHa.
  rewrite H, IHa; auto.
Qed.

Instance AvarsFvOpenCases : FvOpenCases ListAbstractSyntax.
Proof.
  hnf; intros.
  induction a; repeat apply union_eq_cases; auto using fv_open_cases.
Qed.
