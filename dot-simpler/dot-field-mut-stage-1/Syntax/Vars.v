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
