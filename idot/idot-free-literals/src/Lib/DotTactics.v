(** remove printing ~ *)

(** This proof uses the
    #<a href="http://www.chargueraud.org/softs/tlc/">TLC</a>#
    Coq library by Arthur Chargueraud. *)

Set Implicit Arguments.

Require Import Bool.
Require Import LibExtra.
Require String.
Export Coq.Strings.String.StringSyntax.

(** * Tactics *)

(** Tactics for naming cases in case analysis. *)

Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.

(** Invert Bindings *)
Ltac binds_eq :=
  match goal with
  | [Hb1: binds ?x _ ?G,
     Hb2: binds ?x _ ?G |- _] =>
     apply (binds_functional Hb1) in Hb2; inversions Hb2
  end.

Ltac binds_contra H1 H2 :=
  pose proof (binds_functional H1 H2); congruence.

Ltac binds_middle_subst :=
  match goal with
  | [ Hbi : binds ?x ?i (?D1 & ?x ~ ?i1 & ?D2), Hfr : ?x # ?D2 |- _ ] =>
    pose proof (binds_push_eq_inv (binds_concat_left_inv Hbi Hfr)); subst
  | [ Hbi : binds ?x ?i (?D1 & ?x ~ ?i1 & ?D2), Hfr : ?x # ?D1 & ?D2 |- _ ] =>
    pose proof (binds_push_eq_inv
                  (binds_concat_left_inv Hbi (notin_dom_concat_r Hfr))); subst
  end.

(** Automatically destruct premises *)
Ltac destruct_iffs :=
  repeat match goal with
  | [ H : ?A <-> ?B |- _ ] => destruct H
  end.

Ltac destruct_ands :=
  repeat match goal with
  | [ H : ?A /\ ?B |- _ ] => destruct H
  end.

Ltac destruct_ors :=
  repeat match goal with
  | [ H : ?A \/ ?B |- _ ] => destruct H
  end.

Ltac destruct_orbs :=
  repeat
    match goal with
    | [H : _ || _ = true |- _] => apply orb_prop in H
    | [|- _ || _ = true] => apply orb_true_intro
    end.

Ltac destruct_andbs :=
  repeat
    match goal with
    | [H : _ && _ = true |- _] => apply andb_prop in H
    | [|- _ && _ = true] => apply andb_true_intro
    end.

Ltac destruct_all :=
  repeat match goal with
  | [ H : exists x, _ |- _ ]  => destruct H
  | [ H : ?A /\ ?B |- _ ] => destruct H
  | [ H : ?A \/ ?B |- _ ] => destruct H
  end.

Ltac destruct_notin :=
  repeat match goal with
         | [ H: ?z \notin ?E1 \u ?E2 |- _ ] =>
           apply notin_union in H; destruct H
         end.

Ltac specialize_notins :=
  repeat match goal with
  | [ H : (?x \notin ?F ?y -> _), H' : ?x \notin ?F ?y |- _] =>
    specialize (H H')
  end.

Ltac repeat_split_right :=
  match goal with
  | |- ?A /\ ?B => split; repeat_split_right
  | _ => idtac
  end.

Ltac omega := Coq.omega.Omega.omega.
