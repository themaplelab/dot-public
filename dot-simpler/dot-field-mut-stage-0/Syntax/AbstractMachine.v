Set Implicit Arguments.

Require Import LibExtra Vars Terms.

(** A heap, maps locations to heap items. *)
Notation heap := (env item).

Inductive frame : Set :=
  | frame_let : trm -> frame.

Notation stack := (list frame).
Notation config := (trm * stack * heap)%type.
Notation "t ; s ; Sigma"
  := (t, s, Sigma) (at level 39, s, Sigma at level 38) : syntax_scope.
