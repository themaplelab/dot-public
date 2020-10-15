(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra Vars Terms Items.

(* ************************************************************************** *)
(** * Abstract Machine
A configuration of the idot abstract machine consists of a control term [t], a
stack of frames [Fs], and a heap [Sigma]. *)

(** A heap, maps locations to heap items. *)
Notation heap := (env item).

(** Frames represent continuations of exeucting let bindings or calling
constructors.
[frame_let t] represents a let-frame [let x = [ ] in t]
[frame_ret x] represents a return-frame [return x] *)
Inductive frame : Set :=
  | frame_let : trm -> frame
  | frame_ret : var -> frame.

(** Frame stacks represent evaluation contexts *)
Notation stack := (list frame).

(** Configurations of the abstract machine *)
Notation config := (trm * stack * heap)%type.
Notation "t ; Fs ; Sigma"
  := (t, Fs, Sigma) (at level 39, Fs, Sigma at level 38) : syntax_scope.
