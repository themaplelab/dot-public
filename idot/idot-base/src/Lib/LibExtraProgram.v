(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Program.Basics.
From TLC Require Import LibAxioms.

Definition ignore_second {A B C : Type} (f : A -> C) (x : A) (n : B) := f x.

Definition compose12 {A B C D : Type} (g : B -> D -> C) (f : A -> D -> B) (x : A) (n : D) :=
  g (f x n) n.

Notation " g ∘∘ f "
  := (compose12 g f) (at level 40, left associativity) : program_scope.

Hint Unfold ignore_second compose12 : core.

Open Scope program_scope.

Lemma fold_compose : forall {A B C : Type} (g : B -> C) (f : A -> B) x,
    g (f x) = (g ∘ f) x.
Proof. auto. Qed.

Definition dec_apply {A B : Type} dec (f : A -> B) g x :=
  match dec x with
  | true => f x
  | false => g x
  end.

Lemma dec_apply_negb : forall {A B : Type} dec (f : A -> B) g,
    dec_apply (negb ∘ dec) f g = dec_apply dec g f.
Proof.
  intros. unfold compose, dec_apply.
  apply fun_ext_dep. intros x.
  destruct (dec x); reflexivity.
Qed.

Lemma fold_compose12 : forall {A B C D : Type} (g : B -> D -> C) (f : A -> D -> B) x n,
    g (f x n) n = (g ∘∘ f) x n.
Proof. auto. Qed.

Lemma lift_depth_commute12 :
  forall {N N' V V' D A : Type} {p : N -> D -> N} {q : N' -> D -> N'}
    (g : N' -> V' -> A -> A) (f : N -> V -> A -> A) x y m n,
    (forall d, (f (p m d) x) ∘ (g (q n d) y) = (g (q n d) y) ∘ (f (p m d) x)) ->
    ((fun a d => f (p m d) x a)) ∘∘ ((fun a d => g (q n d) y a))
    = ((fun a d => g (q n d) y a)) ∘∘ ((fun a d => f (p m d) x a)).
Proof.
  intros N N' V V' D A. intros.
  apply fun_ext_dep. intros a.
  apply fun_ext_dep. intros k.
  unfold compose12.
  rewrite (fold_compose (f _ _)), H.
  auto.
Qed.
