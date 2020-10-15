(** remove printing ~ *)

Set Implicit Arguments.

From TLC Require Import LibTactics LibLogic LibVar.
Require Import LibExtraList.

Fixpoint vars_zip_map {A} f (xs : list var) (ys : list var) (X : A) :=
  match xs, ys with
  | nil, _ => X
  | _, nil => X
  | cons x xs, cons y ys => f x y (vars_zip_map f xs ys X)
  end.

Lemma var_decide : forall (x y : var), {x = y} + {x <> y}.
Proof.
  intros x y.
  pose proof (var_compare_eq x y).
  rewrite LibReflect.isTrue_eq_if in H.
  cases_if; auto.
Qed.

Lemma fv_decide : forall (x : var) s, {x \in s} + {x \notin s}.
Proof.
  intros. apply classicT.
Qed.

Lemma fresh_cons : forall L n x ys,
    fresh L (S n) (x :: ys) ->
    x \notin L /\ fresh (L \u \{ x}) n ys.
Proof.
  unfold fresh; auto.
Qed.

Lemma fresh_single_in : forall l ys x F,
    x \in F ->
    fresh F l ys ->
    fresh \{ x} l ys.
Proof.
  induction l; induction ys; intros; simpl; auto.
  simpl in H0. destruct H0. split.
  - intros ?H. rewrite in_singleton in H2; subst a; auto.
  - apply fresh_union_l; auto. eapply IHl; eauto.
Qed.

Lemma fresh_from_list : forall ys x L,
    x \notin from_list ys ->
    fresh L (length ys) ys ->
    fresh \{ x} (length ys) ys.
Proof.
  induction ys; intros; simpl; auto.
  rewrite from_list_cons in H. split.
  - notin_solve.
  - simpl in H0. destruct H0.
    fresh_solve. eapply IHys; eauto.
Qed.

Lemma from_list_fresh : forall ys x,
    fresh \{ x} (length ys) ys ->
    x \notin from_list ys.
Proof.
  induction ys; intros; simpl; auto.
  - rewrite from_list_nil; auto.
  - rewrite from_list_cons, notin_union; auto.
Qed.

Lemma fresh_cons_app : forall x ys L,
    fresh L (length (x :: ys)) (x :: ys) ->
    fresh L (length (ys ++ x :: nil)) (ys ++ x :: nil).
Proof.
  intros x. induction ys; simpls; intros; auto.
  destruct H. destruct H0.
  split; auto.
Qed.

Lemma fresh_app : forall xs ys L,
    fresh L (length (xs ++ ys)) (xs ++ ys) ->
    fresh L (length (ys ++ xs)) (ys ++ xs).
Proof.
  induction xs; intros.
  - simpls. rewrite List.app_nil_r. auto.
  - assert ((a :: xs)%list = ((a :: nil) ++ xs)%list) by reflexivity.
    rewrite ? H0 in H. rewrite <- ? List.app_assoc in H.
    clear H0. apply fresh_cons_app in H.
    rewrite <- List.app_assoc in H. apply IHxs in H.
    rewrite <- List.app_assoc in H. apply H.
Qed.

Lemma fresh_app_l : forall xs ys L,
    fresh L (length (xs ++ ys)) (xs ++ ys) ->
    fresh L (length xs) xs.
Proof.
  induction ys.
  - rewrite <- List.app_nil_end; auto.
  - intros L Hfr.
    apply fresh_app in Hfr.
    destruct Hfr as [? Hfr].
    apply fresh_app in Hfr.
    apply IHys; auto.
Qed.

Lemma fresh_rev : forall L xs,
    fresh L (length xs) xs ->
    fresh L (length (List.rev xs)) (List.rev xs).
Proof.
  intros L xs. gen L.
  induction xs using List.rev_ind; simpls; intros; auto.
  rewrite List.rev_app_distr. apply fresh_app.
  apply fresh_app in H. apply fresh_cons_app.
  simpls. destruct H. split; auto.
Qed.
Hint Extern 2 (fresh ?L (length (List.rev ?xs)) (List.rev ?xs)) =>
apply fresh_rev; auto 1 : core.

Lemma fresh_S_split : forall L n ys',
    fresh L (S n) ys' ->
    exists x ys, ys' = (x :: ys)%list.
Proof.
  intros. unfold fresh in H; destruct ys'.
  - destruct H.
  - exists v ys'; auto.
Qed.

Lemma fresh_length : forall ys L n,
    fresh L n ys ->
    length ys = n.
Proof.
  intros. apply fresh_length in H. rewrite liblist_length in H.
  congruence.
Qed.
Hint Resolve fresh_length : core.

Lemma fresh_length_rev : forall ys L n,
    fresh L n (List.rev ys) ->
    length ys = n.
Proof.
  intros. rewrite <- List.rev_length.
  eauto 2.
Qed.
Hint Resolve fresh_length_rev : core.

Lemma fresh_length_S : forall x ys L n,
    fresh L (S n) (x :: ys) ->
    length ys = n.
Proof.
  intros; apply (fresh_length _ L).
  destruct (fresh_cons H); auto.
Qed.
Hint Resolve fresh_length_S : core.

Lemma fresh_length_rev_S : forall x ys L n,
    fresh L (S n) (x :: (List.rev ys)) ->
    length ys = n.
Proof.
  intros. rewrite <- List.rev_length.
  eauto.
Qed.
Hint Resolve fresh_length_rev_S : core.
