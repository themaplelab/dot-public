(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Bool.Bool.
Require Export Coq.Program.Basics.
From TLC Require Export LibVar LibLN.

Open Scope program_scope.

Section Program.
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

  Definition ignore_second {A B C : Type} (f : A -> C) (x : A) (n : B) := f x.

  Definition compose12 {A B C D : Type} (g : B -> D -> C) (f : A -> D -> B) (x : A) (n : D) :=
    g (f x n) n.

  Notation " g ∘∘ f " := (compose12 g f) (at level 40, left associativity).

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
End Program.

Notation " g ∘∘ f "
  := (compose12 g f) (at level 40, left associativity) : program_scope.
Hint Unfold ignore_second compose12 : core.

Module Nat := PeanoNat.Nat.

Lemma length_eq_implies_rev_length_eq : forall A B (l1 : list A) (l2 : list B),
    length l1 = length l2 ->
    length (List.rev l1) = length (List.rev l2).
Proof.
  intros. rewrite ? List.rev_length. auto.
Qed.

Lemma rev_length_eq_implies_length_eq : forall A B (l1 : list A) (l2 : list B),
    length (List.rev l1) = length (List.rev l2) ->
    length l1 = length l2.
Proof.
  intros. rewrite ? List.rev_length in *. auto.
Qed.
Hint Resolve length_eq_implies_rev_length_eq : core.


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

Fixpoint vars_zip_map {A} f (xs : list var) (ys : list var) (X : A) :=
  match xs, ys with
  | nil, _ => X
  | _, nil => X
  | cons x xs, cons y ys => f x y (vars_zip_map f xs ys X)
  end.

Notation "z '\[' x '->' y ']'" := (If z = x then y else z) (x at level 69, at level 70).
Definition subst_fvar (x y z: var): var := If z = x then y else z.

(** Converting between binding and in dom *)
Lemma dom_to_binds : forall A (E : env A) x,
    x \in dom E ->
    exists v, binds x v E.
Proof.
  induction E using env_ind.
  - intros; false. simpl_dom.
    rewrite in_empty in H; auto.
  - intros.
    destruct (var_decide x0 x) as [?H | ?H].
    + subst x0; exists v; auto.
    + rewrite dom_concat, in_union in H.
      destruct H.
      * apply IHE in H.
        destruct H as [?v ?H].
        exists v0; apply binds_concat_left; auto.
      * false. simpl_dom; rewrite in_singleton in H.
        auto.
Qed.

Lemma binds_to_dom : forall A (E : env A) x v,
    binds x v E ->
    x \in dom E.
Proof.
  introv H. induction E using env_ind.
  - exfalso; eauto using binds_empty_inv.
  - destruct (binds_push_inv H) as [[? ?] | [? ?]]; subst; simpl_dom; rewrite in_union.
    + left. auto using in_singleton_self.
    + right. auto.
Qed.

Hint Extern 1 (_ # _) =>
match goal with
| [H : dom ?G1 = dom ?G2, _ : ?x # ?G1 |- ?x # ?G2 ] => rewrite <- H; assumption
| [H : dom ?G2 = dom ?G1, _ : ?x # ?G1 |- ?x # ?G2 ] => rewrite H; assumption
end : core.

Lemma ok_val : forall A (E : env A) x v1 v2,
    ok (E & x ~ v1) ->
    ok (E & x ~ v2).
Proof.
  introv H; apply ok_push_inv in H as [? ?]; auto 2.
Qed.
Hint Extern 1 (ok _) =>
match goal with
| [H : ok (?E & ?x ~ ?v1) |- ok (?E & ?x ~ ?v2)] =>
  apply (ok_val (v1:=v1)); assumption
end : core.

Lemma binds_weaken :
  forall (A : Type) (x : var) (a : A) (E F G : env A),
    binds x a (E & G) -> ok (E & F) -> binds x a (E & F & G).
Proof.
  intros A x a E F G Bi Hok.
  apply binds_concat_inv in Bi.
  destruct Bi as [Bi | [Fr Bi]]; auto 2.
  apply binds_concat_left.
  apply binds_concat_left_ok.
  all: auto.
Qed.

Lemma liblist_length :
  LibList.length = length.
Proof.
  apply fun_ext_dep. intros A.
  apply fun_ext_dep. intros xs.
  induction xs as [ | x xs IHxs].
  - unfold LibList.length. simpl. auto.
  - simpl. rewrite <- IHxs. unfold LibList.length. auto.
Qed.

Lemma liblist_app : LibList.app = app.
Proof.
  apply fun_ext_dep. intros A.
  apply fun_ext_dep. intros xs.
  induction xs as [ | x xs IHxs].
  - reflexivity.
  - apply fun_ext_dep. intros ys.
    simpl. rewrite <- IHxs.
    reflexivity.
Qed.

Lemma liblist_rev :
  LibList.rev = List.rev.
Proof.
  apply fun_ext_dep. intros A.
  apply fun_ext_dep. intros xs.
  induction xs as [ | x xs IHxs].
  - reflexivity.
  - simpl. rewrite <- IHxs.
    rewrite LibList.rev_cons. rewrite liblist_app.
    reflexivity.
Qed.

Lemma liblist_fold_right: forall A B,
    @LibList.fold_right B A = @List.fold_right A B.
Proof.
  intros.
  apply fun_ext_dep. intros f.
  apply fun_ext_dep. intros acc.
  apply fun_ext_dep. intros xs.
  induction xs as [ | x xs IHxs].
  - reflexivity.
  - simpl. rewrite <- IHxs.
    reflexivity.
Qed.

Lemma liblist_map : LibList.map = List.map.
Proof.
  apply fun_ext_dep. intros A.
  apply fun_ext_dep. intros B.
  apply fun_ext_dep. intros f.
  apply fun_ext_dep. intros xs.
  induction xs as [ | x xs IHxs].
  - reflexivity.
  - simpl. rewrite <- IHxs.
    reflexivity.
Qed.


Notation "xs ~** vs" := (singles (List.rev xs) (List.rev vs))
  (at level 27, left associativity) : env_scope.


Lemma singles_nil : forall A,
    nil ~* (@nil A) = empty.
Proof.
  intros. rewrite singles_def; auto.
Qed.

Lemma singles_push_r : forall A (v : A) (vs : list A) y ys,
    (y :: ys)%list ~* (v :: vs)%list = ys ~* vs & y ~ v.
Proof.
  intros. rewrite singles_def. auto.
Qed.

Lemma singles_push_l : forall A (v : A) (vs : list A) y ys,
    length ys = length vs ->
    (ys ++ y :: nil)%list ~* (vs ++ v :: nil)%list = y ~ v & ys ~* vs.
Proof.
  intros A v vs y ys. gen vs.
  induction ys; induction vs; intros; simpls; try congruence.
  - rewrite singles_push_r, ? singles_nil, concat_empty_l, concat_empty_r; auto.
  - rewrite ? singles_push_r. rewrite IHys; auto.
    rewrite concat_assoc. auto.
Qed.

Lemma singles_rev_push : forall A (v : A) (vs : list A) y ys,
    length ys = length vs ->
    (y :: ys)%list ~** (v :: vs)%list
    = y ~ v & ys ~** vs.
Proof.
  intros. simpl.
  rewrite singles_push_l; auto.
Qed.

Lemma singles_rev_cons : forall A (v : A) (vs : list A) y ys,
    (ys ++ y :: nil)%list ~** (vs ++ v :: nil)%list
    = ys ~** vs & y ~ v.
Proof.
  intros. simpl.
  rewrite ? List.rev_unit.
  rewrite singles_push_r; auto.
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

Lemma fresh_ok_ys : forall A (E : env A) vs x ys,
    fresh (dom E) (S (length ys)) (x :: ys) ->
    length ys = length vs ->
    ok E ->
    ok (E & ys ~* vs).
Proof.
  intros. simpl in H. destruct H.
  assert (fresh (dom E) (length vs) ys) by auto.
  eapply ok_singles; eauto.
  rewrite ? liblist_length.
  auto.
Qed.

Lemma fresh_ok_rev_ys : forall A (E : env A) vs x ys,
    fresh (dom E) (S (length ys)) (x :: ys) ->
    length ys = length vs ->
    ok E ->
    ok (E & ys ~** vs).
Proof.
  eauto using fresh_ok_ys.
Qed.

Lemma fresh_cons_notin : forall A (E : env A) vs x ys,
    fresh (dom E) (S (length ys)) (x :: ys) ->
    length ys = length vs ->
    x \notin dom (E & ys ~* vs).
Proof.
  intros A E vs x. induction vs; induction ys; simpls; try congruence.
  - intros. destruct H. rewrite singles_nil, concat_empty_r. auto.
  - intros. rewrite singles_push_r.
    repeat rewrite dom_concat, notin_union.
    destruct H. destruct H1.
    split; auto 1. split; auto 1.
    rewrite dom_singles by (rewrite ? liblist_length; congruence).
    apply from_list_fresh; auto.
Qed.

Lemma fresh_cons_notin_rev : forall A (E : env A) vs x ys,
    fresh (dom E) (S (length ys)) (x :: ys) ->
    length ys = length vs ->
    x \notin dom (E & ys ~** vs).
Proof.
  auto using fresh_cons_notin.
Qed.

Lemma fresh_ok : forall A (E : env A) v vs x ys,
    fresh (dom E) (S (length ys)) (x :: ys) ->
    length ys = length vs ->
    ok E ->
    ok (E & ys ~* vs & x ~ v).
Proof.
  intros. apply ok_push; eauto 2 using fresh_ok_ys, fresh_cons_notin.
Qed.

Lemma fresh_ok_rev : forall A (E : env A) v vs x ys,
    fresh (dom E) (S (length ys)) (x :: ys) ->
    length ys = length vs ->
    ok E ->
    ok (E & ys ~** vs & x ~ v).
Proof.
  auto using fresh_ok.
Qed.
Hint Resolve fresh_ok_rev : core.

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

Lemma fresh_vars_map : forall x y ys,
    fresh \{ x} (length ys) ys ->
    List.map (subst_fvar x y) ys = ys.
Proof.
  intros. induction ys.
  - auto.
  - simpls. destruct H. f_equal.
    + unfold subst_fvar; cases_if.
      * exfalso. apply H. rewrite in_singleton. auto.
      * auto.
    + apply IHys; auto.
Qed.


Hint Extern 1 (?F \u ?G = ?G \u ?F) => rewrite union_comm; reflexivity : core.
Hint Extern 1 (?E \u ?F \u ?G = (?E \u ?F) \u ?G) => rewrite union_assoc; reflexivity : core.
Hint Extern 1 (?E \u ?F \u ?G = ?E \u ?G \u ?F) =>
rewrite (@union_comm _ F G); reflexivity : core.
Hint Extern 1 (?E \u ?F \u ?G = ?F \u ?E \u ?G) =>
rewrite (@union_comm_assoc _ E F G); reflexivity : core.
Hint Extern 1 (?E \u ?F \u ?E = ?F \u ?E) =>
rewrite union_comm_assoc; rewrite union_same; reflexivity : core.
Hint Extern 1 (?E \u \{} = ?E) => rewrite union_empty_r; reflexivity : core.
Hint Extern 1 (?E = ?E \u \{}) => rewrite union_empty_r; reflexivity : core.
Hint Extern 1 (\{} \u ?E = ?E) => rewrite union_empty_l; reflexivity : core.
Hint Extern 1 (?E = \{} \u ?E) => rewrite union_empty_l; reflexivity : core.

Lemma union_same_push : forall A (E F : fset A),
    E \u (E \u F) = E \u F.
Proof.
  intros. rewrite union_assoc, union_same. reflexivity.
Qed.

Lemma union_eq_cases : forall A (E F G H I : fset A),
    E = F \/ E = I \u F ->
    G = H \/ G = I \u H ->
    E \u G = F \u H \/ E \u G = I \u F \u H.
Proof.
  intros. destruct H0; destruct H1; subst; try solve [left; auto 2 | right; auto 2].
  - right. rewrite <- union_assoc. auto.
  - right.
    rewrite union_comm_assoc, <- union_assoc, union_same_push. auto 2.
Qed.



Hint Extern 1 (?E & ?F & ?G = ?E & (?F & ?G)) =>
  rewrite concat_assoc; reflexivity : core.
Hint Extern 1 (?E & ?F & ?G & ?H = ?E & (?F & (?G & ?H))) =>
  rewrite 2 concat_assoc; reflexivity : core.
Hint Extern 1 (?E & ?F & ?G & ?H & ?I = ?E & ?F & (?G & ?H & ?I)) =>
  rewrite 2 concat_assoc; reflexivity : core.



Lemma fv_in_values_empty : forall (A : Type) f,
    @fv_in_values A f empty = \{}.
Proof.
  intros A f. unfold fv_in_values. rewrite empty_def, values_def.
  reflexivity.
Qed.

Lemma fv_in_values_cons : forall A (E1: env A) x v f,
    fv_in_values f (E1 & x ~ v) = fv_in_values f E1 \u (fv_in_values f (x ~ v)).
Proof.
  intros. rewrite union_comm.
  unfold fv_in_values. rewrite single_def, values_def, concat_def.
  simpl. rewrite union_empty_r. reflexivity.
Qed.

Lemma fv_in_values_concat : forall A (E1 E2: env A) f,
    fv_in_values f (E1 & E2) = fv_in_values f E1 \u fv_in_values f E2.
Proof.
  intros A E1 E2. gen E1. induction E2 using env_ind; intros.
  - rewrite concat_empty_r. rewrite <- (union_empty_r (fv_in_values f E1)) at 1.
    f_equal. unfold fv_in_values. rewrite empty_def, values_def; auto.
  - rewrite concat_assoc. rewrite ? fv_in_values_cons.
    rewrite ? IHE2. rewrite <- union_assoc. auto.
Qed.

Ltac intros_fun_ext :=
  repeat (apply fun_ext_dep; intro).

Lemma or_orb_iff_left : forall P Q b1 b2,
    P <-> b1 = true ->
    Q <-> b2 = true ->
    P \/ Q <-> b1 || b2 = true.
Proof.
  intros. destruct H, H0. split; destruct b1, b2; simpl; auto.
  intros. destruct H3; auto.
Qed.

Lemma Is_true_iff_eq_true : forall bl,
    Is_true bl <-> bl = true.
Proof.
  intros; split; auto using Is_true_eq_true, Is_true_eq_left.
Qed.
