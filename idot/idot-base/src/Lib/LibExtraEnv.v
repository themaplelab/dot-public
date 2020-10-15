(** remove printing ~ *)

Set Implicit Arguments.

From TLC Require Import LibEnv LibTactics.
Require Import LibExtraFset LibExtraVar LibExtraList.

Lemma in_dom_decide : forall {A} x (E : env A),
    (x \in dom E) \/ (x # E).
Proof.
  intros. induction E using env_ind.
  - right; auto.
  - simpl_dom. rewrite in_union, in_singleton.
    destruct (var_decide x x0); subst; auto.
    destruct IHE; auto.
Qed.

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

Lemma notin_dom_concat_r : forall {A} (E1 E2 : env A) x,
    x # (E1 & E2) ->
    x # E2.
Proof.
  intros; simpl_dom; auto.
Qed.

Lemma binds_to_middle : forall {A} (E : env A) x v,
    binds x v E ->
    exists E1 E2, E = E1 & x ~ v & E2 /\ x # E2.
Proof.
  induction E using env_ind.
  - intros. exfalso; eauto using binds_empty_inv.
  - intros. pose proof (binds_push_inv H) as [[Heq1 Heq2] | [Hneq Hbi]].
    + subst. exists E (empty (A:=A)).
      rewrite concat_empty_r; split; auto.
    + specialize (IHE _ _ Hbi) as [E1 [E2 [Heq Hfr]]].
      exists E1 (E2 & x ~ v); subst; split; auto.
      rewrite concat_assoc; auto.
Qed.

Lemma empty_dom_eq_empty : forall {A} (E : env A),
    dom E = \{} ->
    E = empty.
Proof.
  induction E as [| E x v IHE] using env_ind; auto.
  intros H; exfalso.
  assert (Hin : x \in dom (E & x ~ v))
    by (simpl_dom; rewrite in_union, in_singleton; auto).
  rewrite H in Hin; eauto using in_empty_inv.
Qed.

Lemma binds_concat_cases : forall {A} (E1 E2 : env A) x v,
    binds x v (E1 & E2) ->
    binds x v E2 \/ binds x v E1 /\ x # E2.
Proof.
  intros. induction E2 using env_ind.
  - rewrite concat_empty_r in *; auto.
  - rewrite concat_assoc in H.
    apply binds_push_inv in H.
    destruct H as [[Heq Heq'] | [Hneq Hbi]]; subst; auto.
    apply IHE2 in Hbi. destruct Hbi as [HbiE2 | [HbiE1 Hfr]]; auto.
Qed.

Lemma binds_middle_change : forall {A} (E1 E2 : env A) x v y v1 v2,
    binds x v (E1 & y ~ v1 & E2) ->
    v <> v1 ->
    binds x v (E1 & y ~ v2 & E2).
Proof.
  introv H Hneq. pose proof (binds_middle_inv H)
    as [Hbi2 | [[_ [_ contra]] | [Hfr [Hneq' Hbi]]]]; auto; congruence.
Qed.

Lemma binds_middle_update : forall {A} (E1 E2 : env A) x v y v1 v2,
    binds x v (E1 & y ~ v1 & E2) ->
    x <> y ->
    binds x v (E1 & y ~ v2 & E2).
Proof.
  introv H Hneq.
  pose proof (binds_middle_inv H)
    as [ Hbi2
       | [ [_ [contra _]]
         | [Hfr [Hneq' Hbi]]]];
                   auto; congruence.
Qed.

Lemma binds_middle_neq_binds :
  forall (A : Type) (x y : var) (E1 E2 : env A) v1 v2,
    binds x v1 (E1 & y ~ v2 & E2) ->
    x <> y ->
    binds x v1 (E1 & E2).
Proof.
  introv H Hneq. pose proof (binds_middle_inv H)
    as [Hbi2 | [[_ [contra _]] | [Hfr [_ Hbi]]]];
                   auto using binds_concat_right;
                   try congruence.
Qed.

Lemma binds_middle_eq_fresh_inv :
  forall (A : Type) (x : var) (E1 E2 : env A) (v1 v2 : A),
    binds x v1 (E1 & x ~ v2 & E2) ->
    x # E2 ->
    v1 = v2.
Proof.
  introv H Hdm. pose proof (binds_middle_inv H)
    as [Hbi2 | [[_ [_ Heq]] | [_ [contra _]]]]; try congruence.
  exfalso; eauto using binds_fresh_inv.
Qed.

Lemma ok_env_of_env : forall {A} (E : env A),
    exists E', ok E' /\ forall x v, binds x v E' <-> binds x v E.
Proof.
  induction E using env_ind.
  - exists (empty (A:=A)). split; auto; intros; split; auto.
  - destruct IHE as [E' [Hok Hbieq]].
    destruct (in_dom_decide x E').
    + apply dom_to_binds in H. destruct H as [v' Hbi].
      apply binds_to_middle in Hbi as [E1 [E2 [Heq Hfr]]]; subst.
      exists (E1 & x ~ v & E2). split; eauto using ok_middle_change.
      intros x' v''; destruct (var_decide x' x); subst.
      * split; introv Hbi.
        -- apply binds_middle_eq_inv in Hbi; subst; auto;
             eauto using ok_middle_change, binds_middle_eq_inv.
        -- apply binds_push_eq_inv in Hbi; destruct Hbi;
             eauto using binds_middle_eq.
      * split; intros.
        -- apply binds_push_neq; auto.
           apply Hbieq. apply binds_not_middle_inv in H; auto.
           destruct H; auto. destruct H.
           rewrite <- concat_assoc in Hok. auto.
        -- apply binds_push_neq_inv in H; auto.
           apply Hbieq in H.
           apply binds_not_middle_inv in H; auto.
           destruct H as [Hbi | [Hfr' Hbi]]; auto.
    + exists (E' & x ~ v); split; auto.
      intros. destruct (var_decide x0 x) as [?H | Hneq]; subst.
      * split; introv Heq; apply binds_push_eq_inv in Heq; subst; auto.
      * specialize (Hbieq x0 v0) as [?H ?H].
        split; introv Hbi; apply binds_push_neq;
          apply binds_push_neq_inv in Hbi; auto.
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

Lemma binds_push_fresh :
  forall (A : Type) (x x' : var) (a a' : A) (E : env A),
    binds x a E -> x' # E -> binds x a (E & x' ~ a').
Proof.
  intros A x x' a a' E.
  introv Hbi Hfr. apply binds_push_neq; auto.
  intros Heq; subst. apply Hfr.
  eapply binds_to_dom; eauto.
Qed.

Lemma binds_push_fresh_middle :
  forall (A : Type) (x x' : var) (a a' : A) (E F : env A),
    binds x a (E & F) -> x' # E -> binds x a (E & x' ~ a' & F).
Proof.
  intros A x x' a a' E.
  introv Hbi Hfr. apply binds_concat_inv in Hbi.
  destruct Hbi as [Hbi | [Hfr' Hbi]]; auto using binds_concat_right.
  apply binds_concat_left; auto.
  apply binds_concat_left; auto.
  apply binds_to_dom in Hbi.
  simpl_dom. intros Heq; rewrite in_singleton in Heq; subst.
  auto.
Qed.

Lemma dom_update_binds_inv : forall {A} (E1 E2 : env A) x,
    dom E1 = dom E2 ->
    (forall z v, z <> x -> binds z v E1 -> binds z v E2) ->
    (forall z v, z <> x -> binds z v E2 -> binds z v E1).
Proof.
  introv Heq HE2 Hneq HbiE2.
  pose proof (binds_to_dom HbiE2) as Hdom; rewrite <- Heq in Hdom.
  apply dom_to_binds in Hdom. destruct Hdom as [v' HbiE1].
  pose proof (HE2 _ _ Hneq HbiE1) as HbiE2'.
  pose proof (binds_functional HbiE2 HbiE2'); subst; auto.
Qed.

(** Inducting on Environments from the front. *)
Lemma env_ind_rev : forall (A : Type) (P : env A -> Prop),
    P empty ->
    (forall (E : env A) (x : var) (v : A), P E -> P (x ~ v & E)) ->
    forall E : env A, P E.
Proof.
  intro. unfold env.
  rewrite empty_def, concat_def, single_def.
  rewrite liblist_app. intros P Hnil Hcons.
  apply List.rev_ind with (P:=P); auto.
  intros [x v]; auto.
Qed.

(** Singles and Rev Singles *)
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

(** Freshness of Lists *)
Lemma dom_singles_rev : forall A ys (vs : list A),
    length ys = length vs ->
    from_list ys = dom (ys ~** vs).
Proof.
  intros * Hlen.
  rewrite dom_singles with (vs:=List.rev vs).
  + rewrite  <- from_list_rev; auto.
  + rewrite liblist_length.
    rewrite ? List.rev_length; auto.
Qed.

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

Lemma fresh_end_notin_dom : forall A (E : env A) vs x ys,
    fresh (dom E) (S (length ys)) (ys ++ (x :: nil)) ->
    length ys = length vs ->
    x \notin dom (E & ys ~** vs).
Proof.
  intros * Hfr Hlen.
  change (S (length ys)) with (length (x :: nil) + length ys) in Hfr.
  rewrite PeanoNat.Nat.add_comm, <- List.app_length in Hfr.
  apply fresh_app in Hfr.
  auto using fresh_cons_notin.
Qed.

Lemma fresh_dom_last : forall A (E : env A) vs x ys,
    length ys = length vs ->
    fresh (dom E) (S (length ys)) (ys ++ (x :: nil)) ->
    fresh (dom E) (length ys) ys /\
    x \notin dom (E & ys ~** vs).
Proof.
  intros * Hlen Hfr.
  split; auto 2 using fresh_end_notin_dom.
  change (S (length ys)) with (length ((x :: nil) ++ ys)) in Hfr.
  rewrite List.app_length in Hfr.
  rewrite PeanoNat.Nat.add_comm, <- List.app_length in Hfr.
  eauto using fresh_app_l.
Qed.

Lemma fresh_notin_dom : forall A (vs : list A) x ys,
    length ys = length vs ->
    fresh \{ x} (length ys) ys ->
    x \notin dom (ys ~** vs).
Proof.
  intros ? vs x ys Hlen Hfr.
  rewrite <- (concat_empty_l (ys ~** vs)).
  apply fresh_cons_notin_rev; auto.
  simpl; split; auto.
  simpl_dom. rewrite union_empty_l; auto.
Qed.

Lemma fresh_list_notin : forall A L ys (vs : list A) y n,
    length ys = length vs ->
    fresh L n ys ->
    y \in dom (ys ~** vs) ->
    y \notin L.
Proof.
  induction ys.
  - induction vs; rewrite ? singles_nil, ? dom_empty.
    + intros * ? ? Contra.
      exfalso. apply (in_empty_inv Contra).
    + inversion 1.
  - induction vs.
    + inversion 1.
    + inversion 1.
      rewrite singles_rev_push, dom_concat,
      dom_single, in_union, in_singleton by auto.
      intro Hfr.
      pose proof (fresh_length _ _ _ Hfr) as Hlen. subst n.
      destruct Hfr as [Hfr' Hfr].
      apply fresh_union_r1 in Hfr.
      destruct 1; subst; auto.
      eapply IHys; eauto.
Qed.

Lemma fresh_binds : forall A E (vs : list A) x ys y v1 v2,
    length ys = length vs ->
    binds y v1 E ->
    fresh (dom E) (S (length ys)) (x :: ys) ->
    binds y v1 (E & ys ~** vs & x ~ v2).
Proof.
  intros * Hlen Hbi Hfr.
  apply binds_push_neq.
  - apply binds_concat_left; auto 2.
    apply fresh_notin_dom; auto 2.
    apply fresh_single_in with (F := dom E);
      eauto using binds_to_dom.
    destruct (fresh_cons  Hfr); auto.
  - apply binds_to_dom in Hbi.
    intro; subst.
    destruct (fresh_cons  Hfr); auto.
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

(** Lemmas and Hints to solve environment equality *)
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

Lemma concat_assoc_eq4 {A} : forall {E1 E2 E3 E4 : env A},
    E1 & E2 & E3 & E4 = E1 & E2 & (E3 & E4).
Proof.
  intros. rewrite concat_assoc; auto.
Qed.
Hint Resolve concat_assoc_eq4 : core.

Lemma concat_assoc_eq5 {A} : forall {E1 E2 E3 E4 E5 : env A},
    E1 & E2 & E3 & E4 & E5 = E1 & E2 & (E3 & E4 & E5).
Proof.
  intros. rewrite ? concat_assoc; auto.
Qed.
Hint Resolve concat_assoc_eq5 : core.

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
