(** remove printing ~ *)

Set Implicit Arguments.

From TLC Require Import LibEnv LibTactics LibLN.
Require Import LibExtraVar LibExtraList LibExtraFset.

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

Definition subst_pair_fset_vars {A} (vs : fset var) (y : A) (e : var * A) :=
  match e with
  | (x, y') => If x \in vs then (x, y) else (x, y')
end.

Definition subst_env_fset_vars {A}
           (E : env A) (vs : fset var) (y : A) : (env A) :=
  List.map (subst_pair_fset_vars vs y) E.


Lemma subst_env_fset_vars_distrib_env : forall A (E1 : env A) (E2 : env A) vs i,
    subst_env_fset_vars (E1 & E2) vs i =
    (subst_env_fset_vars E1 vs i) & (subst_env_fset_vars E2 vs i).
Proof with eauto.
  induction E2; intros...
  - simpl. rewrite <- empty_def. repeat(rewrite concat_empty_r)...
  - rewrite concat_def in *. simpl. rewrite IHE2...
Qed.

Lemma subst_env_fset_vars_empty : forall A (E : env A) i,
    subst_env_fset_vars E \{} i = E.
Proof with eauto.
  induction E...
  destruct a. simpl. rewrite cons_to_push. cases_if.
  + rewrite in_empty in C. destruct C.
  + intros. rewrite IHE. rewrite cons_to_push...
Qed.

Lemma subst_env_fset_vars_single_notin : forall A (E : env A) (x : var) i,
    x # E ->
    subst_env_fset_vars E \{x} i = E.
Proof with eauto.
  induction E...
  destruct a. intros.
  rewrite cons_to_push in *. rewrite dom_concat in H.
  rewrite notin_union in H. destruct H.
  rewrite <- cons_to_push. simpl.
  rewrite dom_single, notin_singleton in H0. cases_if.
  - exfalso. rewrite in_singleton in C...
  - apply f_equal...
Qed.

Lemma subst_pair_fset_vars_same : forall A (xs : vars) (i : A) (x : var),
    subst_pair_fset_vars xs i (x, i) = (x, i).
Proof with eauto. intros... simpl. cases_if... Qed.

Lemma subst_pair_fset_in_vars : forall A (xs : vars) (i a : A) (x : var),
    x \in xs ->
    subst_pair_fset_vars xs i (x, a) = (x, i).
Proof with eauto. intros... simpl. cases_if... Qed.

Lemma subst_pair_fset_notin_vars : forall A (xs : vars) (i a : A) (x : var),
    x \notin xs ->
    subst_pair_fset_vars xs i (x, a) = (x, a).
Proof with eauto. intros... simpl. cases_if... Qed.

Lemma subst_env_fset_vars_distrib_vs : forall A (E : env A) vs x i,
    subst_env_fset_vars E (vs \u \{x}) i =
    subst_env_fset_vars (subst_env_fset_vars E vs i) \{x} i.
Proof with eauto.
  induction E...
  destruct a. intros. simpl. cases_if.
  - cases_if.
    + rewrite subst_pair_fset_vars_same. apply f_equal...
    + rewrite in_union in C.
      destruct C; try(solve[exfalso; eauto]).
      rewrite subst_pair_fset_in_vars... apply f_equal...
  - rewrite in_union in C. rewrite not_or_eq in C. destruct C.
    cases_if. rewrite subst_pair_fset_notin_vars... apply f_equal...
Qed.

Lemma subst_env_fset_vars_dom : forall A (E : env A) vs i,
    dom (subst_env_fset_vars E vs i) = dom E.
Proof with eauto.
  induction E...
  intros. simpl. destruct a.
  simpl. cases_if.
  - repeat(rewrite cons_to_push; rewrite dom_concat; rewrite dom_single).
    rewrite IHE...
  - repeat(rewrite cons_to_push; rewrite dom_concat; rewrite dom_single).
    rewrite IHE...
Qed.

Lemma subst_env_fset_vars_ignore_fresh : forall A (E : env A) vs x i,
    x # E ->
    subst_env_fset_vars E (vs \u \{x}) i =
    subst_env_fset_vars E vs i.
Proof with eauto.
  introv Hfrx. pose proof (fset_finite vs) as [L Hleq].
  generalize dependent vs. induction L.
  - intros. subst. rewrite from_list_nil. rewrite union_empty_l.
    rewrite subst_env_fset_vars_empty, subst_env_fset_vars_single_notin...
  - intros. rewrite from_list_cons in Hleq. subst.
    rewrite subst_env_fset_vars_distrib_vs.
    rewrite subst_env_fset_vars_single_notin...
    rewrite subst_env_fset_vars_dom...
Qed.

Lemma subst_env_fset_vars_single : forall A (x : var) (a : A) vs (i : A),
    subst_env_fset_vars (x ~ a) vs i = (x ~ If x \in vs then i else a).
Proof with eauto. intros. rewrite single_def. simpl. cases_if... Qed.

Lemma subst_env_fset_vars_in_vs_single : forall A (x : var) (a : A) vs (i : A),
    x \in vs ->
    subst_env_fset_vars (x ~ a) vs i = (x ~ i).
Proof.
  intros.
  rewrite subst_env_fset_vars_single.
  cases_if; auto.
Qed.

Lemma subst_env_fset_vars_ok : forall A (E : env A) vs i,
    ok E ->
    ok (subst_env_fset_vars E vs i).
Proof with eauto.
  intros. induction H...
  - rewrite empty_def. simpl. rewrite <- empty_def...
  - rewrite subst_env_fset_vars_distrib_env.
    rewrite subst_env_fset_vars_single. econstructor...
    rewrite subst_env_fset_vars_dom...
Qed.

Lemma subst_env_fset_vars_binds_single : forall A (E : env A) vs i (a : A) x,
    binds x i (subst_env_fset_vars (x ~ a) vs i) ->
    a = i \/ x \in vs.
Proof with eauto.
  intros. rewrite single_def in H. simpl in H.
  cases_if...
  rewrite cons_to_push, <- empty_def, concat_empty_l in H.
  apply binds_single_eq_inv in H...
Qed.

Lemma subst_env_fset_vars_binds : forall A (E : env A) vs i x,
    binds x i (subst_env_fset_vars E vs i) ->
    binds x i E \/ x \in vs.
Proof with eauto.
  induction E...
  intros. destruct a. rewrite cons_to_push in *.
  rewrite subst_env_fset_vars_distrib_env in H.
  apply binds_concat_inv in H.
  destruct H.
  - apply binds_to_dom in H as ?.
    rewrite subst_env_fset_vars_dom, dom_single, in_singleton in H0. subst.
    apply subst_env_fset_vars_binds_single in H... destruct H; subst...
  - rewrite subst_env_fset_vars_dom, dom_single, notin_singleton in H.
    destruct H. specialize (IHE vs i x H0). destruct IHE...
Qed.

Lemma subst_pair_fset_vars_binds : forall A E (xs : vars) (i : A) (x : var),
    binds x i E ->
    binds x i (subst_env_fset_vars E xs i).
Proof with eauto.
  intros. induction E...
  destruct a. rewrite cons_to_push in *.
  apply binds_concat_inv in H. destruct H.
  - apply binds_single_inv in H. destruct H; subst.
    rewrite subst_env_fset_vars_distrib_env.
    apply binds_concat_right.
    rewrite subst_env_fset_vars_single. cases_if; eauto using binds_single_eq.
  - destruct H.
    rewrite subst_env_fset_vars_distrib_env.
    apply binds_concat_left...
    rewrite subst_env_fset_vars_single. cases_if; eauto using binds_single_eq.
Qed.

Lemma subst_env_fset_vars_more : forall A (E : env A) vs vs' i x,
    binds x i (subst_env_fset_vars E vs i) ->
    vs \c vs' ->
    binds x i (subst_env_fset_vars E vs' i).
Proof with eauto.
  induction E...
  intros. simpl. destruct a.
  simpl. cases_if.
  - rewrite cons_to_push in *.
    rewrite subst_env_fset_vars_distrib_env in H.
    apply binds_concat_inv in H. destruct H.
    + rewrite subst_env_fset_vars_single in H.
      apply binds_single_inv in H. destruct H; subst...
    + destruct H. eapply IHE in H1...
      rewrite subst_env_fset_vars_dom in H...
  - rewrite cons_to_push in *.
    rewrite subst_env_fset_vars_distrib_env in H.
    apply binds_concat_inv in H. destruct H.
    + rewrite subst_env_fset_vars_single in H.
      apply binds_single_inv in H. destruct H; subst. cases_if...
      * exfalso... * subst...
    + destruct H. eapply IHE in H1...
      rewrite subst_env_fset_vars_dom in H...
Qed.

Lemma subst_env_fset_vars_in_vs : forall A (E : env A) vs i i' x,
    (x \in vs) -> binds x i' E ->
    binds x i (subst_env_fset_vars E vs i).
Proof with eauto.
  introv Hinv HbiX.
  induction E.
  - rewrite <- empty_def in HbiX. exfalso. apply binds_to_dom in HbiX.
    rewrite dom_empty, in_empty in HbiX...
  - destruct a. rewrite cons_to_push in HbiX.
    apply binds_concat_inv in HbiX.
    destruct HbiX.
    + apply binds_single_inv in H. destruct H; subst.
      simpl. cases_if...
      rewrite cons_to_push...
    + simpl. rewrite dom_single, notin_singleton in H. destruct H. cases_if...
      * rewrite cons_to_push...
      * rewrite cons_to_push...
Qed.

Lemma subst_env_fset_vars_more_env : forall A (E E' : env A) vs i x,
    (forall y, binds y i E -> binds y i E') ->
    (forall y a,
        y \in vs -> binds y a E -> binds y a E') ->
    binds x i (subst_env_fset_vars E vs i) ->
    binds x i (subst_env_fset_vars E' vs i).
Proof with eauto.
  introv Hmi Hsub Hbix.
  apply subst_env_fset_vars_binds in Hbix as ?.
  destruct H.
  - apply subst_pair_fset_vars_binds...
  - apply binds_to_dom in Hbix as ?.
    rewrite subst_env_fset_vars_dom in H0.
    apply dom_to_binds in H0. destruct H0...
    eapply subst_env_fset_vars_in_vs...
Qed.

Lemma subst_env_fset_vars_notin_binds : forall A (E : env A) x vs i,
    x \notin vs ->
    binds x i (subst_env_fset_vars E vs i) ->
    binds x i E.
Proof with eauto.
  induction E; introv Hnin Hbin...
  destruct a. simpl in Hbin. cases_if.
  - rewrite cons_to_push in *. apply binds_concat_inv in Hbin.
    destruct Hbin.
    + apply binds_single_inv in H. destruct H; subst. exfalso...
    + destruct H. rewrite dom_single, notin_singleton in H...
  - rewrite cons_to_push in *. apply binds_concat_inv in Hbin.
    destruct Hbin.
    + apply binds_single_inv in H. destruct H; subst...
    + destruct H. rewrite dom_single, notin_singleton in H...
Qed.

Lemma subst_env_fset_vars_already_subst : forall A (E E' : env A) x vs i,
    dom E = dom E' ->
    (forall (y : var),
        y \in vs -> binds y i E') ->
    (forall (y : var) (j : A),
        y \notin vs -> binds y j E -> binds y j E') ->
    binds x i (subst_env_fset_vars E vs i) ->
    binds x i E'.
Proof with eauto.
  induction E; introv HdomEq HinBin HninBin Hbinx.
  - simpl in Hbinx. rewrite <- empty_def in Hbinx.
    exfalso. eapply binds_empty_inv...
  - destruct E'.
    + destruct a.
      rewrite <- empty_def, dom_empty, cons_to_push, dom_concat, dom_single
        in HdomEq.
      exfalso. erewrite <- in_empty, <- HdomEq, in_union, in_singleton.
      right...
    + destruct (fv_decide x vs)...
      destruct a, p. simpl in Hbinx.
      cases_if; repeat(rewrite cons_to_push in *).
      * apply HninBin... apply binds_concat_inv in Hbinx.
        destruct Hbinx.
        { exfalso. apply binds_single_inv in H. destruct H; subst... }
        { destruct H. rewrite dom_single, notin_singleton in H.
          apply binds_to_dom in H0 as ?. rewrite subst_env_fset_vars_dom in H1.
          apply dom_to_binds in H1. destruct H1. eapply binds_push_neq...
          eapply subst_env_fset_vars_notin_binds... }
      * apply HninBin... apply binds_concat_inv in Hbinx.
        destruct Hbinx...
        destruct H. rewrite dom_single, notin_singleton in H.
        apply binds_to_dom in H0 as ?. rewrite subst_env_fset_vars_dom in H1.
        apply dom_to_binds in H1. destruct H1. eapply binds_push_neq...
        eapply subst_env_fset_vars_notin_binds...
Qed.

Lemma subst_env_fset_vars_in_vs_inv : forall A (E : env A) x vs (i i' : A),
    (x \in vs) ->
    binds x i (subst_env_fset_vars E vs i') ->
    i = i'.
Proof with eauto.
  induction E; introv Hin Hbin...
  - simpl in Hbin. rewrite <- empty_def in Hbin.
    exfalso; eauto using binds_empty_inv.
  - destruct a. simpl in Hbin. cases_if.
    + rewrite cons_to_push in *. apply binds_concat_inv in Hbin.
      destruct Hbin.
      * apply binds_single_inv in H; destruct H; subst...
      * destruct H...
    + rewrite cons_to_push in *. apply binds_concat_inv in Hbin.
      destruct Hbin.
      * apply binds_single_inv in H; destruct H; subst. exfalso...
      * destruct H...
Qed.

Lemma subst_env_fset_vars_notin_vs_inv : forall A (E : env A) x vs (i i' : A),
    (x \notin vs) ->
    binds x i (subst_env_fset_vars E vs i') ->
    binds x i E.
Proof with eauto.
  induction E; introv Hin Hbin...
  destruct a. simpl in Hbin. cases_if.
  - rewrite cons_to_push in *. apply binds_concat_inv in Hbin.
    destruct Hbin.
    + apply binds_single_inv in H; destruct H; subst; exfalso...
    + destruct H...
  - rewrite cons_to_push in *. apply binds_concat_inv in Hbin.
    destruct Hbin... destruct H...
Qed.

Lemma subst_env_fset_vars_notin_ignore : forall A (E : env A) x vs (i i' : A),
    (x \notin vs) ->
    binds x i E ->
    binds x i (subst_env_fset_vars E vs i').
Proof with eauto.
  induction E; introv Hin Hbin...
  destruct a. simpl in Hbin. rewrite cons_to_push in Hbin.
  apply binds_concat_inv in Hbin. destruct Hbin.
  - apply binds_single_inv in H; destruct H; subst. simpl. cases_if.
    rewrite cons_to_push...
  - destruct H. rewrite dom_single, notin_singleton in H. simpl.
    cases_if; rewrite cons_to_push...
Qed.

Lemma subst_env_fset_vars_more_E : forall A (E E' : env A) x vs (i i0 : A),
    (forall y j, binds y j E -> binds y j E') ->
    binds x i (subst_env_fset_vars E  vs i0) ->
    binds x i (subst_env_fset_vars E' vs i0).
Proof with eauto.
  introv Hmore Hbin.
  destruct (fv_decide x vs).
  - pose proof (subst_env_fset_vars_in_vs_inv _ i0 m Hbin); subst.
    apply binds_to_dom in Hbin. rewrite subst_env_fset_vars_dom in Hbin.
    apply dom_to_binds in Hbin. destruct Hbin as [v Hbin].
    eapply subst_env_fset_vars_in_vs...
  - pose proof (subst_env_fset_vars_notin_vs_inv _ _ n Hbin).
    specialize (Hmore _ _ H).
    eapply subst_env_fset_vars_notin_ignore...
Qed.

Lemma subst_env_fset_vars_notin_remove : forall A (E : env A) x vs i,
    x \notin dom E ->
    subst_env_fset_vars E vs i = subst_env_fset_vars E (vs \- \{x}) i.
Proof with eauto.
  induction E...
  introv Hxnin. destruct a.
  rewrite cons_to_push, dom_concat, notin_union, dom_single, notin_singleton
    in Hxnin.
  destruct Hxnin as [Hxnin Hxneq]. simpl. cases_if.
  - rewrite IHE with (x := x)... cases_if...
    exfalso. pose proof (remove_notin_inv C C0)...
  - rewrite IHE with (x := x)... cases_if...
    exfalso. rewrite in_remove in C0. destruct C0...
Qed.
