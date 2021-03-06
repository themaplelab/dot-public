(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import InitLookup InitLookupLemmas VarsSubst.

Local Hint Constructors init_var init_sub : core.

(** * Initialization Subtype Bindings *)
(* This is a condition used for substitution lemmas of the initialization system. *)
Definition init_binds_sub (x : var) (Delta1 : init_ctx) (y : var) (Delta2 : init_ctx) : Prop :=
  forall i, binds x i Delta1 -> exists i', init_sub i' i /\ binds y i' Delta2.

(** ** Lemmas about Initialization Subtype Bindings *)
Lemma init_var_same : forall Delta1 x i Delta2,
    x # Delta2 ->
    init_var (Delta1 & x ~ i & Delta2) \{x} x i.
Proof.
  intros Delta1 x i Delta2 Hfr.
  destruct i; eauto using in_singleton_self.
Qed.

Lemma init_var_binds_subst_cond : forall (Delta1 Delta2 : init_ctx) (x y : var) (vs : vars) (i : init_typ),
    x # Delta2 ->
    init_var (Delta1 & Delta2) vs y i ->
    init_binds_sub x (Delta1 & x ~ i & Delta2) y (Delta1 & Delta2).
Proof.
  intros * Hfr Hiv.
  intros i' Hbi.
  apply binds_middle_eq_fresh_inv in Hbi; auto; subst.
  eauto using init_var_typing_implies_bound_sub.
Qed.

Lemma init_binds_sub_push : forall Delta1 x i Delta2 y z i',
    z <> x ->
    z <> y ->
    x # Delta2 ->
    init_binds_sub x (Delta1 & x ~ i & Delta2) y (Delta1 & Delta2) ->
    init_binds_sub x (Delta1 & x ~ i & Delta2 & z ~ i') y (Delta1 & Delta2 & z ~ i').
Proof.
  unfold init_binds_sub.
  intros * Hzx Hzy Hfr Hisub.
  intros i1 Hbi.
  pose proof (binds_push_inv Hbi) as [[? ?] | [? Hbix]]; try congruence; subst.
  specialize (Hisub _ Hbix).
  destruct Hisub as [i2 [Hisub Hbiy]].
  exists i2; split; auto.
Qed.

Lemma init_binds_sub_push_fresh : forall Delta1 x i Delta2 y ys is',
    length ys = length is' ->
    fresh (dom (Delta1 & x ~ i & Delta2)) (length ys) ys ->
    x # Delta2 ->
    init_binds_sub x (Delta1 & x ~ i & Delta2) y (Delta1 & Delta2) ->
    init_binds_sub x (Delta1 & x ~ i & Delta2 & ys ~** is') y (Delta1 & Delta2 & ys ~** is').
Proof.
  induction ys as [| y' ys IHys] using List.rev_ind.
  - destruct is' as [| i' is']; [| simpl; congruence].
    rewrite singles_nil, ? concat_empty_r; auto.
  - destruct is' as [| i' is' _] using List.rev_ind.
    + intro Contra; exfalso.
      rewrite List.app_length, Nat.add_comm in Contra.
      simpl in Contra; congruence.
    + intro Hlen.
      repeat (rewrite List.app_length, Nat.add_comm in Hlen; simpl in Hlen).
      inversion Hlen as [Hlen'].
      rewrite ? singles_rev_cons, ? concat_assoc.
      intros Hfr Hfrx Hisub.
      rewrite List.app_length, Nat.add_comm in Hfr.
      simpl "+" in Hfr.
      pose proof (fresh_dom_last _ _ _ _ Hlen' Hfr) as [Hfrys Hfry].
      pose proof (IHys _ Hlen' Hfrys Hfrx Hisub).
      rewrite (concat_assoc_eq4 (E1 := Delta1)).
      rewrite <- (concat_assoc Delta1 Delta2).
      rewrite ? dom_concat, ? dom_single, ? notin_union in Hfry.
      destruct_all.
      apply init_binds_sub_push.
      * rewrite <- ? notin_singleton; auto 2.
      * assert (binds x i (Delta1 & x ~ i & Delta2)) as Hbi by auto.
        apply Hisub in Hbi. destruct Hbi as [? [_ Hbiy]].
        apply binds_to_dom in Hbiy. rewrite dom_concat, in_union in Hbiy.
        intro Contra; subst. destruct Hbiy; auto.
      * rewrite dom_concat, notin_union. split; auto 2.
        apply fresh_notin_dom; auto.
        rewrite ? dom_concat, ? dom_single in Hfrys; auto.
      * rewrite ? concat_assoc; auto.
Qed.

Lemma init_binds_sub_push_fresh_cons : forall Delta1 x i Delta2 y ys is' x' i',
    length ys = length is' ->
    fresh (dom (Delta1 & x ~ i & Delta2)) (S (length ys)) (x' :: ys) ->
    x # Delta2 ->
    init_binds_sub x (Delta1 & x ~ i & Delta2) y (Delta1 & Delta2) ->
    init_binds_sub x (Delta1 & x ~ i & Delta2 & ys ~** is' & x' ~ i') y (Delta1 & Delta2 & ys ~** is' & x' ~ i').
Proof.
  intros * Hlen Hfr Hfrx Hibsub.
  rewrite <- concat_assoc; rewrite <- singles_rev_cons.
  rewrite <- concat_assoc with (G:=(x' ~ i')); rewrite <- singles_rev_cons.
  apply init_binds_sub_push_fresh; auto using fresh_app.
  repeat (rewrite List.app_length, Nat.add_comm; simpl); auto.
Qed.

Lemma init_binds_sub_substitution_middle_subst :
  forall (Delta1 : init_ctx) (x : var) (i' : init_typ) (Delta2 : init_ctx) (vs : vars)
    (z y : var) (i : init_typ),
    x # Delta2 ->
    init_binds_sub x (Delta1 & x ~ i' & Delta2) y (Delta1 & Delta2) ->
    init_var (Delta1 & x ~ i' & Delta2) vs z i ->
    init_var (Delta1 & Delta2) (vs /[ x -> y]) (z \[ x -> y]) i.
Proof.
  intros * Hfr Hibsub Hiv.
  assert (forall i z, binds z i (Delta1 & x ~ i' & Delta2) ->
                  binds z i (Delta1 & Delta2) \/
                 z = x /\ i = i') as Hcases.
  { clear. intros * Hbi.
    apply binds_middle_inv in Hbi.
    destruct_all; auto. }
  remember (Delta1 & x ~ i' & Delta2) as D eqn:HeqD.
  induction Hiv; subst; eauto.
  - constructor.
    cases_if; eauto using binds_middle_neq_binds.
    apply Hibsub in H. destruct H as [?i [His Hbiy]]; inversions His; auto.
  - apply init_var_free; auto using vars_subst_in.
    cases_if; eauto using binds_middle_neq_binds.
    apply Hibsub in H0. destruct H0 as [?i [His Hbiy]]; inversions His; auto.
  - cases_if.
    + apply Hibsub in H0. destruct H0 as [?i [His Hbiy]]; inversions His; eauto.
      * apply init_var_unspec; auto using vars_subst_in1.
      * apply init_var_sub with (i' := free); auto using vars_subst_in1.
    + apply init_var_unspec; auto using vars_subst_in2.
      eauto using binds_middle_neq_binds.
Qed.

Lemma init_binds_sub_subst_cond_push : forall (Delta : init_ctx) (x y : var) (vs : vars) (i : init_typ),
    init_var Delta vs x i ->
    init_binds_sub y (Delta & y ~ i) x Delta.
Proof.
  intros * Hiv.
  intros i' Hbi'.
  pose proof (binds_push_eq_inv Hbi'); subst i'; clear Hbi'.
  inversion Hiv; subst; eauto using init_var_typing_implies_bound_sub.
Qed.
