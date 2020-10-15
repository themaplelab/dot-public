(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Effects.

Implicit Type (ℰ : eff_ctx).

(** * Effect Context Update *)
(** [eff_update ℰ x E ℰ'] represents the relation [ℰ' = ℰ[x := E]], where [ℰ] us
    updated so that [x] now maps to [E]. *)
Definition eff_update ℰ x effs' ℰ' :=
  dom ℰ = dom ℰ' /\
  binds x effs' ℰ' /\
  forall y effs,
            y <> x ->
            binds y effs ℰ ->
            binds y effs ℰ'.

(** ** Effect Context Updates exists *)
Section EffUpdateExists.
  Lemma eff_update_exists : forall ℰ x effs',
    x \in dom ℰ ->
          (exists ℰ', eff_update ℰ x effs' ℰ').
  Proof.
    intros. exists (ℰ & x ~ effs').
    unfold eff_update; repeat_split_right; auto.
    induction ℰ using env_ind; simpl_dom.
    - exfalso; rewrite in_empty in *; auto.
    - rewrite in_union, in_singleton in *.
      destruct H; subst.
      + rewrite union_assoc, union_same; auto.
      + apply IHℰ in H; auto. rewrite H at 1.
        rewrite union_comm_assoc at 1; auto.
  Qed.

  Lemma eff_update_ok_exists : forall ℰ x effs',
      ok ℰ ->
      x \in dom ℰ ->
            (exists ℰ', ok ℰ /\ eff_update ℰ x effs' ℰ').
  Proof.
    induction ℰ using env_ind; intros.
    - rewrite dom_empty, in_empty in *; exfalso; auto.
    - rewrite dom_push, in_union, in_singleton in *.
      destruct_ors; subst.
      + exists (ℰ & x ~ effs'); unfold eff_update;
          repeat_split_right; simpl_dom; auto.
        introv Hneq Hbi.
        apply binds_push_neq_inv in Hbi;
          eauto using binds_push_neq.
      + apply ok_push_inv in H. destruct_ands.
        specialize (IHℰ _ effs' H H0) as [ℰ' [Hok Heu]].
        exists (ℰ' & x ~ v). split; auto. unfold eff_update in *.
        destruct_ands; repeat_split_right; simpl_dom; try congruence.
        * assert (x <> x0) by congruence.
          apply binds_push_neq; eauto.
        * intros.
          apply binds_push_inv in H6; destruct_ors; destruct_ands; subst; auto.
  Qed.
End EffUpdateExists.


(** * Effect Set Updates *)
(** [eff_remove E x a E'] represets the relation [E' = E ∖ (x,a)], i.e. E' is
    the effect set [E], but with [(x,a)] removed. *)
Definition eff_remove (effs : effects) x a effs' :=
  (x,a) \notin (from_list effs') /\
  (forall eff, eff <> (x,a) ->
               eff \in (from_list effs) -> eff \in (from_list effs')) /\
  (from_list effs') \c (from_list effs).
