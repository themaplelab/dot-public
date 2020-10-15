(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import PreTyping Typing GeneralTyping Weakening.
Require Import Effects InitVar InitTyping.

(** This module collects together some miscellaneous lemmas about initailization
    typing. Many of these are lifted versions of InitLookup lemmas. *)

Lemma commit_typing_implies_bound : forall Gamma Delta x,
    Gamma ⸴ Delta ⊢c trm_var (avar_f x) ->
    binds x committed Delta.
Proof.
  inversion 1; auto.
Qed.

Lemma init_typing_implies_bound : forall Gamma Delta vs x i,
    Gamma ⸴ Delta ⸴ vs ⊢i trm_var (avar_f x) ∶ i ->
    exists i', binds x i' Delta.
Proof.
  inversion 1; subst;
    eauto using init_var_typing_implies_bound,
    commit_typing_implies_bound.
Qed.

Lemma init_typing_committed_inv : forall Gamma Delta vs x,
    Gamma ⸴ Delta ⸴ vs ⊢i trm_var (avar_f x) ∶ committed ->
    binds x committed Delta.
Proof.
  introv H. inversions H.
  - inversions H4; auto.
  - inversions H0; auto.
Qed.

Lemma well_committed_vars_of_avars : forall Gamma Delta ys avs,
    vars_of_avars ys avs ->
    Gamma ⸴ Delta ⊢c avs ->
    (forall y, y \in from_list ys -> binds y committed Delta).
Proof with eauto.
  induction ys.
  - intros. rewrite from_list_nil in H1. rewrite in_empty in H1. destruct H1.
  - intros. inversion H; subst. inversion H0; subst.
    rewrite from_list_cons in H1. rewrite in_union in H1.
    rewrite in_singleton in H1.
    destruct H1.
    + subst. inversion H7; subst...
    + eapply IHys...
Qed.

Lemma init_avars_concat : forall is1 is2 Gamma Delta vs avs,
    Gamma ⸴ Delta ⸴ vs ⊢i avs :: (is1 ++ is2) ->
    exists avs1 avs2,
      avs = (avs1 ++ avs2)%list /\
      Gamma ⸴ Delta ⸴ vs ⊢i avs1 :: is1 /\ Gamma ⸴ Delta ⸴ vs ⊢i avs2 :: is2.
Proof.
  induction is1 as [|i is1 IHis1]; simpl; intros * Hinits.
  - exists (@nil avar) avs; simpl; repeat_split_right; auto; try constructor.
  - inversion Hinits as [| ?Gamma ?Delta ?vs ?x ?i avs' ?is' Hi His];
      subst.
    apply IHis1 in His.
    destruct His as [avs1 [avs2 [Heq [?H ?H]]]]; subst.
    exists (avar_f x :: avs1)%list avs2; simpl.
    repeat_split_right; auto.
Qed.

Lemma init_avars_concat_l : forall avs1 avs2 Gamma Delta vs is',
    Gamma ⸴ Delta ⸴ vs ⊢i (avs1 ++ avs2)%list :: is' ->
    exists is1 is2,
      is' = (is1 ++ is2)%list /\
      Gamma ⸴ Delta ⸴ vs ⊢i avs1 :: is1 /\ Gamma ⸴ Delta ⸴ vs ⊢i avs2 :: is2.
Proof.
  induction avs1 as [|av avs1 IHavs1]; simpl; intros * Hinits.
  - exists (@nil init_typ) is'; simpl; repeat_split_right; auto; try constructor.
  - inversion Hinits as [| ?Gamma ?Delta ?vs ?x ?i ?avs is'' Hi His];
      subst.
    apply IHavs1 in His.
    destruct His as [is1 [is2 [Heq [?H ?H]]]]; subst.
    exists (i :: is1)%list is2; simpl.
    repeat_split_right; auto.
Qed.

Lemma all_comm_unspec_inits : forall Gamma Delta avs is,
    all_comm_unspec is ->
    length avs = length is ->
    Gamma ⸴ Delta ⊢c avs ->
    Gamma ⸴ Delta ⸴ \{} ⊢i avs :: is.
Proof with eauto.
  introv Hac Hlen Hwc.
  generalize dependent is. induction avs; intros.
  - simpl in Hlen. destruct is; inversions Hlen...
  - simpl in Hlen. destruct is; inversions Hlen. rename H0 into Hlen.
    inversions Hac. rename H1 into Hcu. rename H2 into Hac.
    inversions Hwc. rename H3 into Hwc. rename H4 into Hwcs.
    econstructor... inversion Hwc; subst. rename H2 into Hbin.
    econstructor. destruct Hcu; subst.
    + apply init_var_commit...
    + apply init_var_commit_unspec...
Qed.
