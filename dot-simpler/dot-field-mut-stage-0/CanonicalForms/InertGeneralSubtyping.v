(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibExtra DotTactics.
Require Import AbstractSyntax
        GeneralTyping RecordAndInertTypes PreciseTyping TightTyping
        InvertibleTyping GeneralToTight InertTightSubtyping
        Weakening Substitution.

Hint Resolve general_to_tight_typing : core.

Lemma inert_trm_obj_typing : forall G T T' ds,
    inert G ->
    G ⊢ lit_obj T' ds ∶ typ_bnd T ->
    T' = T.
Proof.
  introv Hi HT.
  inversions HT; auto.
Qed.

Lemma inert_trm_obj_defs : forall G T ds,
    inert G ->
    G ⊢ lit_obj T ds ∶ typ_bnd T ->
    exists L,
      forall (x : var),
        x \notin L ->
        G & x ~ open x T ⊢ open x ds ∶ open x T.
Proof.
  introv Hi Ht. inversions Ht; eauto.
Qed.

Lemma inert_trm_con_apply_defs : forall G T ds x,
    inert G ->
    G ⊢ lit_obj T ds ∶ typ_bnd T ->
    x # G ->
    G & x ~ open x T ⊢ open x ds ∶ open x T.
Proof.
  intros.
  apply (inert_trm_obj_defs H) in H0. destruct H0 as [L Hdefs].
  remember (L \u fv T
              \u fv ds \u fv_env G
              \u dom G \u \{ x}) as L' eqn:Heq.
  assert (exists x', x' \notin L').
  { pick_fresh_gen L' x'.
    exists x'. auto. }
  destruct H0 as [x' ?H].
  assert (x' \notin L) by (subst L'; auto).
  specialize (Hdefs _ H2). clear H2.
  assert (ok (G & x ~ open x T)) by auto.
  assert (x' # (G & x ~ open x T)) by (subst L'; auto).
  eapply weaken_rules in Hdefs; try reflexivity; try eassumption.
  eapply renaming_def; eauto 2.
  rewrite fv_env_push, <- ? union_assoc.
  subst L'; notin_solve.
  destruct (fv_open_cases x T 0) as [Hr | Hr]; rewrite Hr; auto.
Qed.

Lemma inert_trm_obj_record_type : forall G T ds,
    inert G ->
    G ⊢ lit_obj T ds ∶ typ_bnd T ->
    record_type T.
Proof.
  introv Hi Ht. pose proof (inert_trm_obj_defs Hi Ht) as [L H].
  assert (Fr: exists x, x \notin L \u fv T).
  { pick_fresh_gen (L \u fv T) x. exists x. auto. }
  destruct Fr as [x Fr].
  assert (Fr': x \notin L) by auto.
  specialize (H _ Fr'). pose proof (ty_defs_record_type H).
  eapply record_type_open_rec; eauto; auto.
Qed.
