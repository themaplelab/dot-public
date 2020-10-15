(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import AbstractSyntax Typing
        GeneralTyping
        RecordTypes InertTypes DefRecordInertTyping PreciseTyping TightTyping
        InvertibleTyping GeneralToTight InertTightSubtyping
        Weakening Substitution RenameConstructors.

Hint Resolve general_to_tight_typing : core.

(** In this module we prove some inversion lemmas about general typing under
    inert contexts. *)

Lemma inert_trm_con_typing : forall G Ts is' T Ts' is'' T' ds t,
    inert G ->
    G ⊢ lit_con Ts' is'' T' ds t ∶ typ_con Ts is' T ->
    Ts' = Ts /\ T' = T /\ is'' = is'.
Proof.
  introv Hi HT.
  apply inert_con_typing in HT; inversions HT; auto.
Qed.

Lemma inert_trm_con_defs : forall G Ts is' T ds t,
    inert G ->
    G ⊢ lit_con Ts is' T ds t ∶ typ_con Ts is' T ->
    exists L, forall (x : var) (ys : list var),
        length ys = length_s Ts ->
        fresh L (S (length ys)) (x :: ys) ->
        G & ys ~** to_list Ts & x ~ open_vars (x :: ys) T ⊢
        open_vars (x :: ys) ds ∶ open_vars (x :: ys) T.
Proof.
  introv Hi Ht. inversions Ht; eauto.
Qed.

Lemma inert_trm_con_trm : forall G Ts is' T ds t,
    inert G ->
    G ⊢ lit_con Ts is' T ds t ∶ typ_con Ts is' T ->
    exists L T', forall (x : var) (ys : list var),
        length ys = length_s Ts ->
        fresh L (S (length ys)) (x :: ys) ->
        (G & ys ~** to_list Ts & x ~ open_vars (x :: ys) T)
          ⊢ open_vars (x :: ys) t ∶ open_vars (x :: ys) T'.
Proof.
  introv Hi Ht. inversions Ht; eauto.
Qed.

Lemma inert_trm_con_apply_trm : forall G Ts is' T ds t x xs avs,
    inert G ->
    G ⊢ lit_con Ts is' T ds t ∶ typ_con Ts is' T ->
    x # G ->
    x \notin fv (open_rec_vars 1 xs ds) ->
    length xs = length_s Ts ->
    vars_of_avars xs avs ->
    G ⊢ avs :: Ts ->
    exists T', G & x ~ open_rec_vars 1 xs (open x T)
                ⊢  open_rec_vars 1 xs (open x t) ∶ T'.
Proof.
  intros.
  apply (inert_trm_con_trm H) in H0. destruct H0 as [L [T' Htrm]].
  apply (rename_con_vars_open_push (x:=x) (xs:=xs) (avs:=avs)) in Htrm; auto.
  eauto.
Qed.

Lemma inert_trm_con_apply_defs : forall G Ts is' T ds t x xs avs,
    inert G ->
    G ⊢ lit_con Ts is' T ds t ∶ typ_con Ts is' T ->
    x # G ->
    x \notin fv (open_rec_vars 1 xs ds) ->
    length xs = length_s Ts ->
    vars_of_avars xs avs ->
    G ⊢ avs :: Ts ->
    G & x ~ open_rec_vars 1 xs (open x T)
          ⊢ open_rec_vars 1 xs (open x ds)
          ∶ open_rec_vars 1 xs (open x T).
Proof.
  intros.
  apply (inert_trm_con_defs H) in H0. destruct H0 as [L Hdefs].
  apply (rename_con_vars_open_push (x:=x) (xs:=xs) (avs:=avs)) in Hdefs; auto.
Qed.

Lemma inert_trm_con_record_type : forall G Ts is' T ds t,
    inert G ->
    G ⊢ lit_con Ts is' T ds t ∶ typ_con Ts is' T ->
    record_type T.
Proof.
  introv Hi Ht. pose proof (inert_trm_con_defs Hi Ht) as [L H].
  assert (Fr: exists x ys, fresh (L \u fv T) (S (length_s Ts)) (cons x ys)).
  { destruct (var_freshes (L \u fv T) (S (length_s Ts))) as [xys ?Fr].
    assert (length xys = S (length_s Ts)) by eauto.
    destruct xys; simpls; try congruence. exists v xys; auto. }
  destruct Fr as [x [ys Fr]].
  assert (Hlen: length ys = length_s Ts) by eauto.
  rewrite <- Hlen in Fr.
  assert (Fr': fresh L (S (length ys)) (x :: ys)) by auto.
  specialize (H _ _ Hlen Fr'). pose proof (ty_defs_record_type H).
  eapply record_type_open_rec_vars; eauto; auto.
Qed.
