(** remove printing ~ *)

Set Implicit Arguments.

Require Import DotTactics LibExtra.
Require Import AbstractSyntax PreTyping Typing GeneralTyping Weakening SubstitutionClass Substitution.

(** In this module we specialize the substitution lemma for functions with
    multiple arguments *)

Section AboutRenameCon.
  Context {A : Set} {SA : SubstVar A} {TyA : Typing A}.
  Context {TySM : TySubstMiddle TyA}.
  Context {OA : Openable A} {FA : FreeVar A} {AS : AbstractSyntax OA FA SA}.
  Context {SI : SubstIntro AS}.

  Hint Extern 2 => simple apply weaken : core.

  Lemma rename_con_middle_var : forall y' n T' Gamma T T'' t x x',
    x # Gamma ->
    y' \notin (fv T \u fv T' \u fv T'' \u fv t \u fv_env Gamma \u dom Gamma \u \{x}) ->
    Gamma & y' ~ T' & x ~ open_rec n y' T ⊢ open_rec n y' t ∶ open_rec n y' T'' ->
    Gamma ⊢ trm_var (avar_f x') ∶ T' ->
    Gamma & x ~ open_rec n x' T ⊢ open_rec n x' t ∶ open_rec n x' T''.
  Proof.
    intros.
    repeat rewrite (subst_intro (x:=y') x' n); auto.
    rewrite subst_single.
    apply ty_subst_middle with (y:=x') (S:=T');
      rewrite ? map_single;
      repeat rewrite <- subst_intro by auto;
      repeat rewrite subst_fresh by auto;
      auto.
  Qed.

  Context {FOC: FvOpenCases AS}.

  (** Special version of the subsitution lemma for rename_coning *)
  Lemma rename_con_middle_ind_case : forall G x x0 x1 n ys T Ts t U T',
      x0 # G ->
      length ys = length_s Ts ->
      fresh
        (fv T \u
            fv Ts \u fv U \u
            fv t \u fv T' \u fv_env G \u dom G \u \{ x0})
        (length (x :: ys)) (x :: ys) ->
      G ⊢ trm_var (avar_f x1) ∶ U ->
      G & ys ~** to_list Ts & x ~ U &
      x0 ~ open_rec (n + length ys) x (open_rec_vars n ys T)
         ⊢ open_rec (n + length ys) x (open_rec_vars n ys t)
         ∶ open_rec (n + length ys) x (open_rec_vars n ys T') ->
      G & ys ~** to_list Ts &
      x0 ~ open_rec (n + length ys) x1 (open_rec_vars n ys T)
         ⊢ open_rec (n + length ys) x1 (open_rec_vars n ys t)
         ∶ open_rec (n + length ys) x1 (open_rec_vars n ys T').
  Proof.
    intros * Hfr Hlen Hfrs; intros.
    eapply rename_con_middle_var;
      eauto 4 using fresh_cons_notin_rev.
    rewrite fv_in_values_concat, fv_env_singles, <- ? union_assoc by auto.
    rewrite dom_concat, dom_singles by (rewrite liblist_length; auto).
    notin_solve; try apply notin_open_rec_vars_list;
      auto 2 using from_list_fresh.
    apply weaken_fresh_list; auto.
    destruct Hfrs; auto.
  Qed.

  Context {OC: OpenCommut OA}.
  Lemma rename_con_middle_singles : forall ys n Ts L G T T' t x avs xs,
      x # G ->
      length ys = length_s Ts ->
      fresh (L \u fv T \u fv Ts
               \u fv t \u fv T'
               \u fv_env G \u dom G \u \{x}) (length ys) ys ->
      G & (ys ~** to_list Ts) & x ~ open_rec_vars n ys T ⊢
                                  open_rec_vars n ys t ∶ open_rec_vars n ys T' ->
      G ⊢ avs :: Ts ->
      vars_of_avars xs avs ->
      G & x ~ open_rec_vars n xs T ⊢ open_rec_vars n xs t ∶ open_rec_vars n xs T'.
  Proof.
    induction ys using List.rev_ind.
    - intros. destruct Ts; inversion H0.
      simpl in H2. rewrite singles_nil, concat_empty_r in H2.
      inversions H3. inversions H4. auto.
    - intros n Ts. gen n. induction Ts using listlike_rev_ind.
      intros. rewrite List.app_length, Nat.add_1_r in H0. inversion H0.
      clear IHTs. intros.
      (* simplify length  eq *)
      rewrite List.app_length, app_s_length_s, ? Nat.add_1_r in H0. inversion H0.
      (* simplify H2 context *)
      sympl in H2.
      rewrite singles_rev_cons, concat_assoc in H2.
      (* simplify H2 typing *)
      repeat rewrite open_vars_app in H2. sympl in H2.
      repeat rewrite open_rec_vars_open_rec_commut in H2 by omega.
      (* *)
      apply fresh_app in H1; simpl List.app in H1.
      (* split up avar typing in H3 *)
      apply ty_avars_concat in H3.
      destruct H3 as [avs1 [avs2 [?H [?H ?H]]]]; subst.
      inversions H7. inversions H12.
      (* split vars of avars typing in H4 *)
      apply vars_of_avars_app_r in H4.
      destruct H4 as [ys' [zs' [?H [?H ?H]]]]; subst.
      inversions H7. inversions H9.
      (* weaken H2 *)
      clear H0. rename H6 into H0.
      simpl of_list in H1; simpl app_s in H1.
      rewrite of_list_app, fv_app_union,
      to_list_of_list, fv_one, <- ? union_assoc in H1.
      apply (rename_con_middle_ind_case (x1:=x1)) in H2; auto 2.

      (* Proving goal *)
      repeat rewrite open_vars_app. sympl.
      eapply IHys with (L:=L); eauto 2.
      + sympl in H1.
        destruct H1. fresh_solve; eauto 3.
        * destruct (fv_open_cases x1 T (n + length ys'))
            as [Hfveq | Hfveq]; rewrite Hfveq; auto.
          apply typing_implies_bound in H11. destruct H11 as [?S H11].
          apply binds_to_dom in H11.
          fresh_solve. eauto using fresh_single_in.
        * destruct (fv_open_cases x1 t (n + length ys'))
          as [Hfveq | Hfveq]; rewrite Hfveq; auto.
          apply typing_implies_bound in H11. destruct H11 as [?S H11].
          apply binds_to_dom in H11.
          fresh_solve. eauto using fresh_single_in.
        * destruct (fv_open_cases x1 T' (n + length ys'))
          as [Hfveq | Hfveq]; rewrite Hfveq; auto.
          apply typing_implies_bound in H11. destruct H11 as [?S H11].
          apply binds_to_dom in H11.
          fresh_solve. eauto using fresh_single_in.
      + assert (length ys = length ys').
        { apply length_vars_of_avars in H4.
          apply length_ty_avars in H5. omega. }
        repeat rewrite open_rec_vars_open_rec_commut by omega.
        rewrite <- H3; auto.
  Qed.

  Lemma rename_con_vars_L : forall L Gamma xs avs Ts T t T',
      (forall x ys,
          length ys = length_s Ts ->
          fresh L (S (length ys)) (x :: ys) ->
          (Gamma & (ys ~** (to_list Ts)) & (x ~ open_vars (x :: ys) T)
               ⊢ (open_vars (x :: ys) t)
               ∶ (open_vars (x :: ys) T'))) ->
      length xs = length_s Ts ->
      vars_of_avars xs avs ->
      Gamma ⊢ avs :: Ts ->
      exists L', (forall x : var,
                x \notin L' ->
                Gamma & (x ~ open x (open_rec_vars 1 xs T))
                      ⊢ (open x (open_rec_vars 1 xs t))
                      ∶ (open x (open_rec_vars 1 xs T'))).
  Proof.
    introv Hkon Hlen Hxs Havs.
    exists (L \u dom Gamma). intros x HxL.
    pose proof (var_freshes (L \u fv (open x T) \u fv Ts
                               \u fv (open x t) \u fv (open x T')
                               \u fv_env Gamma \u dom Gamma \u \{x}) (length xs))
      as [ys Hfr].
    pose proof (fresh_length _ _ _ Hfr) as Hys.
    assert (HfrL: fresh L (S (length ys)) (x :: ys)) by auto.
    assert (HlenTs: length ys = length_s Ts) by congruence.
    assert (Hfr' : x # Gamma) by auto.
    repeat rewrite <- open_vars_S_commut.
    eapply rename_con_middle_singles with (L:=L); eauto.
  Qed.

  Context {TyWM: PreTypingWeakenMiddle (TyPreTyping TyA)}.

  Lemma rename_con_vars_open_push : forall L Gamma x xs avs Ts T t T',
      x # Gamma ->
      (forall x ys,
          length ys = length_s Ts ->
          fresh L (S (length ys)) (x :: ys) ->
          (Gamma & (ys ~** (to_list Ts)) & (x ~ open_vars (x :: ys) T)
               ⊢ (open_vars (x :: ys) t)
               ∶ (open_vars (x :: ys) T'))) ->
      length xs = length_s Ts ->
      vars_of_avars xs avs ->
      Gamma ⊢ avs :: Ts ->
      Gamma & (x ~ open_vars (x :: xs) T)
            ⊢ (open_vars (x :: xs) t) ∶ (open_vars (x :: xs) T').
    Proof.
      introv Hfr Hkon Hlen Hxs Havs.
      pose proof
           (@rename_con_vars_L L Gamma xs avs Ts T t T' Hkon Hlen Hxs Havs)
        as [L' HL].
      sympl. repeat rewrite open_vars_S_commut.
      eapply renaming_open_push; try eassumption.
    Qed.
End AboutRenameCon.
