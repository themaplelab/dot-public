(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import PreTyping Typing GeneralTyping Weakening.
Require Import Substitution.
Require Import InitVar InitVarSubtyping InitTyping InitTypingLemmas InitWeakening.
Require Import EffectSubstitution InitSubstitution.

Implicit Types (i : init_typ) (t : trm) (l : lit) (avs : avars).

Local Hint Resolve init_var_weaken_vars init_var_weaken_D init_var_more_committed : core.
Local Hint Extern 2 => simple apply weaken_ok_middle : core.
Local Hint Extern 2 => simple apply weaken_middle : core.
Local Hint Resolve init_var_substitution_middle_empty init_var_substitution_middle_remove : core.

(* For replacements *)
Local Hint Resolve concat_empty_r : core.
Local Hint Extern 2 (?Gamma & (subst_env ?x ?y) empty = ?Gamma) =>
rewrite map_empty; apply concat_empty_r : core.


(** * Renaming Lemmas *)
(** For Substitution into let frames *)
Lemma renaming_fresh_init : forall Gamma Delta vs T L x t i i',
    ok Gamma ->
    Gamma ⊢ trm_var (avar_f x) ∶ T ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_var (avar_f x) ∶ i ->
    (forall x : var,
        x \notin L ->
        Gamma & x ~ T ⸴ Delta & x ~ i ⸴ vs \u \{ x} ⊢i open x t ∶ i') ->
    Gamma ⸴ Delta ⸴ vs ⊢i open x t ∶ i'.
Proof.
  introv ok_Gamma x_typ x_init fresh_open_init.
  pick_fresh_gen ((fv t) \u (fv T) \u L \u (fv_env Gamma) \u (dom Gamma)
                         \u (dom Delta) \u vs \u \{ x}) y.
  repeat (rewrite notin_union in Fr).
  destruct Fr as
      [[[[[[[y_notin_t y_notin_T] y_notin_L]
             y_notfree_Gamma] y_notin_Gamma] y_notin_Delta] y_notin_vs] y_notin_x].
  assert (y \notin vs \u \{ x}) as y_notin_vs_x by auto.
  replace (open x t) with ((open y t) /[y -> x])
    by (erewrite <- subst_intro; eauto).
  specialize (fresh_open_init y y_notin_L) as open_y_init.
  apply init_strengethen_vs with (x := x) (i := i); eauto.
  rewrite <- (vars_subst_notin x y_notin_vs),
  (vars_subst_singleton_same x y),
  <- vars_subst_union.
  eapply well_init_subst_term_push;
    eauto 4 using init_var_subst_cond_push.
  rewrite subst_fresh by auto; auto.
  inversions x_init.
  - eapply init_binds_sub_subst_cond_push; eauto.
  - inversions H.
    eapply init_binds_sub_subst_cond_push with (vs:=\{}); eauto using init_var_commit.
Qed.

(** For Substitution into constructor bodies *)
Lemma renaming_con_no_args : forall L Gamma Delta vs T x t i,
    ok Gamma ->
    x # Gamma ->
    x # Delta ->
    (forall (x : var),
        x \notin L ->
        Gamma & x ~ open x T
        ⸴ Delta & x ~ free
        ⸴ vs \u \{ x} ⊢i open x t ∶ i) ->
    Gamma & x ~ open x T ⸴ Delta & x ~ free ⸴ vs \u \{ x} ⊢i open x t ∶ i.
Proof.
  intros * Hok HxG HxD HOpen.
  pick_fresh_gen
    (L \u fv (open x t) \u fv (open x T)
       \u fv_env Gamma \u dom Delta \u \{ x} \u vs
       \u fv t \u fv T \u dom Gamma)
    y.
  assert (y \notin L) as Hy by auto; apply HOpen in Hy.
  rewrite subst_intro with (x0:=y) (y0:=x) by auto.
  rewrite subst_intro with (x0:=y) (y0:=x) by auto.
  assert (x # (Gamma & y ~ open y T)) as HxG' by auto.
  assert (x # (Delta & y ~ free)) as HxD' by auto.
  pose proof (init_weaken_same_vars
                (open x T) free _ _ i
                Hy HxG' HxD') as HySubst.
  apply well_init_subst_term with (x:=y) (y:=x)
    in HySubst; auto.
  + rewrite vars_subst_union in HySubst.
    rewrite <- vars_subst_singleton_same in HySubst.
    rewrite vars_subst_notin in HySubst by auto.
    rewrite <- subst_single in HySubst.
    rewrite <- subst_intro by auto.
    rewrite subst_fresh in HySubst by auto.
    auto.
  + rewrite <- subst_single.
    rewrite subst_fresh by auto.
    rewrite <- subst_intro by auto.
    auto.
  + assert (x <> y) as Hneq by auto.
    intros i' Hbi'. exists free.
    split; auto.
    apply binds_push_neq_inv in Hbi'; auto.
    apply binds_push_eq_inv in Hbi'; subst; auto.
Qed.

(** We prove some renaming lemmas about multiple arguments. For now, we prove
them in a general form, without worrying about the [this] variable. *)
Lemma renaming_con_middle_var :
  forall y' n T' i' Gamma Delta vs T i t x x',
    ok Gamma ->
    x # Gamma ->
    x # Delta ->
    y' \notin (fv T \u fv T' \u fv t
              \u fv_env Gamma \u dom Gamma \u dom Delta
              \u vs \u \{x} \u \{x'}) ->
    Gamma & y' ~ T' & x ~ open_rec n y' T
    ⸴ Delta & y' ~ i' & x ~ free ⸴
    (vs \u \{x} \u \{y'}) ⊢i open_rec n y' t ∶ i ->
    Gamma ⊢ trm_var (avar_f x') ∶ T' ->
    init_var Delta vs x' i' ->
    Gamma & x ~ open_rec n x' T
    ⸴ Delta & x ~ free ⸴
    vs \u \{ x} ⊢i open_rec n x' t ∶ i.
Proof.
  intros * Hok HxG HxD Hyfr HOpen Hty Hinit.
  repeat rewrite (subst_intro (x:=y') x' n); auto.
  rewrite subst_single.
  assert (x <> x') as Hxx'.
  { intro; subst; apply HxD.
    apply init_var_typing_implies_bound in Hinit as [?i Hin].
    eauto using binds_to_dom. }
  assert (x' # x ~ free) as Hx' by auto.
  assert (y' # x ~ free) as Hy' by auto.
  apply init_var_weaken_D_push with (y:=x) (i':=free) in Hinit;
    auto 2.
  apply init_strengethen_vs with (x := x') (i := i');
    auto using init_var_weaken_vars.
  rewrite <- (@vars_subst_notin y' x' (vs \u \{x})) by auto.
  rewrite (@vars_subst_singleton_same x' y').
  rewrite <- vars_subst_union, <- union_assoc.
  pose proof (init_var_binds_subst_cond (x:=y') (i:=i') Hy' Hinit).
  eapply well_init_subst_term with (i':=i') (T':=T'); eauto.
  rewrite <- subst_single.
  rewrite <- subst_intro, subst_fresh by auto.
  apply weaken; auto.
Qed.

Lemma renaming_con_middle_ind_case :
  forall y n T' i' ys Ts is' Gamma Delta vs T i t x x',
    ok Gamma ->
    x # Gamma ->
    x # Delta ->
    length ys = length_s Ts ->
    length is' = length_s Ts ->
    fresh
      (fv T \u fv Ts \u fv t \u fv T' \u
          fv_env Gamma \u dom Gamma \u dom Delta \u \{ x})
      (length ys) ys ->
    y \notin (fv T \u fv Ts \u fv t \u fv T' \u
             fv_env Gamma \u dom Gamma \u dom Delta \u
             vs \u
             \{ x} \u \{ x'} \u from_list ys) ->
    Gamma & ys ~** to_list Ts & y ~ T' & x ~ open_rec (n + length ys) y (open_rec_vars n ys T)
    ⸴ Delta & ys ~** is' & y ~ i' & x ~ free ⸴
    (vs \u (from_list ys) \u \{x} \u \{y})
    ⊢i open_rec (n + length ys) y (open_rec_vars n ys t) ∶ i ->
    Gamma ⊢ trm_var (avar_f x') ∶ T' ->
    init_var Delta vs x' i' ->
    Gamma & ys ~** to_list Ts & x ~ open_rec (n + length ys) x' (open_rec_vars n ys T)
    ⸴ Delta & ys ~** is' & x ~ free ⸴
    (vs \u from_list ys) \u \{ x} ⊢i open_rec (n + length ys) x' (open_rec_vars n ys t) ∶ i.
Proof.
  intros.
  eapply renaming_con_middle_var with (y':=y) (T':=T') (i':=i').
  - apply fresh_ok_rev_ys with (x:=x); auto.
  - rewrite dom_concat, notin_union; split;
      auto using fresh_notin_dom.
  - rewrite dom_concat, notin_union; split; auto 2.
    apply fresh_notin_dom; try congruence.
    simpl in *; destruct_all; auto.
  - assert (fresh \{ y} (length ys) ys).
    { simpl in *; destruct_all.
      eapply fresh_from_list; eauto. }
    rewrite ? dom_concat, ? notin_union;
      repeat (split;
              try (apply fresh_notin_dom; try congruence);
              try apply notin_open_rec_vars_list); auto.
    rewrite fv_in_values_concat, notin_union,
    fv_env_singles by auto; split; auto 2.
  - rewrite <- union_assoc; auto.
  - apply weaken_ok; eauto 4 using fresh_ok_ys.
  - apply init_var_weaken_vars.
    apply init_var_weaken_D_fresh; auto 2.
    apply fresh_notin_dom; try congruence.
    apply fresh_single_in with (F:=dom Delta); auto.
    inversions H8; eauto using binds_to_dom.
    apply init_var_typing_implies_bound in H9 as [?i Hin].
    eauto using binds_to_dom.
Qed.

Lemma renaming_con_middle_singles :
  forall ys Ts is' n Gamma Delta vs T i t x xs avs,
    ok Gamma ->
    x # Gamma ->
    x # Delta ->
    length ys = length_s Ts ->
    length is' = length_s Ts ->
    fresh (fv T \u fv Ts
              \u fv t
              \u fv_env Gamma \u dom Gamma \u dom Delta \u \{x}
              \u vs)
          (length ys) ys ->
    Gamma & ys ~** to_list Ts & x ~ open_rec_vars n ys T
    ⸴ Delta & ys ~** is' & x ~ free ⸴
    vs \u (from_list ys) \u \{x}
    ⊢i open_rec_vars n ys t ∶ i ->
    Gamma ⊢ avs :: Ts ->
    Gamma⸴ Delta⸴ vs ⊢i avs :: is' ->
    vars_of_avars xs avs ->
    Gamma & x ~ open_rec_vars n xs T
    ⸴ Delta & x ~ free ⸴
    vs \u \{x} ⊢i open_rec_vars n xs t ∶ i.
Proof.
  induction ys as [| y ys IHys] using List.rev_ind.
  - intros * Hok HfrG HfrD HysTs HisTs Hysfr HOpen HavsTs
                 Havsis Hxsavs.
    induction Ts; try (simpl in *; inversion HysTs).
    induction is'; try (simpl in *; inversion HisTs).
    inversions HavsTs; inversions Hxsavs. simpl.
    rewrite ? singles_nil, ? concat_empty_r,
    ? from_list_nil, ? union_empty_l in HOpen.
    auto.
  - induction Ts as [| Tx' Ts' _] using listlike_rev_ind;
      [intros * Hok HfrG HfrD HysTs;
       rewrite List.app_length, Nat.add_1_r in HysTs;
       simpl in HysTs;
       inversion HysTs|].

    intros * Hok HfrG HfrD HysTs HisTs Hysfr HOpen HavsTs
                 Havsis Hxsavs.

    rewrite List.app_length, app_s_length_s, ? Nat.add_1_r
      in HysTs.
    rewrite app_s_length_s, ? Nat.add_1_r in HisTs.

    pose proof (ty_avars_concat _ _ HavsTs)
      as [avs'' [avx [Heq [HavsTs' HavTx']]]]; subst.
    inversion HavTx' as [| ?Gamma x'' ?T ?avs ?Ts Htyx' Hnil];
      subst; inversions Hnil.

    pose proof (vars_of_avars_app_r _ _ Hxsavs)
      as [xs' [x''' [Heq [Hxsavs' Hx'av]]]].
    inversion Hx'av as [|? ? ? Hnil];
      subst; inversions Hnil; clear Hx'av.

    pose proof (init_avars_concat_l _ _ Havsis)
      as [is1 [is2 [Heq [Havsis' Havsx]]]]; subst.
    inversion Havsx as [|? ? ? ? i' ? ? Havx Hnil];
      subst; inversions Hnil.
    rewrite List.app_length, ? Nat.add_1_r in HisTs.
    inversion HisTs as [HisTs']; inversion HysTs as [HysTs'].

    rewrite ? open_vars_app; sympl.
    eapply IHys; clear IHys; eauto.
    + apply fresh_app in Hysfr. sympl in Hysfr.
      rewrite of_list_app, fv_app_union,
      to_list_of_list, fv_one, <- ? union_assoc in Hysfr.
      destruct Hysfr as [Hyfr Hysfr].
      assert (fresh \{ x''} (length ys) ys).
      { apply fresh_single_in with (F:=dom Gamma); auto.
        destruct (typing_implies_bound Htyx') as [? ?].
        eauto using binds_to_dom. }
      fresh_solve; auto.
      * pose proof (fv_open_cases x'' T (n + length xs'))
          as [Heq | Heq]; rewrite Heq; fresh_solve.
      * pose proof (fv_open_cases x'' t (n + length xs'))
          as [Heq | Heq]; rewrite Heq; fresh_solve.
    + rewrite union_assoc.
      pose proof (length_ty_avars HavsTs').
      pose proof (length_vars_of_avars Hxsavs').
      rewrite open_rec_vars_open_rec_commut by omega.
      rewrite open_rec_vars_open_rec_commut by omega.
      assert (length xs' = length ys) as Hxsys by omega.
      rewrite ? Hxsys.

      apply fresh_app in Hysfr. sympl in Hysfr.
      rewrite of_list_app, fv_app_union,
      to_list_of_list, fv_one, <- ? union_assoc in Hysfr.
      destruct Hysfr as [Hyfr Hysfr].
      assert (x'' \in dom Gamma).
      { destruct (typing_implies_bound Htyx') as [? ?];
          eauto using binds_to_dom. }
      assert (fresh \{ x''} (length ys) ys).
      { apply fresh_single_in with (F:=dom Gamma); auto. }
      eapply renaming_con_middle_ind_case with
          (Gamma:=Gamma) (vs:=vs) (ys:=ys) (y:=y) (Ts:=Ts') (x:=x)
          (i':=i'); eauto 3.
      * fresh_solve; auto.
      * notin_solve; auto.
        -- rewrite notin_singleton; intro; subst;
             apply Hyfr; rewrite ? in_union; auto 7.
        -- apply from_list_fresh; auto.
      * sympl in HOpen.
        rewrite ? singles_rev_cons, ? concat_assoc in HOpen.
        rewrite <- open_rec_vars_open_rec_commut by omega.
        rewrite <- open_rec_vars_open_rec_commut by omega.
        change (open_rec (n + length ys) y T) with
            (open_rec_vars (n + length ys) (y :: nil) T).
        change (open_rec (n + length ys) y t) with
            (open_rec_vars (n + length ys) (y :: nil) t).
        rewrite <- open_vars_app.
        rewrite <- open_vars_app.
        rewrite union_comm with (E:=\{ x}).
        rewrite from_list_concat, from_list_cons, from_list_nil,
        union_empty_r, <- ? union_assoc in HOpen; auto.
      * inversions Havx; auto.
        constructor. inversion H3; auto.
Qed.

Lemma renaming_con : forall L Gamma Delta vs xs Ts avs is' T x t i,
    ok Gamma ->
    x # Gamma ->
    x # Delta ->
    length xs = length_s Ts ->
    length is' = length_s Ts ->
    vars_of_avars xs avs ->
    Gamma ⊢ avs :: Ts ->
    Gamma ⸴ Delta ⸴ vs ⊢i avs :: is' ->
    (forall (x : var) (ys : list var),
        length ys = length_s Ts ->
        fresh L (S (length ys)) (x :: ys) ->
        Gamma & ys ~** to_list Ts & x ~ open_vars (x :: ys) T
        ⸴ Delta & ys ~** is' & x ~ free ⸴
        from_list ys \u \{ x} ⊢i open_vars (x :: ys) t ∶ i) ->
    Gamma & x ~ open_vars (x :: xs) T
    ⸴ Delta & x ~ free ⸴
    vs \u \{ x} ⊢i open_vars (x :: xs) t ∶ i.
Proof.
  intros * Hok HfrG HfrD HxsTs HisTs Hxsavs HavsTs Havsis HOpen.
  pick_freshes_gen
    (L \u fv T \u fv Ts \u fv t \u fv_env Gamma \u dom Gamma
       \u dom Delta \u \{ x} \u vs)
    (S (length xs)) ys'.
  assert (length ys' = S (length xs)) as Hlenys'
    by eauto using fresh_length.
  induction ys' as [|y ys _];
    [ inversion Hlenys'
    | inversion Hlenys' as [Hlenys]; clear Hlenys'].
  sympl.
  rewrite <- Hlenys in Fr.
  assert (Gamma & y ~ open_vars (y :: xs) T
          ⸴ Delta & y ~ free ⸴
          vs \u \{ y} ⊢i open_vars (y :: xs) t ∶ i) as Hinity.
  { eapply renaming_con_middle_singles with (ys:=ys) (xs:=xs);
      eauto 2; try congruence.
    - rewrite <- ? union_assoc in Fr.
      destruct Fr as [Hfry Hfrys].
      fresh_solve; auto.
      + apply fresh_open; auto.
      + apply fresh_open; auto.
    - rewrite union_comm.
      apply well_init_weaken_vs_rules.
      eapply HOpen; eauto 2; try congruence. }

  rewrite ? open_vars_S_commut.
  assert (y \notin from_list xs).
  { eapply notin_vars_of_avars with (G:=Gamma); eauto 2. }
  rewrite subst_intro with (x0:=y) (y0:=x)
    by (apply notin_open_rec_vars_list; auto).
  rewrite subst_intro with (x0:=y) (y0:=x)
    by (apply notin_open_rec_vars_list; auto).

  apply init_weaken
    with (x0:=x) (i':=free) (vs':=\{}) (T':=open y (open_rec_vars 1 xs T))
    in Hinity; auto.
  simpl open_rec_vars in Hinity.
  rewrite ? open_vars_S_commut in Hinity.
  rewrite union_empty_r in Hinity.

  rewrite <- vars_subst_notin with (vs:=vs) (x:=y) (y:=x) by auto.
  rewrite vars_subst_singleton_same with (y:=y).
  rewrite <- vars_subst_union.
  rewrite subst_single.
  eapply well_init_subst_term with (x:=y) (y:=x); eauto.
  - rewrite <- subst_single; auto.
  - assert (x <> y) as Hneq by auto.
    intros i' Hbi'. exists free.
    split; auto.
    apply binds_push_neq_inv in Hbi'; auto.
    apply binds_push_eq_inv in Hbi'; subst; auto.
Qed.

(** For trm_app *)
Lemma renaming_init_fun_app_commit : forall Gamma Delta T L x t,
    ok Gamma ->
    Gamma ⊢ trm_var (avar_f x) ∶ T ->
    Gamma ⸴ Delta ⊢c trm_var (avar_f x) ->
    (forall x : var,
        x \notin L ->
        Gamma & x ~ T ⸴ Delta & x ~ committed ⊢c open x t) ->
    Gamma ⸴ Delta ⊢c open x t.
Proof.
  intros * Hok Htyx Hinitx HfrOpen.
  pick_fresh_gen ((fv t) \u (fv T) \u L \u (fv_env Gamma) \u (dom Gamma)
                         \u (dom Delta) \u \{ x}) y.
  assert (y \notin L) as HyOpen by auto.
  apply HfrOpen in HyOpen.
  replace (Gamma & y ~ T) with (Gamma & y ~ T & empty) in * by auto.
  replace (Delta & y ~ committed) with (Delta & y ~ committed & empty) in * by auto.
  rewrite <- (map_empty (subst_var x y)) in HyOpen.
  apply (well_comm_subst_term) with (y:=x) in HyOpen;
    rewrite ? map_empty, ? concat_empty_r in *; auto.
  + rewrite <- subst_intro in HyOpen by auto; auto.
  + rewrite subst_fresh by auto; auto.
  + inversion Hinitx; subst.
    intros i' Hbi.
    apply binds_push_eq_inv in Hbi; subst.
    eauto using init_sub_refl.
Qed.

(** For let_lit *)
(** Well-committted let_lit *)
Lemma renaming_init_lit_comm : forall Gamma Delta T L x t,
    ok Gamma ->
    x # Gamma ->
    x # Delta ->
    (forall x : var,
        x \notin L ->
        Gamma & x ~ T ⸴ Delta & x ~ committed ⊢c open x t) ->
    Gamma & x ~ T ⸴ Delta & x ~ committed ⊢c open x t.
Proof.
  intros * Hok Hfr HfrD HfrOpen.
  pick_fresh_gen ((fv t) \u (fv T) \u L \u (fv_env Gamma) \u (dom Gamma)
                         \u (dom Delta) \u \{ x}) y.
  assert (y \notin L) as HyOpen by auto.
  apply HfrOpen in HyOpen.
  apply (commit_weaken (x:=x)) with (T':=T) (i':=committed)
    in HyOpen; auto.
  apply (well_comm_subst_term) with (y:=x) in HyOpen; auto.
  + rewrite map_single in HyOpen.
    rewrite subst_fresh in HyOpen by auto.
    rewrite <- subst_intro in HyOpen by auto.
    auto.
  + rewrite map_single, subst_fresh by auto; auto.
  + assert (x <> y) as Hneq by auto.
    intros i' Hbi'. exists committed.
    split; auto.
    apply binds_push_neq_inv in Hbi'; auto.
    apply binds_push_eq_inv in Hbi'; subst; auto.
Qed.

(** Well-init let_lit *)
Lemma renaming_init_lit_init : forall Gamma Delta vs T L x t i1 i2,
    ok Gamma ->
    x # Gamma ->
    x # Delta ->
    (forall x : var,
        x \notin L ->
        Gamma & x ~ T ⸴ Delta & x ~ committed ⸴ vs ⊢i open x t ∶ i2) ->
    Gamma & x ~ T ⸴ Delta & x ~ committed ⸴ vs ⊢i open x t ∶ i2.
Proof.
  intros * i i' Hok Hfr HfrD HfrOpen.
  pick_fresh_gen ((fv t) \u (fv T) \u L \u (fv_env Gamma) \u (dom Gamma)
                         \u (dom Delta) \u vs \u \{ x}) y.
  assert (y \notin L) as HyOpen by auto.
  apply HfrOpen in HyOpen.
  apply (init_weaken_same_vars (x:=x)) with (T':=T) (i'0:=committed)
    in HyOpen; auto.
  apply (well_init_subst_term) with (y:=x) in HyOpen; auto.
  + rewrite map_single in HyOpen.
    rewrite subst_fresh in HyOpen by auto.
    rewrite <- subst_intro in HyOpen by auto.
    unfold subst_var, VarsSubstVar in HyOpen.
    assert (y \notin vs) as Hyvs by auto. unfold notin in Hyvs.
    cases_if; auto.
  + rewrite map_single, subst_fresh by auto; auto.
  + assert (x <> y) as Hneq by auto.
    intros ? Hbi'. exists committed.
    split; auto.
    apply binds_push_neq_inv in Hbi'; auto.
    apply binds_push_eq_inv in Hbi'; subst; auto.
Qed.

(** Well-init let_lit *)
Lemma renaming_init_lit : forall Gamma x Delta vs T l t i,
    ok Gamma ->
    x # Gamma ->
    x # Delta ->
    Gamma ⸴ Delta ⸴ vs ⊢i trm_lit T l t ∶ i ->
    Gamma & x ~ T ⸴ Delta & x ~ committed ⸴ vs ⊢i open x t ∶ i.
Proof.
  inversion 4; subst.
  - inversion H3; subst.
    eauto using renaming_init_lit_comm.
  - eauto using renaming_init_lit_init.
Qed.
