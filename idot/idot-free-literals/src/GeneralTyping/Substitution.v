(** remove printing ~ *)

Set Implicit Arguments.

Require Import DotTactics LibExtra.
Require Import AbstractSyntax PreTyping Typing SubstitutionClass GeneralTyping Weakening.

(** * Tactics for Subsitution Lemma *)
Ltac unfold_fvar :=
  unfold subst_fvar; rewrite~ If_r.

Ltac subst_open_fresh :=
  repeat match goal with
         | [ |- context [ (?O ?n ?z (?S ?x ?y ?T)) ] ] =>
           rewrite <- (subst_open_commut_single n y T) by auto
         end.

Ltac fold_subst_env :=
  try rewrite ? subst_singles_rev_to_list by auto;
  try rewrite ? subst_single;
  rewrite <- ? concat_assoc, <- ? map_concat, ? concat_assoc.

Ltac unfold_subst_env :=
  rewrite map_concat, <- subst_single.

Local Hint Extern 1 (_ & _ ⊢ _ ∶ _) => apply weaken : core.
Local Hint Extern 2 (_ & _ ⊢ _ <: _) => apply weaken_middle : core.

Ltac subst_solver :=
    fresh_constructor;
    subst_open_fresh;
    match goal with
    | [ H: forall z, z \notin ?L -> forall G, _
        |- context [ ?G1 & map (?S1 ?x ?y) ?G2 & ?z ~ ?S2 ?x ?y ?T] ] =>
      assert (G1 & map (S1 x y) G2 & z ~ S2 x y T
              = G1 & subst_env x y (G2 & z ~ T))
        as B by (unfold_subst_env; rewrite concat_assoc; auto);
      rewrite B; apply H; rewrite ? concat_assoc; auto 2;
      rewrite map_concat; rewrite ? concat_assoc;
      rewrite ? map_single; auto
    end.

Ltac subst_open_commut_solver :=
  sympls;
  try rewrite subst_open_commut;
  auto; eauto 4.


Ltac fold_subst :=
  repeat match goal with
    | [ |- context [ trm_var (avar_f (If ?x = ?y then ?z else ?x)) ] ] =>
        asserts_rewrite (trm_var (avar_f (If x = y then z else x))
                         = subst_trm y z (trm_var (avar_f x))); auto
    | [ |- context [ open (If ?x = ?y then ?z else ?x) (subst_var ?y ?z ?T) ] ] =>
        asserts_rewrite (open (If x = y then z else x) (subst_var y z T)
                     = subst_var y z (open x T)); auto  end.

Local Ltac simpl_length_s :=
  repeat match goal with
  | [ |- context[ length_s (_ /[ _ -> _]) ] ] =>
    rewrite length_s_subst
  | [ H: context[ length_s (_ /[ _ -> _]) ] |- _ ] =>
    rewrite length_s_subst in H
  end.

Implicit Types (d : def) (ds : defs) (T : typ).

(** * Substitution Lemmas *)
Instance DefDecTySubstMiddle : DecTySubstMiddle ty_def.
Proof.
  hnf; introv Hfr Hty; inversions Hty; sympl; auto.
Qed.

(** [G1, x: S, G2 ⊢ t∶ T]            #<br>#
    [x # G2]               #<br>#
    [x \notin fv(G1)]                 #<br>#
    [G1, G2[y/x] ⊢ y∶ S[y/x]]       #<br>#
    [―――――――――――――――――――――――――――――]  #<br>#
    [G1, G2[y/x] ⊢ t[y/x]∶ T[y/x]] #<br>#  #<br>#

    and

    [G1, x: S, G2 ⊢ d∶ D]            #<br>#
    [x # G2]               #<br>#
    [x \notin fv(G1)]                 #<br>#
    [G1, G2[y/x] ⊢ y∶ S[y/x]]       #<br>#
    [―――――――――――――――――――――――――――――]  #<br>#
    [G1, G2[y/x] ⊢ d[y/x]∶ D[y/x]] #<br>#  #<br>#

    and

    [G1, x: S, G2 ⊢ ds∶ T]           #<br>#
    [x # G2]               #<br>#
    [x \notin fv(G1)]                 #<br>#
    [G1, G2[y/x] ⊢ y∶ S[y/x]]       #<br>#
    [――――――――――――――――――――――――――――――] #<br>#
    [G1, G2[y/x] ⊢ ds[y/x]∶ T[y/x]] #<br>#  #<br>#

    and

    [G1, x: S, G2 ⊢ T <: U]           #<br>#
    [x # G2]               #<br>#
    [x \notin fv(G1)]                  #<br>#
    [G1, G2[y/x] ⊢ y∶ S[y/x]]        #<br>#
    [―――――――――――――――――――――――――――――――] #<br>#
    [G1, G2[y/x] ⊢ T[y/x] <: U[y/x]] #<br>#  #<br># *)

(** The proof is by mutual induction on term typing, literal typing, and
    subtyping. The [x \notin fv_env G1] is required because the typing rules allow
    [x] to appear free in the context [G1].
    Example: [typ_all (typ_sel x A) (typ_sel x A)]. *)
Lemma subst_rules: forall y S,
  (forall G t T, G ⊢ t ∶ T -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    x # G2 ->
    x \notin fv_env G1 ->
    G1 & (subst_env x y G2) ⊢ trm_var (avar_f y) ∶ subst_var x y S ->
    G1 & (subst_env x y G2) ⊢ subst_var x y t ∶ subst_var x y T) /\
  (forall G (l : lit) T, G ⊢ l ∶ T -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    x # G2 ->
    x \notin fv_env G1 ->
    G1 & (subst_env x y G2) ⊢ trm_var (avar_f y) ∶ subst_var x y S ->
    G1 & (subst_env x y G2) ⊢ subst_var x y l ∶ subst_var x y T) /\
  (forall G T U, G ⊢ T <: U -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    x # G2 ->
    x \notin fv_env G1 ->
    G1 & (subst_env x y G2) ⊢ trm_var (avar_f y) ∶ subst_var x y S ->
    G1 & (subst_env x y G2) ⊢ subst_var x y T <: subst_var x y U) /\
  (forall G avs Ts, G ⊢ avs :: Ts -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    x # G2 ->
    x \notin fv_env G1 ->
    G1 & (subst_env x y G2) ⊢ trm_var (avar_f y) ∶ subst_var x y S ->
    G1 & (subst_env x y G2) ⊢ subst_var x y avs :: subst_var x y Ts).
Proof.
  introv.
  apply rules_mutind; intros; subst; sympl in *;
    try subst_solver; subst_open_commut_solver.
  - Case "ty_var".
    cases_if.
    + apply binds_middle_eq_fresh_inv in b; subst; assumption.
    + apply (subst_fresh_ctx y) in H1.
      rewrite <- H1, <- map_concat.
      eauto using binds_map, binds_subst.
  - Case "ty_new".
    rewrite subst_open_rec_vars_commut.
    econstructor; auto 2. apply subst_vars_of_avars; auto.
  - Case "ty_rec_intro".
    apply ty_rec_intro. fold_subst; sympl; eauto.
    rewrite subst_open_commut. auto.
  - Case "ty_con_intro".
    (* clear t0 t1. *)
    apply* (@ty_con_intro (L \u dom (G1 & x ~ S & G2))); intros.
    + repeat rewrite <- subst_open_vars_commut_fresh_length
        by (simpls; destruct_all; simpl_dom; auto).
      simpl_length_s; fold_subst_env.
      destruct H4.
      apply ty_subst_middle with (S0:= S); eauto 3;
        rewrite <- ? concat_assoc, ? map_concat, ? concat_assoc;
        sympl; eauto.
      * simpl_dom; rewrite ? notin_union; repeat split; auto.
        apply fresh_notin_dom; auto.
      * rewrite <- ? subst_single;
          rewrite <- ? subst_singles_rev_to_list by auto.
        apply weaken_fresh_list_cons; auto.
        -- rewrite dom_concat, dom_map.
           rewrite ? dom_concat, <- ? union_assoc in H5.
           split; auto.
        -- change (length (to_list (Ts /[ x -> y ])))
             with (length_s (Ts /[ x -> y ])).
           rewrite length_s_subst. auto.
    + repeat rewrite <- subst_open_vars_commut_fresh_length
        by (simpls; destruct_all; simpl_dom; split; auto).
      simpl_length_s; fold_subst_env.
      destruct H4. sympl.
      assert (fresh L (length (x0 :: ys)) (x0 :: ys)) by auto.
      specialize (H x0 ys H0 H6 G1
                     (G2
                      & ys ~** to_list Ts
                      & x0 ~ open_rec_vars 1 ys (open x0 T)) x).
      assert ((open_rec_vars 1 ys (open x0 T') /[ x -> y])
                = (open_rec_vars 1 ys (open x0 (T' /[ x -> y])))).
      { rewrite subst_open_vars_commut_fresh_length
          by (simpl_dom; auto).
        assert (x0 <> x)
          by (rewrite <- notin_singleton; simpl_dom; auto).
        rewrite subst_open_commut; cases_if; auto. }
      rewrite H7 in H.
      apply H; rewrite ? concat_assoc; auto.
      -- rewrite dom_concat, notin_union; split; auto 2.
         eapply fresh_cons_notin_rev; auto. split; auto.
         rewrite ? dom_concat, ? dom_single, <- ? union_assoc in *.
         auto.
      -- rewrite ? map_concat, ? concat_assoc.
         rewrite <- subst_singles_rev_to_list, map_single by auto.
         apply weaken_fresh_list_cons; auto 2.
         ++ rewrite ? dom_concat, ? dom_map in *; auto.
         ++ change (length (to_list (Ts /[ x -> y])))
              with (length_s (Ts /[ x -> y ])).
            rewrite length_s_subst. auto.
Qed.

(** The substitution lemma for term typing. *)
Instance TrmTySubstMiddle : TySubstMiddle ty_trm.
Proof.
  hnf; intros; eapply subst_rules; eauto.
Qed.

Instance LitTySubstMiddle : TySubstMiddle ty_lit.
Proof.
  hnf; intros; eapply subst_rules; eauto.
Qed.

Instance AvarsTysSubst : TysSubstMiddle ty_avars.
Proof.
  hnf; intros; eapply subst_rules; eauto.
Qed.
