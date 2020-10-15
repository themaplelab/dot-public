Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import List.
Require Import Effects.

Implicit Types
         (Gamma : ctx) (Delta : init_ctx) (Sigma : heap) (ℰ : eff_ctx)
         (effs : effects) (ef : effect).

(* The 'effects' type is a list of (var * trm_label), so when y is substituted
   for x in a list of effects, the car of each pair is replaced *)
Instance EffSubstVar : SubstVar effect :=
  (fun x y eff =>
     match eff with
     | (z, l) => (If z = x then (y, l) else (z, l))
     end).

(* The domain of a set of effects is the set of variables that are going to be
   assigned given some effects *)
Fixpoint eff_dom (eff : effects) : vars :=
  match eff with
  | nil => \{}
  | (x, l) :: effs => \{x} \u (eff_dom effs)
  end%list.

(** * A distributivity lemma for substituting in effects: just a special case
    for the general version with mapping over lists *)
Lemma subst_app_distrib : forall eff1 eff2 x y,
    ((eff1 ++ eff2) /[x -> y])%list =
    ((eff1 /[x -> y]) ++ (eff2 /[x -> y]))%list.
Proof with eauto. intros. eapply map_app. Qed.

(** * If y is fresh enough (not free in t) then effects of t^x are the same as
    (t^y [y := x]). This is because for fresh y, one has that t^x = t^y [y := x].
    Nothing specific to effects here, but just stating this lemma here so the main
    proposition for this file has a easier proof *)
Lemma effs_subst_fresh_in_trm : forall t x y effs,
    y \notin fv t ->
    ⊢e (open y t) /[y -> x] ∶ effs ->
    ⊢e (open x t) ∶ effs.
Proof with eauto. introv y_fresh. rewrite <- subst_intro... Qed.

Lemma effs_subst_var_fresh_in_trm : forall t x y effs n,
    y \notin fv t ->
    ⊢e (open_rec n y t) /[y -> x] ∶ effs ->
    ⊢e (open_rec n x t) ∶ effs.
Proof with eauto.
  introv y_fresh. rewrite <- subst_intro...
Qed.


(** * If t has effects effs then (t [x := y]) has the same effects as
    (E [x := y]). Proof by induction on the effects derivation. *)
Lemma effs_subst_in_effs_and_trm : forall t x y effs,
    ⊢e t ∶ effs ->
    ⊢e (t /[x -> y]) ∶ (effs /[x -> y]).
Proof with eauto.
  introv t_effs.
  induction t_effs...
  - (* Assignment *) simpl. cases_if...
  - (* Let variables *)
    rename H into u_effs. rename H0 into open_u_effs. simpl.
    (* Need a substitution distributing over append for effects lemma here *)
    pose proof (subst_app_distrib eff1 eff2 x y) as susbt_app_distrib.
    rewrite subst_app_distrib.
    (* Choose a fresh enough x0 *)
    apply eff_let with (L := L \u \{x})...
    introv x0_fresh.
    repeat (rewrite notin_union in x0_fresh).
    destruct x0_fresh as [x0_notin_L x0_neq_x].
    rewrite notin_singleton in x0_neq_x.
    (* subst_trm is basically subst_var because of type classes *)
    replace (open x0 (subst_trm x y u)) with (open x0 (subst_var x y u)) by eauto.
    (* By subst_open_commut, have that opening u with x0 then substituting
       instances of x with y is the same as substituting x with y in both
       u and x0, then opening:
                      (u^x0) [x:=y] = (u [x:=y]) ^ (x0 [x:=y])
       But then x0 is a variable and it is possible to make it as fresh as necessary.
       In particular, x0 fresh enough so x0 ≠ x gives
                      (u^x0) [x:=y] = (u [x:=y]) ^ x0
       and so the goal can be solved just using hypothesis after some rewrites *)
    specialize (open_u_effs x0 x0_notin_L) as open_u_x0.
    rewrite subst_open_commut in open_u_x0.
    replace (x0 \[ x -> y]) with x0 in open_u_x0 by (cases_if; eauto).
    assumption.
  - (* Let literals: the same idea for let variables. *)
    rename H into u_effs. rename H0 into open_u_effs. simpl.
    (* Choose a fresh enough x0 *)
    apply eff_llit with (L := L \u \{x})...
    introv x0_fresh.
    repeat (rewrite notin_union in x0_fresh).
    destruct x0_fresh as [x0_notin_L x0_neq_x].
    rewrite notin_singleton in x0_neq_x.
    (* subst_trm is basically subst_var because of type classes *)
    replace (open x0 (subst_trm x y u)) with (open x0 (subst_var x y u)) by eauto.
    (* Same argument as above: opening u with x0 then substituting x for y is
       the same as substituting in x and y then doing the opening. But
       x0 is fresh enough so substituting x for x0 does nothing *)
    specialize (open_u_effs x0 x0_notin_L) as open_u_x0.
    rewrite subst_open_commut in open_u_x0.
    replace (x0 \[ x -> y]) with x0 in open_u_x0 by (cases_if; eauto).
    assumption.
Qed.

Lemma def_eff_subst1 : forall x y z ds,
    def_eff x (ds /[ y -> z]) = def_eff x ds.
Proof.
  intros.
  induction ds; auto.
  destruct a; eauto.
  sympl; congruence.
Qed.

Lemma def_eff_subst2 : forall x y z ds,
    def_eff (x \[y -> z]) ds = (def_eff x ds /[y -> z]).
Proof.
  induction ds as [| d ds].
  - simpl; auto.
  - destruct d; eauto.
    sympl.
    repeat (cases_if; simpl in *); congruence.
Qed.

Lemma def_eff_subst3 : forall x y z ds,
    def_eff (x \[y -> z]) ds = (def_eff x ds /[y -> z]).
Proof.
  intros; rewrite def_eff_subst2; auto.
Qed.

Lemma def_eff_subst4: forall x y ds,
    y \notin \{x} ->
    def_eff x ds = (def_eff y ds /[y -> x]).
Proof.
  intros x y ds Hfr.
  assert (def_eff x ds = def_eff (x \[y -> x]) ds)
    as Heq by (cases_if; auto).
  rewrite <- def_eff_subst2.
  cases_if; auto.
Qed.

Lemma def_eff_subst : forall x y z ds,
    x \notin \{ y} ->
    def_eff x ds = (def_eff x ds /[y -> z]).
Proof.
  intros x y z ds H; rewrite <- def_eff_subst3.
  apply notin_singleton in H.
  cases_if; auto.
Qed.

(** * If y is fresh enough (i.e. not in the domain of effs) then
    (effs /e[y := x]) = effs. Nothing special to effects here. *)
Lemma effs_subst_fresh_in_effs : forall x y effs,
    y \notin eff_dom effs ->
    effs /[y -> x] = effs.
Proof with eauto.
  (* If the 'free variables' of a set of effects were to be defined as its domain
     then existing lemmas probably does the job. *)
  introv y_fresh. induction effs as [| [z a] effs IHeffs]...
  simpl in y_fresh. rewrite notin_union in y_fresh.
  destruct y_fresh as [y_neq_z y_notin_dom].
  rewrite notin_singleton in y_neq_z.
  change ((z, a) :: effs /[ y -> x]) with
      (((z, a) /[ y -> x]):: (effs /[ y -> x])).
  rewrite IHeffs... sympl; case_if...
Qed.

(** * Finally the renaming_fresh dual for effects. The proof will go as follows:
    Suppose that ⊢e t^y : eff for all y ∉ L. Let x be given. Then, the goal is to
    show that ⊢e t^x : eff also. To do so:
    1. Choose a fresh enough y (freshness retrospectively determined)
    2. Then, by effs_subst_fresh_in_trm (y ∉ fv t), it suffices to show that
                           ⊢e t^y [y := x] : eff
    3. But y is fresh (y ∉ L), so by hypothesis,
                               ⊢e t^y : eff
    4. By effs_subst_in_effs_and_trm, ⊢e t^y : eff implies
                       ⊢e t^y [y := x] : eff [y := x]
    5. But y is fresh (y ∉ eff_dom eff), so (eff [y := x]) = eff and
                           ⊢e t^y [y := x] : eff
    6. By effs_subst_fresh_in_trm, (t^y [y := x]) = t^x, so
                               ⊢e t^x : eff
 *)
Lemma renaming_fresh_effs : forall L effs t x,
    (forall x : var, x \notin L -> ⊢e open x t ∶ effs) ->
    (⊢e open x t ∶ effs).
Proof with eauto.
  introv fresh_open_effs.
  (* Chose y fresh *)
  pick_fresh_gen ((fv t) \u L \u (eff_dom effs)) y.
  repeat (rewrite notin_union in Fr).
  destruct Fr as [[y_notin_t y_notin_L] y_notin_effs].
  (* Invoke the previously proven lemmas as described in the outline *)
  eapply effs_subst_fresh_in_trm...
  replace effs with (effs /[y -> x])
    by (erewrite <- effs_subst_fresh_in_effs; eauto).
  eapply effs_subst_in_effs_and_trm...
Qed.

Lemma renaming_fresh_var_n_effs : forall L effs t x n,
    (forall x : var, x \notin L -> ⊢e open_rec n x t ∶ effs) ->
    (⊢e open_rec n x t ∶ effs).
Proof with eauto.
  introv fresh_open_effs.
  pick_fresh_gen ((fv t) \u L \u (eff_dom effs)) y.
  repeat (rewrite notin_union in Fr).
  destruct Fr as [[y_notin_t y_notin_L] y_notin_effs].
  eapply effs_subst_var_fresh_in_trm...
  replace effs with (effs /[y -> x])
    by (erewrite <- effs_subst_fresh_in_effs; eauto).
  eapply effs_subst_in_effs_and_trm...
Qed.

Lemma renaming_fresh_vars_n_effs : forall L effs t xs n,
    (forall (ys : list var),
        fresh L (length ys) ys ->
        ⊢e open_rec_vars n ys t ∶ effs) ->
    ⊢e open_rec_vars n xs t ∶ effs.
Proof with eauto.
  introv. generalize dependent L. generalize dependent effs. generalize dependent t.
  generalize dependent n.
  induction xs; intros...
  assert (forall (ys : list var) (x : var),
             fresh L (length (x :: ys)) (x :: ys) ->
             ⊢e open_rec_vars n (x :: ys) t ∶ effs) as cons_rename... clear H.
  simpl in cons_rename. simpl.
  rewrite open_vars_S_commut.
  eapply renaming_fresh_var_n_effs.
  introv x_fresh.
  rewrite <- open_vars_S_commut.
  eapply IHxs.
  introv ys_fresh.
  apply cons_rename...
Qed.

Lemma renaming_fresh_vars_n_effs_len_eq : forall L effs t xs n,
    (forall (ys : list var),
        length ys = length xs ->
        fresh L (length ys) ys ->
        ⊢e open_rec_vars n ys t ∶ effs) ->
    ⊢e open_rec_vars n xs t ∶ effs.
Proof with eauto.
  introv. generalize dependent L. generalize dependent effs. generalize dependent t.
  generalize dependent n.
  induction xs; intros...
  assert (forall (ys : list var) (x : var),
             length ys = length xs ->
             fresh L (length (x :: ys)) (x :: ys) ->
             ⊢e open_rec_vars n (x :: ys) t ∶ effs) as cons_rename... clear H.
  simpl in cons_rename. simpl.
  rewrite open_vars_S_commut.
  eapply renaming_fresh_var_n_effs.
  introv x_fresh.
  rewrite <- open_vars_S_commut.
  eapply IHxs.
  introv ys_length ys_fresh.
  apply cons_rename...
Qed.

Lemma renaming_con_def_eff_no_args : forall L ds t x,
    (forall (y : var),
        y \notin L ->
        ⊢e open y t ∶ def_eff y ds) ->
    ⊢e open x t ∶ def_eff x ds.
Proof.
  intros * HOpen.
  pick_fresh_gen (L \u fv t \u \{ x}) z.
  assert (z \notin L) as Hz by auto. apply HOpen in Hz.
  assert (z \notin \{ x}) as Hx by auto.
  rewrite def_eff_subst4 with (y:=z) by auto.
  rewrite subst_intro with (y:=x) (x0:=z) by auto.
  apply effs_subst_in_effs_and_trm; auto.
Qed.

Lemma renaming_con_def_eff : forall L ds t x xs,
    (forall (y : var) (ys : list var),
        length ys = length xs ->
        fresh L (length (y :: ys)) (y :: ys) ->
        ⊢e open_vars (y :: ys) t ∶ def_eff y ds) ->
    ⊢e open_vars (x :: xs) t ∶ def_eff x ds.
Proof.
  intros * HOpen.
  simpl. rewrite open_vars_S_commut.
  apply renaming_con_def_eff_no_args with (L:=L); auto.
  intros. rewrite <- open_vars_S_commut.
  apply renaming_fresh_vars_n_effs_len_eq with (L:=L \u \{y}).
  intros ys Hlen Hfr.
  apply HOpen; auto.
Qed.

Corollary renaming_fresh_vars_eff_len_eq : forall L effs t xs,
    (forall (ys : list var),
        length ys = length xs ->
        fresh L (length ys) ys ->
        ⊢e open_vars ys t ∶ effs) ->
    ⊢e open_vars xs t ∶ effs.
Proof with eauto.
  intros. eapply renaming_fresh_vars_n_effs_len_eq...
Qed.

Corollary renaming_fresh_vars_eff : forall L effs t xs,
    (forall (ys : list var),
        fresh L (length ys) ys ->
        ⊢e open_vars ys t ∶ effs) ->
    ⊢e open_vars xs t ∶ effs.
Proof with eauto. intros. eapply renaming_fresh_vars_n_effs... Qed.

Lemma renaming_fresh_vars_n_effs_len : forall L effs t xs n,
    (forall (ys : list var),
        length ys >= length xs ->
        fresh L (length ys) ys ->
        ⊢e open_rec_vars n ys t ∶ effs) ->
    ⊢e open_rec_vars n xs t ∶ effs.
Proof with eauto.
  introv. generalize dependent L. generalize dependent effs. generalize dependent t.
  generalize dependent n.
  induction xs; intros...
  assert (forall (ys : list var) (x : var),
             length ys >= length xs ->
             fresh L (length (x :: ys)) (x :: ys) ->
             ⊢e open_rec_vars n (x :: ys) t ∶ effs) as cons_rename.
  { simpl in H. intros. eapply H... simpl. omega. }
  simpl in cons_rename. simpl.
  rewrite open_vars_S_commut.
  eapply renaming_fresh_var_n_effs.
  introv x_fresh.
  rewrite <- open_vars_S_commut.
  eapply IHxs.
  introv ys_length ys_fresh.
  apply cons_rename...
Qed.

Corollary renaming_fresh_vars_eff_len : forall L effs t xs,
    (forall (ys : list var),
        length ys >= length xs ->
        fresh L (length ys) ys ->
        ⊢e open_vars ys t ∶ effs) ->
    ⊢e open_vars xs t ∶ effs.
Proof with eauto.
  intros. eapply renaming_fresh_vars_n_effs_len...
Qed.

Corollary renaming_fresh_eff_cons_len_eq : forall L effs t y ys,
    (forall (x : var) (xs : list var),
        length xs = length ys ->
        fresh L (S (length xs)) (x :: xs) ->
        ⊢e open_vars (x :: xs) t ∶ effs) ->
    ⊢e open_vars (y :: ys) t ∶ effs.
Proof with eauto.
  intros.
  eapply renaming_fresh_vars_eff_len_eq.
  intros. destruct ys0; inversions H0.  rename ys0 into vs.
  eapply H...
Qed.

Corollary renaming_fresh_eff_cons_len : forall L effs t y ys,
    (forall (x : var) (xs : list var),
        length xs >= length ys ->
        fresh L (S (length xs)) (x :: xs) ->
        ⊢e open_vars (x :: xs) t ∶ effs) ->
    ⊢e open_vars (y :: ys) t ∶ effs.
Proof with eauto.
  intros.
  eapply renaming_fresh_vars_eff_len.
  intros.
  destruct ys0; try(solve[inversions H0]).
  eapply H... simpl in H0. omega.
Qed.

Corollary renaming_fresh_eff_cons : forall L effs t y ys,
    (forall (x : var) (xs : list var),
        fresh L (S (length xs)) (x :: xs) ->
        ⊢e open_vars (x :: xs) t ∶ effs) ->
    ⊢e open_vars (y :: ys) t ∶ effs.
Proof with eauto.
  intros.
  eapply renaming_fresh_vars_eff_len.
  intros. destruct ys0; inversions H0...
Qed.

Lemma from_list_subst_inv : forall x y effs eff,
    eff \in from_list (effs /[x -> y]) ->
    exists eff', (eff = (eff' /[x -> y])) /\ (eff' \in from_list effs).
Proof.
  intros x y effs [z a]. rewrite from_list_in.
  induction effs as [| [z' a'] effs IHeffs].
  - simpl; intros; exfalso; auto.
  - intros [Heq | Hin].
    + exists (z', a'); split; auto.
      rewrite from_list_in.
      simpl; auto.
    + destruct (IHeffs Hin) as [eff' [Heq Hfl]].
      exists eff'. rewrite from_list_cons, in_union.
      auto.
Qed.

Lemma from_list_subst_in : forall x y effs eff,
    eff \in from_list effs ->
    (eff /[x -> y]) \in from_list (effs /[x -> y]).
Proof.
  induction effs as [| eff' effs IHeffs]; intros eff.
  - rewrite ? from_list_nil, ? from_list_cons.
    intro; exfalso.
    eauto using in_empty_inv.
  - change (eff' :: effs /[ x -> y])
      with ((eff' /[ x -> y]) :: (effs /[ x -> y])).
    rewrite ? from_list_nil, ? from_list_cons,
    ? in_union, ? in_singleton.
    destruct 1 as [Heq | Hin]; subst; auto.
Qed.

Lemma eff_from_list_subst : forall x y effs1 effs2,
    from_list effs1 = from_list effs2 ->
    from_list (effs1 /[x -> y])  = from_list (effs2 /[x -> y]).
Proof.
  intros * Heq.
  assert (from_list effs1 \c from_list effs2) as Hsub1
    by (rewrite Heq; apply subset_refl).
  assert (from_list effs2 \c from_list effs1) as Hsub2
    by (rewrite Heq; apply subset_refl).
  apply fset_extens; unfold "\c" in *; intros eff.
  - intros Hin.
    pose proof (from_list_subst_inv _ _ _ Hin)
      as [eff' [Heq' Hin']]; subst.
    rewrite Heq in Hin'; eauto using from_list_subst_in.
  - intros Hin.
    pose proof (from_list_subst_inv _ _ _ Hin)
      as [eff' [Heq' Hin']]; subst.
    rewrite <- Heq in Hin'; eauto using from_list_subst_in.
Qed.

Lemma def_eff_from_list_subst : forall x y z ds effs,
    from_list (def_eff x ds) = from_list effs ->
    from_list (def_eff x ds /[ y -> z]) = from_list (effs /[ y -> z]).
Proof.
  eauto using eff_from_list_subst.
Qed.

(** * Has effects *)
(** Substitution for has effects *)
Lemma has_effs_subst_in_effs_and_trm : forall t x y effs,
    has_effs t effs ->
    has_effs (t /[x -> y]) (effs /[x -> y]).
Proof.
  intros * [effs' [Hef Hfl]].
  exists (effs' /[x -> y]); split;
    eauto using effs_subst_in_effs_and_trm,
    eff_from_list_subst.
Qed.

(** Renaming for has effects *)
Lemma renaming_con_has_def_eff_no_args : forall L ds t x,
    (forall (y : var),
        y \notin L ->
        has_effs (open y t) (def_eff y ds)) ->
    has_effs (open x t) (def_eff x ds).
Proof.
  intros * HOpen.
  pick_fresh_gen (L \u fv t \u \{ x}) z.
  assert (z \notin L) as Hz by auto. apply HOpen in Hz.
  assert (z \notin \{ x}) as Hx by auto.
  rewrite def_eff_subst4 with (y:=z) by auto.
  rewrite subst_intro with (y:=x) (x0:=z) by auto.
  apply has_effs_subst_in_effs_and_trm; auto.
Qed.

Lemma renaming_has_effs_n_effs : forall L effs t x n,
    (forall x : var, x \notin L -> has_effs (open_rec n x t) effs) ->
    has_effs (open_rec n x t) effs.
Proof with eauto.
  introv fresh_open_effs.
  pick_fresh_gen ((fv t) \u L \u (eff_dom effs)) y.
  repeat (rewrite notin_union in Fr).
  destruct Fr as [[y_notin_t y_notin_L] y_notin_effs].
  rewrite subst_intro with (y0:=x) (x0:=y) by auto.
  replace effs with (effs /[y -> x])
    by (erewrite <- effs_subst_fresh_in_effs; eauto).
  apply has_effs_subst_in_effs_and_trm; auto.
Qed.

Lemma renaming_has_eff_n_effs_len_eq : forall L effs t xs n,
    (forall (ys : list var),
        length ys = length xs ->
        fresh L (length ys) ys ->
        has_effs (open_rec_vars n ys t) effs) ->
    has_effs (open_rec_vars n xs t) effs.
Proof with eauto.
  introv HOpen.
  generalize dependent L.
  generalize dependent effs.
  generalize dependent t.
  generalize dependent n.
  induction xs as [|x xs IHxs]; intros...
  assert (forall (ys : list var) (x : var),
             length ys = length xs ->
             fresh L (length (x :: ys)) (x :: ys) ->
             has_effs (open_rec_vars n (x :: ys) t) effs)
    as HOpen' by eauto. clear HOpen.
  simpl in HOpen'. simpl.
  rewrite open_vars_S_commut.
  eapply renaming_has_effs_n_effs with (L:=L).
  introv x_fresh.
  rewrite <- open_vars_S_commut.
  eapply IHxs with (L:=L \u \{x0}).
  introv ys_length ys_fresh.
  apply HOpen'...
Qed.

Lemma renaming_has_eff_con : forall L t ds x xs,
    (forall (x : var) (ys : list var),
        length ys = length xs ->
        fresh L (S (length ys)) (x :: ys) ->
        has_effs (open_vars (x :: ys) t) (def_eff x ds)) ->
    has_effs (open_vars (x :: xs) t) (def_eff x ds).
Proof.
  intros * HOpen.
  simpl. rewrite open_vars_S_commut.
  eapply renaming_con_has_def_eff_no_args with (L:=L).
  intros y Hni. specialize (HOpen y).
  rewrite <- open_vars_S_commut.
  eapply renaming_has_eff_n_effs_len_eq with (L:=L \u \{y}).
  intros. eapply HOpen; auto.
Qed.
