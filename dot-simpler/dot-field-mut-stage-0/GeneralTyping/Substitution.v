(** remove printing ~ *)

Set Implicit Arguments.

Require Import DotTactics LibExtra.
Require Import AbstractSyntax GeneralTyping Weakening.

Ltac unfold_fvar :=
  unfold subst_fvar; rewrite~ If_r.

Ltac subst_open_fresh :=
  repeat match goal with
    | [ |- context [ (?O ?n ?z (?S ?x ?y ?T)) ] ] =>
        (replace (O n z (S x y T)) with (O n (subst_fvar x y z) (S x y T))
          by unfold_fvar);
        let H := fresh in
        pose proof (subst_open_commut x y z T) as H;
        unfold subst_fvar; rewrite <- H; clear H
         end;
  try unfold_fvar.

Ltac fold_subst_env :=
  try rewrite ? subst_singles_rev_to_list by auto;
  try rewrite ? subst_single;
  rewrite <- ? concat_assoc, <- ? map_concat, ? concat_assoc.

Ltac unfold_subst_env :=
  rewrite map_concat, <- subst_single.

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
      auto using weaken_ty_trm
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


(** * Substitution Lemma *)
(** [G1, x: S, G2 ⊢ t∶ T]            #<br>#
    [ok(G1, x: S, G2)]               #<br>#
    [x \notin fv(G1)]                 #<br>#
    [G1, G2[y/x] ⊢ y∶ S[y/x]]       #<br>#
    [―――――――――――――――――――――――――――――]  #<br>#
    [G1, G2[y/x] ⊢ t[y/x]∶ T[y/x]] #<br>#  #<br>#

    and

    [G1, x: S, G2 ⊢ d∶ D]            #<br>#
    [ok(G1, x: S, G2)]               #<br>#
    [x \notin fv(G1)]                 #<br>#
    [G1, G2[y/x] ⊢ y∶ S[y/x]]       #<br>#
    [―――――――――――――――――――――――――――――]  #<br>#
    [G1, G2[y/x] ⊢ d[y/x]∶ D[y/x]] #<br>#  #<br>#

    and

    [G1, x: S, G2 ⊢ ds∶ T]           #<br>#
    [ok(G1, x: S, G2)]               #<br>#
    [x \notin fv(G1)]                 #<br>#
    [G1, G2[y/x] ⊢ y∶ S[y/x]]       #<br>#
    [――――――――――――――――――――――――――――――] #<br>#
    [G1, G2[y/x] ⊢ ds[y/x]∶ T[y/x]] #<br>#  #<br>#

    and

    [G1, x: S, G2 ⊢ T <: U]           #<br>#
    [ok(G1, x: S, G2)]                #<br>#
    [x \notin fv(G1)]                  #<br>#
    [G1, G2[y/x] ⊢ y∶ S[y/x]]        #<br>#
    [―――――――――――――――――――――――――――――――] #<br>#
    [G1, G2[y/x] ⊢ T[y/x] <: U[y/x]] #<br>#  #<br># *)

(** The proof is by mutual induction on term typing, definition typing, and subtyping. *)
Lemma subst_rules: forall y S,
  (forall G t T, G ⊢ t ∶ T -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_env G1 ->
    G1 & (subst_env x y G2) ⊢ trm_var (avar_f y) ∶ subst_var x y S ->
    G1 & (subst_env x y G2) ⊢ subst_var x y t ∶ subst_var x y T) /\
  (forall G (l : lit) T, G ⊢ l ∶ T -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_env G1 ->
    G1 & (subst_env x y G2) ⊢ trm_var (avar_f y) ∶ subst_var x y S ->
    G1 & (subst_env x y G2) ⊢ subst_var x y l ∶ subst_var x y T) /\
  (forall G d D, G ⊢ d ∶d D -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_env G1 ->
    G1 & (subst_env x y G2) ⊢ trm_var (avar_f y) ∶ subst_var x y S ->
    G1 & (subst_env x y G2) ⊢ subst_var x y d ∶d subst_var x y D) /\
  (forall G (ds : defs) T, G ⊢ ds ∶ T -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_env G1 ->
    G1 & (subst_env x y G2) ⊢ trm_var (avar_f y) ∶ subst_var x y S ->
    G1 & (subst_env x y G2) ⊢ subst_var x y ds ∶ subst_var x y T) /\
  (forall G T U, G ⊢ T <: U -> forall G1 G2 x,
    G = G1 & x ~ S & G2 ->
    ok (G1 & x ~ S & G2) ->
    x \notin fv_env G1 ->
    G1 & (subst_env x y G2) ⊢ trm_var (avar_f y) ∶ subst_var x y S ->
    G1 & (subst_env x y G2) ⊢ subst_var x y T <: subst_var x y U).
Proof.
  introv.
  apply rules_mutind; intros; subst; sympl in *;
    try subst_solver; subst_open_commut_solver.
  - Case "ty_var".
    cases_if.
    + apply binds_middle_eq_inv in b; subst; assumption.
    + apply (subst_fresh_ctx y) in H1.
      rewrite <- H1, <- map_concat.
      eauto using binds_map, binds_subst.
  - Case "ty_rec_intro".
    apply ty_rec_intro. fold_subst; sympl; eauto.
    rewrite subst_open_commut. auto.
  - Case "ty_defs_cons".
    constructor*. rewrite <- subst_label_of_def. apply* subst_defs_hasnt.
Qed.

(** The substitution lemma for term typing. *)
Lemma subst_ty_trm: forall y S G x (t : trm) T,
    G & x ~ S ⊢ t ∶ T ->
    ok (G & x ~ S) ->
    x \notin fv_env G ->
    G ⊢ trm_var (avar_f y) ∶ subst_var x y S ->
    G ⊢ subst_var x y t ∶ subst_var x y T.
Proof.
  intros.
  apply (proj51 (subst_rules y S)) with (G1:=G) (G2:=empty) (x:=x) in H;
  try rewrite map_empty in *; try rewrite concat_empty_r in *; auto.
Qed.

(** The substitution lemma for definition typing. *)
Lemma subst_ty_defs: forall y S G x (ds : defs) T,
    G & x ~ S ⊢ ds ∶ T ->
    ok (G & x ~ S) ->
    x \notin fv_env G ->
    G ⊢ trm_var (avar_f y) ∶ subst_var x y S ->
    G ⊢ subst_var x y ds ∶ subst_var x y T.
Proof.
  intros.
  apply (subst_rules y S) with (G1:=G) (G2:=empty) (x:=x) in H;
    try rewrite map_empty in *; try rewrite concat_empty_r in *; auto.
Qed.

Lemma subst_ctx_vars_ok : forall xs ys G1 G2,
    ok (G1 & G2) ->
    ok (G1 & subst_env_vars xs ys G2).
Proof.
  intros. apply ok_concat_map; auto.
Qed.

(** * Renaming  *)

(** Renaming the name of the opening variable for definition typing.  #<br>#

    [ok G]                   #<br>#
    [z] fresh                #<br>#
    [G, z: T^z ⊢ ds^z ∶ T^z] #<br>#
    [G ⊢ x∶ T^x]             #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ ds^x ∶ T^x]         *)
Lemma renaming_def : forall G n z T (ds : defs) x,
    ok G ->
    z # G ->
    z \notin (fv_env G \u fv ds \u fv T) ->
    G & z ~ open z T ⊢ open_rec n z ds ∶ open_rec n z T ->
    G ⊢ trm_var (avar_f x) ∶ open x T ->
    G ⊢ open_rec n x ds ∶ open_rec n x T.
Proof.
  introv Hok Hnz Hnz' Hz Hx.
  rewrite subst_intro with (x0:=z) (y:=x) by auto.
  rewrite subst_intro with (x0:=z) (y:=x) by auto.
  eapply subst_ty_defs; auto. eapply Hz. rewrite <- subst_intro. all: auto.
Qed.

(** Renaming the name of the opening variable for term typing. #<br>#
    [ok G]                   #<br>#
    [z] fresh                #<br>#
    [G, z: U ⊢ t^z ∶ T^z]    #<br>#
    [G ⊢ x∶ U]               #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ t^x ∶ T^x]         *)
Lemma renaming_typ: forall G z T U (t : trm) x,
    ok G ->
    z # G ->
    z \notin (fv_env G \u fv U \u fv T \u fv t) ->
    G & z ~ U ⊢ open z t ∶ open z T ->
    G ⊢ trm_var (avar_f x) ∶ U ->
    G ⊢ open x t ∶ open x T.
Proof.
  introv Hok Hnz Hnz' Hz Hx.
  rewrite subst_intro with (x0:=z) (y:=x).
  rewrite subst_intro with (x0:=z) (y:=x).
  eapply subst_ty_trm; auto. eapply Hz. rewrite subst_fresh. all: auto.
Qed.

Lemma renaming_open_typ: forall G z T U (t : trm) x,
    ok G ->
    z # G ->
    z \notin (fv_env G \u fv U \u fv T \u fv t) ->
    G & z ~ open z U ⊢ open z t ∶ open z T ->
    G ⊢ trm_var (avar_f x) ∶ open x U ->
    G ⊢ open x t ∶ open x T.
Proof.
  introv Hok Hnz Hnz' Hz Hx.
  rewrite subst_intro with (x0:=z) (y:=x).
  rewrite subst_intro with (x0:=z) (y:=x).
  eapply subst_ty_trm; auto. eapply Hz.
  rewrite <- subst_intro. all: auto.
Qed.

(** Renaming the name of the opening variable for term typing. #<br>#
    [ok G]                   #<br>#
    [z] fresh                #<br>#
    [G, z: U ⊢ t^z ∶ T^z]    #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ t^x ∶ T^x]         *)
Lemma renaming_fresh : forall L G T (t : trm) U x,
    ok G ->
    (forall x : var, x \notin L -> G & x ~ T ⊢ open x t ∶ U) ->
    G ⊢ trm_var (avar_f x) ∶ T ->
    G ⊢ open x t ∶ U.
Proof.
  introv Hok Hu Hx.
  pick_fresh y.
  rewrite subst_intro with (x0:=y) (y0:=x) by auto.
  rewrite <- subst_fresh with (x0:=y) (y0:=x) by auto.
  eapply subst_ty_trm; auto. rewrite subst_fresh; auto.
Qed.

Lemma renaming_push : forall L G T (t : trm) U x,
    ok (G & x ~ T) ->
    (forall x : var, x \notin L -> G & x ~ T ⊢ open x t ∶ U) ->
    G & x ~ T ⊢ open x t ∶ U.
Proof.
  introv Hok Hu. eapply renaming_fresh with (L:=L); eauto.
  intros. eapply weaken_rules; eauto.
Qed.

Lemma weaken_middle_trm : forall y' n T' G T T'' (t : trm) x x',
    ok (G & x ~ open_rec n x' T) ->
    y' \notin (fv T \u fv T' \u fv T'' \u fv t \u fv_env G \u dom G \u \{x}) ->
    G & y' ~ T' & x ~ open_rec n y' T ⊢ open_rec n y' t ∶ open_rec n y' T'' ->
    G ⊢ trm_var (avar_f x') ∶ T' ->
    G & x ~ open_rec n x' T ⊢ open_rec n x' t ∶ open_rec n x' T''.
Proof.
  intros.
  repeat rewrite (subst_intro (x:=y') x' n); auto.
  rewrite subst_single.
  apply ok_push_inv in H. destruct H.
  eapply (proj51 (subst_rules x' T')); trivial; try assumption; auto 3.
  rewrite subst_fresh; auto. rewrite <- subst_single. apply weaken_ty_trm; auto.
Qed.
