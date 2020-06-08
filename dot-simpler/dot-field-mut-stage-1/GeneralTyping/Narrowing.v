(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import AbstractSyntax GeneralTyping Subenvironments Weakening.

(** * Narrowing Lemma *)
(** The narrowing lemma states that typing is preserved under subenvironments.
    The proof is by mutual induction on term typing, definition typing,
    and subtyping. *)

Lemma narrow_var : forall G (x : var) T,
    binds x T G ->
    forall G',
      G' ⪯ G ->
      G' ⊢ trm_var (avar_f x) ∶ T.
Proof.
  introv B.
  induction 1;
    [exfalso; eauto using binds_empty_inv
    | apply binds_push_inv in B];
    destruct_all; subst;
      eauto using ty_var, weaken_subtyp, weaken_ty_trm.
Qed.

(** [G ⊢ t: T]                 #<br>#
    [G' subG G]                #<br>#
    [ok G']                    #<br>#
    [―――――――――――――――――]        #<br>#
    [G' ⊢ t: T]

    and

    [G ⊢ d: D]                 #<br>#
    [G' subG G]                #<br>#
    [ok G']                    #<br>#
    [―――――――――――――――――]        #<br>#
    [G' ⊢ d: D]

    and

    [G ⊢ ds :: T]              #<br>#
    [G' subG G]                #<br>#
    [ok G']                    #<br>#
    [―――――――――――――――――]        #<br>#
    [G' ⊢ ds :: T]

    and

    [G ⊢ S <: U]               #<br>#
    [G' subG G]                #<br>#
    [ok G']                    #<br>#
    [―――――――――――――――――]        #<br>#
    [G' ⊢ S <: U]              #<br># *)
Lemma narrow_rules:
  (forall G (t : trm) T, G ⊢ t ∶ T -> forall G',
    G' ⪯ G ->
    G' ⊢ t ∶ T)
/\ (forall G (l : lit) T, G ⊢ l ∶ T -> forall G',
    G' ⪯ G ->
    G' ⊢ l ∶ T)
/\ (forall G d D, G ⊢ d ∶d D -> forall G',
    G' ⪯ G ->
    G' ⊢ d ∶d D)
/\ (forall G (ds : defs) T, G ⊢ ds ∶ T -> forall G',
    G' ⪯ G ->
    G' ⊢ ds ∶ T)
/\ (forall G S U, G ⊢ S <: U -> forall G',
    G' ⪯ G ->
    G' ⊢ S <: U).
Proof.
  apply rules_mutind; intros;
    match goal with
    | [ B: binds _ _ _, H : ?G' ⪯ _ |- _ ⊢ trm_var (avar_f _) ∶ _ ] =>
      eauto using narrow_var
    | _ => try fresh_constructor; eauto
    end.
Qed.


(** The narrowing lemma, formulated only for term typing. *)
Lemma narrow_typing: forall G G' (t : trm) T,
  G ⊢ t ∶ T ->
  G' ⪯ G ->
  G' ⊢ t ∶ T.
Proof.
  intros. apply* narrow_rules.
Qed.

(** The narrowing lemma, formulated only for subtyping. *)
Lemma narrow_subtyping: forall G G' S U,
  G ⊢ S <: U ->
  G' ⪯ G ->
  G' ⊢ S <: U.
Proof.
  intros. apply* narrow_rules.
Qed.

Lemma narrow_typing_subtyp: forall G G' (t : trm) T U,
    G ⊢ t ∶ T ->
    G' ⪯ G ->
    G' ⊢ T <: U ->
    G' ⊢ t ∶ U.
Proof.
  intros. eauto using ty_sub, narrow_typing.
Qed.

Lemma ty_open_implies_ty_bnd: forall G1 y T1,
    (forall G (t : trm) T,
        G ⊢ t ∶ T ->
        (forall G2, G = G1 & y ~ open y T1 & G2 ->
               G1 & y ~ typ_bnd T1 & G2 ⊢ t ∶ T)) /\
    (forall G (l : lit) T,
        G ⊢ l ∶ T ->
        (forall G2, G = G1 & y ~ open y T1 & G2 ->
               G1 & y ~ typ_bnd T1 & G2 ⊢ l ∶ T)) /\
    (forall G d D,
        G ⊢ d ∶d D ->
        (forall G2, G = G1 & y ~ open y T1 & G2 ->
               G1 & y ~ typ_bnd T1 & G2 ⊢ d ∶d D)) /\
    (forall G (ds : defs) T,
        G ⊢ ds ∶ T ->
        (forall G2, G = G1 & y ~ open y T1 & G2 ->
               G1 & y ~ typ_bnd T1 & G2 ⊢ ds ∶ T)) /\
    (forall G T T',
        G ⊢ T <: T' ->
        (forall G2, G = G1 & y ~ open y T1 & G2 ->
               G1 & y ~ typ_bnd T1 & G2 ⊢ T <: T')).
Proof.
  intros. apply rules_mutind; intros; subst;
            try solve [fresh_constructor || econstructor; auto].
  pose proof (binds_middle_inv b) as Bi.
  destruct Bi as [ Bi | [ [Fr [ Eqx ExT ]] | [Fr [Neqx Bi]]]]; subst; auto.
Qed.

Lemma ty_open_implies_ty_bnd_push: forall G y T t U,
    G & y ~ (open y T) ⊢ t ∶ U ->
    G & y ~ typ_bnd T ⊢ t ∶ U.
Proof.
  intros. rewrite <- (concat_empty_r (G & _)).
  eapply (proj1 (ty_open_implies_ty_bnd G y T));
    eauto using concat_empty_r.
Qed.

Lemma ty_open_implies_ty_bnd_defs_push: forall G y T (ds : defs) U,
    G & y ~ (open y T) ⊢ ds ∶ U ->
    G & y ~ typ_bnd T ⊢ ds ∶ U.
Proof.
  intros. rewrite <- (concat_empty_r (G & _)).
  eapply (ty_open_implies_ty_bnd G y T);
    eauto using concat_empty_r.
Qed.
