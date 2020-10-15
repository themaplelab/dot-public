(** remove printing ~ *)

Set Implicit Arguments.

Require Import DotTactics LibExtra.
Require Import AbstractSyntax PreTyping Typing GeneralTyping.

(** * Substitution Classes *)
(* DOT uses a dependent subsitution lemma. Here we define typeclasses to specify
the substition lemmas for the various kinds of syntax. *)
Class DecTySubstMiddle {A : Set} `{SubstVar A} `(DecTyping A) :=
  dec_ty_subst_middle : forall y S G1 G2 x d D,
    x # G2 ->
    G1 & x ~ S & G2 ⊢ d ∶d D ->
    x \notin fv_env G1 ->
    G1 & (subst_env x y G2) ⊢ trm_var (avar_f y) ∶ subst_var x y S ->
    G1 & (subst_env x y G2) ⊢ subst_var x y d ∶d subst_var x y D.

Class TySubstMiddle {A : Set} `{SubstVar A} `(Typing A) :=
  ty_subst_middle : forall y S G1 G2 x t T,
    x # G2 ->
    G1 & x ~ S & G2 ⊢ t ∶ T ->
    x \notin fv_env G1 ->
    G1 & (subst_env x y G2) ⊢ trm_var (avar_f y) ∶ subst_var x y S ->
    G1 & (subst_env x y G2) ⊢ subst_var x y t ∶ subst_var x y T.

Class TysSubstMiddle {A : Set} `{SubstVar A} `(Typings A) :=
  tys_subst_middle : forall y S G1 G2 x ts Ts,
    x # G2 ->
    G1 & x ~ S & G2 ⊢ ts :: Ts ->
    x \notin fv_env G1 ->
    G1 & (subst_env x y G2) ⊢ trm_var (avar_f y) ∶ subst_var x y S ->
    G1 & (subst_env x y G2) ⊢ subst_var x y ts :: subst_var x y Ts.

Section TySubstMiddleLemmas.
  Context {A : Set} {SA: SubstVar A}.

  Section DecTy.
    Context {DT: DecTyping A} {H : @DecTySubstMiddle A SA DT}.

    Hint Extern 4 => apply dec_ty_subst_middle : core.

    Lemma dec_ty_subst : forall y S Gamma x d D,
        Gamma & x ~ S ⊢ d ∶d D ->
        x \notin fv_env Gamma ->
        Gamma ⊢ trm_var (avar_f y) ∶ subst_var x y S ->
        Gamma ⊢ subst_var x y d ∶d subst_var x y D.
    Proof.
      introv. rewrite <- (concat_empty_r (Gamma & x ~ S)).
      intros HTy Hx. rewrite <- (concat_empty_r Gamma).
      erewrite <- map_empty; eauto.
    Qed.
  End DecTy.

  Section Ty.
    Context {Ty: Typing A} {H : @TySubstMiddle A SA Ty}.

    Hint Extern 4 => apply ty_subst_middle : core.

    Lemma ty_subst : forall y S Gamma x t T,
        Gamma & x ~ S ⊢ t ∶ T ->
        x \notin fv_env Gamma ->
        Gamma ⊢ trm_var (avar_f y) ∶ subst_var x y S ->
        Gamma ⊢ subst_var x y t ∶ subst_var x y T.
    Proof.
      introv. rewrite <- (concat_empty_r (Gamma & x ~ S)).
      intros HTy Hx. rewrite <- (concat_empty_r Gamma).
      erewrite <- map_empty; eauto.
    Qed.

    (** Renaming Lemmas *)
    Context {OA: Openable A} {FA: FreeVar A}.
    Context {AS: AbstractSyntax OA FA SA}.
    Context {SI: SubstIntro AS}.

    (** Renaming the name of the opening variable for term typing. #<br>#
    [z] fresh                #<br>#
    [G, z: U ⊢ t^z ∶ T^z]    #<br>#
    [G ⊢ x∶ U]               #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ t^x ∶ T^x]         *)
    Lemma renaming : forall G n z T U t x,
        z # G ->
        z \notin (fv_env G \u fv U \u fv T \u fv t) ->
        G & z ~ U ⊢ open_rec n z t ∶ open_rec n z T ->
        G ⊢ trm_var (avar_f x) ∶ U ->
        G ⊢ open_rec n x t ∶ open_rec n x T.
    Proof.
      introv Hnz Hnz' Hz Hx.
      rewrite subst_intro with (x0:=z) (y:=x) by auto.
      rewrite subst_intro with (x0:=z) (y:=x) by auto.
      eapply ty_subst; auto. eapply Hz. rewrite subst_fresh. all: auto.
    Qed.

    (** Renaming lemma for function bodies. #<br>#
    [z notin L -> G, z: T ⊢ t^z ∶ U^z]    #<br>#
    [G ⊢ x∶ U]                       #<br>#
    [――――――――――――――――――――――]         #<br>#
    [G ⊢ t^x ∶ T^x]         *)
    Lemma renaming_fun_app : forall L Gamma T U t x,
        (forall x : var,
            x \notin L ->
            Gamma & x ~ T ⊢ open x t ∶ open x U) ->
        Gamma ⊢ trm_var (avar_f x) ∶ T ->
        Gamma ⊢ open x t ∶ open x U.
    Proof.
      intros * Hopen Hx.
      pick_fresh_gen (fv_env Gamma \u fv T \u fv U \u fv t \u dom Gamma \u L) z.
      assert (z \notin dom Gamma) by auto.
      assert (z \notin (fv_env Gamma \u fv T \u fv U \u fv t)) by auto.
      assert (z \notin L) as HL by auto.
      apply Hopen in HL.
      eapply renaming; eauto 2.
    Qed.

    (** Renaming the name of the opening variable for definition typing.  #<br>#

    [z] fresh                #<br>#
    [G, z: T^z ⊢ ds^z ∶ T^z] #<br>#
    [G ⊢ x∶ T^x]             #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ ds^x ∶ T^x]         *)
    Lemma renaming_open : forall G n z T t x,
        z # G ->
        z \notin (fv_env G \u fv T \u fv t) ->
        G & z ~ open_rec n z T ⊢ open_rec n z t ∶ open_rec n z T ->
        G ⊢ trm_var (avar_f x) ∶ open_rec n x T ->
        G ⊢ open_rec n x t ∶ open_rec n x T.
    Proof.
      introv Hnz Hnz' Hz Hx.
      rewrite subst_intro with (x0:=z) (y:=x) by auto.
      rewrite subst_intro with (x0:=z) (y:=x) by auto.
      eapply ty_subst; auto. eapply Hz. rewrite <- subst_intro. all: auto.
    Qed.

    (** Renaming the name of the opening variable for term typing. #<br>#
    [z] fresh                #<br>#
    [G, z: U ⊢ t^z ∶ T^z]    #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ t^x ∶ T^x]         *)
    Lemma renaming_fresh : forall L G T t U x,
        (forall x : var, x \notin L -> G & x ~ T ⊢ open x t ∶ U) ->
        G ⊢ trm_var (avar_f x) ∶ T ->
        G ⊢ open x t ∶ U.
    Proof.
      introv Hu Hx.
      pick_fresh_gen (L \u dom G \u fv_env G \u fv U \u fv T \u fv t) y.
      rewrite subst_intro with (x0:=y) (y0:=x) by auto.
      rewrite <- subst_fresh with (x0:=y) (y0:=x) by auto.
      eapply ty_subst; auto. rewrite subst_fresh; auto.
    Qed.

    Context {TW: PreTypingWeakenMiddle (TyPreTyping Ty)}.
    Hint Extern 3 => simple apply weaken_middle : core.

    Lemma renaming_push : forall L Gamma T t U x,
        x # Gamma ->
        (forall x : var, x \notin L -> Gamma & x ~ T ⊢ open x t ∶ U) ->
        Gamma & x ~ T ⊢ open x t ∶ U.
    Proof.
      introv Hfr Hu. eapply renaming_fresh with (L:=L); eauto.
    Qed.

    Lemma renaming_open_push : forall L Gamma T t U x,
        x # Gamma ->
        (forall x : var, x \notin L -> Gamma & x ~ open x T ⊢ open x t ∶ open x U) ->
        Gamma & x ~ open x T ⊢ open x t ∶ open x U.
    Proof.
      introv Hfr Hu.
      pick_fresh_gen (L \u dom Gamma \u fv_env Gamma \u fv U \u fv T \u fv t \u \{x}) y.
      rewrite subst_intro with (X:=t) (x0:=y) (y0:=x) by auto.
      rewrite subst_intro with (X:=U) (x0:=y) (y0:=x) by auto.
      assert (y \notin L) by auto.
      pose proof (Hu y H0); clear H0.
      apply (weaken_middle (x:=x)) with (T':= open x T) in H1;
        auto.
      eapply ty_subst; auto.
      - rewrite fv_env_push. notin_solve. apply notin_open; auto.
      - rewrite <- subst_intro by auto. auto.
    Qed.
  End Ty.

  Section Tys.
    Context {Tys: Typings A} {H : @TysSubstMiddle A SA Tys}.

    Hint Extern 4 => apply tys_subst_middle : core.

    Lemma tys_subst : forall y S Gamma x ts Ts,
        Gamma & x ~ S ⊢ ts :: Ts ->
        x \notin fv_env Gamma ->
        Gamma ⊢ trm_var (avar_f y) ∶ subst_var x y S ->
        Gamma ⊢ subst_var x y ts :: subst_var x y Ts.
    Proof.
      introv. rewrite <- (concat_empty_r (Gamma & x ~ S)).
      intros HTy Hx. rewrite <- (concat_empty_r Gamma).
      erewrite <- map_empty; eauto.
    Qed.
  End Tys.
End TySubstMiddleLemmas.

Section DefsTySubstMiddle.
  Context {A : Set} {SA: SubstVar A} {L: LabelOf A}.
  Context {SL: SubstLabel SA L}.
  Context {DT: DecTyping A} {DTS: @DecTySubstMiddle A SA DT}.

  Instance DefsTySubstMiddle : TySubstMiddle ty_defs.
  Proof.
    hnf; introv Hfr Hty;
      remember (G1 & x ~ S & G2) as G eqn:Heq;
      induction Hty; subst; intros; sympl;
        constructor; try eapply (dec_ty_subst_middle); eauto.
    rewrite subst_label. apply* subst_labels_hasnt.
  Qed.
End DefsTySubstMiddle.
Existing Instance DefsTySubstMiddle.
