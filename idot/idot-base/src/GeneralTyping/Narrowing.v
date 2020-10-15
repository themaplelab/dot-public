(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import AbstractSyntax PreTyping Typing.
Require Import GeneralTyping Subenvironments Weakening.

(** * Narrowing Lemma *)
(** The narrowing lemma states that typing is preserved under subenvironments.
    The proof is by mutual induction on term typing, definition typing,
    and subtyping. *)

Implicit Types (d : def) (ds : defs).

Local Hint Extern 5 (_ ⊢ _ ∶ _) => simple apply weaken_ok : core.
Local Hint Extern 5 (_ ⊢ _ <: _) => simple apply weaken_ok : core.

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
    destruct_all; subst; eauto using weaken_ok.
Qed.

Lemma narrow_def : forall G d D,
    G ⊢ d ∶d D ->
    forall G',
      G' ⪯ G ->
      G' ⊢ d ∶d D.
Proof.
  induction 2; auto.
  inversions H; auto.
Qed.

Lemma narrow_defs : forall G ds T,
    G ⊢ ds ∶ T ->
    forall G',
      G' ⪯ G ->
      G' ⊢ ds ∶ T.
Proof.
  induction 1; eauto using narrow_def.
Qed.

(** [G ⊢ t: T]                 #<br>#
    [G' subG G]                #<br>#
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
/\ (forall G S U, G ⊢ S <: U -> forall G',
    G' ⪯ G ->
    G' ⊢ S <: U)
/\ (forall G avs Ts, G ⊢ avs :: Ts -> forall G',
    G' ⪯ G ->
    G' ⊢ avs :: Ts).
Proof.
  apply rules_mutind; intros;
    match goal with
    | [ B: binds _ _ _, H : ?G' ⪯ _ |- _ ⊢ trm_var (avar_f _) ∶ _ ] =>
      eauto using narrow_var
    | _ => try fresh_constructor; eauto 6 using narrow_defs
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
