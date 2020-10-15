(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import Coq.Program.Equality.
Require Import AbstractSyntax RecordTypes InertTypes
        Typing GeneralTyping.

Implicit Types (ds : defs) (hds : heap_defs).

(** In this module we prove some lemmas relating record types, inert types, and
    definition typing. *)

(** Correspondence between definition typing and record types *)
Section DecTypingRecord.
  Context {A : Set}.
  Class DecTypingRecord `(DecTyping A) :=
    ty_def_record_dec : forall Gamma d D,
      Gamma ⊢ d ∶d D ->
      record_dec D.
End DecTypingRecord.

Instance TyDefDecTypingRecord : DecTypingRecord ty_def.
Proof.
  hnf; induction 1; constructor.
Qed.

Section TyDefsRecordType.
  Context {A : Set} `{LA : LabelOf A} `{DTA : DecTyping A}.
  Context {DTL : DecTypingLabels DTA}.
  Context {DTR : DecTypingRecord DTA}.

  (** The type of definitions is a record type. *)
  Lemma ty_defs_record_type : forall Gamma (ds : list A) T,
      Gamma ⊢ ds ∶ T ->
      record_type T.
  Proof.
    intros Gamma ds T H.
    induction H as [Gamma d D Htyd | Gamma ds d T D Htyds IH Htyd Hlab];
      unfold record_type in *.
    - exists \{label_of D}.
      eauto using ty_def_record_dec.
    - destruct IH as [ls' H].
      eexists; econstructor; eauto using ty_def_record_dec.
      erewrite ty_def_label_eq;
        eauto using hasnt_notin.
  Qed.
End TyDefsRecordType.

Lemma constructor_record_type : forall Gamma L Ts ds T,
    (forall (x : var) (ys : list var),
        length ys = length_s Ts ->
        fresh L (S (length ys)) (x :: ys) ->
        Gamma & ys ~** to_list Ts & x ~ open_vars (x :: ys) T
        ⊢ open_vars (x :: ys) ds ∶ open_vars (x :: ys) T) ->
    record_type T.
Proof.
  introv H.
  pose proof (var_freshes (L \u fv T) (S (length_s Ts))) as [zs Hfr].
  pose proof (fresh_S_split _ _ _ Hfr) as [x [ys Heq]]; subst.
  pose proof (fresh_length _ _ _ Hfr) as Hlen';
    simpl in Hlen'; inversion Hlen' as [Hlen]; clear Hlen'.
  rewrite <- Hlen in Hfr.
  assert (Hfr' : fresh L (S (length ys)) (x :: ys)) by auto.
  pose proof (H x ys Hlen Hfr') as Hty.
  apply (ty_defs_record_type) in Hty.
  apply (record_type_open_vars_S) in Hty; auto.
Qed.

(** Literals have inert types *)
Lemma ty_lit_inert_type : forall Gamma (l : lit) T,
    Gamma ⊢ l ∶ T ->
    inert_typ T.
Proof.
  intros * H.
  inversions H; constructor; eauto using constructor_record_type.
Qed.
