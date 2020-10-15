(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import Coq.Program.Equality.
Require Import AbstractSyntax Typing.

Implicit Types (ds : defs) (hds : heap_defs).

(** * Record Types *)

(** A record declaration is either a type declaration with equal bounds,
    or a field declaration.*)
Inductive record_dec : dec -> Prop :=
| rd_typ : forall A T, record_dec (dec_typ A T T)
| rd_trm : forall a T, record_dec (dec_trm a T T).

(** Given a record declaration, a [record_typ] keeps track of the declaration's
    field member labels (i.e. names of fields) and type member labels
    (i.e. names of abstract type members). [record_typ] also requires that the
    labels are distinct.  *)
Inductive record_typ : typ -> fset label -> Prop :=
| rt_one : forall D l,
  record_dec D ->
  l = label_of D ->
  record_typ (typ_rcd D) \{l}
| rt_cons: forall T ls D l,
  record_typ T ls ->
  record_dec D ->
  l = label_of D ->
  l \notin ls ->
  record_typ (typ_and T (typ_rcd D)) (union ls \{l}).

(** A [record_type] is a [record_typ] with an unspecified set of labels. The meaning
    of [record_type] is an intersection of type/field declarations with distinct labels. *)
Definition record_type T := exists ls, record_typ T ls.

(** Given a type [T = D1 /\ D2 /\ ... /\ Dn] and member declaration [D], [record_has T D] tells whether
    [D] is contained in the intersection of [Di]'s. *)
Inductive record_has: typ -> dec -> Prop :=
| rh_one : forall D,
    record_has (typ_rcd D) D
| rh_andl : forall T U D,
    record_has T D ->
    record_has (typ_and T U) D
| rh_andr : forall T U D,
    record_has U D ->
    record_has (typ_and T U) D.

Hint Constructors record_typ record_has : core.

(** ** Lemmas About Records and Record Types *)

Section HasntNotIn.
  Context {A : Set} `{LA : LabelOf A} `{DTA : DecTyping A}.
  Context {DTL : DecTypingLabels DTA}.
  (** [G ⊢ ds :: U]                          #<br>#
    [U] is a record type with labels [ls]  #<br>#
    [ds] are definitions with label [ls']  #<br>#
    [l \notin ls']                          #<br>#
    [―――――――――――――――――――――――――――――――――――]  #<br>#
    [l \notin ls] *)
  Lemma hasnt_notin : forall Gamma (ds : list A) ls l U,
      Gamma ⊢ ds ∶ U ->
      record_typ U ls ->
      labels_hasnt ds l ->
      l \notin ls.
  Proof.
    intros * H. gen H ls l.
    induction 1.
    - inversion 1; subst.
      intros Hhnt.
      pose proof (labels_hasnt_cons_inv Hhnt) as [? Hnil].
      erewrite ty_def_label_eq; eauto.
      rewrite notin_singleton; auto.
    - intros * Hrt.
      inversion Hrt as [| ?T ?ls ?D ?l Hrt' Hrd Heq Hni]; subst.
      intros Hhnt.
      pose proof (labels_hasnt_cons_inv Hhnt) as [? Hhnt'].
      rewrite notin_union, notin_singleton.
      erewrite ty_def_label_eq; eauto.
  Qed.
End HasntNotIn.

Section RecordHasTyDefs.
  Context {A : Set} `{LA : LabelOf A} `{DTA : DecTyping A}.
  (** [G ⊢ ds :: ... /\ D /\ ...]       #<br>#
    [―――――――――――――――――――――――]       #<br>#
    [exists d, ds = ... /\ d /\ ...]       #<br>#
    [G ⊢ d: D]                      *)
  Lemma record_has_ty_defs: forall G T (ds : list A) D,
      G ⊢ ds ∶ T ->
      record_has T D ->
      exists d, labels_has ds d /\ G ⊢ d ∶d D.
  Proof.
    introv Hdefs Hhas. induction Hdefs.
    - inversion Hhas; subst. exists d. split.
      + unfold labels_has. simpl. cases_if; reflexivity.
      + assumption.
    - inversion Hhas; subst.
      + destruct (IHHdefs H5) as [d' [H3 H4]].
        exists d'. split.
        * unfold labels_has. simpl. cases_if. apply H3.
        * assumption.
      + exists d. split.
        * unfold labels_has. simpl. rewrite If_l; reflexivity.
        * inversions* H5.
  Qed.
End RecordHasTyDefs.

(** [labels(D) = labels(D^x)] *)
Lemma open_dec_preserves_label: forall (D : dec) x i,
  label_of (open_rec i x D) = label_of D.
Proof.
  intros. induction D; reflexivity.
Qed.

Lemma open_rec_record_dec: forall D n x,
  record_dec D -> record_dec (open_rec n x D).
Proof.
  intros. inversion H; constructor.
Qed.

(** [record_dec D]   #<br>#
    [――――――――――――――] #<br>#
    [record_dec D^x] *)
Lemma open_record_dec: forall D x,
  record_dec D -> record_dec (open x D).
Proof.
  auto using open_rec_record_dec.
Qed.

Lemma open_rec_record_typ: forall T ls n x,
  record_typ T ls -> record_typ (open_rec n x T) ls.
Proof.
  introv H.
  induction H; simpl;
    [apply rt_one | apply rt_cons];
    try apply open_rec_record_dec;
    try rewrite open_dec_preserves_label;
    auto.
Qed.

(** [record_typ T]   #<br>#
    [――――――――――――――] #<br>#
    [record_typ T^x] *)
Lemma open_record_typ: forall T x ls,
  record_typ T ls -> record_typ (open x T) ls.
Proof.
  auto using open_rec_record_typ.
Qed.

Lemma open_rec_vars_record_typ: forall ys n T ls,
  record_typ T ls -> record_typ (open_rec_vars n ys T) ls.
Proof.
  induction ys; simpls;
    intros; auto using open_rec_record_typ.
Qed.

(** [record_typ T]   #<br>#
    [――――――――――――――] #<br>#
    [record_typ T^x] *)
Lemma open_record_type: forall T x,
  record_type T -> record_type (open x T).
Proof.
  introv [ls H]. exists ls. apply open_record_typ.
  assumption.
Qed.

Lemma open_vars_record_type: forall ys n T,
  record_type T -> record_type (open_rec_vars n ys T).
Proof.
  unfold record_type.
  introv [ls H]. exists ls.
  eauto using open_rec_vars_record_typ.
Qed.

(** Opening does not affect the labels of a [record_typ]. *)
Lemma opening_preserves_labels : forall z n T ls ls',
    record_typ T ls ->
    record_typ (open_rec n z T) ls' ->
    ls = ls'.
Proof.
  introv Ht Hopen. gen ls'.
  dependent induction Ht; intros.
  - inversions Hopen. rewrite* open_dec_preserves_label.
  - inversions Hopen. rewrite* open_dec_preserves_label.
    specialize (IHHt ls0 H4). rewrite* IHHt.
Qed.

(** Opening does not affect the labels of a [record_type]. *)
Lemma record_dec_open_rec : forall D n z,
  z \notin fv D ->
  record_dec (open_rec n z D) ->
  record_dec D.
Proof.
  intros D n z Hz H.
  inversions H;
    destruct D; sympls; destruct_notin;
      match goal with
      | [ H : _ = _ |- _ ] => inversions H
      end;
      match goal with
      | [ H1: _ \notin ?f ?T1, H2: _ \notin ?f ?T2, H3 : _ = _ |- _ ] =>
        let H := fresh in
        pose proof (open_fresh_injective T1 T2) as H; apply H in H3
      end; subst; eauto; constructor.
Qed.

Lemma record_type_open_rec : forall n z T,
    z \notin fv T ->
    record_type (open_rec n z T) ->
    record_type T.
Proof.
  introv Hz H. destruct H as [ls H].
  exists ls. remember (open_rec n z T) as T' eqn:Heq. gen T. induction H; intros.
  - destruct T; inversion Heq; subst.
    rewrite open_dec_preserves_label.
    constructor; eauto using record_dec_open_rec.
  - destruct T0; inversion Heq; subst. rename T0_1 into T1. rename T0_2 into T2.
    destruct T2; inversion Heq; subst.
    rewrite open_dec_preserves_label in *; sympls; destruct_notin.
    apply rt_cons; eauto using record_dec_open_rec.
Qed.

Lemma record_type_open_rec_vars : forall ys n T,
    fresh (fv T) (length ys) ys ->
    record_type (open_rec_vars n ys T) ->
    record_type T.
Proof.
  induction ys; eauto using record_type_open_rec.
  intros. simpl in H; destruct H.
  simpl in H0. apply (record_type_open_rec n T H).
  eapply IHys; eauto.
  pose proof (fv_open_cases a T n) as H';
    destruct H' as [H' | H']; rewrite H'; auto.
Qed.

Lemma record_type_open_vars_S : forall x ys n T,
    fresh (fv T) (S (length ys)) (x :: ys) ->
    record_type (open_rec_vars n (x :: ys) T) ->
    record_type T.
Proof.
  intros.
  apply (record_type_open_rec_vars (x :: ys) n T); auto.
Qed.

(** If [T] is a record type with labels [ls], and [T = ... /\ D /\ ...],
    then [label(D) isin ls]. *)
Lemma record_typ_has_label_in: forall T D ls,
  record_typ T ls ->
  record_has T D ->
  label_of D \in ls.
Proof.
  introv Htyp Has. generalize dependent D. induction Htyp; intros.
  - inversion Has. subst. apply in_singleton_self.
  - inversion Has; subst; rewrite in_union.
    + left. apply* IHHtyp.
    + right. inversions H5. apply in_singleton_self.
Qed.

(** [T = ... /\ {A: T1..T1} /\ ...] #<br>#
    [T = ... /\ {A: T2..T2} /\ ...] #<br>#
    [―――――――――――――――――――――――――――] #<br>#
    [T1 = T2] *)
Lemma unique_rcd_typ: forall T A T1 T2,
  record_type T ->
  record_has T (dec_typ A T1 T1) ->
  record_has T (dec_typ A T2 T2) ->
  T1 = T2.
Proof.
  introv Htype Has1 Has2.
  generalize dependent T2. generalize dependent T1. generalize dependent A.
  destruct Htype as [ls Htyp]. induction Htyp; intros; inversion Has1; inversion Has2; subst.
  - inversion* H3.
  - inversion* H5.
  - apply record_typ_has_label_in with (D:=dec_typ A T1 T1) in Htyp.
    + inversions H9. false* H1.
    + assumption.
  - apply record_typ_has_label_in with (D:=dec_typ A T2 T2) in Htyp.
    + inversions H5. false* H1.
    + assumption.
  - inversions H5. inversions* H9.
Qed.

Lemma unique_rcd_trm: forall T a T1 T2,
  record_type T ->
  record_has T (dec_trm a T1 T1) ->
  record_has T (dec_trm a T2 T2) ->
  T1 = T2.
Proof.
  introv [ls Htyp] Has1 Has2. gen T1 T2 a.
  induction Htyp; intros; inversion Has1; inversion Has2; subst.
  - inversion* H3.
  - inversion* H5.
  - apply record_typ_has_label_in with (D:=dec_trm a T1 T1) in Htyp.
    + inversions H9. false* H1.
    + assumption.
  - apply record_typ_has_label_in with (D:=dec_trm a T2 T2) in Htyp.
    + inversions H5. false* H1.
    + assumption.
  - inversions H5. inversions* H9.
Qed.

(** [ds = ... /\ {a = t} /\ ...]  #<br>#
    [ds = ... /\ {a = t'} /\ ...] #<br>#
    [―――――――――――――――――――――――――] #<br>#
    [t = t'] *)
Lemma heap_defs_has_inv: forall hds a t t',
    labels_has hds (heap_def_trm a t) ->
    labels_has hds (heap_def_trm a t') ->
    t = t'.
Proof.
  intros. (* unfold labels_has, label_of in *. *)
  inversions H. inversions H0.
  rewrite H1 in H2. inversions H2.
  reflexivity.
Qed.
