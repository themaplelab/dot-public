(** remove printing ~ *)

(** This module reasons about the precise types of variables in inert contexts. *)

Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import Coq.Program.Equality.
Require Import AbstractSyntax Typing.
Require Import PreciseTyping GeneralTyping RecordTypes InertTypes DefRecordInertTyping Narrowing.

Opaque open_rec fv.

(** ** Precise Flow Lemmas *)

(** If [G ⊢! x: T ⪼ U] then [G(x) = T]. *)
Lemma pf_binds: forall G x T U,
    G ⊢! x ∶ T ⪼ U ->
    binds x T G.
Proof.
  introv Pf. induction Pf; auto.
Qed.

(** If [G(x) = forall(S)T], then [x]'s precise type can be only [forall(S)T]. *)
Lemma precise_flow_all_inv : forall x G S T U,
    G ⊢! x ∶ typ_all S T ⪼ U ->
    U = typ_all S T.
Proof.
  introv Hpf.
  dependent induction Hpf; auto;
    specialize (IHHpf S T eq_refl); inversion IHHpf.
Qed.

Lemma precise_flow_con_inv : forall x G Ts is' T U,
    G ⊢! x ∶ typ_con Ts is' T ⪼ U ->
    U = typ_con Ts is' T.
Proof.
  introv Hpf.
  dependent induction Hpf; auto;
    specialize (IHHpf Ts is' T eq_refl); inversion IHHpf.
Qed.

(** The following two lemmas say that the type to which a variable is bound in an inert context is inert. *)
Lemma binds_inert : forall G x T,
    binds x T G ->
    inert G ->
    inert_typ T.
Proof.
  introv Bi HiG. induction HiG.
  - false * binds_empty_inv.
  - destruct (binds_push_inv Bi).
    + destruct H1. subst. assumption.
    + destruct H1. apply (IHHiG H2).
Qed.

(** See [binds_inert]. *)
Lemma pf_inert_T : forall G x T U,
    inert G ->
    G ⊢! x ∶ T ⪼ U ->
    inert_typ T.
Proof.
  introv Hi Pf. induction Pf; eauto.
  apply (binds_inert H Hi).
Qed.

(** See [inert_typ_bnd_record] *)
Lemma pf_rcd_T : forall G x T U,
    inert G ->
    G ⊢! x ∶ (typ_bnd T) ⪼ U ->
    record_type T.
Proof.
  introv Hi Pf. apply (pf_inert_T Hi) in Pf; inversions Pf; assumption.
Qed.

(** If [G(x) = mu(x: T)], then [x]'s precise type can be only [mu(x: T)]
     or a record type. *)
Lemma pf_bnd_same_or_rcd : forall G x T U,
    inert G ->
    G ⊢! x ∶ typ_bnd T ⪼ U ->
    U = typ_bnd T \/ record_type U.
Proof.
  introv Hi Pf.
  dependent induction Pf; try solve [left*]; right.
  - specialize (IHPf T Hi eq_refl). destruct IHPf as [eq | r].
    * apply open_record_type.
      inversion eq. apply* pf_rcd_T.
    * inversion r. inversion H.
  - destruct (IHPf T Hi eq_refl) as [F | Hr]. inversion F.
    inversion Hr. inversions H.
    exists ls. assumption.
  - destruct (IHPf T Hi eq_refl) as [F | Hr]. inversion F.
    inversion Hr. inversions H.
    eexists. apply* rt_one.
Qed.

(** If [x]'s precise type is [mu(x: U)], then [G(x) = mu(x: U)] *)
Lemma pf_inert_bnd_U: forall G x T U,
    inert G ->
    G ⊢! x ∶ T ⪼ typ_bnd U ->
    T = typ_bnd U.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert_T Hi Pf).
  destruct HT.
  - apply precise_flow_all_inv in Pf. congruence.
  - apply precise_flow_con_inv in Pf. congruence.
  - destruct (pf_bnd_same_or_rcd Hi Pf) as [Heq | Hr].
    + auto.
    + inversion Hr. inversion H0.
Qed.

(** If [x]'s precise type is a field or type declaration, then [G(x)] is
    a recursive type. *)
Lemma pf_inert_rcd_U: forall G x T D,
    inert G ->
    G ⊢! x ∶ T ⪼ typ_rcd D ->
    exists U, T = typ_bnd U.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert_T Hi Pf).
  destruct HT.
  - apply precise_flow_all_inv in Pf. congruence.
  - apply precise_flow_con_inv in Pf. congruence.
  - exists* T.
Qed.


(** If [x]'s precise type is a record type, then [G(x)] is a recursive type. *)
Lemma pf_inert_rcd_typ_U: forall G x T Ds,
    inert G ->
    G ⊢! x ∶ T ⪼ Ds ->
    record_type Ds ->
    exists U, T = typ_bnd U.
Proof.
  introv Hi Pf Hr.
  lets HT: (pf_inert_T Hi Pf).
  destruct HT.
  - apply precise_flow_all_inv in Pf. subst.
    inversion Hr. inversion H.
  - apply precise_flow_con_inv in Pf. subst.
    inversion Hr. inversion H0.
  - exists* T.
Qed.

(** The following two lemmas express that if [x]'s precise type is a function type,
    then [G(x)] is the same function type. *)
Lemma pf_inert_lambda_U : forall x G S T U,
    inert G ->
    G ⊢! x ∶ U ⪼ typ_all S T ->
    U = typ_all S T.
Proof.
  introv Hi Pf.
  lets Hiu: (pf_inert_T Hi Pf).
  destruct Hiu.
  - apply precise_flow_all_inv in Pf. congruence.
  - apply precise_flow_con_inv in Pf. congruence.
  - destruct (pf_bnd_same_or_rcd Hi Pf) as [H1 | H1]; inversions H1.
    inversion H0.
Qed.

Lemma pf_inert_con_U : forall x G Ts is' T U,
    inert G ->
    G ⊢! x ∶ U ⪼ typ_con Ts is' T ->
    U = typ_con Ts is' T.
Proof.
  introv Hi Pf.
  lets Hiu: (pf_inert_T Hi Pf).
  destruct Hiu.
  - apply precise_flow_all_inv in Pf. congruence.
  - apply precise_flow_con_inv in Pf. congruence.
  - destruct (pf_bnd_same_or_rcd Hi Pf) as [H1 | H1]; inversions H1.
    inversion H0.
Qed.

(** See [pf_inert_lambda_U]. *)
Lemma inert_precise_all_inv : forall x G S T U,
    inert G ->
    G ⊢! x ∶ U ⪼ typ_all S T ->
    binds x (typ_all S T) G.
Proof.
  introv Hi Htyp. lets H: (pf_inert_lambda_U Hi Htyp). subst.
  apply* pf_binds.
Qed.

Lemma inert_precise_con_inv : forall x G Ts is' T U,
    inert G ->
    G ⊢! x ∶ U ⪼ typ_con Ts is' T ->
    binds x (typ_con Ts is' T) G.
Proof.
  introv Hi Htyp. lets H: (pf_inert_con_U Hi Htyp). subst.
  apply* pf_binds.
Qed.

(** In an inert context, the precise type of a variable
    cannot be bottom. *)
Lemma pf_bot_false : forall G x T,
    inert G ->
    G ⊢! x ∶ T ⪼ typ_bot ->
    False.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert_T Hi Pf). destruct HT.
  - apply precise_flow_all_inv in Pf. congruence.
  - apply precise_flow_con_inv in Pf. congruence.
  - destruct (pf_bnd_same_or_rcd Hi Pf); inversion H0. inversion H1.
Qed.

(** In an inert context, the precise type of
    a variable cannot be type selection. *)
Lemma pf_psel_false : forall G T x y A,
    inert G ->
    G ⊢! x ∶ T ⪼ typ_sel y A ->
    False.
Proof.
  introv Hi Pf.
  lets HT: (pf_inert_T Hi Pf). destruct HT.
  - apply precise_flow_all_inv in Pf. congruence.
  - apply precise_flow_con_inv in Pf. congruence.
  - destruct (pf_bnd_same_or_rcd Hi Pf); inversion H0. inversion H1.
Qed.

(** If [G(x) = mu(T)], and [G ⊢! x : ... /\ D /\ ...], then [T^x = ... /\ D /\ ...]. *)
Lemma pf_record_sub : forall x G T T' D,
    inert G ->
    G ⊢! x ∶ typ_bnd T ⪼ T' ->
    record_has T' D ->
    record_has (open x T) D.
Proof.
  introv Hi Pf Hr. dependent induction Pf; auto.
  - inversions Hr.
  - apply (pf_inert_bnd_U Hi) in Pf. congruence.
Qed.

(** If [G(x) = mu(S)] and [G ⊢! x : D], where [D] is a field or type declaration,
    then [S^x = ... /\ D /\ ...]. *)
Lemma precise_flow_record_has: forall S G x D,
    inert G ->
    G ⊢! x ∶ typ_bnd S ⪼ typ_rcd D ->
    record_has (open x S) D.
Proof.
  introv Hi Pf. apply* pf_record_sub.
Qed.

(** If
    - [G ⊢! x : mu(T) ⪼ {A: T1..T1}]
    - [G ⊢! x : mu(T) ⪼ {A: T2..T2}]
    then [T1 = T2]. *)
Lemma pf_record_unique_tight_bounds_rec : forall G x T A T1 T2,
    inert G ->
    G ⊢! x ∶ typ_bnd T ⪼ typ_rcd (dec_typ A T1 T1) ->
    G ⊢! x ∶ typ_bnd T ⪼ typ_rcd (dec_typ A T2 T2) ->
    T1 = T2.
Proof.
  introv Hi Pf1 Pf2.
  pose proof (precise_flow_record_has Hi Pf1) as H1.
  pose proof (precise_flow_record_has Hi Pf2) as H2.
  eapply unique_rcd_typ; eauto.
  apply open_record_type; apply* pf_rcd_T.
Qed.

(** If
    - [G ⊢! x : T ⪼ {A: T1..T1}]
    - [G ⊢! x : T ⪼ {A: T2..T2}]
    then [T1 = T2]. *)(** *)
Lemma pf_inert_unique_tight_bounds : forall G x T T1 T2 A,
    inert G ->
    G ⊢! x ∶ T ⪼ typ_rcd (dec_typ A T1 T1) ->
    G ⊢! x ∶ T ⪼ typ_rcd (dec_typ A T2 T2) ->
    T1 = T2.
Proof.
  introv Hi Pf1 Pf2.
  pose proof (pf_inert_rcd_U Hi Pf1) as [?U ?H]; subst.
  apply* pf_record_unique_tight_bounds_rec.
Qed.

(** The type to which a variable is bound in an environment is unique. *)
Lemma x_bound_unique: forall G x T1 T2 U1 U2,
    G ⊢! x ∶ T1 ⪼ U1 ->
    G ⊢! x ∶ T2 ⪼ U2 ->
    T1 = T2.
Proof.
  introv Pf1 Pf2.
  apply pf_binds in Pf1.
  apply pf_binds in Pf2.
  apply (binds_functional Pf1 Pf2).
Qed.

(** If a typing context is inert, then the variables in its domain are distinct. #<br>#
    Note: [ok] is defined in [TLC.LibEnv.v]. *)
Lemma inert_ok : forall G,
    inert G ->
    ok G.
Proof.
  introv Hi. induction Hi; auto.
Qed.

Hint Resolve inert_ok : core.

(** If [G ⊢! x : {A: S..U}] then [S = U]. *)
Lemma pf_dec_typ_inv : forall G x T A S U,
    inert G ->
    G ⊢! x ∶ T ⪼ typ_rcd (dec_typ A S U) ->
    S = U.
Proof.
  introv Hi Pf. destruct (pf_inert_rcd_U Hi Pf) as [V H]. subst.
  destruct (pf_bnd_same_or_rcd Hi Pf); try congruence.
  destruct H as [?ls ?H]. inversions H. inversions* H1.
Qed.

Lemma pf_dec_trm_inv : forall G x T a S U,
    inert G ->
    G ⊢! x ∶ T ⪼ typ_rcd (dec_trm a S U) ->
    S = U.
Proof.
  introv Hi Pf. destruct (pf_inert_rcd_U Hi Pf) as [V H]. subst.
  destruct (pf_bnd_same_or_rcd Hi Pf); try congruence.
  destruct H as [?ls ?H]. inversions H. inversions* H1.
Qed.
