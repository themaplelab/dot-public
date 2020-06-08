(** remove printing ~ *)

(** This module proves the Canonical Forms Lemmas, which allow us
    to retrieve the shape of an item given its type. *)

Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import LibExtra DotTactics.
Require Import AbstractSyntax GeneralTyping
        RecordAndInertTypes PreciseTyping TightTyping InvertibleTyping
        GeneralToTight Subenvironments Weakening Narrowing
        Substitution HeapCorrespondence InertTightSubtyping.

(** * Functions under Inert Contexts *)
(** [inert G]            #<br>#
    [G ⊢ x∶ forall(T)U]       #<br>#
    [――――――――――――――-]    #<br>#
    [exists T', U',]          #<br>#
    [G(x) = forall(T')U']     #<br>#
    [G ⊢ T <: T']        #<br>#
    [forall fresh y, G, y: T ⊢ U'^y <: U^y] *)
Lemma var_typ_all_to_binds: forall G x T U,
    inert G ->
    G ⊢ trm_var (avar_f x) ∶ typ_all T U ->
    (exists L T' U',
        binds x (typ_all T' U') G /\
        G ⊢ T <: T' /\
        (forall y, y \notin L -> G & y ~ T ⊢ (open y U') <: (open y U))).
Proof.
  introv Hin Ht.
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_typ_all (inert_ok Hin) Hinv) as [T' [U' [V' [L [Htp [Hs1 Hs2]]]]]].
  exists L T' U'. repeat split.
  - apply* inert_precise_all_inv.
  - apply~ tight_to_general.
  - assumption.
Qed.

(** * Objects under Inert Contexts *)
(** [inert G]                    #<br>#
    [G ⊢ x∶ {a: T}]              #<br>#
    [―――――――――――――――――――――――]    #<br>#
    [exists S, T', G(x) = mu(S)]       #<br>#
    [S^x = ... /\ {a: T'} /\ ...]  #<br>#
    [G ⊢ T' <: T]                *)
Lemma var_typ_rcd_to_binds: forall G x a T U,
    inert G ->
    G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a T U) ->
    (exists S T',
        binds x (typ_bnd S) G /\
        record_has (open x S) (dec_trm a T' T') /\
        G ⊢ T <: T' /\
        G ⊢ T' <: U).
Proof.
  introv Hin Ht.
  destruct (typing_implies_bound Ht) as [S BiG].
  lets Htt: (general_to_tight_typing Hin Ht).
  lets Hinv: (tight_to_invertible Hin Htt).
  destruct (invertible_to_precise_trm_dec Hinv) as [S' [T' [U' [Htp [Hs1 Hs2]]]]].
  destruct (pf_dec_trm_inv Hin Htp).
  destruct (pf_inert_rcd_U Hin Htp) as [?U' Hr]. subst.
  lets Hr': (precise_flow_record_has Hin Htp). apply pf_binds in Htp.
  exists U'0 S'. repeat_split_right; try assumption; apply* tight_to_general.
Qed.

(** [inert G]                  #<br>#
    [G ⊢ v∶ mu(T)]             #<br>#
    [G ⊢ x∶ T^x]               #<br>#
    [T = ... /\ {a: U} /\ ...  ] #<br>#
    [――――――――――――――――――――――――] #<br>#
    [exists t, ds, v = nu(T)ds     ] #<br>#
    [ds^x = ... /\ {a = t} /\ ...] #<br>#
    [G ⊢ t∶ U] *)
Lemma strong_mu_to_new: forall G s x T,
    inert G ->
    ty_item_s G s x ->
    binds x (typ_bnd T) G ->
    exists ds, binds x (item_obj T (open x ds)) s /\
               G ⊢ open x ds ∶ open x T.
Proof.
  introv Hi Hts Bi.
  inversions Hts; binds_eq.
  exists ds; split; auto.
Qed.

(** * Canonical Forms for Functions

    [inert G]            #<br>#
    [s: G]               #<br>#
    [G ⊢ x∶ forall(T)U]       #<br>#
    [――――――――――――――――――] #<br>#
    [s(x) = lambda(T')t] #<br>#
    [G ⊢ T <: T']        #<br>#
    [G, x: T ⊢ t∶ U]          *)
Lemma canonical_forms_fun: forall G s x T U,
  inert G ->
  heap_correspond G s ->
  G ⊢ trm_var (avar_f x) ∶ typ_all T U ->
  (exists L T' t, binds x (item_fun T' t) s /\
             (G ⊢ T <: T') /\
             forall y, y \notin L -> G & y ~ T ⊢ open y t ∶ open y U).
Proof.
  introv Hin Hst Hty.
  destruct (var_typ_all_to_binds Hin Hty) as [L [S [T' [BiG [Hs1 Hs2]]]]].
  pose proof (corresponding_types Hst BiG).
  inversions H; binds_eq.
  exists (L0 \u L \u dom G) S0 t. repeat_split_right; auto.
  intros.
  assert (Ht: G & y ~ S0 ⊢ open y t ∶ open y T0) by auto.
  apply (narrow_typing_subtyp Ht); auto 2.
  apply subenv_grow; auto 3.
Qed.

(** * Canonical Forms for Objects

    [inert G]            #<br>#
    [s: G]               #<br>#
    [G ⊢ x∶ {a:T}]       #<br>#
    [――――――――――――――――――] #<br>#
    [exists S, ds, t,] #<br>#
    [s(x) = nu(S)ds] #<br>#
    [ds^x = ... /\ {a = t} /\ ...] #<br>#
    [G ⊢ t∶ T] *)
Lemma canonical_forms_obj: forall G s x a S T,
  inert G ->
  heap_correspond G s ->
  G ⊢ trm_var (avar_f x) ∶ (typ_rcd (dec_trm a S T)) ->
  (exists S ds t, binds x (item_obj S (open x ds)) s /\
                  defs_has (open x ds) (def_trm a t) /\
                  G ⊢ t ∶ T).
Proof.
  introv Hi Hst Hty.
  destruct (var_typ_rcd_to_binds Hi Hty) as [?S [?T' [?H [?H [?H ?H]]]]].
  pose proof (corresponding_types Hst H) as Hts.
  destruct (strong_mu_to_new Hi Hts H) as [?ds [?Bis ?]].
  pose proof (record_has_ty_defs H3 H0) as [?d [? ?]].
  inversions H5.
  exists S0 ds t. repeat_split_right; eauto.
Qed.
