(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra.
Require Import AbstractSyntax GeneralTyping.

(** * A ⊥ typed term *)

Section OmegaIsBotTyped.
  Hint Resolve binds_single_eq : core.

  (** Using [null] as the field label *)
  Parameter null : trm_label.

  (** nPkg = ν (x : {null : ⊥}){null=x.null} *)
  Definition nPkg :=
    lit_obj
      (typ_rcd (dec_trm null typ_bot typ_bot))
      (defs_cons
         (defs_nil)
         (def_trm null (trm_sel (avar_b 0) null))).

  (** Ω = #<br />#
      let newPkg = ν (x : {null : ⊥}){null=x.null} in #<br />#
      nPkg.null *)
  Definition dot_omega :=
    trm_lit nPkg (trm_sel (avar_b 0) null).

  (** ⊢ nPkg : μ(x:{null : ⊥}) *)
  Lemma nPkg_typed :
    empty ⊢ nPkg ∶
          typ_bnd (typ_rcd (dec_trm null typ_bot typ_bot)).
  Proof.
    unfold nPkg.
    apply ty_obj_intro with
        (L:=\{}) (T:=(typ_rcd (dec_trm null typ_bot typ_bot))).
    - intros x Hfr.
      simpl; cases_if; eauto.
  Qed.

  (** ⊢ Ω : ⊥ *)
  Lemma omega_typed_bot :
    empty ⊢ dot_omega ∶ typ_bot.
  Proof.
    unfold dot_omega.
    apply (ty_llit (L:=\{}) _ nPkg_typed).
    intros nPkg Hfr.
    simpl; cases_if.
    apply ty_rcd_elim with (S:=typ_bot).
    eauto.
  Qed.
End OmegaIsBotTyped.
