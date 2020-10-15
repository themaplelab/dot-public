(** remove printing ~ *)

Require Import LibExtra DotTactics AbstractSyntax.
Require Import PreTyping Typing GeneralTyping Weakening.
Require Import InitVar InitTyping InitWeakening Subenvironments Narrowing.

Implicit Types (i : init_typ) (t : trm) (l : lit) (avs : avars).

Local Hint Extern 7 => init_fresh_constructor_extern : core.

Lemma well_init_narrow_rules :
  (forall Gamma Delta t,
      Gamma ⸴ Delta ⊢c t ->
      forall Gamma', Gamma' ⪯ Gamma ->
        Gamma' ⸴ Delta ⊢c t ) /\
  (forall Gamma Delta avs,
      Gamma ⸴ Delta ⊢c avs ->
      forall Gamma', Gamma' ⪯ Gamma ->
        Gamma' ⸴ Delta ⊢c avs) /\
  (forall Gamma Delta l,
      Gamma ⸴ Delta ⊢c l ->
      forall Gamma', Gamma' ⪯ Gamma ->
        Gamma' ⸴ Delta ⊢c l) /\
  (forall Gamma Delta vs t i,
      Gamma ⸴ Delta ⸴ vs ⊢i t ∶ i ->
      forall Gamma', Gamma' ⪯ Gamma ->
        Gamma' ⸴ Delta ⸴ vs ⊢i t ∶ i) /\
  (forall Gamma Delta vs avs is',
      Gamma ⸴ Delta ⸴ vs ⊢i avs :: is' ->
      forall Gamma', Gamma' ⪯ Gamma ->
        Gamma' ⸴ Delta ⸴ vs ⊢i avs :: is').
Proof.
  apply well_init_mut_ind; intros;
    subst; eauto 7 using narrow_typing.
Qed.
