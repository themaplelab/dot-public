Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import Coq.Program.Equality.
Require Import
        AbstractSyntax GeneralTyping
        InertTightSubtyping
        GeneralToTight TightTyping InvertibleTyping
        RecordAndInertTypes PreciseTyping
        OperationalSemantics Substitution Weakening
        HeapCorrespondence HeapUpdate CanonicalForms
        InertGeneralSubtyping Subenvironments Narrowing.

(** The typing of a term with a stack *)
Inductive ty_stack : ctx -> typ -> stack -> typ -> Prop :=
  | ty_stack_nil : forall Gamma T U,
      Gamma ⊢ T <: U ->
      ty_stack Gamma T nil U
  | ty_stack_let : forall L Gamma s t S T U,
      ty_stack Gamma T s U ->
      (forall x,
          x \notin L ->
          Gamma & x ~ S ⊢ open x t ∶ T) ->
      ty_stack Gamma S (frame_let t :: s)%list U.

Inductive ty_config : ctx -> config -> typ -> Prop :=
| ty_config_c : forall Gamma s Sigma t T U,
    inert Gamma ->
    heap_correspond Gamma Sigma ->
    ty_stack Gamma T s U ->
    Gamma ⊢ t ∶ T ->
    ty_config Gamma (t; s; Sigma) U.

Inductive config_typd : config -> typ -> Prop :=
| config_typd_c : forall Gamma c U,
    ty_config Gamma c U ->
    config_typd c U.

Hint Constructors ty_stack ty_config config_typd : core.

Notation "'⊢' c '∶' T" := (config_typd c T) (at level 40, c at level 59).

Lemma ty_stack_push : forall G T x T' s U,
    ok G ->
    x # G ->
    ty_stack G T s U ->
    ty_stack (G & x ~ T') T s U.
Proof.
  introv Hok Fr Hts.
  induction Hts.
  + apply ty_stack_nil.
    apply weaken_subtyp; auto.
  + specialize (IHHts Hok Fr).
    eapply (@ty_stack_let (L \u dom Gamma)); eauto 2.
    intros. eapply weaken_rules; eauto.
Qed.
Hint Resolve ty_stack_push : core.

Lemma ty_stack_sub : forall Gamma T T' s U,
  ok Gamma ->
  ty_stack Gamma T s U ->
  Gamma ⊢ T' <: T ->
  ty_stack Gamma T' s U.
Proof.
  introv Hok Hts Hsub.
  inversions Hts; eauto.
  eapply (@ty_stack_let (L \u (dom Gamma))); eauto.
  intros. eauto using narrow_typing.
Qed.

(** * Preservation *)

(** Helper tactics for proving Preservation *)

Ltac invert_red :=
  match goal with
  | [Hr: _ ↦ _ |- _] => inversions Hr
  end.

Local Ltac empty_exists :=
  exists (@empty typ); rewrite (@concat_empty_r typ).

Local Ltac item_inv :=
  match goal with
  | [H : ty_stack ?G ?T _ _, _ : ?x # ?S
     |- (exists G', ty_config _ (_ ; _ ; ?S & ?x ~ ?v) _)] =>
    exists (x ~ T);
    try assert (x # G) by (eauto 3 using heap_correspond_notin_dom);
    pose proof (binds_push_eq x T G);
    pose proof (binds_push_eq x v S);
    try assert (ty_item_s (G & x ~ T) (S & x ~ v) x)
      by (try solve_ty_item_push; eauto using ty_item_s_push);
    try assert (heap_correspond (G & x ~ T) (S & x ~ v))
      by (eauto 3 using heap_correspond_push, heap_correspond_push_obj)
  end.

Local Ltac solve_val :=
  item_inv; econstructor; eauto using ty_stack_push.

Local Ltac solve_empty := empty_exists; eauto.

Local Ltac solve_var :=
  match goal with
  | [ H : trm_var (avar_f ?x) ; _ ; _ ↦ _, Hs : ty_stack _ _ _ _
      |- _] =>
    empty_exists; invert_red; inversions Hs; eauto;
    econstructor; try eassumption;
    eapply renaming_fresh; eauto
  end.

Local Ltac item_inv' :=
  match goal with
  | [H : ty_stack ?G ?U _ _,
         H' : forall x : var, x \notin ?L -> ?G & x ~ ?T ⊢ open x ?u ∶ ?U,
         _ : ?x # ?S
     |- (exists G', ty_config _ (open ?x ?u ; _ ; ?S & ?x ~ ?v) _)] =>
    exists (x ~ T);
    try assert (x # G) by (eauto 3 using heap_correspond_notin_dom);
    pose proof (binds_push_eq x T G);
    pose proof (binds_push_eq x v S);
    try assert (ty_item_s (G & x ~ T) (S & x ~ v) x)
      by (try solve_ty_item_push; eauto using ty_item_s_push);
    try assert (heap_correspond (G & x ~ T) (S & x ~ v))
      by (eauto 3 using heap_correspond_push, heap_correspond_push_obj)
  end.

Lemma preservation_llit : forall L Gamma Sigma T s U T' l u c,
    inert Gamma ->
    heap_correspond Gamma Sigma ->
    ty_stack Gamma T' s U ->
    Gamma ⊢ l ∶ T ->
    (forall x, x \notin L -> Gamma & x ~ T ⊢ open x u ∶ T') ->
    trm_lit l u ; s ; Sigma ↦ c ->
    exists Gamma', ty_config (Gamma & Gamma') c U.
Proof.
  intros.
  invert_red; item_inv'; inversions H2;
    econstructor; eauto using renaming_push, inert_trm_obj_record_type,
                  heap_correspond_push_obj;
      unfold heap_correspond in *; destruct_ands;
        repeat_split_right; try solve [simpl_dom; congruence];
          eauto; intros; simpl_dom;
            match goal with
            | [ H : ?x \in \{ ?y} \u dom ?G |- _ ] =>
              rewrite in_union, in_singleton in H;
                destruct H; subst; eauto using ty_item_s_push
            end.
  - eapply ty_item_fun_s with (L:=L0); auto.
    intros. eapply weaken_rules; try reflexivity; auto.
Qed.

(** [s: G]                  #<br>#
    [inert [G]]             #<br>#
    [(s, t) |-> (s', t')]   #<br>#
    [G ⊢ t∶ T]              #<br>#
    [―――――――――――――――――――]   #<br>#
    [exists G', inert G']        #<br>#
    [s': G, G']             #<br>#
    [G, G' ⊢ t'∶ T]         *)
Lemma preservation_helper:
  forall Gamma c c' U,
    ty_config Gamma c U ->
    c ↦ c' ->
    exists Gamma', ty_config (Gamma & Gamma') c' U.
Proof.
  introv Htc Hred. gen c'.
  inversion Htc as [Gamma' s Sigma t T U' Hin Hst Hs Ht]; subst; clear Htc.
  induction Ht; intros; try solve [solve_var | invert_red; solve_val].
  - Case "ty_all_elim".
    invert_red. empty_exists. econstructor; eauto.
    destruct (canonical_forms_fun Hin Hst H) as
        [?L [?T [?t [?Bis [?Hsub ?Hty]]]]]; binds_eq.
    pick_fresh y.
    eapply (@renaming_typ G y); try eassumption; eauto.
  - Case "ty_rec_elim".
    invert_red. empty_exists. econstructor; eauto.
    pose proof (canonical_forms_obj Hin Hst H)
      as [?S [ds' [t' [Bis [Has Ty]]]]]; binds_eq.
    rewrite <- H2 in Has.
    rewrite* <- (defs_has_inv Has H6).
  - Case "ty_fld_asn".
    invert_red; empty_exists.
    econstructor; eauto 3 using heap_update_inert.
    pose proof (var_typ_rcd_to_binds Hin H)
      as [_ [?T [_ [_ [?H ?H]]]]]; eauto 3.
  - Case "ty_let".
    invert_red; empty_exists; eauto 3.
  - Case "ty_llit".
    eauto using preservation_llit.
  - Case "ty_sub".
    apply IHHt; eauto using ty_stack_sub.
Qed.

(** ** Preservation Theorem *)

(** [⊢ (s, t)∶ T]           #<br>#
    [(s, t) |-> (s', t')]   #<br>#
    [―――――――――――――――――――]   #<br>#
    [⊢ (s', t')∶ T]         *)
Theorem preservation : forall t s Sigma t' s' Sigma' T,
    ⊢ (t; s; Sigma) ∶ T ->
    (t; s; Sigma) ↦ (t'; s'; Sigma') ->
    ⊢ (t'; s'; Sigma') ∶ T.
Proof.
  introv Ht Hr. inversions Ht.
  lets Hp: (preservation_helper H Hr).
  destruct Hp as [Gamma' Htc].
  eauto.
Qed.

(** * Progress *)

(** Helper tactics for proving progress *)
Local Ltac solve_item_prog :=
  match goal with
    [Ht : ⊢ _ ; _ ; ?Sigma ∶ _ |- _ ] =>
    let x := fresh in
    right; pick_fresh_gen (dom Sigma) x; eauto
  end.

(** ** Progress Theorem *)
Theorem progress_var: forall x s Sigma T,
    ⊢ (trm_var (avar_f x); s; Sigma) ∶ T ->
    answer ((trm_var (avar_f x)); s; Sigma) \/
    exists t' s' Sigma', ((trm_var (avar_f x)); s; Sigma) ↦ (t'; s'; Sigma').
Proof.
  intros x. destruct s as [| f s]; intros; auto.
  right. destruct f; eauto.
Qed.
Local Hint Resolve progress_var : core.

(** [⊢ (s, t)∶ T]           #<br>#
    [(s, t) |-> (s', t')]   #<br>#
    [―――――――――――――――――――]   #<br>#
    [t] is in normal form   #<br>#
    or [exists s', t'] such that [(s, t) |-> (s', t')] *)
Theorem progress: forall t s Sigma T,
    ⊢ (t; s; Sigma) ∶ T ->
    answer (t; s; Sigma) \/
    exists t' s' Sigma', (t; s; Sigma) ↦ (t'; s'; Sigma').
Proof.
  introv Ht. inversion Ht as [Gamma c T' Htc]; subst.
  inversion Htc as [Gamma' s' Sigma' t' T' T'' Hin Hst Hts HT]; subst.
  induction HT; try solve [solve_item_prog]; eauto.
  - Case "ty_all_elim".
    pose proof (canonical_forms_fun Hin Hst H). destruct_all. right*.
  - Case "ty_new_elim".
    pose proof (canonical_forms_obj Hin Hst H). destruct_all. right*.
  - Case "ty_fld_asn".
    pose proof (heap_update_exists Hin Hst H H0) as [?s' ?H]. right*.
  - Case "ty_llit".
    destruct l;
      pick_fresh x; assert (x # Sigma) by auto;
        inversions H; right; eauto.
  - Case "ty_sub".
    apply IHHT; eauto using ty_stack_sub.
Qed.
