Set Implicit Arguments.

Require Import List LibExtra DotTactics.
Require Import
        AbstractSyntax PreTyping Typing GeneralTyping
        InertTightSubtyping
        GeneralToTight TightTyping InvertibleTyping
        RecordAndInertTypes PreciseTyping
        OperationalSemantics
        SubstitutionClass Substitution RenameConstructors
        EffectSubstitution InitSubstitution InitRenaming
        Weakening
        HeapCorrespondence CanonicalForms
        HeapUpdate HeapUpdateCorrespondence
        InertGeneralSubtyping Subenvironments Narrowing
        StackTyping ConfigTyping.
Require Import Effects InitVar InitTyping InitWeakening
        HeapCommit HeapItemFree SubHeapFree
        InitCorrespondence.

Implicit Types (Gamma : ctx) (Delta : init_ctx) (Sigma : heap) (ℰ : eff_ctx).

Lemma progress_var: forall Gamma Delta ℰs Es x s Sigma T,
    ty_config Gamma Delta ℰs Es (trm_var (avar_f x); s; Sigma) T ->
    answer ((trm_var (avar_f x)); s; Sigma) \/
    exists s' Sigma' t', ((trm_var (avar_f x)); s; Sigma) ↦ (t'; s'; Sigma').
Proof.
  intros Gamma Delta ℰs Es x. destruct s as [| f s]; intros; auto.
  right. destruct f; eauto.
Qed.
Local Hint Resolve progress_var : core.

Lemma progress_read: forall Gamma Delta ℰs Es x a s Sigma T,
    ty_config Gamma Delta ℰs Es (trm_sel (avar_f x) a; s; Sigma) T ->
    exists t', (trm_sel (avar_f x) a; s; Sigma) ↦ (t'; s; Sigma).
Proof.
  inversion 1
    as [?Gamma ?Delta ?Sigma ?ℰ ?ℰs ?s ?t ?T ?i ?U ?effs' ?effs ?effss
         ?Hin ?HinD ?Hhc ?Hfshs ?Hts ?Hty ?Hef ?Hit ?Hecc]; subst.
  remember (trm_sel (avar_f x) a) as t eqn:Htrm.
  induction Hty; inversions Htrm;
    eauto using ty_stack_sub; try clear IHHty.

  inversions Hit. rename H1 into HinitSel.
  inversions HinitSel. rename H4 into HinitObj.
  inversions HinitObj. rename H4 into HbixD.
  destruct (free_sub_heaps_well_committed Hfshs)
    as [HdomEqGD [HdomEqDS Hchi]].
  pose proof (canonical_forms_obj Hin Hhc H0)
    as [? [hds [HbixS Hcases]]].
  pose proof (Hchi _ _ HbixD HbixS) as Hcho.
  inversions Hcho. rename H4 into Hchds.
  destruct Hcases as [Contra| [y [Hhas Hty]]];
    [exfalso;
     eauto using committed_heap_defs_labels_has_None_inv
    | eauto].
Qed.

Lemma progress_write: forall Gamma Delta ℰs Es x y m s Sigma T,
    ty_config Gamma Delta ℰs Es (trm_asn (avar_f x) m (avar_f y); s; Sigma) T ->
    exists Sigma' t',
      (trm_asn (avar_f x) m (avar_f y); s; Sigma) ↦ (t'; s; Sigma').
Proof with eauto.
  inversion 1
    as [?Gamma ?Delta ?Sigma ?ℰ ?ℰs ?s ?t ?T ?i ?U ?effs' ?effs ?effss
         ?Hin ?HinD ?Hhc ?Hfshs ?Hts ?Hty ?Hef ?Hit ?Hecc]; subst.

  remember (trm_asn (avar_f x) m (avar_f y)) as t eqn:Htrm.
  induction Hty; inversions Htrm;
    eauto using ty_stack_sub; try(clear IHHty); try(clear IHHty0).
  rename H0 into Htypx. rename H1 into Htypy.

  pose proof (heap_update_exists Hin Hhc Htypx Htypy) as [Sigma' Hupd]...
Qed.

Lemma progress_app: forall Gamma Delta ℰs effss f x s Sigma U,
    ty_config Gamma Delta ℰs effss
              (trm_app (avar_f f) (avar_f x); s; Sigma) U ->
    exists t', (trm_app (avar_f f) (avar_f x); s; Sigma) ↦ (t'; s; Sigma).
Proof with eauto.
  inversion 1
    as [?Gamma ?Delta ?Sigma ?ℰ ?ℰs ?s ?t ?T ?i ?U ?effs' ?effs ?effss
         ?Hin ?HinD ?Hhc ?Hfshs ?Hts ?Hty ?Hef ?Hit ?Hecc]; subst.
  remember (trm_app (avar_f f) (avar_f x)) as t eqn:Htrm.
  induction Hty; inversions Htrm;
    eauto using ty_stack_sub; try(clear IHHty); try(clear IHHty0).

  rename H0 into Htyf.

  pose proof (canonical_forms_fun Hin Hhc Htyf).
  destruct_all; eauto.
Qed.

Lemma progress_let_lit: forall Gamma Delta ℰs effss T l t s Sigma U,
    ty_config Gamma Delta ℰs effss (trm_lit T l t; s; Sigma) U ->
    exists s' Sigma' t', (trm_lit T l t; s; Sigma) ↦ (t'; s'; Sigma').
Proof with eauto.
  inversion 1
    as [?Gamma ?Delta ?Sigma ?ℰ ?ℰs ?s ?t ?T ?i ?U ?effs' ?effs ?effss
         ?Hin ?HinD ?Hhc ?Hfshs ?Hts ?Hty ?Hef ?Hit ?Hecc]; subst.
  pick_fresh_gen (dom Sigma) x...
Qed.

Lemma progress_con: forall Gamma Delta ℰs effss k avs s Sigma U,
    ty_config Gamma Delta ℰs effss (trm_new (avar_f k) avs; s; Sigma) U ->
    exists s' Sigma' t', (trm_new (avar_f k) avs; s; Sigma) ↦ (t'; s'; Sigma').
Proof with eauto.
  inversion 1
    as [?Gamma ?Delta ?Sigma ?ℰ ?ℰs ?s ?t ?T ?i ?U ?effs' ?effs ?effss
         ?Hin ?HinD ?Hhc ?Hfshs ?Hts ?Hty ?Hef ?Hit ?Hecc]; subst.
  remember (trm_new (avar_f k) avs) as t eqn:Htrm.
  induction Hty; inversions Htrm;
    eauto using ty_stack_sub; try clear IHHty.

  rename H0 into Htyk. rename H2 into Hvavs. rename H1 into Htyavs.
  rename xs into ys.

  pose proof (length_ty_avars Htyavs) as HlenaT.
  pose proof (length_vars_of_avars Hvavs) as Hlenya.
  assert (Hlen : length ys = length_s Ts) by congruence.

  pose proof (canonical_forms_con Hin Hhc Htyk) as [_ [?ds [?t [_ [?B _]]]]].
  pick_fresh_gen (dom Sigma \u fv (open_rec_vars 1 ys ds)) x.
  exists (frame_ret x :: s)%list. eexists. exists (open_vars (cons x ys) t).
  econstructor; eauto; auto.
Qed.

Lemma progress: forall Gamma Delta ℰs Es t s Sigma T,
    ty_config Gamma Delta ℰs Es (t ; s; Sigma) T ->
    answer (t; s; Sigma) \/
    exists s' Sigma' t', (t; s; Sigma) ↦ (t'; s'; Sigma').
Proof.
  inversion 1
    as [?Gamma ?Delta ?Sigma ?ℰ ?ℰs ?s ?t ?T ?i ?U ?effs' ?effs ?effss
         ?Hin ?HinD ?Hhc ?Hfshs ?Hts ?Hty ?Hef ?Hit ?Hecc]; subst.
  induction Hty; eauto using ty_stack_sub; try clear IHHty.
  - (* Function application *)
    eauto using progress_app.
  - (* Constructor application *)
    eauto using progress_con.
  - (* Field Read *)
    eauto using progress_read.
  - (* Assignment *)
    eauto using progress_write.
  - (* Literal allocation *)
    eauto using progress_let_lit.
Qed.
