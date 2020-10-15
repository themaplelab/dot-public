Set Implicit Arguments.

Require Import DotTactics LibExtra.
Require Import AbstractSyntax Typing PreTyping.
Require Import GeneralTyping RecordTypes InertTypes DefRecordInertTyping PreciseTyping.
Require Import SubstitutionClass Substitution Weakening Narrowing BndIntro.

(** * Heap Correspondence *)

(** The operational semantics will be defined in terms of configurations
    consisting of a term [t], a stack [s], and a heap [Sigma].
    For typing a configuration, [heap_correspond] establishes a correspondence
    between the context [Gamma] and the heap [Sigma].

    We say that a context [Gamma] corresponds to a heap [Sigma] if
    - [G = {(xi mapsto Ti) | i = 1, ..., n}]
    - [Sigma = {(xi mapsto hi) | i = 1, ..., n}]
    - If [hi = l] is a literal then [G ⊢ l∶ Ti]
    - If [hi = nu(T)hds] is an object then [Ti = mu(... /\ D /\ ...)] and
      [G ⊢ hds^xi :: (... /\ D /\ ...)^xi].
 *)

(** ** Typing for heap definitions *)
(** We first define a typing relation for heap definitions. This closely mirrors
    the typing relation for definitions, but we have an additional case for
    non-null fields. *)
Inductive ty_heap_def : DecTyping heap_def :=
(** [G ⊢ {A = T}: {A: T..T}]   *)
| ty_heap_def_typ : forall Gamma A T,
    Gamma ⊢ heap_def_typ A T ∶d dec_typ A T T

(** [―――――――――――――――――――] #<br>#
    [G ⊢ {a = null}: {a: T .. T}] *)

(* A null def in a heap has any type *)
| ty_heap_def_trm_none : forall Gamma a T,
    Gamma ⊢ heap_def_trm a None ∶d dec_trm a T T

(** [G ⊢ x: T]            #<br>#
    [―――――――――――――――――――] #<br>#
    [G ⊢ {a = x}: {a: T .. T}] *)

| ty_heap_def_trm_some : forall Gamma a x T,
    Gamma ⊢ (trm_var (avar_f x)) ∶ T ->
    Gamma ⊢ heap_def_trm a (Some x) ∶d dec_trm a T T.
Existing Instance ty_heap_def.
Hint Constructors ty_heap_def : core.

(** *** Infrastructure for [ty_heap_def].  *)
Instance TyHeapDefDecTypingLabels : DecTypingLabels ty_heap_def.
Proof.
  hnf; induction 1; auto.
Qed.

Instance TyHeapDefDecTypingRecord : DecTypingRecord ty_heap_def.
Proof.
  hnf; induction 1; constructor.
Qed.

Instance HeapDefDecTypingBndIntroMiddle : PreTypingBndIntroMiddle (DecPreTyping ty_heap_def).
Proof.
  hnf. inversion 1; subst; auto using bnd_intro_middle.
Qed.

Local Hint Extern 2 => simple apply weaken_middle : core.

Instance HeapDefDecTypingWeakenMiddle :
  PreTypingWeakenMiddle (DecPreTyping ty_heap_def).
Proof.
  hnf; introv H. inversions H; auto.
Qed.

Instance HeapDefTySubstMiddle : DecTySubstMiddle ty_heap_def.
Proof.
  hnf; introv Hok Htyd; inversions Htyd; sympl; auto.
  intros; eapply ty_subst_middle in H; eauto.
Qed.

(** ** Strong Bindings for Locations *)

(** We first define a correspondence relation for a single location. This
    definition will later be lifted to entire contexts and heaps. *)

(** We say that a location [x] is strongly bound in the context [Gamma] and heap
    [Sigma], denoted [Gamma(x) ∼ Sigma(x)] if there exists a [T] such t
    - if [Sigma(x)] is a literal [l] then [Gamma ⊢ l ∶ T]
    - if [Sigma(x)] is an object [nu(y: U)ds] for some [U], then [T = mu(U)] and
      [Gamma ⊢ ds^x :: U^x]
    Notice that we only use literal typing and heap definition typing, and we do
    not need to invert any subtying at the outermost level when inverting strong
    bindings.
 *)

Inductive ty_item_s : ctx -> heap -> var -> Prop :=
| ty_item_lit_s : forall Gamma Sigma x l T,
    binds x T Gamma ->
    binds x (item_lit l) Sigma ->
    Gamma ⊢ l ∶ T ->
    ty_item_s Gamma Sigma x
| ty_item_obj_s : forall Gamma Sigma x U hds,
    binds x (typ_bnd U) Gamma ->
    binds x (item_obj U hds) Sigma ->
    Gamma ⊢ hds ∶ open x U ->
    ty_item_s Gamma Sigma x.
Hint Constructors ty_item_s : core.

Implicit Type (hds : heap_defs).

Ltac solve_ty_item_push :=
  match goal with
  | [H1: binds ?y ?T ?G,
         H2: binds ?y (item_lit ?l) ?s,
             H3 : ?G ⊢ ?l ∶ ?T |- ty_item_s _ _ ?y] =>
    eapply ty_item_lit_s; eauto 2;
    intros; eapply weaken; eauto
  | [H1: binds _ (item_obj _ _) _ |- _] =>
    eapply ty_item_obj_s; eauto 2;
    eapply weaken; eauto
  end.

(** A strongly bound location stays strongly bound in extended heaps and contexts *)
Lemma ty_item_s_push: forall G s x y T v,
    ty_item_s G s x ->
    y # G ->
    ty_item_s (G & y ~ T) (s & y ~ v) x.
Proof.
  intros.
  assert (x \notin \{ y }).
  { apply notin_singleton.
    intros ?H. subst x.
    inversions H; eauto using binds_fresh_inv. }
  destruct H; solve_ty_item_push.
Qed.

(** ** Heap Correspondence *)

(** [Gamma ∼ Sigma] if [Sigma] and [Gamma] have the same domain and every location in [Sigma] is
    strongly bound *)
Definition heap_correspond (G : ctx) (Sigma : heap) : Prop :=
  (dom G = dom Sigma) /\
  (forall x,
      x \in dom G ->
      ty_item_s G Sigma x).
Hint Unfold heap_correspond : core.

(** ** Simple lemmas for Heap Correspondence *)

(** [Gamma ∼ Sigma]       #<br>#
    [x ∉ dom(s)] #<br>#
    [――――――――――] #<br>#
    [x ∉ dom(G)] *)
Lemma heap_correspond_notin_dom: forall G s x,
    heap_correspond G s ->
    x # s ->
    x # G.
Proof.
  introv Hwt. destruct Hwt as [?Hdom ?].
  rewrite Hdom; auto.
Qed.

(** ** Inductive lemmas for Heap Correspondence *)

Lemma heap_correspond_empty:
    heap_correspond empty empty.
Proof.
  repeat split; auto.
  - simpl_dom; auto.
  - introv B. simpl_dom.
    rewrite in_empty in B.
    destruct B.
Qed.
Hint Resolve heap_correspond_empty : core.

Lemma heap_correspond_push: forall Gamma s y T v,
    heap_correspond Gamma s ->
    y # Gamma ->
    ty_item_s (Gamma & y ~ T) (s & y ~ v) y ->
    heap_correspond (Gamma & y ~ T) (s & y ~ v).
Proof.
  intros. unfold heap_correspond in *.
  destruct_all; repeat_split_right; auto.
  - rewrite ? dom_push; congruence.
  - intros. rewrite dom_push, in_union, in_singleton in *.
    destruct_all; subst; auto using ty_item_s_push.
Qed.

Lemma heap_correspond_push_obj: forall L Gamma s x T ds,
    heap_correspond Gamma s ->
    x # Gamma ->
    (forall x : var, x \notin L -> Gamma & x ~ open x T ⊢ open x ds ∶ open x T) ->
    x \notin fv ds ->
    heap_correspond (Gamma & x ~ typ_bnd T) (s & x ~ item_obj T (open x ds)).
Proof.
  intros.
  unfold heap_correspond in *.
  destruct_all; repeat_split_right; auto.
  + simpl_dom. fequal. auto.
  + intros x0 Hd.
    pose proof (dom_to_binds Hd) as [?T ?]; clear Hd.
    assert (binds x (item_obj T (open x ds)) (s & x ~ (item_obj T (open x ds)))) by auto.
    destruct (binds_push_inv H4) as [[? ?] | [? ?]]; subst.
    * apply (ty_item_obj_s H4 H5); auto.
      apply bnd_intro.
      apply (renaming_open_push (L:=L)); auto.
    * apply ty_item_s_push; eauto using binds_to_dom.
Qed.

(** ** Inversion lemmas for [Gamma ∼ Sigma] *)

(** [Gamma ∼ Sigma] implies every location is strongly typed *)

(** [Gamma ∼ Sigma]              #<br>#
    [G(l) = T]          #<br>#
    [―――――――――――――]     #<br>#
    [s(l):G(l)]         *)
Lemma corresponding_types: forall G s x T,
    heap_correspond G s ->
    binds x T G ->
    ty_item_s G s x.
Proof.
  intros. unfold heap_correspond in H.
  destruct_all.
  eauto using binds_to_dom.
Qed.

(** [Gamma ∼ Sigma]              #<br>#
    [Sigma(l) = v]          #<br>#
    [―――――――――――――]     #<br>#
    [Sigma(l):G(l)]         *)
Lemma corresponding_types_s: forall G s x v,
    heap_correspond G s ->
    binds x v s ->
    ty_item_s G s x.
Proof.
  intros. unfold heap_correspond in H.
  destruct_all.
  apply H1. rewrite H.
  eauto using binds_to_dom.
Qed.

Lemma heap_defs_same_typ : forall ds Gamma T,
    Gamma ⊢ ds ∶ T ->
    Gamma ⊢ (heap_defs_of_defs ds) ∶ T.
Proof with eauto.
  induction ds.
  - inversion 1.
  - introv ds_typ.
    inversions ds_typ.
    + simpl. constructor. inversions H3; simpl...
    + simpl. apply ty_defs_cons...
      * inversions H3; simpl...
      * inversions H3; simpl in *;
          apply ds_labels_hasnt_hds_labels_hasnt...
Qed.

Lemma not_free_in_ds_hds : forall (ds : defs) (x : var),
    x \notin fv ds ->
    x \notin fv (heap_defs_of_defs ds).
Proof with eauto.
  induction ds; intros...
  simpl in *. repeat(rewrite notin_union in H); destruct_all.
  rewrite notin_union. split...
  destruct a...
Qed.
