Set Implicit Arguments.

Require Import Coq.Program.Equality.
Require Import DotTactics LibExtra.
Require Import
        AbstractSyntax GeneralTyping
        PreciseTyping Substitution Weakening Narrowing.

(** * Heap Correspondence *)

(** The operational semantics will be defined in terms of configurations
    consisting of a term [t], a stack [s], and a heap [Sigma].
    For typing a configuration, [heap_correspond] establishes a correspondence
    between the context [Gamma] and the heap [Sigma].

    We say that a context [Gamma] corresponds to a heap [Sigma] if
    - [G = {(xi mapsto Ti) | i = 1, ..., n}]
    - [s = {(xi mapsto vi) | i = 1, ..., n}]
    - If [vi] is a function then [G ⊢ vi∶ Ti]
    - If [vi = nu(T)ds] is an object then [Ti = mu(... /\ D /\ ...)] and
      [G ⊢ ds^xi :: (... /\ D /\ ...)^xi].
 *)

(** ** Strong Bindings for Locations *)

(** We first define a correspondence relation for a single location. This
    definition will later be lifted to entire contexts and heaps. *)

(** We say that a location [l] is strongly bound in the context [G] and heap
    [Sigma], denoted [s(l):G(l)] if there exists a [T] such t
    - if [s(x)] is a function [lambda(y: T)t] then [G ⊢ lambda(y∶ T)t ∶ T]
    - if [s(x)] is an object [nu(y: U)ds] for some [U], then [T = mu(U)] and
      [G ⊢ ds^x :: U^x] *)

Inductive ty_item_s : ctx -> heap -> var -> Prop :=
| ty_item_fun_s : forall G s x S t L T,
    binds x (typ_all S T) G ->
    binds x (item_fun S t) s ->
    (forall x, x \notin L ->
      G & x ~ S ⊢ open x t ∶ open x T) ->
    ty_item_s G s x
| ty_item_obj_s : forall G s x U ds T,
    binds x T G ->
    binds x (item_obj U (open x ds)) s ->
    T = typ_bnd U ->
    G ⊢ open x ds ∶ open x U ->
    ty_item_s G s x.
Hint Constructors ty_item_s : core.

Ltac solve_ty_item_push :=
  match goal with
  | [H1: binds ?y (typ_all ?S ?T) _,
         H2: binds ?y (item_fun ?S ?t) ?s,
             H3 : forall x : var, x \notin ?L -> _ & x ~ ?S ⊢ open x ?t ∶ open x ?T
                             |- ty_item_s _ _ ?y] =>
    eapply ty_item_fun_s with (L:=L); eauto 2;
    intros; eapply weaken_rules; eauto
  | [H1: binds _ (item_obj _ _) _ |- _] =>
    eapply ty_item_obj_s; eauto using weaken_ty_defs
  end.

(** A strongly bound location stays strongly bound in extended heaps and contexts *)
Lemma ty_item_s_push: forall G s x y T v,
    ty_item_s G s x ->
    ok G ->
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

(** [s:G] if [s] and [G] have the same domain and every location in [s] is
    strongly bound *)
Definition heap_correspond (G : ctx) (s : heap) : Prop :=
  ok G /\
  ok s /\
  (dom G = dom s) /\
  (forall x,
      x \in dom G ->
      ty_item_s G s x).
Hint Unfold heap_correspond : core.

(** ** Simple lemmas for Heap Correspondence *)

(** If [s: G], the variables in the domain of [s] are distinct. *)
Lemma heap_correspond_to_ok_G: forall s G,
    heap_correspond G s -> ok G.
Proof.
  intros. destruct H as [? [? ?]]. auto.
Qed.
Hint Resolve heap_correspond_to_ok_G : core.

Lemma heap_correspond_to_ok_s: forall s G,
    heap_correspond G s -> ok s.
Proof.
  intros. destruct H as [? [? ?]]. auto.
Qed.
Hint Resolve heap_correspond_to_ok_s : core.

(** [s: G]       #<br>#
    [x ∉ dom(s)] #<br>#
    [――――――――――] #<br>#
    [x ∉ dom(G)] *)
Lemma heap_correspond_notin_dom: forall G s x,
    heap_correspond G s ->
    x # s ->
    x # G.
Proof.
  introv Hwt. destruct Hwt as [? [? [?Hdom ?]]].
  unfold notin. rewrite Hdom.
  auto.
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

Lemma heap_correspond_push: forall G s y T v,
    heap_correspond G s ->
    y # G ->
    ty_item_s (G & y ~ T) (s & y ~ v) y ->
    heap_correspond (G & y ~ T) (s & y ~ v).
Proof.
  intros. unfold heap_correspond in *.
  destruct_all; repeat_split_right; auto.
  - simpl_dom; rewrite H3; auto.
  - intros. rewrite dom_push, in_union, in_singleton in H5.
    destruct_all; subst; auto using ty_item_s_push.
Qed.

Lemma heap_correspond_push_obj: forall L G s x T ds,
    heap_correspond G s ->
    x # G ->
    (forall x : var, x \notin L -> G & x ~ open x T ⊢ open x ds ∶ open x T) ->
    x \notin fv ds ->
    heap_correspond (G & x ~ typ_bnd T) (s & x ~ item_obj T (open x ds)).
Proof.
  intros.
  unfold heap_correspond in *.
  destruct_all; repeat_split_right; auto.
  + simpl_dom. fequal. auto.
  + intros x0 Hd.
    pose proof (dom_to_binds Hd) as [?T ?]; clear Hd.
    assert (binds x (item_obj T (open x ds)) (s & x ~ (item_obj T (open x ds)))) by auto.
    destruct (binds_push_inv H6) as [[? ?] | [? ?]]; subst.
    * apply (ty_item_obj_s _ H6 H7); auto.
      pick_fresh z.
      apply (@renaming_def _ _ z); auto.
      -- rewrite fv_env_push; sympl; auto.
      -- eapply (proj54 weaken_rules); auto.
    * apply ty_item_s_push; eauto using binds_to_dom.
Qed.

(** ** Inversion lemmas for [s:G] *)

(** [s:G] implies every location is strongly typed *)

(** [s: G]              #<br>#
    [G(l) = T]          #<br>#
    [―――――――――――――]     #<br>#
    [s(l):G(l)]         *)
Lemma corresponding_types: forall G s x T,
    heap_correspond G s ->
    binds x T G ->
    ty_item_s G s x.
Proof.
  intros. unfold heap_correspond in H.
  destruct_all. apply H3.
  eauto using binds_to_dom.
Qed.

(** [s: G]              #<br>#
    [s(l) = v]          #<br>#
    [―――――――――――――]     #<br>#
    [s(l):G(l)]         *)
Lemma corresponding_types_s: forall G s x v,
    heap_correspond G s ->
    binds x v s ->
    ty_item_s G s x.
Proof.
  intros. unfold heap_correspond in H.
  destruct_all. apply H3.
  rewrite H2. eauto using binds_to_dom.
Qed.
