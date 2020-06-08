(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import LibExtra.

Generalizable Variables A B.

Declare Scope syntax_scope.
Delimit Scope syntax_scope with S.
Open Scope syntax_scope.

(* ************************************************************************** *)
(** * Type Classes for Syntax *)

(** The proof represents variables using the locally nameless representation
    which combines De Bruijn indices and named variables. So any syntax comes
    with the following functions:
    - [open_rec] to replace bound variables (represented by De Bruijn indices)
      with a named variable
    - [fv] to gather the free variables
    - [subst_var] to substitute all instances of a named variable with another
      one
*)
Class Openable (A : Set) := open_rec : nat -> var -> A -> A.
Class FreeVar (A : Set) := fv : A -> vars.
Class SubstVar (A : Set) := subst_var : var -> var -> A -> A.
Bind Scope syntax_scope with Openable FreeVar SubstVar.
Arguments open_rec _ _ _ _ !_ /.
Arguments fv _ _ !_ /.
Arguments subst_var _ _ _ _ !_ /.

Class AbstractSyntax (A : Set) `(Openable A) `(FreeVar A) `(SubstVar A).

(** We introduce some notation to prettify our proof *)
Notation "z '/[' x '->' y ']'"
  := (subst_var x y z) (x at level 69, at level 70) : syntax_scope.

Notation subst_vars := (vars_zip_map subst_var).
Notation "z '/[' xs '-->' ys ']'"
  := (subst_vars xs ys z) (xs at level 69, at level 70) : syntax_scope.

(** We often only replace the outer most De Bruijn index, so we add some special
    syntax for it *)
Notation open := (open_rec 0).

(** We often open syntax at a certain depth *)
Definition open_depth_rec `{AS : Openable A} n x a d
  := open_rec (n + d) x a.
Notation open_depth := (open_depth_rec 0).
Arguments open_depth_rec _ _ _ _ !_ _ /.

(** Closedness *)
Definition closed `{AS: Openable A} a
  := forall n x, open_rec n x a = a.

(** It's also useful to open with a list of variables *)
Fixpoint open_rec_vars `{AS : Openable A} (k: nat) (ys: list var) (X: A): A :=
  match ys with
  | nil => X
  | cons y ys => open_rec_vars (S k) ys (open_rec k y X)
  end.
Notation open_vars := (open_rec_vars 0).
Arguments open_rec_vars _ _ _ !_ _ /.


(* ************************************************************************** *)
(** ** Decide Free Variables *)
(** Deciding whether a variables is free or not is not required for typing
    definitions, but it is are needed to lift certain lemmas between different
    Syntax Classes
    - [dec_fv x a] returns true if x is in [fv a] and false otherwise
 *)
Class DecideFv `(AS: AbstractSyntax A) := dec_fv : var -> A -> bool.
Arguments dec_fv _ _ _ _ _ _ _ !_ /.

Definition dec_notin_fv `{DFv: DecideFv A} x a := negb (dec_fv x a).
Arguments dec_notin_fv _ _ _ _ _ _ _ !_ /.

Class ReflectFv `(DFv: DecideFv A) :=
  reflect_fv : forall x a,
    (x \in fv a) <-> (dec_fv x a) = true.

(* ************************************************************************** *)
(** ** Closing *)
(** Closing is not required for typing definitions, but they are needed to lift
    certain lemmas between different Syntax Classes
    - [close_rec] replaces all instances of a variable with a unnamed free
      variable
 *)
Class Closing `(AS: AbstractSyntax A) :=
  close_rec : nat -> var -> A -> A.

Bind Scope syntax_scope with Closing.
Notation close := (close_rec 0).
Arguments close_rec _ _ _ _ _ _ _ _ !_ /.

Definition close_depth_rec `{Cl : Closing A} n x a d
  := close_rec (n + d) x a.
Notation close_depth := (close_depth_rec 0).
Arguments close_depth_rec _ _ _ _ _ _ _ _ !_ /.


(* ************************************************************************** *)
(** ** Labels *)

(** The Proof is parameterized over different representations of typ and term
    labels *)
Parameter typ_label: Set.
Parameter trm_label: Set.

(** *** Term and type members
        Type member labels ([A], [B], [C]) and term (field) member labels ([a],
        [b], [c]).  *)
Inductive label: Set :=
| label_typ: typ_label -> label
| label_trm: trm_label -> label.

(** Some syntax will contain labels *)
Class LabelOf (A : Set) := label_of : A -> label.
Arguments label_of _ _ !_ /.


(* ************************************************************************** *)
(** ** Syntax Lemmas *)

(** Composing Opens *)
Class OpenTwice `(AS: Openable A) :=
  open_twice : forall n x y,
    (open_rec n y) ∘ (open_rec n x) = (open_rec n x).
Class OpenCommut `(AS: Openable A) :=
    open_commut : forall m n x y,
        m <> n ->
        (open_rec m x) ∘ (open_rec n y) = (open_rec n y) ∘ (open_rec m x).

Class SubstFresh `(AS : AbstractSyntax A) :=
  subst_fresh : forall x y X,
    x \notin fv X -> subst_var x y X = X.

Class SubstOpenCommut `(AS : AbstractSyntax A) :=
  subst_open_commut : forall x y z X n,
    subst_var x y (open_rec n z X)
    = open_rec n (z \[x -> y]) (subst_var x y X).

Class FvOpenCases `(AS : AbstractSyntax A) :=
  fv_open_cases : forall x a n,
    fv (open_rec n x a) = fv a \/
    fv (open_rec n x a) = \{ x} \u fv a.

(** Sanity check for opening and closing *)
Class OpenClose `(Cl: Closing A) :=
  open_close : forall n x,
    (open_rec n x) ∘ (close_rec n x) = open_rec n x.
Class CloseOpen `(Cl: Closing A) :=
  close_open : forall n x,
    (close_rec n x) ∘ (open_rec n x) = close_rec n x.
Class SubstOpenClose `(Cl: Closing A) :=
  subst_open_close : forall n x y,
    (subst_var x y) ∘ (open_rec n x) = (open_rec n y) ∘ (close_rec n x).

Class CloseUnbound `(Cl: Closing) :=
  close_unbound : forall x a n,
    x \notin fv a ->
    close_rec n x a = a.

Class OpenInjective `(AS : AbstractSyntax) :=
  open_fresh_injective : forall (X Y : A) k z,
    z \notin fv X ->
    z \notin fv Y ->
    open_rec k z X = open_rec k z Y ->
    X = Y.

Class SubstIntro `(AS : AbstractSyntax) :=
  subst_intro : forall x y n X,
    x \notin (fv X) ->
    open_rec n y X = subst_var x y (open_rec n x X).

(** *** For some Syntax classes, operations are decision procedures on [fv] *)
Class ClosingInner
      `{AS: AbstractSyntax A}
      {DFv: DecideFv AS} (DFvS: ReflectFv DFv)
      (C: Closing AS) :=
  close_inner : forall n x,
    close_depth_rec n x
    = (dec_apply (dec_notin_fv x) (ignore_second id) (close_depth_rec n x)).

Class SubstitutionInner
      `{AS: AbstractSyntax A}
      {DFv: DecideFv AS} (DFvS: ReflectFv DFv) :=
  subst_inner : forall {B : Type} x y,
    (ignore_second (B:=B) (subst_var x y))
    = (dec_apply (dec_notin_fv x) (ignore_second id) (ignore_second (subst_var x y))).


(* ************************************************************************** *)
(** ** List-Like Syntax *)
(** To better use some of Coq's built-in features for generating induction
    schemes for mutually recursive structures we will often define specialized
    versions of list. In the following typeclass we think of [A] being a list
    containing [B]s. *)

Class ToList (B A : Set) :=
  to_list : A -> list B.
Arguments to_list _ _ _ !_ /.

Class OfList (B A : Set) :=
  of_list : list B -> A.
Arguments of_list _ _ _ !_ /.

Class ListLike {B A : Set} `(ToList B A) `(OfList B A) :=
  { to_list_of_list : forall x, (of_list (to_list x)) = x;
    of_list_to_list : forall l, (to_list (of_list l)) = l;
  }.
Bind Scope syntax_scope with ToList OfList.


(* ************************************************************************** *)
(** ** Syntax Environments *)
(** Free variables in the range (types) of a context *)
Notation fv_env := (fv_in_values fv).
Notation subst_env x y := (map (subst_var x y)).
Notation subst_env_vars xs ys := (map (subst_vars xs ys)).

(* ************************************************************************** *)
(** ** Extra Definitions and Simple Lemmas *)
Section Open_depth.
  Context `{AS: AbstractSyntax A}.
  Lemma open_eq_open_depth : forall n x a,
      open_rec n x a = open_depth_rec n x a 0.
  Proof.
    intros.
    unfold open_depth_rec.
    rewrite Nat.add_0_r.
    auto.
  Qed.
End Open_depth.

Section Subst_depth.
  Context `{AS: AbstractSyntax A}.
  Lemma subst_depth: forall {x y} (n : nat) (a : A),
    subst_var x y a = (ignore_second (subst_var x y)) a n.
  Proof. auto. Qed.
End Subst_depth.

Section Close_depth.
  Context `{AS: AbstractSyntax A} {Cl: Closing AS}.
  Lemma close_eq_close_depth : forall n x a,
      close_rec n x a = close_depth_rec n x a 0.
  Proof.
    intros.
    unfold close_depth_rec.
    rewrite Nat.add_0_r.
    auto.
  Qed.
End Close_depth.

Section Fv_env.
  Context `{AS: AbstractSyntax A}.

  Lemma fv_env_single: forall x a,
    fv_env (x ~ a) = fv a.
  Proof.
    intros. unfold fv_in_values.
    rewrite single_def, values_def.
    rewrite liblist_fold_right, liblist_map.
    simpl. rewrite union_empty_r. auto.
  Qed.

  Lemma fv_env_push: forall E x a,
      fv_env (E & x ~ a) = fv_env E \u fv a.
  Proof.
    intros. rewrite fv_in_values_cons.
    rewrite fv_env_single. auto.
  Qed.
End Fv_env.

Section Subst_env.
  Context `{AS: AbstractSyntax A}.

  Lemma subst_single: forall x y z a,
    z ~ subst_var x y a = subst_env x y (z ~ a).
  Proof.
    intros. rewrite map_single; auto.
  Qed.
End Subst_env.

Section About_OpenTwice.
  Context `{OpenTwice}.

  Lemma open_depth_twice : forall n x y,
      (open_depth_rec n y) ∘∘ (open_depth_rec n x) = (open_depth_rec n x).
  Proof.
    intros.
    apply fun_ext_dep. intros a.
    apply fun_ext_dep. intros m.
    unfold compose12, open_depth_rec.
    rewrite (fold_compose (open_rec _ _)), open_twice.
    auto.
  Qed.
End About_OpenTwice.

Section About_OpenCommut.
  Context `{OpenCommut}.

  Lemma open_depth_commut : forall m n x y,
      m <> n ->
      (open_depth_rec m x) ∘∘ (open_depth_rec n y)
      = (open_depth_rec n y) ∘∘ (open_depth_rec m x).
  Proof.
    intros.
    unfold open_depth. rewrite lift_depth_commute12; auto.
    intros. apply open_commut.
    rewrite Nat.add_cancel_r; auto.
  Qed.

  Lemma open_rec_vars_open_rec_commut : forall x xs n m a,
      n < m \/ (length xs + m) < S n ->
      (open_rec_vars m xs (open_rec n x a))
      = open_rec n x (open_rec_vars m xs a).
  Proof.
    intros x. induction xs; simpl; intros.
    - auto.
    - rewrite <- IHxs; try Coq.omega.Omega.omega.
      fequal. rewrite (fold_compose (open_rec _ _)).
      rewrite open_commut; auto; Coq.omega.Omega.omega.
  Qed.

  Lemma open_vars_S_commut : forall x xs n a,
      (open_rec_vars (S n) xs (open_rec n x a))
      = open_rec n x (open_rec_vars (S n) xs a).
  Proof.
    intros. apply open_rec_vars_open_rec_commut.
    Coq.omega.Omega.omega.
  Qed.

  Lemma open_vars_app : forall xs ys n a,
      open_rec_vars n (xs ++ ys) a =
      open_rec_vars n xs (open_rec_vars (n + length xs) ys a).
  Proof.
    induction xs; simpl; intros.
    - rewrite Nat.add_0_r; auto.
    - rewrite IHxs. rewrite open_rec_vars_open_rec_commut by Coq.omega.Omega.omega.
      rewrite Nat.add_succ_comm; auto.
  Qed.
End About_OpenCommut.

Section About_SubstFresh.
  Context `{SubstFresh A}.

  Lemma subst_fresh_ctx: forall x y G,
    x \notin fv_env G -> subst_env x y G = G.
  Proof.
    intros x y G. induction G using env_ind; intros.
    - rewrite map_empty; auto.
    - rewrite fv_env_push, notin_union in H3.
      rewrite map_concat. destruct H3. rewrite IHG by auto.
      rewrite map_single. rewrite subst_fresh by auto.
      auto.
  Qed.

End About_SubstFresh.

Section About_SubstOpenCommut.
  Context `{SubstOpenCommut}.

  Lemma subst_open_commut_depth : forall n x y z,
      (ignore_second (subst_var x y)) ∘∘ (open_depth_rec n z) =
      open_depth_rec n (z \[x -> y]) ∘∘ (ignore_second (subst_var x y)).
  Proof.
    intros.
    apply fun_ext_dep. intros a.
    apply fun_ext_dep. intros m.
    unfold compose12, open_depth, ignore_second.
    rewrite subst_open_commut; auto.
  Qed.

  Lemma subst_open_rec_vars_commut : forall x y ys t n,
    subst_var x y (open_rec_vars n ys t)
    = open_rec_vars n (List.map (subst_fvar x y) ys) (subst_var x y t).
  Proof.
    intros x y ys. induction ys.
    - auto.
    - intros. simpl. rewrite IHys. rewrite subst_open_commut.
      auto.
  Qed.

  Lemma subst_open_vars_commut_fresh_length: forall x y ys a n,
      (fresh \{ x } (length ys) ys) ->
      subst_var x y (open_rec_vars n ys a)
      = open_rec_vars n ys (subst_var x y a).
  Proof.
    intros. rewrite subst_open_rec_vars_commut.
    rewrite fresh_vars_map; auto.
  Qed.
End About_SubstOpenCommut.

Section About_FvOpenCases.
  Context `{FvOpenCases}.
  Lemma notin_open_rec_vars : forall x ys T n,
    x \notin fv T ->
    fresh (\{ x} \u (fv T)) (length ys) ys ->
    x \notin fv (open_rec_vars n ys T).
  Proof.
    induction ys; intros; simpls; auto.
    assert (H' : fv (open_rec n a T) = fv T \/
                 fv (open_rec n a T) = \{ a} \u fv T)
      by auto using fv_open_cases. destruct H4.
    apply IHys; destruct H' as [H' | H']; rewrite H'; auto.
  Qed.

  Lemma notin_open_rec_vars_list : forall x ys T n,
    x \notin fv T ->
    x \notin from_list ys ->
    x \notin fv (open_rec_vars n ys T).
  Proof.
    intros x ys.
    induction ys; intros; simpls; auto.
    rewrite from_list_cons in H4.
    apply IHys; auto.
    assert (H' : fv (open_rec n a T) = fv T \/
                 fv (open_rec n a T) = \{ a} \u fv T)
      by auto using fv_open_cases.
    destruct H' as [H' | H']; rewrite H'; auto.
  Qed.
End About_FvOpenCases.

Section About_ClosingSanity.
  Section OpenClose.
    Context `{OpenClose}.

  Lemma open_depth_close_depth : forall n x,
      (open_depth_rec n x ∘∘ close_depth_rec n x) = open_depth_rec n x.
  Proof.
    intros.
    apply fun_ext_dep. intros a.
    apply fun_ext_dep. intros m.
    unfold open_depth, close_depth, compose12.
    rewrite (fold_compose (open_rec _ _)).
    rewrite open_close.
    auto.
  Qed.
  End OpenClose.

  Section CloseOpen.
    Context `{CloseOpen}.
    Lemma close_depth_open_depth : forall n x,
        (close_depth_rec n x ∘∘ open_depth_rec n x) = close_depth_rec n x.
    Proof.
      intros.
      apply fun_ext_dep. intros a.
      apply fun_ext_dep. intros m.
      unfold open_depth, close_depth, compose12.
      rewrite (fold_compose (close_rec _ _)).
      rewrite close_open.
      auto.
    Qed.
  End CloseOpen.

  Section SubstOpenClose.
    Context `{SubstOpenClose}.
    Lemma subst_open_close_depth : forall n x y,
      (ignore_second (subst_var x y)) ∘∘ (open_depth_rec n x)
      = (open_depth_rec n y) ∘∘ (close_depth_rec n x).
    Proof.
      intros.
      apply fun_ext_dep. intros a.
      apply fun_ext_dep. intros m.
      unfold open_depth, close_depth, ignore_second, compose12.
      rewrite (fold_compose (subst_var _ _)).
      rewrite (subst_open_close (n + m) x y).
      auto.
    Qed.
  End SubstOpenClose.
End About_ClosingSanity.

Section About_ListLike.
  Context `{ListLike B A}.

  Definition app_s xs ys := of_list ((to_list xs) ++ (to_list ys)).

  Infix "++" := app_s (right associativity, at level 60).

  Lemma app_s_assoc : forall xs ys zs,
      xs ++ ys ++ zs = (xs ++ ys) ++ zs.
  Proof.
    intros. unfold app_s. rewrite ? of_list_to_list.
    apply f_equal. rewrite List.app_assoc.
    auto.
  Qed.

  Definition map_f f x := of_list (List.map f (to_list x)).

  Lemma map_f_app_s : forall xs ys f,
      map_f f (xs ++ ys) = (map_f f xs) ++ (map_f f ys).
  Proof.
    intros. unfold app_s, map_f. rewrite ? of_list_to_list.
    apply f_equal. rewrite List.map_app.
    auto.
  Qed.

  Definition length_s xs := length (to_list xs).

  Lemma app_s_length_s : forall xs ys,
      length_s (xs ++ ys) = length_s xs + length_s ys.
  Proof.
    intros. unfold length_s, app_s. rewrite ? of_list_to_list.
    rewrite List.app_length; auto.
  Qed.

  Lemma singles_map_to_list : forall f ys a,
      length ys = length_s a ->
      ys ~* (to_list (map_f f a)) = map f (ys ~* to_list a).
  Proof.
    intros. rewrite map_singles.
    - rewrite liblist_map.
      unfold map_f;rewrite of_list_to_list.
      auto.
    - rewrite liblist_length. auto.
  Qed.

  Lemma singles_rev_map_to_list : forall f ys a,
      length ys = length_s a ->
      ys ~** (to_list (map_f f a)) = map f (ys ~** to_list a).
  Proof.
    intros. rewrite map_singles.
    - rewrite liblist_map. rewrite List.map_rev.
      unfold map_f; rewrite of_list_to_list; auto.
    - rewrite liblist_length. rewrite ? List.rev_length.
      auto.
  Qed.

  Lemma of_list_app : forall xs ys,
      of_list (xs ++ ys) = (of_list xs) ++ (of_list ys).
  Proof.
    intros. unfold app_s.
    rewrite ? of_list_to_list; auto.
  Qed.

  Lemma listlike_rev_ind : forall (P : A -> Prop),
       P (of_list nil) ->
       (forall (b : B) (a : A),
           P a ->
           P (a ++ (of_list (b :: nil)))) ->
       forall a : A, P a.
  Proof.
    intros. rewrite <- to_list_of_list.
    induction (to_list a) using List.rev_ind; auto.
    rewrite of_list_app; auto.
  Qed.

End About_ListLike.

Infix "++" := app_s (right associativity, at level 60) : syntax_scope.
Arguments app_s _ _ _ _ _ !_ /.
Arguments length_s _ _ _ !_ /.


(* ************************************************************************** *)
(** ** Typeclass Implications *)
Section About_CloseUnbound.
  Context `{AS: AbstractSyntax A}.
  Context {C: Closing AS}.
  Context {CU: CloseUnbound C}.
  Context {CO: CloseOpen C}.

  (** Every CloseUnbound leads to a OpenInjective *)
  Instance CloseUnboundOpenInjective : OpenInjective AS.
  Proof.
    hnf. intros.
    apply (f_equal (close_rec k z)) in H4.
    rewrite ? (fold_compose (close_rec _ _)) in H4.
    rewrite close_open in H4.
    rewrite (close_unbound _ _ H3), (close_unbound _ _ H2) in H4.
    auto.
  Qed.

  Context {SOC: SubstOpenClose C}.
  Instance CloseUnboundSubstIntro : SubstIntro AS.
  Proof.
    hnf. intros. rewrite (fold_compose (subst_var x y)).
    rewrite subst_open_close. unfold compose.
    apply f_equal. symmetry. auto using close_unbound.
  Qed.
End About_CloseUnbound.
Existing Instances
         CloseUnboundOpenInjective
         CloseUnboundSubstIntro.

(** *** List of Syntax *)
Section ListOfSyntax.
  Context {A: Set}.
  Context {O: Openable A}.
  Context {F: FreeVar A}.
  Context {S: SubstVar A}.
  Context {AS: AbstractSyntax O F S}.

  Lemma list_map_compose : forall {A B C : Type} (f : A -> B) (g : B -> C),
      List.map g ∘ List.map f = List.map (g ∘ f).
  Proof.
    intros. unfold compose.
    apply fun_ext_dep; intros xs.
    rewrite List.map_map; auto.
  Qed.

  Instance ListOpenable : Openable (list A) :=
    (fun n x => List.map (open_rec n x)).
  Instance ListFreeVar : FreeVar (list A) :=
    (List.fold_right (fun a acc => union (fv a) acc) \{}).
  Instance ListSubstVar : SubstVar (list A) :=
    (fun x y => List.map (subst_var x y)).

  Instance ListAbstractSyntax : AbstractSyntax ListOpenable ListFreeVar ListSubstVar := {}.

  Section OpenCompose.
    Context {OT: OpenTwice O}.

    Instance ListOpenTwice : OpenTwice ListOpenable.
    Proof.
      hnf. unfold open_rec, ListOpenable; cbn.
      intros; rewrite list_map_compose.
      rewrite open_twice; auto.
    Qed.

    Context {OC: OpenCommut O}.
    Instance ListOpenCommut : OpenCommut ListOpenable.
    Proof.
      hnf; unfold open_rec, ListOpenable; simpl.
      intros; rewrite ? list_map_compose.
      rewrite open_commut by auto; auto.
    Qed.
  End OpenCompose.

  Section SubstFresh.
    Context {SF: SubstFresh AS}.


    Instance ListSubstFresh : SubstFresh ListAbstractSyntax.
    Proof.
      unfold SubstFresh. induction X; intros.
      - simpl; auto.
      - cbn in *. rewrite notin_union in H.
        destruct H. apply IHX in H0. rewrite H0.
        rewrite subst_fresh; auto.
    Qed.
  End SubstFresh.

  Section SubstOpenCommut.
    Context {SF: SubstOpenCommut AS}.

    Instance ListSubstOpenCommut : SubstOpenCommut ListAbstractSyntax.
    Proof.
      hnf; intros.
      unfold open_rec, subst_var; simpl.
      induction X; auto.
      simpl. rewrite subst_open_commut.
      f_equal; auto.
    Qed.
  End SubstOpenCommut.

  Section FvOpenCases.
    Context {FOC: FvOpenCases AS}.

    Instance ListFvOpenCases : FvOpenCases ListAbstractSyntax.
    Proof.
      hnf; intros x a n. induction a; auto.
      intros; simpl. apply union_eq_cases; auto using fv_open_cases.
    Qed.
  End FvOpenCases.

  Section Closing.
    Context {C: Closing AS}.

    Instance ListClosing : Closing ListAbstractSyntax :=
      (fun n x => List.map (close_rec n x)).

    Local Ltac lift_closing lem :=
      hnf;
      unfold open_rec, close_rec, subst_var,
      ListOpenable, ListClosing, ListSubstVar;
      simpl; intros;
      rewrite ? list_map_compose, lem; auto.

    Context {OC: OpenClose C}.
    Instance ListOpenClose : OpenClose ListClosing.
    Proof.
      hnf;
      unfold open_rec, close_rec, subst_var; simpl; intros;
      lift_closing open_close.
    Qed.

    Context {CO: CloseOpen C}.
    Instance ListCloseOpen : CloseOpen ListClosing.
    Proof.
      lift_closing close_open.
    Qed.

    Context {SOC: SubstOpenClose C}.
    Instance ListSubstOpenClose : SubstOpenClose ListClosing.
    Proof.
      lift_closing subst_open_close.
    Qed.

    Context {CU: CloseUnbound C}.

    Instance ListCloseUnbound : CloseUnbound ListClosing.
    Proof.
      hnf; intros. unfold close_rec; simpl.
      induction a; auto.
      simpl in H. apply notin_union in H. destruct H.
      simpl. rewrite close_unbound by auto.
      rewrite IHa by auto. auto.
    Qed.

    (** From above, this implies OpenInjective and SubstIntro *)
  End Closing.
End ListOfSyntax.
Existing Instances
         ListOpenable
         ListFreeVar
         ListSubstVar
         ListAbstractSyntax
         ListOpenTwice
         ListOpenCommut
         ListSubstFresh
         ListSubstOpenCommut
         ListClosing
         ListOpenClose
         ListCloseOpen
         ListSubstOpenClose
         ListCloseUnbound.

(* ************************************************************************** *)
(** ** Tactics *)
Ltac unfold_syntax :=
  unfold open_depth_rec, close_depth_rec,
  open_rec, fv, subst_var, close_rec, dec_fv;
  simpls.
