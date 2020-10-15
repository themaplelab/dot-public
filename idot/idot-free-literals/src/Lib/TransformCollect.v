(** remove printing ~ *)

Set Implicit Arguments.

Require Import Coq.Bool.Bool.
Require Import LibExtra SyntaxClasses.

Generalizable Variables A B.


(* ************************************************************************** *)
(** ** Collecting *)
(** Many operations on a syntax class involves collecting information about
    all instances of a sub-syntax. *)
Class Collect `(AS : AbstractSyntax B) `(AS': AbstractSyntax A) :=
  collect : forall {C : Type}, C -> (B -> C) -> (C -> C -> C) -> A -> C.
Arguments collect _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ !_ /.

Class ListLikeCollect `{ASB : AbstractSyntax B} `{ASA: AbstractSyntax A}
      {C: Set} `{ASC: AbstractSyntax C} {TL: ToList C A}
      (CBC: Collect ASB ASC) (CBA: Collect ASB ASA) :=
  collect_fold_right_map : forall (C' : Type) (df : C') f comb (a : A),
    collect df f comb a =
    List.fold_right comb df (List.map (collect df f comb) (to_list a)).

(** Sanity for Collect *)
Class CollectCompose `(C: Collect B A) :=
  collect_compose :
    forall {C D} (f : C -> D) g comb1 comb2 i,
      (forall x y, f (comb1 x y) = comb2 (f x) (f y)) ->
      f ∘ (collect i g comb1) = collect (f i) (f ∘ g) comb2.

Class CollectReflect `(C: Collect B A) :=
  collect_reflect : forall P p,
    (forall b, (P b) <-> (p b) = true) ->
    forall {bl} a,
      ((collect (Is_true bl) P or a) <-> (collect bl p orb a) = true).


(** Lifting Syntax Operations *)
Class FvCollect `(Collect) :=
  fv_collect : fv = collect (\{}) fv (@union var).

Section AboutCollectCompose.
  Context `{C: Collect B A}.

  Context {CC: CollectCompose C}.
  Lemma collect_compose_same :
      forall {C} (f : C -> C) g comb i,
        (forall x y, f (comb x y) = comb (f x) (f y)) ->
               f ∘ (collect i g comb) = collect (f i) (f ∘ g) comb.
  Proof using CC.
    auto using collect_compose.
  Qed.

  Lemma collect_compose_negb_orb : forall b f,
    negb ∘ (collect b f orb) = collect (negb b) (negb ∘ f) andb.
  Proof using CC.
    intros. apply collect_compose.
    apply negb_orb.
  Qed.

  Lemma in_collect : forall x a,
      (x \in collect \{} fv (union (A:=var)) a) =
      collect (x \in \{}) (fun b => x \in fv b) or a.
  Proof using CC.
    intros.
    remember (fun s => x \in s) as ff.
    assert (H': forall y z, ff (y \u z) = (ff y \/ ff z)).
    { intros. rewrite Heqff. apply in_union. }
    rewrite (fold_compose ff).
    rewrite (collect_compose ff fv (@union var) or \{}); auto.
  Qed.

  Lemma notin_collect : forall x a,
      (x \notin collect \{} fv (union (A:=var)) a) =
      collect (x \notin \{}) (fun b => x \notin fv b) and a.
  Proof using CC.
    intros.
    remember (fun s => x \notin s) as ff.
    assert (H': forall y z, ff (y \u z) = (ff y /\ ff z)).
    { intros. apply prop_ext. rewrite Heqff. apply notin_union. }
    rewrite (fold_compose ff).
    rewrite (collect_compose ff fv (@union var) and \{}); auto.
  Qed.

End AboutCollectCompose.


(* ************************************************************************** *)
(** ** Transforming *)
(** Many operations on a syntax class involves transforming sub-syntaxes. *)
Class Transform `(AS : AbstractSyntax B) `(AS': AbstractSyntax A) :=
  transform : (B -> nat -> B) -> A -> nat -> A.
Arguments transform _ _ _ _ _ _ _ _ _ _ _ _ !_ /.

Class ListLikeTransform `{ASB : AbstractSyntax B} `{ASA: AbstractSyntax A}
      {C: Set} `{ASC: AbstractSyntax C}
      {TL: ToList C A} {FL: OfList C A} {LL: ListLike TL FL}
      (TBC: Transform ASB ASC) (TBA: Transform ASB ASA) :=
  transform_map_f : forall f n a,
    transform f a n = map_f (fun c => transform f c n) a.

(** Sanity for Transform *)
Class TransformId `(T: Transform B A) :=
  transform_id : forall x n,
    transform (ignore_second id) x n = x.

Class TransformCompose `(T: Transform B A) :=
  transform_compose : forall f g,
    (transform f) ∘∘ (transform g) = transform (f ∘∘ g).

(** Lifting Syntax Operations *)
Class OpenTransform `(Transform) :=
  open_transform : forall n x,
    (open_depth_rec n x) = transform (open_depth_rec n x).

Class SubstTransform `(Transform) :=
  subst_transform : forall x y,
    (ignore_second (subst_var x y)) = transform (ignore_second (subst_var x y)).


(* ************************************************************************** *)
(** ** Links Between Syntax, Collect and Transform *)
Class CollectTransform
      `{ASB : AbstractSyntax B} `{ASA : AbstractSyntax A}
      (C : Collect ASB ASA) (T : Transform ASB ASA) :=
  collect_transform: forall bl p a f g,
    (collect bl p andb a) = true ->
    transform (dec_apply p f g) a = transform f a.


(* ************************************************************************** *)
(** ** Transformed Syntax Lemmas *)
Section AboutTransformSyntax.
  Context `{OA: Openable A} {FA: FreeVar A} {SA: SubstVar A}.
  Context `{OB: Openable B} {FB: FreeVar B} {SB: SubstVar B}.
  Context {ASB: AbstractSyntax OB FB SB} {ASA: AbstractSyntax OA FA SA}.
  Context {C: Collect ASB ASA} {CC: CollectCompose C} {CR: CollectReflect C}
          {FC: FvCollect C}.
  Context {T: Transform ASB ASA} {TI: TransformId T} {TC: TransformCompose T}
          {OT: OpenTransform T} {ST: SubstTransform T}.
  Context {CT: CollectTransform C T}.

  Section List.
    (** We can lift Collect and Transform to Lists *)
    Definition collect_list : Collect ASB (ListAbstractSyntax (A:=A)) :=
      fun (C : Type) (df : C) f comb as' =>
        (List.fold_right (fun a acc => comb (collect df f comb a) acc) df) as'.
    Definition transform_list : Transform ASB (ListAbstractSyntax (A:=A)) :=
      (fun f as' n => List.map (fun a => transform f a n) as').
    Instance ListCollect : Collect ASB (ListAbstractSyntax (A:=A)) :=
      collect_list.
    Instance ListTransform : Transform ASB (ListAbstractSyntax (A:=A)) :=
      transform_list.

    Instance ListCollectCompose : CollectCompose ListCollect.
    Proof using CC.
      hnf. intros. unfold "∘".
      apply fun_ext_dep. intros as'.
      induction as'; simpl; auto.
      change (ListCollect (f i) (fun x : B => f (g x)) comb2 as')
        with (collect (f i) (fun x : B => f (g x)) comb2 as').
      change (ListCollect i g comb1 as') with
          (collect i g comb1 as').
      rewrite <- IHas'. rewrite H.
      f_equal. rewrite ? (fold_compose f).
      rewrite (collect_compose (C:=C) f g comb1 comb2); auto.
    Qed.

    Ltac foldLC :=
      change ListCollect with
          (@collect B OB FB SB ASB (list A) (@ListOpenable A OA)
                    (@ListFreeVar A FA) (@ListSubstVar A SA)
                    (@ListAbstractSyntax A OA FA SA) ListCollect).

    Instance ListCollectReflect : CollectReflect ListCollect.
    Proof using CR.
      hnf. intros.
      induction a; simpl; auto using Is_true_iff_eq_true.
      foldLC.
      rewrite collect_reflect, IHa by auto.
      symmetry; auto using orb_true_iff.
    Qed.

    Instance ListFvCollect : FvCollect ListCollect.
    Proof using FC.
      hnf. apply fun_ext_dep; intros as'.
      induction as'; simpl; auto.
      foldLC; f_equal; auto.
      rewrite <- fv_collect; auto.
    Qed.

    Ltac foldLT :=
      change ListTransform
      with (@transform B OB FB SB ASB (list A) (@ListOpenable A OA)
                       (@ListFreeVar A FA) (@ListSubstVar A SA)
                       (@ListAbstractSyntax A OA FA SA)
                       ListTransform).

    Instance ListTransformId : TransformId ListTransform.
    Proof using TI.
      hnf. intros as'; induction as'; intros; simpl; auto; foldLT.
      rewrite transform_id, IHas'. reflexivity.
    Qed.

    Instance ListTransformCompose : TransformCompose ListTransform.
    Proof using TC.
      hnf. intros f g. unfold "∘∘".
      intros_fun_ext. induction x; simpl; auto.
      foldLT. rewrite <- IHx.
      rewrite (fold_compose12 (transform f)), transform_compose.
      unfold "∘∘". congruence.
    Qed.

    Instance ListOpenTransform : OpenTransform ListTransform.
    Proof using OT.
      hnf. intros n x. apply fun_ext_dep; intros as'.
      induction as'; apply fun_ext_dep; intros; simpl;
        foldLT; auto. rewrite <- IHas'.
      rewrite <- open_transform. unfold open_depth_rec, open_rec.
      auto.
    Qed.

    Instance ListSubstTransform : SubstTransform ListTransform.
    Proof using ST.
      hnf. intros x y. apply fun_ext_dep; intros as'.
      induction as'; apply fun_ext_dep; intros; simpl;
        foldLT; auto. rewrite <- IHas', <- subst_transform.
      unfold ignore_second; simpl. unfold subst_var.
      auto.
    Qed.

    Instance ListCollectTransform : CollectTransform ListCollect ListTransform.
    Proof using CT.
      hnf. intros.
      induction a; apply fun_ext_dep; intros n; simpl; foldLT; auto.
      change (collect bl p andb (a :: a0)%list = true) with
          (collect bl p andb a && collect bl p andb a0 = true) in H.
      apply andb_prop in H. destruct H.
      erewrite collect_transform, IHa by eauto. auto.
    Qed.
  End List.

  (** Every TransformSyntax leads to OpenCompose *)
  Section OpenCompose.
    Context {OTA: OpenTwice OB}.
    Instance TransformOpenTwice : OpenTwice OA.
    Proof using OT OTA TC.
      hnf.
      intros. unfold compose.
      apply fun_ext_dep. intros a.
      rewrite ? open_eq_open_depth.
      rewrite (open_transform n x). rewrite (open_transform n y).
      rewrite fold_compose12. rewrite transform_compose.
      rewrite open_depth_twice.
      auto.
    Qed.

    Context {OTC: OpenCommut OB}.
    Instance TransformOpenCommut : OpenCommut OA.
    Proof using OT OTC TC.
      hnf.
      intros.
      apply fun_ext_dep. intros a.
      unfold compose. rewrite ? open_eq_open_depth.
      rewrite ? (open_transform m x). rewrite ? (open_transform n y).
      rewrite ? fold_compose12. rewrite ? transform_compose.
      rewrite open_depth_commut; auto.
    Qed.
  End OpenCompose.

  (** Every TransformSyntax leads to SubstOpenCommut *)
  Section SubstOpenCommut.
    Context {SF: SubstOpenCommut ASB}.

    Instance TransformSubstOpenCommut : SubstOpenCommut ASA.
    Proof using OT SF ST TC.
      hnf. intros.
      rewrite ? open_eq_open_depth, ? (subst_depth 0).
      rewrite ? subst_transform.
      rewrite (open_transform n z), (open_transform n (z \[ x -> y])).
      rewrite ? fold_compose12. rewrite ? transform_compose.
      rewrite subst_open_commut_depth. auto.
    Qed.
  End SubstOpenCommut.

  (** ListLike transform leads to length preserving opening *)
  Section ListLike.
    Context {SC: Set}.
    Context `{ASSC: AbstractSyntax SC}.
    Context {CSC: Collect ASB ASSC}.
    Context {CCSC: CollectCompose CSC} {CRSC: CollectReflect CSC}
            {FCSC: FvCollect CSC}.
    Context {TSC: Transform ASB ASSC}.
    Context {TISC: TransformId TSC} {TCSC: TransformCompose TSC}
            {OTSC: OpenTransform TSC} {STSC: SubstTransform TSC}.
    Context {TCSSC: CollectTransform CSC TSC}.
    Context {TL: ToList SC A} {FL: OfList SC A} {LL: ListLike TL FL}.

    Section ListLikeCollect.
      Context {LLC: ListLikeCollect CSC C}.

      Lemma fv_one : forall c,
          fv (of_list (c :: nil)) = fv c.
      Proof using FC FCSC LL LLC.
        intros. rewrite fv_collect.
        rewrite collect_fold_right_map.
        rewrite <- fv_collect. rewrite of_list_to_list.
        simpl. auto.
      Qed.

      Lemma fv_rev : forall a,
          fv a = fv (of_list (List.rev (to_list a))).
      Proof using FC LL LLC.
        intros.
        assert (H': a = (of_list (to_list a)))
          by (symmetry; apply to_list_of_list).
        rewrite H' at 1; clear H'.
        rewrite fv_collect. rewrite ? collect_fold_right_map, ? of_list_to_list.
        rewrite List.map_rev. rewrite List.fold_left_rev_right.
        symmetry.
        assert (H': forall A, (fun (x y : fset A) => y \u x) = (fun x y => x \u y))
          by (intros; intros_fun_ext; apply union_comm); rewrite H'; clear H'.
        apply List.fold_symmetric; auto.
      Qed.

      Lemma fv_app_union : forall xs ys,
          fv (of_list xs ++ of_list ys)
          = fv (of_list xs) \u fv (of_list ys).
      Proof using FC FCSC LL LLC.
        intros. induction xs.
        + rewrite fv_collect, collect_fold_right_map.
          unfold app_s. rewrite ? of_list_to_list. unfold List.app.
          rewrite <- (of_list_to_list ys), <- collect_fold_right_map at 1.
          rewrite <- union_empty_l at 1. f_equal.
          rewrite collect_fold_right_map, of_list_to_list. auto.
        + unfold app_s. rewrite ? of_list_to_list.
          rewrite <- List.app_comm_cons.
          rewrite ? fv_collect, ? collect_fold_right_map, 2 of_list_to_list.
          simpl. rewrite <- union_assoc.
          rewrite <- (of_list_to_list (xs ++ ys)), <- (of_list_to_list xs).
          rewrite <- ? collect_fold_right_map, <- ? fv_collect, of_list_to_list.
          rewrite of_list_app. rewrite IHxs. auto.
      Qed.

      Lemma fv_env_singles_forward : forall ys a,
          length ys = length (to_list a) ->
          fv_env (ys ~* to_list a) = fv a.
      Proof using FC FCSC LLC.
        intros.
        assert (R: fv a
                   = collect \{} fv (@union var) a)
          by (rewrite fv_collect; auto); rewrite R; clear R.
        rewrite fv_collect. rewrite collect_fold_right_map.
        unfold fv_in_values. rewrite liblist_fold_right.
        rewrite values_singles;
          rewrite ? liblist_length; auto.
        clear H2. induction (to_list a); simpl; auto.
        rewrite IHl; auto.
      Qed.

      Lemma fv_env_singles : forall ys a,
          length ys = length_s a ->
          fv_env (ys ~** to_list a) = fv a.
      Proof using FC FCSC LL LLC.
        unfold length_s. intros.
        rewrite fv_rev.
        assert (R: (List.rev (to_list a))
                   = (to_list (of_list (List.rev (to_list a)))))
          by (rewrite of_list_to_list; auto); rewrite R.
        rewrite fv_env_singles_forward
          by (rewrite of_list_to_list, ? List.rev_length; auto).
        rewrite to_list_of_list; auto.
      Qed.
    End ListLikeCollect.

    Section ListLikeTransform.
      Context {LLT: ListLikeTransform TSC T}.

      Lemma transform_length_s :
        forall f n a, length_s (transform f a n) = length_s a.
      Proof using LLT.
        intros. rewrite transform_map_f. unfold length_s, map_f.
        rewrite of_list_to_list. rewrite List.map_length; auto.
      Qed.

      Lemma length_s_open :
        forall n x a, length_s (open_rec n x a) = length_s a.
      Proof using LLT OT.
        intros. rewrite open_eq_open_depth, open_transform.
        rewrite transform_length_s; auto.
      Qed.

      Lemma length_s_subst :
        forall x y a, length_s (subst_var x y a) = length_s a.
      Proof using LLT ST.
        intros. rewrite (subst_depth 0), subst_transform, transform_length_s.
        auto.
      Qed.

      Lemma subst_map_f : forall x y a,
          subst_var x y a = map_f (subst_var x y) a.
      Proof using LLT ST STSC.
        intros. rewrite (subst_depth 0), subst_transform, transform_map_f.
        rewrite <- subst_transform. auto.
      Qed.

      Lemma subst_singles_to_list : forall x y ys a,
          length ys = length_s a ->
          (ys ~* to_list (subst_var x y a)) = subst_env x y (ys ~* to_list a).
      Proof using LLT ST STSC.
        intros. rewrite map_singles. rewrite liblist_map.
        rewrite subst_map_f. unfold map_f. rewrite of_list_to_list; auto.
        rewrite liblist_length; auto.
      Qed.

      Lemma subst_singles_rev_to_list : forall x y ys a,
          length ys = length_s a ->
          (ys ~** to_list (subst_var x y a)) = subst_env x y (ys ~** to_list a).
      Proof using LLT ST STSC.
        intros. rewrite subst_map_f. rewrite map_singles, liblist_map.
        rewrite List.map_rev. unfold map_f. rewrite of_list_to_list; auto.
        rewrite liblist_length; auto.
      Qed.
    End ListLikeTransform.
  End ListLike.

  (** Every TransformSyntax leads to a DecideFv and Closing *)
  Section DecideFvClosing.
    Context {DFv: DecideFv ASB}.
    Context {DFvS: ReflectFv DFv}.

    Instance CollectDecideFv : DecideFv ASA :=
      (fun x => collect false (fun a => dec_fv x a) orb).

    Instance CollectReflectFv : ReflectFv CollectDecideFv.
    Proof using CC CR DFvS FC.
      hnf. unfold dec_notin_fv, dec_fv, CollectDecideFv. simpl.
      rewrite fv_collect.
      intros. rewrite in_collect.
      assert (x \in \{} = (Bool.Is_true false)) by (auto using in_empty).
      rewrite H. apply collect_reflect.
      auto using reflect_fv.
    Qed.

    Lemma notin_fv_collect : forall x a,
        x \notin fv a ->
        collect (negb false) (dec_notin_fv x) andb a = true.
    Proof using CC CR DFvS FC.
      intros x a H.
      pose proof ((reflect_fv x a)) as [H1 H2].
      assert (H3: negb (dec_fv x a) = true) by (destruct (dec_fv x a); auto).
      unfold dec_fv, CollectDecideFv in H3; simpl in H3.
      rewrite (fold_compose negb) in H3.
      rewrite collect_compose_negb_orb in H3.
      auto.
    Qed.

    Section SubstFresh.
      Context {SI: SubstitutionInner DFvS}.
      Context {SF: SubstFresh ASB}.

      Instance TransformSubstFresh : SubstFresh ASA.
      Proof using CC CR CT FC SI ST TI.
        hnf. intros.
        apply notin_fv_collect in H.
        rewrite (subst_depth 0), subst_transform.
        rewrite subst_inner.
        rewrite (collect_transform _ _ _ _ _ H).
        apply transform_id.
      Qed.
    End SubstFresh.

    Section Closing.
      Context {Cl: Closing ASB}.
      Context {OC: OpenClose Cl} {CO: CloseOpen Cl} {SOC: SubstOpenClose Cl}.

      Instance TransformClosing : Closing ASA :=
        (fun n x a => transform (close_depth_rec n x) a 0).

      Instance TransformOpenClose : OpenClose TransformClosing.
      Proof using OC OT TC.
        hnf.
        unfold close_rec, TransformClosing. simpl. intros.
        apply fun_ext_dep. intros a.
        unfold compose. rewrite ? open_eq_open_depth.
        rewrite open_transform. rewrite fold_compose12.
        rewrite transform_compose. rewrite open_depth_close_depth.
        auto.
      Qed.

      Instance TransformCloseOpen : CloseOpen TransformClosing.
      Proof using CO OT TC.
        hnf.
        unfold close_rec, TransformClosing. simpl. intros.
        apply fun_ext_dep. intros a.
        unfold compose. rewrite ? open_eq_open_depth.
        rewrite open_transform. rewrite fold_compose12.
        rewrite transform_compose. rewrite close_depth_open_depth.
        auto.
      Qed.

      Instance TransformSubstOpenClose : SubstOpenClose TransformClosing.
      Proof using OT SOC ST TC.
        hnf.
        unfold close_rec, TransformClosing. simpl. intros.
        apply fun_ext_dep. intros a.
        unfold compose. rewrite ? (subst_depth 0), ? open_eq_open_depth.
        rewrite (subst_transform x y).
        rewrite (open_transform n x), (open_transform n y).
        rewrite ? fold_compose12. rewrite ? transform_compose.
        rewrite subst_open_close_depth. auto.
      Qed.

      Section CloseUnbound.
        Context {CU: CloseUnbound Cl}.
        Context {CI: ClosingInner DFvS Cl}.

        Instance TransformCloseUnbound : CloseUnbound TransformClosing.
        Proof using CC CI CR CT FC TI.
          hnf.
          simpl. intros.
          apply notin_fv_collect in H.
          unfold close_rec, TransformClosing; simpl.
          rewrite close_inner.
          rewrite (collect_transform _ _ _ _ _ H).
          apply transform_id.
        Qed.

      End CloseUnbound.
    End Closing.

  End DecideFvClosing.

End AboutTransformSyntax.

Existing Instances
         ListCollect ListTransform
         ListCollectCompose ListCollectReflect ListFvCollect
         ListTransformId ListTransformCompose
         ListOpenTransform ListSubstTransform
         ListCollectTransform | 1.
Arguments ListCollect _ _ _ _ _ _ _ _ _ _ _ _ /.
Arguments ListTransform _ _ _ _ _ _ _ _ _ _ _ _ /.

Existing Instances
         TransformOpenTwice
         TransformOpenCommut
         TransformSubstOpenCommut
         CollectDecideFv
         CollectReflectFv
         TransformSubstFresh
         TransformClosing
         TransformOpenClose
         TransformCloseOpen
         TransformSubstOpenClose
         TransformCloseUnbound | 2.
