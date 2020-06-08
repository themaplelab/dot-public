(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra DotTactics.

(** * Abstract Syntax *)

Require Export SyntaxClasses TransformCollect Vars Types Terms AbstractMachine.

(** Helper functions to retrieve labels of declarations and definitions *)
Fixpoint get_def(l: label)(ds: defs): option def :=
match ds with
| defs_nil => None
| defs_cons ds' d => If label_of d = l then Some d else get_def l ds'
end.

Definition defs_has(ds: defs)(d: def) := get_def (label_of d) ds = Some d.

Definition defs_hasnt(ds: defs)(l: label) := get_def l ds = None.

(** Substitution preserves labels of definitions: [label(d) = label(d[y/x])] *)
Lemma subst_label_of_def: forall x y (d : def),
  label_of d = label_of (subst_var x y d).
Proof.
  intros. destruct d; reflexivity.
Qed.

(** [l \notin labels(ds)]     #<br>#
    [――――――――――――――――――――――] #<br>#
    [l \notin labels(ds[y/x]] *)
Lemma subst_defs_hasnt: forall x y l ds,
  defs_hasnt ds l ->
  defs_hasnt (subst_var x y ds) l.
Proof.
  intros x y l ds. unfold defs_hasnt. induction ds; introv Eq.
  - reflexivity.
  - unfold get_def. simpl. rewrite <- subst_label_of_def.
    simpl in Eq. case_if~.
Qed.

(** Typing environment ([Gamma]) *)
Notation ctx := (env typ).

Inductive lit_item_fun : item -> lit -> Prop :=
  | lit_item_fun_c : forall T t,
    lit_item_fun (item_fun T t) (lit_fun T t).

Inductive lit_item_obj : item -> lit -> Prop :=
  | lit_item_obj_c : forall T ds,
    lit_item_obj (item_obj T ds) (lit_obj T ds).

Hint Constructors lit_item_obj lit_item_fun : core.

(** ** Tactics *)

(** Tactics for avars *)
Ltac fold_var_abs :=
  repeat match goal with
  | |- context [(AvarOpenable ?x)] =>
    change (AvarOpenable x) with (@open_rec avar AvarOpenable x)
  | |- context [(AvarFreeVar ?x)] =>
    change (AvarFreeVar x) with (@fv avar AvarFreeVar x)
  | |- context [(AvarSubstVar ?x)] =>
    change (AvarSubstVar x) with (@subst_var avar AvarSubstVar x)
  end.

Tactic Notation "fold_var_abs" "in" hyp(H) :=
  repeat match type of H with
  | context [(AvarOpenable ?x)] =>
    change (AvarOpenable x) with (@open_rec avar AvarOpenable x) in H
  | context [(AvarFreeVar ?x)] =>
    change (AvarFreeVar x) with (@fv avar AvarFreeVar x) in H
  | context [(AvarSubstVar ?x)] =>
    change (AvarSubstVar x) with (@subst_var avar AvarSubstVar x) in H
  end.

Tactic Notation "fold_var_abs" "in" "*" :=
  repeat match goal with
  | [H : context [(AvarOpenable ?x)] |- _] =>
    change (AvarOpenable x) with (@open_rec avar AvarOpenable x) in *
  | |- context [(AvarOpenable ?x)] =>
    change (AvarOpenable x) with (@open_rec avar AvarOpenable x) in *
  | [H : context [(AvarFreeVar ?x)] |- _] =>
    change (AvarFreeVar x) with (@fv avar AvarFreeVar x) in *
  | |- context [(AvarFreeVar ?x)] =>
    change (AvarFreeVar x) with (@fv avar AvarFreeVar x) in *
  | [H : context [(AvarSubstVar ?x)] |- _] =>
    change (AvarSubstVar x) with (@subst_var avar AvarSubstVar x) in *
  | |- context [(AvarSubstVar ?x)] =>
    change (AvarSubstVar x) with (@subst_var avar AvarSubstVar x) in *
  | [H : context [(@ListOpenable avar AvarOpenable ?x)] |- _] =>
    change (@ListOpenable avar AvarOpenable ?x) with
        (@open_rec (list avar) (@ListOpenable avar AvarOpenable) x) in *
  | |- context [(@ListOpenable avar AvarOpenable ?x)] =>
    change (@ListOpenable avar AvarOpenable ?x) with
        (@open_rec (list avar) (@ListOpenable avar AvarOpenable) x) in *
  | [H : context [(@ListFreeVar avar AvarFreeVar ?x)] |- _] =>
    change (@ListFreeVar avar AvarFreeVar ?x) with
        (@fv (list avar) (@ListFreeVar avar AvarFreeVar) x) in *
  | |- context [(@ListFreeVar avar AvarFreeVar ?x)] =>
    change (@ListFreeVar avar AvarFreeVar ?x) with
        (@fv (list avar) (@ListFreeVar avar AvarFreeVar) x) in *
  | [H : context [(@ListSubstVar avar AvarSubstVar ?x)] |- _] =>
    change (@ListSubstVar avar AvarSubstVar ?x) with
        (@subst_var (list avar) (@ListSubstVar avar AvarSubstVar) x) in *
  | |- context [(@ListSubstVar avar AvarSubstVar ?x)] =>
    change (@ListSubstVar avar AvarSubstVar ?x) with
        (@subst_var (list avar) (@ListSubstVar avar AvarSubstVar) x) in *
  end.

(** Tactics for Types *)
Tactic Notation "fold_typ_abs" "in" hyp(H) :=
  change (open_rec_dec) with (@open_rec dec DecOpenable) in H;
  change (open_rec_typ) with (@open_rec typ TypOpenable) in H;
  change (fv_dec) with (@fv dec DecFreeVar) in H;
  change (fv_typ) with (@fv typ TypFreeVar) in H;
  change (subst_dec) with (@subst_var dec DecSubstVar) in H;
  change (subst_typ) with (@subst_var typ TypSubstVar) in H.

Tactic Notation "fold_typ_abs" "in" "*" :=
  change (open_rec_dec) with (@open_rec dec DecOpenable) in *;
  change (open_rec_typ) with (@open_rec typ TypOpenable) in *;
  change (fv_dec) with (@fv dec DecFreeVar) in *;
  change (fv_typ) with (@fv typ TypFreeVar) in *;
  change (subst_dec) with (@subst_var dec DecSubstVar) in *;
  change (subst_typ) with (@subst_var typ TypSubstVar) in *.

(** Tactics for Terms *)
Tactic Notation "fold_trm_abs" "in" hyp(H) :=
  change (open_rec_trm) with (@open_rec trm TrmOpenable) in H;
  change (open_rec_lit) with (@open_rec lit LitOpenable) in H;
  change (open_rec_def) with (@open_rec def DefOpenable) in H;
  change (open_rec_defs) with (@open_rec defs DefsOpenable) in H;
  change (fv_trm) with (@fv trm TrmFreeVar) in H;
  change (fv_lit) with (@fv lit LitFreeVar) in H;
  change (fv_def) with (@fv def DefFreeVar) in H;
  change (fv_defs) with (@fv defs DefsFreeVar) in H;
  change (subst_trm) with (@subst_var trm TrmSubstVar) in H;
  change (subst_lit) with (@subst_var lit LitSubstVar) in H;
  change (subst_def) with (@subst_var def DefSubstVar) in H;
  change (subst_defs) with (@subst_var defs DefsSubstVar) in H.

Tactic Notation "fold_trm_abs" "in" "*" :=
  change (open_rec_trm) with (@open_rec trm TrmOpenable) in *;
  change (open_rec_lit) with (@open_rec lit LitOpenable) in *;
  change (open_rec_def) with (@open_rec def DefOpenable) in *;
  change (open_rec_defs) with (@open_rec defs DefsOpenable) in *;
  change (fv_trm) with (@fv trm TrmFreeVar) in *;
  change (fv_lit) with (@fv lit LitFreeVar) in *;
  change (fv_def) with (@fv def DefFreeVar) in *;
  change (fv_defs) with (@fv defs DefsFreeVar) in *;
  change (subst_trm) with (@subst_var trm TrmSubstVar) in *;
  change (subst_lit) with (@subst_var lit LitSubstVar) in *;
  change (subst_def) with (@subst_var def DefSubstVar) in *;
  change (subst_defs) with (@subst_var defs DefsSubstVar) in *.


(** Tactics for simplifying SyntaxClasses *)
Tactic Notation "sympl" :=
  rewrite ? to_list_of_list, ? of_list_to_list;
  simpl; repeat (fold_var_abs; fold_typ_abs; fold_trm_abs);
  rewrite ? to_list_of_list, ? of_list_to_list.

Tactic Notation "sympl" "in" hyp(H) :=
  rewrite ? to_list_of_list, ? of_list_to_list in H;
  simpl in H;
  repeat (fold_var_abs in H; fold_typ_abs in H; fold_trm_abs in H);
  rewrite ? to_list_of_list, ? of_list_to_list in H.

Tactic Notation "sympl" "in" "*" :=
  rewrite ? to_list_of_list, ? of_list_to_list in *; simpl in *;
  repeat (fold_var_abs in *; fold_typ_abs in *; fold_trm_abs in *);
  rewrite ? to_list_of_list, ? of_list_to_list in *.

Ltac sympls := sympl in *.

(** Tactics for generating fresh variables. *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars      => x                ) in
  let B := gather_vars_with (fun x : var       => \{ x }           ) in
  let C := gather_vars_with (fun x : ctx       => dom x \u fv_env x) in
  let D := gather_vars_with (fun x : heap      => dom x \u fv_env x) in
  let E := gather_vars_with (fun x : avar      => fv x             ) in
  let F := gather_vars_with (fun x : trm       => fv x             ) in
  let G := gather_vars_with (fun x : item      => fv x             ) in
  let H := gather_vars_with (fun x : def       => fv x             ) in
  let I := gather_vars_with (fun x : defs      => fv x             ) in
  let J := gather_vars_with (fun x : typ       => fv x             ) in
  let K := gather_vars_with (fun x : lit       => fv x             ) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J \u K).

Ltac pick_fresh x :=
  let L := gather_vars in
  (pick_fresh_gen L x); sympl in *.

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.
