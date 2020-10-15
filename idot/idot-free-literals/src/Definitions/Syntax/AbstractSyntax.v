(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra DotTactics.

(* ************************************************************************** *)
(** * Abstract Syntax *)
(** This module collects together all the infrastructure related to syntax. *)

Require Export SyntaxClasses TransformCollect.
Require Export Vars Types Terms Items AbstractMachine.

Implicit Types (ds : defs) (hds : heap_defs).

Lemma typs_to_list_cons : forall {T : typ} {Ts : typs},
    to_list (typs_cons T Ts) = cons T (to_list Ts).
Proof. auto. Qed.

(** Typing environment ([Gamma]) *)
Notation ctx := (env typ).

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
  repeat change typs_to_list with (@to_list typ typs TypsToList) in H;
  repeat change typs_of_list with (@of_list typ typs TypsOfList) in H;
  change (open_rec_dec) with (@open_rec dec DecOpenable) in H;
  change (open_rec_typs) with (@open_rec typs TypsOpenable) in H;
  change (open_rec_typ) with (@open_rec typ TypOpenable) in H;
  change (fv_dec) with (@fv dec DecFreeVar) in H;
  change (fv_typs) with (@fv typs TypsFreeVar) in H;
  change (fv_typ) with (@fv typ TypFreeVar) in H;
  change (subst_dec) with (@subst_var dec DecSubstVar) in H;
  change (subst_typs) with (@subst_var typs TypsSubstVar) in H;
  change (subst_typ) with (@subst_var typ TypSubstVar) in H.

Tactic Notation "fold_typ_abs" "in" "*" :=
  repeat change typs_to_list with (@to_list typ typs TypsToList) in *;
  repeat change typs_of_list with (@of_list typ typs TypsOfList) in *;
  change (open_rec_dec) with (@open_rec dec DecOpenable) in *;
  change (open_rec_typs) with (@open_rec typs TypsOpenable) in *;
  change (open_rec_typ) with (@open_rec typ TypOpenable) in *;
  change (fv_dec) with (@fv dec DecFreeVar) in *;
  change (fv_typs) with (@fv typs TypsFreeVar) in *;
  change (fv_typ) with (@fv typ TypFreeVar) in *;
  change (subst_dec) with (@subst_var dec DecSubstVar) in *;
  change (subst_typs) with (@subst_var typs TypsSubstVar) in *;
  change (subst_typ) with (@subst_var typ TypSubstVar) in *.

(** Tactics for Terms *)
Tactic Notation "fold_trm_abs" "in" hyp(H) :=
  change (open_rec_trm) with (@open_rec trm TrmOpenable) in H;
  change (open_rec_lit) with (@open_rec lit LitOpenable) in H;
  change (open_rec_def) with (@open_rec def DefOpenable) in H;
  change (fv_trm) with (@fv trm TrmFreeVar) in H;
  change (fv_lit) with (@fv lit LitFreeVar) in H;
  change (fv_def) with (@fv def DefFreeVar) in H;
  change (subst_trm) with (@subst_var trm TrmSubstVar) in H;
  change (subst_lit) with (@subst_var lit LitSubstVar) in H;
  change (subst_def) with (@subst_var def DefSubstVar) in H;
  change (@subst_var_list def DefSubstVar)
    with (@subst_var defs (@ListSubstVar def DefSubstVar)) in H;
  fold_list in H.

Tactic Notation "fold_trm_abs" "in" "*" :=
  change (open_rec_trm) with (@open_rec trm TrmOpenable) in *;
  change (open_rec_lit) with (@open_rec lit LitOpenable) in *;
  change (open_rec_def) with (@open_rec def DefOpenable) in *;
  change (fv_trm) with (@fv trm TrmFreeVar) in *;
  change (fv_lit) with (@fv lit LitFreeVar) in *;
  change (fv_def) with (@fv def DefFreeVar) in *;
  change (subst_trm) with (@subst_var trm TrmSubstVar) in *;
  change (subst_lit) with (@subst_var lit LitSubstVar) in *;
  change (subst_def) with (@subst_var def DefSubstVar) in *;
  change (@subst_var_list def DefSubstVar)
    with (@subst_var defs (@ListSubstVar def DefSubstVar)) in *;
  fold_list in *.


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
  let K := gather_vars_with (fun x : typs      => fv x             ) in
  let L := gather_vars_with (fun x : lit       => fv x             ) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H \u I \u J \u K \u L).

Ltac pick_fresh x :=
  let L := gather_vars in
  (pick_fresh_gen L x); sympl in *.

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.
