(** remove printing ~ *)

Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax PreTyping Typing.

(** * Typing Rules *)
Implicit Types (Gamma G : ctx) (T U : typ) (x y z : var) (t : trm).

(** ** Single-definition typing [G ⊢ d: D] *)
Inductive ty_def : DecTyping def :=
(** [G ⊢ {A = T}: {A: T..T}]   *)
| ty_def_typ : forall G A T,
    G ⊢ def_typ A T ∶d dec_typ A T T

(** [G ⊢ {a = null}: {a: T}] *)
| ty_def_trm : forall G a t T,
    G ⊢ def_trm a ∶d dec_trm a T T.
Existing Instance ty_def.

(** ** Term typing [G ⊢ t: T] *)
Inductive ty_trm : Typing trm :=

(** [G(x) = T]  #<br>#
    [――――――――]  #<br>#
    [G ⊢ x: T]  *)
| ty_var : forall G x T,
    binds x T G ->
    G ⊢ trm_var (avar_f x) ∶ T

(** [G ⊢ x: forall(S)T] #<br>#
    [G ⊢ z: S]     #<br>#
    [――――――――――――] #<br>#
    [G ⊢ x z: T^z]     *)
| ty_all_elim : forall G x z S T,
    G ⊢ trm_var (avar_f x) ∶ typ_all S T ->
    G ⊢ trm_var (avar_f z) ∶ S ->
    G ⊢ trm_app (avar_f x) (avar_f z) ∶ open z T

(** [G ⊢ k : K(is Ts)U]  #<br>#
    [G ⊢ xs :: Ts]                  #<br>#
    [―――――――――――――――――――――――]  #<br>#
    [G ⊢ new k(xs) :: mu(U^Ts)]          *)
| ty_new : forall G x avs xs Ts is' T,
    G ⊢ trm_var (avar_f x) ∶ typ_con Ts is' T ->
    G ⊢ avs :: Ts ->
    vars_of_avars xs avs ->
    G ⊢ trm_new (avar_f x) avs ∶ typ_bnd (open_rec_vars 1 xs T)

(** [G ⊢ x: {a: S .. T}] #<br>#
    [―――――――――――――] #<br>#
    [G ⊢ x.a: T]        *)
| ty_rcd_elim : forall G x a S T,
    G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T) ->
    G ⊢ trm_sel (avar_f x) a ∶ T

(** [G ⊢ x: {a: S .. T}] #<br>#
    [G ⊢ y: S] #<br>#
    [―――――――――――――] #<br>#
    [G ⊢ x.a := y : T]        *)
| ty_fld_asn : forall G x y a S T,
    G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_trm a S T) ->
    G ⊢ trm_var (avar_f y) ∶ S ->
    G ⊢ trm_asn (avar_f x) a (avar_f y) ∶ T

(** [G ⊢ t: T]          #<br>#
    [G, x: T ⊢ u^x: U]  #<br>#
    [x fresh]           #<br>#
    [―――――――――――――――――] #<br>#
    [G ⊢ let t in u: U]     *)
| ty_let : forall L G t u T U,
    G ⊢ t ∶ T ->
    (forall x, x \notin L ->
      G & x ~ T ⊢ open x u ∶ U) ->
    G ⊢ trm_let T t u ∶ U

(** [G ⊢ l: T]          #<br>#
    [G, x: T ⊢ u^x: U]  #<br>#
    [x fresh]           #<br>#
    [―――――――――――――――――] #<br>#
    [G ⊢ let l in u: U]     *)
| ty_llit : forall L G l u T U,
    G ⊢ l ∶ T ->
    (forall x, x \notin L ->
      G & x ~ T ⊢ open x u ∶ U) ->
    G ⊢ trm_lit T l u ∶ U

(** [G ⊢ x: T^x]   #<br>#
    [――――――――――――] #<br>#
    [G ⊢ x: mu(T)]     *)
| ty_rec_intro : forall G x T,
    G ⊢ trm_var (avar_f x) ∶ open x T ->
    G ⊢ trm_var (avar_f x) ∶ typ_bnd T

(** [G ⊢ x: mu(T)] #<br>#
    [――――――――――――] #<br>#
    [G ⊢ x: T^x]   *)
| ty_rec_elim : forall G x T,
    G ⊢ trm_var (avar_f x) ∶ typ_bnd T ->
    G ⊢ trm_var (avar_f x) ∶ open x T

(** [G ⊢ x: T]     #<br>#
    [G ⊢ x: U]     #<br>#
    [――――――――――――] #<br>#
    [G ⊢ x: T /\ U]     *)
| ty_and_intro : forall G x T U,
    G ⊢ trm_var (avar_f x) ∶ T ->
    G ⊢ trm_var (avar_f x) ∶ U ->
    G ⊢ trm_var (avar_f x) ∶ typ_and T U

(** [G ⊢ t: T]   #<br>#
    [G ⊢ T <: U] #<br>#
    [――――――――――] #<br>#
    [G ⊢ t: U]   *)
| ty_sub : forall G (t : trm) T U,
    G ⊢ t ∶ T ->
    G ⊢ T <: U ->
    G ⊢ t ∶ U

with ty_lit : Typing lit :=
(** [G, x: T ⊢ t^x: U^x]     #<br>#
    [x fresh]                #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ lambda(T)t: forall(T)U]      *)
| ty_all_intro : forall L G T t U,
    (forall x, x \notin L ->
      G & x ~ T ⊢ open x t ∶ open x U) ->
    G ⊢ lit_fun T t ∶ typ_all T U

(** [G, y1: T1, ..., x:U ⊢ ds^(x,y1,..): U^(x,y1,...)]     #<br>#
    [x, y1, ... fresh]                #<br>#
    [G, y1: T1, ..., x:U ⊢ t^(x,y1,..): T^(x,y1,...)]     #<br>#
    [――――――――――――――――――――――] #<br>#
    [G ⊢ kappa(x1:i1 T1,...->U){ds}t : K(x1:i1 T1,...)U]      *)
| ty_con_intro : forall L G Ts is' T ds t T',
    (forall x ys,
        length ys = length_s Ts ->
        fresh L (S (length ys)) (cons x ys) ->
        G & (ys ~** (to_list Ts))
        & (x ~ open_vars (cons x ys) T)
            ⊢ (open_vars (cons x ys) ds)
            ∶ (open_vars (cons x ys) T)) ->
    (forall x ys,
        length ys = length_s Ts ->
        fresh L (S (length ys)) (cons x ys) ->
        (G & (ys ~** (to_list Ts)) & (x ~ open_vars (cons x ys) T)
            ⊢ (open_vars (cons x ys) t)
            ∶ (open_vars (cons x ys) T'))) ->
    G ⊢ lit_con Ts is' T ds t ∶ typ_con Ts is' T

(** ** Subtyping [G ⊢ T <: U] *)
with subtyp : Subtyping :=

(** [G ⊢ T <: top] *)
| subtyp_top: forall G T,
    G ⊢ T <: typ_top

(** [G ⊢ bot <: T] *)
| subtyp_bot: forall G T,
    G ⊢ typ_bot <: T

(** [G ⊢ T <: T] *)
| subtyp_refl: forall G T,
    G ⊢ T <: T

(** [G ⊢ S <: T]     #<br>#
    [G ⊢ T <: U]     #<br>#
    [――――――――――]     #<br>#
    [G ⊢ S <: U]         *)
| subtyp_trans: forall G S T U,
    G ⊢ S <: T ->
    G ⊢ T <: U ->
    G ⊢ S <: U

(** [G ⊢ T /\ U <: T] *)
| subtyp_and11: forall G T U,
    G ⊢ typ_and T U <: T

(** [G ⊢ T /\ U <: U] *)
| subtyp_and12: forall G T U,
    G ⊢ typ_and T U <: U

(** [G ⊢ S <: T]       #<br>#
    [G ⊢ S <: U]       #<br>#
    [――――――――――――――]   #<br>#
    [G ⊢ S <: T /\ U]          *)
| subtyp_and2: forall G S T U,
    G ⊢ S <: T ->
    G ⊢ S <: U ->
    G ⊢ S <: typ_and T U

(** [G ⊢ T1 <: T2]           #<br>#
    [G ⊢ U1 <: U2]           #<br>#
    [――――――――――――――――――――] #<br>#
    [G ⊢ {a: T2 .. U1} <: {a: T1 .. U2}] *)
| subtyp_fld: forall G a T1 T2 U1 U2,
    G ⊢ T1 <: T2 ->
    G ⊢ U1 <: U2 ->
    G ⊢ typ_rcd (dec_trm a T2 U1) <: typ_rcd (dec_trm a T1 U2)

(** [G ⊢ S2 <: S1]                   #<br>#
    [G ⊢ T1 <: T2]                   #<br>#
    [――――――――――――――――――――――――――――――] #<br>#
    [G ⊢ {A: S1..T1} <: {A: S2..T2}]     *)
| subtyp_typ: forall G A S1 T1 S2 T2,
    G ⊢ S2 <: S1 ->
    G ⊢ T1 <: T2 ->
    G ⊢ typ_rcd (dec_typ A S1 T1) <: typ_rcd (dec_typ A S2 T2)

(** [G ⊢ x: {A: S..T}] #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢ S <: x.A]     *)
| subtyp_sel2: forall G x A S T,
    G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_typ A S T) ->
    G ⊢ S <: typ_sel (avar_f x) A

(** [G ⊢ x: {A: S..T}] #<br>#
    [――――――――――――――――] #<br>#
    [G ⊢ x.A <: T]     *)
| subtyp_sel1: forall G x A S T,
    G ⊢ trm_var (avar_f x) ∶ typ_rcd (dec_typ A S T) ->
    G ⊢ typ_sel (avar_f x) A <: T

(** [G ⊢ S2 <: S1]                #<br>#
    [G, x: S2 ⊢ T1^x <: T2^x]     #<br>#
    [x fresh]                     #<br>#
    [―――――――――――――――――――――――]     #<br>#
    [G ⊢ forall(S1)T1 <: forall(S2)T2]      *)
| subtyp_all: forall L G S1 T1 S2 T2,
    G ⊢ S2 <: S1 ->
    (forall x, x \notin L ->
       G & x ~ S2 ⊢ open x T1 <: open x T2) ->
    G ⊢ typ_all S1 T1 <: typ_all S2 T2

(** ** Typing list of variables [G ⊢ xs :: Ts] *)
with ty_avars : Typings (list avar) :=
     | typ_avars_nil : forall G,
         G ⊢ nil :: typs_nil

     | typ_avars_cons : forall G x T avs Ts,
         G ⊢ (trm_var (avar_f x)) ∶ T ->
         G ⊢ avs :: Ts ->
         G ⊢ (cons (avar_f x) avs) :: (typs_cons T Ts).
Existing Instances ty_trm ty_avars subtyp.
Existing Instances ty_lit | 1.

Hint Constructors ty_trm ty_lit ty_def ty_defs ty_avars subtyp : core.
Remove Hints subtyp_trans ty_sub : core.
Hint Resolve subtyp_trans ty_sub | 10 : core.

(** ** Mutual Induction Principles *)

Scheme ts_ty_trm_mut := Induction for ty_trm Sort Prop
with   ts_subtyp     := Induction for subtyp Sort Prop
with   ts_ty_avars   := Induction for ty_avars Sort Prop.
Combined Scheme ts_mutind from ts_ty_trm_mut, ts_subtyp, ts_ty_avars.

Scheme rules_trm_mut    := Induction for ty_trm Sort Prop
with   rules_lit_mut    := Induction for ty_lit Sort Prop
with   rules_subtyp     := Induction for subtyp Sort Prop
with   rules_avars_mut  := Induction for ty_avars Sort Prop.
Combined Scheme rules_mutind from rules_trm_mut, rules_lit_mut,
rules_subtyp, rules_avars_mut.

(** ** Tactics *)

Ltac fresh_constructor_extern :=
  match goal with
  | [ |- _ ⊢ lit_con _ _ _ _ _ ∶ typ_con _ _ _ ] =>
    let z := fresh "z" in
    apply_fresh ty_con_intro as z
  | [ |- _ ⊢ lit_fun _ _ ∶ typ_all _ _ ] =>
    let z := fresh "z" in
    apply_fresh ty_all_intro as z
  | [ |- _ ⊢ trm_let _ _ _ ∶ _ ] =>
    let z := fresh "z" in
    apply_fresh ty_let as z
  | [ |- _ ⊢ typ_all _ _ <: typ_all _ _ ] =>
    let z := fresh "z" in
    apply_fresh subtyp_all as z
  | [ |- _ ⊢ trm_lit _ _ _ ∶ _ ] =>
    let z := fresh "z" in
    apply_fresh ty_llit as z
  end.

Hint Extern 4 (_ ⊢ _ ∶ _) => fresh_constructor_extern : core.

Ltac fresh_constructor :=
  fresh_constructor_extern; auto.

(** ** Simple Class Instances *)
Instance TyDefDecTypingLabels : DecTypingLabels ty_def.
Proof.
  hnf; induction 1; reflexivity.
Qed.

(** * Simple Lemmas *)
Lemma ty_avars_concat : forall Ts1 Ts2 G avs,
    G ⊢ avs :: (Ts1 ++ Ts2) ->
    exists avs1 avs2,
      avs = (avs1 ++ avs2)%list /\
      G ⊢ avs1 :: Ts1 /\ G ⊢ avs2 :: Ts2.
Proof.
  induction Ts1; simpl; intros.
  - exists (@nil avar) avs; simpl; repeat_split_right; auto; try constructor.
    assert (R: (typs_nil ++ Ts2) = of_list (to_list Ts2)) by auto; rewrite R in H; clear R.
    rewrite to_list_of_list in H. apply H.
  - replace (typs_cons t Ts1 ++ Ts2) with (typs_cons t (Ts1 ++ Ts2)) in H by auto.
    inversions H. apply IHTs1 in H5. destruct H5 as [avs1 [avs2 H5]].
    destruct_all; subst. exists (avar_f x :: avs1)%list avs2.
    repeat_split_right; auto; try constructor; auto.
Qed.

(** If a variable can be typed in an environment,
    then it is bound in that environment. *)
Lemma typing_implies_bound: forall G x T,
  G ⊢ trm_var (avar_f x) ∶ T ->
  exists S, binds x S G.
Proof.
  introv Ht. remember (trm_var (avar_f x)).
  induction Ht; try congruence;
    match goal with
    | [ H : _ = _ |- _ ] => inversions H
    end; eauto.
Qed.

Lemma var_typing_implies_avar_f: forall G a T,
    G ⊢ trm_var a ∶ T ->
    exists x, a = avar_f x.
Proof.
  intros G a T H.
  remember (trm_var a) as t eqn:Heqt.
  induction H; inversion Heqt; eauto.
Qed.

Lemma length_ty_avars : forall G avs Ts,
    G ⊢ avs :: Ts ->
    length avs = length_s Ts.
Proof.
  introv H. induction H; simpl; auto.
Qed.

(* Note don't add following to hintdb as resolve hints.
   Bug in simpl_dom/rewrite_all tactic in TLC when x # ?G,
   where ?G an existential *)

Lemma typing_notin : forall G x y T,
    x \notin dom G ->
    G ⊢ trm_var (avar_f y) ∶ T ->
    x \notin \{ y}.
Proof.
  introv HG HTy. apply typing_implies_bound in HTy.
  destruct HTy as [S HTy].
  intros Contra. apply HG.
  rewrite in_singleton in Contra; subst.
  apply binds_to_dom in HTy; auto.
Qed.

Lemma typing_notin_open : forall G x y n T U,
    x # G ->
    x \notin fv T ->
    G ⊢ trm_var (avar_f y) ∶ U ->
    x \notin fv (open_rec n y T).
Proof.
  intros. apply notin_open; auto.
  eapply typing_notin; eassumption.
Qed.

Lemma notin_vars_of_avars : forall G x avs ys Ts,
    x \notin dom G ->
    G ⊢ avs :: Ts ->
    vars_of_avars ys avs ->
    x \notin from_list ys.
Proof.
  intros. gen ys. induction H0; intros.
  + inversion H1. rewrite from_list_nil.
    auto.
  + inversions H2. specialize (IHty_avars H _ H5).
    rewrite from_list_cons. notin_solve.
    apply typing_implies_bound in H0.
    destruct H0 as [?S H0]. apply binds_to_dom in H0.
    rewrite notin_singleton. intro Heq; subst.
    contradiction.
Qed.
