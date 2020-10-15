(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.

(** * Effects *)
(** An effect is a pair [(x, a)], where [x] is a reference to an object and [a]
is a field of that object. To perform the effect [(x, a)] means to assign a
location to the field [a] of the object referred to by [x]. Depending on the
situation, we will either require an effect to be performed or will guarantee
that an effect will be performed. *)
Notation effect := (var * trm_label)%type.

(** We use lists instead of sets to combine multiple effects together so that
    renaming and substitution for effects becomes easier to prove *)
Notation effects := (list effect).

(** An effect context ([eff_ctx]) is a mapping from locations to effects.
    In an effect context [ℰ], if [ℰ(x)=eff], then [eff] is a list of all effects
    that are required to be performed to make [x] null-free. *)
Notation eff_ctx := (env effects).

(** Given the definitions [ds] for the object [x] which is about to be
allocated, [def_eff x ds] computes the effects that have to be performed to make
[x] null-free.
This is precisely all the declared fields because fields are initially declared
to be null *)
Fixpoint def_eff (x : var) (ds : defs) : (list effect) :=
  match ds with
  | nil => nil
  | (def_typ _ _) :: ds => def_eff x ds
  | (def_trm l) :: ds => (x,l) :: (def_eff x ds)
  end%list.

(** ** Simple Lemmas about Effects *)
(** Effect membership is decidable. *)
Lemma eff_from_list_decide (eff : effect) effs :
  {eff \in (from_list effs)} + {eff \notin (from_list effs)}.
Proof.
  induction effs as [| eff' effs IHeffs].
  - right. rewrite from_list_nil.
    notin_solve.
  - rewrite from_list_cons.
    destruct IHeffs as [Hin | Hni].
    + left. rewrite in_union; auto.
    + refine (If (eff = eff') then _ else _); subst.
      * left; rewrite in_union, in_singleton.
        auto.
      * right; rewrite notin_union, notin_singleton.
        auto.
Qed.

(** * Effect System *)
Reserved Notation "'⊢e' t '∶' eff"
         (at level 40, t at level 59).

(** The effect system is a definite assignment analysis.
If [⊢e t ∶ eff] holds, then executing [t] will definitely assign to the fields
[eff], i.e. executing [t] it will perform the effects [eff]. *)
Inductive eff_trm :
  trm -> effects -> Prop :=

(** [⊢e t : {}] *)
| eff_ignore : forall t,
    ⊢e t ∶ nil

(** [⊢e x.a := y : {(x,a)}] *)
| eff_fld_asn : forall x a y,
    ⊢e trm_asn (avar_f x) a (avar_f y) ∶ ((x,a) :: nil)

(** [⊢e t : E1 ]  #<br>#
    [⊢e u : E2 ]  #<br>#
    [x fresh ]  #<br>#
    [――――――――]  #<br>#
    [⊢e let (x : T) = t in u : E1 ∪ E2 ] *)
| eff_let : forall L T t u eff1 eff2,
    ⊢e t ∶ eff1 ->
    (forall x, x \notin L -> ⊢e open x u ∶ eff2) ->
    ⊢e trm_let T t u ∶ (eff1 ++ eff2)

(** [⊢e u : E ]  #<br>#
    [x fresh ]  #<br>#
    [――――――――]  #<br>#
    [⊢e let (x : T) = l in u : E ] *)
| eff_llit : forall L T l u eff,
    (forall x, x \notin L -> ⊢e open x u ∶ eff) ->
    ⊢e trm_lit T l u ∶ eff

where "'⊢e' t '∶' eff" := (eff_trm t eff).
Hint Constructors eff_trm : core.

(** We lift the above effect system to allow the effect list to be reordered. *)
Definition has_effs t effs := exists effs',
    ⊢e t ∶ effs' /\ from_list effs = from_list effs'.
