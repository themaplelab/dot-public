Set Implicit Arguments.

Require Import LibExtra DotTactics.
Require Import
        AbstractSyntax PreTyping Typing
        GeneralTyping.
Require Import Effects Initialization InitLookupLemmas InitTyping.

(** * Stack Typing *)
(** Frame stacks represent evaluation contexts, and to extend the type and
    effect systems to the abstract machine, we must type the frame stacks.
   [ty_stack Gamma Delta ℰs Fs T i Es U], represented in our paper with [Gamma; Delta; ℰs ⊢ Fs : (T, i) => (Es, U)]
   says that if the current hole has type T and initialisation type i under:
   - the given typing context Gamma
   - initialisation context Delta
   - and only has access to free variables in the topmost eff_ctx of ℰs
   then the overall stack s (hole + awaiting continuations) will end up performing
   effects Es and having type U *)
Inductive ty_stack :
  ctx -> init_ctx -> list eff_ctx -> stack ->
  typ -> init_typ -> list effects -> typ -> Prop :=
(** [Gamma ⊢ T <: U ]  #<br>#
    [――――――――]  #<br>#
    [Gamma; Delta; (ℰ :: nil) ⊢ nil : (T, i) => (ε :: nil, U)]  *)
  | ty_stack_nil : forall Gamma Delta T U ℰ i,
      Gamma ⊢ T <: U ->
              ty_stack Gamma Delta (ℰ :: nil) (* (empty :: nil) *)
                       nil T i
                       (nil :: nil)%list U

(** [Gamma; Delta; (ℰ :: ℰs) ⊢ Fs : (T, i') => (E :: Es, U)]  #<br>#
    [Gamma,x:S ⊢ t : T ]  #<br>#
    [Gamma,x:S; Delta,x:i; (dom ℰ) ∪ { x } ⊢ t : i' ]  #<br>#
    [⊢e t : E']  #<br>#
    [x fresh]  #<br>#
    [――――――――]  #<br>#
    [Gamma; Delta; (ℰ :: ℰs) ⊢ (let (x:T) = [] in u :: Fs) : (S, i) => (E' ∪ E :: Es, U)]  *)
  | ty_stack_let : forall L Gamma Delta ℰ ℰs Fs t S i i' T effs effss effs' U,
      ty_stack Gamma Delta (ℰ :: ℰs)
               Fs T i'
               (effs :: effss) U ->
      (forall x, x \notin L -> Gamma & x ~ S ⊢ open x t ∶ T) ->
      (forall x,
          x \notin L ->
          Gamma & x ~ S ⸴ Delta & x ~ i ⸴ dom ℰ \u \{ x} ⊢i open x t ∶ i') ->
      (forall x, x \notin L -> ⊢e open x t ∶ effs') ->
      ty_stack Gamma Delta (ℰ :: ℰs)
               (frame_let t :: Fs)%list S i
               ((effs' ++ effs) :: effss)%list U
(** [Gamma; Delta; (ℰ :: ℰs) ⊢ Fs : (T, free) => (E :: Es, U)]  #<br>#
    [Gamma ⊢ x : T ]  #<br>#
    [Gamma; Delta; (dom ℰ) ⊢ x : free ]  #<br>#
    [――――――――]  #<br>#
    [Gamma; Delta; (ℰ :: ℰs) ⊢ (return x :: Fs) : (S, i) => (E :: Es, U)]  *)
  | ty_stack_ret_free : forall Gamma Delta ℰ ℰs Fs x S i effs effss T U,
      ty_stack Gamma Delta (ℰ :: ℰs)
               Fs T free
               (effs :: effss) U ->
      Gamma ⊢ trm_var (avar_f x) ∶ T ->
      Gamma ⸴ Delta ⸴ (dom ℰ) ⊢i trm_var (avar_f x) ∶ free ->
      ty_stack Gamma Delta (ℰ :: ℰs)
               (frame_ret x :: Fs)%list S i
               (effs :: effss)%list U
(** [Gamma; Delta; ℰs ⊢ Fs : (T, committed) => (Es, U)]  #<br>#
    [Gamma ⊢ x : T ]  #<br>#
    [Gamma; Delta; (dom ℰ) ⊢ x : free ]  #<br>#
    [――――――――]  #<br>#
    [Gamma; Delta; (ℰ :: ℰs) ⊢ (return x :: Fs) : (S, i) => (ε :: Es, U)]  *)
  | ty_stack_ret_committed : forall Gamma Delta ℰ ℰs Fs x S i effss T U,
      ty_stack Gamma Delta ℰs
               Fs T committed
               effss U ->
      Gamma ⊢ trm_var (avar_f x) ∶ T ->
      (* This is before x becomes part of the committed heap *)
      Gamma ⸴ Delta ⸴ (dom ℰ) ⊢i trm_var (avar_f x) ∶ free ->
      ty_stack Gamma Delta (ℰ :: ℰs)
               (frame_ret x :: Fs)%list S i
               (nil :: effss)%list U.
Hint Constructors ty_stack : core.
