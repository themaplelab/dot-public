(** remove printing ~ *)
Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax.
Require Import Effects Initialization InitLookup.

(** We collect all the Initialization Lookup lemmas together so that they can be
    imported all at once.. *)

Require Export InitLookupBinds
        InitLookupWeaken InitLookupStrengthen
        InitLookupNarrowing
        InitLookupRestrict
        InitLookupSubst.
