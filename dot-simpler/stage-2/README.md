# A Simpler Syntactic Soundness Proof for Dependent Object Types

In this repo, we present some simplifications of the [Rapoport et al.
proof](https://plg.uwaterloo.ca/~olhotak/pubs/oopsla17.pdf) of type soundness
for the DOT calculus.

The simplification occurs in three stages:
  - In Stage 1, we simplify the tight typing relation so that it is only defined
    for paths and values instead of being defined for arbitrary terms.
  - In Stage 2, we strengthen the well-typed contexts relation so that it uses
    the precise typing for values instead of general typing. This makes the
    well-typed contexts relation the same as store correspondence of the [Amin
    et al.
    proof](https://github.com/samuelgruetter/dot-calculus/blob/master/dev/lf/dot_top_bot.v)
    of type safety for the DOT calculus. This allows us to remove the tight and
    invertible typing relations for values.
  - In Stage 3, we modify the dot typing rules themselves so that typing is
    separately defined for values. This makes the precise typing relation for
    values show up naturally in the type system itself, so it does not need to
    be separately defined.

## Stage 2 Simplifications

This folder contains the stage 2 simplifications.

The additional changes from the [Stage
1](https://github.com/themaplelab/dot-public/tree/master/dot-simpler/stage-1)
are as follows:
  - We moved the definition of well-typed stacks from
    [Definitions.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-2/Definitions.v)
    to
    [PreciseTyping.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-2/Definitions.v)
    and changed well-typed stacks to now use precise typing.
  - We removed the relation `ty_val_t` and the lemma `tight_to_general_val` from
    [TightTyping.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-2/TightTyping.v).
  - We removed the relation `ty_val_inv` and the lemma
    `invertible_val_to_precise_lambda` from
    [InvertibleTyping.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-2/InvertibleTyping.v).
  - We removed the `general_to_tight_val` lemma from
    [GeneralToTight.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-2/GeneralToTight.v).
  - In
    [CanonicalForms.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-2/CanonicalForms.v)
    we changed the `val_typ_all_to_lambda`, `val_mu_to_new`,
    `corresponding_types` lemmas to use precise typing, added the lemma
    `weaken_ty_precise_v`, and made appropriate changes to the proofs of
    `val_typ_all_to_lambda`, `val_mu_to_new`, `corresponding_types`,
    `well_typed_push`, `canonical_forms_fun`, and `canonical_forms_obj`.
  - In
    [Safety.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-2/Safety.v)
    we made minor changes to the proof of `preservation_helper`.

The original files can be found at:
  - [Definitions.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-1/Definitions.v)
  - [PreciseTyping.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-1/PreciseTyping.v)
  - [TightTyping.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-1/TightTyping.v)
  - [InvertibleTyping.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-1/InvertibleTyping.v)
  - [GeneralToTight.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-1/GeneralToTight.v)
  - [CanonicalForms.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-1/CanonicalForms.v)
  - [Safety.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-1/Safety.v)

## Compiling the Proof

To compile the proof, we require
  - [Coq 8.10.2](https://coq.inria.fr/opam-using.html) and related tooling to be run in a unix-like environment. In particular, we require the following tools in the `PATH` enviroment variable:
    * coqc
    * coqtop
    * coqdep
    * coqdoc
    * coqmakefile
  - the [TLC](https://gitlab.inria.fr/charguer/tlc) library which can be installed through

```
 opam repo add coq-released http://coq.inria.fr/opam/released
 opam install -j4 coq-tlc
```

To compile the proof, run

    git clone https://github.com/themaplelab/dot-public
    cd dot-public/dot-simpler/stage-1/
    make

`make` will do the following:

- compile the safety proof
- generate documentation.
