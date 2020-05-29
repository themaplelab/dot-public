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

## Stage 1 Simplifications

This folder contains the stage 1 simplifications.

The changes from the Coq formalization of the [Rapoport et al.
proof](https://github.com/amaurremi/dot-calculus) are as follows:
  - In
    [TightTyping.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-1/TightTyping.v)
    we changed the type of the relation `ty_trm_t` from `ctx -> trm -> typ ->
    Prop` to `ctx -> var -> typ -> Prop` and removed non-variable terms from the
    relation. We also added a separate tight typing relation for values
    `Inductive ty_val_t : ctx -> val -> typ -> Prop`.
  - In
    [InvertibleTyping.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-1/InvertibleTyping.v)
    we changed the lemmas `tight_to_invertible` and `tight_to_invertible_v` to
    use the new tight typing relations.
  - In
    [GeneralToTight.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-1/GeneralToTight.v)
    we changed the lemma `general_to_tight_typing` to be about variables instead
    of terms. We also added the lemmas `general_to_tight_subtyping` and
    `general_to_tight_val`.
  - In
    [CanonicalForms.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-1/CanonicalForms.v)
    we changed some of the lemmas to use `general_to_tight_val` instead of the
    previous `general_to_tight` lemma.

The original files can be found at:
  - [TightTyping.v](https://github.com/amaurremi/dot-calculus/blob/master/src/simple-proof/proof/TightTyping.v)
  - [InvertibleTyping.v](https://github.com/amaurremi/dot-calculus/blob/master/src/simple-proof/proof/InvertibleTyping.v)
  - [GeneralToTight.v](https://github.com/amaurremi/dot-calculus/blob/master/src/simple-proof/proof/GeneralToTight.v)
  - [CanonicalForms.v](https://github.com/amaurremi/dot-calculus/blob/master/src/simple-proof/proof/CanonicalForms.v)

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
