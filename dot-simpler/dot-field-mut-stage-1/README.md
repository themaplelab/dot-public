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

## Simplifications for Field Mutable DOT

This folder contains the stage 1 simplifications for Field Mutable DOT.

Field Mutable DOT is based on κDOT, which is already defined in terms of the
stage 3 simplifications, and its type safety proof already utilizes the stage 2
simplifications. Thus we only apply the stage 1 simplifications for Field
Mutable DOT.

The changes from the [Field Mutable DOT safety
proof](https://github.com/themaplelab/dot-public/tree/master/dot-simpler/dot-field-mut-stage-0)
are as follows:
  - In
    [TightTyping.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/dot-field-mut-stage-1/CanonicalForms/TightTyping.v)
    we changed the type of the relation `ty_trm_t` from `ctx -> trm -> typ ->
    Prop` to `ctx -> var -> typ -> Prop` and removed non-variable terms from the
    relation. We also changed the lemma `tight_to_general` from being a lemma
    about `trm`s to a lemma about `var`s.
  - In
    [InvertibleTyping.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/dot-field-mut-stage-1/CanonicalForms/InvertibleTyping.v)
    we changed `tight_to_invertible` from being a lemma about terms that are
    variabes to be a lemma about variables.
  - In
    [GeneralToTight.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/dot-field-mut-stage-1/CanonicalForms/GeneralToTight.v)
    we made appropriate changes to `sel_replacement`, `general_to_tight`, and
    `general_to_tight_typing`.

The original files can be found at:
  - [TightTyping.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/dot-field-mut-stage-0/CanonicalForms/TightTyping.v)
  - [InvertibleTyping.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/dot-field-mut-stage-0/CanonicalForms/InvertibleTyping.v)
  - [GeneralToTight.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/dot-field-mut-stage-0/CanonicalForms/GeneralToTight.v)

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
    cd dot-public/dot-simpler/dot-field-mut-stage-1/
    make

`make` will do the following:

- compile the safety proof
