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

## Stage 3 Simplifications

This folder contains the stage 3 simplifications.

The additional changes from the [Stage
2](https://github.com/themaplelab/dot-public/tree/master/dot-simpler/stage-2)
are as follows:
  - In
    [Definitions.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-3/Definitions.v)
    we removed the rules `ty_all_intro` and `ty_new_intro` from `ty_trm`, and
    added moved `ty_val_p` from
    [PreciseTyping.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-3/Definitions.v)
    made it part of the recursive definition of typing using the `ty_val` typing
    rule.
  - The weakening, narrowing, and subsititution lemmas now have additional cases
    for value typing in
    [Weakening.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-3/Weakening.v),
    [Narrowing.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-3/Narrowing.v),
    and
    [Substitution.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-3/Substitution.v).

The original files can be found at:
  - [Definitions.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-2/Definitions.v)
  - [PreciseTyping.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-2/PreciseTyping.v)
  - [Weakening.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-2/Weakening.v)
  - [Narrowing.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-2/Narrowing.v)
  - [Substitution.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/stage-2/Substitution.v)

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
