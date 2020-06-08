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

## Field Mutable DOT

This folder contains the type safety proof for Field Mutable DOT.

Field Mutable DOT can be thought of being a calculus somewhere in between
[WadlerFest DOT](https://infoscience.epfl.ch/record/215280/files/paper_1.pdf)
and [κDOT](https://plg.uwaterloo.ca/~olhotak/pubs/scala18.pdf). It has the same
values as WadlerFest DOT, but it also features the same sort of mutation and
[bounded field
typing](https://ifazk.com/blog/2018-11-26-Bounded-field-typing.html) as κDOT.
Unlike κDOT, it does not feature constructors.

Field Mutable DOT is based on κDOT, which is already defined in terms of the
stage 3 simplifications, and its type safety proof already utilizes the stage 2
simplifications.

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
    cd dot-public/dot-simpler/dot-field-mut-stage-0/
    make

`make` will do the following:

- compile the safety proof
