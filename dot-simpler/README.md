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

# Simplifications
- The
  [stage-1](https://github.com/themaplelab/dot-public/tree/master/dot-simpler/stage-1)
  folder contains the Stage 1 simplifications.
- The
  [stage-2](https://github.com/themaplelab/dot-public/tree/master/dot-simpler/stage-2)
  folder contains the Stage 2 simplifications.
- The
  [stage-3](https://github.com/themaplelab/dot-public/tree/master/dot-simpler/stage-3)
  folder contains the Stage 3 simplifications.
