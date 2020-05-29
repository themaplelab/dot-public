# A Simpler Syntactic Soundness Proof for pDOT

In this repo, we present some simplifications of the type safety proof of the
[pDOT calculus](https://arxiv.org/abs/1904.07298v1).

Here we only present the Stage 1 simplifications, where we simplify the tight
typing relation so that it is only defined for paths and values.

The original repository without our simplifications can be found
[here](https://amaurremi.github.io/dot-calculus/src/extensions/paths/).

## Stage 1 Simplifications

This folder contains the stage 1 simplifications.

The changes from the Coq formalization of the [Rapoport et al.
proof](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths)
are as follows:
  - In
    [TightTyping.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/pdot-stage-1/TightTyping.v)
    we changed the type of the relation `ty_trm_t` from `ctx -> trm -> typ ->
    Prop` to `ctx -> path -> typ -> Prop` and removed non-path terms from the
    relation. We also added a separate tight typing relation for values
    `Inductive ty_val_t : ctx -> val -> typ -> Prop`.
  - In
    [ReplacementTyping.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/pdot-stage-1/ReplacementTyping.v)
    we changed the lemmas `replacement_closure` and `replacement_closure_v` to
    use the new tight typing relations.
  - In
    [GeneralToTight.v](https://github.com/themaplelab/dot-public/blob/master/dot-simpler/pdot-stage-1/GeneralToTight.v)
    we changed the lemma `general_to_tight_typing` to be about variables instead
    of terms. We also added the lemmas `general_to_tight_subtyping` and
    `general_to_tight_val`.


## Compiling the Proof

**System requirements**:

  - make
  - an installation of [Coq 8.10.2](https://coq.inria.fr/opam-using.html), preferably through [opam](https://opam.ocaml.org/)
  - the [TLC](https://gitlab.inria.fr/charguer/tlc) library which can
  be installed through

```
 opam repo add coq-released http://coq.inria.fr/opam/released
 opam install -j4 coq-tlc
```

To **compile the proof**, run

```
 git clone https://github.com/themaplelab/dot-public
 cd dot-public/dot-simpler/pdot-stage-1/
 make
```
