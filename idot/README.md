# &#x03B9;DOT: A DOT Calculus with Safe Object Initialization

Our paper presents &#x03B9;DOT calculus, which extends the &#x03BA;DOT calculus
of Kabir and Lhot&aacute;k with a type and effect system object to ensure
null-safety and makes fields non-lazy.
&#x03BA;DOT is itself an extension of the WadlerFest DOT calculus of Amin el al.
(2016).
This repository contains a formalization of the type-safety proof of the
calculus and various extensions of the calculus in Coq.

[&#x03B9;DOT paper](https://doi.org/10.1145/3428276) | [Documentation](https://themaplelab.github.io/dot-public/idot/README.html)

## System Requirements
- `make`
- the `dot` program from the Graphviz collection
- an installation of [Coq 8.10.2](https://coq.inria.fr/opam-using.html), preferably installed using `opam`
- the [TLC](https://gitlab.inria.fr/charguer/tlc) library (version 20181116) whach can be installed through
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam pin add coq-tlc 20181116
    opam install coq-tlc

## Compiling the Proofs
To compile the proof, clone the repository, open up a terminal, navigate to the
`idot` directory on the command line, and run `make`.
This will compile the proof and regenerate the documentation in all the subdirectories.

## Documentation

The repository contains the pregenerated documentation for the Coq proofs.
Open the `idot/README.html` file to view the documentation.
You may also view the documentation [here](https://themaplelab.github.io/dot-public/idot/README.html).
