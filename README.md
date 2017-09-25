# HoTT Classes

This repository used to contain formalizations of algebra based on
[Math Classes](https://math-classes.github.io/) but for
[HoTT](https://github.com/hott/hott). They have been merged in
upstream HoTT ([commit dd7c823](https://github.com/HoTT/HoTT/commit/dd7c8232a59bbfbab1a880688c5895cf616654fb)).

Here remain results depending on inductive-inductive types, an
experimental feature not yet merged in Coq, mostly about defining
Cauchy real numbers.

# Related Publications

See SCIENCE.md

# Build

You can follow what travis does ([.travis.yml](.travis.yml), [build-dependencies.sh](build-dependencies.sh) and [build-HoTTClasses.sh](build-HoTTClasses.sh)), or:

- Install dependencies:

    - [Coq with inductive-inductive types](https://github.com/mattam82/coq/tree/IR) including its depencies (some Ocaml libraries)
    - [HoTT modified to compile with Coq IR](https://github.com/SkySkimmer/HoTT/tree/mz-8.7)

- In this guide they are installed respectively in directories `coq/` and `HoTT/`.

- `./configure --hoqdir HoTT/ --coqbin coq/bin/`

- `make`

# Using IDEs

## Coqide

The `./ide` script only works if HoTT/ is in your `$PATH`, use `/path/to/HoTT/hoqide -R theories HoTTClasses` otherwise.

## Proof General

[Proof General](https://github.com/ProofGeneral/PG/) understands the `_CoqProject` produced by `./configure`. `./configure` also sets up `.dir-locals.el` so that PG calls the right hoqtop program.
