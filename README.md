# Setup
## Installation
We recomend installing Iris via opam (2.0.0 or
newer).  To obtain the latest stable release, you have to add the Coq opam
repository:

    opam repo add coq-released https://coq.inria.fr/opam/released

If you wish to obtain a development version, also add the Iris opam repository:

    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

## Editor
Iris uses unicode charecters in its notation. [This guide](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/editor.md) describes how to set up your favorite editor.

# Tactics
This [cheatsheet](/cheatsheet.mk) contains a table of the most importent tactics for each logical connective. A full description of the tactics can be found [here](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_mode.md).


- logic/base.v
  - logic/pure.v
  - logic/persistently.v
- heaplang/base.v
  - heaplang/linked_lists.v
    - heaplang/fixpoint.v
  - heaplang/threads.v
  - heaplang/invariant.v

- logic/cmra.v
  - logic/key.v
