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
This [cheatsheet](/cheatsheet.md) contains a table of the most importent tactics for each logical connective. A full description of the tactics can be found [here](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_mode.md).

- [base](/theories/base.v) - Introduction to the Iris proofmode
  - [pure](/theories/pure.v) - Distinktion between the Coq context and Iris context
  - [persistently](/theories/persistently.v) - The 3rd context
- [lang](/theories/lang.v) - Introduction to heaplang
- [linked_lists](/theories/linked_lists.v) - Exercises with linked lists
  - [fixpoint](/theories/fixpoint.v) - Fixpoints of propositions
- [invariants](/theories/invariants.v) - Introduction to invariants
  - [threads](/theories/threads.v) - Construction of thread operations
  - [spin_lock](/theories/spin_lock.v) - Specification for a spin lock
  - [counter](/theories/counter.v) - Introduction to the authoratative camera.
  - [ticket_lock](/theories/ticket_lock.v) - Specification for a ticket lock (TO BE DOCUMENTED)
- [adequacy](/theories/adequacy.v)

# To be sorted
- logic/cmra.v
  - logic/key.v
