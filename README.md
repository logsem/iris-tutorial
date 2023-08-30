# Setup
## Installation
We recomend installing Iris via opam (2.0.0 or
newer).  To obtain the latest stable release, you have to add the Coq opam
repository:

    opam repo add coq-released https://coq.inria.fr/opam/released

If you wish to obtain a development version, also add the Iris opam repository:

    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

Now to install iris simply run:

    opam install coq-iris
    opam install coq-iris-heap-lang

To fetch updates later, run `opam update && opam upgrade`.

## Editor
Iris uses unicode charecters in its notation. [This guide](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/editor.md) describes how to set up your favorite editor.

# Tactics
This [cheatsheet](/cheatsheet.md) contains a table of the most importent tactics for each logical connective. A full description of the tactics can be found [here](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_mode.md).

# Usage
It is recomended that you go through the files in the order specified in [Content](README.md#content), as later files will relly on knowledge and examples from the previous files.

# Content

- [base](/theories/base.v) - Introduction to the Iris proofmode
  - [pure](/theories/pure.v) - Distinction between the Coq context and Iris context
  - [persistently](/theories/persistently.v) - The 3rd context
- [lang](/theories/lang.v) - Introduction to heaplang
  - [later](/theories/later.v) - Recursive functions
- [linked_lists](/theories/linked_lists.v) - Exercises with linked lists
  - [fixpoint](/theories/fixpoint.v) - Fixpoints of propositions
- [arrays](/theories/arrays.v) - Introduction to arrays in heaplang
  - [merge_sort](/theories/merge_sort.v) - Merge sort
- [invariants](/theories/invariants.v) - Introduction to invariants
  - [counter](/theories/counter.v) - Introduction to the authoratative camera
  - [spin_lock](/theories/spin_lock.v) - Specification for a spin lock
  - [threads](/theories/threads.v) - Construction of thread operations
  - [ticket_lock](/theories/ticket_lock.v) - Specification for a ticket lock
- [adequacy](/theories/adequacy.v)

# To be sorted
- logic/cmra.v
  - logic/key.v
