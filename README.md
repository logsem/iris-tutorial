# Setup
## Installation
The recommended way to install the dependencies is through [opam](https://opam.ocaml.org/doc/Install.html).

1. Install [opam](https://opam.ocaml.org/doc/Install.html) if not already installed (a version greater than 2.0 is required).
2. Install a new switch and link it to the project.
```
opam switch create iris_tutorial 4.14.0
opam switch link iris_tutorial .
```
3. Add the Coq and Iris opam repositories.
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam update
```
4. Install the right version of the dependencies as specified in the iris-tutorial.opam file.
```
opam install . --deps-only
```

## Editor
Iris uses unicode charecters in its notation. [This guide](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/editor.md) describes how to set up your favorite editor.

# Tactics
This [cheatsheet](/cheatsheet.md) contains a table of the most importent tactics for each logical connective. A full description of the tactics can be found [here](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_mode.md).

# Usage
It is recomended that you go through the files in the order specified in [Content](README.md#content), as later files will relly on knowledge and examples from the previous files.

Most excersises consist of `Admitted` proofs. The excersise is to finish the proof and replace `Admitted` with `Qed`.

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
