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

# Working on the excersises
To work on the excersises, simply edit the files in the `excersises/` folder. Some proofs and definitions are admitted and marked as `(* excersise *)`; your task is to fill in thoses definitions and complete the proofs all the way to `Qed`. It's recomended that you go through the excersises in the order specified in [Content](README.md#content).

After you are done with a file, run make `make` (with your working directory being the repository root, where the `Makefile` is located) to compile and check the excersises.

If you are stuck, you can find solutions in the corresponding file in the `theories/` folder.

## Editor
Iris uses unicode charecters in its notation. [This guide](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/editor.md) describes how to set up your favorite editor.

# Documentation
This [cheatsheet](/cheatsheet.md) contains a table of the most importent tactics for each logical connective. A full description of the tactics can be found in the files [proof_mode.md](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/proof_mode.md) and  [heap_lang.md](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/heap_lang.md).

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

# Generating the excersises
If you want to contribute to the tutorial, note that the files in `excersises/` are generated from the corresponding files in `theories/`. Run `make excersises` to re-generate those files this requires `gawk` to be installed (which should be available on Linux, and on macOS can be installed via `brew install gawk`).

The syntax for the solution files is as follows:

    (* SOLUTION *) Proof.
      solution here.
    Qed.

is replaced by

    Proof.
      (* exercise *)
    Admitted.

and the more powerful

    (* BEGIN SOLUTION *)
      solution here.
    (* END SOLUTION BEGIN TEMPLATE
      exercise template here.
    END TEMPLATE *)

is replaced by

      exercise template here.