# Fixes
- The chapter [gr_predicates.v] does actually not talk about guarded fixpoints, only least fixpoints
- Clean up proofs in some chapters
  - Reduce use of SSreflect
  - Simplify proofs

# Possible future topics
- Chapter on prophecies
- Chapter on HOCAP-style specifications
- Chapters "Linked List", "Arrays", and "Merge Sort" all use list functionality from std++ (e.g. fmap and lookup). These should be introduced beforehand, for example in an appendix, with the chapters referring to the appendix.
- Consider introducing commands "About", "Locate", "Print", etc. in an introductory chapter.
- Add example with "Landin's knot" (recursion through the store) to showcase use of dicardable fractions or invariants for sequential programs
- Add some exercises from Persistently chapter in ILN to Persistently chapter.
- Introduce Generic CMRAs
- Introduce Higher Order CMRAs
- Internal equivalence and validity (Plainly, SIProp)
- Inner workings of BI and using Iris proofmode on other logics.
  - Incompatibility of excluded middle.
- Defining new modalities
  - Run through the relevant typeclasses
- On inductive, co-inductive, and guarded-recursive predicates (based on chapter in ILN).
- How to define a new language in Iris.
- How to define a new program in Iris.
- How to define logical relations models of type systems in Iris.

# Features
- Make tutorial accessible as an interactive webpage (jscoq)
  - See e.g. https://jscoq.github.io/ext/sf/
