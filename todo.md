## Design
- [x] Redo type declaration syntax.
- [x] Turn `PCons` into a general binary construct.
- [x] Remove `CONS` and any builtin operator in favour of identifying it later on or something.
- [x] Parse implicit arguments
- [x] Mutiple arguments in a single binding (i.e. `(a, b, c : Type)`)
- [x] Properly desugar record constructors.
- [ ] Consider pattern synonyms? like in haskell.
- [x] Add type annotations - `10 ~ Nat`.
- [x] Add as patterns - either `x@y` or `y as x`, where y is some pattern.
- [x] Add an `inline` keyword to inline a function definition.
- [ ] Consider adding namespaces within files with a `namespace` and `end` keyword.

## Diagnostics
- [x] Make a logging library
  - [x] Add different severities of messages.
  - [x] Colour output

## Parser
- [x] Migrate from use of exceptions to a custom error type.
- [x] Parse and desugar new type declaration structures.
- [ ] Parse typeclasses.
  - See examples/tclass.dent for syntax ideas.
- [ ] Consider adding error recovery, maybe in the form of token insertion (what token you'd expect to be there)?
  - [ ] Remove usage of `Base.Or_error` alongside this change, swap to accumulating errors and then reporting them all at once.

## Elaborator
- [x] Get basic elaboration working (no holes/solving holes, no implicit arguments).
  - [x] Typecheck basic type-level programming.
- [x] Add meta variables and solving of them to allow for inference of typed holes.
  - [x] Typecheck functions with arguments
  - [x] Properly typecheck match cases (compare patterns to condition type).
    - [x] Implement the algorithm explained in [this paper](https://jesper.sikanda.be/files/elaborating-dependent-copattern-matching.pdf).
    - [x] Properly turn function definitons into case trees.
  - [x] Properly typecheck record update syntax.
    - [x] Decide on whether the language uses haskell field access (`y x`) or typical field access (`x.y`).
    - [x] Add record patterns and desugar them to `PCtor` (have a `located_pattern` for the ast and core syntax).
    - [ ] Generate record access functions.
  - [x] Make sure that aliases, unions and records actually work.
  - [x] Add a pass over functions/expressions to ensure that there aren't any typed holes.
  - [ ] Add impossible patterns (`!` ?) and build the appropriate case for it.
- [ ] Make implicit arguments work properly.
  - [x] Add `forall`/`∀` qualifier to denote types that are implicit (and are erased).
- [ ] Add universe polymorphism.
- [ ] Add type erasure, where you can specify which types can be erased at runtime and which can't.
  - [ ] Implement the algorithm explained in [this paper](https://arxiv.org/pdf/2605.00655)
- [ ] Implement type classes.
  - Save this for later on, maybe after codegen is in place?
