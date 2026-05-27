## Design
- [x] Redo type declaration syntax.
- [x] Turn `PCons` into a general binary construct.
- [x] Remove `CONS` and any builtin operator in favour of identifying it later on or something.
- [x] Parse implicit arguments
- [x] Mutiple arguments in a single binding (i.e. `(a, b, c : Type)`)
- [x] Properly desugar record constructors.
- [ ] Consider pattern synonyms? like in haskell.

## Diagnostics
- [x] Make a logging library
  - [x] Add different severities of messages.
  - [x] Colour output
- [ ] Replace any use of `Base.Or_error.t` with an `option`-style error, and use the logger to print errs to console.
  - [ ] When done, remove error.ml.

## Parser
- [x] Migrate from use of exceptions to a custom error type.
- [x] Parse and desugar new type declaration structures.
- [ ] Consider adding error recovery, maybe in the form of token insertion (what token you'd expect to be there)?

## Elaborator
- [x] Get basic elaboration working (no holes/solving holes, no implicit arguments).
  - [x] Typecheck basic type-level programming.
- [ ] Add meta variables and solving of them to allow for inference of typed holes.
  - [x] Typecheck functions with arguments
  - [ ] Properly typecheck match cases (compare patterns to condition type).
  - [ ] Properly typecheck record update syntax.
  - [ ] Make sure that aliases, unions and records actually work.
  - [ ] Add a pass over functions/expressions to ensure that there aren't any typed holes.
    - if there is, report the inferred type to the user by looking up the mv in the meta context
    - return a `None` (migrate to logging before this) to prevent further compilation.
- [ ] Make implicit arguments work properly.
