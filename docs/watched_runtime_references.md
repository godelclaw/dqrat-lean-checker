# Watched Runtime References

This branch keeps the proof-oriented checker intact and experiments with a
parallel runtime-oriented propagation stack. The goal is to use standard
solver-side propagation accelerations while preserving a clean future
verification story:

- long clauses use two watched literals;
- watch entries may carry a blocking literal as a cache hint;
- binary clauses use a direct implication cache instead of entering the long
  watch machinery.
- cache-only implication entries may be pruned lazily when they are observed to
  point to deleted clauses.
- DQRATE / path-style traversals use a separate live-occurrence cache rather
  than scanning semantic occurrence lists full of deleted clauses.

## Why this shape is verification-friendly

The runtime state is intentionally split into semantic and cache layers:

- `clauses` remains the semantic source of truth;
- `watchedBy`, `binaryImpBy`, and `liveOccBy` are accelerators that can be
  justified later by refinement lemmas back to the clause store;
- binary clauses are isolated from long-clause watch maintenance, which should
  make it easier to prove focused invariants for the two paths separately.

This means a future proof can aim for statements of the form:

- every live binary clause `(a ∨ b)` contributes direct implications
  `¬a → b` and `¬b → a`;
- every live non-binary clause is covered by the watched-literal invariant;
- every live literal occurrence is mirrored in `liveOccBy`;
- propagation over the cache layers refines propagation over the semantic
  clause store.

## Sources

### Two watched literals and blocking literals

1. Markus Iser, Tomáš Balyo.
   *Unit Propagation with Stable Watches*.
   CP 2021.
   https://drops.dagstuhl.de/opus/volltexte/2021/15297/pdf/LIPIcs-CP-2021-6.pdf

Relevant points for this branch:

- the paper describes state-of-the-art propagation as based on two watched
  literals;
- it also notes the common use of a blocking literal per watch entry to skip
  clause access when another literal is already satisfied;
- it mentions a further optimization of remembering where the watch-replacement
  search last succeeded. We are **not** implementing that yet because it adds
  more mutable clause-side state to verify.

### Binary implication graph / binary clause fast path

2. Google OR-Tools C++ reference:
   `BinaryImplicationGraph`.
   https://developers.google.com/optimization/reference/sat/clause/BinaryImplicationGraph

Relevant points for this branch:

- "Special class to store and propagate clauses of size 2";
- `AddBinaryClause(a, b)` is documented as equivalent to `¬a => b` and also to
  `¬b => a`;
- the API cleanly separates implication propagation from the rest of the clause
  machinery, which matches the refinement-friendly split used here.

Relevant points for the current maintenance strategy:

- the class exposes explicit cleanup / removal operations such as
  `CleanupAllRemovedVariables` and `RemoveFixedVariables`;
- it also documents pruning and transitive-reduction ideas for keeping
  implication lists efficient over time.

In this Lean branch we take the smallest proof-friendly step in that direction:
we lazily compact implication lists only when a traversed entry is discovered to
refer to a deleted clause. This is weaker than full graph simplification, but it
keeps the cache layer from growing monotonically with dead entries.

### Reference solver architecture

3. Armin Biere.
   *SATCH* repository README.
   https://github.com/arminbiere/satch

Relevant point for this branch:

- SATCH is presented as a simpler code base that still contains the important
  implementation techniques of state-of-the-art SAT solvers. We use it as an
  architectural reference for "strong but still explainable" design choices.

4. MiniSat project page.
   https://minisat.se/MiniSat.html

Relevant point for this branch:

- the MiniSat page identifies the two-literal watch scheme as one of the core
  state-of-the-art implementation techniques of that solver line.

## Deferred ideas

These are plausible later additions, but are deliberately deferred until the
binary implication path is stable and benchmarked:

- remembered watch-replacement cursors for long clauses;
- "stable watch" selection heuristics;
- specialized ternary-clause paths;
- deduplication / cleanup passes for stale cache entries left behind by deleted
  clauses.

## Citation note

When code comments cite the runtime design, they should prefer pointing here for
the bibliographic context and keep local comments short and implementation
specific.
