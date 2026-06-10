# CLAUDE.md — dqrat-lean

## Project Overview

Lean 4 implementation and formal verification of a **DQRAT proof checker** for DQBF (Dependency Quantified Boolean Formulas). The checker verifies refutation proofs in the DQRAT proof system, which generalizes DRAT to the DQBF setting.

- **Reference implementation**: `dqrat-check/` — original C++ checker (for cross-referencing behavior)
- **Papers**: `papers/` — informal proofs and algorithmic background (PDFs)
- **Lean implementation**: `DqratLean/` + `Main.lean`
- **Lean version**: Lean 4, build via `lake build`

## Lean Tooling

Use the **lean-lsp MCP server** for all Lean interactions:
- `lean_goal` — proof state at a position
- `lean_diagnostic_messages` — compiler errors/warnings
- `lean_multi_attempt` — test tactics without editing
- `lean_leansearch` / `lean_loogle` / `lean_leanfinder` — search Mathlib
- `lean_hover_info` — type signatures and docs
- `lean_local_search` — fast search within the project

## File Structure

| File | Purpose |
|------|---------|
| `DqratLean/Types.lean` | `Var`, `Literal` (MiniSAT encoding), `CRef` |
| `DqratLean/Formula.lean` | `DQBF` struct: variables, dependency sets, ordering |
| `DqratLean/ClauseStore.lean` | Clause storage with occurrence lists; proved lemmas for add/delete |
| `DqratLean/CheckState.lean` | `CheckState`, `CheckM` monad, trail, propagation, independence cache |
| `DqratLean/Checker.lean` | Core algorithms: `negateAndPropagate`, `checkDQRATE`, `checkDQRATU`, `checkPathC` |
| `DqratLean/Parser.lean` | DQDIMACS parsing + two-phase proof parsing; `ProofResult` |
| `DqratLean/SoundnessCore.lean` | Invariant definitions: `CheckState.Sound`/`Correct`/`FullCorrect` |
| `DqratLean/DeletionSemantics.lean` | Deletion semantic layer: `forceDelDeps`, independence bridges, `flipUniv` |
| `DqratLean/DeletionPaths.lean` | `DeletePurePath`, `getReachable` BFS spec, `NoDeleteCrossPaths` |
| `DqratLean/DeletionExhibition.lean` | The single open frontier theorem (leaf) |
| `DqratLean/Semantics.lean` | Formal DQBF semantics via Skolem functions: `DQBFTrue`, `DQBFFalse`, `ValidSkolem` |
| `DqratLean/Soundness.lean` | Formal soundness proofs (partially proved — see status below) |
| `DqratLean/Basic.lean` | Re-exports all submodules |
| `Main.lean` | CLI entry: reads files, calls `parseDQDIMACS` then `processProof` |
| `MonadTutor.lean` | Tutorial on `Std.Do` Hoare triples for verifying stateful (`EStateM`) programs. Read it whenever you need to reason about monadic programs in Lean. |

## Key Types

```lean
-- Literals use MiniSAT encoding: 2*var + (1 if pos, 0 if neg)
structure Literal where x : Nat
abbrev Var := Nat  -- 1-indexed

-- Formula
structure DQBF where
  maxVar : Var
  depset : Array (Array Var)  -- depset[v] = sorted deps of existential v
  isExistential : Array Bool
  -- ...

-- Checker monad: error/state over CheckState
abbrev CheckM := EStateM String CheckState

-- Semantics
def DQBFTrue (f : DQBF) (cs : ClauseStore) : Prop  -- ∃ valid Skolem assignment
def DQBFFalse (f : DQBF) (cs : ClauseStore) : Prop  -- ¬ DQBFTrue
```

## Soundness Proof Status

### Fully Proved
- Parser correctness (`parseDQDIMACS_correct`) and executable regressions
- DEL rule, addClause monotonicity, UR rule, RUP soundness
- DQRATE soundness (`checkDQRATE_sound_spec` on the executable-aligned
  `FullCorrect` surface, with the occurrence-completeness invariant)
- Add-only existential modification (`checkModifyExistentialAddOnly_sound`)
- Full wrapper chain: `checkAction_sound`, `processProof_sound'`
- ClauseStore operations

### Complete (2026-06-10)
- `deleteIndependenceSetBridge_of_noDeleteCrossPathsSet` and the entire
  deletion rule family are PROVED (`DqratLean/DeletionExhibition.lean`,
  transcribing Beyersdorff-Blinkhorn-Chew-Schmidt-Suda JAR 2019).
- The library is sorry-free; `processProof_sound'` depends only on
  `propext`, `Classical.choice`, `Quot.sound`.

## Verification Approach

The checker state monad `CheckM = EStateM String CheckState` is well-suited to the `Std.Do` toolkit for Hoare-triple-style verification. See `MonadTutor.lean` for working examples of this style applied to checker operations like `newDecisionLevel` and `enqueue`.

Key predicates for invariant reasoning (defined in `Soundness.lean`):
- `StatePreservesModels`: assigned variables are forced by any satisfying assignment
- `ConsistentWith`: checker state is consistent with a given satisfying assignment
- `ClausesWellFormed`: all literals are in valid variable range

## Algorithms

### Unit Propagation
Occurrence-list based (`CheckState.propagate`). `trail[i]` holds literals assigned at level `i`. Backtrack via `backtrackBefore`.

### RUP / DQRATE
`checkDQRATE` in `Checker.lean`:
1. Negate all literals, propagate → conflict means RUP succeeds
2. If RUP fails: for each clause containing `¬pivot` (existential), negate its "outer" literals and propagate → all must conflict (RAT check)

### DQRATU
`checkDQRATU`: like DQRATE but pivot is universal; uses `checkPathC` to skip clauses disconnected via D^∀-pure paths (Mixed-EUR variant).

### Independence Cache
`CheckState.computeDeps` lazily computes which existentials are independent of a universal via BFS reachability (`getReachable`). Invalidated on clause additions.

## Testing

After any code change (not needed after just a proof update), verify that all 6 tests in `dqrat-check/test/` produce the same result as the C++ reference checker.

```sh
CPP=dqrat-check/build/src/dqrat-check
LEAN=.lake/build/bin/dqrat-lean
TESTS=dqrat-check/test

for i in 01 02 03 04 05 06; do
  f=$(ls $TESTS/test_${i}_*.dqdimacs)
  p=$(ls $TESTS/test_${i}_*.dqrat)
  echo "$(basename $f .dqdimacs)"
  echo "  C++:  $($CPP  $f $p 2>&1 | grep '^s ')"
  echo "  Lean: $($LEAN $f $p 2>&1 | grep '^s ')"
done
```

### Expected Results (verified 2026-03-21)

| Test | Expected (`s` line) | What it exercises |
|------|---------------------|-------------------|
| `test_01_ldq-unsound` | `s FAILED` | Correctly rejects a proof that is unsound under LDQ but valid under DQRAT |
| `test_02_propositionally_unsat` | `s VERIFIED` | UP derives conflict at line 1 (propositional UNSAT) |
| `test_03_UP_unsat` | `s VERIFIED` | Formula itself is UNSAT by UP during parsing — no proof needed |
| `test_04_propositional_drat` | `s UNKNOWN` | All lemmas check out but no final conflict clause — incomplete proof |
| `test_05_ex2_BCJ14_Thm7` | `s VERIFIED` | DQBF example from BCJ14 Thm 7; UP conflict at line 23 |
| `test_06_fork` | `s VERIFIED` | Fork example; UP conflict at line 54 |

Both checkers agree on all 6 tests. Minor output differences (C++ prints a timing line; message wording differs slightly) are expected and not a concern — only the `s` verdict line matters.

## Building

```sh
lake build          # build everything
lake build dqrat-lean   # build executable only
```

Binary: `.lake/build/bin/dqrat-lean <formula.dqdimacs> <proof.dqrat>`

## Next Proof Goals (Priority Order)

1. Prove `deleteIndependenceSetBridge_of_noDeleteCrossPathsSet` in `DeletionExhibition.lean` (see `sound_todo.md`)
3. Formalize DQRATE soundness: show each RAT blocker contributes a contradiction
4. Formalize DQRATU soundness: incorporate UR condition and path connectivity
5. Assemble `processProof_sound` via induction on proof steps
