# Reading the Lean development as a mathematician

One page of recurring notions; every docstring leans on these.

**DQBF semantics** (`Semantics.lean`). A universal assignment σ maps each
universal variable to a Boolean. A Skolem assignment `sk` gives each
existential variable x a function of the values of its dependency set D(x)
(`sk x` is applied to the vector of σ-values of D(x)). `varValue σ sk v` is
σ(v) for universal v and `sk x (σ restricted to D(x))` for existential x;
clauses are disjunctions, the matrix is their conjunction. The formula is
TRUE (`DQBFTrue`) iff some `sk` satisfies the matrix under every σ; FALSE
(`DQBFFalse`) iff every `sk` is beaten by some σ.

**Checker-state invariants** (`SoundnessCore.lean`), strongest last:
`Sound` (structural well-formedness of arrays/trail), `Correct` (Sound +
"action boundary": propagation queue empty, single trail level, all clause
literals in range, and the current formula/clauses are a truth-preserving
extension of the originals), `FullCorrect` (Correct + occurrence-list
completeness: every live clause is indexed under each of its literals —
the property the DQRATE argument genuinely needs; dropping it admits
counterexamples, see `Counterexamples.lean`).

**Hoare triples** (notation from `Std.Do`).
`⦃P⦄ prog ⦃⇓? r s' => Q⦄` reads: from ANY state satisfying P, running
`prog` either throws an exception — about which nothing is claimed — or
returns result `r` in state `s'` with Q holding. Soundness statements are
therefore "if the checker answers, the answer is right"; termination and
completeness are not claimed.

**Verdicts.** `.Verified` carries the semantic claim `DQBFFalse` for the
ORIGINAL parsed formula (a DQRAT refutation shows falsity). `.Failed` and
`.Unknown` carry no semantic claim — the checker may reject or give up on
valid proofs.

**Postconditions.** `FullStepPost`/`FullStepFullPost` package "invariant
preserved, and a Verified result implies `DQBFFalse`" for one proof action
(on the `Correct` / `FullCorrect` surface respectively); `ReadMatrixPost r s`
says: if matrix reading returned `r = true` (conflict while reading), the
parsed formula is already false; otherwise the state is `Correct`.

**Dependency deletion** (`Deletion*.lean`). The `e`-line may delete u from
D(x) when the checker's BFS (`getReachable`) certifies no "u-pure
resolution paths" connect both polarities of u to x
(`NoDeleteCrossPaths`). Soundness is the *full exhibition* of the
reflexive resolution-path dependency scheme: any model can be repaired
(two-stage "reform", copying values from the u-flipped half-space unless a
resolution path refuses it) into one whose Skolem functions ignore u.
Transcribed from Beyersdorff–Blinkhorn–Chew–Schmidt–Suda, JAR 63 (2019)
§6 — alignment table in `DeletionExhibition.lean`, paper in `docs/papers/`.
