import Std.Tactic.Do
import DqratLean.CheckState
import DqratLean.Semantics
open Std.Do

/-!
# MonadTutor — reasoning about `CheckM` programs

`CheckM = StateT CheckState (Except String)` is the workhorse monad of the DQBF
checker.  This file works through three layers of the `Std.Do` verification toolkit:

1. **`m*` tactics** — separation-logic proof mode for `SPred` goals
2. **`mspec`** — apply a single Hoare-triple spec to one program step
3. **`mvcgen`** — automated VC generation for whole structured programs

References
- Tactic API: `Std.Tactic.Do.Syntax` (https://lean-lang.org/doc/api/Std/Tactic/Do/Syntax.html)
- Tutorial:   `mvcgen` tactic tutorial (https://lean-lang.org/doc/tutorials/4.29.0-rc6/mvcgen/)
-/

-- ─── §1  The `m*` tactic family ─────────────────────────────────────────────
/-!
## §1  SPred reasoning with `m*` tactics

`SPred σs` is the type of *stateful predicates* over a list of state types `σs`.
Entailment `P ⊢ₛ Q` means "whenever `P` holds for a state, so does `Q`".

Pure Lean propositions are *lifted* into `SPred` via `⌜φ⌝ : SPred σs`.

The `m*` tactics mirror ordinary Lean tactics but work in the stateful proof mode
where hypotheses can be stateful (`h : P`) or pure (extracted via `mpure`).
-/

section SPredExamples
variable {σs : List Type} (P Q R : SPred σs) (p q : Prop)

-- ── mintro / mexact ──────────────────────────────────────────────────────────

-- `mintro h` introduces the left-hand side of `A ⊢ₛ B` as hypothesis `h`.
-- `mexact h` closes the goal when `h` matches.
example : P ⊢ₛ P := by
  mintro h
  mexact h

-- ── mintro with patterns: conjunction ────────────────────────────────────────

-- Conjunction patterns `⟨h₁, h₂⟩` work inside `mintro`, like `intro ⟨_, _⟩`.
example : P ∧ Q ⊢ₛ Q ∧ P := by
  mintro ⟨hp, hq⟩
  mconstructor
  · mexact hq
  · mexact hp

-- ── mleft / mright: choosing a disjunct ─────────────────────────────────────

example : P ⊢ₛ P ∨ Q := by mintro hp; mleft;  mexact hp
example : Q ⊢ₛ P ∨ Q := by mintro hq; mright; mexact hq

-- ── mcases: pattern-matching on a stateful hypothesis ────────────────────────

-- `⟨pat₁, pat₂⟩` destructs conjunctions; `⟨pat₁ | pat₂⟩` branches on disjunctions.
-- `_` discards; `⌜h⌝` extracts a pure fact to the Lean context.
example : P ∧ Q ∧ R ⊢ₛ R ∧ P := by
  mintro ⟨hp, _, hr⟩  -- `_` discards Q
  mconstructor
  · mexact hr
  · mexact hp

example : P ∨ Q ⊢ₛ Q ∨ P := by
  mintro h
  mcases h with ⟨hp | hq⟩
  · mright; mexact hp
  · mleft;  mexact hq

-- ── mexists: existential witnesses ───────────────────────────────────────────

example (ψ : Nat → SPred σs) : ψ 42 ⊢ₛ ∃ n, ψ n := by
  mintro h; mexists 42

-- ── mpure: move a `⌜φ⌝` hypothesis into the ordinary Lean context ─────────────

example (f : p → ⊢ₛ P) : ⌜p⌝ ⊢ₛ P := by
  mintro hp
  mpure hp   -- hp : p is now a plain Lean proof
  mexact f hp

-- ── mpure_intro: discharge a pure goal ───────────────────────────────────────

-- When the goal is `⊢ₛ ⌜φ⌝`, `mpure_intro` leaves the pure Lean goal `⊢ φ`.
-- Note: here the "precondition" is implicit ⊤ (vacuously true).
example : ⊢ₛ (⌜True⌝ : SPred σs) := by
  mpure_intro
  trivial

-- ── mhave: intermediate stateful fact ────────────────────────────────────────

-- `mhave h : T := by ...` is the stateful analog of `have`.
example : P ⊢ₛ (P → Q) → Q := by
  mintro hp hpq
  mhave hq : Q := by mspecialize hpq hp; mexact hpq
  mexact hq

-- ── mspecialize ──────────────────────────────────────────────────────────────

-- `mspecialize h arg` instantiates a stateful implication with `arg`.
example : P ⊢ₛ (P → Q) → Q := by
  mintro hp hpq
  mspecialize hpq hp
  mexact hpq

-- ── mrevert ──────────────────────────────────────────────────────────────────

-- `mrevert h` is the inverse of `mintro h`.
example : P ∧ Q ⊢ₛ Q := by
  mintro ⟨_, hq⟩
  mrevert hq
  mintro hq'
  mexact hq'

-- ── mrefine ──────────────────────────────────────────────────────────────────

-- `mrefine pat` constructs a stateful term with pattern syntax.
example : P ∧ Q ⊢ₛ Q ∧ P := by
  mintro ⟨hp, hq⟩
  mrefine ⟨hq, hp⟩

-- ── mexfalso ─────────────────────────────────────────────────────────────────

-- If we have `⌜False⌝`, any goal follows.
example : ⌜False⌝ ⊢ₛ P := by
  mintro hf
  mexfalso
  mexact hf

end SPredExamples

-- ─── §2  Hoare triples for `CheckM` ────────────────────────────────────────
/-!
## §2  Hoare Triples

A Hoare triple `⦃P⦄ prog ⦃⇓ r s' => Q r s'⦄` means:
- If precondition `P s₀` holds for the initial state `s₀`,
- and `prog` runs to successful completion with result `r` and final state `s₁`,
- then postcondition `Q r s₁` holds.

**Relationship to `⊢ₛ`**: A Hoare triple is literally an `SPred` entailment:
```lean
def Triple [WP m ps] (x : m α) (P : Assertion ps) (Q : PostCond α ps) : Prop :=
  P ⊢ₛ wp⟦x⟧ Q
```
-/
#print Triple
/-
So `⦃P⦄ prog ⦃Q⦄` means "precondition `P` entails the *weakest precondition*
of `prog` for postcondition `Q`".  For `CheckM`, this unfolded reads:
`∀ s, P s → wp⟦prog⟧ Q s`.  The `m*` tactics from §1 work directly on `⊢ₛ`
goals, so in principle a Hoare triple could be proved with `mintro`/`mexact`;
in practice `mvcgen` (which automates the WP reasoning) is always easier.

For `CheckM = StateT CheckState (Except String)`, preconditions/postconditions
are functions `CheckState → Prop`, typically written `fun s => ⌜prop(s)⌝`.

**Ghost variables**: Parameters like `n : Nat` capture properties of the initial
state so the postcondition can mention them.  This is the standard trick for
relating final states to initial states:

```
@[spec] theorem f_spec (n : Nat) :
    ⦃fun s => ⌜s.someField = n⌝⦄       -- precondition captures n from initial state
    (f : CheckM Unit)
    ⦃⇓ _ s' => ⌜s'.someField = n + 1⌝⦄  -- postcondition uses captured n
```

### Postconditions: `⇓` vs `⇓?`

The two postcondition forms differ in how they treat exceptions:

|           Syntax           |       Long name     |                       On exception                      |
|----------------------------|---------------------|---------------------------------------------------------|
| `⦃P⦄ prog ⦃⇓ r s' => Q⦄`  | `PostCond.noThrow`  | **Forbidden** — triple implies `False` if `prog` throws |
| `⦃P⦄ prog ⦃⇓? r s' => Q⦄` | `PostCond.mayThrow` | **Vacuous** — nothing is asserted when `prog` throws    |

Internally, the distinction is in the *exception condition*:
```lean
PostCond.noThrow p = (p, ExceptConds.false)  -- exception postcond = ⌜False⌝
PostCond.mayThrow p = (p, ExceptConds.true)   -- exception postcond = ⌜True⌝
```

`⇓` (noThrow) encodes **total correctness**: the program must succeed *and* Q holds.
`⇓?` (mayThrow) encodes **partial correctness**: Q is only asserted on success.

All checker operations in this file use `⇓` because they are total — they cannot
throw under the assumed invariants.  Use `⇓?` when checking that a function *may*
throw (e.g. for negative-test specs).
-/

-- ── §2.1  Primitive operation specs ──────────────────────────────────────────

-- `pure v` leaves the state unchanged and returns `v`.
example {α : Type} (v : α) :
    ⦃fun _ => ⌜True⌝⦄
    (pure v : CheckM α)
    ⦃⇓ r _ => ⌜r = v⌝⦄ := by
  mvcgen

-- `get` returns the current state.
example :
    ⦃fun _ => ⌜True⌝⦄
    (get : CheckM CheckState)
    ⦃⇓ r s' => ⌜r = s'⌝⦄ := by
  mvcgen

-- `set s'` replaces the state with `s'`.
example (s' : CheckState) :
    ⦃fun _ => ⌜True⌝⦄
    (set s' : CheckM Unit)
    ⦃⇓ _ s'' => ⌜s'' = s'⌝⦄ := by
  mvcgen

-- ── §2.2  `modify` and ghost variables ───────────────────────────────────────

-- For `modify f`, we capture a property of the initial state via a ghost variable.
-- The VCs (Verification Conditions: sub-goals left after mvcgen decomposes the
-- triple) are ground propositions; use `grind` to close them.

-- After `mvcgen`, the VC has a let-binding `t✝` for the modified state:
--   t✝ : PUnit × CheckState := ((), { ..., trail := s✝.trail.push #[], ... })
--   ⊢ t✝.snd.trail.size = n + 1
-- `grind` unfolds the transparent let `t✝`, applies Array.size_push, and closes
-- with the hypothesis h✝ : s✝.trail.size = n.
--
-- To name inaccessible variables (h✝, s✝) that `mvcgen` leaves behind, use
-- `rename_i` before applying a tactic that needs them explicitly:
example (n : Nat) :
    ⦃fun s => ⌜s.trail.size = n⌝⦄
    (modify (fun st => { st with trail := st.trail.push #[] }) : CheckM Unit)
    ⦃⇓ _ s' => ⌜s'.trail.size = n + 1⌝⦄ := by
  mvcgen
  -- Goal (schematically): let t✝ := ...; t✝.snd.trail.size = n + 1
  -- Hypotheses: s✝ : CheckState, h✝ : s✝.trail.size = n
  -- `rename_i s₀ h₀` gives them readable names before the closing tactic:
  rename_i s₀ h₀
  -- Now h₀ : s₀.trail.size = n.  `grind` handles the let-bound intermediate:
  grind

-- ── §2.3  Sequencing ─────────────────────────────────────────────────────────

-- `mvcgen` decomposes sequential `do`-programs.  Both pushes are visible in the VC.
example (n : Nat) :
    ⦃fun s => ⌜s.trail.size = n⌝⦄
    (do modify (fun st => { st with trail := st.trail.push #[] })
        modify (fun st => { st with trail := st.trail.push #[] })
        : CheckM Unit)
    ⦃⇓ _ s' => ⌜s'.trail.size = n + 2⌝⦄ := by
  mvcgen
  grind

-- ─── §3  Registering specs with `@[spec]` ───────────────────────────────────
/-!
## §3  Registering Specs

Tag a theorem with `@[spec]` so that `mvcgen` applies it automatically whenever
it encounters the corresponding function.

Proof structure:
1. `mvcgen [f]` — generate while unfolding `f` VCs
   sometimes explicit unfold is necessary in two steps `unfold f; mvcgen`
2. Close VCs with `grind` (handles let-bound intermediates) or `lia` for arithmetic

The `mvcgen_trivial` tactic (called internally by `mvcgen`) automatically closes
VCs that are immediately provable via `trivial`.
-/

/-- `newDecisionLevel` pushes an empty trail entry; the trail grows by exactly 1. -/
@[spec]
theorem newDecisionLevel_spec (n : Nat) :
    ⦃fun s => ⌜s.trail.size = n⌝⦄
    (newDecisionLevel : CheckM Unit)
    ⦃⇓ _ s' => ⌜s'.trail.size = n + 1⌝⦄ := by
  mvcgen [newDecisionLevel]
  -- VC: t✝.snd.trail.size = n + 1  where t✝.snd.trail = s✝.trail.push #[]
  -- `grind` handles the let-bound t✝ and the Array.size_push fact automatically.
  grind

-- ─── §4  Proving a spec for `enqueue` ───────────────────────────────────────
/-!
## §4  Specs for `enqueue`

`enqueue` has three branches:
1. **Out-of-range** (`v = 0` or `v > maxVar`): `return ()`, state unchanged.
2. **Already assigned** (`isAssigned[v-1] = true`): `return ()`, state unchanged.
3. **Actually enqueue**: updates `isAssigned`, `value`, `trail`, `propQueue`.

`mvcgen` splits on the `if`-guards automatically.  `mvcgen_trivial` closes the
two early-return VCs automatically (state unchanged → precondition holds).
Only the third VC remains, requiring `setIfInBounds` size preservation.
-/

/-- `enqueue` does not change the sizes of `isAssigned` or `value`. -/
@[spec]
theorem enqueue_preserves_sizes (l : Literal) (n : Nat) :
    ⦃fun s => ⌜s.isAssigned.size = n ∧ s.value.size = n⌝⦄
    (enqueue l : CheckM Unit)
    ⦃⇓ _ s' => ⌜s'.isAssigned.size = n ∧ s'.value.size = n⌝⦄ := by
  unfold enqueue; mvcgen
  -- mvcgen_trivial closed the two early-return VCs automatically.
  -- One VC remains: the actual-enqueue branch.
  grind

-- ─── §5  Compositional reasoning ────────────────────────────────────────────
/-!
## §5  Compositional Reasoning

Once `@[spec]` theorems are registered, `mvcgen` applies them automatically
without re-reading function bodies.
-/

/-- Two consecutive decision levels grow the trail by 2.
    `mvcgen` applies `newDecisionLevel_spec` twice via the registered spec. -/
theorem two_levels_spec (n : Nat) :
    ⦃fun s => ⌜s.trail.size = n⌝⦄
    (do newDecisionLevel; newDecisionLevel : CheckM Unit)
    ⦃⇓ _ s' => ⌜s'.trail.size = n + 2⌝⦄ := by
  mvcgen
  omega

-- ── §5.2  Loops and invariants ────────────────────────────────────────────────
/-!
### Loops and Invariants

For `for` loops, `mvcgen invariants` asks for a *loop invariant*.
The invariant must:
- Hold initially,
- Be preserved by each loop body (the step VC),
- Imply the postcondition when the loop finishes.

Syntax:
```lean
mvcgen invariants
· ⇓⟨xs, acc⟩ state => ⌜invariant_about xs.prefix state acc⌝
  with tactic_to_close_VCs
```
`xs` is the `ForInRange.RangeIterator` capturing how far we've iterated.
`xs.prefix` is the prefix of iterations completed so far.
-/

/-- Helper: push `k` decision levels onto the trail. -/
def pushNLevels (k : Nat) : CheckM Unit :=
  for _ in [:k] do newDecisionLevel

/-- After `pushNLevels k`, the trail has grown by exactly `k`. -/
theorem pushNLevels_spec (k : Nat) (n : Nat) :
    ⦃fun s => ⌜s.trail.size = n⌝⦄
    (pushNLevels k : CheckM Unit)
    ⦃⇓ _ s' => ⌜s'.trail.size = n + k⌝⦄ := by
  mvcgen [pushNLevels] invariants
  -- Invariant: after `xs.prefix.length` iterations, trail size = n + that count
  · ⇓⟨xs, ()⟩ s => ⌜s.trail.size = n + xs.prefix.length⌝
    with grind

-- ─── §6  `mspec`: single-step specification application ─────────────────────
/-!
## §6  `mspec`

`mvcgen` is fully automated: it introduces preconditions, decomposes binds, applies
`@[spec]` theorems, and runs `mleave` on every generated VC.  `mspec` does exactly
one of those steps — applying a single specification — and leaves everything else
to the user.

`mspec` expects the goal to already be a *stateful target* `H ⊢ₛ wp⟦prog⟧ Q`.
Calling `mspec` directly on a fresh `⦃P⦄ prog ⦃Q⦄` (equivalently `P ⊢ₛ wp⟦prog⟧ Q`)
fails because the precondition `P` has not yet been introduced into the stateful
context `H`.  Fix it by calling `mintro` first.

The two proofs below are equivalent; the second spells out the three `mspec` steps
that `mvcgen` performs internally:

| step | `mvcgen` (automatic)                 | `mspec` (manual)              |
|------|--------------------------------------|-------------------------------|
| 1    | intro precondition                   | `mintro h`                    |
| 2    | `newDecisionLevel` + bind decompose  | `mspec newDecisionLevel_spec` |
| 3    | second `newDecisionLevel`            | `mspec newDecisionLevel_spec` |
| 4    | `mleave` + close VC                  | `mleave; omega`               |

Note that `mspec spec` automatically decomposes `x >>= f` before matching `spec`
against `x`; use `mspec_no_bind spec` to skip the bind decomposition.
-/

-- Fully automated: `mvcgen` handles intro, bind, specs, and mleave internally.
theorem two_levels_mvcgen (n : Nat) :
    ⦃fun s => ⌜s.trail.size = n⌝⦄
    (do newDecisionLevel; newDecisionLevel : CheckM Unit)
    ⦃⇓ _ s' => ⌜s'.trail.size = n + 2⌝⦄ := by
  mvcgen
  omega

-- Manual: each `mspec` call handles one specification step.
theorem two_levels_mspec (n : Nat) :
    ⦃fun s => ⌜s.trail.size = n⌝⦄
    (do newDecisionLevel; newDecisionLevel : CheckM Unit)
    ⦃⇓ _ s' => ⌜s'.trail.size = n + 2⌝⦄ := by
  mintro h                      -- introduce precondition into stateful context
  mspec newDecisionLevel_spec   -- apply spec for first newDecisionLevel (+ bind)
  mspec newDecisionLevel_spec   -- apply spec for second newDecisionLevel
  mleave; omega                 -- discharge remaining arithmetic VC

-- ─── §7  From Hoare Triples to `prog.run` ────────────────────────────────────
/-!
## §7  From `@[spec]` to `prog.run`

A Hoare triple `⦃P⦄ prog ⦃⇓ r s' => ⌜Q r s'⌝⦄` is `P ⊢ₛ wp⟦prog⟧ Q`.
For `CheckM`, `wp⟦prog⟧ Q st` reduces to:
```
match prog.run st with
| .ok (a, s') => Q.1 a s'   -- success: postcondition Q holds
| .error _   => Q.2.1 _     -- noThrow (⇓): False; mayThrow (⇓?): True
```

To convert between a Hoare triple and a fact about `run`, we need
to unfold both sides, for example as follows.
-/

theorem triple_to_run (prog : CheckM Bool) (st : CheckState)
    (h : ⦃fun s => ⌜s = st⌝⦄ prog ⦃⇓ r _s => ⌜r = true⌝⦄) :
    match prog.run' st with
    | .some x => x = true
    | .none => False := by
  -- unfold the Hoare triple
  specialize h st rfl -- plug in the initial state & the initial condition
  simp only [WP.wp, PredTrans.apply] at h -- uncover `match` at `h`
  simp only [EStateM.run'] -- uncover `match` at `prog.run`
  split at h
  · rename_i a s heq -- case result
    simp only [heq]
    exact h
  · rename_i a s heq -- error is guaranteed not to happen by the hoare triple
    exfalso
    exact h
