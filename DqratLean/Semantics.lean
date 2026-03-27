import DqratLean.Formula
import DqratLean.ClauseStore

/-!
# Semantics of DQBF via Skolem Functions

A closed DQBF (Dependency Quantified Boolean Formula) consists of:

* **Universal variables** U = {u₁, …, uₙ},
* **Existential variables** E = {y₁, …, yₘ}, each with an explicit
  *dependency set* D(yᵢ) ⊆ U, and
* a **matrix** — a propositional formula in CNF over U ∪ E.

The formula is **true** iff there exist *Skolem functions*

    fᵢ : Bool^|D(yᵢ)| → Bool    (one per existential yᵢ)

such that, for **every** assignment σ : U → Bool, the matrix evaluates to `true`
after replacing each yᵢ with fᵢ(σ|_{D(yᵢ)}).

## Types

| Name               | Type                | Role                                      |
|--------------------|---------------------|-------------------------------------------|
| `UnivAssignment`   | `Var → Bool`        | assignment to the universal variables     |
| `SkolemFn`         | `Array Bool → Bool` | Skolem function for one existential       |
| `SkolemAssignment` | `Var → SkolemFn`    | one Skolem function per existential       |

## Dependency correctness

The Skolem function for yᵢ is called as `sk yᵢ (D(yᵢ).map σ)`: it receives
*exactly* the values of its declared dependencies.  It cannot observe universals
outside D(yᵢ), so the dependency constraint is enforced by construction.

`ValidSkolem` makes this explicit; `ValidSkolem.trivial` shows it costs nothing.
-/

-- ─── Core types ────────────────────────────────────────────────────────────

/-- Assignment to the universal variables.
    Only the values at universal variable indices are semantically meaningful;
    existential values are supplied entirely by the Skolem assignment. -/
abbrev UnivAssignment := Var → Bool

/-- Skolem function for one existential variable.
    Input: the Boolean values of the dependency variables, in `DQBF.depset` order.
    Output: the existential's Boolean value. -/
abbrev SkolemFn := Array Bool → Bool

/-- Maps each existential internal variable index to its Skolem function. -/
abbrev SkolemAssignment := Var → SkolemFn

-- ─── Variable and literal evaluation ───────────────────────────────────────

namespace DQBF

/-- Value of existential variable `v` under `σ` and `sk`.

    `sk v` is applied to `depset[v].map σ` — the values of `v`'s declared
    dependencies under `σ`.  The Skolem function therefore only ever sees the
    variables in D(v) and nothing outside them. -/
def exiValue (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment) (v : Var) : Bool :=
  sk v (f.depset.getD v #[] |>.map σ)

/-- Value of any variable under `σ` and `sk`:
    * **universal** → read from `σ` directly;
    * **existential** → computed via `exiValue`. -/
def varValue (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment) (v : Var) : Bool :=
  if f.isVarExistential v then f.exiValue σ sk v else σ v

/-- Value of literal `l`:  the variable's value, possibly negated. -/
def litValue (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment) (l : Literal) : Bool :=
  let b := f.varValue σ sk l.var
  if l.isPos then b else !b

/-- Value of a clause — a **disjunction** of literals.
    The empty clause has no satisfying literals and evaluates to `false`. -/
def clauseValue (f : DQBF) (σ : UnivAssignment) (sk : SkolemAssignment)
    (lits : Array Literal) : Bool :=
  lits.any (f.litValue σ sk)

end DQBF

-- ─── Matrix evaluation ─────────────────────────────────────────────────────

namespace ClauseStore

/-- Value of the CNF matrix — a **conjunction** of clauses — under `σ` and `sk`.

    Index 0 is the dummy CRef_Undef sentinel and is skipped.
    Deleted clauses are vacuously `true` (they have been removed from the formula). -/
def matrixValue (f : DQBF) (cs : ClauseStore) (σ : UnivAssignment) (sk : SkolemAssignment) :
    Bool :=
  (List.range (cs.clauses.size - 1)).all fun i =>
    match cs.getClause (i + 1) with   -- real clauses: indices 1 … size-1
    | none   => true                  -- deleted; no constraint
    | some c => f.clauseValue σ sk c.lits

end ClauseStore

-- ─── Validity of Skolem functions ──────────────────────────────────────────

/-- A Skolem assignment `sk` is *valid* for `f` if the value of each existential
    depends only on its declared dependency set: two universal assignments that agree
    on every variable in `depset[v]` must produce the same value for existential `v`.

    This is the semantic constraint that distinguishes DQBF from QBF: each existential
    has its own, possibly non-linear dependency set rather than depending on all
    preceding universals.

    **Remark.** Because `exiValue f σ sk v = sk v (depset[v].map σ)`, the Skolem
    function only ever receives `depset[v].map σ` as its argument.  Two assignments
    agreeing on `depset[v]` produce the same input array, hence the same output.
    `ValidSkolem` is therefore satisfied automatically — see `ValidSkolem.trivial`. -/
def ValidSkolem (f : DQBF) (sk : SkolemAssignment) : Prop :=
  ∀ v : Var, f.isVarExistential v →
    ∀ σ₁ σ₂ : UnivAssignment,
      (∀ u ∈ f.depset.getD v #[], σ₁ u = σ₂ u) →
      f.exiValue σ₁ sk v = f.exiValue σ₂ sk v

/-- Every Skolem assignment trivially satisfies `ValidSkolem`:
    `exiValue` only passes `depset[v].map σ` to the Skolem function, so the function
    cannot distinguish two assignments that agree on `depset[v]`. -/
theorem ValidSkolem.trivial (f : DQBF) (sk : SkolemAssignment) : ValidSkolem f sk := by
  intro v _ σ₁ σ₂ hAgree
  simp only [DQBF.exiValue]
  congr 1
  apply Array.ext (by simp [Array.size_map])
  intro i hi₁ _
  simp only [Array.getElem_map]
  have hi : i < (f.depset.getD v #[]).size := by simpa [Array.size_map] using hi₁
  exact hAgree _ (Array.getElem_mem hi)

-- ─── Truth and falsity predicates ──────────────────────────────────────────

/-- The DQBF formula `(f, cs)` is **true** iff there exists a Skolem assignment
    under which *every* universal assignment satisfies the matrix.

    This is the standard game-theoretic / Skolem-function characterisation:
    the existential player first commits to strategies `sk`, then the universal
    player picks `σ` adversarially; the existential player wins iff every clause
    in the matrix is satisfied. -/
def DQBFTrue (f : DQBF) (cs : ClauseStore) : Prop :=
  ∃ sk : SkolemAssignment,
    ∀ σ : UnivAssignment, cs.matrixValue f σ sk = true

/-- The formula is **false** iff it is not true — equivalently, for every Skolem
    assignment there exists a universal assignment that falsifies some clause. -/
def DQBFFalse (f : DQBF) (cs : ClauseStore) : Prop :=
  ∀ sk : SkolemAssignment,
    ∃ σ : UnivAssignment, cs.matrixValue f σ sk = false

-- ─── Basic lemmas ──────────────────────────────────────────────────────────

/-- A formula containing an empty (zero-literal) clause is always false:
    the empty disjunction is unsatisfiable under every assignment. -/
theorem DQBFFalse.of_empty_clause (f : DQBF) (cs : ClauseStore)
    (cref : CRef) (hcref : 1 ≤ cref) (hsize : cref < cs.clauses.size)
    (hempty : ∃ c, cs.getClause cref = some c ∧ c.lits = #[]) :
    DQBFFalse f cs := by
  obtain ⟨_c, hget, hlits⟩ := hempty
  intro sk
  refine ⟨fun _ => true, ?_⟩
  simp only [ClauseStore.matrixValue, List.all_eq_false]
  -- witness: cref - 1 is in range and the clause function returns false there
  refine ⟨cref - 1, List.mem_range.mpr ?_, ?_⟩
  · exact Nat.sub_lt_sub_right hcref hsize
  · have heq : cref - 1 + 1 = cref := Nat.succ_pred_eq_of_pos (Nat.lt_of_succ_le hcref)
    simp [heq, hget, hlits, DQBF.clauseValue]

/-- A formula with no clauses (empty matrix) is trivially true:
    the empty conjunction is vacuously satisfied by any Skolem assignment. -/
theorem DQBFTrue.of_empty_matrix (f : DQBF) (cs : ClauseStore)
    (h : cs.clauses.size ≤ 1) : DQBFTrue f cs := by
  refine ⟨fun _ _ => true, fun σ => ?_⟩
  simp [ClauseStore.matrixValue, show cs.clauses.size - 1 = 0 from by omega]
