import DqratLean.Types
import DqratLean.Formula
import DqratLean.ClauseStore
import Std.Tactic.Do
open Std.Do

-- Combined checker state
structure CheckState where
  formula    : DQBF
  clauses    : ClauseStore
  -- Assignment arrays indexed by (var - 1)
  isAssigned : Array Bool         -- is variable assigned?
  value      : Array Bool         -- assigned value (meaningful if isAssigned)
  -- Trail: decision levels; each level is a list of literals assigned at that level
  trail      : Array (Array Literal) := #[#[]]  -- start with level 0
  -- Propagation queue (LIFO)
  propQueue  : Array Literal := #[]
  -- Independence cache indexed by (univar - 1)
  indepKnown : Array Bool := #[]
  indepOf    : Array (Array Var) := #[]   -- existential vars independent of this univar

abbrev CheckM := EStateM String CheckState

-- ─── Assignment helpers ────────────────────────────────────────────────────

def satisfied (st : CheckState) (l : Literal) : Bool :=
  let v := l.var
  v > 0 && v <= st.formula.maxVar &&
  st.isAssigned.getD (v - 1) false &&
  (st.value.getD (v - 1) false == l.isPos)

def isAssigned (st : CheckState) (v : Var) : Bool :=
  v > 0 && v <= st.formula.maxVar &&
  st.isAssigned.getD (v - 1) false

-- ─── Trail / decision level management ────────────────────────────────────

def newDecisionLevel : CheckM Unit :=
  modify fun st => { st with trail := st.trail.push #[] }

def backtrackBefore (level : Nat) : CheckM Unit :=
  modify fun st =>
    let rec clearLevels (tr : Array (Array Literal)) (ia : Array Bool) :
        Array (Array Literal) × Array Bool :=
      if tr.size <= level then (tr, ia)
      else
        let lvl := tr.getD (tr.size - 1) #[]
        let ia' := lvl.foldl (fun acc l =>
          let v := l.var
          if v > 0 then acc.setIfInBounds (v - 1) false else acc
        ) ia
        clearLevels tr.pop ia'
    termination_by tr.size
    let (trail', isAssigned') := clearLevels st.trail st.isAssigned
    { st with trail := trail', isAssigned := isAssigned', propQueue := #[] }

-- ─── Enqueue ───────────────────────────────────────────────────────────────

def enqueue (l : Literal) : CheckM Unit := do
  let st ← get
  let v := l.var
  if v = 0 || v > st.formula.maxVar then return ()
  if v - 1 >= st.isAssigned.size then return ()
  if st.isAssigned.getD (v - 1) false then return ()
  let lastIdx := st.trail.size - 1
  let lastLevel := st.trail.getD lastIdx #[]
  set { st with
    isAssigned := st.isAssigned.setIfInBounds (v - 1) true
    value      := st.value.setIfInBounds      (v - 1) l.isPos
    trail      := st.trail.setIfInBounds      lastIdx (lastLevel.push l)
    propQueue  := st.propQueue.push l
  }

-- `enqueue` preserves propQueue.size + isAssigned.count false.
-- Key: the bounds guard `v - 1 >= isAssigned.size → return ()` ensures setIfInBounds
-- is always in-bounds in the actual-enqueue branch, so push +1 and count false -1 cancel.
theorem enqueue_measure_spec (l : Literal) (m : Nat) :
    ⦃fun s => ⌜s.propQueue.size + s.isAssigned.count false = m⌝⦄
    (enqueue l : CheckM Unit)
    ⦃⇓ _ s' => ⌜s'.propQueue.size + s'.isAssigned.count false = m⌝⦄ := by
  mvcgen [enqueue]
  -- rename_i goes oldest→newest; positions: 1=state, 2=measure, 3=var,
  -- 4-6=do_jp/guard/do_jp, 7=bounds_check, 8=do_jp, 9=assigned_check, 10-11=let-bindings
  rename_i s hm v _ _ _ s0 _ hv _ _
  -- s : CheckState, hm : measure, v : Var := l.var
  -- s0 : ¬(v - 1 ≥ s.isAssigned.size), hv : ¬isAssigned.getD (v-1) false = true
  have hlt := Nat.lt_of_not_le s0
  simp only [Bool.not_eq_true] at hv
  -- hv : s.isAssigned.getD (v-1) false = false
  simp only [Array.size_push, Array.setIfInBounds_def, dif_pos hlt, Array.count_set hlt]
  -- count_set uses getElem notation; convert to getD via one rw (avoids simp loop)
  rw [Array.getElem_eq_getD (fallback := false)]
  simp only [hv, show (false == false) = true from rfl, show (true == false) = false from rfl,
             ↓reduceIte, show (false = true) = False from by decide]
  -- goal: s.propQueue.size + 1 + (Array.count false s.isAssigned - 1) = m
  have hpos : 1 ≤ Array.count false s.isAssigned := by
    have hmem := Array.getElem_mem hlt
    rw [Array.getElem_eq_getD (fallback := false), hv] at hmem
    exact Array.one_le_count_iff.mpr hmem
  omega

-- ─── Occurrence-list unit propagation ─────────────────────────────────────

-- Process one propagated literal: check all clauses containing its negation
-- Returns Some cref on conflict, None on success
def propagateOne (l : Literal) : CheckM (Option CRef) := do
  let negL := l.negate
  let st ← get
  let occs := st.clauses.getOcc negL
  occs.foldlM (fun acc cref => do
    match acc with
    | some _ => return acc
    | none =>
      let st ← get
      match st.clauses.getClause cref with
      | none => return none  -- deleted or invalid
      | some clause =>
        -- Check if clause is satisfied
        let sat := clause.lits.any fun lit =>
          let v := lit.var
          v > 0 && v <= st.formula.maxVar &&
          st.isAssigned.getD (v - 1) false &&
          (st.value.getD (v - 1) false == lit.isPos)
        if sat then return none
        -- Find unassigned literals
        let unassigned := clause.lits.filter fun lit =>
          let v := lit.var
          v > 0 && v <= st.formula.maxVar &&
          !st.isAssigned.getD (v - 1) false
        if unassigned.isEmpty then
          return some cref  -- all literals false = conflict
        else if unassigned.size = 1 then
          enqueue (unassigned.getD 0 ⟨0⟩)
          return none
        else
          return none
  ) none

-- `propagateOne` preserves the measure (propQueue.size + isAssigned.count false).
-- The only state-changing call inside is `enqueue`, which preserves by enqueue_measure_spec.
theorem propagateOne_measure_spec (l : Literal) (m : Nat) :
    ⦃fun s => ⌜s.propQueue.size + s.isAssigned.count false = m⌝⦄
    (propagateOne l : CheckM (Option CRef))
    ⦃⇓? _ s' => ⌜s'.propQueue.size + s'.isAssigned.count false = m⌝⦄ := by
  mvcgen [propagateOne, enqueue_measure_spec] invariants
  · ⇓⟨_, _⟩ s => ⌜s.propQueue.size + s.isAssigned.count false = m⌝
    with all_goals (first | assumption | omega | (intro; assumption))

-- `propagate`: unit-propagate until the queue is empty or a conflict is found.
-- Termination: each iteration pops one literal (measure -1) and enqueue preserves
-- the measure, so propQueue.size + isAssigned.count false decreases by exactly 1.
def propagate : CheckM (Option CRef) := fun st => aux st
where
  aux (st : CheckState) : EStateM.Result String CheckState (Option CRef) :=
    if st.propQueue.isEmpty then .ok none st
    else
      let l  := st.propQueue.getD (st.propQueue.size - 1) ⟨0⟩
      let s₁ := { st with propQueue := st.propQueue.pop }
      match hm : (propagateOne l) s₁ with
      | .error e s => .error e s
      | .ok (some c) s => .ok (some c) s
      | .ok none s => aux s
  termination_by st.propQueue.size + st.isAssigned.count false
  decreasing_by
    -- hm : (propagateOne l) s₁ = .ok none s (named via 'match hm : ...')
    rename_i hne
    -- hne : ¬st.propQueue.isEmpty = true
    -- propagateOne preserves measure: s.propQueue.size + s.isAssigned.count false
    --   = s₁.propQueue.size + s₁.isAssigned.count false
    have hmeas : s.propQueue.size + s.isAssigned.count false
               = s₁.propQueue.size + s₁.isAssigned.count false := by
      have hspec := propagateOne_measure_spec l (s₁.propQueue.size + s₁.isAssigned.count false)
      specialize hspec s₁ rfl
      simp only [WP.wp, PredTrans.apply, EStateM.run] at hspec
      rw [hm] at hspec
      exact hspec
    -- s₁ = st with propQueue popped: s₁.propQueue.size = st.propQueue.size - 1
    have hpop : s₁.propQueue.size = st.propQueue.size - 1 := by
      simp [s₁, Array.size_pop]
    -- hne: propQueue non-empty, so size ≥ 1
    have hpos : 0 < st.propQueue.size := by
      simp only [Array.isEmpty_iff_size_eq_zero] at hne
      omega
    -- s₁.isAssigned = st.isAssigned (only propQueue changed)
    have hisac : s₁.isAssigned.count false = st.isAssigned.count false := rfl
    omega

-- ─── BFS reachability for D^∀-pure dep scheme ─────────────────────────────

-- Compute reachable literals starting from literal l (for universal l).
-- reachable[lit.x] = true if lit can be reached via u-pure paths in clauses.
def getReachable (st : CheckState) (l : Literal) : Array Bool :=
  let numLits := st.formula.maxVar * 2 + 2
  let lvar    := l.var
  -- Only meaningful for universal l
  if st.formula.isVarExistential lvar then
    (List.replicate numLits true).toArray  -- existential: all reachable (conservative)
  else
    let negL   := l.negate
    let reachable := (List.replicate numLits false).toArray
    let explored  := (List.replicate numLits false).toArray
    -- BFS/DFS: terminates because each literal is explored at most once.
    -- Measure: (unexplored count, worklist size) in lexicographic order.
    let rec go (worklist : Array Literal) (reach expl : Array Bool) : Array Bool :=
      if worklist.isEmpty then reach
      else
        let cur  := worklist.getD (worklist.size - 1) ⟨0⟩
        let wl'  := worklist.pop
        let idx  := cur.x
        if expl.getD idx false then
          -- already explored or out-of-bounds default: skip, worklist shrinks
          go wl' reach expl
        else if h : idx < expl.size then
          -- newly explored: mark and process
          let expl' := expl.set idx true h
          let occs := st.clauses.getOcc cur
          let (wl'', reach') := occs.foldl (fun (wl, rch) cref =>
            match st.clauses.getClauseRaw cref with
            | none => (wl, rch)
            | some clause =>
              if clause.deleted then (wl, rch)
              else if clause.lits.contains negL then (wl, rch)
              else
                clause.lits.foldl (fun (wl2, rch2) lit =>
                  if lit = cur then (wl2, rch2)
                  else if expl'.getD lit.negate.x false then (wl2, rch2)
                  else
                    let litvar   := lit.var
                    let litIsExi := st.formula.isVarExistential litvar
                    let depset   := st.formula.depset.getD litvar #[]
                    let dependsOnL := depset.contains lvar
                    let wl3 := if litIsExi && dependsOnL then wl2.push lit.negate else wl2
                    let rch3 := if litIsExi && dependsOnL then
                      rch2.setIfInBounds lit.x true else rch2
                    (wl3, rch3)
                ) (wl, rch)
          ) (wl', reach)
          go wl'' reach' expl'
        else
          -- idx ≥ expl.size: out-of-bounds literal, skip (setIfInBounds is no-op)
          go wl' reach expl
    termination_by (expl.count false, worklist.size)
    decreasing_by
      · -- skip: already explored, worklist shrinks
        simp_wf; apply Prod.Lex.right
        have hne : worklist.size ≠ 0 := fun hz => ‹¬_› (by simp [Array.isEmpty, hz])
        lia
      · -- newly explored: expl gains one true, so countP (! ·) decreases
        simp_wf; apply Prod.Lex.left
        rename ¬expl.getD idx false = true => hval
        simp only [Bool.not_eq_true] at hval
        rw [←Array.getElem_eq_getD (h := h)] at hval
        have hpos : 0 < expl.count false :=
          Array.count_pos_iff.mpr (Array.mem_of_getElem hval)
        simp only [Array.count_set]
        simp only [beq_false, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          Nat.add_zero, gt_iff_lt]
        simp only [← Array.getD_eq_getD_getElem?]
        rw [hval]
        simp [Nat.sub_one_lt_of_lt hpos]
      · -- out-of-bounds: expl unchanged, worklist shrinks
        simp_wf; apply Prod.Lex.right
        have hne : worklist.size ≠ 0 := fun hz =>
          ‹¬worklist.isEmpty› (by simp [Array.isEmpty, hz])
        lia
    go #[l] reachable explored

-- ─── Independence cache management ────────────────────────────────────────

def makeIndepUnknown (univar : Var) : CheckM Unit :=
  if univar = 0 then return ()
  else modify fun st =>
    { st with
      indepKnown := st.indepKnown.setIfInBounds (univar - 1) false
      indepOf    := st.indepOf.setIfInBounds    (univar - 1) #[]
    }

-- Compute and cache independence for universal var v
def computeDeps (v : Var) : CheckM Unit := do
  let st ← get
  if st.formula.isVarExistential v then return ()  -- only for universals
  let reachPos := getReachable st (mkLit v true)
  let reachNeg := getReachable st (mkLit v false)
  -- Collect existential vars with internal index > v that are independent
  let indep := st.formula.exivars.filter fun xvar =>
    if xvar <= v then false
    else
      let xNeg := xvar * 2      -- negative literal index
      let xPos := xvar * 2 + 1  -- positive literal index
      -- dependent if there's a path from pos(v) to neg(xvar) and neg(v) to pos(xvar)
      --          or from pos(v) to pos(xvar) and neg(v) to neg(xvar)
      -- independent = NOT dependent
      !((reachPos.getD xNeg false && reachNeg.getD xPos false) ||
        (reachPos.getD xPos false && reachNeg.getD xNeg false))
  modify fun s =>
    { s with
      indepKnown := s.indepKnown.setIfInBounds (v - 1) true
      indepOf    := s.indepOf.setIfInBounds    (v - 1) indep
    }

-- Check if existential exiVar does NOT depend on universal univar
-- (using and lazily computing the independence cache)
def notDependsOn (exiVar univar : Var) : CheckM Bool := do
  let st ← get
  let idx := univar - 1
  if !st.indepKnown.getD idx false then
    computeDeps univar
  let st ← get
  let indep := st.indepOf.getD idx #[]
  return indep.contains exiVar

-- Invalidate independence cache for all universals in dep-union of exi vars in clause
def invalidateDepCaches (lits : Array Literal) : CheckM Unit := do
  let st ← get
  for l in lits do
    let v := l.var
    if v > 0 && st.formula.isVarExistential v then
      let deps := st.formula.depset.getD v #[]
      for u in deps do
        makeIndepUnknown u

/-- `SameFC s₀ s₁` means `s₁` has the same formula and clause store as `s₀`. -/
def SameFC (s₀ s₁ : CheckState) : Prop :=
  s₁.formula = s₀.formula ∧ s₁.clauses = s₀.clauses

theorem sameFC_trans {s₀ s₁ s₂ : CheckState}
    (h₀₁ : SameFC s₀ s₁) (h₁₂ : SameFC s₁ s₂) : SameFC s₀ s₂ := by
  rcases h₀₁ with ⟨hformula₀₁, hclauses₀₁⟩
  rcases h₁₂ with ⟨hformula₁₂, hclauses₁₂⟩
  exact ⟨hformula₁₂.trans hformula₀₁, hclauses₁₂.trans hclauses₀₁⟩

theorem makeIndepUnknown_sameFC_spec (u : Var) (s₀ : CheckState) :
    ⦃fun s => ⌜SameFC s₀ s⌝⦄
    (makeIndepUnknown u : CheckM Unit)
    ⦃⇓ _ s' => ⌜SameFC s₀ s'⌝⦄ := by
  intro s hsame
  rcases hsame with ⟨hformula, hclauses⟩
  unfold makeIndepUnknown
  by_cases hu : u = 0
  · simp [hu, SameFC, hformula, hclauses]
  · simp [hu, SameFC, hformula, hclauses]

theorem invalidateDepCaches_sameFC_spec (lits : Array Literal) (s₀ : CheckState) :
    ⦃fun s => ⌜SameFC s₀ s⌝⦄
    (invalidateDepCaches lits : CheckM Unit)
    ⦃⇓ _ s' => ⌜SameFC s₀ s'⌝⦄ := by
  intro s hsame
  have hfor :
      ⦃fun s' => ⌜SameFC s₀ s'⌝⦄
      (forIn lits.toList PUnit.unit (fun l _ => do
        let v := l.var
        if v > 0 && s.formula.isVarExistential v then
          let _ ← forIn (s.formula.depset.getD v #[]).toList PUnit.unit (fun u _ => do
            makeIndepUnknown u
            pure (ForInStep.yield PUnit.unit))
          pure (ForInStep.yield PUnit.unit)
        else
          pure (ForInStep.yield PUnit.unit)) : CheckM PUnit)
      ⦃⇓ _ s' => ⌜SameFC s₀ s'⌝⦄ := by
    refine (Spec.forIn_list_const_inv
      (xs := lits.toList)
      (init := PUnit.unit)
      (f := fun l _ => do
        let v := l.var
        if v > 0 && s.formula.isVarExistential v then
          let _ ← forIn (s.formula.depset.getD v #[]).toList PUnit.unit (fun u _ => do
            makeIndepUnknown u
            pure (ForInStep.yield PUnit.unit))
          pure (ForInStep.yield PUnit.unit)
        else
          pure (ForInStep.yield PUnit.unit))
      (inv := (⇓ _ s' => ⌜SameFC s₀ s'⌝))
      ?_)
    intro l b
    cases b
    mvcgen [makeIndepUnknown_sameFC_spec] invariants
    · ⇓⟨xs, ()⟩ s' => ⌜SameFC s₀ s'⌝
      with all_goals first | assumption | exact sameFC_trans ‹_› ‹_› | exact ‹_›
  simpa [invalidateDepCaches, Array.forIn_toList] using hfor s hsame

-- ─── Variable addition (updates all state arrays) ─────────────────────────

def addVarForall (ext : Nat) : CheckM Var := do
  let st ← get
  let v := st.formula.maxVar + 1
  let f := { st.formula with
    maxVar       := v
    internalName := st.formula.internalName.push (ext, v)
    externalName := st.formula.externalName.push ext
    isExistential := st.formula.isExistential.push false
    univars      := st.formula.univars.push v
    depset       := st.formula.depset.push #[]
  }
  set { st with
    formula    := f
    isAssigned := st.isAssigned.push false
    value      := st.value.push false
    indepKnown := st.indepKnown.push false
    indepOf    := st.indepOf.push #[]
  }
  return v

def addVarExists (ext : Nat) (deps : Array Var) : CheckM Var := do
  let st ← get
  let v := st.formula.maxVar + 1
  let f := { st.formula with
    maxVar        := v
    internalName  := st.formula.internalName.push (ext, v)
    externalName  := st.formula.externalName.push ext
    isExistential := st.formula.isExistential.push true
    exivars       := st.formula.exivars.push v
    depset        := st.formula.depset.push deps
  }
  set { st with
    formula    := f
    isAssigned := st.isAssigned.push false
    value      := st.value.push false
    indepKnown := st.indepKnown.push false
    indepOf    := st.indepOf.push #[]
  }
  -- Invalidate independence cache for each universal in the initial dep set
  for u in deps do
    makeIndepUnknown u
  return v

/-- Forget all current propagation state and return to a clean action boundary.
    Formula, clause store, and independence caches are preserved. -/
def resetPropagationState : CheckM Unit := do
  let st ← get
  let n := st.formula.maxVar
  set { st with
    isAssigned := Array.replicate n false
    value      := Array.replicate n false
    trail      := #[#[]]
    propQueue  := #[] }

-- Add a dependency: existential of_ now depends on universal on_
-- Matches C++ addDependency behavior (no-op if on_ is existential)
def addDependency (of_ on_ : Var) : CheckM Unit := do
  let st ← get
  if !st.formula.isVarExistential of_ then return ()
  if st.formula.isVarExistential on_ then return ()  -- C++ bug: no-op
  let deps := st.formula.depset.getD of_ #[]
  if deps.contains on_ then return ()  -- already there
  modify fun s => { s with
    formula := s.formula.addDependencyFormula of_ on_
  }
  makeIndepUnknown on_

def addDependencyReset (of_ on_ : Var) : CheckM Unit := do
  addDependency of_ on_
  resetPropagationState

-- Delete a dependency after checking via dep scheme
-- Returns false (in Except) if deletion not allowed
def delDependency (of_ on_ : Var) : CheckM Bool := do
  let st ← get
  if !st.formula.isVarExistential of_ then return true
  let allowed ← notDependsOn of_ on_
  if allowed then
    modify fun s => { s with
      formula := s.formula.forceDelDep of_ on_
    }
    makeIndepUnknown on_
    return true
  else
    return false

def delDependencyReset (of_ on_ : Var) : CheckM Bool := do
  let ok ← delDependency of_ on_
  if ok then
    resetPropagationState
    return true
  else
    return false

-- ─── Initial CheckState ────────────────────────────────────────────────────

def CheckState.empty : CheckState :=
  { formula    := {}
    clauses    := {}
    isAssigned := #[]
    value      := #[]
    trail      := #[#[]]
    propQueue  := #[]
    indepKnown := #[]
    indepOf    := #[]
  }
