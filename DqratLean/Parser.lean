import DqratLean.CheckState
import DqratLean.Checker

-- ─── Tokenizer ─────────────────────────────────────────────────────────────

def tokenize (content : String) : Array String :=
  let (tokens, last) := content.foldl (fun (acc, cur) c =>
    if c.isWhitespace then
      if cur.isEmpty then (acc, "")
      else (acc.push cur, "")
    else (acc, cur.push c)
  ) ((#[] : Array String), "")
  if last.isEmpty then tokens else tokens.push last

-- ─── Pure token-list readers ───────────────────────────────────────────────

/-- Read a 0-terminated signed-integer list starting at `start`.
    Returns (integers, position-after-terminator). -/
def readIntList (toks : Array String) (start : Nat) : List Int × {p : Nat // start ≤ p} :=
  let rec go (pos : Nat) (acc : List Int) : List Int × {p : Nat // pos ≤ p} :=
    if pos >= toks.size then (acc.reverse, ⟨pos, Nat.le_refl _⟩)
    else match (toks.getD pos "").toInt? with
      | none   | some 0 => (acc.reverse, ⟨pos + 1, Nat.le_succ _⟩)
      | some i           =>
        let (ints, ⟨p', hge⟩) := go (pos + 1) (i :: acc)
        (ints, ⟨p', Nat.le_trans (Nat.le_succ _) hge⟩)
  termination_by toks.size - pos
  let (ints, ⟨p', hge⟩) := go start []
  (ints, ⟨p', hge⟩)

-- ─── Monadic token-list readers for parseDQDIMACS ─────────────────────────

/-- Read 'a'-line universals (via `toNat?`), adding each to the formula. -/
def readUniVarsM (toks : Array String) (start : Nat) (acc : Array Var) :
    CheckM ({p : Nat // start ≤ p} × Array Var) := do
  if start >= toks.size then return (⟨start, Nat.le_refl _⟩, acc)
  else match (toks.getD start "").toNat? with
    | none   | some 0 => return (⟨start + 1, Nat.le_succ _⟩, acc)
    | some extVar =>
      let f ← (·.formula) <$> get
      if f.externalVarExists extVar then throw s!"Dup var {extVar}"
      let v ← addVarForall extVar
      let (⟨p', hge⟩, acc') ← readUniVarsM toks (start + 1) (acc.push v)
      return (⟨p', Nat.le_trans (Nat.le_succ _) hge⟩, acc')
termination_by toks.size - start

/-- Read 'e'-line existentials, using `allUnivs` as the dep-set for each. -/
def readExiVarsM (toks : Array String) (allUnivs : Array Var) (start : Nat) :
    CheckM {p : Nat // start ≤ p} := do
  if start >= toks.size then return ⟨start, Nat.le_refl _⟩
  else match (toks.getD start "").toNat? with
    | none   | some 0 => return ⟨start + 1, Nat.le_succ _⟩
    | some extExi =>
      let f ← (·.formula) <$> get
      if f.externalVarExists extExi then throw s!"Dup var {extExi}"
      let _ ← addVarExists extExi allUnivs
      let ⟨p', hge⟩ ← readExiVarsM toks allUnivs (start + 1)
      return ⟨p', Nat.le_trans (Nat.le_succ _) hge⟩
termination_by toks.size - start

/-- Read a 'd'-line dep list (via `toInt?`), creating missing universals as needed. -/
def readDepsM (toks : Array String) (start : Nat) (acc : Array Var) :
    CheckM ({p : Nat // start ≤ p} × Array Var) := do
  if start >= toks.size then return (⟨start, Nat.le_refl _⟩, acc)
  else match (toks.getD start "").toInt? with
    | none   | some 0 => return (⟨start + 1, Nat.le_succ _⟩, acc)
    | some dv =>
      let extDep := dv.natAbs
      let f ← (·.formula) <$> get
      let iv ←
        if !f.externalVarExists extDep then addVarForall extDep
        else match f.lookupInternal extDep with
          | none   => throw s!"Dep var {extDep} not found"
          | some v => pure v
      let (⟨p', hge⟩, acc') ← readDepsM toks (start + 1) (acc.push iv)
      return (⟨p', Nat.le_trans (Nat.le_succ _) hge⟩, acc')
termination_by toks.size - start

/-- Process DQDIMACS prefix lines until matrix start.
    Returns (first-matrix-token-pos, all-universals-seen). -/
def readPrefixM (toks : Array String) (pos : Nat) (univs : Array Var) :
    CheckM (Nat × Array Var) := do
  if pos >= toks.size then return (pos, univs)
  else
    let tok := toks.getD pos ""
    if tok = "a" then
      let (⟨pos', _hge⟩, newUnivs) ← readUniVarsM toks (pos + 1) #[]
      readPrefixM toks pos' (univs ++ newUnivs)
    else if tok = "e" then do
      let ⟨pos', _hge⟩ ← readExiVarsM toks univs (pos + 1)
      readPrefixM toks pos' univs
    else if tok = "d" then do
      match (toks.getD (pos + 1) "").toNat? with
      | none => throw "Expected exi var in 'd' line"
      | some extExi =>
        let f ← (·.formula) <$> get
        let iv ←
          if !f.externalVarExists extExi then addVarExists extExi #[]
          else match f.lookupInternal extExi with
            | none   => throw s!"Var {extExi} not found"
            | some v => pure v
        let (⟨pos', _hge⟩, deps) ← readDepsM toks (pos + 2) #[]
        modify fun st =>
          { st with formula :=
            { st.formula with depset := st.formula.depset.setIfInBounds iv deps } }
        for u in deps do makeIndepUnknown u
        readPrefixM toks pos' univs
    else if tok = "c" then
      readPrefixM toks (pos + 1) univs
    else
      return (pos, univs)   -- start of matrix
termination_by toks.size - pos

/-- Read matrix clauses; returns `true` if UNSAT by UP, else `false`. -/
def readMatrixM (toks : Array String) (pos : Nat) (curLits : Array Literal) :
    CheckM Bool := do
  if pos >= toks.size then return false
  else
    let tok := toks.getD pos ""
    if tok = "c" then
      readMatrixM toks (pos + 1) curLits
    else match tok.toInt? with
      | none   => readMatrixM toks (pos + 1) curLits
      | some 0 =>
        let sorted := curLits.qsort (fun a b => a.x < b.x)
        let isTauto :=
          (List.range (if sorted.size > 0 then sorted.size - 1 else 0)).any fun i =>
            sorted.getD i ⟨0⟩ == (sorted.getD (i + 1) ⟨0⟩).negate
        if !isTauto then
          let r ← addClause sorted
          if r.isNone then return true
        readMatrixM toks (pos + 1) #[]
      | some lit =>
        let extVar := lit.natAbs
        let f ← (·.formula) <$> get
        match f.lookupInternal extVar with
        | none    => throw s!"Unknown var {extVar} in matrix"
        | some iv => readMatrixM toks (pos + 1) (curLits.push (mkLit iv (lit > 0)))
termination_by toks.size - pos

-- ─── DQDIMACS parser ───────────────────────────────────────────────────────

/-- Parse formula file. Returns None if formula UNSAT by UP (= already verified),
    or Some state if proof is needed. -/
def parseDQDIMACS (content : String) : Except String (Option CheckState) := do
  let allToks := tokenize content
  let pIdx    := allToks.findIdx? (· == "p") |>.getD 0
  if pIdx >= allToks.size || allToks.getD (pIdx + 1) "" != "cnf" then
    throw "Expected 'p cnf <maxVar> <numClauses>'"
  let innerOp : CheckM Bool := do
    let (matrixStart, _) ← readPrefixM allToks (pIdx + 4) #[]
    readMatrixM allToks matrixStart #[]
  match innerOp.run CheckState.empty with
  | .error e _   => throw e
  | .ok true _   => return none
  | .ok false st => return some st

-- ─── Proof action parser ───────────────────────────────────────────────────

/-- Tokenize proof content and produce a list of DQRatActions.
    Pure, no state access. Well-founded recursion on `toks.size - pos`. -/
def parseProofActions (content : String) : List DQRatAction :=
  let toks := tokenize content
  let n    := toks.size
  let rec go (pos lineNum : Nat) (acc : List DQRatAction) : List DQRatAction :=
    if pos >= n then acc.reverse
    else
      let tok := toks.getD pos ""
      let pos' := pos + 1
      let ln   := lineNum + 1
      if tok = "a" then
        let (vars, ⟨pos'', _hge⟩) := readIntList toks pos'
        go pos'' ln (.AddUniversal ln vars :: acc)
      else if tok = "e" then
        if pos' >= n then
          go pos' ln (.ModifyExistential ln 0 [] :: acc)
        else
          match (toks.getD pos' "").toNat? with
          | none =>
            go (pos' + 1) ln (.ModifyExistential ln 0 [] :: acc)
          | some extExi =>
            let (deps, ⟨pos'', _hge⟩) := readIntList toks (pos' + 1)
            go pos'' ln (.ModifyExistential ln extExi deps :: acc)
      else if tok = "d" then
        let (lits, ⟨pos'', _hge⟩) := readIntList toks pos'
        go pos'' ln (.DeleteClause ln lits :: acc)
      else if tok = "u" then
        let (lits, ⟨pos'', _hge⟩) := readIntList toks pos'
        go pos'' ln (.UniversalReduction ln lits :: acc)
      else
        match tok.toInt? with
        | none => go pos' ln acc
        | some firstLit =>
          let (rest, ⟨pos'', _hge⟩) := readIntList toks pos'
          let extLits := if firstLit = 0 then rest else firstLit :: rest
          go pos'' ln (.RatClause ln extLits :: acc)
  termination_by n - pos
  go 0 0 []

-- ─── Proof processor ───────────────────────────────────────────────────────

def processProof (st : CheckState) (content : String) : ProofResult :=
  match (checkActions (parseProofActions content)).run st with
  | .error e _ => .Failed 0 #[e] #[] none
  | .ok r _    => r
