import DqratLean.CheckState
import DqratLean.Checker

-- ─── Proof result ──────────────────────────────────────────────────────────

inductive ProofResult where
  | Verified (line : Nat)
  | Failed   (line : Nat) (rules : Array String) (info : Array Int) (blocker : Option CRef)
  | Unknown

def formatResult : ProofResult → String
  | .Verified _ => "s VERIFIED"
  | .Failed _ _ _ _ => "s FAILED"
  | .Unknown => "s UNKNOWN"

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
private def readIntList (toks : Array String) (start : Nat) : List Int × {p : Nat // start ≤ p} :=
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
private def readUniVarsM (toks : Array String) (start : Nat) (acc : Array Var) :
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
private def readExiVarsM (toks : Array String) (allUnivs : Array Var) (start : Nat) :
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
private def readDepsM (toks : Array String) (start : Nat) (acc : Array Var) :
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
private def readPrefixM (toks : Array String) (pos : Nat) (univs : Array Var) :
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
private def readMatrixM (toks : Array String) (pos : Nat) (curLits : Array Literal) :
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

-- ─── Proof actions ─────────────────────────────────────────────────────────

/-- A single step in a DQRAT proof, with external variable numbers still unresolved. -/
inductive DQRatAction where
  /-- 'a': add universal variables (extVars may include negatives for error reporting) -/
  | AddUniversal      (lineNum : Nat) (extVars    : List Int)
  /-- 'e': modify existential; positive dep = add, negative dep = remove -/
  | ModifyExistential (lineNum : Nat) (extExi     : Nat) (depChanges : List Int)
  /-- 'd': delete clause given by external literals -/
  | DeleteClause      (lineNum : Nat) (extLits    : List Int)
  /-- 'u': universal reduction -/
  | UniversalReduction(lineNum : Nat) (extLits    : List Int)
  /-- digit: RUP / DQRATE step -/
  | RatClause         (lineNum : Nat) (extLits    : List Int)

-- ─── Phase 1: pure parsing ─────────────────────────────────────────────────

/-- Phase 1: tokenize proof content and produce a list of DQRatAction.
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

-- ─── Phase 2: monadic checking ─────────────────────────────────────────────

/-- Phase 2: execute a list of parsed actions in CheckM.
    Structural recursion on the action list. -/
private def checkActions : List DQRatAction → CheckM ProofResult
  | [] => return .Unknown

  | .AddUniversal lineNum extVars :: rest => do
    for cv in extVars do
      if cv < 0 then
        let extVar := (-cv).toNat
        let f ← (·.formula) <$> get
        if f.externalVarExists extVar then
          return .Failed lineNum #["UADD"] #[cv] none
      else
        let extVar := cv.toNat
        let f ← (·.formula) <$> get
        if f.externalVarExists extVar then
          return .Failed lineNum #["UADD"] #[cv] none
        else
          let _ ← addVarForall extVar
    checkActions rest

  | .ModifyExistential lineNum extExi depChanges :: rest => do
    if extExi = 0 then return .Failed lineNum #["UADD"] #[] none
    let f ← (·.formula) <$> get
    let internalExi ←
      if !f.externalVarExists extExi then addVarExists extExi #[]
      else match f.lookupInternal extExi with
        | none   => throw s!"Var {extExi} not found"
        | some v => pure v
    for cv in depChanges do
      if cv < 0 then
        let extDep := (-cv).toNat
        let f2 ← (·.formula) <$> get
        if f2.externalVarExists extDep then
          match f2.lookupInternal extDep with
          | none => pure ()
          | some internalDep =>
            let ok ← delDependency internalExi internalDep
            if !ok then
              return .Failed lineNum #["DPURE"] #[cv, Int.ofNat extExi] none
      else
        let extDep := cv.toNat
        let f2 ← (·.formula) <$> get
        let internalDep ←
          if !f2.externalVarExists extDep then addVarForall extDep
          else match f2.lookupInternal extDep with
            | none   => throw s!"Dep var {extDep} not found"
            | some v => pure v
        addDependency internalExi internalDep
    checkActions rest

  | .DeleteClause lineNum extLits :: rest => do
    let lits ← extLits.foldlM (fun acc lit => do
      let f ← (·.formula) <$> get
      match f.lookupInternal lit.natAbs with
      | none    => return acc
      | some iv => return (acc.push (mkLit iv (lit > 0)))
    ) #[]
    let st ← get
    match st.clauses.findSortedClause (lits.qsort (fun a b => a.x < b.x)) with
    | none      => return .Failed lineNum #["LOCATE", "DEL"] #[] none
    | some cref =>
      modify fun s => { s with clauses := s.clauses.deleteClause cref }
      checkActions rest

  | .UniversalReduction lineNum extLits :: rest => do
    let lits ← extLits.foldlM (fun acc lit => do
      let f ← (·.formula) <$> get
      match f.lookupInternal lit.natAbs with
      | none    => return acc
      | some iv => return (acc.push (mkLit iv (lit > 0)))
    ) #[]
    if lits.isEmpty then return .Failed lineNum #["UR"] #[] none
    let pivot := lits.getD 0 ⟨0⟩
    let f ← (·.formula) <$> get
    if f.isVarExistential pivot.var then
      return .Failed lineNum #["UR"] #[f.externalizeLit pivot] none
    let st ← get
    match st.clauses.findSortedClause (lits.qsort (fun a b => a.x < b.x)) with
    | none   => return .Failed lineNum #["LOCATE", "UR"] #[] none
    | some _ =>
      let f2 ← (·.formula) <$> get
      -- Not reducible if clause contains ~pivot (Mixed-EUR: no tautology reductions)
      let pivotReducible := !lits.any (· = pivot.negate) && lits.all fun l =>
        !f2.isVarExistential l.var || !f2.isVarOuterOfExivar pivot.var l.var
      if pivotReducible then
        let r ← addClause (lits.filter (· ≠ pivot))
        if r.isNone then return .Verified lineNum
      else
        let ok ← checkDQRATU lits pivot
        if !ok then return .Failed lineNum #["UR", "DQRATU"] #[] none
        let r ← addClause lits
        if r.isNone then return .Verified lineNum
      checkActions rest

  | .RatClause lineNum extLits :: rest => do
    let lits ← extLits.foldlM (fun acc lit => do
      let extVar := lit.natAbs
      let f ← (·.formula) <$> get
      -- QRAT compat: create extension var with all univars as deps
      if !f.externalVarExists extVar then
        let _ ← addVarExists extVar f.univars
      let f2 ← (·.formula) <$> get
      match f2.lookupInternal extVar with
      | none    => return acc
      | some iv => return (acc.push (mkLit iv (lit > 0)))
    ) #[]
    let (success, blocker) ← checkDQRATE lits
    if !success then return .Failed lineNum #["RUP", "DQRATE"] #[] blocker
    let r ← addClause lits
    if r.isNone then return .Verified lineNum
    checkActions rest

-- ─── Proof processor ───────────────────────────────────────────────────────

def processProof (st : CheckState) (content : String) : ProofResult :=
  match (checkActions (parseProofActions content)).run st with
  | .error e _ => .Failed 0 #[e] #[] none
  | .ok r _    => r
