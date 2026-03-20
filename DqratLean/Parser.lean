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

-- ─── DQDIMACS parser ───────────────────────────────────────────────────────

-- Parse formula file. Returns None if formula UNSAT by UP (= already verified),
-- or Some state if proof is needed.
def parseDQDIMACS (content : String) : Except String (Option CheckState) := do
  let allToks := tokenize content
  let n := allToks.size

  -- Skip leading 'c' tokens (comment lines)
  -- Find 'p' token
  let pIdx := allToks.findIdx? (· == "p") |>.getD 0
  if pIdx >= n || allToks.getD (pIdx + 1) "" != "cnf" then
    throw "Expected 'p cnf <maxVar> <numClauses>'"

  let innerOp : CheckM (Option Unit) := do
    let mut pos := pIdx + 4  -- skip: p cnf maxVar numClauses
    let mut allUnivsSoFar : Array Var := #[]
    let mut done := false

    -- Read prefix
    while !done && pos < n do
      let tok := allToks.getD pos ""
      if tok == "a" then
        pos := pos + 1
        let mut inner := true
        while inner && pos < n do
          let varTok := allToks.getD pos ""
          pos := pos + 1
          match varTok.toNat? with
          | none   => inner := false
          | some 0 => inner := false
          | some extVar =>
            let f ← (·.formula) <$> get
            if f.externalVarExists extVar then throw s!"Dup var {extVar}"
            let v ← addVarForall extVar
            allUnivsSoFar := allUnivsSoFar.push v
      else if tok == "e" then
        pos := pos + 1
        -- QDIMACS 'e' line: multiple existential vars until 0
        let mut inner := true
        while inner && pos < n do
          let varTok := allToks.getD pos ""
          pos := pos + 1
          match varTok.toNat? with
          | none   => inner := false
          | some 0 => inner := false
          | some extExi =>
            let f ← (·.formula) <$> get
            if f.externalVarExists extExi then throw s!"Dup var {extExi}"
            let _ ← addVarExists extExi allUnivsSoFar
      else if tok == "d" then
        pos := pos + 1
        match (allToks.getD pos "").toNat? with
        | none => throw "Expected exi var in 'd' line"
        | some extExi =>
          pos := pos + 1
          let f ← (·.formula) <$> get
          let internalExi ←
            if !f.externalVarExists extExi then addVarExists extExi #[]
            else match f.lookupInternal extExi with
              | none   => throw s!"Var {extExi} not found"
              | some v => pure v
          let mut deps : Array Var := #[]
          let mut inner := true
          while inner && pos < n do
            let dt := allToks.getD pos ""
            pos := pos + 1
            match dt.toInt? with
            | none   => inner := false
            | some 0 => inner := false
            | some dv =>
              let extDep := dv.natAbs
              let f2 ← (·.formula) <$> get
              let internalDep ←
                if !f2.externalVarExists extDep then addVarForall extDep
                else match f2.lookupInternal extDep with
                  | none   => throw s!"Dep var {extDep} not found"
                  | some v => pure v
              deps := deps.push internalDep
          modify fun st =>
            { st with formula :=
              { st.formula with depset := st.formula.depset.setIfInBounds internalExi deps } }
          for u in deps do makeIndepUnknown u
      else if tok == "c" then
        -- Skip comment token (the rest of the line is already tokenized away)
        pos := pos + 1
      else
        done := true  -- start of matrix

    -- Read matrix
    let mut curLits : Array Literal := #[]
    while pos < n do
      let tok := allToks.getD pos ""
      pos := pos + 1
      if tok == "c" then
        -- skip comment line (simplified)
        pure ()
      else
        match tok.toInt? with
        | none => pure ()
        | some 0 =>
          let sorted := curLits.qsort (fun a b => a.x < b.x)
          let isTauto := (List.range (if sorted.size > 0 then sorted.size - 1 else 0)).any fun i =>
            sorted.getD i ⟨0⟩ == (sorted.getD (i + 1) ⟨0⟩).negate
          if !isTauto then
            let r ← addClause sorted
            if r.isNone then return some ()  -- UNSAT detected
          curLits := #[]
        | some lit =>
          let extVar := lit.natAbs
          let f ← (·.formula) <$> get
          match f.lookupInternal extVar with
          | none    => throw s!"Unknown var {extVar} in matrix"
          | some iv => curLits := curLits.push (mkLit iv (lit > 0))

    return none  -- proof needed

  match innerOp.run CheckState.empty with
  | .error e        => throw e
  | .ok (some _, _) => return none    -- UNSAT during parsing
  | .ok (none, st)  => return some st

-- ─── Proof actions ─────────────────────────────────────────────────────────

/-- A single step in a DQRAT proof, with external variable numbers still unresolved. -/
inductive DQRatAction where
  /-- 'a': add universal variables (extVars may include negatives for error reporting) -/
  | AddUniversal      (lineNum : Nat) (extVars    : List Int)
  /-- 'e': modify existential; positive dep = add, negative dep = remove -/
  | ModifyExistential (lineNum : Nat) (extExi     : Nat)  (depChanges : List Int)
  /-- 'd': delete clause given by external literals -/
  | DeleteClause      (lineNum : Nat) (extLits    : List Int)
  /-- 'u': universal reduction -/
  | UniversalReduction(lineNum : Nat) (extLits    : List Int)
  /-- digit: RUP / DQRATE step -/
  | RatClause         (lineNum : Nat) (extLits    : List Int)

-- ─── Phase 1: pure parsing ─────────────────────────────────────────────────

/-- Read integers from `toks` starting at `pos` until a 0 or non-integer token.
    Returns the (non-zero) integer list and the new position (after the terminator). -/
private def readIntList (toks : Array String) (start : Nat) : List Int × Nat :=
  let n := toks.size
  let rec go (pos : Nat) (acc : List Int) : List Int × Nat :=
    if pos >= n then (acc.reverse, pos)
    else
      match (toks.getD pos "").toInt? with
      | none   => (acc.reverse, pos + 1)
      | some 0 => (acc.reverse, pos + 1)
      | some i => go (pos + 1) (i :: acc)
  termination_by n - pos
  go start []

/-- Phase 1: tokenize proof content and produce a list of DQRatAction.
    Pure function — no state access. -/
def parseProofActions (content : String) : List DQRatAction := Id.run do
  let toks := tokenize content
  let n    := toks.size
  let mut pos     := 0
  let mut lineNum := 0
  let mut acc : List DQRatAction := []

  while pos < n do
    let tok := toks.getD pos ""
    pos     := pos + 1
    lineNum := lineNum + 1

    if tok = "a" then
      let (vars, pos') := readIntList toks pos
      pos := pos'
      acc := .AddUniversal lineNum vars :: acc

    else if tok = "e" then
      if pos >= n then
        acc := .ModifyExistential lineNum 0 [] :: acc
      else
        let exiStr := toks.getD pos ""
        match exiStr.toNat? with
        | none =>
          pos := pos + 1
          acc := .ModifyExistential lineNum 0 [] :: acc
        | some extExi =>
          pos := pos + 1
          let (deps, pos') := readIntList toks pos
          pos := pos'
          acc := .ModifyExistential lineNum extExi deps :: acc

    else if tok = "d" then
      let (lits, pos') := readIntList toks pos
      pos := pos'
      acc := .DeleteClause lineNum lits :: acc

    else if tok = "u" then
      let (lits, pos') := readIntList toks pos
      pos := pos'
      acc := .UniversalReduction lineNum lits :: acc

    else
      match tok.toInt? with
      | none => pure ()  -- skip unrecognised token
      | some firstLit =>
        let (rest, pos') := readIntList toks pos
        pos := pos'
        let extLits := if firstLit = 0 then rest else firstLit :: rest
        acc := .RatClause lineNum extLits :: acc

  return acc.reverse

-- ─── Phase 2: monadic checking ─────────────────────────────────────────────

/-- Phase 2: execute a list of parsed actions in CheckM. -/
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
    let mut lits : Array Literal := #[]
    for lit in extLits do
      let extVar := lit.natAbs
      let f ← (·.formula) <$> get
      match f.lookupInternal extVar with
      | none    => pure ()
      | some iv => lits := lits.push (mkLit iv (lit > 0))
    let sorted := lits.qsort (fun a b => a.x < b.x)
    let st ← get
    match st.clauses.findSortedClause sorted with
    | none =>
      return .Failed lineNum #["LOCATE", "DEL"] #[] none
    | some cref =>
      modify fun s => { s with clauses := s.clauses.deleteClause cref }
      checkActions rest

  | .UniversalReduction lineNum extLits :: rest => do
    let mut lits : Array Literal := #[]
    for lit in extLits do
      let extVar := lit.natAbs
      let f ← (·.formula) <$> get
      match f.lookupInternal extVar with
      | none    => pure ()
      | some iv => lits := lits.push (mkLit iv (lit > 0))
    if lits.isEmpty then
      return .Failed lineNum #["UR"] #[] none
    let pivot := lits.getD 0 ⟨0⟩
    let f ← (·.formula) <$> get
    if f.isVarExistential pivot.var then
      return .Failed lineNum #["UR"] #[f.externalizeLit pivot] none
    let sorted := lits.qsort (fun a b => a.x < b.x)
    let st ← get
    match st.clauses.findSortedClause sorted with
    | none =>
      return .Failed lineNum #["LOCATE", "UR"] #[] none
    | some _ =>
      let f2 ← (·.formula) <$> get
      -- Not reducible if clause contains ~pivot (Mixed-EUR: no tautology reductions)
      let pivotReducible := !lits.any (· = pivot.negate) && lits.all fun l =>
        !f2.isVarExistential l.var || !f2.isVarOuterOfExivar pivot.var l.var
      if pivotReducible then
        let litsNoPivot := lits.filter (· ≠ pivot)
        let r ← addClause litsNoPivot
        if r.isNone then return .Verified lineNum
      else
        let ok ← checkDQRATU lits pivot
        if !ok then
          return .Failed lineNum #["UR", "DQRATU"] #[] none
        else
          let r ← addClause lits
          if r.isNone then return .Verified lineNum
      checkActions rest

  | .RatClause lineNum extLits :: rest => do
    let mut lits : Array Literal := #[]
    for lit in extLits do
      let extVar := lit.natAbs
      let f ← (·.formula) <$> get
      if !f.externalVarExists extVar then
        -- QRAT compat: create extension var with all univars as deps
        let univs := f.univars
        let _ ← addVarExists extVar univs
      let f2 ← (·.formula) <$> get
      match f2.lookupInternal extVar with
      | none    => pure ()
      | some iv => lits := lits.push (mkLit iv (lit > 0))
    let (success, blocker) ← checkDQRATE lits
    if !success then
      return .Failed lineNum #["RUP", "DQRATE"] #[] blocker
    else
      let r ← addClause lits
      if r.isNone then return .Verified lineNum
      checkActions rest

-- ─── Proof processor ───────────────────────────────────────────────────────

def processProof (st : CheckState) (content : String) : ProofResult :=
  match (checkActions (parseProofActions content)).run st with
  | .error e   => .Failed 0 #[e] #[] none
  | .ok (r, _) => r
