import DqratLean.Parser
import DqratLean.WatchedChecker

namespace DqratLean.Watched

def ensureWithinMaxVar (declaredMaxVar extVar : Nat) : CheckM Unit := do
  if extVar > declaredMaxVar then
    throw s!"Variable {extVar} exceeds maximum declared variable"

def readUniVarsM (declaredMaxVar : Nat) (toks : Array String) (start : Nat) (acc : Array Var) :
    CheckM ({p : Nat // start ≤ p} × Array Var) := do
  if start >= toks.size then return (⟨start, Nat.le_refl _⟩, acc)
  else match (toks.getD start "").toNat? with
    | none | some 0 => return (⟨start + 1, Nat.le_succ _⟩, acc)
    | some extVar =>
        ensureWithinMaxVar declaredMaxVar extVar
        let f ← (·.formula) <$> get
        if f.externalVarExists extVar then throw s!"Dup var {extVar}"
        let v ← addVarForall extVar
        let (⟨p', hge⟩, acc') ← readUniVarsM declaredMaxVar toks (start + 1) (acc.push v)
        return (⟨p', Nat.le_trans (Nat.le_succ _) hge⟩, acc')
termination_by toks.size - start

def readExiVarsM (declaredMaxVar : Nat) (toks : Array String) (allUnivs : Array Var) (start : Nat) :
    CheckM {p : Nat // start ≤ p} := do
  if start >= toks.size then return ⟨start, Nat.le_refl _⟩
  else match (toks.getD start "").toNat? with
    | none | some 0 => return ⟨start + 1, Nat.le_succ _⟩
    | some extExi =>
        ensureWithinMaxVar declaredMaxVar extExi
        let f ← (·.formula) <$> get
        if f.externalVarExists extExi then throw s!"Dup var {extExi}"
        let _ ← addVarExists extExi allUnivs
        let ⟨p', hge⟩ ← readExiVarsM declaredMaxVar toks allUnivs (start + 1)
        return ⟨p', Nat.le_trans (Nat.le_succ _) hge⟩
termination_by toks.size - start

def readDepsM (declaredMaxVar : Nat) (toks : Array String) (start : Nat) (acc : Array Var) :
    CheckM ({p : Nat // start ≤ p} × Array Var) := do
  if start >= toks.size then return (⟨start, Nat.le_refl _⟩, acc)
  else match (toks.getD start "").toInt? with
    | none | some 0 => return (⟨start + 1, Nat.le_succ _⟩, acc)
    | some dv =>
        let extDep := dv.natAbs
        ensureWithinMaxVar declaredMaxVar extDep
        let f ← (·.formula) <$> get
        let iv ←
          if !f.externalVarExists extDep then addVarForall extDep
          else match f.lookupInternal extDep with
            | none => throw s!"Dep var {extDep} not found"
            | some v => pure v
        let (⟨p', hge⟩, acc') ← readDepsM declaredMaxVar toks (start + 1) (acc.push iv)
        return (⟨p', Nat.le_trans (Nat.le_succ _) hge⟩, acc')
termination_by toks.size - start

def resolvePrefixDepVarM (declaredMaxVar extExi : Nat) : CheckM Var := do
  if extExi = 0 then
    throw "Expected positive exi var in 'd' line"
  ensureWithinMaxVar declaredMaxVar extExi
  let f ← (·.formula) <$> get
  if !f.externalVarExists extExi then
    addVarExists extExi #[]
  else
    match f.lookupInternal extExi with
    | none => throw s!"Var {extExi} not found"
    | some v => pure v

def readPrefixDepLineM (declaredMaxVar : Nat) (toks : Array String) (pos : Nat) :
    CheckM {p : Nat // pos < p} := do
  match (toks.getD (pos + 1) "").toNat? with
  | none => throw "Expected exi var in 'd' line"
  | some extExi =>
      let iv ← resolvePrefixDepVarM declaredMaxVar extExi
      let (⟨pos', hge⟩, deps) ← readDepsM declaredMaxVar toks (pos + 2) #[]
      modify fun st =>
        { st with formula :=
          { st.formula with depset := st.formula.depset.setIfInBounds iv deps } }
      for u in deps do
        makeIndepUnknown u
      pure ⟨pos', by
        have hlt : pos < pos + 2 := by omega
        exact Nat.lt_of_lt_of_le hlt hge⟩

def readPrefixM (declaredMaxVar : Nat) (toks : Array String) (pos : Nat) (univs : Array Var) :
    CheckM (Nat × Array Var) := do
  if pos >= toks.size then return (pos, univs)
  else
    let tok := toks.getD pos ""
    if tok = "a" then
      let (⟨pos', _⟩, newUnivs) ← readUniVarsM declaredMaxVar toks (pos + 1) #[]
      readPrefixM declaredMaxVar toks pos' (univs ++ newUnivs)
    else if tok = "e" then
      let ⟨pos', _⟩ ← readExiVarsM declaredMaxVar toks univs (pos + 1)
      readPrefixM declaredMaxVar toks pos' univs
    else if tok = "d" then
      let ⟨pos', _⟩ ← readPrefixDepLineM declaredMaxVar toks pos
      readPrefixM declaredMaxVar toks pos' univs
    else
      return (pos, univs)
termination_by toks.size - pos

def readMatrixM (declaredMaxVar : Nat) (toks : Array String) (pos : Nat) (curLits : Array Literal) :
    CheckM Bool := do
  if pos >= toks.size then return false
  else
    let tok := toks.getD pos ""
    match tok.toInt? with
    | none => readMatrixM declaredMaxVar toks (pos + 1) curLits
    | some 0 =>
        let sorted := ClauseStore.sortLits curLits
        let isTauto :=
          (List.range (if sorted.size > 0 then sorted.size - 1 else 0)).any fun i =>
            sorted.getD i (mkLit 0 false) == (sorted.getD (i + 1) (mkLit 0 false)).negate
        if !isTauto then
          let r ← addClause sorted
          if r.isNone then return true
        readMatrixM declaredMaxVar toks (pos + 1) #[]
    | some lit =>
        let extVar := lit.natAbs
        ensureWithinMaxVar declaredMaxVar extVar
        let f ← (·.formula) <$> get
        match f.lookupInternal extVar with
        | none => throw s!"Unknown var {extVar} in matrix"
        | some iv =>
            readMatrixM declaredMaxVar toks (pos + 1) (curLits.push (mkLit iv (lit > 0)))
termination_by toks.size - pos

def parseDQDIMACSInner (declaredMaxVar : Nat) (allToks : Array String) : CheckM Bool := do
  let (matrixStart, _) ← readPrefixM declaredMaxVar allToks 4 #[]
  readMatrixM declaredMaxVar allToks matrixStart #[]

def parseDQDIMACSTokensAfterHeader (declaredMaxVar : Nat) (allToks : Array String) :
    Except String (Option CheckState) :=
  match (parseDQDIMACSInner declaredMaxVar allToks).run CheckState.empty with
  | .error e _ => .error e
  | .ok true _ => .ok none
  | .ok false st => .ok (some st)

def parseDQDIMACSTokens (allToks : Array String) : Except String (Option CheckState) := do
  if allToks.getD 0 "" != "p" || allToks.getD 1 "" != "cnf" then
    throw "Expected 'p cnf <maxVar> <numClauses>'"
  let declaredMaxVar ←
    match (allToks.getD 2 "").toNat? with
    | some n => pure n
    | none => throw "Expected numeric <maxVar> in header"
  let _declaredNumClauses ←
    match (allToks.getD 3 "").toNat? with
    | some n => pure n
    | none => throw "Expected numeric <numClauses> in header"
  parseDQDIMACSTokensAfterHeader declaredMaxVar allToks

def parseDQDIMACS (content : String) : Except String (Option CheckState) := do
  let _ ← validateDQDIMACSStructure content
  parseDQDIMACSTokens (tokenize (stripCommentLines content))

private def parseProofLineAction (lineNum : Nat) (toks : Array String) : Option DQRatAction :=
  let tok := toks.getD 0 ""
  if tok = "a" then
    let (vars, _) := readIntList toks 1
    some (.AddUniversal lineNum vars)
  else if tok = "e" then
    match (toks.getD 1 "").toNat? with
    | none => some (.ModifyExistential lineNum 0 [])
    | some extExi =>
        let (deps, _) := readIntList toks 2
        some (.ModifyExistential lineNum extExi deps)
  else if tok = "d" then
    let (lits, _) := readIntList toks 1
    some (.DeleteClause lineNum lits)
  else if tok = "u" then
    let (lits, _) := readIntList toks 1
    some (.UniversalReduction lineNum lits)
  else
    match tok.toInt? with
    | none => none
    | some firstLit =>
        let (rest, _) := readIntList toks 1
        let extLits := if firstLit = 0 then rest else firstLit :: rest
        some (.RatClause lineNum extLits)

def parseProofActions (content : String) : List DQRatAction :=
  let rec go (lines : List String) (lineNum : Nat) (acc : List DQRatAction) : List DQRatAction :=
    match lines with
    | [] => acc.reverse
    | line :: rest =>
        let toks := tokenize line
        if toks.isEmpty || isCommentLine line then
          go rest (lineNum + 1) acc
        else
          let acc' := match parseProofLineAction lineNum toks with
            | some action => action :: acc
            | none => acc
          go rest (lineNum + 1) acc'
  go (content.splitOn "\n") 1 []

private def parseProofActionsStrict (content : String) : Except String (List DQRatAction) := do
  let validateSignedZeroTerminated (lineNum : Nat) (ctx : String)
      (toks : Array String) (start : Nat) : Except String Unit := do
    let rec goSigned (pos : Nat) : Except String Unit := do
      if _ : pos < toks.size then
        let tok := toks.getD pos ""
        match tok.toInt? with
        | none => throw s!"Line {lineNum}: expected integer in {ctx}, got '{tok}'"
        | some 0 =>
            if pos + 1 = toks.size then pure ()
            else throw s!"Line {lineNum}: unexpected tokens after 0 terminator in {ctx}"
        | some _ => goSigned (pos + 1)
      else
        throw s!"Line {lineNum}: expected 0 terminator in {ctx}"
    termination_by toks.size - pos
    if start >= toks.size then
      throw s!"Line {lineNum}: expected 0-terminated {ctx}"
    goSigned start
  let rec go (lines : List String) (lineNum : Nat) (acc : List DQRatAction) :
      Except String (List DQRatAction) := do
    match lines with
    | [] => pure acc.reverse
    | line :: rest =>
        let toks := tokenize line
        if toks.isEmpty || isCommentLine line then
          go rest (lineNum + 1) acc
        else
          let tok := toks.getD 0 ""
          if tok = "a" then
            validateSignedZeroTerminated lineNum "'a' line" toks 1
          else if tok = "e" then
            match (toks.getD 1 "").toNat? with
            | none => throw s!"Line {lineNum}: expected existential variable after 'e'"
            | some _ => validateSignedZeroTerminated lineNum "'e' line" toks 2
          else if tok = "d" then
            validateSignedZeroTerminated lineNum "'d' line" toks 1
          else if tok = "u" then
            validateSignedZeroTerminated lineNum "'u' line" toks 1
          else
            match tok.toInt? with
            | none => throw s!"Line {lineNum}: expected proof action"
            | some _ => validateSignedZeroTerminated lineNum "clause line" toks 0
          let acc' := match parseProofLineAction lineNum toks with
            | some action => action :: acc
            | none => acc
          go rest (lineNum + 1) acc'
  go (content.splitOn "\n") 1 []

def processProof (st : CheckState) (content : String) : ProofResult :=
  match parseProofActionsStrict content with
  | .error e => .Failed 0 #[s!"PARSE: {e}"] #[] none
  | .ok actions =>
      match (checkActions actions).run st with
      | .error e _ => .Failed 0 #[e] #[] none
      | .ok r _ => r

def processProofNoNegE (st : CheckState) (content : String) : ProofResult :=
  match parseProofActionsStrict content with
  | .error e => .Failed 0 #[s!"PARSE: {e}"] #[] none
  | .ok actions =>
      match (checkActionsNoNegE actions).run st with
      | .error e _ => .Failed 0 #[e] #[] none
      | .ok r _ => r

end DqratLean.Watched
