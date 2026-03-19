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
              { st.formula with depset := arraySafeSet st.formula.depset internalExi deps } }
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

-- ─── Proof processor ───────────────────────────────────────────────────────

def processProof (st : CheckState) (content : String) : ProofResult :=
  let toks := tokenize content
  let n := toks.size

  let proc : CheckM ProofResult := do
    let mut pos := 0
    let mut lineCtr := 0
    let mut finalResult : ProofResult := .Unknown

    while pos < n do
      let tok := toks.getD pos ""
      pos := pos + 1
      lineCtr := lineCtr + 1

      if tok == "a" then
        let mut failed := false
        let mut inner := true
        while inner && pos < n do
          let varTok := toks.getD pos ""
          pos := pos + 1
          match varTok.toInt? with
          | none   => inner := false
          | some 0 => inner := false
          | some cv =>
            if cv < 0 then
              let extVar := (-cv).toNat
              let f ← (·.formula) <$> get
              if f.externalVarExists extVar then
                finalResult := .Failed lineCtr #["UADD"] #[cv] none
                failed := true; inner := false
            else
              let extVar := cv.toNat
              let f ← (·.formula) <$> get
              if f.externalVarExists extVar then
                finalResult := .Failed lineCtr #["UADD"] #[cv] none
                failed := true; inner := false
              else
                let _ ← addVarForall extVar
        if failed then break

      else if tok == "e" then
        let exiTok := toks.getD pos ""
        pos := pos + 1
        match exiTok.toNat? with
        | none =>
          finalResult := .Failed lineCtr #["UADD"] #[] none; break
        | some extExi =>
          let f ← (·.formula) <$> get
          let internalExi ←
            if !f.externalVarExists extExi then addVarExists extExi #[]
            else match f.lookupInternal extExi with
              | none   => throw s!"Var {extExi} not found"
              | some v => pure v
          let mut failed := false
          let mut inner := true
          while inner && pos < n do
            let dtok := toks.getD pos ""
            pos := pos + 1
            match dtok.toInt? with
            | none   => inner := false
            | some 0 => inner := false
            | some cv =>
              if cv < 0 then
                let extDep := (-cv).toNat
                let f2 ← (·.formula) <$> get
                if f2.externalVarExists extDep then
                  match f2.lookupInternal extDep with
                  | none => pure ()
                  | some internalDep =>
                    let ok ← delDependency internalExi internalDep
                    if !ok then
                      finalResult := .Failed lineCtr #["DPURE"] #[cv, Int.ofNat extExi] none
                      failed := true; inner := false
              else
                let extDep := cv.toNat
                let f2 ← (·.formula) <$> get
                let internalDep ←
                  if !f2.externalVarExists extDep then addVarForall extDep
                  else match f2.lookupInternal extDep with
                    | none   => throw s!"Dep var {extDep} not found"
                    | some v => pure v
                addDependency internalExi internalDep
          if failed then break

      else if tok == "d" then
        let mut lits : Array Literal := #[]
        let mut inner := true
        while inner && pos < n do
          let ltok := toks.getD pos ""
          pos := pos + 1
          match ltok.toInt? with
          | none   => inner := false
          | some 0 => inner := false
          | some lit =>
            let extVar := lit.natAbs
            let f ← (·.formula) <$> get
            match f.lookupInternal extVar with
            | none    => pure ()
            | some iv => lits := lits.push (mkLit iv (lit > 0))
        let sorted := lits.qsort (fun a b => a.x < b.x)
        let st2 ← get
        match st2.clauses.findSortedClause sorted with
        | none =>
          finalResult := .Failed lineCtr #["LOCATE", "DEL"] #[] none; break
        | some cref =>
          modify fun s => { s with clauses := s.clauses.deleteClause cref }

      else if tok == "u" then
        let mut lits : Array Literal := #[]
        let mut inner := true
        while inner && pos < n do
          let ltok := toks.getD pos ""
          pos := pos + 1
          match ltok.toInt? with
          | none   => inner := false
          | some 0 => inner := false
          | some lit =>
            let extVar := lit.natAbs
            let f ← (·.formula) <$> get
            match f.lookupInternal extVar with
            | none    => pure ()
            | some iv => lits := lits.push (mkLit iv (lit > 0))
        if lits.isEmpty then
          finalResult := .Failed lineCtr #["UR"] #[] none; break
        let pivot := lits.getD 0 ⟨0⟩
        let f ← (·.formula) <$> get
        if f.isVarExistential pivot.var then
          finalResult := .Failed lineCtr #["UR"] #[f.externalizeLit pivot] none; break
        let sorted := lits.qsort (fun a b => a.x < b.x)
        let st2 ← get
        match st2.clauses.findSortedClause sorted with
        | none =>
          finalResult := .Failed lineCtr #["LOCATE", "UR"] #[] none; break
        | some _ =>
          let f2 ← (·.formula) <$> get
          let pivotReducible := lits.all fun l =>
            !f2.isVarExistential l.var || !f2.isVarOuterOfExivar pivot.var l.var
          if pivotReducible then
            let litsNoPivot := lits.filter (· != pivot)
            let r ← addClause litsNoPivot
            if r.isNone then
              finalResult := .Verified lineCtr; break
          else
            let ok ← checkDQRATU lits pivot
            if !ok then
              finalResult := .Failed lineCtr #["UR", "DQRATU"] #[] none; break
            else
              let r ← addClause lits
              if r.isNone then
                finalResult := .Verified lineCtr; break

      else
        match tok.toInt? with
        | none => pure ()  -- skip non-integer token
        | some firstLit =>
          let mut lits : Array Literal := #[]
          if firstLit != 0 then
            let extVar := firstLit.natAbs
            let f ← (·.formula) <$> get
            if !f.externalVarExists extVar then
              -- QRAT compat: create extension var with all univars as deps
              let univs := f.univars
              let _ ← addVarExists extVar univs
            let f2 ← (·.formula) <$> get
            match f2.lookupInternal extVar with
            | none    => pure ()
            | some iv => lits := lits.push (mkLit iv (firstLit > 0))
          let mut inner := true
          while inner && pos < n do
            let ltok := toks.getD pos ""
            pos := pos + 1
            match ltok.toInt? with
            | none   => inner := false
            | some 0 => inner := false
            | some lit =>
              let extVar := lit.natAbs
              let f ← (·.formula) <$> get
              match f.lookupInternal extVar with
              | none    => pure ()
              | some iv => lits := lits.push (mkLit iv (lit > 0))
          let (success, blocker) ← checkDQRATE lits
          if !success then
            finalResult := .Failed lineCtr #["RUP", "DQRATE"] #[] blocker; break
          else
            let r ← addClause lits
            if r.isNone then
              finalResult := .Verified lineCtr; break

    return finalResult

  match proc.run st with
  | .error e  => .Failed 0 #[e] #[] none
  | .ok (r, _) => r
