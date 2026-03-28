import DqratLean

-- ─── Proof processor ───────────────────────────────────────────────────────

-- def processProof (st : CheckState) (content : String) : ProofResult :=
--   match (checkActions (parseProofActions content)).run st with
--   | .error e _ => .failed 0 #[e] #[] none
--   | .ok r _    => r

def main : List String → IO UInt32
  | [formulaFile, proofFile] => do
    let formula ← IO.FS.readFile formulaFile
    let proof   ← IO.FS.readFile proofFile
    match (parseDQDIMACS formula).run {} with
    | .error (.failed _ es _ _) _ =>
      for e in es do
        IO.eprintln s!"c parse error: {e}"
      return 1
    | .error (.verified _) _ =>
      -- Formula UNSAT by UP during parsing
      IO.println "c formula found unsat during reading in"
      IO.println "s VERIFIED"
      return 0
    | .ok _ st =>
      IO.println s!"c formula read successfully"
      let proof := parseProofActions proof
      match (checkActions proof).run st with
      | .error (.verified line) _ =>
        IO.println s!"c line {line}: unit propagation derived conflict, proof valid"
        IO.println "s VERIFIED"
      | .error (.failed line rules _info blocker) _ =>
        let rulesStr := rules.foldl (· ++ ", " ++ ·) "" |>.drop 2
        IO.println s!"c line {line}: lemma checked for: {rulesStr}"
        if let some _ := blocker then
          IO.println "c (blocker clause found)"
        IO.println "c the check has failed. The proof is invalid"
        IO.println "s FAILED"
      | .ok _ _ =>
        IO.println "c lemmas are correct, but there is no conflict at the end"
        IO.println "s UNKNOWN"
      return 0
  | _ => do
      IO.println "Usage: dqrat-lean <formula.dqdimacs> <proof.dqrat>"
      return 1
