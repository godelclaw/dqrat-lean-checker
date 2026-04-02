import DqratLean

def main : List String → IO UInt32
  | [formulaFile, proofFile] => do
      let formulaContent ← IO.FS.readFile formulaFile
      let proofContent   ← IO.FS.readFile proofFile
      match parseDQDIMACS formulaContent with
      | .error e =>
        IO.eprintln s!"c parse error: {e}"
        return 1
      | .ok none =>
        -- Formula UNSAT by UP during parsing
        IO.println "c formula found unsat during reading in"
        IO.println "s VERIFIED"
        return 0
      | .ok (some st) =>
        IO.println s!"c formula read successfully"
        let result := processProof st proofContent
        match result with
        | .Verified line =>
          IO.println s!"c line {line}: unit propagation derived conflict, proof valid"
        | .Failed line rules _info blocker =>
          let parseMsg := rules.getD 0 ""
          if line = 0 && rules.size = 1 && parseMsg.startsWith "PARSE: " then
            IO.println s!"c proof parse error: {parseMsg.drop 7}"
          else
            let rulesStr := rules.foldl (· ++ ", " ++ ·) "" |>.drop 2
            IO.println s!"c line {line}: lemma checked for: {rulesStr}"
            if let some _ := blocker then
              IO.println "c (blocker clause found)"
            IO.println "c the check has failed. The proof is invalid"
        | .Unknown =>
          IO.println "c lemmas are correct, but there is no conflict at the end"
        IO.println (formatResult result)
        return 0
  | _ => do
      IO.println "Usage: dqrat-lean <formula.dqdimacs> <proof.dqrat>"
      return 1
