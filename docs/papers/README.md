# Reference papers for the deletion-exhibition proof

## Primary: Beyersdorff, Blinkhorn, Chew, Schmidt, Suda (JAR 2019)

"Reinterpreting Dependency Schemes: Soundness Meets Incompleteness in DQBF",
Journal of Automated Reasoning (2019) 63:597-623.
DOI: 10.1007/s10817-018-9482-4. Open access (CC-BY 4.0), full text:
https://pmc.ncbi.nlm.nih.gov/articles/PMC6710225/

Files here:
- `...-jar2019-reinterpreting-dependency-schemes.pdf` — first 10 pages
  (publisher PDF render truncates; full text in the .txt).
- `...-jar2019-fulltext.txt` — complete text extracted from the open-access
  PMC HTML (CC-BY; all authorship/attribution retained).

This is the proof we transcribe in `DqratLean/DeletionExhibition.lean`:
Section 6, Definitions 9-13 (resolution paths, assignment trees, reformed
paths, reformed model) and Lemmas 2-5 + Theorem 8 (Drrs is fully exhibited).
The Lean development needs only Lemma 2 (reformed paths satisfy clauses),
the left/right structure of Definition 13, and Lemma 4 (the reformed model
exhibits independence) — Lemma 5 (preservation across successive reforms)
is not needed because the checker deletes dependencies one universal at a
time, re-running the theorem on the updated formula.

## Secondary: Wimmer, Wimmer, Scholl, Becker (SAT 2016)

"Dependency Schemes for DQBF", SAT 2016, LNCS 9710, pp. 473-489.
DOI: 10.1007/978-3-319-40970-2_29 (paywalled; not archived here).
Original DQBF soundness of the reflexive resolution-path scheme
(Theorems 3-4); cited via the JAR paper and via Beyersdorff, Blinkhorn,
Peitl, "Strong (D)QBF Dependency Schemes via Tautology-Free Resolution
Paths" (SAT 2020), Theorem 11, which states full exhibition explicitly.
