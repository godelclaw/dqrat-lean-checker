# dqrat-lean-checker

This repository is a GitHub mirror for ongoing work on the Lean DQRAT checker.

Upstream source:
- Mirek Olsak's original repository: `https://git.olsak.net/mirek/dqrat-lean-checker`

Provenance:
- Original project and baseline code are by Mirek Olsak.
- This branch carries local work-in-progress changes for parser fixes, checker alignment, and soundness-proof scaffolding.

Status:
- This mirror is not the canonical upstream.
- Proof work is still in progress; the Lean project currently builds with remaining `sorry`s in the soundness development.

Build:
```bash
lake build
```
