import DqratLean.DeletionSemantics
import DqratLean.DeletionPaths

/-!
# Deletion Exhibition (open frontier)

This leaf module contains the single open theorem of the development.
Iterate here: `lake build DqratLean.DeletionExhibition` rebuilds only this
file against the compiled support modules.
-/
open Std.Do

/-- **The open deletion frontier: full exhibition of the reflexive
resolution-path dependency scheme.**

If no variable of `vars` is connected to both polarities of the universal
`on_` by `on_`-pure resolution paths (`NoDeleteCrossPathsSet`, certified by
the executable `getReachable` BFS), then any model of the formula can be
repaired into a model whose Skolem functions for every `of_ ∈ vars` are
simultaneously independent of `on_` (`DeleteIndependenceSetBridge`).

This statement is known to be true: the reflexive resolution-path dependency
scheme is *fully exhibited* for DQBF. See R. Wimmer, K. Wimmer, C. Scholl,
B. Becker, "Dependency Schemes for DQBF" (SAT 2016), and O. Beyersdorff,
J. Blinkhorn, "Reinterpreting Dependency Schemes: Soundness Meets
Incompleteness in DQBF" (J. Automated Reasoning, 2019). The intended proof is
the literature's one-shot merged-witness construction over the two reach
cones. A fiber-counting witness-descent proof was attempted and abandoned:
its restart obligation over abstract progress candidates is as hard as this
whole theorem (see docs/negative_e_strategy_split.md and the WIP checkpoint
commit in git history). -/
theorem deleteIndependenceSetBridge_of_noDeleteCrossPathsSet
    {dqbf : DQBF} {cs : ClauseStore} {st : CheckState} {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs st)
    (hon_le : on_ ≤ st.formula.maxVar)
    (hon_univ : st.formula.isVarExistential on_ = false)
    (hgt : ∀ of_ ∈ vars.toList, on_ < of_)
    (hexi : ∀ of_ ∈ vars.toList, st.formula.isVarExistential of_ = true)
    (hcontains : ∀ of_ ∈ vars.toList,
      (st.formula.depset.getD of_ #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet st vars on_) :
    DeleteIndependenceSetBridge st vars on_ := by
  sorry
