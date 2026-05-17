import DqratLean.DependencyRemovalNarrative

/-!
Compatibility wrappers for older dependency-removal bridge names.

The main TeX-interleaved proof now lives in `DependencyRemovalNarrative`.  This
module keeps the older theorem names available without forcing the narrative
file itself to carry that compatibility tail.
-/

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_twoTierProperGrowthEquivalentReducedLowPhaseProgress
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hproperGrowth :
      DependencyRemovalSameClauseConcreteProperGrowthFrontierLowPhaseProgress
        s vars on_)
    (hequivReduced :
      DependencyRemovalEquivalentFootprintReducedLowPhaseProgressDischarge
        s vars on_) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_natStageProperGrowthEquivalentReducedRestartProgress
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
    (on_ := on_) hfull hon_le hon_univ hclosed hgt hexi hcontains
    hpaths hproperGrowth hequivReduced

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_twoTierProperGrowthEquivalentReducedLowPhaseGuardedStagedRankProgress
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hproperGrowth :
      DependencyRemovalSameClauseConcreteProperGrowthFrontierLowPhaseProgress
        s vars on_)
    (hequivReduced :
      DependencyRemovalEquivalentFootprintReducedLowPhaseProgressDischarge
        s vars on_) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_natStageProperGrowthEquivalentReducedRestartProgress
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
    (on_ := on_) hfull hon_le hon_univ hclosed hgt hexi hcontains
    hpaths hproperGrowth hequivReduced

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_twoTierReducedEquivalentReducedLowPhaseProgress
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hreduced :
      DependencyRemovalCurrentFrontierReducedLowPhaseProgressDischarge
        s vars on_)
    (hequivReduced :
      DependencyRemovalEquivalentFootprintReducedLowPhaseProgressDischarge
        s vars on_) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_natStageReducedEquivalentReducedRestartProgress
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
    (on_ := on_) hfull hon_le hon_univ hclosed hgt hexi hcontains
    hpaths hreduced hequivReduced

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_twoTierReducedEquivalentReducedLowPhaseGuardedStagedRankProgress
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hreduced :
      DependencyRemovalCurrentFrontierReducedLowPhaseProgressDischarge
        s vars on_)
    (hequivReduced :
      DependencyRemovalEquivalentFootprintReducedLowPhaseProgressDischarge
        s vars on_) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_natStageReducedEquivalentReducedRestartProgress
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
    (on_ := on_) hfull hon_le hon_univ hclosed hgt hexi hcontains
    hpaths hreduced hequivReduced

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_twoTierReducedEquivalentSearchStepLowPhaseProgress
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hreduced :
      DependencyRemovalCurrentFrontierReducedLowPhaseProgressDischarge
        s vars on_)
    (hequivSearch :
      DependencyRemovalEquivalentFootprintSearchStepLowPhaseProgressDischarge
        s vars on_) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_natStageReducedEquivalentSearchStepLowPhaseProgress
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
    (on_ := on_) hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
    (dependencyRemoval_currentFrontierSearchStepLowPhaseProgressDischarge_of_reducedDischarge
      (s := s) (vars := vars) (on_ := on_) hreduced)
    hequivSearch

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_twoTierReducedEquivalentSearchStepLowPhaseGuardedStagedRankProgress
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hreduced :
      DependencyRemovalCurrentFrontierReducedLowPhaseProgressDischarge
        s vars on_)
    (hequivSearch :
      DependencyRemovalEquivalentFootprintSearchStepLowPhaseProgressDischarge
        s vars on_) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_natStageReducedEquivalentSearchStepLowPhaseProgress
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
    (on_ := on_) hfull hon_le hon_univ hclosed hgt hexi hcontains hpaths
    (dependencyRemoval_currentFrontierSearchStepLowPhaseProgressDischarge_of_reducedDischarge
      (s := s) (vars := vars) (on_ := on_) hreduced)
    hequivSearch

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_twoTierRestartResidualLowPhaseProgress
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hcurrentRestart :
      DependencyRemovalCurrentFrontierRestartResidualLowPhaseProgressDischarge
        s vars on_)
    (hequivRestart :
      DependencyRemovalEquivalentFootprintRestartResidualLowPhaseProgressDischarge
        s vars on_) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_natStageReducedEquivalentReducedRestartProgress
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
    (on_ := on_) hfull hon_le hon_univ hclosed hgt hexi hcontains
    hpaths
    (dependencyRemoval_currentFrontierReducedLowPhaseProgressDischarge_of_restartResidualDischarge
      (s := s) (vars := vars) (on_ := on_) hcurrentRestart)
    (dependencyRemoval_equivalentFootprintReducedLowPhaseProgressDischarge_of_restartResidualDischarge
      (s := s) (vars := vars) (on_ := on_) hequivRestart)

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_twoTierRestartResidualLowPhaseGuardedStagedRankProgress
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hcurrentRestart :
      DependencyRemovalCurrentFrontierRestartResidualLowPhaseProgressDischarge
        s vars on_) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_natStageCurrentFrontierReducedLowPhaseRestartProgress
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
    (on_ := on_) hfull hon_le hon_univ hclosed hgt hexi hcontains
    hpaths
    (dependencyRemoval_currentFrontierReducedLowPhaseProgressDischarge_of_restartResidualDischarge
      (s := s) (vars := vars) (on_ := on_) hcurrentRestart)

theorem dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_twoTierSearchStepLowPhaseProgress
    {dqbf : DQBF} {cs : ClauseStore} {s : CheckState}
    {vars : Array Var} {on_ : Var}
    (hfull : CheckState.FullCorrect dqbf cs s)
    (hon_le : on_ ≤ s.formula.maxVar)
    (hon_univ : s.formula.isVarExistential on_ = false)
    (hclosed : ∀ x, s.formula.isVarExistential x = true →
      (s.formula.depset.getD x #[]).contains on_ = true → x ∈ vars.toList)
    (hgt : ∀ x ∈ vars.toList, on_ < x)
    (hexi : ∀ x ∈ vars.toList, s.formula.isVarExistential x = true)
    (hcontains : ∀ x ∈ vars.toList,
      (s.formula.depset.getD x #[]).contains on_ = true)
    (hpaths : NoDeleteCrossPathsSet s vars on_)
    (hcurrentSearch :
      DependencyRemovalCurrentFrontierSearchStepLowPhaseProgressDischarge
        s vars on_)
    (hequivSearch :
      DependencyRemovalEquivalentFootprintSearchStepLowPhaseProgressDischarge
        s vars on_) :
    DeleteIndependenceSetBridge s vars on_ :=
  dependencyRemovalBridge_of_initialPatchLocalRepair_noCrossPaths_natStageReducedEquivalentSearchStepLowPhaseProgress
    (dqbf := dqbf) (cs := cs) (s := s) (vars := vars)
    (on_ := on_) hfull hon_le hon_univ hclosed hgt hexi hcontains
    hpaths hcurrentSearch hequivSearch
