import «colorwheel.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

-- ═══ Pure helpers ═══
prove_correct clamp by unfold Pure.clamp; loom_solve
prove_correct normalizeHue by unfold Pure.normalizeHue; loom_solve
prove_correct clampColor by unfold Pure.clampColor Pure.normalizeHue Pure.clamp; loom_solve
prove_correct moodBoundsOf by unfold Pure.moodBoundsOf; loom_solve
prove_correct colorSatisfiesMood by unfold Pure.colorSatisfiesMood; loom_solve
prove_correct adjustColorSL by unfold Pure.adjustColorSL; loom_solve
prove_correct validBaseHue by unfold Pure.validBaseHue; loom_solve
prove_correct applySelectContrastPair by unfold Pure.applySelectContrastPair; loom_solve
prove_correct randomInRange by loom_solve
prove_correct validRandomSeeds by unfold Pure.validRandomSeeds; loom_solve
prove_correct allColorsSatisfyMood by unfold Pure.allColorsSatisfyMood; loom_solve
prove_correct baseHarmonyHues by unfold Pure.baseHarmonyHues; loom_solve
prove_correct allHarmonyHues by unfold Pure.allHarmonyHues; loom_solve
prove_correct huesMatchHarmony by unfold Pure.huesMatchHarmony; loom_solve

-- ═══ Generation ═══
prove_correct goldenSLForMood by loom_solve
prove_correct generateColorGolden by loom_solve
prove_correct generatePaletteColors by loom_solve
prove_correct init by loom_solve

-- ═══ Transitions (now pure with ternaries) ═══
prove_correct applyGeneratePalette by loom_solve
prove_correct applyRegenerateMood by loom_solve
prove_correct applyRegenerateHarmony by loom_solve
prove_correct applyRandomizeBaseHue by loom_solve
prove_correct applyIndependentAdjustment by loom_solve
prove_correct applySetColorDirect by loom_solve
prove_correct applyLinkedAdjustment by loom_solve
prove_correct applyAdjustPalette by loom_solve
prove_correct normalizeModel by loom_solve
prove_correct apply by loom_solve
prove_correct step by loom_solve

-- ═══ Invariant theorems ═══

theorem initSatisfiesInv : ModelInv (Pure.init) := by decide

-- TODO: prove normalizeModel always produces valid model,
-- which implies StepPreservesInv
theorem stepPreservesInv (m : Model) (a : Action) (h : ModelInv m) :
    ModelInv (Pure.step m a) := by sorry
