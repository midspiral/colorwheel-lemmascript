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

-- ═══ Transitions ═══
prove_correct applyGeneratePalette by loom_solve
prove_correct applyRegenerateMood by loom_solve
prove_correct applyRegenerateHarmony by loom_solve
prove_correct applyRandomizeBaseHue by loom_solve

set_option maxHeartbeats 1600000
prove_correct applyIndependentAdjustment by loom_solve
prove_correct applySetColorDirect by loom_solve

-- ═══ Sorry (3 remaining) ═══
-- applyLinkedAdjustment: times out (10 adjustColorSL calls across 2 branches)
prove_correct applyLinkedAdjustment by sorry
-- applyAdjustPalette: depends on applyLinkedAdjustment
prove_correct applyAdjustPalette by sorry
-- normalizeModel: Loom WPGen can't prove #[a,b,c,d,e].size = 5 for requires
prove_correct normalizeModel by sorry
-- apply: depends on above
prove_correct apply by sorry
