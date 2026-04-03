import «colorwheel.def»

set_option loom.semantics.termination "total"
set_option loom.semantics.choice "demonic"

-- ═══ Proved ═══
prove_correct clamp by
  unfold Pure.clamp; loom_solve

prove_correct normalizeHue by
  unfold Pure.normalizeHue; loom_solve

prove_correct clampColor by
  unfold Pure.clampColor; loom_solve

prove_correct moodBoundsOf by
  unfold Pure.moodBoundsOf; loom_solve

prove_correct colorSatisfiesMood by
  unfold Pure.colorSatisfiesMood; loom_solve

prove_correct adjustColorSL by
  unfold Pure.adjustColorSL; loom_solve

prove_correct validBaseHue by
  unfold Pure.validBaseHue; loom_solve

prove_correct applySelectContrastPair by
  unfold Pure.applySelectContrastPair; loom_solve

-- ═══ Sorry ═══
prove_correct randomInRange by sorry
prove_correct goldenSLForMood by sorry
prove_correct generateColorGolden by sorry
prove_correct allColorsSatisfyMood by sorry
prove_correct huesMatchHarmony by sorry
prove_correct baseHarmonyHues by sorry
prove_correct allHarmonyHues by sorry
prove_correct generatePaletteColors by sorry
prove_correct validRandomSeeds by sorry
prove_correct init by sorry
prove_correct applyIndependentAdjustment by sorry
prove_correct applyLinkedAdjustment by sorry
prove_correct applySetColorDirect by sorry
prove_correct applyGeneratePalette by sorry
prove_correct applyAdjustPalette by sorry
prove_correct applyRegenerateMood by sorry
prove_correct applyRegenerateHarmony by sorry
prove_correct applyRandomizeBaseHue by sorry
prove_correct normalize by sorry
prove_correct apply by sorry
