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

-- Helper lemmas for normalizeModel proof

private theorem normalizeHue_nonneg (h : Int) : 0 ≤ Pure.normalizeHue h := by
  simp only [Pure.normalizeHue]; split <;> omega

private theorem normalizeHue_lt (h : Int) : Pure.normalizeHue h < 360 := by
  simp only [Pure.normalizeHue]; split <;> omega

private theorem clamp_bounds (x lo hi : Int) (h : lo ≤ hi) :
    lo ≤ Pure.clamp x lo hi ∧ Pure.clamp x lo hi ≤ hi := by
  simp only [Pure.clamp]
  constructor <;> {split; omega; split <;> omega}

private theorem clampColor_valid (c : Color) : ValidColor (Pure.clampColor c) := by
  simp only [ValidColor, Pure.clampColor]
  exact ⟨normalizeHue_nonneg _, normalizeHue_lt _,
         (clamp_bounds _ 0 100 (by omega)).1, (clamp_bounds _ 0 100 (by omega)).2,
         (clamp_bounds _ 0 100 (by omega)).1, (clamp_bounds _ 0 100 (by omega)).2⟩

private lemma nm_baseHue_nonneg (m : Model) : 0 ≤ (Pure.normalizeModel m).baseHue :=
  normalizeHue_nonneg _

private lemma nm_baseHue_lt (m : Model) : (Pure.normalizeModel m).baseHue < 360 :=
  normalizeHue_lt _

private lemma nm_colors_size (m : Model) : (Pure.normalizeModel m).colors.size = 5 := by
  simp only [Pure.normalizeModel]; split <;> simp

private lemma nm_contrast_valid (m : Model) :
    0 ≤ (Pure.normalizeModel m).contrastPair.fg ∧ (Pure.normalizeModel m).contrastPair.fg < 5
    ∧ 0 ≤ (Pure.normalizeModel m).contrastPair.bg ∧ (Pure.normalizeModel m).contrastPair.bg < 5 := by
  simp only [Pure.normalizeModel]; split <;> simp_all

private lemma nm_colors_valid (m : Model) (i : Nat) (hi : i < 5) :
    ValidColor (Pure.normalizeModel m).colors[i]! := by
  simp only [Pure.normalizeModel]
  split
  · interval_cases i <;> exact clampColor_valid _
  · interval_cases i <;> decide

private lemma nm_mood (m : Model) :
    (Pure.normalizeModel m).mood ≠ .Custom →
    Pure.allColorsSatisfyMood (Pure.normalizeModel m).colors (Pure.normalizeModel m).mood = true := by
  simp only [Pure.normalizeModel]
  intro h; split_ifs at h ⊢ <;> simp_all

private lemma huesMatchHarmony_custom (colors : Array Color) (baseHue : Int) :
    Pure.huesMatchHarmony colors baseHue .Custom = true := by
  simp [Pure.huesMatchHarmony]

private lemma nm_harmony (m : Model) :
    Pure.huesMatchHarmony (Pure.normalizeModel m).colors (Pure.normalizeModel m).baseHue
      (Pure.normalizeModel m).harmony = true := by
  simp only [Pure.normalizeModel]
  split_ifs <;> (first | rfl | assumption)

theorem normalizeModel_satisfiesInv (m : Model) : ModelInv (Pure.normalizeModel m) := by
  exact ⟨nm_baseHue_nonneg m, nm_baseHue_lt m, nm_colors_size m, nm_colors_valid m,
         (nm_contrast_valid m).1, (nm_contrast_valid m).2.1,
         (nm_contrast_valid m).2.2.1, (nm_contrast_valid m).2.2.2,
         nm_mood m, nm_harmony m⟩

theorem stepPreservesInv (m : Model) (a : Action) (_h : ModelInv m) :
    ModelInv (Pure.step m a) := by
  unfold Pure.step
  exact normalizeModel_satisfiesInv _
