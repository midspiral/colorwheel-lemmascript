import «colorwheel.def»

set_option velvet.semantics.termination "total"

-- `normalizeHue`/`goldenSLForMood` use `Int.tmod` (JS `%` truncates toward zero),
-- which `omega`/`grind` don't reason about natively. These bounds let them close.
attribute [local grind] Int.tmod_lt_of_pos Int.lt_tmod_of_pos

-- ═══ Pure helpers ═══
prove_correct clamp by
  velvet_vcgen [clamp] with finish [Pure.clamp]
prove_correct normalizeHue by
  velvet_vcgen [normalizeHue] with finish [Pure.normalizeHue]
prove_correct clampColor by
  velvet_vcgen [clampColor] with finish [Pure.clampColor, Pure.normalizeHue, Pure.clamp]
prove_correct moodBoundsOf by
  velvet_vcgen [moodBoundsOf] with finish [Pure.moodBoundsOf]
prove_correct colorSatisfiesMood by
  velvet_vcgen [colorSatisfiesMood] with finish [Pure.colorSatisfiesMood]
prove_correct adjustColorSL by
  velvet_vcgen [adjustColorSL] with finish [Pure.adjustColorSL]
prove_correct validBaseHue by
  velvet_vcgen [validBaseHue] with finish [Pure.validBaseHue]
prove_correct applySelectContrastPair by
  velvet_vcgen [applySelectContrastPair] with finish [Pure.applySelectContrastPair]
prove_correct randomInRange by
  velvet_vcgen [randomInRange] with first
    (apply Pure.randomInRange_ge <;> finish)
    (apply Pure.randomInRange_le <;> finish)
prove_correct validRandomSeeds by
  velvet_vcgen [validRandomSeeds] with finish [Pure.validRandomSeeds]
prove_correct allColorsSatisfyMood by
  velvet_vcgen [allColorsSatisfyMood] with finish [Pure.allColorsSatisfyMood]
prove_correct baseHarmonyHues by
  velvet_vcgen [baseHarmonyHues] with finish [Pure.baseHarmonyHues]
prove_correct allHarmonyHues by
  velvet_vcgen [allHarmonyHues] with finish [Pure.allHarmonyHues]
prove_correct huesMatchHarmony by
  velvet_vcgen [huesMatchHarmony] with finish [Pure.huesMatchHarmony]

-- ═══ Generation ═══
prove_correct goldenSLForMood by
  velvet_vcgen [goldenSLForMood] with try finish
prove_correct generateColorGolden by
  velvet_vcgen [generateColorGolden] with try finish
prove_correct generatePaletteColors by
  velvet_vcgen [generatePaletteColors] with try finish
prove_correct init by
  velvet_vcgen [init] with try finish

-- ═══ Transitions (now pure with ternaries) ═══
prove_correct applyGeneratePalette by
  velvet_vcgen [applyGeneratePalette] with try finish
prove_correct applyRegenerateMood by
  velvet_vcgen [applyRegenerateMood] with try finish
prove_correct applyRegenerateHarmony by
  velvet_vcgen [applyRegenerateHarmony] with try finish
prove_correct applyRandomizeBaseHue by
  velvet_vcgen [applyRandomizeBaseHue] with try finish
prove_correct applyIndependentAdjustment by
  velvet_vcgen [applyIndependentAdjustment] with try finish
prove_correct applySetColorDirect by
  velvet_vcgen [applySetColorDirect] with try finish
prove_correct applyLinkedAdjustment by
  velvet_vcgen [applyLinkedAdjustment] with try finish
prove_correct applyAdjustPalette by
  velvet_vcgen [applyAdjustPalette] with try finish
prove_correct normalizeModel by
  velvet_vcgen [normalizeModel] with try finish
prove_correct apply by
  velvet_vcgen [apply] with try finish
prove_correct step by
  velvet_vcgen [step] with try finish

-- ═══ Invariant theorems ═══

theorem initSatisfiesInv : ModelInv (Pure.init) := by decide

-- Helper lemmas for normalizeModel proof

private theorem normalizeHue_nonneg (h : Int) : 0 ≤ Pure.normalizeHue h := by
  have := Int.lt_tmod_of_pos h (show (0:Int) < 360 by omega)
  simp only [Pure.normalizeHue]; split <;> omega

private theorem normalizeHue_lt (h : Int) : Pure.normalizeHue h < 360 := by
  have := Int.tmod_lt_of_pos h (show (0:Int) < 360 by omega)
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
