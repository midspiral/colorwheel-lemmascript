/-
  Behavioral properties of the ColorWheel spec.
  Ported from ColorWheelProps.dfy (dafny-replay).
-/
import «colorwheel.proof»

-- ═══ Foundational: idempotence of normalization on valid models ═══

private theorem normalizeHue_idempotent (h : Int) (h0 : 0 ≤ h) (h1 : h < 360) :
    Pure.normalizeHue h = h := by
  simp only [Pure.normalizeHue]; omega

private theorem clamp_idempotent (x lo hi : Int) (hlo : lo ≤ x) (hhi : x ≤ hi) :
    Pure.clamp x lo hi = x := by
  simp only [Pure.clamp]; omega

private theorem clampColor_idempotent (c : Color) (hv : ValidColor c) :
    Pure.clampColor c = c := by
  unfold ValidColor at hv; obtain ⟨hh0, hh1, hs0, hs1, hl0, hl1⟩ := hv
  show Color.mk _ _ _ = c
  rw [normalizeHue_idempotent _ hh0 hh1, clamp_idempotent _ _ _ hs0 hs1,
      clamp_idempotent _ _ _ hl0 hl1]

-- normalizeModel m = m when ModelInv m (colors array reconstruction is the hard part)
private theorem normalizeModel_idempotent (m : Model) (h : ModelInv m) :
    Pure.normalizeModel m = m := by sorry

-- ═══ Harmony Geometry ═══

theorem complementaryAre180Apart (baseHue : Int) :
    let hues := Pure.baseHarmonyHues baseHue .Complementary
    hues.size ≥ 2 ∧ hues[1]! = Pure.normalizeHue (hues[0]! + 180) := by
  simp [Pure.baseHarmonyHues]

theorem triadicAre120Apart (baseHue : Int) :
    let hues := Pure.baseHarmonyHues baseHue .Triadic
    hues.size ≥ 3
    ∧ hues[1]! = Pure.normalizeHue (hues[0]! + 120)
    ∧ hues[2]! = Pure.normalizeHue (hues[0]! + 240) := by
  simp [Pure.baseHarmonyHues]

theorem analogousWithin30 (baseHue : Int) :
    let hues := Pure.allHarmonyHues baseHue .Analogous
    hues.size = 5
    ∧ hues[0]! = Pure.normalizeHue (baseHue - 30)
    ∧ hues[1]! = Pure.normalizeHue (baseHue - 15)
    ∧ hues[2]! = baseHue
    ∧ hues[3]! = Pure.normalizeHue (baseHue + 15)
    ∧ hues[4]! = Pure.normalizeHue (baseHue + 30) := by
  simp [Pure.allHarmonyHues]

-- ═══ Field Independence ═══

private theorem apply_adjustColor_contrastPair (m : Model) (idx dH dS dL : Int) :
    (Pure.apply m (.AdjustColor idx dH dS dL)).contrastPair = m.contrastPair := by
  simp [Pure.apply, Pure.applyIndependentAdjustment]

private theorem apply_adjustPalette_contrastPair (m : Model) (dH dS dL : Int) :
    (Pure.apply m (.AdjustPalette dH dS dL)).contrastPair = m.contrastPair := by
  simp [Pure.apply, Pure.applyAdjustPalette, Pure.applyLinkedAdjustment]

private theorem apply_setColorDirect_contrastPair (m : Model) (idx : Int) (c : Color) :
    (Pure.apply m (.SetColorDirect idx c)).contrastPair = m.contrastPair := by
  simp [Pure.apply, Pure.applySetColorDirect]

private theorem normalizeModel_preserves_contrastPair (m : Model)
    (h0 : 0 ≤ m.contrastPair.fg) (h1 : m.contrastPair.fg < 5)
    (h2 : 0 ≤ m.contrastPair.bg) (h3 : m.contrastPair.bg < 5) :
    (Pure.normalizeModel m).contrastPair = m.contrastPair := by
  simp only [Pure.normalizeModel]; split_ifs <;> simp_all <;> omega

theorem adjustColorPreservesContrastPair (m : Model) (idx dH dS dL : Int) (h : ModelInv m) :
    (Pure.step m (.AdjustColor idx dH dS dL)).contrastPair = m.contrastPair := by
  unfold ModelInv at h; simp only [Pure.step]
  rw [normalizeModel_preserves_contrastPair]
  · exact apply_adjustColor_contrastPair m idx dH dS dL
  all_goals (simp [apply_adjustColor_contrastPair]; omega)

theorem adjustPalettePreservesContrastPair (m : Model) (dH dS dL : Int) (h : ModelInv m) :
    (Pure.step m (.AdjustPalette dH dS dL)).contrastPair = m.contrastPair := by
  unfold ModelInv at h; simp only [Pure.step]
  rw [normalizeModel_preserves_contrastPair]
  · exact apply_adjustPalette_contrastPair m dH dS dL
  all_goals (simp [apply_adjustPalette_contrastPair]; omega)

theorem setColorDirectPreservesContrastPair (m : Model) (idx : Int) (c : Color) (h : ModelInv m) :
    (Pure.step m (.SetColorDirect idx c)).contrastPair = m.contrastPair := by
  unfold ModelInv at h; simp only [Pure.step]
  rw [normalizeModel_preserves_contrastPair]
  · exact apply_setColorDirect_contrastPair m idx c
  all_goals (simp [apply_setColorDirect_contrastPair]; omega)

-- SelectContrastPair preserves colors, mood, harmony, baseHue
theorem selectContrastPairPreservesColors (m : Model) (fg bg : Int) (h : ModelInv m)
    (_hfg : 0 ≤ fg ∧ fg < 5) (_hbg : 0 ≤ bg ∧ bg < 5) :
    (Pure.step m (.SelectContrastPair fg bg)).colors = m.colors
    ∧ (Pure.step m (.SelectContrastPair fg bg)).mood = m.mood
    ∧ (Pure.step m (.SelectContrastPair fg bg)).harmony = m.harmony
    ∧ (Pure.step m (.SelectContrastPair fg bg)).baseHue = m.baseHue := by
  -- SelectContrastPair only changes contrastPair;
  -- normalizeModel on a valid-except-contrastPair model preserves the rest
  -- Requires normalizeModel_idempotent under {m with contrastPair := ...}
  sorry

-- ═══ GeneratePalette Properties ═══

theorem generatePaletteResetsAdjustments (m : Model) (baseHue : Int) (mood : Mood)
    (harmony : Harmony) (seeds : Array Int) (_h : ModelInv m)
    (hvb : Pure.validBaseHue baseHue = true) (hvs : seeds.size = 10)
    (hvr : Pure.validRandomSeeds seeds = true) :
    (Pure.step m (.GeneratePalette baseHue mood harmony seeds)).adjustmentH = 0
    ∧ (Pure.step m (.GeneratePalette baseHue mood harmony seeds)).adjustmentS = 0
    ∧ (Pure.step m (.GeneratePalette baseHue mood harmony seeds)).adjustmentL = 0 := by
  simp only [Pure.step, Pure.apply, Pure.applyGeneratePalette, Pure.validBaseHue] at *
  split_ifs <;> simp_all [Pure.normalizeModel]

theorem generatePaletteIdempotent (m : Model) (baseHue : Int) (mood : Mood)
    (harmony : Harmony) (seeds : Array Int) (h : ModelInv m)
    (_hvb : Pure.validBaseHue baseHue = true) (_hvs : seeds.size = 10)
    (_hvr : Pure.validRandomSeeds seeds = true) :
    let m' := Pure.step m (.GeneratePalette baseHue mood harmony seeds)
    Pure.step m' (.GeneratePalette baseHue mood harmony seeds) = m' := by
  -- m' satisfies ModelInv; applying same GeneratePalette produces same apply result;
  -- normalizeModel is idempotent on valid models
  simp only
  have hinv := stepPreservesInv m (.GeneratePalette baseHue mood harmony seeds) h
  sorry

-- ═══ Monotonicity of Degradation ═══

set_option maxHeartbeats 400000 in
theorem moodOnlyDegradesToCustom (m : Model) (idx dH dS dL : Int) (_h : ModelInv m)
    (_hidx : 0 ≤ idx ∧ idx < 5) :
    let m' := Pure.step m (.AdjustColor idx dH dS dL)
    (m.mood = .Custom → m'.mood = .Custom)
    ∧ (m'.mood ≠ .Custom → m'.mood = m.mood) := by
  simp only [Pure.step, Pure.apply, Pure.applyIndependentAdjustment, Pure.normalizeModel]
  constructor <;> (intro hm; split_ifs <;> simp_all)

-- getElem vs getElem! mismatch blocks automation; needs dedicated simp lemmas
theorem harmonyOnlyDegradesToCustom (m : Model) (idx dH dS dL : Int) (_h : ModelInv m)
    (_hidx : 0 ≤ idx ∧ idx < 5) :
    let m' := Pure.step m (.AdjustColor idx dH dS dL)
    (m.harmony = .Custom → m'.harmony = .Custom)
    ∧ (m'.harmony ≠ .Custom → m'.harmony = m.harmony) := by
  sorry

-- ═══ Reachability ═══

theorem canReachAnyColor (m : Model) (idx : Int) (target : Color) (_h : ModelInv m)
    (_hidx : 0 ≤ idx ∧ idx < 5) (_hv : ValidColor target) :
    (Pure.step m (.SetColorDirect idx target)).colors[idx.toNat]! = target := by
  sorry

theorem canRecoverMood (m : Model) (targetMood : Mood) (seeds : Array Int) (_h : ModelInv m)
    (_hvs : seeds.size = 10) (_hvr : Pure.validRandomSeeds seeds = true) :
    (Pure.step m (.RegenerateMood targetMood seeds)).mood = targetMood := by
  sorry

theorem canRecoverHarmony (m : Model) (targetHarmony : Harmony) (seeds : Array Int) (_h : ModelInv m)
    (_hvs : seeds.size = 10) (_hvr : Pure.validRandomSeeds seeds = true) :
    (Pure.step m (.RegenerateHarmony targetHarmony seeds)).harmony = targetHarmony := by
  sorry

-- ═══ Idempotence ═══

theorem selectContrastPairIdempotent (m : Model) (fg bg : Int) (h : ModelInv m)
    (_hfg : 0 ≤ fg ∧ fg < 5) (_hbg : 0 ≤ bg ∧ bg < 5) :
    Pure.step (Pure.step m (.SelectContrastPair fg bg)) (.SelectContrastPair fg bg)
    = Pure.step m (.SelectContrastPair fg bg) := by
  have hinv := stepPreservesInv m (.SelectContrastPair fg bg) h
  sorry

-- ═══ Commutativity ═══

theorem selectContrastPairCommutesWithAdjustColor (m : Model) (fg bg idx dH dS dL : Int)
    (_h : ModelInv m) (_hfg : 0 ≤ fg ∧ fg < 5) (_hbg : 0 ≤ bg ∧ bg < 5) :
    Pure.step (Pure.step m (.SelectContrastPair fg bg)) (.AdjustColor idx dH dS dL)
    = Pure.step (Pure.step m (.AdjustColor idx dH dS dL)) (.SelectContrastPair fg bg) := by
  sorry

theorem selectContrastPairCommutesWithAdjustPalette (m : Model) (fg bg dH dS dL : Int)
    (_h : ModelInv m) (_hfg : 0 ≤ fg ∧ fg < 5) (_hbg : 0 ≤ bg ∧ bg < 5) :
    Pure.step (Pure.step m (.SelectContrastPair fg bg)) (.AdjustPalette dH dS dL)
    = Pure.step (Pure.step m (.AdjustPalette dH dS dL)) (.SelectContrastPair fg bg) := by
  sorry

theorem selectContrastPairCommutesWithSetColorDirect (m : Model) (fg bg idx : Int) (c : Color)
    (_h : ModelInv m) (_hfg : 0 ≤ fg ∧ fg < 5) (_hbg : 0 ≤ bg ∧ bg < 5) :
    Pure.step (Pure.step m (.SelectContrastPair fg bg)) (.SetColorDirect idx c)
    = Pure.step (Pure.step m (.SetColorDirect idx c)) (.SelectContrastPair fg bg) := by
  sorry

theorem adjustColorCommutes (m : Model) (i j dH1 dS1 dL1 dH2 dS2 dL2 : Int)
    (_h : ModelInv m) (_hi : 0 ≤ i ∧ i < 5) (_hj : 0 ≤ j ∧ j < 5) (_hne : i ≠ j) :
    Pure.step (Pure.step m (.AdjustColor i dH1 dS1 dL1)) (.AdjustColor j dH2 dS2 dL2)
    = Pure.step (Pure.step m (.AdjustColor j dH2 dS2 dL2)) (.AdjustColor i dH1 dS1 dL1) := by
  sorry
