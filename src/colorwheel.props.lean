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

@[simp] private theorem getElem!_of_lt {α : Type} [Inhabited α] (a : Array α) (i : Nat) (h : i < a.size) :
    a[i]! = a[i] := by
  simp [Array.getElem!_eq_getD, Array.getD, h]

set_option maxHeartbeats 800000 in
private theorem normalizeModel_idempotent (m : Model) (h : ModelInv m) :
    Pure.normalizeModel m = m := by
  unfold ModelInv at h
  obtain ⟨hbh0, hbh1, hcs, hcv, hcf0, hcf1, hcb0, hcb1, hmood, hharm⟩ := h
  have hbh := normalizeHue_idempotent _ hbh0 hbh1
  have hc0 := clampColor_idempotent _ (hcv 0 (by omega))
  have hc1 := clampColor_idempotent _ (hcv 1 (by omega))
  have hc2 := clampColor_idempotent _ (hcv 2 (by omega))
  have hc3 := clampColor_idempotent _ (hcv 3 (by omega))
  have hc4 := clampColor_idempotent _ (hcv 4 (by omega))
  -- Normalize getElem! in hypotheses first
  simp only [getElem!_of_lt _ _ (by omega : 0 < m.colors.size),
             getElem!_of_lt _ _ (by omega : 1 < m.colors.size),
             getElem!_of_lt _ _ (by omega : 2 < m.colors.size),
             getElem!_of_lt _ _ (by omega : 3 < m.colors.size),
             getElem!_of_lt _ _ (by omega : 4 < m.colors.size)] at hc0 hc1 hc2 hc3 hc4 hmood hharm
  -- Unfold normalizeModel + rewrite getElem! + apply clampColor identity — all in one pass
  simp only [Pure.normalizeModel, hcs, ↓reduceIte, hbh,
             getElem!_of_lt _ _ (by omega : 0 < m.colors.size),
             getElem!_of_lt _ _ (by omega : 1 < m.colors.size),
             getElem!_of_lt _ _ (by omega : 2 < m.colors.size),
             getElem!_of_lt _ _ (by omega : 3 < m.colors.size),
             getElem!_of_lt _ _ (by omega : 4 < m.colors.size),
             hc0, hc1, hc2, hc3, hc4]
  -- Reconstruct array equality
  have harr : #[m.colors[0], m.colors[1], m.colors[2], m.colors[3], m.colors[4]] = m.colors :=
    Array.ext (by simp [hcs]) (by intro i hi1 hi2; simp at hi1; interval_cases i <;> simp)
  simp only [harr, hmood, hharm, hcf0, hcf1, hcb0, hcb1, ↓reduceIte, and_self, ite_true]
  split_ifs <;> (cases m; simp_all)

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
set_option maxHeartbeats 800000 in
theorem selectContrastPairPreservesColors (m : Model) (fg bg : Int) (h : ModelInv m)
    (hfg : 0 ≤ fg ∧ fg < 5) (hbg : 0 ≤ bg ∧ bg < 5) :
    (Pure.step m (.SelectContrastPair fg bg)).colors = m.colors
    ∧ (Pure.step m (.SelectContrastPair fg bg)).mood = m.mood
    ∧ (Pure.step m (.SelectContrastPair fg bg)).harmony = m.harmony
    ∧ (Pure.step m (.SelectContrastPair fg bg)).baseHue = m.baseHue := by
  have hid := normalizeModel_idempotent m h
  simp only [Pure.step, Pure.apply, Pure.applySelectContrastPair]
  split_ifs
  · -- normalizeModel doesn't read contrastPair for colors/mood/harmony/baseHue
    -- so {m with contrastPair := _} produces the same result as m for those fields
    have hc : (Pure.normalizeModel {m with contrastPair := ⟨fg, bg⟩}).colors = (Pure.normalizeModel m).colors := rfl
    have hmo : (Pure.normalizeModel {m with contrastPair := ⟨fg, bg⟩}).mood = (Pure.normalizeModel m).mood := rfl
    have hha : (Pure.normalizeModel {m with contrastPair := ⟨fg, bg⟩}).harmony = (Pure.normalizeModel m).harmony := rfl
    have hbh : (Pure.normalizeModel {m with contrastPair := ⟨fg, bg⟩}).baseHue = (Pure.normalizeModel m).baseHue := rfl
    rw [hc, hmo, hha, hbh]; rw [hid]; exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [hid]; exact ⟨rfl, rfl, rfl, rfl⟩

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
  simp only
  have hinv := stepPreservesInv m (.GeneratePalette baseHue mood harmony seeds) h
  -- step m' (GP ...) = normalizeModel (apply m' (GP ...))
  -- apply m' (GP ...) applies generatePalette with same params
  -- normalizeModel on the result gives back m' (by idempotence)
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

-- Blocked by getElem vs getElem! on allHarmonyHues array
theorem harmonyOnlyDegradesToCustom (m : Model) (idx dH dS dL : Int) (_h : ModelInv m)
    (_hidx : 0 ≤ idx ∧ idx < 5) :
    let m' := Pure.step m (.AdjustColor idx dH dS dL)
    (m.harmony = .Custom → m'.harmony = .Custom)
    ∧ (m'.harmony ≠ .Custom → m'.harmony = m.harmony) := by sorry

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
    (hfg : 0 ≤ fg ∧ fg < 5) (hbg : 0 ≤ bg ∧ bg < 5) :
    Pure.step (Pure.step m (.SelectContrastPair fg bg)) (.SelectContrastPair fg bg)
    = Pure.step m (.SelectContrastPair fg bg) := by
  have hinv := stepPreservesInv m (.SelectContrastPair fg bg) h
  rw [Pure.step, Pure.apply]
  simp only [Pure.applySelectContrastPair]
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
