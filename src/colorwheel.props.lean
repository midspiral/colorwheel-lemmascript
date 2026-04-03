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

@[simp] private theorem normalizeHue_idem (h : Int) :
    Pure.normalizeHue (Pure.normalizeHue h) = Pure.normalizeHue h :=
  normalizeHue_idempotent _ (by simp only [Pure.normalizeHue]; split <;> omega)
    (by simp only [Pure.normalizeHue]; split <;> omega)

@[simp] private theorem clampColor_idem (c : Color) :
    Pure.clampColor (Pure.clampColor c) = Pure.clampColor c :=
  clampColor_idempotent _ (by constructor <;> simp only [Pure.clampColor, Pure.normalizeHue, Pure.clamp] <;> split <;> omega)

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

-- normalizeModel is idempotent on ANY model (not just valid ones)
private theorem normalizeModel_idem (m : Model) :
    Pure.normalizeModel (Pure.normalizeModel m) = Pure.normalizeModel m :=
  normalizeModel_idempotent _ (normalizeModel_satisfiesInv m)

@[simp] private theorem allHarmonyHues_size (baseHue : Int) (harmony : Harmony)
    (h : harmony ≠ .Custom) : (Pure.allHarmonyHues baseHue harmony).size = 5 := by
  cases harmony <;> simp_all [Pure.allHarmonyHues]

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
  -- Both steps apply GP with same params: the only difference is contrastPair
  -- (from m vs from normalizeModel result). normalizeModel's non-cp output is cp-independent (rfl).
  simp only [Pure.step, Pure.apply, Pure.applyGeneratePalette, Pure.validBaseHue]
  split_ifs with hv
  · -- params invalid: contradicts preconditions
    exfalso; simp_all [Pure.validBaseHue]
  · -- params valid: two normalizeModel calls on inputs differing only in contrastPair
    -- Show the contrastPair from normalizeModel equals m.contrastPair (ModelInv → valid cp)
    unfold ModelInv at h; obtain ⟨_, _, _, _, hcf0, hcf1, hcb0, hcb1, _, _⟩ := h
    rw [normalizeModel_preserves_contrastPair
      (⟨baseHue, mood, harmony, Pure.generatePaletteColors baseHue mood harmony seeds,
        m.contrastPair, 0, 0, 0⟩ : Model) hcf0 hcf1 hcb0 hcb1]

-- ═══ Monotonicity of Degradation ═══

set_option maxHeartbeats 400000 in
theorem moodOnlyDegradesToCustom (m : Model) (idx dH dS dL : Int) (_h : ModelInv m)
    (_hidx : 0 ≤ idx ∧ idx < 5) :
    let m' := Pure.step m (.AdjustColor idx dH dS dL)
    (m.mood = .Custom → m'.mood = .Custom)
    ∧ (m'.mood ≠ .Custom → m'.mood = m.mood) := by
  simp only [Pure.step, Pure.apply, Pure.applyIndependentAdjustment, Pure.normalizeModel]
  constructor <;> (intro hm; split_ifs <;> simp_all)

set_option maxHeartbeats 800000 in
theorem harmonyOnlyDegradesToCustom (m : Model) (idx dH dS dL : Int) (h : ModelInv m)
    (hidx : 0 ≤ idx ∧ idx < 5) :
    let m' := Pure.step m (.AdjustColor idx dH dS dL)
    (m.harmony = .Custom → m'.harmony = .Custom)
    ∧ (m'.harmony ≠ .Custom → m'.harmony = m.harmony) := by
  unfold ModelInv at h; obtain ⟨_, _, hcs, _, _, _, _, _, _, _⟩ := h
  simp only [Pure.step, Pure.apply, Pure.applyIndependentAdjustment, Pure.normalizeModel,
             getElem!_of_lt _ _ (by omega : idx.toNat < m.colors.size)]
  constructor <;> intro hm <;> split_ifs <;>
    simp_all [getElem!_of_lt, allHarmonyHues_size]
  -- One remaining: a[i] ≠ a[i]! is contradictory when size is known
  exfalso; obtain ⟨_, hsz, habs⟩ := ‹_ ∧ _ ∧ ¬_›
  rw [getElem!_of_lt _ _ (hsz ▸ by omega)] at habs; exact habs rfl

-- ═══ Core arithmetic: generated colors satisfy their mood ═══

-- clampColor preserves s/l when already in [0, 100]
private lemma clampColor_preserves_sl (c : Color) :
    (Pure.clampColor c).s = Pure.clamp c.s 0 100 ∧ (Pure.clampColor c).l = Pure.clamp c.l 0 100 := by
  simp [Pure.clampColor]

-- A single generated color satisfies its mood (the key arithmetic lemma).
-- Individual bound args for simp-friendly side condition discharge.
set_option maxHeartbeats 800000 in
private lemma colorSatisfiesMood_of_generated_core (mood : Mood) (h i seedS seedL : Int)
    (hi : 0 ≤ i ∧ i < 5) (hs : 0 ≤ seedS ∧ seedS ≤ 100) (hl : 0 ≤ seedL ∧ seedL ≤ 100) :
    Pure.colorSatisfiesMood (Pure.clampColor (Pure.generateColorGolden h mood i seedS seedL)) mood = true := by
  -- Don't unfold randomInRange - use its spec lemmas for bounds
  simp only [Pure.generateColorGolden, Pure.goldenSLForMood, Pure.moodBoundsOf,
             Pure.colorSatisfiesMood, Pure.clampColor, Pure.clamp, Pure.normalizeHue,
             decide_eq_true_eq]
  -- spreadS/spreadL are in [0, 100] from % 101
  set sS := (seedS + i * 62) % 101
  set sL := (seedL + i * 38) % 101
  have hsS0 : 0 ≤ sS := Int.emod_nonneg _ (by omega)
  have hsS1 : sS ≤ 100 := by have := Int.emod_lt_of_pos (seedS + i * 62) (by omega : (101 : Int) > 0); omega
  have hsL0 : 0 ≤ sL := Int.emod_nonneg _ (by omega)
  have hsL1 : sL ≤ 100 := by have := Int.emod_lt_of_pos (seedL + i * 38) (by omega : (101 : Int) > 0); omega
  -- Per mood: each first branch provides bounds + closes with omega
  have rge := @Pure.randomInRange_ge; have rle := @Pure.randomInRange_le
  cases mood <;> simp only [decide_eq_true_eq] <;> first
    | trivial
    | (have := rge sS 70 100 hsS0 hsS1 (by omega); have := rle sS 70 100 hsS0 hsS1 (by omega)
       have := rge sL 40 60 hsL0 hsL1 (by omega); have := rle sL 40 60 hsL0 hsL1 (by omega)
       split_ifs <;> omega)
    | (have := rge sS 20 45 hsS0 hsS1 (by omega); have := rle sS 20 45 hsS0 hsS1 (by omega)
       have := rge sL 55 75 hsL0 hsL1 (by omega); have := rle sL 55 75 hsL0 hsL1 (by omega)
       split_ifs <;> omega)
    | (have := rge sS 0 35 hsS0 hsS1 (by omega); have := rle sS 0 35 hsS0 hsS1 (by omega)
       have := rge sL 75 100 hsL0 hsL1 (by omega); have := rle sL 75 100 hsL0 hsL1 (by omega)
       split_ifs <;> omega)
    | (have := rge sS 60 100 hsS0 hsS1 (by omega); have := rle sS 60 100 hsS0 hsS1 (by omega)
       have := rge sL 25 45 hsL0 hsL1 (by omega); have := rle sL 25 45 hsL0 hsL1 (by omega)
       split_ifs <;> omega)
    | (have := rge sS 15 40 hsS0 hsS1 (by omega); have := rle sS 15 40 hsS0 hsS1 (by omega)
       have := rge sL 30 60 hsL0 hsL1 (by omega); have := rle sL 30 60 hsL0 hsL1 (by omega)
       split_ifs <;> omega)
    | (have := rge sS 90 100 hsS0 hsS1 (by omega); have := rle sS 90 100 hsS0 hsS1 (by omega)
       have := rge sL 50 65 hsL0 hsL1 (by omega); have := rle sL 50 65 hsL0 hsL1 (by omega)
       split_ifs <;> omega)

-- Simp-friendly wrapper with individual bound args for automatic side condition discharge
@[simp] private lemma colorSatisfiesMood_of_generated (mood : Mood) (h i seedS seedL : Int)
    (hs0 : 0 ≤ seedS) (hs1 : seedS ≤ 100) (hl0 : 0 ≤ seedL) (hl1 : seedL ≤ 100)
    (hi0 : 0 ≤ i) (hi1 : i < 5) :
    Pure.colorSatisfiesMood (Pure.clampColor (Pure.generateColorGolden h mood i seedS seedL)) mood = true :=
  colorSatisfiesMood_of_generated_core mood h i seedS seedL ⟨hi0, hi1⟩ ⟨hs0, hs1⟩ ⟨hl0, hl1⟩

-- ═══ Reachability ═══

theorem canReachAnyColor (m : Model) (idx : Int) (target : Color) (_h : ModelInv m)
    (_hidx : 0 ≤ idx ∧ idx < 5) (_hv : ValidColor target) :
    (Pure.step m (.SetColorDirect idx target)).colors[idx.toNat]! = target := by
  sorry

set_option maxHeartbeats 1600000 in
set_option auto.smt.timeout 30 in
theorem canRecoverMood (m : Model) (targetMood : Mood) (seeds : Array Int) (h : ModelInv m)
    (hvs : seeds.size = 10) (hvr : Pure.validRandomSeeds seeds = true) :
    (Pure.step m (.RegenerateMood targetMood seeds)).mood = targetMood := by
  unfold ModelInv at h; obtain ⟨hbh0, hbh1, hcs, _, _, _, _, _, _, _⟩ := h
  simp only [Pure.step, Pure.apply, Pure.applyRegenerateMood, Pure.validRandomSeeds] at *
  split_ifs with hv
  · -- invalid seeds: model unchanged, need m.mood = targetMood... contradiction
    exfalso; simp_all
  · -- valid seeds: generated colors satisfy mood → normalizeModel preserves mood
    simp only [Pure.validRandomSeeds, Bool.and_eq_true, decide_eq_true_eq,
               getElem!_of_lt seeds 0 (by omega), getElem!_of_lt seeds 1 (by omega),
               getElem!_of_lt seeds 2 (by omega), getElem!_of_lt seeds 3 (by omega),
               getElem!_of_lt seeds 4 (by omega), getElem!_of_lt seeds 5 (by omega),
               getElem!_of_lt seeds 6 (by omega), getElem!_of_lt seeds 7 (by omega),
               getElem!_of_lt seeds 8 (by omega), getElem!_of_lt seeds 9 (by omega)] at hvr
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hvr
    simp only [Pure.normalizeModel, Pure.allColorsSatisfyMood,
               Pure.generatePaletteColors,
               getElem!_of_lt seeds 0 (by omega), getElem!_of_lt seeds 1 (by omega),
               getElem!_of_lt seeds 2 (by omega), getElem!_of_lt seeds 3 (by omega),
               getElem!_of_lt seeds 4 (by omega), getElem!_of_lt seeds 5 (by omega),
               getElem!_of_lt seeds 6 (by omega), getElem!_of_lt seeds 7 (by omega),
               getElem!_of_lt seeds 8 (by omega), getElem!_of_lt seeds 9 (by omega),
               colorSatisfiesMood_of_generated, Bool.and_eq_true, decide_eq_true_eq,
               eq_iff_iff, iff_true]
    split_ifs <;> simp_all

set_option maxHeartbeats 1600000 in
theorem canRecoverHarmony (m : Model) (targetHarmony : Harmony) (seeds : Array Int) (h : ModelInv m)
    (hvs : seeds.size = 10) (hvr : Pure.validRandomSeeds seeds = true) :
    (Pure.step m (.RegenerateHarmony targetHarmony seeds)).harmony = targetHarmony := by
  unfold ModelInv at h; obtain ⟨hbh0, hbh1, hcs, _, _, _, _, _, _, _⟩ := h
  simp only [Pure.step, Pure.apply, Pure.applyRegenerateHarmony, Pure.validRandomSeeds] at *
  split_ifs with hv
  · exfalso; simp_all
  · -- Key: normalizeHue_idempotent aligns baseHues, normalizeHue_idem handles double-normalize
    simp only [Pure.normalizeModel, normalizeHue_idempotent _ hbh0 hbh1, normalizeHue_idem,
               Pure.huesMatchHarmony, Pure.generatePaletteColors, Pure.allHarmonyHues,
               Pure.generateColorGolden, Pure.clampColor, Pure.allColorsSatisfyMood]
    cases targetHarmony <;> simp_all [normalizeHue_idempotent _ hbh0 hbh1]

-- ═══ Idempotence ═══

set_option maxHeartbeats 800000 in
theorem selectContrastPairIdempotent (m : Model) (fg bg : Int) (h : ModelInv m)
    (hfg : 0 ≤ fg ∧ fg < 5) (hbg : 0 ≤ bg ∧ bg < 5) :
    Pure.step (Pure.step m (.SelectContrastPair fg bg)) (.SelectContrastPair fg bg)
    = Pure.step m (.SelectContrastPair fg bg) := by
  simp only [Pure.step, Pure.apply, Pure.applySelectContrastPair]
  split_ifs with hv1
  · -- normalizeModel {normalizeModel {m with cp} with cp} = normalizeModel {m with cp}
    -- Non-cp fields: normalizeModel reads same inputs (rfl for cp independence)
    -- cp field: same {fg,bg} on both sides
    simp only [Pure.normalizeModel]; cases m; split_ifs <;> simp_all
    -- Remaining: clampColor on defaults (decide) or ModelInv vs ¬size=5 (contradiction)
    all_goals (first | decide | (exact absurd h.2.2.1 ‹_›) | (constructor <;> first | decide | exact absurd h.2.2.1 ‹_›))
  · -- normalizeModel (normalizeModel m) = normalizeModel m
    exact normalizeModel_idempotent _ (normalizeModel_satisfiesInv m)

-- ═══ Commutativity ═══

-- Key helper: normalizeModel on two models that differ only in contrastPair
-- produces the same result when given the same contrastPair override.
-- This is because normalizeModel's non-cp computation is cp-independent.
private lemma normalizeModel_cp_congr (m₁ m₂ : Model) (cp : ContrastPair)
    (h : Pure.normalizeModel m₁ = Pure.normalizeModel m₂) :
    Pure.normalizeModel {m₁ with contrastPair := cp}
    = Pure.normalizeModel {m₂ with contrastPair := cp} := by
  -- Non-cp fields of normalizeModel are cp-independent (rfl), so they match via h.
  -- Cp field: both have same cp input, so normalizeModel produces same cp output.
  cases m₁; cases m₂
  simp only [Pure.normalizeModel, Model.mk.injEq] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, trivial, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

-- All three SCP-commutes proofs follow the same pattern:
-- valid SCP: use normalizeModel_cp_congr + normalizeModel_idem
-- invalid SCP: contradicts hfg/hbg

-- {m with cp} satisfies ModelInv when m does and cp is valid
private lemma modelInv_with_cp (m : Model) (cp : ContrastPair) (h : ModelInv m)
    (h0 : 0 ≤ cp.fg) (h1 : cp.fg < 5) (h2 : 0 ≤ cp.bg) (h3 : cp.bg < 5) :
    ModelInv {m with contrastPair := cp} := by
  unfold ModelInv at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h0, h1, h2, h3, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

-- Actions are cp-independent: applying to {m with cp} = {apply m with cp}
-- These are rfl because the apply functions use { m with ... } overriding
-- only non-cp fields, so cp passes through unchanged.
private lemma adjIndep_cp (m : Model) (cp : ContrastPair) (idx dH dS dL : Int) :
    Pure.applyIndependentAdjustment {m with contrastPair := cp} idx dH dS dL
    = {Pure.applyIndependentAdjustment m idx dH dS dL with contrastPair := cp} := rfl

private lemma adjPalette_cp (m : Model) (cp : ContrastPair) (dH dS dL : Int) :
    Pure.applyAdjustPalette {m with contrastPair := cp} dH dS dL
    = {Pure.applyAdjustPalette m dH dS dL with contrastPair := cp} := rfl

private lemma setDirect_cp (m : Model) (cp : ContrastPair) (idx : Int) (c : Color) :
    Pure.applySetColorDirect {m with contrastPair := cp} idx c
    = {Pure.applySetColorDirect m idx c with contrastPair := cp} := rfl

-- SCP commutativity: SCP only changes cp; other actions don't read cp.
-- Proof: normalizeModel_idempotent on {m with cp} + normalizeModel_cp_congr + normalizeModel_idem.

theorem selectContrastPairCommutesWithAdjustColor (m : Model) (fg bg idx dH dS dL : Int)
    (h : ModelInv m) (hfg : 0 ≤ fg ∧ fg < 5) (hbg : 0 ≤ bg ∧ bg < 5) :
    Pure.step (Pure.step m (.SelectContrastPair fg bg)) (.AdjustColor idx dH dS dL)
    = Pure.step (Pure.step m (.AdjustColor idx dH dS dL)) (.SelectContrastPair fg bg) := by
  simp only [Pure.step, Pure.apply, Pure.applySelectContrastPair]
  split_ifs
  · -- valid: use cp-independence rfl lemma + normalizeModel_cp_congr
    rw [normalizeModel_idempotent _ (modelInv_with_cp m _ h hfg.1 hfg.2 hbg.1 hbg.2),
        adjIndep_cp m ⟨fg, bg⟩ idx dH dS dL]
    exact normalizeModel_cp_congr _ _ _ (normalizeModel_idem _).symm
  · -- invalid: normalizeModel_idempotent + normalizeModel_idem
    simp only [normalizeModel_idempotent m h]; exact (normalizeModel_idem _).symm

theorem selectContrastPairCommutesWithAdjustPalette (m : Model) (fg bg dH dS dL : Int)
    (h : ModelInv m) (hfg : 0 ≤ fg ∧ fg < 5) (hbg : 0 ≤ bg ∧ bg < 5) :
    Pure.step (Pure.step m (.SelectContrastPair fg bg)) (.AdjustPalette dH dS dL)
    = Pure.step (Pure.step m (.AdjustPalette dH dS dL)) (.SelectContrastPair fg bg) := by
  simp only [Pure.step, Pure.apply, Pure.applySelectContrastPair]
  split_ifs
  · rw [normalizeModel_idempotent _ (modelInv_with_cp m _ h hfg.1 hfg.2 hbg.1 hbg.2),
        adjPalette_cp m ⟨fg, bg⟩ dH dS dL]
    exact normalizeModel_cp_congr _ _ _ (normalizeModel_idem _).symm
  · simp only [normalizeModel_idempotent m h]; exact (normalizeModel_idem _).symm

theorem selectContrastPairCommutesWithSetColorDirect (m : Model) (fg bg idx : Int) (c : Color)
    (h : ModelInv m) (hfg : 0 ≤ fg ∧ fg < 5) (hbg : 0 ≤ bg ∧ bg < 5) :
    Pure.step (Pure.step m (.SelectContrastPair fg bg)) (.SetColorDirect idx c)
    = Pure.step (Pure.step m (.SetColorDirect idx c)) (.SelectContrastPair fg bg) := by
  simp only [Pure.step, Pure.apply, Pure.applySelectContrastPair]
  split_ifs
  · rw [normalizeModel_idempotent _ (modelInv_with_cp m _ h hfg.1 hfg.2 hbg.1 hbg.2),
        setDirect_cp m ⟨fg, bg⟩ idx c]
    exact normalizeModel_cp_congr _ _ _ (normalizeModel_idem _).symm
  · simp only [normalizeModel_idempotent m h]; exact (normalizeModel_idem _).symm

theorem adjustColorCommutes (m : Model) (i j dH1 dS1 dL1 dH2 dS2 dL2 : Int)
    (_h : ModelInv m) (_hi : 0 ≤ i ∧ i < 5) (_hj : 0 ≤ j ∧ j < 5) (_hne : i ≠ j) :
    Pure.step (Pure.step m (.AdjustColor i dH1 dS1 dL1)) (.AdjustColor j dH2 dS2 dL2)
    = Pure.step (Pure.step m (.AdjustColor j dH2 dS2 dL2)) (.AdjustColor i dH1 dS1 dL1) := by
  sorry
