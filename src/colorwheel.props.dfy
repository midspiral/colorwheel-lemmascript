/*
ColorWheel Behavioral Properties
Adapted from dafny-replay/colorwheel/ColorWheelProps.dfy

Commutativity, idempotence, monotonicity, reachability,
field independence, and harmony geometry theorems.
*/

include "colorwheel.dfy"
include "colorwheel.proofs.dfy"

// ============================================================================
// Commutativity: SelectContrastPair with other actions
// ============================================================================

// SelectContrastPair only modifies contrastPair, so it commutes with
// any action that doesn't modify contrastPair

lemma SelectContrastPairCommutesWithAdjustColor(
  m: Model, fg: int, bg: int, idx: int, dH: int, dS: int, dL: int)
  requires Inv(m)
  requires 0 <= fg < 5 && 0 <= bg < 5
  requires 0 <= idx < 5
  ensures step(step(m, SelectContrastPair(fg, bg)), AdjustColor(idx, dH, dS, dL))
       == step(step(m, AdjustColor(idx, dH, dS, dL)), SelectContrastPair(fg, bg))
{
  StepPreservesInv(m, SelectContrastPair(fg, bg));
  StepPreservesInv(m, AdjustColor(idx, dH, dS, dL));
}

lemma SelectContrastPairCommutesWithAdjustPalette(
  m: Model, fg: int, bg: int, dH: int, dS: int, dL: int)
  requires Inv(m)
  requires 0 <= fg < 5 && 0 <= bg < 5
  ensures step(step(m, SelectContrastPair(fg, bg)), AdjustPalette(dH, dS, dL))
       == step(step(m, AdjustPalette(dH, dS, dL)), SelectContrastPair(fg, bg))
{
  StepPreservesInv(m, SelectContrastPair(fg, bg));
  StepPreservesInv(m, AdjustPalette(dH, dS, dL));

  // Help Dafny see that SCP only changes contrastPair
  var m_scp := step(m, SelectContrastPair(fg, bg));
  var m_ap := step(m, AdjustPalette(dH, dS, dL));

  // After SCP: colors/mood/harmony/baseHue/adjustments unchanged (just contrastPair)
  // After AP: contrastPair unchanged
  // So the two paths produce the same final state
  assert apply(m, SelectContrastPair(fg, bg)) == m.(contrastPair := ContrastPair(fg, bg));
  assert apply(m, AdjustPalette(dH, dS, dL)).contrastPair == m.contrastPair;
}

lemma SelectContrastPairCommutesWithSetColorDirect(
  m: Model, fg: int, bg: int, idx: int, c: Color)
  requires Inv(m)
  requires 0 <= fg < 5 && 0 <= bg < 5
  requires 0 <= idx < 5
  ensures step(step(m, SelectContrastPair(fg, bg)), SetColorDirect(idx, c))
       == step(step(m, SetColorDirect(idx, c)), SelectContrastPair(fg, bg))
{
  StepPreservesInv(m, SelectContrastPair(fg, bg));
  StepPreservesInv(m, SetColorDirect(idx, c));
}

// SelectContrastPair is idempotent
lemma SelectContrastPairIdempotent(m: Model, fg: int, bg: int)
  requires Inv(m)
  requires 0 <= fg < 5 && 0 <= bg < 5
  ensures step(step(m, SelectContrastPair(fg, bg)), SelectContrastPair(fg, bg))
       == step(m, SelectContrastPair(fg, bg))
{
  StepPreservesInv(m, SelectContrastPair(fg, bg));
}

// ============================================================================
// AdjustColor on different indices commutes
// ============================================================================

lemma AdjustColorCommutes(
  m: Model, i: int, j: int,
  dH1: int, dS1: int, dL1: int,
  dH2: int, dS2: int, dL2: int)
  requires Inv(m)
  requires 0 <= i < 5 && 0 <= j < 5 && i != j
  ensures step(step(m, AdjustColor(i, dH1, dS1, dL1)), AdjustColor(j, dH2, dS2, dL2))
       == step(step(m, AdjustColor(j, dH2, dS2, dL2)), AdjustColor(i, dH1, dS1, dL1))
{
  StepPreservesInv(m, AdjustColor(i, dH1, dS1, dL1));
  StepPreservesInv(m, AdjustColor(j, dH2, dS2, dL2));

  AdjustColorIndependentColors(m, i, j, dH1, dS1, dL1, dH2, dS2, dL2);
  AdjustColorMoodMonotonic(m, i, j, dH1, dS1, dL1, dH2, dS2, dL2);
  AdjustColorHarmonyMonotonic(m, i, j, dH1, dS1, dL1, dH2, dS2, dL2);
}

// Helper: Colors at different indices are set independently
lemma AdjustColorIndependentColors(
  m: Model, i: int, j: int,
  dH1: int, dS1: int, dL1: int,
  dH2: int, dS2: int, dL2: int)
  requires Inv(m)
  requires 0 <= i < 5 && 0 <= j < 5 && i != j
  ensures var m_ij := step(step(m, AdjustColor(i, dH1, dS1, dL1)), AdjustColor(j, dH2, dS2, dL2));
          var m_ji := step(step(m, AdjustColor(j, dH2, dS2, dL2)), AdjustColor(i, dH1, dS1, dL1));
          m_ij.colors == m_ji.colors
{
  StepPreservesInv(m, AdjustColor(i, dH1, dS1, dL1));
  StepPreservesInv(m, AdjustColor(j, dH2, dS2, dL2));

  var newColor_i := clampColor(Color(
    m.colors[i].h + dH1, m.colors[i].s + dS1, m.colors[i].l + dL1));
  var newColor_j := clampColor(Color(
    m.colors[j].h + dH2, m.colors[j].s + dS2, m.colors[j].l + dL2));
}

// Helper: Mood degradation is symmetric
lemma AdjustColorMoodMonotonic(
  m: Model, i: int, j: int,
  dH1: int, dS1: int, dL1: int,
  dH2: int, dS2: int, dL2: int)
  requires Inv(m)
  requires 0 <= i < 5 && 0 <= j < 5 && i != j
  ensures var m_ij := step(step(m, AdjustColor(i, dH1, dS1, dL1)), AdjustColor(j, dH2, dS2, dL2));
          var m_ji := step(step(m, AdjustColor(j, dH2, dS2, dL2)), AdjustColor(i, dH1, dS1, dL1));
          m_ij.mood == m_ji.mood
{
  StepPreservesInv(m, AdjustColor(i, dH1, dS1, dL1));
  StepPreservesInv(m, AdjustColor(j, dH2, dS2, dL2));

  var newColor_i := clampColor(Color(
    m.colors[i].h + dH1, m.colors[i].s + dS1, m.colors[i].l + dL1));
  var newColor_j := clampColor(Color(
    m.colors[j].h + dH2, m.colors[j].s + dS2, m.colors[j].l + dL2));

  var breaks_i := m.mood != Mood.Custom && !colorSatisfiesMood(newColor_i, m.mood);
  var breaks_j := m.mood != Mood.Custom && !colorSatisfiesMood(newColor_j, m.mood);
}

// Helper: Harmony degradation is symmetric
lemma AdjustColorHarmonyMonotonic(
  m: Model, i: int, j: int,
  dH1: int, dS1: int, dL1: int,
  dH2: int, dS2: int, dL2: int)
  requires Inv(m)
  requires 0 <= i < 5 && 0 <= j < 5 && i != j
  ensures var m_ij := step(step(m, AdjustColor(i, dH1, dS1, dL1)), AdjustColor(j, dH2, dS2, dL2));
          var m_ji := step(step(m, AdjustColor(j, dH2, dS2, dL2)), AdjustColor(i, dH1, dS1, dL1));
          m_ij.harmony == m_ji.harmony
{
  StepPreservesInv(m, AdjustColor(i, dH1, dS1, dL1));
  StepPreservesInv(m, AdjustColor(j, dH2, dS2, dL2));

  var newColor_i := clampColor(Color(
    m.colors[i].h + dH1, m.colors[i].s + dS1, m.colors[i].l + dL1));
  var newColor_j := clampColor(Color(
    m.colors[j].h + dH2, m.colors[j].s + dS2, m.colors[j].l + dL2));

  var expectedHues := allHarmonyHues(m.baseHue, m.harmony);

  var breaks_i := m.harmony != Harmony.Custom &&
                  |expectedHues| == 5 && newColor_i.h != expectedHues[i];
  var breaks_j := m.harmony != Harmony.Custom &&
                  |expectedHues| == 5 && newColor_j.h != expectedHues[j];
}

// ============================================================================
// GeneratePalette Properties
// ============================================================================

lemma GeneratePaletteResetsAdjustments(m: Model, baseHue: int, mood: Mood,
                                        harmony: Harmony, seeds: seq<int>)
  requires Inv(m)
  requires validBaseHue(baseHue)
  requires |seeds| == 10 && validRandomSeeds(seeds)
  ensures step(m, GeneratePalette(baseHue, mood, harmony, seeds)).adjustmentH == 0
  ensures step(m, GeneratePalette(baseHue, mood, harmony, seeds)).adjustmentS == 0
  ensures step(m, GeneratePalette(baseHue, mood, harmony, seeds)).adjustmentL == 0
{}

// GeneratePalette with same params is idempotent
lemma GeneratePaletteIdempotent(m: Model, baseHue: int, mood: Mood,
                                 harmony: Harmony, seeds: seq<int>)
  requires Inv(m)
  requires validBaseHue(baseHue)
  requires |seeds| == 10 && validRandomSeeds(seeds)
  ensures var m' := step(m, GeneratePalette(baseHue, mood, harmony, seeds));
          step(m', GeneratePalette(baseHue, mood, harmony, seeds)) == m'
{
  StepPreservesInv(m, GeneratePalette(baseHue, mood, harmony, seeds));
}

// ============================================================================
// Monotonicity of Degradation
// ============================================================================

// AdjustColor can only degrade mood to Custom, never restore it
lemma MoodOnlyDegradesToCustom(m: Model, idx: int, dH: int, dS: int, dL: int)
  requires Inv(m)
  requires 0 <= idx < 5
  ensures var m' := step(m, AdjustColor(idx, dH, dS, dL));
          m.mood == Mood.Custom ==> m'.mood == Mood.Custom
  ensures var m' := step(m, AdjustColor(idx, dH, dS, dL));
          m'.mood != Mood.Custom ==> m'.mood == m.mood
{
  StepPreservesInv(m, AdjustColor(idx, dH, dS, dL));
}

// AdjustColor can only degrade harmony to Custom, never restore it
lemma HarmonyOnlyDegradesToCustom(m: Model, idx: int, dH: int, dS: int, dL: int)
  requires Inv(m)
  requires 0 <= idx < 5
  ensures var m' := step(m, AdjustColor(idx, dH, dS, dL));
          m.harmony == Harmony.Custom ==> m'.harmony == Harmony.Custom
  ensures var m' := step(m, AdjustColor(idx, dH, dS, dL));
          m'.harmony != Harmony.Custom ==> m'.harmony == m.harmony
{
  StepPreservesInv(m, AdjustColor(idx, dH, dS, dL));
}

// ============================================================================
// Reachability
// ============================================================================

// Any valid color can be set at any index
lemma CanReachAnyColor(m: Model, idx: int, target: Color)
  requires Inv(m)
  requires 0 <= idx < 5
  requires ValidColor(target)
  ensures step(m, SetColorDirect(idx, target)).colors[idx] == target
{
  StepPreservesInv(m, SetColorDirect(idx, target));
}

// Any mood can be restored via RegenerateMood
lemma CanRecoverMood(m: Model, targetMood: Mood, seeds: seq<int>)
  requires Inv(m)
  requires |seeds| == 10 && validRandomSeeds(seeds)
  ensures step(m, RegenerateMood(targetMood, seeds)).mood == targetMood
{
  StepPreservesInv(m, RegenerateMood(targetMood, seeds));
}

// Any harmony can be restored via RegenerateHarmony
lemma CanRecoverHarmony(m: Model, targetHarmony: Harmony, seeds: seq<int>)
  requires Inv(m)
  requires |seeds| == 10 && validRandomSeeds(seeds)
  ensures step(m, RegenerateHarmony(targetHarmony, seeds)).harmony == targetHarmony
{
  // Help Dafny see that generated palette satisfies the new harmony
  var colors := generatePaletteColors(m.baseHue, m.mood, targetHarmony, seeds);
  GeneratePaletteColorsValid(m.baseHue, m.mood, targetHarmony, seeds);
  assert huesMatchHarmony(colors, m.baseHue, targetHarmony);
  StepPreservesInv(m, RegenerateHarmony(targetHarmony, seeds));
}

// ============================================================================
// Field Independence
// ============================================================================

// AdjustColor never changes contrastPair
lemma AdjustColorPreservesContrastPair(m: Model, idx: int, dH: int, dS: int, dL: int)
  requires Inv(m)
  requires 0 <= idx < 5
  ensures step(m, AdjustColor(idx, dH, dS, dL)).contrastPair == m.contrastPair
{}

// AdjustPalette never changes contrastPair
lemma AdjustPalettePreservesContrastPair(m: Model, dH: int, dS: int, dL: int)
  requires Inv(m)
  ensures step(m, AdjustPalette(dH, dS, dL)).contrastPair == m.contrastPair
{}

// SetColorDirect never changes contrastPair
lemma SetColorDirectPreservesContrastPair(m: Model, idx: int, c: Color)
  requires Inv(m)
  requires 0 <= idx < 5
  ensures step(m, SetColorDirect(idx, c)).contrastPair == m.contrastPair
{}

// SelectContrastPair never changes colors, mood, harmony, or baseHue
lemma SelectContrastPairPreservesColors(m: Model, fg: int, bg: int)
  requires Inv(m)
  requires 0 <= fg < 5 && 0 <= bg < 5
  ensures step(m, SelectContrastPair(fg, bg)).colors == m.colors
  ensures step(m, SelectContrastPair(fg, bg)).mood == m.mood
  ensures step(m, SelectContrastPair(fg, bg)).harmony == m.harmony
  ensures step(m, SelectContrastPair(fg, bg)).baseHue == m.baseHue
{}

// ============================================================================
// Domain-Specific: Harmony Geometry
// ============================================================================

// Complementary harmony: first two base hues are 180 degrees apart
lemma ComplementaryAre180Apart(m: Model)
  requires Inv(m)
  requires m.harmony == Harmony.Complementary
  ensures var hues := baseHarmonyHues(m.baseHue, m.harmony);
          |hues| >= 2 && hues[1] == normalizeHue(hues[0] + 180)
{}

// Triadic harmony: base hues are 120 degrees apart
lemma TriadicAre120Apart(m: Model)
  requires Inv(m)
  requires m.harmony == Harmony.Triadic
  ensures var hues := baseHarmonyHues(m.baseHue, m.harmony);
          |hues| >= 3 &&
          hues[1] == normalizeHue(hues[0] + 120) &&
          hues[2] == normalizeHue(hues[0] + 240)
{}

// Analogous harmony: all hues within 30 degrees of baseHue
lemma AnalogousWithin30(m: Model)
  requires Inv(m)
  requires m.harmony == Harmony.Analogous
  ensures var hues := allHarmonyHues(m.baseHue, m.harmony);
          |hues| == 5 &&
          hues[0] == normalizeHue(m.baseHue - 30) &&
          hues[1] == normalizeHue(m.baseHue - 15) &&
          hues[2] == m.baseHue &&
          hues[3] == normalizeHue(m.baseHue + 15) &&
          hues[4] == normalizeHue(m.baseHue + 30)
{}
