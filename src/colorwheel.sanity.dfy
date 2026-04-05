/*
ColorWheel Sanity - Complete Enumeration of NoOp Cases
Adapted from dafny-replay/colorwheel/ColorWheelSanity.dfy

Proves that we have identified ALL cases where apply(m, a) == m
for valid actions. (Invalid-index cases are excluded since the
generated spec requires validAction(a) as a precondition.)
*/

include "colorwheel.dfy"
include "colorwheel.proofs.dfy"

// ============================================================================
// NoOp Case Predicates
// ============================================================================

// --- Invalid Input Cases (guard failures) ---

// Case 1: GeneratePalette with invalid parameters
predicate NoOpGeneratePaletteInvalid(a: Action) {
  a.GeneratePalette? &&
  (!validBaseHue(a.baseHue) || |a.randomSeeds| != 10 ||
   (|a.randomSeeds| == 10 && !validRandomSeeds(a.randomSeeds)))
}

// Case 2: SelectContrastPair with invalid indices
predicate NoOpSelectContrastPairInvalid(a: Action) {
  a.SelectContrastPair? &&
  !(0 <= a.fg < 5 && 0 <= a.bg < 5)
}

// Case 3: RegenerateMood with invalid randomSeeds
predicate NoOpRegenerateMoodInvalid(a: Action) {
  a.RegenerateMood? &&
  (|a.randomSeeds| != 10 || (|a.randomSeeds| == 10 && !validRandomSeeds(a.randomSeeds)))
}

// Case 4: RegenerateHarmony with invalid randomSeeds
predicate NoOpRegenerateHarmonyInvalid(a: Action) {
  a.RegenerateHarmony? &&
  (|a.randomSeeds| != 10 || (|a.randomSeeds| == 10 && !validRandomSeeds(a.randomSeeds)))
}

// Case 5: RandomizeBaseHue with invalid parameters
predicate NoOpRandomizeBaseHueInvalid(a: Action) {
  a.RandomizeBaseHue? &&
  (!validBaseHue(a.newBaseHue) || |a.randomSeeds| != 10 ||
   (|a.randomSeeds| == 10 && !validRandomSeeds(a.randomSeeds)))
}

// --- Zero-Effect Cases ---

// Case 6: AdjustColor with zero deltas
predicate NoOpAdjustColorZeroDeltas(a: Action) {
  a.AdjustColor? &&
  0 <= a.index < 5 &&
  a.deltaH == 0 && a.deltaS == 0 && a.deltaL == 0
}

// Case 7: AdjustPalette with zero deltas
predicate NoOpAdjustPaletteZeroDeltas(a: Action) {
  a.AdjustPalette? &&
  a.deltaH == 0 && a.deltaS == 0 && a.deltaL == 0
}

// Case 8: SelectContrastPair with same pair as current
predicate NoOpSelectContrastPairSame(m: Model, a: Action) {
  a.SelectContrastPair? &&
  0 <= a.fg < 5 && 0 <= a.bg < 5 &&
  m.contrastPair == ContrastPair(a.fg, a.bg)
}

// Case 9: SetColorDirect where clamped color equals existing
predicate NoOpSetColorDirectSameColor(m: Model, a: Action)
  requires |m.colors| == 5
{
  a.SetColorDirect? &&
  0 <= a.index < 5 &&
  clampColor(a.color) == m.colors[a.index] &&
  (m.harmony == Harmony.Custom ||
    (var expectedHues := allHarmonyHues(m.baseHue, m.harmony);
     |expectedHues| == 5 && clampColor(a.color).h == expectedHues[a.index])) &&
  (m.mood == Mood.Custom || colorSatisfiesMood(clampColor(a.color), m.mood))
}

// Case 10: AdjustColor with non-zero deltas but clamping produces same color
predicate NoOpAdjustColorClampedSame(m: Model, a: Action)
  requires |m.colors| == 5
{
  a.AdjustColor? &&
  0 <= a.index < 5 &&
  var oldColor := m.colors[a.index];
  var newColor := clampColor(Color(oldColor.h + a.deltaH, oldColor.s + a.deltaS, oldColor.l + a.deltaL));
  newColor == oldColor &&
  (m.harmony == Harmony.Custom ||
    (var expectedHues := allHarmonyHues(m.baseHue, m.harmony);
     |expectedHues| == 5 && newColor.h == expectedHues[a.index])) &&
  (m.mood == Mood.Custom || colorSatisfiesMood(newColor, m.mood))
}

// --- Coincidental Match Cases ---

// Case 11: GeneratePalette that happens to produce identical model
predicate NoOpGeneratePaletteCoincidental(m: Model, a: Action)
  requires Inv(m)
{
  a.GeneratePalette? &&
  validBaseHue(a.baseHue) && |a.randomSeeds| == 10 && validRandomSeeds(a.randomSeeds) &&
  m.baseHue == a.baseHue &&
  m.mood == a.mood &&
  m.harmony == a.harmony &&
  m.colors == generatePaletteColors(a.baseHue, a.mood, a.harmony, a.randomSeeds) &&
  m.adjustmentH == 0 && m.adjustmentS == 0 && m.adjustmentL == 0
}

// Case 12: RegenerateMood that happens to produce identical model
predicate NoOpRegenerateMoodCoincidental(m: Model, a: Action)
  requires Inv(m)
{
  a.RegenerateMood? &&
  |a.randomSeeds| == 10 && validRandomSeeds(a.randomSeeds) &&
  m.mood == a.mood &&
  m.colors == generatePaletteColors(m.baseHue, a.mood, m.harmony, a.randomSeeds) &&
  m.adjustmentH == 0 && m.adjustmentS == 0 && m.adjustmentL == 0
}

// Case 13: RegenerateHarmony that happens to produce identical model
predicate NoOpRegenerateHarmonyCoincidental(m: Model, a: Action)
  requires Inv(m)
{
  a.RegenerateHarmony? &&
  |a.randomSeeds| == 10 && validRandomSeeds(a.randomSeeds) &&
  m.harmony == a.harmony &&
  m.colors == generatePaletteColors(m.baseHue, m.mood, a.harmony, a.randomSeeds) &&
  m.adjustmentH == 0 && m.adjustmentS == 0 && m.adjustmentL == 0
}

// Case 14: RandomizeBaseHue that happens to produce identical model
predicate NoOpRandomizeBaseHueCoincidental(m: Model, a: Action)
  requires Inv(m)
{
  a.RandomizeBaseHue? &&
  validBaseHue(a.newBaseHue) && |a.randomSeeds| == 10 && validRandomSeeds(a.randomSeeds) &&
  m.baseHue == a.newBaseHue &&
  m.colors == generatePaletteColors(a.newBaseHue, m.mood, m.harmony, a.randomSeeds) &&
  m.adjustmentH == 0 && m.adjustmentS == 0 && m.adjustmentL == 0
}

// ============================================================================
// Main Predicate: Complete enumeration of all NoOp cases
// ============================================================================

predicate IsNoOp(m: Model, a: Action)
  requires Inv(m)
  requires validAction(a)
{
  // Invalid input cases
  NoOpGeneratePaletteInvalid(a) ||
  NoOpSelectContrastPairInvalid(a) ||
  NoOpRegenerateMoodInvalid(a) ||
  NoOpRegenerateHarmonyInvalid(a) ||
  NoOpRandomizeBaseHueInvalid(a) ||
  // Zero-effect cases
  NoOpAdjustColorZeroDeltas(a) ||
  NoOpAdjustPaletteZeroDeltas(a) ||
  NoOpSelectContrastPairSame(m, a) ||
  NoOpSetColorDirectSameColor(m, a) ||
  NoOpAdjustColorClampedSame(m, a) ||
  // Coincidental match cases
  NoOpGeneratePaletteCoincidental(m, a) ||
  NoOpRegenerateMoodCoincidental(m, a) ||
  NoOpRegenerateHarmonyCoincidental(m, a) ||
  NoOpRandomizeBaseHueCoincidental(m, a)
}

// ============================================================================
// Helper Lemmas
// ============================================================================

// ClampColor is idempotent on valid colors
lemma ClampColorIdempotent(c: Color)
  requires ValidColor(c)
  ensures clampColor(c) == c
{
  assert 0 <= c.h < 360;
  assert c.h % 360 == c.h;
  assert normalizeHue(c.h) == c.h;
  assert clamp(c.s, 0, 100) == c.s;
  assert clamp(c.l, 0, 100) == c.l;
}

// AdjustColor with zero deltas is a NoOp
lemma AdjustColorZeroDeltasIsNoOp(m: Model, index: int)
  requires Inv(m)
  requires 0 <= index < 5
  ensures apply(m, AdjustColor(index, 0, 0, 0)) == m
{
  var oldColor := m.colors[index];
  assert ValidColor(oldColor);
  ClampColorIdempotent(oldColor);

  var newColor := clampColor(Color(oldColor.h, oldColor.s, oldColor.l));
  assert newColor == oldColor;

  var expectedHues := allHarmonyHues(m.baseHue, m.harmony);
  if |expectedHues| == 5 {
    assert huesMatchHarmony(m.colors, m.baseHue, m.harmony);
    assert m.colors[index].h == expectedHues[index];
  }
  var hueChanged := |expectedHues| == 5 && newColor.h != expectedHues[index];
  assert !hueChanged;

  if m.mood != Mood.Custom {
    assert colorSatisfiesMood(oldColor, m.mood);
  }

  var newColors := m.colors[index := newColor];
  assert newColors == m.colors;
}

// AdjustPalette with zero deltas is a NoOp
lemma AdjustPaletteZeroDeltasIsNoOp(m: Model)
  requires Inv(m)
  ensures apply(m, AdjustPalette(0, 0, 0)) == m
{
  var newBaseHue := normalizeHue(m.baseHue + 0);
  assert validBaseHue(m.baseHue);
  assert m.baseHue % 360 == m.baseHue;
  assert newBaseHue == m.baseHue;

  var newHues := allHarmonyHues(newBaseHue, m.harmony);
  var oldHues := allHarmonyHues(m.baseHue, m.harmony);
  assert newHues == oldHues;

  forall i | 0 <= i < 5
    ensures ValidColor(m.colors[i])
  {}

  if |newHues| == 5 {
    forall i | 0 <= i < 5
      ensures adjustColorSL(m.colors[i], newHues[i], 0, 0) == m.colors[i]
    {
      var c := m.colors[i];
      assert huesMatchHarmony(m.colors, m.baseHue, m.harmony);
      assert c.h == oldHues[i];
    }
  } else {
    forall i | 0 <= i < 5
      ensures adjustColorSL(m.colors[i], normalizeHue(m.colors[i].h + 0), 0, 0) == m.colors[i]
    {
      var c := m.colors[i];
      assert ValidColor(c);
      assert normalizeHue(c.h) == c.h;
    }
  }

  var adjusted := applyLinkedAdjustment(m, 0, 0, 0);
  assert adjusted == m;
}

// ============================================================================
// Main Theorem: If apply(m, a) == m, then IsNoOp(m, a) (Completeness)
// ============================================================================

lemma CheckNoOps(m: Model, a: Action)
  requires Inv(m)
  requires validAction(a)
  requires m == apply(m, a)
  ensures IsNoOp(m, a)
{
  match a {
    case GeneratePalette(baseHue, mood, harmony, randomSeeds) =>
      if !validBaseHue(baseHue) || |randomSeeds| != 10 || (|randomSeeds| == 10 && !validRandomSeeds(randomSeeds)) {
        assert NoOpGeneratePaletteInvalid(a);
      } else {
        var newColors := generatePaletteColors(baseHue, mood, harmony, randomSeeds);
        var result := m.(baseHue := baseHue, mood := mood, harmony := harmony,
                        colors := newColors,
                        adjustmentH := 0, adjustmentS := 0, adjustmentL := 0);
        assert m == result;
        assert m.baseHue == baseHue;
        assert m.mood == mood;
        assert m.harmony == harmony;
        assert m.colors == newColors;
        assert m.adjustmentH == 0;
        assert m.adjustmentS == 0;
        assert m.adjustmentL == 0;
        assert NoOpGeneratePaletteCoincidental(m, a);
      }

    case AdjustColor(index, deltaH, deltaS, deltaL) =>
      if deltaH == 0 && deltaS == 0 && deltaL == 0 {
        assert NoOpAdjustColorZeroDeltas(a);
      } else {
        var oldColor := m.colors[index];
        var newColor := clampColor(Color(oldColor.h + deltaH, oldColor.s + deltaS, oldColor.l + deltaL));
        var result := applyIndependentAdjustment(m, index, deltaH, deltaS, deltaL);
        assert m == result;
        assert m.colors == result.colors;
        assert result.colors == m.colors[index := newColor];
        assert m.colors[index] == newColor;
        assert newColor == oldColor;
        assert result.harmony == m.harmony;
        assert result.mood == m.mood;
        assert NoOpAdjustColorClampedSame(m, a);
      }

    case AdjustPalette(deltaH, deltaS, deltaL) =>
      if deltaH == 0 && deltaS == 0 && deltaL == 0 {
        assert NoOpAdjustPaletteZeroDeltas(a);
      } else {
        var adjusted := applyLinkedAdjustment(m, deltaH, deltaS, deltaL);
        var result := adjusted.(adjustmentH := m.adjustmentH + deltaH,
                                adjustmentS := m.adjustmentS + deltaS,
                                adjustmentL := m.adjustmentL + deltaL);
        assert m == result;
        assert m.adjustmentH == m.adjustmentH + deltaH;
        assert deltaH == 0;
        assert m.adjustmentS == m.adjustmentS + deltaS;
        assert deltaS == 0;
        assert m.adjustmentL == m.adjustmentL + deltaL;
        assert deltaL == 0;
        assert NoOpAdjustPaletteZeroDeltas(a);
      }

    case SelectContrastPair(fg, bg) =>
      if !(0 <= fg < 5 && 0 <= bg < 5) {
        assert NoOpSelectContrastPairInvalid(a);
      } else {
        assert m == m.(contrastPair := ContrastPair(fg, bg));
        assert m.contrastPair == ContrastPair(fg, bg);
        assert NoOpSelectContrastPairSame(m, a);
      }

    case SetColorDirect(index, color) =>
      var clampedColor := clampColor(color);
      var result := applySetColorDirect(m, index, color);
      assert m == result;
      assert m.colors == result.colors;
      assert result.colors == m.colors[index := clampedColor];
      assert m.colors[index] == clampedColor;
      assert clampedColor == m.colors[index];
      assert result.harmony == m.harmony;
      assert result.mood == m.mood;
      assert NoOpSetColorDirectSameColor(m, a);

    case RegenerateMood(mood, randomSeeds) =>
      if |randomSeeds| != 10 || (|randomSeeds| == 10 && !validRandomSeeds(randomSeeds)) {
        assert NoOpRegenerateMoodInvalid(a);
      } else {
        var newColors := generatePaletteColors(m.baseHue, mood, m.harmony, randomSeeds);
        var result := m.(mood := mood, colors := newColors,
                        adjustmentH := 0, adjustmentS := 0, adjustmentL := 0);
        assert m == result;
        assert m.mood == mood;
        assert m.colors == newColors;
        assert m.adjustmentH == 0;
        assert m.adjustmentS == 0;
        assert m.adjustmentL == 0;
        assert NoOpRegenerateMoodCoincidental(m, a);
      }

    case RegenerateHarmony(harmony, randomSeeds) =>
      if |randomSeeds| != 10 || (|randomSeeds| == 10 && !validRandomSeeds(randomSeeds)) {
        assert NoOpRegenerateHarmonyInvalid(a);
      } else {
        var newColors := generatePaletteColors(m.baseHue, m.mood, harmony, randomSeeds);
        var result := m.(harmony := harmony, colors := newColors,
                        adjustmentH := 0, adjustmentS := 0, adjustmentL := 0);
        assert m == result;
        assert m.harmony == harmony;
        assert m.colors == newColors;
        assert m.adjustmentH == 0;
        assert m.adjustmentS == 0;
        assert m.adjustmentL == 0;
        assert NoOpRegenerateHarmonyCoincidental(m, a);
      }

    case RandomizeBaseHue(newBaseHue, randomSeeds) =>
      if !validBaseHue(newBaseHue) || |randomSeeds| != 10 || (|randomSeeds| == 10 && !validRandomSeeds(randomSeeds)) {
        assert NoOpRandomizeBaseHueInvalid(a);
      } else {
        var newColors := generatePaletteColors(newBaseHue, m.mood, m.harmony, randomSeeds);
        var result := m.(baseHue := newBaseHue, colors := newColors,
                        adjustmentH := 0, adjustmentS := 0, adjustmentL := 0);
        assert m == result;
        assert m.baseHue == newBaseHue;
        assert m.colors == newColors;
        assert m.adjustmentH == 0;
        assert m.adjustmentS == 0;
        assert m.adjustmentL == 0;
        assert NoOpRandomizeBaseHueCoincidental(m, a);
      }
  }
}

// ============================================================================
// Converse: If IsNoOp(m, a), then apply(m, a) == m (Soundness)
// ============================================================================

lemma NoOpImpliesUnchanged(m: Model, a: Action)
  requires Inv(m)
  requires validAction(a)
  requires IsNoOp(m, a)
  ensures apply(m, a) == m
{
  if NoOpAdjustColorZeroDeltas(a) {
    AdjustColorZeroDeltasIsNoOp(m, a.index);
  } else if NoOpAdjustPaletteZeroDeltas(a) {
    AdjustPaletteZeroDeltasIsNoOp(m);
  } else if NoOpSelectContrastPairSame(m, a) {
    assert apply(m, a) == m.(contrastPair := ContrastPair(a.fg, a.bg));
    assert m.contrastPair == ContrastPair(a.fg, a.bg);
  } else if NoOpSetColorDirectSameColor(m, a) {
    var clampedColor := clampColor(a.color);
    assert clampedColor == m.colors[a.index];
    var newColors := m.colors[a.index := clampedColor];
    assert newColors == m.colors;
  } else if NoOpAdjustColorClampedSame(m, a) {
    var oldColor := m.colors[a.index];
    var newColor := clampColor(Color(oldColor.h + a.deltaH, oldColor.s + a.deltaS, oldColor.l + a.deltaL));
    assert newColor == oldColor;
    var newColors := m.colors[a.index := newColor];
    assert newColors == m.colors;
  } else if NoOpGeneratePaletteCoincidental(m, a) {
    var newColors := generatePaletteColors(a.baseHue, a.mood, a.harmony, a.randomSeeds);
    assert m.colors == newColors;
  } else if NoOpRegenerateMoodCoincidental(m, a) {
    var newColors := generatePaletteColors(m.baseHue, a.mood, m.harmony, a.randomSeeds);
    assert m.colors == newColors;
  } else if NoOpRegenerateHarmonyCoincidental(m, a) {
    var newColors := generatePaletteColors(m.baseHue, m.mood, a.harmony, a.randomSeeds);
    assert m.colors == newColors;
  } else if NoOpRandomizeBaseHueCoincidental(m, a) {
    var newColors := generatePaletteColors(a.newBaseHue, m.mood, m.harmony, a.randomSeeds);
    assert m.colors == newColors;
  }
  // Invalid input cases return m directly in apply
}
