// Proofs for ColorWheel specification
// Adapted from dafny-replay/colorwheel/ColorWheelProof.dfy

include "colorwheel.dfy"

// ============================================================================
// Auxiliary predicates (not in generated spec)
// ============================================================================

predicate ValidColor(c: Color) {
  0 <= c.h < 360 && 0 <= c.s <= 100 && 0 <= c.l <= 100
}

predicate Inv(m: Model) {
  && validBaseHue(m.baseHue)
  && |m.colors| == 5
  && (forall i | 0 <= i < 5 :: ValidColor(m.colors[i]))
  && 0 <= m.contrastPair.fg < 5
  && 0 <= m.contrastPair.bg < 5
  && (m.mood != Mood.Custom ==>
        forall i | 0 <= i < 5 :: colorSatisfiesMood(m.colors[i], m.mood))
  && huesMatchHarmony(m.colors, m.baseHue, m.harmony)
}

// ============================================================================
// Init satisfies invariant
// ============================================================================

lemma InitSatisfiesInv()
  ensures Inv(init())
{
  var m := init();
  var randomSeeds := [50, 50, 50, 50, 50, 50, 50, 50, 50, 50];
  assert validBaseHue(180);
  GeneratePaletteColorsValid(180, Mood.Vibrant, Harmony.Complementary, randomSeeds);
}

// ============================================================================
// Color generation validity
// ============================================================================

lemma GeneratePaletteColorsValid(baseHue: int, mood: Mood, harmony: Harmony, randomSeeds: seq<int>)
  requires validBaseHue(baseHue)
  requires |randomSeeds| == 10
  requires forall k: nat :: k < 10 ==> 0 <= randomSeeds[k] <= 100
  ensures var colors := generatePaletteColors(baseHue, mood, harmony, randomSeeds);
          |colors| == 5 &&
          (forall i | 0 <= i < 5 :: ValidColor(colors[i])) &&
          (mood != Mood.Custom ==> forall i | 0 <= i < 5 :: colorSatisfiesMood(colors[i], mood)) &&
          huesMatchHarmony(colors, baseHue, harmony)
{
  var colors := generatePaletteColors(baseHue, mood, harmony, randomSeeds);
  var hues := allHarmonyHues(baseHue, harmony);

  forall i | 0 <= i < 5
    ensures ValidColor(colors[i])
    ensures mood != Mood.Custom ==> colorSatisfiesMood(colors[i], mood)
  {
    GenerateColorGoldenValid(
      if |hues| == 5 then hues[i] else baseHue,
      mood, i, randomSeeds[2*i], randomSeeds[2*i + 1]
    );
  }

  if harmony != Harmony.Custom && |hues| == 5 {
    assert forall i | 0 <= i < 5 :: colors[i].h == hues[i];
  }
}

lemma GenerateColorGoldenValid(h: int, mood: Mood, colorIndex: int, seedS: int, seedL: int)
  requires 0 <= h < 360
  requires 0 <= colorIndex < 5
  requires 0 <= seedS <= 100
  requires 0 <= seedL <= 100
  ensures ValidColor(generateColorGolden(h, mood, colorIndex, seedS, seedL))
  ensures mood != Mood.Custom ==> colorSatisfiesMood(generateColorGolden(h, mood, colorIndex, seedS, seedL), mood)
{
  GoldenSLForMoodValid(mood, colorIndex, seedS, seedL);
}

lemma GoldenSLForMoodValid(mood: Mood, colorIndex: int, seedS: int, seedL: int)
  requires 0 <= colorIndex < 5
  requires 0 <= seedS <= 100
  requires 0 <= seedL <= 100
  ensures var sl := goldenSLForMood(mood, colorIndex, seedS, seedL);
          0 <= sl.s <= 100 && 0 <= sl.l <= 100 &&
          (mood != Mood.Custom ==> colorSatisfiesMood(Color(0, sl.s, sl.l), mood))
{
  var bounds := moodBoundsOf(mood);
  var spreadS := (seedS + colorIndex * 62) % 101;
  var spreadL := (seedL + colorIndex * 38) % 101;
  RandomInRangeValid(spreadS, bounds.minS, bounds.maxS);
  RandomInRangeValid(spreadL, bounds.minL, bounds.maxL);
}

// Helper: JSFloorDiv equals standard division for non-negative dividend and positive divisor
lemma JSFloorDivNonneg(a: int, b: int)
  requires b > 0
  requires a >= 0
  ensures JSFloorDiv(a, b) == a / b
{}

lemma RandomInRangeValid(seed: int, min: int, max: int)
  requires 0 <= seed <= 100
  requires min <= max
  ensures min <= randomInRange(seed, min, max) <= max
{
  if min == max {
  } else {
    var delta := seed * (max - min);
    assert 0 <= delta <= 100 * (max - min);
    JSFloorDivNonneg(delta, 100);
  }
}

// ============================================================================
// Step (normalizeModel . apply) preserves invariant
// ============================================================================

lemma StepPreservesInv(m: Model, a: Action)
  requires Inv(m)
  requires validAction(a)
  ensures Inv(normalizeModel(apply(m, a)))
{
  var applied := apply(m, a);
  NormalizeEnsuresValidBaseHue(applied);
  NormalizeEnsuresColorCount(applied);
  NormalizeEnsuresValidColors(applied);
  NormalizeEnsuresValidContrastPair(applied);
  NormalizeEnsuresMoodConstraint(applied);
  NormalizeEnsuresHarmonyConstraint(applied);
}

// ============================================================================
// NormalizeHue validity
// ============================================================================

lemma NormalizeHueValid(h: int)
  ensures 0 <= normalizeHue(h) < 360
{
  var normalized := h % 360;
  if normalized < 0 {
    assert normalized + 360 >= 0;
    assert normalized + 360 < 360;
  }
}

// ============================================================================
// Normalize ensures each part of the invariant
// ============================================================================

lemma NormalizeEnsuresValidBaseHue(m: Model)
  ensures validBaseHue(normalizeModel(m).baseHue)
{
  NormalizeHueValid(m.baseHue);
}

lemma NormalizeEnsuresColorCount(m: Model)
  ensures |normalizeModel(m).colors| == 5
{}

lemma ClampColorValid(c: Color)
  ensures ValidColor(clampColor(c))
{
  NormalizeHueValid(c.h);
}

lemma NormalizeEnsuresValidColors(m: Model)
  ensures forall i | 0 <= i < 5 :: ValidColor(normalizeModel(m).colors[i])
{
  if |m.colors| == 5 {
    ClampColorValid(m.colors[0]);
    ClampColorValid(m.colors[1]);
    ClampColorValid(m.colors[2]);
    ClampColorValid(m.colors[3]);
    ClampColorValid(m.colors[4]);
  }
}

lemma NormalizeEnsuresValidContrastPair(m: Model)
  ensures 0 <= normalizeModel(m).contrastPair.fg < 5
  ensures 0 <= normalizeModel(m).contrastPair.bg < 5
{}

// Helper function mirroring normalizeModel's color computation
function NormalizedColors(m: Model): seq<Color> {
  if |m.colors| == 5 then
    [clampColor(m.colors[0]), clampColor(m.colors[1]), clampColor(m.colors[2]),
     clampColor(m.colors[3]), clampColor(m.colors[4])]
  else
    [Color(0, 0, 0), Color(0, 0, 0), Color(0, 0, 0), Color(0, 0, 0), Color(0, 0, 0)]
}

lemma NormalizeColorsEquality(m: Model)
  ensures normalizeModel(m).colors == NormalizedColors(m)
{}

lemma NormalizeMoodImpliesCheck(m: Model)
  requires normalizeModel(m).mood != Mood.Custom
  ensures m.mood != Mood.Custom
  ensures normalizeModel(m).mood == m.mood
  ensures allColorsSatisfyMood(NormalizedColors(m), m.mood)
{
  NormalizeColorsEquality(m);

  if m.mood == Mood.Custom {
    assert false;
  }

  var normalizedColors := NormalizedColors(m);
  assert normalizeModel(m).colors == normalizedColors;

  var normalizedBaseHue := normalizeHue(m.baseHue);
  var normalizedContrastPair :=
    if 0 <= m.contrastPair.fg < 5 && 0 <= m.contrastPair.bg < 5 then m.contrastPair
    else ContrastPair(0, 1);
  var internalCheck := allColorsSatisfyMood(normalizedColors, m.mood);
  var finalMood :=
    if m.mood == Mood.Custom then Mood.Custom
    else if internalCheck then m.mood
    else Mood.Custom;
  var finalHarmony :=
    if m.harmony == Harmony.Custom then Harmony.Custom
    else if huesMatchHarmony(normalizedColors, normalizedBaseHue, m.harmony) then m.harmony
    else Harmony.Custom;

  assert normalizeModel(m).baseHue == normalizedBaseHue;
  assert normalizeModel(m).colors == normalizedColors;
  assert normalizeModel(m).contrastPair == normalizedContrastPair;
  assert normalizeModel(m).harmony == finalHarmony;
  assert normalizeModel(m).mood == finalMood;
  assert allColorsSatisfyMood(normalizedColors, m.mood);
}

lemma NormalizeEnsuresMoodConstraint(m: Model)
  ensures normalizeModel(m).mood != Mood.Custom ==>
          forall i | 0 <= i < 5 :: colorSatisfiesMood(normalizeModel(m).colors[i], normalizeModel(m).mood)
{
  if normalizeModel(m).mood != Mood.Custom {
    NormalizeMoodImpliesCheck(m);
    NormalizeColorsEquality(m);
  }
}

lemma NormalizeEnsuresHarmonyConstraint(m: Model)
  ensures huesMatchHarmony(normalizeModel(m).colors, normalizeModel(m).baseHue, normalizeModel(m).harmony)
{}

// ============================================================================
// AdjustPalette shifts all hues by deltaH
// ============================================================================

lemma AdjustPaletteShiftsHues(m: Model, deltaH: int, deltaS: int, deltaL: int)
  requires Inv(m)
  ensures var m' := apply(m, AdjustPalette(deltaH, deltaS, deltaL));
          forall i | 0 <= i < 5 ::
            m'.colors[i].h == normalizeHue(m.colors[i].h + deltaH)
{
  var m' := apply(m, AdjustPalette(deltaH, deltaS, deltaL));
  var newBaseHue := normalizeHue(m.baseHue + deltaH);
  var newHues := allHarmonyHues(newBaseHue, m.harmony);

  if |newHues| == 5 {
    AdjustPaletteShiftsHuesHarmony(m, deltaH, deltaS, deltaL);
  } else {
    forall i | 0 <= i < 5
      ensures m'.colors[i].h == normalizeHue(m.colors[i].h + deltaH)
    {
      NormalizeHueValid(m.colors[i].h + deltaH);
    }
  }
}

lemma AdjustPaletteShiftsHuesHarmony(m: Model, deltaH: int, deltaS: int, deltaL: int)
  requires Inv(m)
  requires |allHarmonyHues(normalizeHue(m.baseHue + deltaH), m.harmony)| == 5
  ensures var m' := apply(m, AdjustPalette(deltaH, deltaS, deltaL));
          forall i | 0 <= i < 5 ::
            m'.colors[i].h == normalizeHue(m.colors[i].h + deltaH)
{
  HarmonyHuesShift(m.baseHue, m.harmony, deltaH);
  assert huesMatchHarmony(m.colors, m.baseHue, m.harmony);
}

// ============================================================================
// Harmony hue shift lemmas
// ============================================================================

lemma HarmonyHuesShift(baseHue: int, harmony: Harmony, deltaH: int)
  requires 0 <= baseHue < 360
  requires harmony != Harmony.Custom
  requires |allHarmonyHues(baseHue, harmony)| == 5
  ensures var oldHues := allHarmonyHues(baseHue, harmony);
          var newHues := allHarmonyHues(normalizeHue(baseHue + deltaH), harmony);
          |newHues| == 5 &&
          forall i | 0 <= i < 5 :: newHues[i] == normalizeHue(oldHues[i] + deltaH)
{
  match harmony {
    case Complementary => HarmonyHuesShiftComplementary(baseHue, deltaH);
    case Triadic => HarmonyHuesShiftTriadic(baseHue, deltaH);
    case Analogous => HarmonyHuesShiftAnalogous(baseHue, deltaH);
    case SplitComplement => HarmonyHuesShiftSplitComplement(baseHue, deltaH);
    case Square => HarmonyHuesShiftSquare(baseHue, deltaH);
    case Custom =>
  }
}

lemma HarmonyHuesShiftComplementary(baseHue: int, deltaH: int)
  requires 0 <= baseHue < 360
  ensures var oldHues := allHarmonyHues(baseHue, Harmony.Complementary);
          var newHues := allHarmonyHues(normalizeHue(baseHue + deltaH), Harmony.Complementary);
          |oldHues| == 5 && |newHues| == 5 &&
          forall i | 0 <= i < 5 :: newHues[i] == normalizeHue(oldHues[i] + deltaH)
{
  NormalizeHueShiftLemma(baseHue, deltaH);
  NormalizeHueShiftLemma(baseHue + 180, deltaH);
  NormalizeHueShiftLemma(baseHue + 35, deltaH);
  NormalizeHueShiftLemma(baseHue + 180 + 35, deltaH);
  NormalizeHueShiftLemma(baseHue - 35, deltaH);
  // Additional calls for generated version (single normalizeHue in allHarmonyHues)
  NormalizeHueShiftLemma(baseHue + deltaH, 180);
  NormalizeHueShiftLemma(baseHue + deltaH, 35);
  NormalizeHueShiftLemma(baseHue + deltaH, 215);
  NormalizeHueShiftLemma(baseHue + deltaH, -35);
}

lemma HarmonyHuesShiftTriadic(baseHue: int, deltaH: int)
  requires 0 <= baseHue < 360
  ensures var oldHues := allHarmonyHues(baseHue, Harmony.Triadic);
          var newHues := allHarmonyHues(normalizeHue(baseHue + deltaH), Harmony.Triadic);
          |oldHues| == 5 && |newHues| == 5 &&
          forall i | 0 <= i < 5 :: newHues[i] == normalizeHue(oldHues[i] + deltaH)
{
  NormalizeHueShiftLemma(baseHue, deltaH);
  NormalizeHueShiftLemma(baseHue + 120, deltaH);
  NormalizeHueShiftLemma(baseHue + 240, deltaH);
  NormalizeHueShiftLemma(baseHue + 35, deltaH);
  NormalizeHueShiftLemma(baseHue + 120 - 35, deltaH);
  NormalizeHueShiftLemma(baseHue + deltaH, 120);
  NormalizeHueShiftLemma(baseHue + deltaH, 240);
  NormalizeHueShiftLemma(baseHue + deltaH, 35);
  NormalizeHueShiftLemma(baseHue + deltaH, 85);
}

lemma HarmonyHuesShiftAnalogous(baseHue: int, deltaH: int)
  requires 0 <= baseHue < 360
  ensures var oldHues := allHarmonyHues(baseHue, Harmony.Analogous);
          var newHues := allHarmonyHues(normalizeHue(baseHue + deltaH), Harmony.Analogous);
          |oldHues| == 5 && |newHues| == 5 &&
          forall i | 0 <= i < 5 :: newHues[i] == normalizeHue(oldHues[i] + deltaH)
{
  NormalizeHueShiftLemma(baseHue - 30, deltaH);
  NormalizeHueShiftLemma(baseHue - 15, deltaH);
  NormalizeHueShiftLemma(baseHue, deltaH);
  NormalizeHueShiftLemma(baseHue + 15, deltaH);
  NormalizeHueShiftLemma(baseHue + 30, deltaH);
  NormalizeHueShiftLemma(baseHue + deltaH, -30);
  NormalizeHueShiftLemma(baseHue + deltaH, -15);
  NormalizeHueShiftLemma(baseHue + deltaH, 15);
  NormalizeHueShiftLemma(baseHue + deltaH, 30);
}

lemma HarmonyHuesShiftSplitComplement(baseHue: int, deltaH: int)
  requires 0 <= baseHue < 360
  ensures var oldHues := allHarmonyHues(baseHue, Harmony.SplitComplement);
          var newHues := allHarmonyHues(normalizeHue(baseHue + deltaH), Harmony.SplitComplement);
          |oldHues| == 5 && |newHues| == 5 &&
          forall i | 0 <= i < 5 :: newHues[i] == normalizeHue(oldHues[i] + deltaH)
{
  NormalizeHueShiftLemma(baseHue, deltaH);
  NormalizeHueShiftLemma(baseHue + 150, deltaH);
  NormalizeHueShiftLemma(baseHue + 210, deltaH);
  NormalizeHueShiftLemma(baseHue + 35, deltaH);
  NormalizeHueShiftLemma(baseHue + 150 - 35, deltaH);
  NormalizeHueShiftLemma(baseHue + deltaH, 150);
  NormalizeHueShiftLemma(baseHue + deltaH, 210);
  NormalizeHueShiftLemma(baseHue + deltaH, 35);
  NormalizeHueShiftLemma(baseHue + deltaH, 115);
}

lemma HarmonyHuesShiftSquare(baseHue: int, deltaH: int)
  requires 0 <= baseHue < 360
  ensures var oldHues := allHarmonyHues(baseHue, Harmony.Square);
          var newHues := allHarmonyHues(normalizeHue(baseHue + deltaH), Harmony.Square);
          |oldHues| == 5 && |newHues| == 5 &&
          forall i | 0 <= i < 5 :: newHues[i] == normalizeHue(oldHues[i] + deltaH)
{
  NormalizeHueShiftLemma(baseHue, deltaH);
  NormalizeHueShiftLemma(baseHue + 90, deltaH);
  NormalizeHueShiftLemma(baseHue + 180, deltaH);
  NormalizeHueShiftLemma(baseHue + 270, deltaH);
  NormalizeHueShiftLemma(baseHue + 45, deltaH);
  NormalizeHueShiftLemma(baseHue + deltaH, 90);
  NormalizeHueShiftLemma(baseHue + deltaH, 180);
  NormalizeHueShiftLemma(baseHue + deltaH, 270);
  NormalizeHueShiftLemma(baseHue + deltaH, 45);
}

// ============================================================================
// Key arithmetic lemma: normalizeHue(normalizeHue(a) + b) == normalizeHue(a + b)
// ============================================================================

lemma NormalizeHueShiftLemma(a: int, b: int)
  ensures normalizeHue(normalizeHue(a) + b) == normalizeHue(a + b)
{
  var left := normalizeHue(a) + b;
  var right := a + b;
  NormalizeHueModEquiv(a, normalizeHue(a));
  assert normalizeHue(a) % 360 == a % 360 || (normalizeHue(a) % 360 - a % 360) % 360 == 0;
}

lemma NormalizeHueModEquiv(x: int, nx: int)
  requires nx == normalizeHue(x)
  ensures (nx - x) % 360 == 0
{
  var normalized := x % 360;
  if normalized < 0 {
    assert nx == normalized + 360;
    assert nx - x == (normalized + 360) - x;
    assert (normalized + 360) - x == (x % 360 + 360) - x;
  } else {
    assert nx == normalized;
    assert nx - x == (x % 360) - x;
  }
}
