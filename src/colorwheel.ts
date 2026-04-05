/**
 * ColorWheel — verified color palette generator.
 * Ported from Dafny (dafny-replay/colorwheel/ColorWheelSpec.dfy).
 */

// ═══ Types ═══

export interface Color {
  h: number;
  s: number;
  l: number;
}

export type Mood = "Vibrant" | "SoftMuted" | "Pastel" | "DeepJewel" | "Earth" | "Neon" | "Custom"

export type Harmony = "Complementary" | "Triadic" | "Analogous" | "SplitComplement" | "Square" | "Custom"

export interface ContrastPair {
  fg: number;
  bg: number;
}

export interface MoodBoundsResult {
  minS: number;
  maxS: number;
  minL: number;
  maxL: number;
}

export interface SLPair {
  s: number;
  l: number;
}

export interface Model {
  baseHue: number;
  mood: Mood;
  harmony: Harmony;
  colors: Color[];
  contrastPair: ContrastPair;
  adjustmentH: number;
  adjustmentS: number;
  adjustmentL: number;
}

export type Action =
  | { tag: "GeneratePalette"; baseHue: number; mood: Mood; harmony: Harmony; randomSeeds: number[] }
  | { tag: "AdjustColor"; index: number; deltaH: number; deltaS: number; deltaL: number }
  | { tag: "AdjustPalette"; deltaH: number; deltaS: number; deltaL: number }
  | { tag: "SelectContrastPair"; fg: number; bg: number }
  | { tag: "SetColorDirect"; index: number; color: Color }
  | { tag: "RegenerateMood"; mood: Mood; randomSeeds: number[] }
  | { tag: "RegenerateHarmony"; harmony: Harmony; randomSeeds: number[] }
  | { tag: "RandomizeBaseHue"; newBaseHue: number; randomSeeds: number[] }

// ═══ Helper functions ═══

function clamp(x: number, min: number, max: number): number {
  //@ requires min <= max
  //@ ensures \result >= min && \result <= max
  if (x < min) return min;
  if (x > max) return max;
  return x;
}

function normalizeHue(h: number): number {
  //@ ensures \result >= 0 && \result < 360
  const normalized = h % 360;
  if (normalized < 0) return normalized + 360;
  return normalized;
}

function clampColor(c: Color): Color {
  //@ ensures \result.h >= 0 && \result.h < 360
  //@ ensures \result.s >= 0 && \result.s <= 100
  //@ ensures \result.l >= 0 && \result.l <= 100
  return {
    h: normalizeHue(c.h),
    s: clamp(c.s, 0, 100),
    l: clamp(c.l, 0, 100)
  };
}

// ═══ Mood functions ═══

function moodBoundsOf(mood: Mood): MoodBoundsResult {
  switch (mood) {
    case "Vibrant":   return { minS: 70, maxS: 100, minL: 40, maxL: 60 };
    case "SoftMuted": return { minS: 20, maxS: 45,  minL: 55, maxL: 75 };
    case "Pastel":    return { minS: 0,  maxS: 35,  minL: 75, maxL: 100 };
    case "DeepJewel": return { minS: 60, maxS: 100, minL: 25, maxL: 45 };
    case "Earth":     return { minS: 15, maxS: 40,  minL: 30, maxL: 60 };
    case "Neon":      return { minS: 90, maxS: 100, minL: 50, maxL: 65 };
    case "Custom":    return { minS: 0,  maxS: 100, minL: 0,  maxL: 100 };
  }
}

function colorSatisfiesMood(c: Color, mood: Mood): boolean {
  switch (mood) {
    case "Vibrant":   return c.s >= 70 && 40 <= c.l && c.l <= 60;
    case "SoftMuted": return 20 <= c.s && c.s <= 45 && 55 <= c.l && c.l <= 75;
    case "Pastel":    return c.s <= 35 && c.l >= 75;
    case "DeepJewel": return c.s >= 60 && 25 <= c.l && c.l <= 45;
    case "Earth":     return 15 <= c.s && c.s <= 40 && 30 <= c.l && c.l <= 60;
    case "Neon":      return c.s >= 90 && 50 <= c.l && c.l <= 65;
    case "Custom":    return true;
  }
}

function randomInRange(seed: number, min: number, max: number): number {
  //@ requires seed >= 0 && seed <= 100
  //@ requires min <= max
  //@ ensures \result >= min && \result <= max
  if (min === max) return min;
  return min + Math.floor((seed * (max - min)) / 100);
}

function goldenSLForMood(mood: Mood, colorIndex: number, seedS: number, seedL: number): SLPair {
  //@ requires colorIndex >= 0 && colorIndex < 5
  //@ requires seedS >= 0 && seedS <= 100
  //@ requires seedL >= 0 && seedL <= 100
  const bounds = moodBoundsOf(mood);
  // GoldenOffset = 62 (golden ratio * 100 ≈ 61.8)
  const spreadS = (seedS + colorIndex * 62) % 101;
  const spreadL = (seedL + colorIndex * 38) % 101;
  return {
    s: randomInRange(spreadS, bounds.minS, bounds.maxS),
    l: randomInRange(spreadL, bounds.minL, bounds.maxL)
  };
}

// ═══ Color generation ═══

function generateColorGolden(h: number, mood: Mood, colorIndex: number, seedS: number, seedL: number): Color {
  //@ requires h >= 0 && h < 360
  //@ requires colorIndex >= 0 && colorIndex < 5
  //@ requires seedS >= 0 && seedS <= 100
  //@ requires seedL >= 0 && seedL <= 100
  const sl = goldenSLForMood(mood, colorIndex, seedS, seedL);
  return { h: h, s: sl.s, l: sl.l };
}

// ═══ Predicates (enumerated over fixed-size arrays) ═══

function allColorsSatisfyMood(colors: Color[], mood: Mood): boolean {
  //@ requires colors.length === 5
  return colorSatisfiesMood(colors[0], mood) &&
         colorSatisfiesMood(colors[1], mood) &&
         colorSatisfiesMood(colors[2], mood) &&
         colorSatisfiesMood(colors[3], mood) &&
         colorSatisfiesMood(colors[4], mood);
}

// ═══ Harmony functions ═══

function baseHarmonyHues(baseHue: number, harmony: Harmony): number[] {
  switch (harmony) {
    case "Complementary":
      return [baseHue, normalizeHue(baseHue + 180)];
    case "Triadic":
      return [baseHue, normalizeHue(baseHue + 120), normalizeHue(baseHue + 240)];
    case "Analogous":
      return [normalizeHue(baseHue - 30), normalizeHue(baseHue - 15),
              baseHue, normalizeHue(baseHue + 15), normalizeHue(baseHue + 30)];
    case "SplitComplement":
      return [baseHue, normalizeHue(baseHue + 150), normalizeHue(baseHue + 210)];
    case "Square":
      return [baseHue, normalizeHue(baseHue + 90),
              normalizeHue(baseHue + 180), normalizeHue(baseHue + 270)];
    case "Custom":
      return [];
  }
}

function allHarmonyHues(baseHue: number, harmony: Harmony): number[] {
  // HueSpread = 35 (degrees of variation)
  switch (harmony) {
    case "Analogous":
      // 5 hues: already complete
      return [normalizeHue(baseHue - 30), normalizeHue(baseHue - 15),
              baseHue, normalizeHue(baseHue + 15), normalizeHue(baseHue + 30)];
    case "Square":
      // 4 base + midpoint between first two
      return [baseHue, normalizeHue(baseHue + 90),
              normalizeHue(baseHue + 180), normalizeHue(baseHue + 270),
              normalizeHue(baseHue + 45)];
    case "Triadic":
      // 3 base + spread first two
      return [baseHue, normalizeHue(baseHue + 120), normalizeHue(baseHue + 240),
              normalizeHue(baseHue + 35), normalizeHue(baseHue + 120 - 35)];
    case "SplitComplement":
      // 3 base + spread first two
      return [baseHue, normalizeHue(baseHue + 150), normalizeHue(baseHue + 210),
              normalizeHue(baseHue + 35), normalizeHue(baseHue + 150 - 35)];
    case "Complementary":
      // 2 base + 3 variations
      return [baseHue, normalizeHue(baseHue + 180),
              normalizeHue(baseHue + 35), normalizeHue(baseHue + 180 + 35),
              normalizeHue(baseHue - 35)];
    case "Custom":
      return [];
  }
}

function huesMatchHarmony(colors: Color[], baseHue: number, harmony: Harmony): boolean {
  if (harmony === "Custom") return true;
  const expectedHues = allHarmonyHues(baseHue, harmony);
  if (colors.length !== 5 || expectedHues.length !== 5) return false;
  return colors[0].h === expectedHues[0] &&
         colors[1].h === expectedHues[1] &&
         colors[2].h === expectedHues[2] &&
         colors[3].h === expectedHues[3] &&
         colors[4].h === expectedHues[4];
}

// ═══ Palette generation ═══

function generatePaletteColors(baseHue: number, mood: Mood, harmony: Harmony, randomSeeds: number[]): Color[] {
  //@ requires baseHue >= 0 && baseHue < 360
  //@ requires randomSeeds.length === 10
  //@ requires forall(k: nat, k < 10 ==> randomSeeds[k] >= 0 && randomSeeds[k] <= 100)
  const hues = allHarmonyHues(baseHue, harmony);
  if (hues.length !== 5) {
    return [generateColorGolden(baseHue, mood, 0, randomSeeds[0], randomSeeds[1]),
            generateColorGolden(baseHue, mood, 1, randomSeeds[2], randomSeeds[3]),
            generateColorGolden(baseHue, mood, 2, randomSeeds[4], randomSeeds[5]),
            generateColorGolden(baseHue, mood, 3, randomSeeds[6], randomSeeds[7]),
            generateColorGolden(baseHue, mood, 4, randomSeeds[8], randomSeeds[9])];
  }
  return [generateColorGolden(hues[0], mood, 0, randomSeeds[0], randomSeeds[1]),
          generateColorGolden(hues[1], mood, 1, randomSeeds[2], randomSeeds[3]),
          generateColorGolden(hues[2], mood, 2, randomSeeds[4], randomSeeds[5]),
          generateColorGolden(hues[3], mood, 3, randomSeeds[6], randomSeeds[7]),
          generateColorGolden(hues[4], mood, 4, randomSeeds[8], randomSeeds[9])];
}

// ═══ Sub-transitions ═══

function adjustColorSL(c: Color, newHue: number, deltaS: number, deltaL: number): Color {
  //@ requires newHue >= 0 && newHue < 360
  return { h: newHue, s: clamp(c.s + deltaS, 0, 100), l: clamp(c.l + deltaL, 0, 100) };
}

function applyIndependentAdjustment(m: Model, index: number, deltaH: number, deltaS: number, deltaL: number): Model {
  //@ requires index >= 0 && index < 5
  //@ requires m.colors.length === 5
  const oldColor = m.colors[index];
  const newColor = clampColor({ h: oldColor.h + deltaH, s: oldColor.s + deltaS, l: oldColor.l + deltaL });
  const expectedHues = allHarmonyHues(m.baseHue, m.harmony);
  const hueChanged = expectedHues.length === 5 && newColor.h !== expectedHues[index];
  const harmonyBroken = m.harmony !== "Custom" && hueChanged;
  const moodBroken = m.mood !== "Custom" && !colorSatisfiesMood(newColor, m.mood);
  const newColors = m.colors.with(index, newColor);
  const newHarmony: Harmony = harmonyBroken ? "Custom" : m.harmony;
  const newMood: Mood = moodBroken ? "Custom" : m.mood;
  return { ...m, colors: newColors, harmony: newHarmony, mood: newMood };
}

function applyLinkedAdjustment(m: Model, deltaH: number, deltaS: number, deltaL: number): Model {
  //@ requires m.colors.length === 5
  const newBaseHue = normalizeHue(m.baseHue + deltaH);
  const newHues = allHarmonyHues(newBaseHue, m.harmony);
  const adjustedColors: Color[] =
    newHues.length === 5
      ? [adjustColorSL(m.colors[0], newHues[0], deltaS, deltaL),
         adjustColorSL(m.colors[1], newHues[1], deltaS, deltaL),
         adjustColorSL(m.colors[2], newHues[2], deltaS, deltaL),
         adjustColorSL(m.colors[3], newHues[3], deltaS, deltaL),
         adjustColorSL(m.colors[4], newHues[4], deltaS, deltaL)]
      : [adjustColorSL(m.colors[0], normalizeHue(m.colors[0].h + deltaH), deltaS, deltaL),
         adjustColorSL(m.colors[1], normalizeHue(m.colors[1].h + deltaH), deltaS, deltaL),
         adjustColorSL(m.colors[2], normalizeHue(m.colors[2].h + deltaH), deltaS, deltaL),
         adjustColorSL(m.colors[3], normalizeHue(m.colors[3].h + deltaH), deltaS, deltaL),
         adjustColorSL(m.colors[4], normalizeHue(m.colors[4].h + deltaH), deltaS, deltaL)];
  const moodBroken = m.mood !== "Custom" && !allColorsSatisfyMood(adjustedColors, m.mood);
  const newMood: Mood = moodBroken ? "Custom" : m.mood;
  return { ...m, baseHue: newBaseHue, colors: adjustedColors, mood: newMood };
}

function applySetColorDirect(m: Model, index: number, color: Color): Model {
  //@ requires index >= 0 && index < 5
  //@ requires m.colors.length === 5
  const clampedColor = clampColor(color);
  const expectedHues = allHarmonyHues(m.baseHue, m.harmony);
  const hueMatches = expectedHues.length === 5 && clampedColor.h === expectedHues[index];
  const harmonyPreserved = m.harmony === "Custom" || hueMatches;
  const moodPreserved = m.mood === "Custom" || colorSatisfiesMood(clampedColor, m.mood);
  const newColors = m.colors.with(index, clampedColor);
  const newHarmony: Harmony = harmonyPreserved ? m.harmony : "Custom";
  const newMood: Mood = moodPreserved ? m.mood : "Custom";
  return { ...m, colors: newColors, harmony: newHarmony, mood: newMood };
}

// ═══ Normalize ═══

export function normalizeModel(m: Model): Model {
  const normalizedBaseHue = normalizeHue(m.baseHue);
  const normalizedColors: Color[] =
    m.colors.length === 5
      ? [clampColor(m.colors[0]), clampColor(m.colors[1]), clampColor(m.colors[2]),
         clampColor(m.colors[3]), clampColor(m.colors[4])]
      : [{ h: 0, s: 0, l: 0 }, { h: 0, s: 0, l: 0 }, { h: 0, s: 0, l: 0 },
         { h: 0, s: 0, l: 0 }, { h: 0, s: 0, l: 0 }];
  const normalizedContrastPair: ContrastPair =
    (0 <= m.contrastPair.fg && m.contrastPair.fg < 5 && 0 <= m.contrastPair.bg && m.contrastPair.bg < 5)
      ? m.contrastPair
      : { fg: 0, bg: 1 };
  const finalMood: Mood =
    m.mood === "Custom" ? "Custom"
    : allColorsSatisfyMood(normalizedColors, m.mood) ? m.mood
    : "Custom";
  const finalHarmony: Harmony =
    m.harmony === "Custom" ? "Custom"
    : huesMatchHarmony(normalizedColors, normalizedBaseHue, m.harmony) ? m.harmony
    : "Custom";
  return { ...m,
    baseHue: normalizedBaseHue,
    colors: normalizedColors,
    contrastPair: normalizedContrastPair,
    mood: finalMood,
    harmony: finalHarmony
  };
}

// ═══ Apply (main state machine transition) ═══

function validBaseHue(h: number): boolean {
  return h >= 0 && h < 360;
}

function validRandomSeeds(seeds: number[]): boolean {
  //@ requires seeds.length === 10
  return seeds[0] >= 0 && seeds[0] <= 100 &&
         seeds[1] >= 0 && seeds[1] <= 100 &&
         seeds[2] >= 0 && seeds[2] <= 100 &&
         seeds[3] >= 0 && seeds[3] <= 100 &&
         seeds[4] >= 0 && seeds[4] <= 100 &&
         seeds[5] >= 0 && seeds[5] <= 100 &&
         seeds[6] >= 0 && seeds[6] <= 100 &&
         seeds[7] >= 0 && seeds[7] <= 100 &&
         seeds[8] >= 0 && seeds[8] <= 100 &&
         seeds[9] >= 0 && seeds[9] <= 100;
}

function applySelectContrastPair(m: Model, fg: number, bg: number): Model {
  if (0 <= fg && fg < 5 && 0 <= bg && bg < 5) {
    return { ...m, contrastPair: { fg: fg, bg: bg } };
  }
  return m;
}

function applyGeneratePalette(m: Model, baseHue: number, mood: Mood, harmony: Harmony, randomSeeds: number[]): Model {
  //@ requires m.colors.length === 5
  if (!validBaseHue(baseHue) || randomSeeds.length !== 10 || !validRandomSeeds(randomSeeds)) return m;
  const colors = generatePaletteColors(baseHue, mood, harmony, randomSeeds);
  return { ...m, baseHue: baseHue, mood: mood, harmony: harmony, colors: colors,
           adjustmentH: 0, adjustmentS: 0, adjustmentL: 0 };
}

function applyAdjustPalette(m: Model, deltaH: number, deltaS: number, deltaL: number): Model {
  //@ requires m.colors.length === 5
  const adjusted = applyLinkedAdjustment(m, deltaH, deltaS, deltaL);
  return { ...adjusted,
           adjustmentH: m.adjustmentH + deltaH,
           adjustmentS: m.adjustmentS + deltaS,
           adjustmentL: m.adjustmentL + deltaL };
}

function applyRegenerateMood(m: Model, mood: Mood, randomSeeds: number[]): Model {
  //@ requires m.colors.length === 5
  //@ requires m.baseHue >= 0 && m.baseHue < 360
  if (randomSeeds.length !== 10 || !validRandomSeeds(randomSeeds)) return m;
  const colors = generatePaletteColors(m.baseHue, mood, m.harmony, randomSeeds);
  return { ...m, mood: mood, colors: colors,
           adjustmentH: 0, adjustmentS: 0, adjustmentL: 0 };
}

function applyRegenerateHarmony(m: Model, harmony: Harmony, randomSeeds: number[]): Model {
  //@ requires m.colors.length === 5
  //@ requires m.baseHue >= 0 && m.baseHue < 360
  if (randomSeeds.length !== 10 || !validRandomSeeds(randomSeeds)) return m;
  const colors = generatePaletteColors(m.baseHue, m.mood, harmony, randomSeeds);
  return { ...m, harmony: harmony, colors: colors,
           adjustmentH: 0, adjustmentS: 0, adjustmentL: 0 };
}

function applyRandomizeBaseHue(m: Model, newBaseHue: number, randomSeeds: number[]): Model {
  //@ requires m.colors.length === 5
  if (randomSeeds.length !== 10 || !validRandomSeeds(randomSeeds) || !validBaseHue(newBaseHue)) return m;
  const colors = generatePaletteColors(newBaseHue, m.mood, m.harmony, randomSeeds);
  return { ...m, baseHue: newBaseHue, colors: colors,
           adjustmentH: 0, adjustmentS: 0, adjustmentL: 0 };
}

//@ pure
function validAction(a: Action): boolean {
  switch (a.tag) {
    case "AdjustColor": return a.index >= 0 && a.index < 5;
    case "SetColorDirect": return a.index >= 0 && a.index < 5;
    default: return true;
  }
}

export function apply(m: Model, a: Action): Model {
  //@ requires m.colors.length === 5
  //@ requires m.baseHue >= 0 && m.baseHue < 360
  //@ requires validAction(a)
  switch (a.tag) {
    case "GeneratePalette": return applyGeneratePalette(m, a.baseHue, a.mood, a.harmony, a.randomSeeds);
    case "AdjustColor": return applyIndependentAdjustment(m, a.index, a.deltaH, a.deltaS, a.deltaL);
    case "AdjustPalette": return applyAdjustPalette(m, a.deltaH, a.deltaS, a.deltaL);
    case "SelectContrastPair": return applySelectContrastPair(m, a.fg, a.bg);
    case "SetColorDirect": return applySetColorDirect(m, a.index, a.color);
    case "RegenerateMood": return applyRegenerateMood(m, a.mood, a.randomSeeds);
    case "RegenerateHarmony": return applyRegenerateHarmony(m, a.harmony, a.randomSeeds);
    case "RandomizeBaseHue": return applyRandomizeBaseHue(m, a.newBaseHue, a.randomSeeds);
  }
}

// ═══ Step (Normalize ∘ Apply) ═══

export function step(m: Model, a: Action): Model {
  //@ requires m.colors.length === 5
  //@ requires m.baseHue >= 0 && m.baseHue < 360
  //@ requires validAction(a)
  return normalizeModel(apply(m, a));
}

// ═══ Init ═══

export function init(): Model {
  const randomSeeds = [50, 50, 50, 50, 50, 50, 50, 50, 50, 50];
  const baseHue = 180;
  const mood: Mood = "Vibrant";
  const harmony: Harmony = "Complementary";
  const colors = generatePaletteColors(baseHue, mood, harmony, randomSeeds);
  return {
    baseHue: baseHue, mood: mood, harmony: harmony, colors: colors,
    contrastPair: { fg: 0, bg: 1 },
    adjustmentH: 0, adjustmentS: 0, adjustmentL: 0
  };
}
