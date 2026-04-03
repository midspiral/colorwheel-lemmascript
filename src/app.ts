/**
 * App layer — verified colorwheel logic + simple undo/redo.
 * No Dafny runtime, no BigNumber, no conversions.
 */

import {
  init, apply, normalize,
  type Color, type Model, type Mood, type Harmony, type Action, type ContrastPair,
} from './colorwheel.ts';

export type { Color, Model, Mood, Harmony, Action, ContrastPair };

// ── History ──

export interface History {
  past: Model[];
  present: Model;
  future: Model[];
}

// ── Mood/Harmony lists ──

export const moods: Mood[] = ['Vibrant', 'SoftMuted', 'Pastel', 'DeepJewel', 'Earth', 'Neon'];
export const harmonies: Harmony[] = ['Complementary', 'Triadic', 'Analogous', 'SplitComplement', 'Square'];

export const moodNames: Record<string, string> = {
  Vibrant: 'Vibrant', SoftMuted: 'Soft/Muted', Pastel: 'Pastel',
  DeepJewel: 'Deep/Jewel', Earth: 'Earth', Neon: 'Neon', Custom: 'Custom',
};

export const harmonyNames: Record<string, string> = {
  Complementary: 'Complementary', Triadic: 'Triadic', Analogous: 'Analogous',
  SplitComplement: 'Split-Complement', Square: 'Square', Custom: 'Custom',
};

// ── Action constructors ──

export const actions = {
  GeneratePalette: (baseHue: number, mood: Mood, harmony: Harmony, randomSeeds: number[]): Action =>
    ({ tag: 'GeneratePalette', baseHue, mood, harmony, randomSeeds }),
  AdjustColor: (index: number, deltaH: number, deltaS: number, deltaL: number): Action =>
    ({ tag: 'AdjustColor', index, deltaH, deltaS, deltaL }),
  AdjustPalette: (deltaH: number, deltaS: number, deltaL: number): Action =>
    ({ tag: 'AdjustPalette', deltaH, deltaS, deltaL }),
  SelectContrastPair: (fg: number, bg: number): Action =>
    ({ tag: 'SelectContrastPair', fg, bg }),
  SetColorDirect: (index: number, color: Color): Action =>
    ({ tag: 'SetColorDirect', index, color }),
  RegenerateMood: (mood: Mood, randomSeeds: number[]): Action =>
    ({ tag: 'RegenerateMood', mood, randomSeeds }),
  RegenerateHarmony: (harmony: Harmony, randomSeeds: number[]): Action =>
    ({ tag: 'RegenerateHarmony', harmony, randomSeeds }),
  RandomizeBaseHue: (newBaseHue: number, randomSeeds: number[]): Action =>
    ({ tag: 'RandomizeBaseHue', newBaseHue, randomSeeds }),
};

// ── Core ──

const step = (model: Model, action: Action): Model => normalize(apply(model, action));

export const app = {
  Init: (): History => ({ past: [], present: init(), future: [] }),
  Present: (h: History): Model => h.present,
  Dispatch: (h: History, action: Action): History => {
    const newModel = step(h.present, action);
    return { past: [...h.past, h.present], present: newModel, future: [] };
  },
  Preview: (h: History, action: Action): History => {
    const newModel = step(h.present, action);
    return { ...h, present: newModel };
  },
  CommitFrom: (h: History, baseline: Model): History => {
    return { past: [...h.past, baseline], present: h.present, future: [] };
  },
  Undo: (h: History): History => {
    if (h.past.length === 0) return h;
    const prev = h.past[h.past.length - 1];
    return { past: h.past.slice(0, -1), present: prev, future: [h.present, ...h.future] };
  },
  Redo: (h: History): History => {
    if (h.future.length === 0) return h;
    const next = h.future[0];
    return { past: [...h.past, h.present], present: next, future: h.future.slice(1) };
  },
  CanUndo: (h: History): boolean => h.past.length > 0,
  CanRedo: (h: History): boolean => h.future.length > 0,
};
