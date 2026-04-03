# ColorWheel — Verified Color Palette Generator

A color palette generator with formally verified state transitions, built with [LemmaScript](https://github.com/midspiral/LemmaScript) and React.

This is a reimplementation of the [Dafny ColorWheel](https://github.com/metareflection/dafny-replay/tree/main/colorwheel) using LemmaScript — the TypeScript is both the implementation and the verified source. No compilation bridge, no BigNumber.js.

## Setup

**Prerequisites:** [elan](https://github.com/leanprover/elan) (Lean 4 toolchain), Node.js >= 18.

**Clone dependencies:**

```sh
git clone https://github.com/namin/loom.git -b lemma ../loom
git clone https://github.com/namin/velvet.git -b lemma ../velvet
git clone https://github.com/midspiral/LemmaScript.git ../lemmascript
```

**Install:**

```sh
npm install
cd ../lemmascript/tools && npm install
```

**Verify (first time fetches mathlib cache):**

```sh
lake build
```

**Run the web app:**

```sh
npm run dev
```

## What's Verified

31 functions, all proved with `loom_solve`. Plus `initSatisfiesInv` proved by `decide`.

### Helpers
- **`clamp`** — ensures result in `[min, max]`
- **`normalizeHue`** — ensures result in `[0, 360)`
- **`clampColor`** — ensures valid H/S/L ranges
- **`randomInRange`** — ensures result in `[min, max]` (integer division bounds via spec lemma)

### Mood & Harmony
- **`moodBoundsOf`** — S/L ranges per mood (switch on 7 variants)
- **`colorSatisfiesMood`** — checks color against mood constraints
- **`allHarmonyHues`** — generates 5 hues per harmony pattern
- **`huesMatchHarmony`** — checks palette hues match expected pattern

### Generation
- **`goldenSLForMood`** — golden ratio S/L distribution
- **`generateColorGolden`** — single color generation
- **`generatePaletteColors`** — full 5-color palette

### State Transitions
- **`apply`** — main state machine (switch on 8 action types)
- **`normalizeModel`** — repair function ensuring invariant
- **`applyIndependentAdjustment`** — adjust single color, degrade mood/harmony if broken
- **`applyLinkedAdjustment`** — adjust all colors together
- **`applySetColorDirect`** — set color from picker, try to preserve constraints

## File Structure

```
src/
  colorwheel.ts           <- Annotated TypeScript (types, all 30 functions)
  colorwheel.types.lean   <- Generated: structures, inductives, Pure namespace (28 defs)
  colorwheel.spec.lean    <- Spec lemmas (randomInRange division bounds)
  colorwheel.def.lean     <- Generated: Velvet method definitions
  colorwheel.proof.lean   <- Proofs: all 30 prove_correct
  app.ts                  <- App layer: action constructors, undo/redo
  context/                <- React context
  components/             <- React UI (palette, sliders, contrast picker)
  App.jsx                 <- Main dashboard
```

## How It Works

1. Add `//@ ` annotations to TypeScript:

   ```typescript
   //@ requires lo <= hi
   //@ ensures \result >= lo && \result <= hi
   ```

2. Generate Lean:

   ```sh
   cd ../lemmascript
   npx tsx tools/src/lsc.ts gen /path/to/colorwheel.ts
   ```

3. Write proofs (or let `loom_solve` handle it):

   ```lean
   prove_correct clamp by
     unfold Pure.clamp; loom_solve
   ```

4. Verify:
   ```sh
   lake build
   ```

The TypeScript is the source of truth. The Lean is generated from it. The React app imports the verified logic directly.

## TODO

- **`stepPreservesInv`** — `ModelInv(m) → ModelInv(step(m, a))`. Stated, not yet proved. The proof is mechanically straightforward (`normalizeModel` repairs any input) but requires case splitting across the 9-conjunct invariant. `initSatisfiesInv` is proved by `decide`.
- **Behavioral properties** (from Dafny `ColorWheelProps.dfy`): commutativity, idempotence, monotonic degradation, field independence, recovery. These are standalone theorems building on the per-function proofs.

## Architecture

Ported from Dafny's `ColorWheelSpec.dfy`. Key design decisions:

- **Ternary expressions** keep transition functions pure (`const` only, no `let mut`). This generates Lean `def`s instead of Velvet methods, which `loom_solve` handles efficiently.
- **Tuples → interfaces** (`ContrastPair`, `SLPair`, `MoodBoundsResult`) since LemmaScript has no tuple types.
- **Quantified predicates → enumeration** over the fixed 5-color palette (`allColorsSatisfyMood` checks each index explicitly).
- **No module refinement** — the Dafny Replay/Kernel undo-redo framework is replaced by simple JS history in `app.ts`.
