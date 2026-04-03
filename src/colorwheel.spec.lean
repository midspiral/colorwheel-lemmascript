import «colorwheel.types»
import Mathlib.Tactic

-- ═══ Invariant ═══

def ValidColor (c : Color) : Prop :=
  0 ≤ c.h ∧ c.h < 360 ∧ 0 ≤ c.s ∧ c.s ≤ 100 ∧ 0 ≤ c.l ∧ c.l ≤ 100

def ModelInv (m : Model) : Prop :=
  0 ≤ m.baseHue ∧ m.baseHue < 360
  ∧ m.colors.size = 5
  ∧ (∀ i : Nat, i < 5 → ValidColor m.colors[i]!)
  ∧ 0 ≤ m.contrastPair.fg ∧ m.contrastPair.fg < 5
  ∧ 0 ≤ m.contrastPair.bg ∧ m.contrastPair.bg < 5
  ∧ (m.mood ≠ .Custom → Pure.allColorsSatisfyMood m.colors m.mood = true)
  ∧ Pure.huesMatchHarmony m.colors m.baseHue m.harmony = true

instance : DecidableEq Color := fun a b => by
  cases a; cases b; simp [Color.mk.injEq]; infer_instance

instance : Decidable (ValidColor c) := by unfold ValidColor; infer_instance
instance : Decidable (ModelInv m) := by unfold ModelInv; infer_instance

-- ═══ Spec lemmas ═══

-- randomInRange bounds: the core arithmetic lemma everything depends on.
@[grind, loomAbstractionSimp]
theorem Pure.randomInRange_ge (seed min max : Int) (hs0 : 0 ≤ seed) (hs1 : seed ≤ 100)
    (hm : min ≤ max) : min ≤ Pure.randomInRange seed min max := by
  unfold Pure.randomInRange
  split
  · omega
  · have : 0 ≤ seed * (max - min) / 100 :=
      Int.ediv_nonneg (mul_nonneg hs0 (by omega)) (by omega)
    omega

@[grind, loomAbstractionSimp]
theorem Pure.randomInRange_le (seed min max : Int) (hs0 : 0 ≤ seed) (hs1 : seed ≤ 100)
    (hm : min ≤ max) : Pure.randomInRange seed min max ≤ max := by
  unfold Pure.randomInRange
  split
  · omega
  · have h1 : seed * (max - min) ≤ 100 * (max - min) := by nlinarith
    have h2 : seed * (max - min) / 100 ≤ 100 * (max - min) / 100 :=
      Int.ediv_le_ediv (by omega) h1
    rw [Int.mul_ediv_cancel_left _ (by omega : (100 : Int) ≠ 0)] at h2
    omega
