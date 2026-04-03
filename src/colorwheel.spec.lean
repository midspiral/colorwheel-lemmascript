import «colorwheel.types»
import Mathlib.Tactic

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
