import RamanujanNested.Oscillatory
import RamanujanNested.NthRootChain
import Mathlib

/-!
# OscillatoryNthRoot.lean — the oscillatory coefficient family, at any root order n ≥ 2

`Oscillatory.lean`'s small-amplitude case (`0 ≤ α ≤ 1`, no need for Lemma 1's
controlled-negativity machinery) is a direct instance of a bounded coefficient
sequence: `oscillatory_bounds` already gives `0 ≤ a_k ≤ 1+α` unconditionally
in this range, which is exactly `NthRootChain.lean`'s hypothesis. No new
moving-ceiling argument is needed — this is a one-line corollary of
`truncRadicalN_converges`, generalizing `oscillatory_converges_small_alpha`
to any root order at once.
-/

namespace RamanujanNested

/-- **Convergence of the oscillatory family, small amplitude, any root order.**
Generalizes `oscillatory_converges_small_alpha` (root order `2`) to any fixed
`n ≥ 2`. -/
theorem oscillatoryN_converges_small_alpha (n : ℕ) (hn : 2 ≤ n) {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) :
    ∃ L : ℝ, Filter.Tendsto (fun d => rollUpN n (oscillatoryCoeff α) 1 d)
      Filter.atTop (nhds L) := by
  have hA : (0 : ℝ) ≤ 1 + α := by linarith
  have ha_nonneg : ∀ k, 0 ≤ oscillatoryCoeff α k := fun k => by
    have := (oscillatory_bounds hα0 k).1; linarith
  have ha_le : ∀ k, oscillatoryCoeff α k ≤ 1 + α := fun k => (oscillatory_bounds hα0 k).2
  exact truncRadicalN_converges hn hA (oscillatoryCoeff α) ha_nonneg ha_le

end RamanujanNested
