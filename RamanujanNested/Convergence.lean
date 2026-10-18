import RamanujanNested.Bounds
import RamanujanNested.Monotone
import Mathlib

/-!
# Convergence.lean — Section 4.1's actual conclusion

"the sequence `(R_1^(N))` is bounded from above ... which implies convergence
of the truncated radicals to a finite real limit." `Bounds.lean` gives the
boundedness, `Monotone.lean` gives the monotonicity; this file combines them
via Mathlib's monotone-bounded-sequence convergence theorem
(`tendsto_atTop_ciSup`) to obtain the convergence statement the paper claims.
-/

namespace RamanujanNested

open Filter Topology

/-- **Section 4.1, convergence.** For coefficients bounded above by `A` and
nonnegative, the truncated radical `truncRadical a N` converges to a finite
real limit as `N → ∞`. This is the paper's actual stated conclusion for
Section 4.1's main sufficient condition. -/
theorem truncRadical_converges {A : ℝ} (hA : 0 ≤ A) (a : ℕ → ℝ)
    (ha_nonneg : ∀ k, 0 ≤ a k) (ha_le : ∀ k, a k ≤ A) :
    ∃ L : ℝ, Tendsto (truncRadical a) atTop (𝓝 L) := by
  have hmono : Monotone (truncRadical a) := truncRadical_monotone a ha_nonneg
  have hbdd : BddAbove (Set.range (truncRadical a)) := by
    refine ⟨rStar A, ?_⟩
    rintro x ⟨N, rfl⟩
    exact (truncRadical_bounded hA N a ha_le).2
  exact ⟨⨆ i, truncRadical a i, tendsto_atTop_ciSup hmono hbdd⟩

end RamanujanNested
