import RamanujanNested.IdentityChain

/-!
# Reconstruction.lean — Algorithm 4, the general inverse construction

"instead of deriving values from coefficients, one may prescribe a structural
profile and compute the coefficients that realize it." For ANY sequence `R`
(not just `N + k - 1`), the coefficient `a_k := (R_k² - 1) / R_{k+1}` makes
`R_k = √(1 + a_k · R_{k+1})` hold exactly, by construction.

This is the general fact that `IdentityChain.lean`'s Algorithm 3 is a special
case of: `reconstructCoeff_chainClosedForm` recovers the specific coefficients
`N + k - 2` when `R` is taken to be the closed form `chainClosedForm N`.
-/

namespace RamanujanNested

/-- Algorithm 4: the coefficient that makes `R k` satisfy the recursion,
given the next value `R (k+1)`. -/
noncomputable def reconstructCoeff (R : ℕ → ℝ) (k : ℕ) : ℝ :=
  (R k ^ 2 - 1) / R (k + 1)

/-- **Algorithm 4, the general reconstruction identity.** For any `R` with
`R (k+1) ≠ 0` and `R k ≥ 0`, the reconstructed coefficient makes `R k` satisfy
the stated recursion exactly — this holds for an arbitrary target profile
`R`, not just the specific `N + k - 1` of Algorithm 3. -/
theorem reconstructCoeff_satisfies_recursion (R : ℕ → ℝ) (k : ℕ)
    (hRk1 : R (k + 1) ≠ 0) (hRk_nonneg : 0 ≤ R k) :
    R k = Real.sqrt (1 + reconstructCoeff R k * R (k + 1)) := by
  unfold reconstructCoeff
  rw [div_mul_cancel₀ (R k ^ 2 - 1) hRk1]
  rw [show (1 : ℝ) + (R k ^ 2 - 1) = R k ^ 2 by ring]
  exact (Real.sqrt_sq hRk_nonneg).symm

/-- **Algorithm 3 recovered as a special case of Algorithm 4.** Applying the
general reconstruction to the target profile `chainClosedForm N` gives back
exactly the coefficients `N + k - 2` from `IdentityChain.lean` / Algorithm 3.
-/
theorem reconstructCoeff_chainClosedForm (N k : ℕ) (hN : 2 ≤ N) :
    reconstructCoeff (chainClosedForm N) k = (N : ℝ) + (k : ℝ) - 2 := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hpos : (0 : ℝ) < (N : ℝ) + (k : ℝ) := by linarith
  have hsucc : chainClosedForm N (k + 1) = (N : ℝ) + (k : ℝ) := by
    unfold chainClosedForm; push_cast; ring
  have hcf : chainClosedForm N k = (N : ℝ) + (k : ℝ) - 1 := rfl
  unfold reconstructCoeff
  rw [hsucc, hcf]
  have hnum : ((N : ℝ) + (k : ℝ) - 1) ^ 2 - 1 =
      ((N : ℝ) + (k : ℝ) - 2) * ((N : ℝ) + (k : ℝ)) := by ring
  rw [hnum, mul_div_assoc, div_self (ne_of_gt hpos), mul_one]

end RamanujanNested
