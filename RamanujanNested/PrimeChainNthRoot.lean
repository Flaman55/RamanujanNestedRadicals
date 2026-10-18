import RamanujanNested.PrimeChain
import RamanujanNested.NthRootChain
import Mathlib

/-!
# PrimeChainNthRoot.lean — the prime-coefficient radical, at any root order n ≥ 2

Generalizes `PrimeChain.lean`'s `rollUp_geomBounded` (geometric moving
ceiling `A·r^i`, root order `2`) to any root order `n ≥ 2`, and specializes
it to `primeCoeff` exactly as `PrimeChain.lean` does, giving existence of a
finite limit for `a_k = p_k` at any root order.

## Why the same hypotheses suffice

`PrimeChain.lean`'s hypothesis `1 ≤ A(A-r²)` forces `A > r² > 1` (since
`r > 1`): if `A ≤ r²` then `A(A-r²) ≤ 0 < 1`, contradicting the hypothesis
(given `A ≥ 0`). So `A > 1`, and since `r^i ≥ 1`, the ceiling `A·r^i ≥ 1`
always. That is exactly what is needed to bootstrap `(A·r^i)^n ≥ (A·r^i)^2`
(`pow_le_pow_right₀`) — the same n=2 argument then supplies
`1+b_1·\text{inner} ≤ (A·r^i)^2 ≤ (A·r^i)^n`, no new hypothesis required.
-/

namespace RamanujanNested

/-- **Geometric moving-ceiling boundedness, any root order.** Same hypotheses
as `rollUp_geomBounded`, generalized to `rollUpN`. -/
theorem rollUpN_geomBounded (n : ℕ) (hn : 2 ≤ n) {r A : ℝ} (hr : 1 < r) (hA : 0 ≤ A)
    (hAr : 1 ≤ A * (A - r ^ 2)) :
    ∀ (d i : ℕ) (b : ℕ → ℝ) (T : ℝ),
      (∀ k, 0 ≤ b k) → (∀ k, b k ≤ r ^ (i + k)) → 0 ≤ T → T ≤ A * r ^ i →
      0 ≤ rollUpN n b T d ∧ rollUpN n b T d ≤ A * r ^ i := by
  have hA_gt : r ^ 2 < A := by
    by_contra h
    push_neg at h
    have : A * (A - r ^ 2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hA (by linarith)
    linarith [hAr]
  have hr2_gt1 : (1:ℝ) < r ^ 2 := by nlinarith [hr, sq_nonneg (r - 1)]
  have hA_gt1 : (1:ℝ) < A := by linarith [hA_gt, hr2_gt1]
  intro d
  induction d with
  | zero =>
    intro i b T _ _ hT0 hTle
    exact ⟨hT0, hTle⟩
  | succ k ih =>
    intro i b T hb_nonneg hb_le hT0 hTle
    have hri_pos : (0 : ℝ) < r ^ i := pow_pos (by linarith : (0 : ℝ) < r) i
    have hpow_mono : r ^ i ≤ r ^ (i + 1) := by
      rw [pow_succ]
      nlinarith [mul_pos hri_pos (show (0 : ℝ) < r - 1 by linarith)]
    have hTle' : T ≤ A * r ^ (i + 1) := by
      have hAmono : A * r ^ i ≤ A * r ^ (i + 1) := mul_le_mul_of_nonneg_left hpow_mono hA
      linarith
    have hshift_nonneg : ∀ k, 0 ≤ (fun k => b (k + 1)) k := fun k => hb_nonneg (k + 1)
    have hshift_le : ∀ k, (fun k => b (k + 1)) k ≤ r ^ (i + 1 + k) := by
      intro k
      have h := hb_le (k + 1)
      have heq : i + (k + 1) = i + 1 + k := by ring
      rwa [heq] at h
    obtain ⟨hlo, hhi⟩ := ih (i + 1) (fun k => b (k + 1)) T hshift_nonneg hshift_le hT0 hTle'
    have hb1_le : b 1 ≤ r ^ (i + 1) := hb_le 1
    have hb1_nonneg : 0 ≤ b 1 := hb_nonneg 1
    have hri1_nonneg : (0 : ℝ) ≤ r ^ (i + 1) :=
      le_of_lt (pow_pos (by linarith : (0 : ℝ) < r) (i + 1))
    have hY1 : (1 : ℝ) ≤ r ^ i * r ^ i := by
      have hri : (1 : ℝ) ≤ r ^ i := one_le_pow_of_one_lt hr i
      nlinarith [hri]
    have hrad_le2 : 1 + b 1 * rollUpN n (fun k => b (k + 1)) T k ≤ (A * r ^ i) ^ 2 := by
      have hstep1 : b 1 * rollUpN n (fun k => b (k + 1)) T k ≤ r ^ (i + 1) * (A * r ^ (i + 1)) :=
        mul_le_mul hb1_le hhi hlo hri1_nonneg
      have hRHS_eq : r ^ (i + 1) * (A * r ^ (i + 1)) = A * r ^ 2 * (r ^ i * r ^ i) := by
        have e1 : r ^ (i + 1) = r ^ i * r := pow_succ r i
        rw [e1]; ring
      have hgoalRHS_eq : (A * r ^ i) ^ 2 = A ^ 2 * (r ^ i * r ^ i) := by ring
      have hkey : (1 : ℝ) ≤ A * (A - r ^ 2) * (r ^ i * r ^ i) := by
        have hb : (0 : ℝ) ≤ A * (A - r ^ 2) := by linarith [hAr]
        nlinarith [mul_le_mul hAr hY1 (by norm_num : (0 : ℝ) ≤ 1) hb]
      have hexpand : A * (A - r ^ 2) * (r ^ i * r ^ i) =
          A ^ 2 * (r ^ i * r ^ i) - A * r ^ 2 * (r ^ i * r ^ i) := by ring
      rw [hRHS_eq] at hstep1
      rw [hgoalRHS_eq]
      linarith [hstep1, hkey, hexpand]
    have hrip_ge1 : (1:ℝ) ≤ r ^ i := one_le_pow_of_one_lt hr i
    have hAri_ge1 : (1:ℝ) ≤ A * r ^ i := by
      have h1 : (1:ℝ) * r ^ i ≤ A * r ^ i :=
        mul_le_mul_of_nonneg_right hA_gt1.le (by linarith [hrip_ge1])
      linarith [h1, hrip_ge1]
    have hpow_n : (A * r ^ i) ^ 2 ≤ (A * r ^ i) ^ n := pow_le_pow_right₀ hAri_ge1 hn
    have hrad_le : 1 + b 1 * rollUpN n (fun k => b (k + 1)) T k ≤ (A * r ^ i) ^ n := by
      linarith [hrad_le2, hpow_n]
    have hn_ne : (n : ℝ) ≠ 0 := by
      have hpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      linarith
    have hradicand_nonneg : 0 ≤ 1 + b 1 * rollUpN n (fun k => b (k + 1)) T k :=
      add_nonneg zero_le_one (mul_nonneg hb1_nonneg hlo)
    rw [rollUpN_succ]
    refine ⟨Real.rpow_nonneg hradicand_nonneg _, ?_⟩
    calc (1 + b 1 * rollUpN n (fun k => b (k + 1)) T k) ^ (1 / (n : ℝ))
        ≤ ((A * r ^ i) ^ n : ℝ) ^ (1 / (n : ℝ)) :=
          Real.rpow_le_rpow hradicand_nonneg hrad_le (by positivity)
      _ = A * r ^ i := by
          rw [← Real.rpow_natCast (A * r ^ i) n, ← Real.rpow_mul (by positivity),
            mul_one_div, div_self hn_ne, Real.rpow_one]

/-- Concrete instantiation, any root order: `r = 4`, `A = 17` (unchanged from
`PrimeChain.lean`, since the hypotheses transfer without modification). -/
theorem primeCoeffN_bounded (n : ℕ) (hn : 2 ≤ n) (d : ℕ) :
    0 ≤ rollUpN n primeCoeff 1 d ∧ rollUpN n primeCoeff 1 d ≤ 17 := by
  have hr : (1 : ℝ) < 4 := by norm_num
  have hA : (0 : ℝ) ≤ 17 := by norm_num
  have hAr : (1 : ℝ) ≤ 17 * (17 - (4 : ℝ) ^ 2) := by norm_num
  have hle : ∀ k, primeCoeff k ≤ (4 : ℝ) ^ (0 + k) := by
    intro k; simpa using primeCoeff_le_pow k
  have hT : (1 : ℝ) ≤ 17 * (4 : ℝ) ^ (0 : ℕ) := by norm_num
  have h := rollUpN_geomBounded n hn hr hA hAr d 0 primeCoeff 1 primeCoeff_nonneg hle
    (by norm_num) hT
  simpa using h

open Filter Topology

/-- **Existence of a limit for `a_k = p_k`, at any root order `n ≥ 2`.**
Generalizes `primeRadical_converges` (`PrimeChain.lean`, root order `2`) to
every root order at once. -/
theorem primeRadicalN_converges (n : ℕ) (hn : 2 ≤ n) :
    ∃ L : ℝ, Tendsto (fun d => rollUpN n primeCoeff 1 d) atTop (𝓝 L) ∧ L ≤ 17 := by
  have hmono : Monotone (fun d => rollUpN n primeCoeff 1 d) :=
    truncRadicalN_monotone n primeCoeff primeCoeff_nonneg
  have hbdd : BddAbove (Set.range (fun d => rollUpN n primeCoeff 1 d)) := by
    refine ⟨17, ?_⟩
    rintro x ⟨d, rfl⟩
    exact (primeCoeffN_bounded n hn d).2
  refine ⟨⨆ i, rollUpN n primeCoeff 1 i, tendsto_atTop_ciSup hmono hbdd, ?_⟩
  apply ciSup_le
  intro d
  exact (primeCoeffN_bounded n hn d).2

end RamanujanNested
