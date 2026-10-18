import RamanujanNested.LinearChainGeneral
import RamanujanNested.NthRootChain
import Mathlib

/-!
# LinearChainGeneralNthRoot.lean — the unbounded linear family, ALL slopes, any root order

`LinearChainNthRoot.lean` generalizes `LinearChain.lean` (slope `m ≥ 1`) to any
root order `n ≥ 2`. This file does the same for `LinearChainGeneral.lean`
(EVERY slope `m > 0`, via the looser ceiling `C(N) = N+1`): existence of a
limit for `linearCoeff m N` at any slope `m > 0` and any root order `n ≥ 2`,
with bound `L ≤ N+1`.

## The key inequality, generalized

`LinearChainGeneral.lean` needs `(N-m)((N+m)+1)+1 ≤ (N+1)^2`, which reduces
to `0 ≤ N+m+m^2` — true unconditionally for `m > 0`, `N ≥ 0`. Since
`(N+1)^n ≥ (N+1)^2` for `N+1 ≥ 1` and `n ≥ 2`, the same unconditional
inequality closes the argument at every root order at once.
-/

namespace RamanujanNested

/-- **Moving-ceiling boundedness, ALL positive slopes, any root order.** -/
theorem rollUpN_linearCoeff_bounded_general (n : ℕ) (hn : 2 ≤ n) :
    ∀ (d : ℕ) (m N T : ℝ), 0 < m → 2 * m ≤ N → 0 ≤ T → T ≤ N + 1 →
      0 ≤ rollUpN n (linearCoeff m N) T d ∧ rollUpN n (linearCoeff m N) T d ≤ N + 1 := by
  intro d
  induction d with
  | zero =>
    intro m N T _ _ hT0 hTN
    exact ⟨hT0, hTN⟩
  | succ k ih =>
    intro m N T hm hN hT0 hTN
    have hN1 : 2 * m ≤ N + m := by linarith
    have hTN1 : T ≤ (N + m) + 1 := by linarith
    obtain ⟨hlo, hhi⟩ := ih m (N + m) T hm hN1 hT0 hTN1
    have hshift : (fun j => linearCoeff m N (j + 1)) = linearCoeff m (N + m) := by
      funext j
      unfold linearCoeff
      push_cast
      ring
    have ha1 : linearCoeff m N 1 = N - m := by
      unfold linearCoeff
      push_cast
      ring
    have ha1_nonneg : 0 ≤ linearCoeff m N 1 := by
      rw [ha1]; linarith
    have hNp1_pos : (1:ℝ) ≤ N + 1 := by linarith
    have hn_ne : (n : ℝ) ≠ 0 := by
      have hpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      linarith
    rw [rollUpN_succ, hshift]
    have hradicand_le :
        1 + linearCoeff m N 1 * rollUpN n (linearCoeff m (N + m)) T k ≤ (N + 1) ^ n := by
      rw [ha1]
      have hmul : (N - m) * rollUpN n (linearCoeff m (N + m)) T k ≤ (N - m) * ((N + m) + 1) :=
        mul_le_mul_of_nonneg_left hhi (by linarith)
      have hpow : (N + 1) ^ 2 ≤ (N + 1) ^ n := pow_le_pow_right₀ hNp1_pos hn
      nlinarith [hmul, hpow, hm, hN, sq_nonneg m]
    have hradicand_nonneg :
        0 ≤ 1 + linearCoeff m N 1 * rollUpN n (linearCoeff m (N + m)) T k :=
      add_nonneg zero_le_one (mul_nonneg ha1_nonneg hlo)
    refine ⟨Real.rpow_nonneg hradicand_nonneg _, ?_⟩
    calc (1 + linearCoeff m N 1 * rollUpN n (linearCoeff m (N + m)) T k) ^ (1 / (n : ℝ))
        ≤ ((N + 1) ^ n : ℝ) ^ (1 / (n : ℝ)) :=
          Real.rpow_le_rpow hradicand_nonneg hradicand_le (by positivity)
      _ = N + 1 := by
          rw [← Real.rpow_natCast (N + 1) n, ← Real.rpow_mul (by linarith), mul_one_div,
            div_self hn_ne, Real.rpow_one]

/-- Specialized to the canonical seed `T = 1`. -/
theorem linearCoeffN_bounded_general {n : ℕ} (hn : 2 ≤ n) {m N : ℝ} (hm : 0 < m)
    (hN : 2 * m ≤ N) (d : ℕ) :
    0 ≤ rollUpN n (linearCoeff m N) 1 d ∧ rollUpN n (linearCoeff m N) 1 d ≤ N + 1 :=
  rollUpN_linearCoeff_bounded_general n hn d m N 1 hm hN (by norm_num) (by linarith)

open Filter Topology

/-- **Existence of a limit for EVERY positive slope, at any root order.**
Generalizes `linearRadical_converges_general` (`LinearChainGeneral.lean`,
root order `2`) to every root order at once. -/
theorem linearRadicalN_converges_general {n : ℕ} (hn : 2 ≤ n) {m N : ℝ} (hm : 0 < m)
    (hN : 2 * m ≤ N) :
    ∃ L : ℝ, Tendsto (fun d => rollUpN n (linearCoeff m N) 1 d) atTop (𝓝 L) ∧ L ≤ N + 1 := by
  have hnonneg : ∀ k, 0 ≤ linearCoeff m N k := fun k => by
    unfold linearCoeff
    have hk2 : (-2 : ℝ) ≤ (k : ℝ) - 2 := by
      have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      linarith
    nlinarith [hk2]
  have hmono : Monotone (fun d => rollUpN n (linearCoeff m N) 1 d) :=
    truncRadicalN_monotone n (linearCoeff m N) hnonneg
  have hbdd : BddAbove (Set.range (fun d => rollUpN n (linearCoeff m N) 1 d)) := by
    refine ⟨N + 1, ?_⟩
    rintro x ⟨d, rfl⟩
    exact (linearCoeffN_bounded_general hn hm hN d).2
  refine ⟨⨆ i, rollUpN n (linearCoeff m N) 1 i, tendsto_atTop_ciSup hmono hbdd, ?_⟩
  apply ciSup_le
  intro d
  exact (linearCoeffN_bounded_general hn hm hN d).2

end RamanujanNested
