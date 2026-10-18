import RamanujanNested.LinearChainTight
import RamanujanNested.NthRootChain
import Mathlib

/-!
# LinearChainTightNthRoot.lean — the unbounded linear family, tight bound, any root order

Generalizes `LinearChainTight.lean` (the exact minimal ceiling shift
`s(m) = (√(5m²+4)-3m)/2` for slope `0 < m ≤ 1`, root order `2`) to any root
order `n ≥ 2`. The bound `L ≤ N+s(m)` carries over unchanged; it is no longer
claimed to be the *tightest possible* at `n ≥ 3` (that would need re-deriving
the minimal shift for each `n`), only that the same ceiling remains valid.

## Why the same ceiling still works

`LinearChainTight.lean`'s key step shows `1+(N-m)((N+m)+s) ≤ (N+s)^2` exactly
(via the identity `s²+3ms+m²=1` and `s(N-2m) ≥ 0`). Since `(N+s)^n ≥ (N+s)^2`
for `N+s ≥ 1` and `n ≥ 2` — and `N+s ≥ 1` is exactly `tightShift_seed_le`,
already proved in `LinearChainTight.lean` — chaining the two inequalities
closes the argument at every root order at once.
-/

namespace RamanujanNested

/-- **Moving-ceiling boundedness, tight shift, any root order.** -/
theorem rollUpN_linearCoeff_bounded_tight (n : ℕ) (hn : 2 ≤ n) :
    ∀ (d : ℕ) (m N T : ℝ), 0 < m → m ≤ 1 → 2 * m ≤ N → 0 ≤ T → T ≤ N + tightShift m →
      0 ≤ rollUpN n (linearCoeff m N) T d ∧
        rollUpN n (linearCoeff m N) T d ≤ N + tightShift m := by
  intro d
  induction d with
  | zero =>
    intro m N T _ _ _ hT0 hTN
    exact ⟨hT0, hTN⟩
  | succ k ih =>
    intro m N T hm hm1 hN hT0 hTN
    have hN1 : 2 * m ≤ N + m := by linarith
    have hTN1 : T ≤ (N + m) + tightShift m := by linarith
    obtain ⟨hlo, hhi⟩ := ih m (N + m) T hm hm1 hN1 hT0 hTN1
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
    have hs_eq := tightShift_sq_eq m
    have hs_nonneg := tightShift_nonneg hm1
    have hNs_ge1 : (1:ℝ) ≤ N + tightShift m := by
      have := tightShift_seed_le hm hm1
      linarith
    have hn_ne : (n : ℝ) ≠ 0 := by
      have hpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      linarith
    rw [rollUpN_succ, hshift]
    have hradicand_le :
        1 + linearCoeff m N 1 * rollUpN n (linearCoeff m (N + m)) T k ≤
          (N + tightShift m) ^ n := by
      rw [ha1]
      have hmul : (N - m) * rollUpN n (linearCoeff m (N + m)) T k ≤
          (N - m) * ((N + m) + tightShift m) :=
        mul_le_mul_of_nonneg_left hhi (by linarith)
      have hkey : (N + tightShift m) ^ 2 -
          (1 + (N - m) * ((N + m) + tightShift m)) = (tightShift m) * (N - 2 * m) := by
        linear_combination hs_eq
      have hprod_nonneg : 0 ≤ (tightShift m) * (N - 2 * m) :=
        mul_nonneg hs_nonneg (by linarith)
      have hceil_ineq2 :
          1 + (N - m) * ((N + m) + tightShift m) ≤ (N + tightShift m) ^ 2 := by
        linarith [hkey, hprod_nonneg]
      have hpow : (N + tightShift m) ^ 2 ≤ (N + tightShift m) ^ n :=
        pow_le_pow_right₀ hNs_ge1 hn
      linarith [hmul, hceil_ineq2, hpow]
    have hradicand_nonneg :
        0 ≤ 1 + linearCoeff m N 1 * rollUpN n (linearCoeff m (N + m)) T k :=
      add_nonneg zero_le_one (mul_nonneg ha1_nonneg hlo)
    refine ⟨Real.rpow_nonneg hradicand_nonneg _, ?_⟩
    calc (1 + linearCoeff m N 1 * rollUpN n (linearCoeff m (N + m)) T k) ^ (1 / (n : ℝ))
        ≤ ((N + tightShift m) ^ n : ℝ) ^ (1 / (n : ℝ)) :=
          Real.rpow_le_rpow hradicand_nonneg hradicand_le (by positivity)
      _ = N + tightShift m := by
          rw [← Real.rpow_natCast (N + tightShift m) n, ← Real.rpow_mul (by linarith),
            mul_one_div, div_self hn_ne, Real.rpow_one]

/-- Specialized to the canonical seed `T = 1`. -/
theorem linearCoeffN_bounded_tight {n : ℕ} (hn : 2 ≤ n) {m N : ℝ} (hm : 0 < m) (hm1 : m ≤ 1)
    (hN : 2 * m ≤ N) (d : ℕ) :
    0 ≤ rollUpN n (linearCoeff m N) 1 d ∧
      rollUpN n (linearCoeff m N) 1 d ≤ N + tightShift m :=
  rollUpN_linearCoeff_bounded_tight n hn d m N 1 hm hm1 hN (by norm_num)
    (by linarith [tightShift_seed_le hm hm1])

open Filter Topology

/-- **Existence of a limit, tight bound, for `0 < m ≤ 1`, at any root order.**
Generalizes `linearRadical_converges_tight` (`LinearChainTight.lean`, root
order `2`) to every root order at once. -/
theorem linearRadicalN_converges_tight {n : ℕ} (hn : 2 ≤ n) {m N : ℝ} (hm : 0 < m)
    (hm1 : m ≤ 1) (hN : 2 * m ≤ N) :
    ∃ L : ℝ, Tendsto (fun d => rollUpN n (linearCoeff m N) 1 d) atTop (𝓝 L) ∧
      L ≤ N + tightShift m := by
  have hnonneg : ∀ k, 0 ≤ linearCoeff m N k := fun k => by
    unfold linearCoeff
    have hk2 : (-2 : ℝ) ≤ (k : ℝ) - 2 := by
      have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      linarith
    nlinarith [hk2]
  have hmono : Monotone (fun d => rollUpN n (linearCoeff m N) 1 d) :=
    truncRadicalN_monotone n (linearCoeff m N) hnonneg
  have hbdd : BddAbove (Set.range (fun d => rollUpN n (linearCoeff m N) 1 d)) := by
    refine ⟨N + tightShift m, ?_⟩
    rintro x ⟨d, rfl⟩
    exact (linearCoeffN_bounded_tight hn hm hm1 hN d).2
  refine ⟨⨆ i, rollUpN n (linearCoeff m N) 1 i, tendsto_atTop_ciSup hmono hbdd, ?_⟩
  apply ciSup_le
  intro d
  exact (linearCoeffN_bounded_tight hn hm hm1 hN d).2

end RamanujanNested
