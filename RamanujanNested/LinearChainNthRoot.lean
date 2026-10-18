import RamanujanNested.LinearChain
import RamanujanNested.NthRootChain
import Mathlib

/-!
# LinearChainNthRoot.lean — the unbounded linear family, at any root order n ≥ 2

`LinearChain.lean` proves existence of a limit for the unbounded linear
coefficient family `linearCoeff m N k = N+m(k-2)`, for any slope `m ≥ 1`, at
root order `2`. `NthRootChain.lean` generalizes root order to any `n ≥ 2`,
but only for *bounded* coefficient sequences. This file combines the two:
existence of a limit for `linearCoeff m N` (unbounded, slope `m ≥ 1`) at any
root order `n ≥ 2`, via the same moving-ceiling technique as `LinearChain.lean`
— the ceiling `C(N) = N` shifting to `C(N+m) = N+m` per recursive layer — now
run against `rollUpN` instead of `rollUp`.

## The key inequality, generalized

`LinearChain.lean`'s inductive step needs `(N-m)(N+m)+1 ≤ N^2`, i.e.
`1 ≤ m^2`, which is why `m ≥ 1` is required. Here the corresponding need is
`(N-m)(N+m)+1 ≤ N^n`. Since `N^n ≥ N^2` for `N ≥ 1` and `n ≥ 2`
(`pow_le_pow_right₀`), the same hypothesis `m ≥ 1` (giving `1 ≤ m^2`) is
enough to close it at every root order at once — no case split on `n`, and
`n = 2` recovers `LinearChain.lean`'s own inequality exactly.

As with `LinearChain.lean` and `PrimeChain.lean`, this establishes existence
of a limit and the bound `L ≤ N`, not the exact value of `L`.
-/

namespace RamanujanNested

/-- **Moving-ceiling boundedness, unbounded linear family, any root order.**
Same shift-by-`m` structure as `rollUp_linearCoeff_bounded`
(`LinearChain.lean`), with `rollUpN`/`rpow` in place of `rollUp`/`sqrt`. -/
theorem rollUpN_linearCoeff_bounded (n : ℕ) (hn : 2 ≤ n) :
    ∀ (d : ℕ) (m N T : ℝ), 1 ≤ m → 2 * m ≤ N → 0 ≤ T → T ≤ N →
      0 ≤ rollUpN n (linearCoeff m N) T d ∧ rollUpN n (linearCoeff m N) T d ≤ N := by
  intro d
  induction d with
  | zero =>
    intro m N T _ _ hT0 hTN
    exact ⟨hT0, hTN⟩
  | succ k ih =>
    intro m N T hm hN hT0 hTN
    have hN1 : 2 * m ≤ N + m := by linarith
    have hTN1 : T ≤ N + m := by linarith
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
    have hN_pos : (1:ℝ) ≤ N := by linarith
    have hn_ne : (n : ℝ) ≠ 0 := by
      have hpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      linarith
    rw [rollUpN_succ, hshift]
    have hradicand_le :
        1 + linearCoeff m N 1 * rollUpN n (linearCoeff m (N + m)) T k ≤ N ^ n := by
      rw [ha1]
      have hmul : (N - m) * rollUpN n (linearCoeff m (N + m)) T k ≤ (N - m) * (N + m) :=
        mul_le_mul_of_nonneg_left hhi (by linarith)
      have hpow : N ^ 2 ≤ N ^ n := pow_le_pow_right₀ hN_pos hn
      nlinarith [hmul, hpow, sq_nonneg (m - 1)]
    have hradicand_nonneg :
        0 ≤ 1 + linearCoeff m N 1 * rollUpN n (linearCoeff m (N + m)) T k :=
      add_nonneg zero_le_one (mul_nonneg ha1_nonneg hlo)
    refine ⟨Real.rpow_nonneg hradicand_nonneg _, ?_⟩
    calc (1 + linearCoeff m N 1 * rollUpN n (linearCoeff m (N + m)) T k) ^ (1 / (n : ℝ))
        ≤ (N ^ n : ℝ) ^ (1 / (n : ℝ)) :=
          Real.rpow_le_rpow hradicand_nonneg hradicand_le (by positivity)
      _ = N := by
          rw [← Real.rpow_natCast N n, ← Real.rpow_mul (by linarith), mul_one_div,
            div_self hn_ne, Real.rpow_one]

/-- Specialized to the canonical seed `T = 1`. -/
theorem linearCoeffN_bounded {n : ℕ} (hn : 2 ≤ n) {m N : ℝ} (hm : 1 ≤ m) (hN : 2 * m ≤ N)
    (d : ℕ) :
    0 ≤ rollUpN n (linearCoeff m N) 1 d ∧ rollUpN n (linearCoeff m N) 1 d ≤ N :=
  rollUpN_linearCoeff_bounded n hn d m N 1 hm hN (by norm_num) (by linarith)

open Filter Topology

/-- **Existence of a limit for any slope `m ≥ 1`, at any root order `n ≥ 2`.**
Generalizes `linearRadical_converges` (`LinearChain.lean`, root order `2`) to
every root order at once. As there, this gives existence and an upper bound
`L ≤ N`, not the exact value of `L`. -/
theorem linearRadicalN_converges {n : ℕ} (hn : 2 ≤ n) {m N : ℝ} (hm : 1 ≤ m)
    (hN : 2 * m ≤ N) :
    ∃ L : ℝ, Tendsto (fun d => rollUpN n (linearCoeff m N) 1 d) atTop (𝓝 L) ∧ L ≤ N := by
  have hnonneg : ∀ k, 0 ≤ linearCoeff m N k := fun k => by
    unfold linearCoeff
    have hk2 : (-2 : ℝ) ≤ (k : ℝ) - 2 := by
      have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      linarith
    nlinarith [hk2]
  have hmono : Monotone (fun d => rollUpN n (linearCoeff m N) 1 d) :=
    truncRadicalN_monotone n (linearCoeff m N) hnonneg
  have hbdd : BddAbove (Set.range (fun d => rollUpN n (linearCoeff m N) 1 d)) := by
    refine ⟨N, ?_⟩
    rintro x ⟨d, rfl⟩
    exact (linearCoeffN_bounded hn hm hN d).2
  refine ⟨⨆ i, rollUpN n (linearCoeff m N) 1 i, tendsto_atTop_ciSup hmono hbdd, ?_⟩
  apply ciSup_le
  intro d
  exact (linearCoeffN_bounded hn hm hN d).2

end RamanujanNested
