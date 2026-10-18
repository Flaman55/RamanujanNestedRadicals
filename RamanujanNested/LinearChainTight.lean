import RamanujanNested.LinearChain
import RamanujanNested.LinearChainGeneral
import Mathlib

/-!
# LinearChainTight.lean — the OPTIMAL bound for `0 < m ≤ 1`, closing the gap for real

`LinearChainGeneral.lean` closes existence for `0 < m < 1`, but with a
deliberately loose bound `L ≤ N+1` (a fixed `+1` slack chosen for simplicity,
not tightness). This file replaces that slack with the *exact* minimal shift
`s(m)` that the moving-ceiling argument allows, making the bound as tight as
possible for every `m` in `(0,1]` — matching `LinearChain.lean`'s tight
`L ≤ N` exactly at the shared boundary `m = 1`.

## The exact shift

The moving-ceiling step needs `s² + 3ms + m² ≥ 1` (see `LinearChain.lean`'s
docstring: this is exactly `m² ≥ 1` when `s = 0`). Taking `s` to be the
*positive root* of the equality case `s² + 3ms + m² = 1` gives the smallest
valid shift:

`s(m) = (√(5m²+4) − 3m) / 2`

This is `≥ 0` exactly when `m ≤ 1` (for `m > 1` it goes negative, which is
why `LinearChain.lean` uses `s = 0` there instead — going negative would mean
a ceiling smaller than `N`, not covered by this file). At `m = 1`,
`s(1) = (√9−3)/2 = 0`, recovering `LinearChain.lean` exactly.

## Why this is enough (not just "an" inequality, but exactly tight)

Expanding `(N+s)² − (1 + (N-m)(N+m+s))` and substituting the identity
`s²+3ms+m² = 1` collapses it to exactly `s·(N−2m)` — which is `≥ 0` given
`s ≥ 0` (from `m ≤ 1`) and `N ≥ 2m` (the standing nonnegativity hypothesis).
So the inductive step holds with the *smallest* ceiling shift that makes the
argument work at all, for every `m` in `(0,1]` at once — no further
tightening is possible within this proof technique.

## Coverage after this file

Existence of a limit for `linearCoeff m N` is now known for every `m > 0`
with the *tightest* bound this technique gives: `L ≤ N` for `m ≥ 1`
(`LinearChain.lean`), `L ≤ N + s(m)` for `0 < m ≤ 1` (this file), continuously
matching at `m = 1`. `LinearChainGeneral.lean`'s looser `L ≤ N+1` is now
superseded for `0 < m < 1` but kept for its simpler, sqrt-free proof.
-/

namespace RamanujanNested

/-- The exact minimal ceiling shift for slope `m`: the positive root of
`s²+3ms+m²=1`. Well-defined for any real `m`; only used here for `m ≤ 1`,
where it is nonnegative (`tightShift_nonneg`). -/
noncomputable def tightShift (m : ℝ) : ℝ := (Real.sqrt (5 * m ^ 2 + 4) - 3 * m) / 2

/-- The defining algebraic identity, unconditional in `m`: follows purely
from `Real.sqrt (5m²+4) ^ 2 = 5m²+4` (valid since `5m²+4 ≥ 0` always) by
straightforward expansion. -/
theorem tightShift_sq_eq (m : ℝ) :
    (tightShift m) ^ 2 + 3 * m * (tightShift m) + m ^ 2 = 1 := by
  have hnn : (0:ℝ) ≤ 5 * m ^ 2 + 4 := by nlinarith [sq_nonneg m]
  have hr2 : Real.sqrt (5 * m ^ 2 + 4) ^ 2 = 5 * m ^ 2 + 4 := Real.sq_sqrt hnn
  unfold tightShift
  nlinarith [hr2]

/-- `s(m) ≥ 0` exactly when `m ≤ 1`: comparing `(3m)² = 9m² ≤ 5m²+4` (which
holds iff `m² ≤ 1`, i.e. `m ≤ 1` together with `m ≥ -1`, but for `m ≤ 0` the
bound `3m ≤ 0 ≤ √(5m²+4)` is immediate anyway) against `√(5m²+4)`. -/
theorem tightShift_nonneg {m : ℝ} (hm1 : m ≤ 1) : 0 ≤ tightShift m := by
  unfold tightShift
  rcases le_or_lt m 0 with hm0 | hm0
  · have hr_nonneg : (0:ℝ) ≤ Real.sqrt (5 * m ^ 2 + 4) := Real.sqrt_nonneg _
    linarith
  · have h3m_nonneg : (0:ℝ) ≤ 3 * m := by linarith
    have hsq_le : (3 * m) ^ 2 ≤ 5 * m ^ 2 + 4 := by nlinarith [hm1, hm0]
    have h3m_eq : 3 * m = Real.sqrt ((3 * m) ^ 2) := (Real.sqrt_sq h3m_nonneg).symm
    have hstep : Real.sqrt ((3 * m) ^ 2) ≤ Real.sqrt (5 * m ^ 2 + 4) :=
      Real.sqrt_le_sqrt hsq_le
    rw [← h3m_eq] at hstep
    linarith

/-- Sanity check: at `m = 1`, the exact shift is `0`, recovering
`LinearChain.lean`'s ceiling exactly. -/
theorem tightShift_one : tightShift 1 = 0 := by
  have hr : Real.sqrt (5 * (1:ℝ) ^ 2 + 4) = 3 := by
    rw [show (5 * (1:ℝ) ^ 2 + 4) = 3 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  unfold tightShift
  rw [hr]
  norm_num

/-- Needed so the canonical seed `T = 1` satisfies `T ≤ N + tightShift m`
whenever `N ≥ 2m`: at the worst case `N = 2m`, this says
`1 ≤ 2m + tightShift m`, i.e. `√(5m²+4) ≥ 2-m` — true because squaring both
(nonnegative, for `0 < m ≤ 1`) sides gives `5m²+4 ≥ (2-m)² = 4-4m+m²`, i.e.
`4m²+4m ≥ 0`, true for `m > 0`. -/
theorem tightShift_seed_le {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) :
    1 ≤ 2 * m + tightShift m := by
  unfold tightShift
  have h2m_nonneg : (0:ℝ) ≤ 2 - m := by linarith
  have hsq : (2 - m) ^ 2 ≤ 5 * m ^ 2 + 4 := by nlinarith [hm, hm1]
  have hstep : Real.sqrt ((2 - m) ^ 2) ≤ Real.sqrt (5 * m ^ 2 + 4) := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq h2m_nonneg] at hstep
  linarith

/-- **Moving-ceiling boundedness, tight version, for `0 < m ≤ 1`.** Same
shift-by-`m` recursive structure as `rollUp_linearCoeff_bounded` and
`rollUp_linearCoeff_bounded_general`, but with the *exact* minimal ceiling
`C(N) = N + tightShift m`. -/
theorem rollUp_linearCoeff_bounded_tight :
    ∀ (d : ℕ) (m N T : ℝ), 0 < m → m ≤ 1 → 2 * m ≤ N → 0 ≤ T → T ≤ N + tightShift m →
      0 ≤ rollUp (linearCoeff m N) T d ∧ rollUp (linearCoeff m N) T d ≤ N + tightShift m := by
  intro d
  induction d with
  | zero =>
    intro m N T _ _ _ hT0 hTN
    exact ⟨hT0, hTN⟩
  | succ n ih =>
    intro m N T hm hm1 hN hT0 hTN
    have hN1 : 2 * m ≤ N + m := by linarith
    have hTN1 : T ≤ (N + m) + tightShift m := by linarith
    obtain ⟨_, hhi⟩ := ih m (N + m) T hm hm1 hN1 hT0 hTN1
    have hshift : (fun k => linearCoeff m N (k + 1)) = linearCoeff m (N + m) := by
      funext k
      unfold linearCoeff
      push_cast
      ring
    have ha1 : linearCoeff m N 1 = N - m := by
      unfold linearCoeff
      push_cast
      ring
    have ha1_nonneg : 0 ≤ linearCoeff m N 1 := by
      rw [ha1]; linarith
    rw [rollUp_succ, hshift]
    have hs_eq := tightShift_sq_eq m
    have hs_nonneg := tightShift_nonneg hm1
    have hkey : (N + tightShift m) ^ 2 -
        (1 + (N - m) * ((N + m) + tightShift m)) = (tightShift m) * (N - 2 * m) := by
      linear_combination hs_eq
    have hprod_nonneg : 0 ≤ (tightShift m) * (N - 2 * m) :=
      mul_nonneg hs_nonneg (by linarith)
    have hceil_ineq :
        1 + (N - m) * ((N + m) + tightShift m) ≤ (N + tightShift m) ^ 2 := by
      linarith [hkey, hprod_nonneg]
    have hradicand_le :
        1 + linearCoeff m N 1 * rollUp (linearCoeff m (N + m)) T n ≤ (N + tightShift m) ^ 2 := by
      rw [ha1]
      have hmul : (N - m) * rollUp (linearCoeff m (N + m)) T n ≤ (N - m) * ((N + m) + tightShift m) :=
        mul_le_mul_of_nonneg_left hhi (by linarith)
      linarith [hmul, hceil_ineq]
    refine ⟨Real.sqrt_nonneg _, ?_⟩
    calc Real.sqrt (1 + linearCoeff m N 1 * rollUp (linearCoeff m (N + m)) T n)
        ≤ Real.sqrt ((N + tightShift m) ^ 2) := Real.sqrt_le_sqrt hradicand_le
      _ = N + tightShift m := Real.sqrt_sq (by linarith [hs_nonneg])

/-- Specialized to the canonical seed `T = 1`. -/
theorem linearCoeff_bounded_tight {m N : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (hN : 2 * m ≤ N)
    (d : ℕ) :
    0 ≤ truncRadical (linearCoeff m N) d ∧
      truncRadical (linearCoeff m N) d ≤ N + tightShift m :=
  rollUp_linearCoeff_bounded_tight d m N 1 hm hm1 hN (by norm_num)
    (by linarith [tightShift_seed_le hm hm1])

open Filter Topology

/-- **Existence of a limit, tight bound, for every `0 < m ≤ 1`.** Combined
with `LinearChain.lean`'s `linearRadical_converges` (for `m ≥ 1`), this gives
the tightest bound this technique provides across the ENTIRE positive-slope
range, with no remaining gap. -/
theorem linearRadical_converges_tight {m N : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (hN : 2 * m ≤ N) :
    ∃ L : ℝ, Tendsto (truncRadical (linearCoeff m N)) atTop (𝓝 L) ∧ L ≤ N + tightShift m := by
  have hnonneg : ∀ k, 0 ≤ linearCoeff m N k := fun k => by
    unfold linearCoeff
    have hk2 : (-2 : ℝ) ≤ (k : ℝ) - 2 := by
      have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      linarith
    nlinarith [hk2]
  have hmono : Monotone (truncRadical (linearCoeff m N)) :=
    truncRadical_monotone (linearCoeff m N) hnonneg
  have hbdd : BddAbove (Set.range (truncRadical (linearCoeff m N))) := by
    refine ⟨N + tightShift m, ?_⟩
    rintro x ⟨d, rfl⟩
    exact (linearCoeff_bounded_tight hm hm1 hN d).2
  refine ⟨⨆ i, truncRadical (linearCoeff m N) i, tendsto_atTop_ciSup hmono hbdd, ?_⟩
  apply ciSup_le
  intro d
  exact (linearCoeff_bounded_tight hm hm1 hN d).2

end RamanujanNested
