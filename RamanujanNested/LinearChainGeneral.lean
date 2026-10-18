import RamanujanNested.LinearChain
import Mathlib

/-!
# LinearChainGeneral.lean — existence of a limit for EVERY positive slope

`LinearChain.lean` proves existence of a limit for `linearCoeff m N`
(`a_k = N+m(k-2)`) only for slope `m ≥ 1`, using the ceiling `C(N) = N`,
which is exactly tight at `m = 1` and fails below it (`m² ≥ 1` is needed).

This file closes the remaining range `0 < m < 1` — and, in fact, gives a
single argument covering ALL `m > 0` at once — by using a slightly looser
ceiling `C(N) = N + 1` instead of `C(N) = N`. The extra `+1` of slack turns
out to be *more* than enough for every positive slope, not just small ones:
the key inequality reduces to `0 ≤ N + m + m²`, which holds unconditionally
once `m > 0` and `N ≥ 0` — no case split on `m` is needed at all.

The price is a looser bound: `L ≤ N+1` here, instead of `L ≤ N`
(`LinearChain.lean`'s tight bound, still the better result whenever
`m ≥ 1` applies). For `0 < m < 1` this is the only bound available, but it
still gives what matters most: existence of a finite limit for the entire
positive-slope range, closing the gap left open in `LinearChain.lean`.

## Coverage after this file

Together with `LinearChain.lean`, existence of a limit is now known for
`linearCoeff m N` at every slope `m > 0`: the tight bound `L ≤ N` for `m ≥ 1`,
the looser bound `L ≤ N+1` for `0 < m < 1` (and, redundantly but harmlessly,
also for `m ≥ 1`). In particular Kusniec's difference-of-oblongs Radiciatory
(slope `q-1`) is now covered for every `q > 1`, not just `q ≥ 2`.
-/

namespace RamanujanNested

/-- **Moving-ceiling boundedness, ALL positive slopes.** Same shift relation
as `rollUp_linearCoeff_bounded`, but with ceiling `C(N) = N+1` instead of
`C(N) = N`. The key inequality `1 + a_1(N)·C(N+m) ≤ C(N)²` reduces (after
expanding) to `0 ≤ N + m + m²`, true for any `m > 0` and `N ≥ 0` — no lower
bound on `m` is needed, unlike `rollUp_linearCoeff_bounded`. -/
theorem rollUp_linearCoeff_bounded_general :
    ∀ (d : ℕ) (m N T : ℝ), 0 < m → 2 * m ≤ N → 0 ≤ T → T ≤ N + 1 →
      0 ≤ rollUp (linearCoeff m N) T d ∧ rollUp (linearCoeff m N) T d ≤ N + 1 := by
  intro d
  induction d with
  | zero =>
    intro m N T _ _ hT0 hTN
    exact ⟨hT0, hTN⟩
  | succ n ih =>
    intro m N T hm hN hT0 hTN
    have hN1 : 2 * m ≤ N + m := by linarith
    have hTN1 : T ≤ (N + m) + 1 := by linarith
    obtain ⟨_, hhi⟩ := ih m (N + m) T hm hN1 hT0 hTN1
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
    have hradicand_le :
        1 + linearCoeff m N 1 * rollUp (linearCoeff m (N + m)) T n ≤ (N + 1) ^ 2 := by
      rw [ha1]
      have hmul : (N - m) * rollUp (linearCoeff m (N + m)) T n ≤ (N - m) * ((N + m) + 1) :=
        mul_le_mul_of_nonneg_left hhi (by linarith)
      nlinarith [hmul, sq_nonneg m, hm, hN]
    refine ⟨Real.sqrt_nonneg _, ?_⟩
    calc Real.sqrt (1 + linearCoeff m N 1 * rollUp (linearCoeff m (N + m)) T n)
        ≤ Real.sqrt ((N + 1) ^ 2) := Real.sqrt_le_sqrt hradicand_le
      _ = N + 1 := Real.sqrt_sq (by linarith)

/-- Specialized to the canonical seed `T = 1`. -/
theorem linearCoeff_bounded_general {m N : ℝ} (hm : 0 < m) (hN : 2 * m ≤ N) (d : ℕ) :
    0 ≤ truncRadical (linearCoeff m N) d ∧ truncRadical (linearCoeff m N) d ≤ N + 1 :=
  rollUp_linearCoeff_bounded_general d m N 1 hm hN (by norm_num) (by linarith)

open Filter Topology

/-- **Existence of a limit for EVERY positive slope `m > 0`.** Closes the gap
`LinearChain.lean` left open for `0 < m < 1`. Gives the looser bound `L ≤ N+1`
rather than `L ≤ N` — use `linearRadical_converges` instead whenever `m ≥ 1`
is known, for the tighter bound. -/
theorem linearRadical_converges_general {m N : ℝ} (hm : 0 < m) (hN : 2 * m ≤ N) :
    ∃ L : ℝ, Tendsto (truncRadical (linearCoeff m N)) atTop (𝓝 L) ∧ L ≤ N + 1 := by
  have hnonneg : ∀ k, 0 ≤ linearCoeff m N k := fun k => by
    unfold linearCoeff
    have hk2 : (-2 : ℝ) ≤ (k : ℝ) - 2 := by
      have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      linarith
    nlinarith [hk2]
  have hmono : Monotone (truncRadical (linearCoeff m N)) :=
    truncRadical_monotone (linearCoeff m N) hnonneg
  have hbdd : BddAbove (Set.range (truncRadical (linearCoeff m N))) := by
    refine ⟨N + 1, ?_⟩
    rintro x ⟨d, rfl⟩
    exact (linearCoeff_bounded_general hm hN d).2
  refine ⟨⨆ i, truncRadical (linearCoeff m N) i, tendsto_atTop_ciSup hmono hbdd, ?_⟩
  apply ciSup_le
  intro d
  exact (linearCoeff_bounded_general hm hN d).2

end RamanujanNested
