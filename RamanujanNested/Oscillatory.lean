import RamanujanNested.ControlledNegative
import RamanujanNested.Convergence
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Oscillatory.lean — Appendix A.2, oscillatory coefficients

`a_k = 1 + α sin k`. The paper: "provided the amplitude α satisfies the
admissibility constraints of Lemma 1, the recursion remains real-valued and
stable" — without pinning down a concrete α or actually invoking Lemma 1's
inequality. We make this precise.

* `oscillatory_bounds`: `1 - α ≤ a_k ≤ 1 + α` for every `k`, unconditionally.
* For `0 ≤ α ≤ 1` this alone gives `a_k ≥ 0`, so the simple machinery
  (`Bounds.lean` + `Monotone.lean` + `Convergence.lean`) already applies —
  Lemma 1 is not even needed in this regime
  (`oscillatory_converges_small_alpha`).
* For general `α ≥ 0`, `a_k` can dip negative; `oscillatory_controlled_negative`
  takes the paper's admissibility condition as an explicit hypothesis
  (`α ≤ 1 / rStar (1+α)`) and discharges `ControlledNegative.lean`'s
  guarantees.
* `oscillatory_alpha_tenth_admissible` plugs in a concrete `α = 1/10`
  (matching the paper's own "small parameter α > 0" framing) and closes the
  admissibility hypothesis by direct numeric computation — one fully closed
  instance with no remaining hypotheses on `α`.
-/

namespace RamanujanNested

/-- The oscillatory coefficient family from Appendix A.2. -/
noncomputable def oscillatoryCoeff (α : ℝ) (k : ℕ) : ℝ := 1 + α * Real.sin (k : ℝ)

/-- Unconditional two-sided bound: `1 - α ≤ a_k ≤ 1 + α`. -/
theorem oscillatory_bounds {α : ℝ} (hα : 0 ≤ α) (k : ℕ) :
    1 - α ≤ oscillatoryCoeff α k ∧ oscillatoryCoeff α k ≤ 1 + α := by
  unfold oscillatoryCoeff
  have hlo := Real.neg_one_le_sin (k : ℝ)
  have hhi := Real.sin_le_one (k : ℝ)
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlo hα]
  · nlinarith [mul_le_mul_of_nonneg_left hhi hα]

/-- For `0 ≤ α ≤ 1`, `a_k ≥ 1 - α ≥ 0`, so the simple (no-negative-coefficient)
machinery already gives convergence — Lemma 1 isn't needed in this regime. -/
theorem oscillatory_converges_small_alpha {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ L : ℝ, Filter.Tendsto (truncRadical (oscillatoryCoeff α)) Filter.atTop (nhds L) := by
  have hA : (0 : ℝ) ≤ 1 + α := by linarith
  have ha_nonneg : ∀ k, 0 ≤ oscillatoryCoeff α k := fun k => by
    have := (oscillatory_bounds hα0 k).1; linarith
  have ha_le : ∀ k, oscillatoryCoeff α k ≤ 1 + α := fun k => (oscillatory_bounds hα0 k).2
  exact truncRadical_converges hA (oscillatoryCoeff α) ha_nonneg ha_le

/-- General `α ≥ 0`: the paper's admissibility condition, made explicit, via
Lemma 1. Realness (nonnegative radicand at every step) and boundedness both
follow once `α ≤ 1 / rStar (1+α)` is supplied. -/
theorem oscillatory_controlled_negative {α : ℝ} (hα : 0 ≤ α)
    (hadm : α ≤ 1 / rStar (1 + α)) (T : ℝ) (hT0 : 0 ≤ T) (hTA : T ≤ rStar (1 + α)) :
    ∀ d, (0 ≤ rollUp (oscillatoryCoeff α) T d ∧
            rollUp (oscillatoryCoeff α) T d ≤ rStar (1 + α)) ∧
          (0 ≤ 1 + oscillatoryCoeff α 1 *
                rollUp (fun k => oscillatoryCoeff α (k + 1)) T d) := by
  intro d
  have hA : (0 : ℝ) ≤ 1 + α := by linarith
  have ha_lo : ∀ k, -α ≤ oscillatoryCoeff α k := fun k => by
    have := (oscillatory_bounds hα k).1; linarith
  have ha_le : ∀ k, oscillatoryCoeff α k ≤ 1 + α := fun k => (oscillatory_bounds hα k).2
  exact rollUp_controlled_negative hA hα hadm hT0 hTA d (oscillatoryCoeff α) ha_lo ha_le

/-- Concrete instance: `α = 1/10`. The admissibility hypothesis of
`oscillatory_controlled_negative` is discharged by direct computation
(`rStar (1.1) ≤ 2`, so `1/rStar(1.1) ≥ 1/2 ≥ 1/10`), giving a fully closed
corollary with no remaining hypotheses on `α`. -/
theorem oscillatory_alpha_tenth_admissible :
    (1 : ℝ) / 10 ≤ 1 / rStar (1 + 1 / 10) := by
  have hA : (0 : ℝ) ≤ 1 + 1 / 10 := by norm_num
  have hrpos : (0 : ℝ) < rStar (1 + 1 / 10) := lt_of_lt_of_le one_pos (one_le_rStar hA)
  have hle2 : rStar (1 + 1 / 10) ≤ 2 := by
    unfold rStar
    have hY : (0 : ℝ) ≤ 4 - (1 + (1 : ℝ) / 10) := by norm_num
    have hXY : (1 + (1 : ℝ) / 10) ^ 2 + 4 ≤ (4 - (1 + (1 : ℝ) / 10)) ^ 2 := by norm_num
    have hs : Real.sqrt ((1 + (1 : ℝ) / 10) ^ 2 + 4) ≤ 4 - (1 + (1 : ℝ) / 10) := by
      calc Real.sqrt ((1 + (1 : ℝ) / 10) ^ 2 + 4)
          ≤ Real.sqrt ((4 - (1 + (1 : ℝ) / 10)) ^ 2) := Real.sqrt_le_sqrt hXY
        _ = 4 - (1 + (1 : ℝ) / 10) := Real.sqrt_sq hY
    linarith
  have hstep : (1 : ℝ) / 2 ≤ 1 / rStar (1 + 1 / 10) :=
    one_div_le_one_div_of_le hrpos hle2
  linarith

end RamanujanNested
