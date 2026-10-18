import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Defs.lean — the general nested radical (Section 4, arbitrary coefficient sequences)

We formalize the recursion
  `R_k = √(1 + a_k · R_{k+1})`,   `R_{N+1} := 1` (virtual seed for the innermost term),
which unwinds to the paper's closed display
  `R_1^{(N)} = √(1 + a_1 √(1 + a_2 √(⋯ √(1 + a_N))))`.

`rollUp a T d` computes this with a general seed `T` at the bottom instead of the
fixed seed `1`, matching Algorithm 1 (`r ← T; for k = d downTo 1: r ← √(1+a_k r)`)
literally: the coefficient used at the OUTERMOST (last) step is always `a 1` of
whatever function is passed in, and the recursive call shifts to `fun k => a (k+1)`
for the remaining `d - 1` steps. This is what makes `a 1` outermost regardless of
depth `d`, matching the paper's fixed indexing (as opposed to a naive recursion
that would put `a d` outermost, which does NOT match the paper's display).

Setting `T = 1` recovers exactly `R_1^{(N)}` as displayed in Section 4.
Setting `T = 0` recovers the specific "forward evaluation" used in Algorithm 1 /
Table 2 for the target-value family `a_k = N + k - 2` (note: Table 2's "classical
forward evaluation" numerically checks out against `a_k = N + k - 2` with `N = 3`,
*not* against the classical `a_k = k` from the Introduction — the two are different
coefficient families; keep them distinct when citing this code against the paper).
-/

namespace RamanujanNested

/-- The truncated nested radical, general seed `T`, depth `d`.
`rollUp a T d` unwinds to `√(1 + a 1 · √(1 + a 2 · √(⋯ √(1 + a d · T))))`
(`d` square roots, seed `T` at the very bottom, `a 1` outermost). -/
noncomputable def rollUp (a : ℕ → ℝ) (T : ℝ) : ℕ → ℝ
  | 0 => T
  | (n + 1) => Real.sqrt (1 + a 1 * rollUp (fun k => a (k + 1)) T n)

/-- Unfolding lemma for `rollUp`, stated explicitly so later proofs don't rely on
definitional unfolding firing silently. -/
theorem rollUp_succ (a : ℕ → ℝ) (T : ℝ) (n : ℕ) :
    rollUp a T (n + 1) = Real.sqrt (1 + a 1 * rollUp (fun k => a (k + 1)) T n) := rfl

/-- The paper's `R_1^{(N)}` (Section 4): `rollUp` with the canonical seed `1`. -/
noncomputable def truncRadical (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  rollUp a 1 N

/-- The universal bound `r* = (A + √(A²+4))/2` (Section 4.1). -/
noncomputable def rStar (A : ℝ) : ℝ :=
  (A + Real.sqrt (A ^ 2 + 4)) / 2

/-- `r*` is nonnegative for `A ≥ 0`. -/
theorem rStar_nonneg {A : ℝ} (hA : 0 ≤ A) : 0 ≤ rStar A := by
  unfold rStar
  have h4 : (0 : ℝ) ≤ A ^ 2 + 4 := by positivity
  have := Real.sqrt_nonneg (A ^ 2 + 4)
  linarith

/-- The defining algebraic property of `r*`: it is the positive root of
`x² = 1 + A·x` (Section 4.1's induction step relies on exactly this identity:
`r*` is constructed so that "one more layer" at the extremal coefficient `A`
and the extremal seed `r*` maps `r*` back to itself). -/
theorem rStar_sq (A : ℝ) : (rStar A) ^ 2 = 1 + A * rStar A := by
  have hsq : Real.sqrt (A ^ 2 + 4) ^ 2 = A ^ 2 + 4 := Real.sq_sqrt (by positivity)
  have expand :
      ((A + Real.sqrt (A ^ 2 + 4)) / 2) ^ 2 -
          (1 + A * ((A + Real.sqrt (A ^ 2 + 4)) / 2)) =
        (Real.sqrt (A ^ 2 + 4) ^ 2 - (A ^ 2 + 4)) / 4 := by ring
  rw [hsq] at expand
  unfold rStar
  linarith [expand]

end RamanujanNested
