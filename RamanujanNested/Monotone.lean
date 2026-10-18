import RamanujanNested.Defs

/-!
# Monotone.lean — Section 4.1, monotonicity of the truncated sequence

"the truncated values R_1^(N) form a monotone increasing sequence in N"
(assuming `a_k ≥ 0` for all `k`, unlike `Bounds.lean` this direction genuinely
needs nonnegativity: a negative coefficient can make adding a layer decrease
the value). We prove the single-step inequality
`rollUp a 1 N ≤ rollUp a 1 (N+1)` and package it as `Monotone (truncRadical a)`.
-/

namespace RamanujanNested

/-- Single-step monotonicity: adding one more layer (with the canonical seed
`1`) never decreases the truncated radical, provided every coefficient is
nonnegative. Stated with `a` quantified inside the induction (same reason as
in `Bounds.lean`: the inductive step needs the claim for the *shifted*
coefficient sequence, not just the original `a`). -/
theorem rollUp_seed_one_step_mono :
    ∀ (N : ℕ) (a : ℕ → ℝ), (∀ k, 0 ≤ a k) → rollUp a 1 N ≤ rollUp a 1 (N + 1) := by
  intro N
  induction N with
  | zero =>
    intro a ha
    rw [rollUp_succ]
    have h1 : rollUp (fun k => a (k + 1)) 1 0 = (1 : ℝ) := rfl
    rw [h1]
    have ha1 : 0 ≤ a 1 := ha 1
    have hle : (1 : ℝ) ≤ 1 + a 1 * 1 := by nlinarith
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + a 1 * 1) := Real.sqrt_le_sqrt hle
  | succ n ih =>
    intro a ha
    have ha_shift : ∀ k, 0 ≤ (fun k => a (k + 1)) k := fun k => ha (k + 1)
    have ih_shift := ih (fun k => a (k + 1)) ha_shift
    rw [rollUp_succ, rollUp_succ]
    have ha1 : 0 ≤ a 1 := ha 1
    have hstep : 1 + a 1 * rollUp (fun k => a (k + 1)) 1 n ≤
        1 + a 1 * rollUp (fun k => a (k + 1)) 1 (n + 1) := by
      have := mul_le_mul_of_nonneg_left ih_shift ha1
      linarith
    exact Real.sqrt_le_sqrt hstep

/-- `truncRadical a` is monotone in the truncation depth, for nonnegative
coefficients — the monotonicity half of Section 4.1's convergence argument. -/
theorem truncRadical_monotone (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) :
    Monotone (truncRadical a) := by
  apply monotone_nat_of_le_succ
  intro N
  exact rollUp_seed_one_step_mono N a ha

/-- **Monotonicity in the seed**, complementing `rollUp_seed_one_step_mono`'s
monotonicity in depth. For nonnegative coefficients, replacing the tail seed
`T` by a larger value can only increase (never decrease) every truncation.
This is the fact Appendix A.1's Table 3 ("tail-independence") invokes
informally — "the map `T ↦ R_1^{(d)}(T)` is monotone increasing" — made
precise here; `UnboundedChain.lean`'s `rollUp_classicalCoeff_le_of_tail_le`
specializes it to the classical family to recover the table's actual claim.
Stated with `a` quantified inside the induction, same reason as
`rollUp_seed_one_step_mono`: the inductive step needs the claim for the
*shifted* coefficient sequence, not just the original `a`. -/
theorem rollUp_mono_seed :
    ∀ (d : ℕ) (a : ℕ → ℝ), (∀ k, 0 ≤ a k) → ∀ (T1 T2 : ℝ), T1 ≤ T2 →
      rollUp a T1 d ≤ rollUp a T2 d := by
  intro d
  induction d with
  | zero => intro a _ T1 T2 hT; exact hT
  | succ n ih =>
    intro a ha T1 T2 hT
    rw [rollUp_succ, rollUp_succ]
    have ha_shift : ∀ k, 0 ≤ (fun k => a (k + 1)) k := fun k => ha (k + 1)
    have ih_shift := ih (fun k => a (k + 1)) ha_shift T1 T2 hT
    have ha1 : 0 ≤ a 1 := ha 1
    have hmul : a 1 * rollUp (fun k => a (k + 1)) T1 n ≤
        a 1 * rollUp (fun k => a (k + 1)) T2 n :=
      mul_le_mul_of_nonneg_left ih_shift ha1
    exact Real.sqrt_le_sqrt (by linarith [hmul])

end RamanujanNested
