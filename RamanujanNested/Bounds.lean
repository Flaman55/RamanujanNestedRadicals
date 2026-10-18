import RamanujanNested.Defs

/-!
# Bounds.lean — Section 4.1's main sufficient condition

If the coefficients are bounded above, `a k ≤ A` for all `k`, and the seed `T`
lies in `[0, r*]` where `r* = rStar A`, every truncation `rollUp a T d` stays
inside `[0, r*]`. This is the boundedness half of the paper's convergence
argument for Section 4.1: "if the coefficients are uniformly bounded ... then
the sequence (R_1^(N)) is bounded from above ... R_1^(N) ≤ r*".

**Note on the hypothesis.** The paper states this for `0 ≤ a_k ≤ A`. The proof
below only ever uses `a_k ≤ A`: the lower bound `0 ≤ rollUp a T d` comes for
free from `Real.sqrt_nonneg` regardless of the sign of `a_k` (Lean's `Real.sqrt`
is total, returning `0` on negative input), and the upper-bound induction only
needs `a 1 ≤ A` together with the inner value being in `[0, r*]` — it never
needs `a 1 ≥ 0`. So the nonnegativity half of the paper's hypothesis is not
actually load-bearing for *this* conclusion; it becomes load-bearing only for
the separate claim that the recursion stays real-valued when coefficients are
allowed to go negative, which is genuinely Lemma 1's content
(`ControlledNegative.lean`), not this file's.

Applying this with `T = 1` (the canonical seed, see `Defs.lean`) and
`one_le_rStar` gives the bound on `truncRadical` itself; see
`truncRadical_bounded` below. Monotonicity and the resulting limit are in
`Monotone.lean` / `Convergence.lean`.
-/

namespace RamanujanNested

/-- **Section 4.1, boundedness.** For any depth `d` and any coefficient function
`a` satisfying `a k ≤ A` pointwise, and any seed `T ∈ [0, r*]`, the truncated
radical `rollUp a T d` stays in `[0, r*]`. (See the file docstring for why no
lower bound on `a` is needed here.) -/
theorem rollUp_bounded {A T : ℝ} (hA : 0 ≤ A) (hT0 : 0 ≤ T) (hTA : T ≤ rStar A) :
    ∀ (d : ℕ) (a : ℕ → ℝ), (∀ k, a k ≤ A) →
      0 ≤ rollUp a T d ∧ rollUp a T d ≤ rStar A := by
  intro d
  induction d with
  | zero => intro a _; exact ⟨hT0, hTA⟩
  | succ n ih =>
    intro a ha_le
    have hshift_le : ∀ k, (fun k => a (k + 1)) k ≤ A := fun k => ha_le (k + 1)
    obtain ⟨hlo, hhi⟩ := ih (fun k => a (k + 1)) hshift_le
    have ha1_le : a 1 ≤ A := ha_le 1
    have hrStar_nonneg : 0 ≤ rStar A := rStar_nonneg hA
    set inner := rollUp (fun k => a (k + 1)) T n with hinner_def
    have hradicand_le : 1 + a 1 * inner ≤ (rStar A) ^ 2 := by
      have hmul : a 1 * inner ≤ A * rStar A :=
        mul_le_mul ha1_le hhi hlo hA
      have hsq := rStar_sq A
      linarith
    rw [rollUp_succ]
    refine ⟨Real.sqrt_nonneg _, ?_⟩
    calc Real.sqrt (1 + a 1 * inner)
        ≤ Real.sqrt ((rStar A) ^ 2) := Real.sqrt_le_sqrt hradicand_le
      _ = rStar A := Real.sqrt_sq hrStar_nonneg

/-- `r* ≥ 1` whenever `A ≥ 0` — needed to justify the canonical seed `T = 1`
sits inside `[0, r*]`. `rStar_sq` gives `r*² = 1 + A r* ≥ 1`, so `r* ≥ 1` since
`r* ≥ 0`. -/
theorem one_le_rStar {A : ℝ} (hA : 0 ≤ A) : 1 ≤ rStar A := by
  unfold rStar
  have h1 : (4 : ℝ) ≤ A ^ 2 + 4 := by nlinarith [sq_nonneg A]
  have h2 : Real.sqrt 4 ≤ Real.sqrt (A ^ 2 + 4) := Real.sqrt_le_sqrt h1
  have h3 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  linarith [h2, h3]

/-- Applying `rollUp_bounded` with the canonical seed `T = 1`: every truncation
`truncRadical a N` (the paper's `R_1^{(N)}`) lies in `[0, r*]`. -/
theorem truncRadical_bounded {A : ℝ} (hA : 0 ≤ A) (N : ℕ) (a : ℕ → ℝ)
    (ha_le : ∀ k, a k ≤ A) :
    0 ≤ truncRadical a N ∧ truncRadical a N ≤ rStar A :=
  rollUp_bounded hA (by norm_num) (one_le_rStar hA) N a ha_le

end RamanujanNested
