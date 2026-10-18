import RamanujanNested.Bounds

/-!
# ControlledNegative.lean — Lemma 1 (controlled negative coefficients)

Section 4.1's relaxation: coefficients may dip below zero, down to `-A₋`, as
long as `A₋ ≤ 2/(A+√(A²+4)) = 1/r*`. `Bounds.lean` already shows (see its file
docstring) that the *boundedness* conclusion `rollUp a T d ∈ [0, r*]` doesn't
actually need `a k ≥ 0` at all — it only needs `a k ≤ A`. So it already covers
Lemma 1's boundedness half for free, for ANY lower bound (or none).

The genuinely new content of Lemma 1 is realness: that the radicand fed into
`Real.sqrt` at every step is actually nonnegative, so the recursion is
"well defined in ℝ" in the meaningful sense — not just that `Real.sqrt`
(which is total and silently returns `0` on negative input in Lean/Mathlib)
happens to produce a bounded output regardless.
-/

namespace RamanujanNested

/-- **Lemma 1, the real content.** If `a 1 ≥ -A₋` and the inner value one layer
down is bounded by `r* = rStar A` (which holds unconditionally by
`rollUp_bounded`, given only `a k ≤ A`), and `A₋ ≤ 1/r*`, then the radicand
`1 + a 1 * inner` used to compute the next layer is nonnegative. This is
exactly the paper's claim: "the condition ensures that the radicand
`1 + a_k R_{k+1}` remains nonnegative for all admissible values of `R_{k+1}`
bounded by `r*`." -/
theorem rollUp_radicand_nonneg {A Aneg T : ℝ} (hA : 0 ≤ A) (hAneg : 0 ≤ Aneg)
    (hbound : Aneg ≤ 1 / rStar A) (hT0 : 0 ≤ T) (hTA : T ≤ rStar A) :
    ∀ (d : ℕ) (a : ℕ → ℝ), (∀ k, -Aneg ≤ a k) → (∀ k, a k ≤ A) →
      0 ≤ 1 + a 1 * rollUp (fun k => a (k + 1)) T d := by
  intro d a ha_lo ha_hi
  have hrStar_pos : 0 < rStar A := lt_of_lt_of_le one_pos (one_le_rStar hA)
  have hshift_le : ∀ k, (fun k => a (k + 1)) k ≤ A := fun k => ha_hi (k + 1)
  obtain ⟨hlo, hhi⟩ := rollUp_bounded hA hT0 hTA d (fun k => a (k + 1)) hshift_le
  set inner := rollUp (fun k => a (k + 1)) T d with hinner_def
  have ha1_lo : -Aneg ≤ a 1 := ha_lo 1
  have hne : rStar A ≠ 0 := ne_of_gt hrStar_pos
  have hAneg1 : Aneg * rStar A ≤ 1 := by
    have h1 : Aneg * rStar A ≤ (1 / rStar A) * rStar A :=
      mul_le_mul_of_nonneg_right hbound (le_of_lt hrStar_pos)
    have h2 : (1 / rStar A) * rStar A = 1 := one_div_mul_cancel hne
    linarith [h1, h2]
  have hworst : -Aneg * inner ≤ a 1 * inner := mul_le_mul_of_nonneg_right ha1_lo hlo
  have hAneginner : Aneg * inner ≤ Aneg * rStar A :=
    mul_le_mul_of_nonneg_left hhi hAneg
  nlinarith [hworst, hAneginner, hAneg1]

/-- Packaged together with `rollUp_bounded`: under Lemma 1's hypotheses, every
truncation is simultaneously (a) in `[0, r*]` and (b) built from a genuinely
nonnegative radicand at every step, i.e. the recursion is well-defined in ℝ
throughout, not merely bounded as a side effect of `Real.sqrt`'s totality. -/
theorem rollUp_controlled_negative {A Aneg T : ℝ} (hA : 0 ≤ A) (hAneg : 0 ≤ Aneg)
    (hbound : Aneg ≤ 1 / rStar A) (hT0 : 0 ≤ T) (hTA : T ≤ rStar A) :
    ∀ (d : ℕ) (a : ℕ → ℝ), (∀ k, -Aneg ≤ a k) → (∀ k, a k ≤ A) →
      (0 ≤ rollUp a T d ∧ rollUp a T d ≤ rStar A) ∧
      (0 ≤ 1 + a 1 * rollUp (fun k => a (k + 1)) T d) := by
  intro d a ha_lo ha_hi
  refine ⟨rollUp_bounded hA hT0 hTA d a ha_hi,
    rollUp_radicand_nonneg hA hAneg hbound hT0 hTA d a ha_lo ha_hi⟩

end RamanujanNested
