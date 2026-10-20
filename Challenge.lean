module

public import Mathlib

/-!
# Advertised statements

This file is the small, trusted surface a mathematical reader should audit. It imports only
Mathlib and states the main results of the accompanying paper *Nested Radicals of Ramanujan's
Type with Arbitrary Coefficient Sequences* (Flamandzki, 2026).

## Setting

For a coefficient sequence `a : ℕ → ℝ` and a seed `T`, the nested radical of depth `d` is built
from the inside out by the recursion

  `R_k = √(1 + a_k · R_{k+1})`,

and `Submission.rollUp a T d` is the depth-`d` truncation with seed `T`
(`Submission.truncRadical a d` uses the seed `1`). For a root order `n ≥ 2` the corresponding
radicals are `Submission.rollUpN` (radicand `1 + a_k · R_{k+1}`, `n`-th root) and, for the
classical unbounded family, `Submission.rollUpNS` (radicand `(-1)ⁿ + a_k · R_{k+1}`, with the
coefficients `Submission.altCoeffR n N k = altSum n (N + k - 1)`, where `altSum n x` is the
alternating polynomial `x^(n-1) - x^(n-2) + ⋯ ± 1`).

## Results

1. `Submission.truncRadical_converges` (bounded coefficients): if `0 ≤ aₖ ≤ A` then the
   truncations converge.
2. `Submission.truncRadical_classical_tendsto` (the classical family): for real `N ≥ 2` and
   `aₖ = N + k - 2` the truncations converge to exactly `N`. For `N = 3` this is Ramanujan's
   radical.
3. `Submission.altSum_identity` and `Submission.chainS_satisfies_recursion` (closed form,
   any root order `n ≥ 2`): `R_k = N + k - 1` satisfies the recursion exactly, for even and odd
   `n` alike.
4. `Submission.truncRadicalNS_tendsto` (the classical family, any root order `n ≥ 2`): the
   truncations converge to exactly `N`, for even and odd `n` alike.
5. `Submission.targetCoeffN_rpow_fixed`, `Submission.targetRadicalN_gap_geometric` and
   `Submission.targetRadicalN_tendsto` (prescribed target, any root order `n ≥ 2`): the constant
   coefficient `(tⁿ - 1)/t` makes the `n`-th-root radical converge to an arbitrary prescribed
   `t ≥ 1`, from any seed `0 ≤ T ≤ t`, with an explicit geometric rate.

6. `Submission.rollUpN_profile_gap` and `Submission.rollUpN_profile_tendsto` (arbitrary profile,
   any root order `n ≥ 2`): if `R k ≥ 1` for `k ≥ 1` and the coefficients are the ones making
   `R` satisfy the recursion exactly, `R_kⁿ = 1 + a_k · R_{k+1}`, then the depth-`d` truncation
   with seed `1` is within `R₁ · ∏_{j<d} (1 - 1/R_j)` of `R₁` (from below), and it converges to
   exactly `R₁` whenever `∑ 1/R_k` diverges. The constant profile `R_k = t` and the profile
   `R_k = N + k - 1` (for `n = 2`, the classical family) are special cases.

No definition is left unspecified: all objects are defined here, and the Solution file defines
them verbatim and proves every theorem.
-/

/-! ## Definitions -/

/-- The depth-`d` square-root nested radical `√(1 + a₁ √(1 + a₂ √(⋯ √(1 + a_d · T))))` with
seed `T` in the innermost position. -/
@[expose] public noncomputable def Submission.rollUp (a : ℕ → ℝ) (T : ℝ) : ℕ → ℝ
  | 0 => T
  | (n + 1) => Real.sqrt (1 + a 1 * Submission.rollUp (fun k => a (k + 1)) T n)

/-- Unfolding lemma for `Submission.rollUp`. -/
public theorem Submission.rollUp_succ (a : ℕ → ℝ) (T : ℝ) (n : ℕ) :
    Submission.rollUp a T (n + 1) =
      Real.sqrt (1 + a 1 * Submission.rollUp (fun k => a (k + 1)) T n) := rfl

/-- The truncated radical `R₁^{(N)}` with the canonical seed `1`. -/
@[expose] public noncomputable def Submission.truncRadical (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  Submission.rollUp a 1 N

/-- The classical coefficient family `aₖ = N + k - 2`. -/
@[expose] public noncomputable def Submission.classicalCoeff (N : ℝ) (k : ℕ) : ℝ :=
  N + (k : ℝ) - 2

/-- The `n`-th-root nested radical `(1 + a₁ (1 + a₂ (⋯)^{1/n})^{1/n})^{1/n}` with seed `T`. -/
@[expose] public noncomputable def Submission.rollUpN (n : ℕ) (a : ℕ → ℝ) (T : ℝ) : ℕ → ℝ
  | 0 => T
  | (k + 1) => (1 + a 1 * Submission.rollUpN n (fun j => a (j + 1)) T k) ^ (1 / (n : ℝ))

/-- Unfolding lemma for `Submission.rollUpN`. -/
public theorem Submission.rollUpN_succ (n : ℕ) (a : ℕ → ℝ) (T : ℝ) (k : ℕ) :
    Submission.rollUpN n a T (k + 1) =
      (1 + a 1 * Submission.rollUpN n (fun j => a (j + 1)) T k) ^ (1 / (n : ℝ)) := rfl

/-- The constant coefficient whose `n`-th-root fixed point is exactly `t`. -/
@[expose] public noncomputable def Submission.targetCoeffN (n : ℕ) (t : ℝ) : ℝ :=
  (t ^ n - 1) / t

/-- The alternating-sign polynomial `x^{n-1} - x^{n-2} + ⋯ ± 1`. -/
@[expose] public noncomputable def Submission.altSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, x ^ i * (-1 : ℝ) ^ (n - 1 - i)

/-- The coefficient family `aₖ = altSum n (N + k - 1)` for real `N`. -/
@[expose] public noncomputable def Submission.altCoeffR (n : ℕ) (N : ℝ) (k : ℕ) : ℝ :=
  Submission.altSum n (N + (k : ℝ) - 1)

/-- The signed `n`-th-root nested radical, with `(-1)ⁿ` in place of the fixed `1`. -/
@[expose] public noncomputable def Submission.rollUpNS (n : ℕ) (a : ℕ → ℝ) (T : ℝ) : ℕ → ℝ
  | 0 => T
  | (k + 1) => ((-1 : ℝ) ^ n + a 1 * Submission.rollUpNS n (fun j => a (j + 1)) T k) ^
      (1 / (n : ℝ))

/-- Unfolding lemma for `Submission.rollUpNS`. -/
public theorem Submission.rollUpNS_succ (n : ℕ) (a : ℕ → ℝ) (T : ℝ) (k : ℕ) :
    Submission.rollUpNS n a T (k + 1) =
      ((-1 : ℝ) ^ n + a 1 * Submission.rollUpNS n (fun j => a (j + 1)) T k) ^
        (1 / (n : ℝ)) := rfl

/-- The truncated radical `R₁^{(N)}` of the signed family, with the canonical seed `1`. -/
@[expose] public noncomputable def Submission.truncRadicalNS (n : ℕ) (N : ℝ) (d : ℕ) : ℝ :=
  Submission.rollUpNS n (Submission.altCoeffR n N) 1 d

/-- The closed form `R_k = N + k - 1`. -/
@[expose] public noncomputable def Submission.chainClosedFormS (N k : ℕ) : ℝ :=
  (N : ℝ) + (k : ℝ) - 1

/-! ## Results -/

/-- **Convergence for bounded coefficients.** If `0 ≤ aₖ ≤ A` for all `k`, the truncated radicals
converge to a finite limit. -/
public theorem Submission.truncRadical_converges {A : ℝ} (hA : 0 ≤ A) (a : ℕ → ℝ)
    (ha_nonneg : ∀ k, 0 ≤ a k) (ha_le : ∀ k, a k ≤ A) :
    ∃ L : ℝ, Filter.Tendsto (Submission.truncRadical a) Filter.atTop (nhds L) := by
  sorry

/-- **The classical unbounded family, square roots.** For real `N ≥ 2` and `aₖ = N + k - 2`, the
truncated radicals converge to exactly `N`. -/
public theorem Submission.truncRadical_classical_tendsto {N : ℝ} (hN : 2 ≤ N) :
    Filter.Tendsto (Submission.truncRadical (Submission.classicalCoeff N)) Filter.atTop
      (nhds N) := by
  sorry

/-- **The unifying identity.** `altSum n x · (x + 1) = xⁿ - (-1)ⁿ`. -/
public theorem Submission.altSum_identity (n : ℕ) (x : ℝ) :
    Submission.altSum n x * (x + 1) = x ^ n - (-1 : ℝ) ^ n := by
  sorry

/-- **The identity chain, any root order `n ≥ 2`.** The closed form `R_k = N + k - 1` satisfies
`R_k = ((-1)ⁿ + altSum n R_k · R_{k+1})^{1/n}` exactly, for even and odd `n` alike. -/
public theorem Submission.chainS_satisfies_recursion {n : ℕ} (hn : 2 ≤ n) (N k : ℕ)
    (hN : 2 ≤ N) :
    Submission.chainClosedFormS N k =
      ((-1 : ℝ) ^ n + Submission.altSum n (Submission.chainClosedFormS N k) *
        Submission.chainClosedFormS N (k + 1)) ^ (1 / (n : ℝ)) := by
  sorry

/-- **The classical unbounded family, any root order.** For every `n ≥ 2` (even or odd) and
real `N ≥ 2`, the truncated radicals of the family `aₖ = altSum n (N + k - 1)` converge to
exactly `N`. -/
public theorem Submission.truncRadicalNS_tendsto {n : ℕ} (hn : 2 ≤ n) {N : ℝ} (hN : 2 ≤ N) :
    Filter.Tendsto (Submission.truncRadicalNS n N) Filter.atTop (nhds N) := by
  sorry

/-- **Fixed point of the target coefficient.** For `t ≥ 1` and `n ≥ 2`,
`(1 + targetCoeffN n t · t)^{1/n} = t`. -/
public theorem Submission.targetCoeffN_rpow_fixed {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 1 ≤ t) :
    (1 + Submission.targetCoeffN n t * t) ^ (1 / (n : ℝ)) = t := by
  sorry

/-- **Geometric rate.** For `t ≥ 1`, `n ≥ 2` and a seed `0 ≤ T ≤ t`, the gap between the target
and the depth-`d` radical with constant coefficient `targetCoeffN n t` is at most
`(targetCoeffN n t / t^(n-1))^d · (t - T)`. -/
public theorem Submission.targetRadicalN_gap_geometric {n : ℕ} (hn : 2 ≤ n) {t T : ℝ}
    (ht : 1 ≤ t) (hT0 : 0 ≤ T) (hTt : T ≤ t) :
    ∀ d : ℕ, t - Submission.rollUpN n (fun _ => Submission.targetCoeffN n t) T d ≤
      (Submission.targetCoeffN n t / t ^ (n - 1)) ^ d * (t - T) := by
  sorry

/-- **Convergence to a prescribed target.** For `t ≥ 1`, `n ≥ 2` and any seed `0 ≤ T ≤ t`, the
radicals with constant coefficient `targetCoeffN n t` converge to exactly `t`. -/
public theorem Submission.targetRadicalN_tendsto {n : ℕ} (hn : 2 ≤ n) {t T : ℝ} (ht : 1 ≤ t)
    (hT0 : 0 ≤ T) (hTt : T ≤ t) :
    Filter.Tendsto (fun d => Submission.rollUpN n (fun _ => Submission.targetCoeffN n t) T d)
      Filter.atTop (nhds t) := by
  sorry

/-- **Explicit gap bound for a profile.** Let `n ≥ 2` and let `R` satisfy `R k ≥ 1` for `k ≥ 1`
and `R_kⁿ = 1 + a_k · R_{k+1}` for `k ≥ 1`. Then the depth-`d` truncation with seed `1` lies below
`R₁`, and `R₁ - rollUpN n a 1 d ≤ R₁ · ∏_{j<d} (1 - 1/R_{j+1})`. -/
public theorem Submission.rollUpN_profile_gap {n : ℕ} (hn : 2 ≤ n) (d : ℕ) (a R : ℕ → ℝ)
    (hR : ∀ k, 1 ≤ R (k + 1))
    (ha : ∀ k, R (k + 1) ^ n = 1 + a (k + 1) * R (k + 2)) :
    0 ≤ R 1 - Submission.rollUpN n a 1 d ∧
      R 1 - Submission.rollUpN n a 1 d ≤
        R 1 * ∏ j ∈ Finset.range d, (1 - 1 / R (j + 1)) := by
  sorry

/-- **Exact value for a profile with divergent `∑ 1/R_k`.** Under the hypotheses of
`Submission.rollUpN_profile_gap`, if `∑ 1/R_k` diverges then the truncations converge to
exactly `R₁`. -/
public theorem Submission.rollUpN_profile_tendsto {n : ℕ} (hn : 2 ≤ n) (a R : ℕ → ℝ)
    (hR : ∀ k, 1 ≤ R (k + 1))
    (ha : ∀ k, R (k + 1) ^ n = 1 + a (k + 1) * R (k + 2))
    (hdiv : ¬ Summable (fun k => 1 / R (k + 1))) :
    Filter.Tendsto (fun d => Submission.rollUpN n a 1 d) Filter.atTop (nhds (R 1)) := by
  sorry
