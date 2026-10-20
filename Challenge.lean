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

1. `Submission.truncRadical_classical_tendsto` (the classical family, square roots): for real
   `N ≥ 2` and `aₖ = N + k - 2` the truncations converge to exactly `N`. For `N = 3` this is
   Ramanujan's radical. This statement is known mathematically (Ramanujan's Entry 4 in Berndt's
   edition, `f(x) = x + 1`); it is included as the base case that the next results extend.
2. `Submission.truncRadicalNS_tendsto` (the classical family, any root order `n ≥ 2`): for the
   coefficients `aₖ = altSum n (N + k - 1)` and the signed radicand `(-1)ⁿ + aₖ · R_{k+1}`, the
   truncations converge to exactly `N`, for even and odd `n` alike. The sign `(-1)ⁿ` is the only
   place where the parity of `n` enters.
3. `Submission.rollUpN_profile_gap` and `Submission.rollUpN_profile_tendsto` (arbitrary profile,
   any root order `n ≥ 2`): if `R k ≥ 1` for `k ≥ 1` and the coefficients are the ones making
   `R` satisfy the recursion exactly, `R_kⁿ = 1 + a_k · R_{k+1}`, then the depth-`d` truncation
   with seed `1` is within `R₁ · ∏_{j<d} (1 - 1/R_j)` of `R₁` (from below), and it converges to
   exactly `R₁` whenever `∑ 1/R_k` diverges. The profile `R_k = N + k - 1` with even `n` (in
   particular the classical family with `n = 2`) and every constant profile `R_k = t` are special
   cases.

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

/-! ## Results -/

/-- **The classical unbounded family, square roots.** For real `N ≥ 2` and `aₖ = N + k - 2`, the
truncated radicals converge to exactly `N`. -/
public theorem Submission.truncRadical_classical_tendsto {N : ℝ} (hN : 2 ≤ N) :
    Filter.Tendsto (Submission.truncRadical (Submission.classicalCoeff N)) Filter.atTop
      (nhds N) := by
  sorry

/-- **The classical unbounded family, any root order.** For every `n ≥ 2` (even or odd) and
real `N ≥ 2`, the truncated radicals of the family `aₖ = altSum n (N + k - 1)` converge to
exactly `N`. -/
public theorem Submission.truncRadicalNS_tendsto {n : ℕ} (hn : 2 ≤ n) {N : ℝ} (hN : 2 ≤ N) :
    Filter.Tendsto (Submission.truncRadicalNS n N) Filter.atTop (nhds N) := by
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
