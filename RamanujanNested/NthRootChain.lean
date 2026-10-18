import RamanujanNested.Defs
import Mathlib

/-!
# NthRootChain.lean — Section 4.1 generalized from square roots to any root order n ≥ 2

`Defs.lean`/`Bounds.lean`/`Monotone.lean`/`Convergence.lean` are all specific to
`Real.sqrt` (root order 2). This file redoes that core result — bounded
coefficients ⟹ bounded, monotone, convergent truncated radical — for the
recursion `R_k = (1 + a_k·R_{k+1})^(1/n)` at ANY fixed root order `n ≥ 2`, for
ARBITRARY coefficient sequences `(a_k)` with `0 ≤ a_k ≤ A`.

This is a genuinely different axis of generalization from the rest of the
project (which generalizes the *coefficients*, staying at `n = 2`): here `n`
varies and the coefficient family is the simplest possible (bounded).

## Relation to the literature (Mitra, arXiv:2404.04051)

Mitra states a general n-th-root identity via a binomial-expansion argument
(his Section 1), but the actual convergence PROOF he gives (his Section 2,
"Polynomial Nature of Nested Cube Root") is carried out only for `n = 3`, for
one specific coefficient family tied to the binomial expansion of `(x+1)^n`.
This file proves boundedness, monotonicity and convergence for ANY `n ≥ 2`
and ANY bounded coefficient sequence `0 ≤ a_k ≤ A` — arbitrary root order
together with arbitrary bounded sequence, not one fixed family per `n`.

## A genuine difference in hypotheses from the `n = 2` case

`Bounds.lean` needs no lower bound on `a_k` at all, because `Real.sqrt` is
total and defaults to `0` on negative input. `Real.rpow` behaves differently
on a negative base, so nonnegativity of the radicand (hence of `a_k`) has to
be tracked explicitly here — this file assumes `0 ≤ a_k` throughout, matching
what the paper's Section 4.1 assumes anyway.

## A notation convention for `rpow`

Every `Real.rpow` term below is written with `^` notation (`x ^ (y : ℝ)`),
never as an explicit `Real.rpow x y` application. The two are defeq, but
`rw` matches syntactically: Mathlib's `rpow` lemmas (`Real.rpow_mul`,
`Real.rpow_one`, ...) are stated using `^`, so writing every term this way
from the start keeps them available to `rw` throughout.
-/

namespace RamanujanNested

/-- The n-th-root nested radical recursion, generalizing `rollUp` (`Defs.lean`,
which is exactly the case `n = 2` up to `Real.sqrt` vs `Real.rpow`). -/
noncomputable def rollUpN (n : ℕ) (a : ℕ → ℝ) (T : ℝ) : ℕ → ℝ
  | 0 => T
  | (k + 1) => (1 + a 1 * rollUpN n (fun j => a (j + 1)) T k) ^ (1 / (n : ℝ))

theorem rollUpN_succ (n : ℕ) (a : ℕ → ℝ) (T : ℝ) (k : ℕ) :
    rollUpN n a T (k + 1) =
      (1 + a 1 * rollUpN n (fun j => a (j + 1)) T k) ^ (1 / (n : ℝ)) := rfl

/-- Nonnegativity, standalone and reusable. Needed explicitly (unlike the
`n = 2` case) since `Real.rpow` is not automatically nonneg on a negative
base the way `Real.sqrt` is — see the file docstring. -/
theorem rollUpN_nonneg (n : ℕ) :
    ∀ (d : ℕ) (a : ℕ → ℝ) (T : ℝ), 0 ≤ T → (∀ k, 0 ≤ a k) → 0 ≤ rollUpN n a T d := by
  intro d
  induction d with
  | zero => intro a T hT _; exact hT
  | succ m ih =>
    intro a T hT ha
    rw [rollUpN_succ]
    have hinner := ih (fun k => a (k + 1)) T hT (fun k => ha (k + 1))
    have ha1 := ha 1
    have hradicand : 0 ≤ 1 + a 1 * rollUpN n (fun k => a (k + 1)) T m :=
      add_nonneg zero_le_one (mul_nonneg ha1 hinner)
    exact Real.rpow_nonneg hradicand _

/-- **Boundedness, general root order.** Given a ceiling `r` compatible with
`A` in the sense `(1+A*r)^(1/n) ≤ r`, every truncation of the n-th-root
radical (with `0 ≤ a_k ≤ A` and seed `T ∈ [0, r]`) stays in `[0, r]`. Stated
with the compatibility hypothesis directly in `rpow` form so the induction
itself never needs to convert between `rpow` and ordinary `pow` — that
conversion is confined to `exists_ceiling_rpow` below, where a concrete `r`
is produced. -/
theorem rollUpN_bounded {n : ℕ} {A r : ℝ} (hA : 0 ≤ A)
    (hceil : (1 + A * r) ^ (1 / (n : ℝ)) ≤ r) :
    ∀ (d : ℕ) (T : ℝ) (a : ℕ → ℝ), 0 ≤ T → T ≤ r → (∀ k, 0 ≤ a k) → (∀ k, a k ≤ A) →
      0 ≤ rollUpN n a T d ∧ rollUpN n a T d ≤ r := by
  intro d
  induction d with
  | zero => intro T _ hT0' hTr _ _; exact ⟨hT0', hTr⟩
  | succ m ih =>
    intro T a hT0' hTr ha_nonneg ha_le
    have hshift_nonneg : ∀ k, 0 ≤ (fun k => a (k + 1)) k := fun k => ha_nonneg (k + 1)
    have hshift_le : ∀ k, (fun k => a (k + 1)) k ≤ A := fun k => ha_le (k + 1)
    obtain ⟨hlo, hhi⟩ := ih T (fun k => a (k + 1)) hT0' hTr hshift_nonneg hshift_le
    have ha1_nonneg : 0 ≤ a 1 := ha_nonneg 1
    have ha1_le : a 1 ≤ A := ha_le 1
    set inner := rollUpN n (fun k => a (k + 1)) T m with hinner_def
    have hradicand_nonneg : 0 ≤ 1 + a 1 * inner :=
      add_nonneg zero_le_one (mul_nonneg ha1_nonneg hlo)
    have hradicand_le : 1 + a 1 * inner ≤ 1 + A * r := by
      have hmul : a 1 * inner ≤ A * r := mul_le_mul ha1_le hhi hlo hA
      linarith
    rw [rollUpN_succ]
    refine ⟨Real.rpow_nonneg hradicand_nonneg _, ?_⟩
    calc (1 + a 1 * inner) ^ (1 / (n : ℝ))
        ≤ (1 + A * r) ^ (1 / (n : ℝ)) :=
          Real.rpow_le_rpow hradicand_nonneg hradicand_le (by positivity)
      _ ≤ r := hceil

/-- **A concrete compatible ceiling always exists**, for any `n ≥ 2` and
`A ≥ 0`: `r = A + 2` works. The one place this file converts between `rpow`
and ordinary `pow`: `(r^n)^(1/n) = r` for `r ≥ 0` (`Real.rpow_natCast` +
`Real.rpow_mul` + `Real.rpow_one`), combined with the elementary polynomial
bound `(A+2)^n ≥ (A+2)^2 ≥ A(A+2)+1` (the first step since `A+2 ≥ 1` and
`n ≥ 2`, the second by direct expansion). -/
theorem exists_ceiling_rpow {n : ℕ} (hn : 2 ≤ n) {A : ℝ} (hA : 0 ≤ A) :
    ∃ r : ℝ, 0 ≤ r ∧ 1 ≤ r ∧ (1 + A * r) ^ (1 / (n : ℝ)) ≤ r := by
  refine ⟨A + 2, by linarith, by linarith, ?_⟩
  have hr_nonneg : (0:ℝ) ≤ A + 2 := by linarith
  have hpow_ge_sq : (A + 2) ^ 2 ≤ (A + 2) ^ n := by
    have hbase : (1:ℝ) ≤ A + 2 := by linarith
    exact pow_le_pow_right₀ hbase hn
  have hpoly : 1 + A * (A + 2) ≤ (A + 2) ^ n := by nlinarith [hpow_ge_sq]
  have hn_ne : (n : ℝ) ≠ 0 := by
    have hpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    linarith
  have hrpow_eq : ((A + 2) ^ n : ℝ) ^ (1 / (n : ℝ)) = A + 2 := by
    rw [← Real.rpow_natCast (A + 2) n, ← Real.rpow_mul hr_nonneg, mul_one_div,
      div_self hn_ne, Real.rpow_one]
  calc (1 + A * (A + 2)) ^ (1 / (n : ℝ))
      ≤ ((A + 2) ^ n : ℝ) ^ (1 / (n : ℝ)) :=
        Real.rpow_le_rpow (by positivity) hpoly (by positivity)
    _ = A + 2 := hrpow_eq

/-- Specialized to the canonical seed `T = 1`. -/
theorem truncRadicalN_bounded {n : ℕ} (hn : 2 ≤ n) {A : ℝ} (hA : 0 ≤ A)
    (a : ℕ → ℝ) (ha_nonneg : ∀ k, 0 ≤ a k) (ha_le : ∀ k, a k ≤ A) (d : ℕ) :
    ∃ r : ℝ, 0 ≤ rollUpN n a 1 d ∧ rollUpN n a 1 d ≤ r := by
  obtain ⟨r, _, hr1, hceil⟩ := exists_ceiling_rpow hn hA
  exact ⟨r, rollUpN_bounded hA hceil d 1 a (by norm_num) hr1 ha_nonneg ha_le⟩

/-- **Monotonicity, general root order.** Adding one more layer never decreases
the value (canonical seed `1`), provided every coefficient is nonnegative —
same structure as `rollUp_seed_one_step_mono` (`Monotone.lean`), with
`Real.rpow_le_rpow` in place of `Real.sqrt_le_sqrt` and `Real.one_rpow` in
place of `Real.sqrt_one`. -/
theorem rollUpN_seed_one_step_mono (n : ℕ) :
    ∀ (N : ℕ) (a : ℕ → ℝ), (∀ k, 0 ≤ a k) →
      rollUpN n a 1 N ≤ rollUpN n a 1 (N + 1) := by
  intro N
  induction N with
  | zero =>
    intro a ha
    rw [rollUpN_succ]
    have h1 : rollUpN n (fun k => a (k + 1)) 1 0 = (1 : ℝ) := rfl
    rw [h1]
    have ha1 : 0 ≤ a 1 := ha 1
    have hle : (1:ℝ) ≤ 1 + a 1 * 1 := by nlinarith
    calc (1:ℝ) = (1:ℝ) ^ (1 / (n:ℝ)) := (Real.one_rpow _).symm
      _ ≤ (1 + a 1 * 1) ^ (1 / (n:ℝ)) :=
          Real.rpow_le_rpow (by norm_num) hle (by positivity)
  | succ m ih =>
    intro a ha
    have ha_shift : ∀ k, 0 ≤ (fun k => a (k + 1)) k := fun k => ha (k + 1)
    have ih_shift := ih (fun k => a (k + 1)) ha_shift
    rw [rollUpN_succ, rollUpN_succ]
    have ha1 : 0 ≤ a 1 := ha 1
    have hstep : 1 + a 1 * rollUpN n (fun k => a (k + 1)) 1 m ≤
        1 + a 1 * rollUpN n (fun k => a (k + 1)) 1 (m + 1) := by
      have := mul_le_mul_of_nonneg_left ih_shift ha1
      linarith
    have hinner_nonneg : 0 ≤ rollUpN n (fun k => a (k + 1)) 1 m :=
      rollUpN_nonneg n m (fun k => a (k + 1)) 1 zero_le_one ha_shift
    have hradicand_nonneg : (0:ℝ) ≤ 1 + a 1 * rollUpN n (fun k => a (k + 1)) 1 m :=
      add_nonneg zero_le_one (mul_nonneg ha1 hinner_nonneg)
    exact Real.rpow_le_rpow hradicand_nonneg hstep (by positivity)

/-- `rollUpN n a 1` is monotone in the truncation depth, for nonnegative
coefficients — the monotonicity half for general root order `n`. -/
theorem truncRadicalN_monotone (n : ℕ) (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) :
    Monotone (fun N => rollUpN n a 1 N) := by
  apply monotone_nat_of_le_succ
  intro N
  exact rollUpN_seed_one_step_mono n N a ha

open Filter Topology

/-- **Convergence, general root order.** For any root order `n ≥ 2` and any
coefficient sequence with `0 ≤ a_k ≤ A`, the n-th-root truncated radical
(canonical seed `1`) converges to a finite real limit as depth `→ ∞` — the
`n = 2` conclusion of `Convergence.lean`, generalized to arbitrary `n`. -/
theorem truncRadicalN_converges {n : ℕ} (hn : 2 ≤ n) {A : ℝ} (hA : 0 ≤ A)
    (a : ℕ → ℝ) (ha_nonneg : ∀ k, 0 ≤ a k) (ha_le : ∀ k, a k ≤ A) :
    ∃ L : ℝ, Tendsto (fun N => rollUpN n a 1 N) atTop (𝓝 L) := by
  obtain ⟨r, _, hr1, hceil⟩ := exists_ceiling_rpow hn hA
  have hmono : Monotone (fun N => rollUpN n a 1 N) := truncRadicalN_monotone n a ha_nonneg
  have hbdd : BddAbove (Set.range (fun N => rollUpN n a 1 N)) := by
    refine ⟨r, ?_⟩
    rintro x ⟨N, rfl⟩
    exact (rollUpN_bounded hA hceil N 1 a (by norm_num) hr1 ha_nonneg ha_le).2
  exact ⟨⨆ i, rollUpN n a 1 i, tendsto_atTop_ciSup hmono hbdd⟩

end RamanujanNested
