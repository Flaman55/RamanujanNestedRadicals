module

public import RamanujanNested

/-!
# Proved solutions

This module defines exactly the same objects as `Challenge.lean` and proves each advertised
statement. The proofs are thin wrappers around the development in `RamanujanNested/`: each
definition given here is shown equal to its counterpart in the `RamanujanNested` namespace, and
the statements follow from
`RamanujanNested.limitVal_tendsto` with `RamanujanNested.limitVal_eq_self`,
`RamanujanNested.limitValNS_tendsto` with `RamanujanNested.limitValNS_eq_self_even` and
`RamanujanNested.limitValNS_eq_self_odd`, and `RamanujanNested.rollUpN_profile_gap` /
`RamanujanNested.rollUpN_profile_tendsto`.
-/

/-! ## Definitions (verbatim from `Challenge.lean`) -/

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

/-! ## Bridges to the `RamanujanNested` development -/

private theorem rollUp_eq (a : ℕ → ℝ) (T : ℝ) (d : ℕ) :
    Submission.rollUp a T d = RamanujanNested.rollUp a T d := by
  induction d generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [Submission.rollUp_succ, RamanujanNested.rollUp_succ, ih]

private theorem truncRadical_eq (a : ℕ → ℝ) :
    Submission.truncRadical a = RamanujanNested.truncRadical a := by
  funext N
  exact rollUp_eq a 1 N

private theorem classicalCoeff_eq :
    Submission.classicalCoeff = RamanujanNested.classicalCoeff := rfl

private theorem rollUpN_eq (n : ℕ) (a : ℕ → ℝ) (T : ℝ) (d : ℕ) :
    Submission.rollUpN n a T d = RamanujanNested.rollUpN n a T d := by
  induction d generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [Submission.rollUpN_succ, RamanujanNested.rollUpN_succ, ih]

private theorem altSum_eq : Submission.altSum = RamanujanNested.altSum := rfl

private theorem altCoeffR_eq : Submission.altCoeffR = RamanujanNested.altCoeffR := rfl

private theorem rollUpNS_eq (n : ℕ) (a : ℕ → ℝ) (T : ℝ) (d : ℕ) :
    Submission.rollUpNS n a T d = RamanujanNested.rollUpNS n a T d := by
  induction d generalizing a with
  | zero => rfl
  | succ k ih =>
    rw [Submission.rollUpNS_succ, RamanujanNested.rollUpNS_succ, ih]

private theorem truncRadicalNS_eq (n : ℕ) (N : ℝ) :
    Submission.truncRadicalNS n N = RamanujanNested.truncRadicalNS n N := by
  funext d
  exact rollUpNS_eq n (Submission.altCoeffR n N) 1 d

/-! ## Results -/

public theorem Submission.truncRadical_classical_tendsto {N : ℝ} (hN : 2 ≤ N) :
    Filter.Tendsto (Submission.truncRadical (Submission.classicalCoeff N)) Filter.atTop
      (nhds N) := by
  rw [truncRadical_eq, classicalCoeff_eq]
  have h := RamanujanNested.limitVal_tendsto hN
  rw [RamanujanNested.limitVal_eq_self hN] at h
  exact h

public theorem Submission.truncRadicalNS_tendsto {n : ℕ} (hn : 2 ≤ n) {N : ℝ} (hN : 2 ≤ N) :
    Filter.Tendsto (Submission.truncRadicalNS n N) Filter.atTop (nhds N) := by
  rw [truncRadicalNS_eq]
  have h := RamanujanNested.limitValNS_tendsto hn hN
  rcases Nat.even_or_odd n with he | ho
  · rw [RamanujanNested.limitValNS_eq_self_even hn he hN] at h
    exact h
  · rw [RamanujanNested.limitValNS_eq_self_odd hn ho hN] at h
    exact h

public theorem Submission.rollUpN_profile_gap {n : ℕ} (hn : 2 ≤ n) (d : ℕ) (a R : ℕ → ℝ)
    (hR : ∀ k, 1 ≤ R (k + 1))
    (ha : ∀ k, R (k + 1) ^ n = 1 + a (k + 1) * R (k + 2)) :
    0 ≤ R 1 - Submission.rollUpN n a 1 d ∧
      R 1 - Submission.rollUpN n a 1 d ≤
        R 1 * ∏ j ∈ Finset.range d, (1 - 1 / R (j + 1)) := by
  rw [rollUpN_eq]
  obtain ⟨_, h0, h1⟩ := RamanujanNested.rollUpN_profile_gap (by omega) d a R hR ha
  exact ⟨h0, h1⟩

public theorem Submission.rollUpN_profile_tendsto {n : ℕ} (hn : 2 ≤ n) (a R : ℕ → ℝ)
    (hR : ∀ k, 1 ≤ R (k + 1))
    (ha : ∀ k, R (k + 1) ^ n = 1 + a (k + 1) * R (k + 2))
    (hdiv : ¬ Summable (fun k => 1 / R (k + 1))) :
    Filter.Tendsto (fun d => Submission.rollUpN n a 1 d) Filter.atTop (nhds (R 1)) := by
  simp only [rollUpN_eq]
  exact RamanujanNested.rollUpN_profile_tendsto (by omega) a R hR ha hdiv
