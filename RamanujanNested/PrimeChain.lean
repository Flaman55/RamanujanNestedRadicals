import RamanujanNested.Bounds
import RamanujanNested.Monotone
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting

/-!
# PrimeChain.lean — existence of a limit for the prime-coefficient radical

The paper's Appendix A.2 example, `a_k = p_k` (the `k`-th prime), is the one
case left genuinely unformalized by `UnboundedChain.lean` /
`HerschfeldClosure.lean`: those files close the `a_k = N+k-2` family exactly,
using an algebraic self-similarity (shifting the sequence by one shifts `N`
by one) that primes simply do not have. This file does NOT attempt the exact
value — it establishes a much weaker, but still new, claim: the truncated
radical for `a_k = p_k` has SOME finite limit as depth `→ ∞`.

## Strategy

`Bounds.lean`'s fixed-ceiling argument needs `a_k ≤ A` for one constant `A`,
which fails for any unbounded sequence. But primes only grow *slowly*
(`p_k ~ k log k`), far below the doubly-exponential growth classically known
to still permit convergence (Herschfeld's original criterion for infinite
nested radicals). Rather than reprove that general criterion, this file
proves a self-contained special case sufficient for primes: a *geometric*
growth bound `a_k ≤ r^k` (any fixed `r > 1`) already gives a genuine, depth-
independent ceiling on the truncated radical (`rollUp_geomBounded`), via a
moving ceiling `A·r^i` that shrinks back to a FIXED constant `A·r^0 = A` at
the top level — no delicate limiting argument needed, unlike
`HerschfeldClosure.lean`.

Primes satisfy `p_k ≤ 4^k` (in fact much less), and that bound itself follows
from Bertrand's postulate: each prime is less than twice the previous one, so
doubling is dominated by base-4 growth with room to spare
(`nth_prime_le_four_pow`). This file uses Mathlib's own Bertrand
(`Nat.exists_prime_lt_and_le_two_mul`, alias `Nat.bertrand`) rather than the
independently-verified `StructuralBertrand.bertrand_chebyshev` (same
statement, from a separate project) purely to avoid a cross-project Lean
dependency; swapping one for the other is a one-line change if the two
projects are later linked.

## Status

No `sorry`: `nth_prime_le_four_pow`, `rollUp_geomBounded` (the general
geometric moving-ceiling bound), and `primeRadical_converges` (the
existence result) are all proved in full.
-/

namespace RamanujanNested

open Filter Topology

/-! ## Step 1: a crude growth bound on the primes, from Bertrand's postulate -/

/-- The `n`-th prime (Mathlib's `Nat.nth Nat.Prime`, 0-indexed: `nth Prime 0 = 2`)
is at most `4^(n+1)`. Proved by induction using Bertrand's postulate: each
prime is less than twice the previous one, and `2 * 4^(n+1) ≤ 4^(n+2)` with
room to spare. -/
theorem nth_prime_le_four_pow : ∀ n : ℕ, Nat.nth Nat.Prime n ≤ 4 ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
    rw [Nat.nth_prime_zero_eq_two]
    norm_num
  | succ n ih =>
    have hprime_n : Nat.Prime (Nat.nth Nat.Prime n) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
    have hpos : Nat.nth Nat.Prime n ≠ 0 := hprime_n.pos.ne'
    obtain ⟨q, hq_prime, hq_lt, hq_le⟩ :=
      Nat.exists_prime_lt_and_le_two_mul (Nat.nth Nat.Prime n) hpos
    have hle1 : Nat.nth Nat.Prime n + 1 ≤ q := by omega
    have hcount : Nat.count Nat.Prime (Nat.nth Nat.Prime n + 1) ≤ Nat.count Nat.Prime q :=
      Nat.count_monotone Nat.Prime hle1
    rw [Nat.count_nth_succ_of_infinite Nat.infinite_setOf_prime n] at hcount
    have hnth_le : Nat.nth Nat.Prime (n + 1) ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime q) :=
      Nat.nth_monotone Nat.infinite_setOf_prime hcount
    rw [Nat.nth_count hq_prime] at hnth_le
    calc Nat.nth Nat.Prime (n + 1) ≤ q := hnth_le
      _ ≤ 2 * Nat.nth Nat.Prime n := hq_le
      _ ≤ 2 * 4 ^ (n + 1) := by nlinarith [ih]
      _ ≤ 4 ^ (n + 2) := by
            have h4 : (4 : ℕ) ^ (n + 2) = 4 ^ (n + 1) * 4 := pow_succ 4 (n + 1)
            nlinarith [h4]

/-! ## Step 2: the coefficient sequence itself -/

/-- The paper's Appendix A.2 example, `a_k = p_k`: the `k`-th prime, 1-indexed
to match the paper's convention (`primeCoeff 1 = 2`, `primeCoeff 2 = 3`,
`primeCoeff 3 = 5`, ...). Index `0` is a dummy — `rollUp`/`truncRadical` never
read `a 0` — set to `0` so it doesn't interfere with the global growth bound
below. -/
noncomputable def primeCoeff (k : ℕ) : ℝ :=
  if k = 0 then 0 else (Nat.nth Nat.Prime (k - 1) : ℝ)

theorem primeCoeff_nonneg (k : ℕ) : 0 ≤ primeCoeff k := by
  unfold primeCoeff
  split
  · norm_num
  · exact Nat.cast_nonneg _

/-- Global growth bound: `primeCoeff k ≤ 4^k` for every `k`, including the
dummy `k = 0` case (`0 ≤ 4^0 = 1`). -/
theorem primeCoeff_le_pow (k : ℕ) : primeCoeff k ≤ (4 : ℝ) ^ k := by
  unfold primeCoeff
  split
  · positivity
  · rename_i hk
    have hbound : Nat.nth Nat.Prime (k - 1) ≤ 4 ^ ((k - 1) + 1) := nth_prime_le_four_pow (k - 1)
    have hk1 : (k - 1) + 1 = k := by omega
    rw [hk1] at hbound
    exact_mod_cast hbound

/-- Elementary fact, proved from scratch (no dependency on a specific
Mathlib `one_le_pow`-style lemma name): for `r > 1`, `r^n ≥ 1` for every `n`. -/
theorem one_le_pow_of_one_lt {r : ℝ} (hr : 1 < r) : ∀ n : ℕ, (1 : ℝ) ≤ r ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ j ihj =>
      rw [pow_succ]
      have hstep := mul_le_mul_of_nonneg_right ihj (by linarith : (0 : ℝ) ≤ r)
      linarith [hstep]

/-! ## Step 3: a general moving-ceiling bound for geometrically-growing
coefficients -/

/-- **Geometric moving-ceiling boundedness.** Generalizes `Bounds.lean`'s
FIXED ceiling to coefficients that grow geometrically instead of staying
below a constant. If `b k ≤ r^(i+k)` for all `k` (the "shifted by `i`" growth
bound), `r > 1`, `A ≥ 0`, and `A` is large enough relative to `r`
(`1 ≤ A*(A - r^2)`), then `rollUp b T d ≤ A * r^i` — a bound that does NOT
grow with the truncation depth `d`, only with the starting shift `i`.
Quantifying `i` (and hence the coefficient function `b`) inside the induction
is the same device `UnboundedChain.lean` uses for the linear family; here the
moving ceiling is `A*r^i` rather than `N+1`, and — unlike that file — it
closes to a genuine fixed constant `A*r^0 = A` at the top level `i = 0`. -/
theorem rollUp_geomBounded {r A : ℝ} (hr : 1 < r) (hA : 0 ≤ A) (hAr : 1 ≤ A * (A - r ^ 2)) :
    ∀ (d i : ℕ) (b : ℕ → ℝ) (T : ℝ),
      (∀ k, 0 ≤ b k) → (∀ k, b k ≤ r ^ (i + k)) → 0 ≤ T → T ≤ A * r ^ i →
      0 ≤ rollUp b T d ∧ rollUp b T d ≤ A * r ^ i := by
  intro d
  induction d with
  | zero =>
    intro i b T _ _ hT0 hTle
    exact ⟨hT0, hTle⟩
  | succ n ih =>
    intro i b T hb_nonneg hb_le hT0 hTle
    have hri_pos : (0 : ℝ) < r ^ i := pow_pos (by linarith : (0 : ℝ) < r) i
    have hpow_mono : r ^ i ≤ r ^ (i + 1) := by
      rw [pow_succ]
      nlinarith [mul_pos hri_pos (show (0 : ℝ) < r - 1 by linarith)]
    have hTle' : T ≤ A * r ^ (i + 1) := by
      have hAmono : A * r ^ i ≤ A * r ^ (i + 1) := mul_le_mul_of_nonneg_left hpow_mono hA
      linarith
    have hshift_nonneg : ∀ k, 0 ≤ (fun k => b (k + 1)) k := fun k => hb_nonneg (k + 1)
    have hshift_le : ∀ k, (fun k => b (k + 1)) k ≤ r ^ (i + 1 + k) := by
      intro k
      have h := hb_le (k + 1)
      have heq : i + (k + 1) = i + 1 + k := by ring
      rwa [heq] at h
    obtain ⟨hlo, hhi⟩ := ih (i + 1) (fun k => b (k + 1)) T hshift_nonneg hshift_le hT0 hTle'
    have hb1_le : b 1 ≤ r ^ (i + 1) := hb_le 1
    have hb1_nonneg : 0 ≤ b 1 := hb_nonneg 1
    have hri1_nonneg : (0 : ℝ) ≤ r ^ (i + 1) := le_of_lt (pow_pos (by linarith : (0 : ℝ) < r) (i + 1))
    have hY1 : (1 : ℝ) ≤ r ^ i * r ^ i := by
      have hri : (1 : ℝ) ≤ r ^ i := one_le_pow_of_one_lt hr i
      nlinarith [hri]
    have hrad_le : 1 + b 1 * rollUp (fun k => b (k + 1)) T n ≤ (A * r ^ i) ^ 2 := by
      have hstep1 : b 1 * rollUp (fun k => b (k + 1)) T n ≤ r ^ (i + 1) * (A * r ^ (i + 1)) :=
        mul_le_mul hb1_le hhi hlo hri1_nonneg
      have hRHS_eq : r ^ (i + 1) * (A * r ^ (i + 1)) = A * r ^ 2 * (r ^ i * r ^ i) := by
        have e1 : r ^ (i + 1) = r ^ i * r := pow_succ r i
        rw [e1]; ring
      have hgoalRHS_eq : (A * r ^ i) ^ 2 = A ^ 2 * (r ^ i * r ^ i) := by ring
      have hkey : (1 : ℝ) ≤ A * (A - r ^ 2) * (r ^ i * r ^ i) := by
        have hb : (0 : ℝ) ≤ A * (A - r ^ 2) := by linarith [hAr]
        nlinarith [mul_le_mul hAr hY1 (by norm_num : (0 : ℝ) ≤ 1) hb]
      have hexpand : A * (A - r ^ 2) * (r ^ i * r ^ i) =
          A ^ 2 * (r ^ i * r ^ i) - A * r ^ 2 * (r ^ i * r ^ i) := by ring
      rw [hRHS_eq] at hstep1
      rw [hgoalRHS_eq]
      linarith [hstep1, hkey, hexpand]
    rw [rollUp_succ]
    refine ⟨Real.sqrt_nonneg _, ?_⟩
    calc Real.sqrt (1 + b 1 * rollUp (fun k => b (k + 1)) T n)
        ≤ Real.sqrt ((A * r ^ i) ^ 2) := Real.sqrt_le_sqrt hrad_le
      _ = A * r ^ i := Real.sqrt_sq (mul_nonneg hA (le_of_lt hri_pos))

/-! ## Step 4: assembling existence of a limit for `a_k = p_k` -/

/-- Concrete instantiation: `r = 4`, `A = 17` satisfies `rollUp_geomBounded`'s
hypotheses (`1 ≤ 17*(17-16) = 17`), and `primeCoeff_le_pow` supplies exactly
the growth bound `primeCoeff k ≤ 4^(0+k)` needed at the top level (`i = 0`). -/
theorem primeCoeff_bounded (d : ℕ) :
    0 ≤ truncRadical primeCoeff d ∧ truncRadical primeCoeff d ≤ 17 := by
  have hr : (1 : ℝ) < 4 := by norm_num
  have hA : (0 : ℝ) ≤ 17 := by norm_num
  have hAr : (1 : ℝ) ≤ 17 * (17 - (4 : ℝ) ^ 2) := by norm_num
  have hle : ∀ k, primeCoeff k ≤ (4 : ℝ) ^ (0 + k) := by
    intro k; simpa using primeCoeff_le_pow k
  have hT : (1 : ℝ) ≤ 17 * (4 : ℝ) ^ (0 : ℕ) := by norm_num
  have h := rollUp_geomBounded hr hA hAr d 0 primeCoeff 1 primeCoeff_nonneg hle
    (by norm_num) hT
  simpa [truncRadical] using h

/-- **Existence of a limit** for the prime-coefficient nested radical
(`a_k = p_k`, the paper's Appendix A.2 example) — the one case the paper
itself leaves as an open problem in v2 (see `RamanujanNested.lean`). Unlike
`HerschfeldClosure.lean`'s exact-value result for `a_k = N+k-2`, this only
establishes EXISTENCE of a finite limit, via a much cruder growth bound
(`p_k ≤ 4^k`, itself following from Bertrand's postulate). The exact value is
not pinned down here and is left open, matching the paper. -/
theorem primeRadical_converges :
    ∃ L : ℝ, Tendsto (truncRadical primeCoeff) atTop (𝓝 L) ∧ L ≤ 17 := by
  have hmono : Monotone (truncRadical primeCoeff) :=
    truncRadical_monotone primeCoeff primeCoeff_nonneg
  have hbdd : BddAbove (Set.range (truncRadical primeCoeff)) := by
    refine ⟨17, ?_⟩
    rintro x ⟨d, rfl⟩
    exact (primeCoeff_bounded d).2
  refine ⟨⨆ i, truncRadical primeCoeff i, tendsto_atTop_ciSup hmono hbdd, ?_⟩
  apply ciSup_le
  intro d
  exact (primeCoeff_bounded d).2

end RamanujanNested
