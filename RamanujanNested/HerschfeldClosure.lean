import RamanujanNested.UnboundedChain
import Mathlib

/-!
# HerschfeldClosure.lean — L(N) = N, exactly

Closes (for the `a_k = N+k-2` family — and, by trivial reindexing, the
classical `a_k = k` case from Section 5.1) the remaining half of the gap
`UnboundedChain.lean` left open: that file proves the truncated radical has a
finite limit `L(N) ≤ N`; this file proves `L(N) = N` exactly.

The argument rests on a single global multiplicative growth bound,
`δ(N+1) ≥ δ(N)·(N+1)/(N-1)`, valid for every `N` (not merely while `δ` is
small — it uses only the trivial ceiling `δ(N) ≤ N-1`), which telescopes to
an explicit *quadratic*-in-step lower bound. This outraces the *linear*
trivial ceiling after finitely many steps, forcing `δ ≡ 0`, with no
arbitrary cutoff at any point in the argument.

## Status

No `sorry`: `limitVal`, its `Tendsto`/bounds, the functional equation
`limitVal_functional_eq`, `deficit_recursion`, `deficit_growth` (the key
global bound), `quad_step` + `deficit_quadratic_lower` (telescoping over `j`
steps), and `limitVal_eq_self` (the closing contradiction) are all proved in
full.
-/

namespace RamanujanNested

open Filter Topology

/-- The limit of the truncated classical-type radical, named (previously
only established as an anonymous witness inside `classicalRadical_converges`
in `UnboundedChain.lean`). -/
noncomputable def limitVal (N : ℝ) : ℝ := ⨆ i, truncRadical (classicalCoeff N) i

section Basic

private theorem limitVal_bddAbove {N : ℝ} (hN : 2 ≤ N) :
    BddAbove (Set.range (truncRadical (classicalCoeff N))) := by
  refine ⟨N, ?_⟩
  rintro x ⟨d, rfl⟩
  exact (classicalCoeff_bounded (by linarith) d).2

private theorem limitVal_mono {N : ℝ} (hN : 2 ≤ N) :
    Monotone (truncRadical (classicalCoeff N)) := by
  have hnonneg : ∀ k, 0 ≤ classicalCoeff N k := fun k => by
    unfold classicalCoeff
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  exact truncRadical_monotone (classicalCoeff N) hnonneg

theorem limitVal_tendsto {N : ℝ} (hN : 2 ≤ N) :
    Tendsto (truncRadical (classicalCoeff N)) atTop (𝓝 (limitVal N)) :=
  tendsto_atTop_ciSup (limitVal_mono hN) (limitVal_bddAbove hN)

theorem limitVal_le {N : ℝ} (hN : 2 ≤ N) : limitVal N ≤ N := by
  apply ciSup_le
  intro d
  exact (classicalCoeff_bounded (by linarith) d).2

theorem limitVal_ge_one {N : ℝ} (hN : 2 ≤ N) : 1 ≤ limitVal N := by
  have h0 : truncRadical (classicalCoeff N) 0 = 1 := rfl
  rw [← h0]
  exact le_ciSup (limitVal_bddAbove hN) 0

end Basic

/-- The exact per-depth identity behind the functional equation: peeling one
layer off the `N`-family exposes the `(N+1)`-family underneath, exactly (no
approximation) — the same shift identity used throughout `UnboundedChain.lean`. -/
private theorem step_identity (N : ℝ) (d : ℕ) :
    truncRadical (classicalCoeff N) (d + 1) =
      Real.sqrt (1 + (N - 1) * truncRadical (classicalCoeff (N + 1)) d) := by
  have hshift : (fun k => classicalCoeff N (k + 1)) = classicalCoeff (N + 1) := by
    funext k; unfold classicalCoeff; push_cast; ring
  have ha1 : classicalCoeff N 1 = N - 1 := by
    unfold classicalCoeff; push_cast; ring
  unfold truncRadical
  rw [rollUp_succ, ha1, hshift]

/-- `d ↦ d+1` tends to `atTop` — the elementary fact making "shifting a
sequence by one index doesn't change its limit" work, proved directly from
the definition of `atTop`. -/
private theorem tendsto_succ_atTop : Tendsto (fun d : ℕ => d + 1) atTop atTop :=
  tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)

/-- **The functional equation.** `L(N) = √(1 + (N-1)·L(N+1))`, obtained by
passing the exact per-depth identity `step_identity` to the limit `d → ∞` on
both sides: the shifted sequence `d ↦ truncRadical (classicalCoeff N) (d+1)`
has the same limit `L(N)` as the original (via `tendsto_succ_atTop`), and
also equals (pointwise, exactly) `d ↦ √(1+(N-1)·truncRadical (classicalCoeff
(N+1)) d)`, which tends to `√(1+(N-1)·L(N+1))` by continuity of `√` and of
the affine map — equate the two limits. -/
theorem limitVal_functional_eq {N : ℝ} (hN : 2 ≤ N) :
    limitVal N = Real.sqrt (1 + (N - 1) * limitVal (N + 1)) := by
  have hN1 : 2 ≤ N + 1 := by linarith
  have hshift_tendsto :
      Tendsto (fun d => truncRadical (classicalCoeff N) (d + 1)) atTop (𝓝 (limitVal N)) :=
    (limitVal_tendsto hN).comp tendsto_succ_atTop
  have heq : (fun d => truncRadical (classicalCoeff N) (d + 1)) =
      (fun d => Real.sqrt (1 + (N - 1) * truncRadical (classicalCoeff (N + 1)) d)) := by
    funext d; exact step_identity N d
  rw [heq] at hshift_tendsto
  have hcont : Continuous (fun x : ℝ => Real.sqrt (1 + (N - 1) * x)) :=
    Real.continuous_sqrt.comp (continuous_const.add (continuous_const.mul continuous_id))
  have hL4 : Tendsto (fun d => Real.sqrt (1 + (N - 1) * truncRadical (classicalCoeff (N + 1)) d))
      atTop (𝓝 (Real.sqrt (1 + (N - 1) * limitVal (N + 1)))) :=
    (hcont.tendsto (limitVal (N + 1))).comp (limitVal_tendsto hN1)
  exact tendsto_nhds_unique hshift_tendsto hL4

/-- The deficit `δ(N) := N - L(N)`, zero exactly when `L(N) = N`. -/
noncomputable def deficit (N : ℝ) : ℝ := N - limitVal N

theorem deficit_nonneg {N : ℝ} (hN : 2 ≤ N) : 0 ≤ deficit N := by
  unfold deficit; linarith [limitVal_le hN]

/-- The trivial ceiling: `δ(N) ≤ N-1`, from `L(N) ≥ 1`. This is the ONLY
independent bound the whole contradiction argument needs. -/
theorem deficit_le_ceiling {N : ℝ} (hN : 2 ≤ N) : deficit N ≤ N - 1 := by
  unfold deficit; linarith [limitVal_ge_one hN]

/-- **The deficit recursion**, `δ(N+1) = δ(N)·(2N-δ(N))/(N-1)`, an exact
algebraic corollary of the functional equation (square both sides, use
`(N-1)(N+1) = N²-1`). -/
theorem deficit_recursion {N : ℝ} (hN : 2 ≤ N) :
    deficit (N + 1) = deficit N * (2 * N - deficit N) / (N - 1) := by
  have hFE := limitVal_functional_eq hN
  have hN1pos : (0 : ℝ) < N - 1 := by linarith
  have hL1_nonneg : (0 : ℝ) ≤ 1 + (N - 1) * limitVal (N + 1) := by
    have := limitVal_ge_one (show (2 : ℝ) ≤ N + 1 by linarith)
    nlinarith
  have hsq : (limitVal N) ^ 2 = 1 + (N - 1) * limitVal (N + 1) := by
    rw [hFE]; exact Real.sq_sqrt hL1_nonneg
  unfold deficit
  rw [eq_div_iff (ne_of_gt hN1pos)]
  linear_combination hsq

/-- **The key global growth bound.** No case distinction and no arbitrary
cutoff are needed: the argument uses only the trivial ceiling `δ(N) ≤ N-1`,
valid everywhere. `δ(N+1)-δ(N) = δ(N)·(N+1-δ(N))/(N-1) ≥ δ(N)·2/(N-1)` (since
`N+1-δ(N) ≥ 2` follows directly from the ceiling), giving the stated
multiplicative bound. -/
theorem deficit_growth {N : ℝ} (hN : 2 ≤ N) :
    deficit N * (N + 1) / (N - 1) ≤ deficit (N + 1) := by
  have hN1pos : (0 : ℝ) < N - 1 := by linarith
  have hceil : deficit N ≤ N - 1 := deficit_le_ceiling hN
  have hnn : 0 ≤ deficit N := deficit_nonneg hN
  rw [deficit_recursion hN, div_le_div_iff₀ hN1pos hN1pos]
  have h1 : N + 1 ≤ 2 * N - deficit N := by linarith
  nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hnn) hN1pos.le]

/-- One step of the telescoping, isolated as a standalone real-number
identity (no natural-number casts at all) to keep the cast bookkeeping in
`deficit_quadratic_lower` itself as small as possible. -/
private theorem quad_step {N₀ M : ℝ} (hN₀ : 2 ≤ N₀) (hM : 2 ≤ M)
    (ih : deficit N₀ * (M * (M - 1)) / (N₀ * (N₀ - 1)) ≤ deficit M) :
    deficit N₀ * ((M + 1) * M) / (N₀ * (N₀ - 1)) ≤ deficit (M + 1) := by
  have hMpos : (0 : ℝ) < M - 1 := by linarith
  have hN0pos : (0 : ℝ) < N₀ * (N₀ - 1) := by nlinarith
  have hratio_nonneg : (0 : ℝ) ≤ (M + 1) / (M - 1) := by positivity
  have hgrow := deficit_growth hM
  have step : deficit N₀ * (M * (M - 1)) / (N₀ * (N₀ - 1)) * ((M + 1) / (M - 1)) ≤
      deficit M * ((M + 1) / (M - 1)) :=
    mul_le_mul_of_nonneg_right ih hratio_nonneg
  have eq1 : deficit N₀ * (M * (M - 1)) / (N₀ * (N₀ - 1)) * ((M + 1) / (M - 1)) =
      deficit N₀ * ((M + 1) * M) / (N₀ * (N₀ - 1)) := by
    field_simp
    ring
  have eq2 : deficit M * ((M + 1) / (M - 1)) = deficit M * (M + 1) / (M - 1) := by ring
  rw [eq1, eq2] at step
  exact le_trans step hgrow

/-- **Telescoping `deficit_growth` over `j` steps.** The product
`∏_{i=0}^{j-1} (N₀+i+1)/(N₀+i-1)` telescopes — numerators `N₀+1,…,N₀+j`,
denominators `N₀-1,…,N₀+j-2` — to exactly `(N₀+j)(N₀+j-1) / (N₀(N₀-1))`,
proved here by induction via `quad_step`. -/
theorem deficit_quadratic_lower {N₀ : ℝ} (hN₀ : 2 ≤ N₀) :
    ∀ j : ℕ, deficit N₀ * ((N₀ + (j : ℝ)) * (N₀ + (j : ℝ) - 1)) / (N₀ * (N₀ - 1)) ≤
      deficit (N₀ + (j : ℝ)) := by
  have hC0pos : (0 : ℝ) < N₀ * (N₀ - 1) := by nlinarith
  intro j
  induction j with
  | zero =>
    simp only [Nat.cast_zero, add_zero]
    rw [mul_div_assoc, div_self (ne_of_gt hC0pos), mul_one]
  | succ n ih =>
    have hnnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hNn : (2 : ℝ) ≤ N₀ + (n : ℝ) := by linarith
    have hstep := quad_step hN₀ hNn ih
    have hcast : (N₀ + ((n + 1 : ℕ) : ℝ)) = (N₀ + (n : ℝ)) + 1 := by push_cast; ring
    rw [hcast]
    have hsimp : (N₀ + (n : ℝ)) + 1 - 1 = N₀ + (n : ℝ) := by ring
    rw [hsimp]
    exact hstep

/-- **The closing contradiction and main theorem: `L(N) = N` exactly.**
Suppose `limitVal N < N` (i.e. `deficit N > 0`). `deficit_quadratic_lower`
gives a lower bound on `deficit (N+j)` growing like `j²`; `deficit_le_ceiling`
gives an upper bound growing only like `j`. The Archimedean property picks a
concrete `j` large enough (`exists_nat_gt`) that the quadratic lower bound
already exceeds the linear ceiling at that `j` — contradiction. -/
theorem limitVal_eq_self {N : ℝ} (hN : 2 ≤ N) : limitVal N = N := by
  by_contra hne
  have hlt : limitVal N < N := lt_of_le_of_ne (limitVal_le hN) hne
  have hδ0_pos : 0 < deficit N := by unfold deficit; linarith
  have hN0pos : (0 : ℝ) < N * (N - 1) := by nlinarith
  obtain ⟨j, hj⟩ := exists_nat_gt (N * (N - 1) / deficit N - N)
  have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hNj : (2 : ℝ) ≤ N + (j : ℝ) := by linarith
  have hNjm1_pos : (0 : ℝ) < N + (j : ℝ) - 1 := by linarith
  have hlow := deficit_quadratic_lower hN j
  have hceil := deficit_le_ceiling hNj
  have hprod : N * (N - 1) < (N + (j : ℝ)) * deficit N := by
    have h1 : N * (N - 1) / deficit N < N + (j : ℝ) := by linarith
    rwa [div_lt_iff₀ hδ0_pos] at h1
  have hfinal : N + (j : ℝ) - 1 <
      deficit N * ((N + (j : ℝ)) * (N + (j : ℝ) - 1)) / (N * (N - 1)) := by
    rw [lt_div_iff₀ hN0pos]
    nlinarith [mul_lt_mul_of_pos_right hprod hNjm1_pos]
  linarith [hlow, hceil, hfinal]

end RamanujanNested
