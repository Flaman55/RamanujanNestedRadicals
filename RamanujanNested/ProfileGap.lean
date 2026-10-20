module

public import Mathlib
public import RamanujanNested.NthRootChain

/-!
# ProfileGap.lean — exact value and explicit rate for an arbitrary profile

Let `n ≥ 1` and let `R : ℕ → ℝ` be a *profile*: `R k ≥ 1` for every `k ≥ 1`, and the
coefficient sequence `a` is the one that makes `R` satisfy the radical recursion exactly,

  `R_k ^ n = 1 + a_k · R_{k+1}`   for every `k ≥ 1`.

(Equivalently `a_k = (R_k ^ n - 1) / R_{k+1}`, which is `Reconstruction.lean`'s inverse
construction.) The truncation of depth `d` with seed `1` is `rollUpN n a 1 d`.

## Main results

* `rollUpN_profile_gap`: for every depth `d`,
  `0 ≤ R_1 - rollUpN n a 1 d ≤ R_1 · ∏_{j<d} (1 - 1/R_{j+1})`.
* `rollUpN_profile_tendsto`: if `∑ 1/R_k` diverges, the truncations converge to exactly `R_1`.

The bound comes from a one-step contraction: with `s = (1 + a_1 u)^{1/n}` and `u` the truncation
of the shifted problem, `R_1^n - s^n = a_1 (R_2 - u)`, and `s ≥ 1` gives
`R_1 - s ≤ (R_1 - 1)(R_2 - u)/R_2`. Iterating telescopes into the product. No limit, no
functional equation and no deficit-growth argument is used.

Special cases: `R_k = t` (constant) is the exact-target radical (`TargetRadical*.lean`) with seed
`1`, and `R_k = N + k - 1` with `n = 2` is the classical family `a_k = N + k - 2`
(`HerschfeldClosure.lean`).
-/

namespace RamanujanNested

open Finset Filter Topology

/-- **Explicit gap bound for a profile.** -/
public theorem rollUpN_profile_gap {n : ℕ} (hn : 1 ≤ n) :
    ∀ (d : ℕ) (a R : ℕ → ℝ), (∀ k, 1 ≤ R (k + 1)) →
      (∀ k, R (k + 1) ^ n = 1 + a (k + 1) * R (k + 2)) →
      1 ≤ rollUpN n a 1 d ∧ 0 ≤ R 1 - rollUpN n a 1 d ∧
        R 1 - rollUpN n a 1 d ≤ R 1 * ∏ j ∈ range d, (1 - 1 / R (j + 1)) := by
  intro d
  induction d with
  | zero =>
    intro a R hR ha
    have h1 : 1 ≤ R 1 := by simpa using hR 0
    have h0 : rollUpN n a 1 0 = 1 := rfl
    rw [h0]
    refine ⟨le_refl 1, ?_, ?_⟩
    · linarith
    · simp only [Finset.range_zero, Finset.prod_empty, mul_one]
      linarith
  | succ d ih =>
    intro a R hR ha
    have hx : 1 ≤ R 1 := by simpa using hR 0
    have hy : 1 ≤ R 2 := by simpa using hR 1
    have hrel : R 1 ^ n = 1 + a 1 * R 2 := by simpa using ha 0
    -- the shifted problem
    have hR' : ∀ k, 1 ≤ (fun j => R (j + 1)) (k + 1) := fun k => hR (k + 1)
    have ha' : ∀ k, (fun j => R (j + 1)) (k + 1) ^ n =
        1 + (fun j => a (j + 1)) (k + 1) * (fun j => R (j + 1)) (k + 2) := fun k => ha (k + 1)
    obtain ⟨hu1, hu0, hugap⟩ := ih (fun j => a (j + 1)) (fun j => R (j + 1)) hR' ha'
    set u := rollUpN n (fun j => a (j + 1)) 1 d with hu_def
    have hu1' : 1 ≤ u := hu1
    have huy : R 2 - u ≤ R 2 * ∏ j ∈ range d, (1 - 1 / R (j + 2)) := hugap
    have huy0 : 0 ≤ R 2 - u := hu0
    have hn0 : n ≠ 0 := by omega
    -- a 1 is nonnegative
    have hxn : 1 ≤ R 1 ^ n := one_le_pow₀ hx
    have ha1 : 0 ≤ a 1 := by
      by_contra hneg
      have hneg' : a 1 < 0 := not_le.mp hneg
      have : a 1 * R 2 < 0 := mul_neg_of_neg_of_pos hneg' (by linarith)
      linarith
    -- the truncation s
    have hsucc : rollUpN n a 1 (d + 1) = (1 + a 1 * u) ^ (1 / (n : ℝ)) := rollUpN_succ n a 1 d
    set s := rollUpN n a 1 (d + 1) with hs_def
    have hbase : 1 ≤ 1 + a 1 * u := by
      have : 0 ≤ a 1 * u := mul_nonneg ha1 (by linarith)
      linarith
    have hs1 : 1 ≤ s := by
      rw [hsucc]; exact Real.one_le_rpow hbase (by positivity)
    have hspow : s ^ n = 1 + a 1 * u := by
      rw [hsucc, one_div]
      exact Real.rpow_inv_natCast_pow (by linarith) hn0
    -- s ≤ R 1 and the key inequality
    have hdiff : R 1 ^ n - s ^ n = a 1 * (R 2 - u) := by
      rw [hrel, hspow]; ring
    have hdiff0 : 0 ≤ R 1 ^ n - s ^ n := by
      rw [hdiff]; exact mul_nonneg ha1 huy0
    have hsx : s ≤ R 1 := by
      by_contra hlt
      have hlt' : R 1 < s := not_le.mp hlt
      have := pow_lt_pow_left₀ hlt' (by linarith) hn0
      linarith
    -- geometric sums
    have hG := geom_sum₂_mul (R 1) s n
    have hH := geom_sum_mul (R 1) n
    set G := ∑ i ∈ range n, R 1 ^ i * s ^ (n - 1 - i) with hG_def
    set H := ∑ i ∈ range n, R 1 ^ i with hH_def
    have hHG : H ≤ G := by
      apply Finset.sum_le_sum
      intro i _
      have : 1 ≤ s ^ (n - 1 - i) := one_le_pow₀ hs1
      have hxi : 0 ≤ R 1 ^ i := by positivity
      exact le_mul_of_one_le_right hxi this
    have hHpos : 0 < H := by
      have : (∑ i ∈ range n, (1 : ℝ)) ≤ H := by
        apply Finset.sum_le_sum
        intro i _
        exact one_le_pow₀ hx
      simp at this
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    -- (R1 - s) * R2 ≤ (R1 - 1) * (R2 - u)
    have hkey : (R 1 - s) * R 2 ≤ (R 1 - 1) * (R 2 - u) := by
      have e1 : (R 1 - s) * G = a 1 * (R 2 - u) := by
        rw [← hdiff, ← hG]; ring
      have e2 : a 1 * R 2 = H * (R 1 - 1) := by
        rw [hH]; linarith [hrel]
      have hxs : 0 ≤ R 1 - s := by linarith
      have hy0 : 0 ≤ R 2 := by linarith
      have h3 : (R 1 - s) * R 2 * H ≤ (R 1 - s) * R 2 * G := by
        apply mul_le_mul_of_nonneg_left hHG (mul_nonneg hxs hy0)
      have h4 : (R 1 - s) * R 2 * G = H * (R 1 - 1) * (R 2 - u) := by
        calc (R 1 - s) * R 2 * G = ((R 1 - s) * G) * R 2 := by ring
          _ = a 1 * (R 2 - u) * R 2 := by rw [e1]
          _ = (a 1 * R 2) * (R 2 - u) := by ring
          _ = H * (R 1 - 1) * (R 2 - u) := by rw [e2]
      have h5 : (R 1 - s) * R 2 * H ≤ ((R 1 - 1) * (R 2 - u)) * H := by
        calc (R 1 - s) * R 2 * H ≤ (R 1 - s) * R 2 * G := h3
          _ = H * (R 1 - 1) * (R 2 - u) := h4
          _ = ((R 1 - 1) * (R 2 - u)) * H := by ring
      exact le_of_mul_le_mul_right h5 hHpos
    have hxs0 : 0 ≤ R 1 - s := by linarith
    -- combine with the induction hypothesis
    refine ⟨hs1, hxs0, ?_⟩
    have hy0 : 0 < R 2 := by linarith
    have hx1 : 0 ≤ R 1 - 1 := by linarith
    have hP : (R 1 - s) * R 2 ≤ (R 1 - 1) * (R 2 * ∏ j ∈ range d, (1 - 1 / R (j + 2))) := by
      calc (R 1 - s) * R 2 ≤ (R 1 - 1) * (R 2 - u) := hkey
        _ ≤ (R 1 - 1) * (R 2 * ∏ j ∈ range d, (1 - 1 / R (j + 2))) :=
          mul_le_mul_of_nonneg_left huy hx1
    have hP' : R 1 - s ≤ (R 1 - 1) * ∏ j ∈ range d, (1 - 1 / R (j + 2)) := by
      have : (R 1 - s) * R 2 ≤ ((R 1 - 1) * ∏ j ∈ range d, (1 - 1 / R (j + 2))) * R 2 := by
        calc (R 1 - s) * R 2 ≤ (R 1 - 1) * (R 2 * ∏ j ∈ range d, (1 - 1 / R (j + 2))) := hP
          _ = ((R 1 - 1) * ∏ j ∈ range d, (1 - 1 / R (j + 2))) * R 2 := by ring
      exact le_of_mul_le_mul_right this hy0
    have hprod : ∏ j ∈ range (d + 1), (1 - 1 / R (j + 1)) =
        (∏ j ∈ range d, (1 - 1 / R (j + 2))) * (1 - 1 / R 1) := by
      exact Finset.prod_range_succ' (fun j => 1 - 1 / R (j + 1)) d
    have hxpos : 0 < R 1 := by linarith
    have hxne : R 1 ≠ 0 := ne_of_gt hxpos
    have hxe : R 1 - 1 = R 1 * (1 - 1 / R 1) := by
      rw [mul_sub, mul_one, mul_one_div_cancel hxne]
    calc R 1 - s ≤ (R 1 - 1) * ∏ j ∈ range d, (1 - 1 / R (j + 2)) := hP'
      _ = R 1 * ∏ j ∈ range (d + 1), (1 - 1 / R (j + 1)) := by
        rw [hprod, hxe]; ring

/-- **Exact value for a profile with divergent `∑ 1/R_k`.** The truncations of the radical built
from `a_k = (R_k^n - 1)/R_{k+1}` converge to exactly `R_1`. -/
public theorem rollUpN_profile_tendsto {n : ℕ} (hn : 1 ≤ n) (a R : ℕ → ℝ)
    (hR : ∀ k, 1 ≤ R (k + 1))
    (ha : ∀ k, R (k + 1) ^ n = 1 + a (k + 1) * R (k + 2))
    (hdiv : ¬ Summable (fun k => 1 / R (k + 1))) :
    Tendsto (fun d => rollUpN n a 1 d) atTop (𝓝 (R 1)) := by
  have hR1 : 1 ≤ R 1 := by simpa using hR 0
  have hpos : ∀ k, 0 < R (k + 1) := fun k => by linarith [hR k]
  have hnonneg : ∀ k, 0 ≤ 1 / R (k + 1) := fun k => by
    have := hpos k
    positivity
  have hS : Tendsto (fun d => ∑ i ∈ range d, 1 / R (i + 1)) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).mp hdiv
  have hexp : Tendsto (fun d => R 1 * Real.exp (-(∑ i ∈ range d, 1 / R (i + 1)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun d => Real.exp (-(∑ i ∈ range d, 1 / R (i + 1)))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hS
    simpa using h1.const_mul (R 1)
  have hbound : ∀ d, ∏ j ∈ range d, (1 - 1 / R (j + 1)) ≤
      Real.exp (-(∑ i ∈ range d, 1 / R (i + 1))) := by
    intro d
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_le_prod₀
    · intro j _
      have hxj : 1 / R (j + 1) ≤ 1 := by
        rw [div_le_one (hpos j)]; exact hR j
      linarith
    · intro j _
      have := Real.add_one_le_exp (-(1 / R (j + 1)))
      linarith
  have hgap : ∀ d, 0 ≤ R 1 - rollUpN n a 1 d ∧
      R 1 - rollUpN n a 1 d ≤ R 1 * Real.exp (-(∑ i ∈ range d, 1 / R (i + 1))) := by
    intro d
    obtain ⟨_, h0, h1⟩ := rollUpN_profile_gap hn d a R hR ha
    refine ⟨h0, ?_⟩
    calc R 1 - rollUpN n a 1 d ≤ R 1 * ∏ j ∈ range d, (1 - 1 / R (j + 1)) := h1
      _ ≤ R 1 * Real.exp (-(∑ i ∈ range d, 1 / R (i + 1))) :=
        mul_le_mul_of_nonneg_left (hbound d) (by linarith)
  have hzero : Tendsto (fun d => R 1 - rollUpN n a 1 d) atTop (𝓝 0) :=
    squeeze_zero (fun d => (hgap d).1) (fun d => (hgap d).2) hexp
  have := (tendsto_const_nhds (x := R 1)).sub hzero
  simpa using this

end RamanujanNested
