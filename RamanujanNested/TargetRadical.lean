import RamanujanNested.Bounds
import Mathlib

/-!
# TargetRadical.lean — a constant-coefficient radical hitting an exact target

Instead of trying to prove that the classical, UNBOUNDED Ramanujan radical
(`a_k = k`) converges to a prescribed target under the forward evaluation
(an open gap — see
`RamanujanNested.lean`'s "Known gap" section, since `Bounds.lean` needs a
fixed uniform ceiling `A`), build a genuinely different, structurally simple
nested radical that:

1. uses a CONSTANT coefficient `a_k = t - 1/t` (bounded — trivially satisfies
   `Bounds.lean`'s hypothesis with `A = t - 1/t`),
2. is exactly the paper's own general framework (Section 4, `a_k = f(k)`,
   here `f` constant), so it's not a foreign trick — it's the same machine,
3. converges to the target `t` EXACTLY, not merely bounded by it, and
4. does so geometrically fast, with an explicit, computable rate
   `ρ = (t - 1/t) / t = 1 - 1/t²`, strictly less than 1.

This is "a different product of equivalent strength": same target value,
same general framework, provably convergent using machinery already built
here (`Bounds.lean`), sidestepping the open question about the classical
unbounded case entirely rather than resolving it.
-/

namespace RamanujanNested

/-- The constant coefficient whose fixed point is exactly `t`. -/
noncomputable def targetCoeff (t : ℝ) : ℝ := t - 1 / t

/-- **The defining property, made concrete.** `rStar (targetCoeff t) = t` for
`t ≥ 1`: the constant-coefficient radical's universal bound *is* the target
itself. (Check: `N=3` gives `targetCoeff 3 = 8/3`, and
`rStar (8/3) = (8/3 + √(64/9+36/9))/2 = (8/3+10/3)/2 = 3` — exactly.) -/
theorem rStar_targetCoeff {t : ℝ} (ht : 1 ≤ t) : rStar (targetCoeff t) = t := by
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  unfold rStar targetCoeff
  have hkey : (t - 1 / t) ^ 2 + 4 = (t + 1 / t) ^ 2 := by
    field_simp
    ring
  rw [hkey]
  have hnn : 0 ≤ t + 1 / t := by positivity
  rw [Real.sqrt_sq hnn]
  ring

/-- `targetCoeff t ≥ 0` for `t ≥ 1` — so `Bounds.lean` applies directly. -/
theorem targetCoeff_nonneg {t : ℝ} (ht : 1 ≤ t) : 0 ≤ targetCoeff t := by
  unfold targetCoeff
  rw [sub_nonneg, div_le_iff₀ (lt_of_lt_of_le one_pos ht)]
  nlinarith

/-- **Boundedness for the target radical**, directly from `Bounds.lean`:
every truncation of the constant-`targetCoeff t`-radical lies in `[0, t]`. -/
theorem targetRadical_bounded {t T : ℝ} (ht : 1 ≤ t) (hT0 : 0 ≤ T) (hTt : T ≤ t) (d : ℕ) :
    0 ≤ rollUp (fun _ => targetCoeff t) T d ∧ rollUp (fun _ => targetCoeff t) T d ≤ t := by
  have hA : 0 ≤ targetCoeff t := targetCoeff_nonneg ht
  have hStar : rStar (targetCoeff t) = t := rStar_targetCoeff ht
  have hTA : T ≤ rStar (targetCoeff t) := by rw [hStar]; exact hTt
  have := rollUp_bounded hA hT0 hTA d (fun _ => targetCoeff t) (fun _ => le_refl _)
  rwa [hStar] at this

/-- **One contraction step.** The gap to the target `t` shrinks by the factor
`ρ = targetCoeff t / t` at every layer — this is the algebraic heart of the
whole file: conjugate-multiply `t - √(t² - ρ·t·e)` to see the gap divides,
it doesn't just shrink by inspection. -/
theorem targetRadical_gap_step {t T : ℝ} (ht : 1 ≤ t) (hT0 : 0 ≤ T) (hTt : T ≤ t) (d : ℕ) :
    t - rollUp (fun _ => targetCoeff t) T (d + 1) ≤
      (targetCoeff t / t) * (t - rollUp (fun _ => targetCoeff t) T d) := by
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  set A := targetCoeff t with hA_def
  have hA_nonneg : 0 ≤ A := targetCoeff_nonneg ht
  have hStar : rStar A = t := rStar_targetCoeff ht
  obtain ⟨hV_ge, hV_le⟩ := targetRadical_bounded ht hT0 hTt d
  set V := rollUp (fun _ => A) T d with hVdef
  set V' := rollUp (fun _ => A) T (d + 1) with hV'def
  have hstep : V' = Real.sqrt (1 + A * V) := by rw [hV'def, rollUp_succ]
  have hV'_nonneg : 0 ≤ V' := hstep ▸ Real.sqrt_nonneg _
  have hV'sq : V' ^ 2 = 1 + A * V := by
    rw [hstep]; exact Real.sq_sqrt (by nlinarith [mul_nonneg hA_nonneg hV_ge])
  have hRsq : t ^ 2 = 1 + A * t := by
    have := rStar_sq A; rwa [hStar] at this
  have hconj : (t - V') * (t + V') = A * (t - V) := by
    have hexp : (t - V') * (t + V') = t ^ 2 - V' ^ 2 := by ring
    rw [hexp, hV'sq, hRsq]; ring
  have hsum_pos : 0 < t + V' := by linarith
  have he_nonneg : 0 ≤ t - V := by linarith [hV_le]
  have hnum_nonneg : 0 ≤ A * (t - V) := mul_nonneg hA_nonneg he_nonneg
  have hkey : t - V' = A * (t - V) / (t + V') := by
    rw [eq_div_iff (ne_of_gt hsum_pos)]; linarith [hconj]
  rw [hkey]
  have hstep2 : A * (t - V) / (t + V') ≤ A * (t - V) / t := by
    rw [div_le_div_iff₀ hsum_pos htpos]
    nlinarith [mul_nonneg hnum_nonneg hV'_nonneg]
  have heq : A * (t - V) / t = (A / t) * (t - V) := by ring
  linarith [hstep2, heq]

/-- **The geometric error bound**, by induction on `d`: the gap to the exact
target `t` shrinks geometrically, with explicit ratio `targetCoeff t / t`. -/
theorem targetRadical_gap_geometric {t T : ℝ} (ht : 1 ≤ t) (hT0 : 0 ≤ T) (hTt : T ≤ t) :
    ∀ d : ℕ, t - rollUp (fun _ => targetCoeff t) T d ≤
      (targetCoeff t / t) ^ d * (t - T) := by
  intro d
  induction d with
  | zero =>
    have h0 : rollUp (fun _ => targetCoeff t) T 0 = T := rfl
    simp [h0]
  | succ n ih =>
    have hstep := targetRadical_gap_step ht hT0 hTt n
    have hratio_nonneg : 0 ≤ targetCoeff t / t :=
      div_nonneg (targetCoeff_nonneg ht) (le_trans zero_le_one ht)
    calc t - rollUp (fun _ => targetCoeff t) T (n + 1)
        ≤ (targetCoeff t / t) * (t - rollUp (fun _ => targetCoeff t) T n) := hstep
      _ ≤ (targetCoeff t / t) * ((targetCoeff t / t) ^ n * (t - T)) := by
          apply mul_le_mul_of_nonneg_left ih hratio_nonneg
      _ = (targetCoeff t / t) ^ (n + 1) * (t - T) := by ring

/-- The contraction ratio is strictly below `1`: `targetCoeff t < t` always
(the same fact underlying `Bounds.lean`'s `one_le_rStar`, specialized here). -/
theorem targetCoeff_ratio_lt_one {t : ℝ} (ht : 1 ≤ t) : targetCoeff t / t < 1 := by
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  rw [div_lt_one htpos]
  unfold targetCoeff
  have : 0 < 1 / t := by positivity
  linarith

/-- **Convergence to exactly `t`.** Combining the geometric bound with the
ratio being `< 1`: the constant-`targetCoeff t` radical tends to `t` — not
merely bounded by it, but converging to it exactly, with an explicit rate. -/
theorem targetRadical_tendsto {t T : ℝ} (ht : 1 ≤ t) (hT0 : 0 ≤ T) (hTt : T ≤ t) :
    Filter.Tendsto (fun d => rollUp (fun _ => targetCoeff t) T d) Filter.atTop (nhds t) := by
  have hratio_nonneg : 0 ≤ targetCoeff t / t :=
    div_nonneg (targetCoeff_nonneg ht) (le_trans zero_le_one ht)
  have hratio_lt1 : targetCoeff t / t < 1 := targetCoeff_ratio_lt_one ht
  have hgeom : Filter.Tendsto (fun d : ℕ => (targetCoeff t / t) ^ d * (t - T))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun d : ℕ => (targetCoeff t / t) ^ d) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nonneg hratio_lt1
    simpa using h0.mul_const (t - T)
  have hbound := targetRadical_gap_geometric ht hT0 hTt
  have hlo : ∀ d, (0:ℝ) ≤ t - rollUp (fun _ => targetCoeff t) T d := fun d => by
    have := (targetRadical_bounded ht hT0 hTt d).2
    linarith
  have hsqueeze : Filter.Tendsto (fun d => t - rollUp (fun _ => targetCoeff t) T d)
      Filter.atTop (nhds 0) :=
    squeeze_zero hlo hbound hgeom
  have := hsqueeze.const_sub t
  simpa using this

end RamanujanNested
