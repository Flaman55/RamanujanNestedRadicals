import RamanujanNested.TargetRadical
import RamanujanNested.NthRootChain
import Mathlib

/-!
# TargetRadicalNthRoot.lean — the constant-coefficient exact-target radical, any root order n ≥ 2

`TargetRadical.lean` builds a CONSTANT coefficient `a = t - 1/t` whose
square-root radical converges to a prescribed target `t` exactly, sidestepping
the classical unbounded-coefficient convergence question entirely. Unlike
`IdentityChain.lean` (which fails to generalize past `n = 2` — see
`NthRootChain.lean`'s docstring — because it needs an entire *sequence*
`R_k = N+k-1` to satisfy the recursion exactly, and `(x+1)^n-1` only
factors that cleanly at `n=2`), this construction only ever needs to solve
ONE equation for ONE constant `a`, given the target `t` and root order `n`:
`a = (t^n-1)/t`. That is a fixed point condition on a single number, not a
factorization of a whole family, so it carries over to every root order with
no obstruction at all.

## The coefficient and its defining identity

`targetCoeffN n t := (t^n-1)/t` is exactly the unique constant coefficient
solving `1 + a\cdot t = t^n` (`targetCoeffN_key`) — the fixed-point equation
for the recursion `R_k = (1+a R_{k+1})^{1/n}`. At `n=2` this is
`(t^2-1)/t = t - 1/t`, recovering `TargetRadical.lean`'s `targetCoeff`
exactly.

## The contraction rate, generalized

`TargetRadical.lean`'s conjugate-multiplication trick (`(t-V')(t+V')=t^2-V'^2`)
is specific to squares. The replacement here avoids needing the general
`n`-term geometric-sum factorization of `t^n-V'^n`: since `0 \le V' \le t`,
`t^{n-1}(t-V') \le t^n - V'^n` reduces (after expanding) to
`V'\cdot(t^{n-1}-V'^{n-1}) \ge 0`, true because `V' \le t` gives
`V'^{n-1}\le t^{n-1}` (`pow_le_pow_left₀`). Combined with `t^n-V'^n=a(t-V)`
(from the two defining equations), this gives the geometric bound
`t-V' \le \rho_n\cdot(t-V)` with `\rho_n = a/t^{n-1} = 1-1/t^n`, which is `<1`
unconditionally for `t>0` (numerically checked against the true asymptotic
rate `(1-1/t^n)/n` for several `n,t`: this bound is valid but not tight,
matching the fact that `TargetRadical.lean`'s own `n=2` bound is not tight
either).
-/

namespace RamanujanNested

/-- The constant coefficient whose n-th-root fixed point is exactly `t`,
generalizing `targetCoeff` (`TargetRadical.lean`, the case `n=2`). -/
noncomputable def targetCoeffN (n : ℕ) (t : ℝ) : ℝ := (t ^ n - 1) / t

theorem targetCoeffN_two_eq (t : ℝ) : targetCoeffN 2 t = targetCoeff t := by
  unfold targetCoeffN targetCoeff
  rcases eq_or_ne t 0 with h0 | h0
  · simp [h0]
  · field_simp
    ring

/-- The defining fixed-point identity: `1 + a\cdot t = t^n`. -/
theorem targetCoeffN_key {n : ℕ} {t : ℝ} (ht0 : t ≠ 0) :
    1 + targetCoeffN n t * t = t ^ n := by
  unfold targetCoeffN
  field_simp [ht0]

theorem targetCoeffN_nonneg {n : ℕ} {t : ℝ} (ht : 1 ≤ t) : 0 ≤ targetCoeffN n t := by
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  unfold targetCoeffN
  have h1 : (1:ℝ) ^ n ≤ t ^ n := pow_le_pow_left₀ (by norm_num) ht n
  rw [one_pow] at h1
  exact div_nonneg (by linarith) htpos.le

/-- **The rpow fixed-point property.** `(1+a\cdot t)^{1/n} = t` for `t \ge 1`. -/
theorem targetCoeffN_rpow_fixed {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 1 ≤ t) :
    (1 + targetCoeffN n t * t) ^ (1 / (n : ℝ)) = t := by
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  have hn_ne : (n : ℝ) ≠ 0 := by
    have hpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    linarith
  rw [targetCoeffN_key (ne_of_gt htpos), ← Real.rpow_natCast t n, ← Real.rpow_mul htpos.le,
    mul_one_div, div_self hn_ne, Real.rpow_one]

/-- **Boundedness for the n-th-root target radical**, directly from
`NthRootChain.lean`'s `rollUpN_bounded`: every truncation of the
constant-`targetCoeffN n t`-radical lies in `[0,t]`. -/
theorem targetRadicalN_bounded {n : ℕ} (hn : 2 ≤ n) {t T : ℝ} (ht : 1 ≤ t) (hT0 : 0 ≤ T)
    (hTt : T ≤ t) (d : ℕ) :
    0 ≤ rollUpN n (fun _ => targetCoeffN n t) T d ∧
      rollUpN n (fun _ => targetCoeffN n t) T d ≤ t := by
  have hA : 0 ≤ targetCoeffN n t := targetCoeffN_nonneg ht
  have hceil : (1 + targetCoeffN n t * t) ^ (1 / (n : ℝ)) ≤ t :=
    le_of_eq (targetCoeffN_rpow_fixed hn ht)
  exact rollUpN_bounded hA hceil d T (fun _ => targetCoeffN n t) hT0 hTt (fun _ => hA)
    (fun _ => le_refl _)

/-- The n-th-power identity for one recursion step: `V'^n = 1+a\cdot V`,
converting the `rpow`-defined recursion back to an ordinary polynomial
equation — the one place this file bridges `rpow` and `pow`, same pattern as
`NthRootChain.lean`. -/
theorem targetRadicalN_step_pow {n : ℕ} (hn : 2 ≤ n) {t T : ℝ} (ht : 1 ≤ t) (hT0 : 0 ≤ T)
    (hTt : T ≤ t) (d : ℕ) :
    (rollUpN n (fun _ => targetCoeffN n t) T (d + 1)) ^ n =
      1 + targetCoeffN n t * rollUpN n (fun _ => targetCoeffN n t) T d := by
  have hA : 0 ≤ targetCoeffN n t := targetCoeffN_nonneg ht
  have hV_nonneg := (targetRadicalN_bounded hn ht hT0 hTt d).1
  have hrad_nonneg : 0 ≤ 1 + targetCoeffN n t * rollUpN n (fun _ => targetCoeffN n t) T d :=
    add_nonneg zero_le_one (mul_nonneg hA hV_nonneg)
  have hn_ne : (n : ℝ) ≠ 0 := by
    have hpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    linarith
  have hstep_eq : rollUpN n (fun _ => targetCoeffN n t) T (d + 1) =
      (1 + targetCoeffN n t * rollUpN n (fun _ => targetCoeffN n t) T d) ^ (1 / (n : ℝ)) :=
    rollUpN_succ n (fun _ => targetCoeffN n t) T d
  have hexp1 : (1 / (n : ℝ)) * (n : ℝ) = 1 := by field_simp [hn_ne]
  rw [hstep_eq, ← Real.rpow_natCast _ n, ← Real.rpow_mul hrad_nonneg, hexp1, Real.rpow_one]

/-- **One contraction step, generalized.** The gap to the target `t` shrinks
by the factor `\rho_n = a/t^{n-1} = 1-1/t^n` at every layer. -/
theorem targetRadicalN_gap_step {n : ℕ} (hn : 2 ≤ n) {t T : ℝ} (ht : 1 ≤ t) (hT0 : 0 ≤ T)
    (hTt : T ≤ t) (d : ℕ) :
    t - rollUpN n (fun _ => targetCoeffN n t) T (d + 1) ≤
      (targetCoeffN n t / t ^ (n - 1)) * (t - rollUpN n (fun _ => targetCoeffN n t) T d) := by
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  have hV_bd := targetRadicalN_bounded hn ht hT0 hTt d
  have hV'_bd := targetRadicalN_bounded hn ht hT0 hTt (d + 1)
  have hV'pow := targetRadicalN_step_pow hn ht hT0 hTt d
  have htpow : 1 + targetCoeffN n t * t = t ^ n := targetCoeffN_key (ne_of_gt htpos)
  set V := rollUpN n (fun _ => targetCoeffN n t) T d with hVdef
  set V' := rollUpN n (fun _ => targetCoeffN n t) T (d + 1) with hV'def
  have hns : t ^ n - V' ^ n = targetCoeffN n t * (t - V) := by
    rw [hV'pow]; rw [← htpow]; ring
  -- t^(n-1)*(t-V') ≤ t^n - V'^n, from V' ≤ t and pow_le_pow_left₀
  have hn1 : n - 1 + 1 = n := by omega
  have hpow_le : V' ^ (n - 1) ≤ t ^ (n - 1) := pow_le_pow_left₀ hV'_bd.1 hV'_bd.2 (n - 1)
  have hlb : t ^ (n - 1) * (t - V') ≤ t ^ n - V' ^ n := by
    have hexp_t : t ^ n = t ^ (n - 1) * t := by
      conv_lhs => rw [← hn1]
      rw [pow_succ]
    have hexp_V' : V' ^ n = V' ^ (n - 1) * V' := by
      conv_lhs => rw [← hn1]
      rw [pow_succ]
    have hkey : t ^ n - V' ^ n - t ^ (n - 1) * (t - V') = V' * (t ^ (n - 1) - V' ^ (n - 1)) := by
      rw [hexp_t, hexp_V']; ring
    have hprod_nonneg : 0 ≤ V' * (t ^ (n - 1) - V' ^ (n - 1)) :=
      mul_nonneg hV'_bd.1 (by linarith [hpow_le])
    linarith [hkey, hprod_nonneg]
  have htpow1_pos : 0 < t ^ (n - 1) := pow_pos htpos (n - 1)
  have hcomb : t ^ (n - 1) * (t - V') ≤ targetCoeffN n t * (t - V) := by
    rw [← hns]; exact hlb
  rw [div_mul_eq_mul_div, le_div_iff₀ htpow1_pos]
  nlinarith [hcomb]

/-- **The geometric error bound**, by induction on `d`. -/
theorem targetRadicalN_gap_geometric {n : ℕ} (hn : 2 ≤ n) {t T : ℝ} (ht : 1 ≤ t) (hT0 : 0 ≤ T)
    (hTt : T ≤ t) :
    ∀ d : ℕ, t - rollUpN n (fun _ => targetCoeffN n t) T d ≤
      (targetCoeffN n t / t ^ (n - 1)) ^ d * (t - T) := by
  intro d
  induction d with
  | zero =>
    have h0 : rollUpN n (fun _ => targetCoeffN n t) T 0 = T := rfl
    simp [h0]
  | succ k ih =>
    have hstep := targetRadicalN_gap_step hn ht hT0 hTt k
    have htpos : 0 < t := lt_of_lt_of_le one_pos ht
    have hratio_nonneg : 0 ≤ targetCoeffN n t / t ^ (n - 1) :=
      div_nonneg (targetCoeffN_nonneg ht) (le_of_lt (pow_pos htpos (n - 1)))
    calc t - rollUpN n (fun _ => targetCoeffN n t) T (k + 1)
        ≤ (targetCoeffN n t / t ^ (n - 1)) *
            (t - rollUpN n (fun _ => targetCoeffN n t) T k) := hstep
      _ ≤ (targetCoeffN n t / t ^ (n - 1)) *
            ((targetCoeffN n t / t ^ (n - 1)) ^ k * (t - T)) :=
          mul_le_mul_of_nonneg_left ih hratio_nonneg
      _ = (targetCoeffN n t / t ^ (n - 1)) ^ (k + 1) * (t - T) := by ring

/-- The contraction ratio is strictly below `1`, unconditionally for `t > 0`:
`t^n - 1 < t^n` always, so `\rho_n = (t^n-1)/t^n < 1`. -/
theorem targetCoeffN_ratio_lt_one {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 1 ≤ t) :
    targetCoeffN n t / t ^ (n - 1) < 1 := by
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  have hn1 : n - 1 + 1 = n := by omega
  have htpow1_pos : 0 < t ^ (n - 1) := pow_pos htpos (n - 1)
  rw [div_lt_one htpow1_pos]
  unfold targetCoeffN
  have hexp : t ^ n = t ^ (n - 1) * t := by
    conv_lhs => rw [← hn1]
    rw [pow_succ]
  rw [hexp, div_lt_iff₀ htpos]
  nlinarith [htpow1_pos]

/-- **Convergence to exactly `t`, at any root order `n \ge 2`.** Generalizes
`targetRadical_tendsto` (`TargetRadical.lean`, `n=2`). -/
theorem targetRadicalN_tendsto {n : ℕ} (hn : 2 ≤ n) {t T : ℝ} (ht : 1 ≤ t) (hT0 : 0 ≤ T)
    (hTt : T ≤ t) :
    Filter.Tendsto (fun d => rollUpN n (fun _ => targetCoeffN n t) T d) Filter.atTop (nhds t) := by
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  have hratio_nonneg : 0 ≤ targetCoeffN n t / t ^ (n - 1) :=
    div_nonneg (targetCoeffN_nonneg ht) (le_of_lt (pow_pos htpos (n - 1)))
  have hratio_lt1 : targetCoeffN n t / t ^ (n - 1) < 1 := targetCoeffN_ratio_lt_one hn ht
  have hgeom : Filter.Tendsto (fun d : ℕ => (targetCoeffN n t / t ^ (n - 1)) ^ d * (t - T))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun d : ℕ => (targetCoeffN n t / t ^ (n - 1)) ^ d)
        Filter.atTop (nhds 0) := tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nonneg hratio_lt1
    simpa using h0.mul_const (t - T)
  have hbound := targetRadicalN_gap_geometric hn ht hT0 hTt
  have hlo : ∀ d, (0:ℝ) ≤ t - rollUpN n (fun _ => targetCoeffN n t) T d := fun d => by
    have := (targetRadicalN_bounded hn ht hT0 hTt d).2
    linarith
  have hsqueeze : Filter.Tendsto (fun d => t - rollUpN n (fun _ => targetCoeffN n t) T d)
      Filter.atTop (nhds 0) := squeeze_zero hlo hbound hgeom
  have := hsqueeze.const_sub t
  simpa using this

end RamanujanNested
