import RamanujanNested.Bounds
import RamanujanNested.Monotone
import RamanujanNested.UnboundedChain
import Mathlib

/-!
# LinearChain.lean — existence of a limit for ANY linear-growth slope, not just slope 1

`UnboundedChain.lean` proves existence of a limit for `a_k = N+k-2`, i.e. a
linear coefficient family with slope exactly `1`. That slope was not an
arbitrary modeling choice: the linear closed-form ansatz `R_k = p*k+q`
satisfies the recursion `R_k = √(1+a_k·R_{k+1})` for `a_k = m*k+b` only when
`m² = 1` (checked directly by matching coefficients of `k²,k,k⁰` after
squaring) — so slope `1` is the *only* slope admitting an exact closed-form
limit via this ansatz. For any other slope, the exact value is presumably not
expressible this simply, if at all.

But *existence* of a limit is a much lower bar than an exact closed form, and
this file shows existence holds for the whole range of slopes `m ≥ 1`, not
just `m = 1` — via the same moving-ceiling technique as `UnboundedChain.lean`,
generalized so the ceiling itself shifts by `m` (not by a fixed `1`) at each
recursive layer. Slopes `0 < m < 1` are not covered here; the key inequality
below (`m² ≥ 1`) fails for them, and closing that range needs a different
(larger, non-`C(N)=N`) ceiling. **See `LinearChainGeneral.lean`**, which
closes the entire remaining range `0 < m < 1` (in fact, gives a single proof
covering all `m > 0` at once) using the looser ceiling `C(N) = N+1`; the
tight bound `L ≤ N` here is still the better result whenever `m ≥ 1` applies.
Any exact-value question beyond `m = 1` remains open regardless.

## Motivation

This generalizes beyond `a_k = N+k-2` because not every linearly-growing
coefficient family appearing in the literature has slope exactly `1`. In
particular, Kusniec's "difference-of-oblongs" Radiciatory
(`R_obl(x,q)`, oblong-based nested radical family) has coefficients linear in
depth with slope `q-1`: existence for that family, whenever `q ≥ 2`, is now a
direct instance of `linearRadical_converges` below, with no new proof needed
per value of `q`. For `1 < q < 2` (slope between 0 and 1), this file does not
yet say anything.
-/

namespace RamanujanNested

/-- A linear-growth coefficient family with general slope `m`, generalizing
`classicalCoeff` (`UnboundedChain.lean`), which is exactly the case `m = 1`:
`linearCoeff 1 N = classicalCoeff N`. -/
noncomputable def linearCoeff (m N : ℝ) (k : ℕ) : ℝ := N + m * ((k : ℝ) - 2)

theorem linearCoeff_one_eq_classicalCoeff (N : ℝ) :
    linearCoeff 1 N = classicalCoeff N := by
  funext k
  unfold linearCoeff classicalCoeff
  ring

/-- **Moving-ceiling boundedness, general slope.** Same structure as
`rollUp_classicalCoeff_bounded`, but the ceiling now shifts by `m` per layer
instead of by a fixed `1`: peeling one layer trades ceiling `N` for `N+m` on
a family with parameter shifted the same way. The key algebraic fact that
replaces `UnboundedChain.lean`'s exact identity `(N-1)(N+1)+1 = N²` is the
*inequality* `(N-m)(N+m)+1 ≤ N²`, i.e. `1 ≤ m²` — which is why `m ≥ 1` is
required (and where the argument would break for `0 < m < 1`). -/
theorem rollUp_linearCoeff_bounded :
    ∀ (d : ℕ) (m N T : ℝ), 1 ≤ m → 2 * m ≤ N → 0 ≤ T → T ≤ N →
      0 ≤ rollUp (linearCoeff m N) T d ∧ rollUp (linearCoeff m N) T d ≤ N := by
  intro d
  induction d with
  | zero =>
    intro m N T _ _ hT0 hTN
    exact ⟨hT0, hTN⟩
  | succ n ih =>
    intro m N T hm hN hT0 hTN
    have hN1 : 2 * m ≤ N + m := by linarith
    have hTN1 : T ≤ N + m := by linarith
    obtain ⟨_, hhi⟩ := ih m (N + m) T hm hN1 hT0 hTN1
    have hshift : (fun k => linearCoeff m N (k + 1)) = linearCoeff m (N + m) := by
      funext k
      unfold linearCoeff
      push_cast
      ring
    have ha1 : linearCoeff m N 1 = N - m := by
      unfold linearCoeff
      push_cast
      ring
    have ha1_nonneg : 0 ≤ linearCoeff m N 1 := by
      rw [ha1]; linarith
    rw [rollUp_succ, hshift]
    have hradicand_le :
        1 + linearCoeff m N 1 * rollUp (linearCoeff m (N + m)) T n ≤ N ^ 2 := by
      rw [ha1]
      have hmul : (N - m) * rollUp (linearCoeff m (N + m)) T n ≤ (N - m) * (N + m) :=
        mul_le_mul_of_nonneg_left hhi (by linarith)
      nlinarith [hmul, sq_nonneg (m - 1), sq_nonneg (m + 1)]
    refine ⟨Real.sqrt_nonneg _, ?_⟩
    calc Real.sqrt (1 + linearCoeff m N 1 * rollUp (linearCoeff m (N + m)) T n)
        ≤ Real.sqrt (N ^ 2) := Real.sqrt_le_sqrt hradicand_le
      _ = N := Real.sqrt_sq (by linarith)

/-- Specialized to the canonical seed `T = 1`. -/
theorem linearCoeff_bounded {m N : ℝ} (hm : 1 ≤ m) (hN : 2 * m ≤ N) (d : ℕ) :
    0 ≤ truncRadical (linearCoeff m N) d ∧ truncRadical (linearCoeff m N) d ≤ N :=
  rollUp_linearCoeff_bounded d m N 1 hm hN (by norm_num) (by linarith)

open Filter Topology

/-- **Existence of a limit for any slope `m ≥ 1`.** Generalizes
`classicalRadical_converges` (`UnboundedChain.lean`, the case `m = 1`) to the
whole family of slopes `m ≥ 1`. As there, this gives existence and an upper
bound `L ≤ N`, not the exact value of `L`. -/
theorem linearRadical_converges {m N : ℝ} (hm : 1 ≤ m) (hN : 2 * m ≤ N) :
    ∃ L : ℝ, Tendsto (truncRadical (linearCoeff m N)) atTop (𝓝 L) ∧ L ≤ N := by
  have hnonneg : ∀ k, 0 ≤ linearCoeff m N k := fun k => by
    unfold linearCoeff
    have hk2 : (-2 : ℝ) ≤ (k : ℝ) - 2 := by
      have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      linarith
    nlinarith [hk2]
  have hmono : Monotone (truncRadical (linearCoeff m N)) :=
    truncRadical_monotone (linearCoeff m N) hnonneg
  have hbdd : BddAbove (Set.range (truncRadical (linearCoeff m N))) := by
    refine ⟨N, ?_⟩
    rintro x ⟨d, rfl⟩
    exact (linearCoeff_bounded hm hN d).2
  refine ⟨⨆ i, truncRadical (linearCoeff m N) i, tendsto_atTop_ciSup hmono hbdd, ?_⟩
  apply ciSup_le
  intro d
  exact (linearCoeff_bounded hm hN d).2

/-- Sanity check: at `m = 1`, this specializes to exactly
`classicalRadical_converges`'s conclusion, confirming `LinearChain.lean`
genuinely generalizes `UnboundedChain.lean` rather than duplicating it. -/
theorem linearRadical_converges_one {N : ℝ} (hN : 2 ≤ N) :
    ∃ L : ℝ, Tendsto (truncRadical (classicalCoeff N)) atTop (𝓝 L) ∧ L ≤ N := by
  rw [← linearCoeff_one_eq_classicalCoeff]
  exact linearRadical_converges (le_refl 1) (by linarith)

end RamanujanNested
