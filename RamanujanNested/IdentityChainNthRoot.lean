import Mathlib

/-!
# IdentityChainNthRoot.lean — the classical unbounded family, any root order `n ≥ 2`

Generalizes `IdentityChain.lean` (Algorithm 3, `n = 2`) and
`HerschfeldClosure.lean` (`L(N) = N` exactly, `n = 2`) to arbitrary root order.

## The unifying identity

For any `n`, `x = -1` is a root of exactly one of `x^n - 1` or `x^n + 1`
(whichever matches the parity of `n`), since `(-1)^n = 1` for even `n` and
`(-1)^n = -1` for odd `n`. Factoring out `(x+1)` in the matching case gives,
uniformly in `n`,

  `altSum n x * (x + 1) = x^n - (-1)^n`

(an instance of Mathlib's `geom_sum₂_mul` with `y = -1`), where `altSum n x`
is the single alternating-sign polynomial `x^{n-1} - x^{n-2} + ⋯ ± 1` — the
SAME polynomial serves both parities; only the sign `(-1)^n` on the other
side of the identity depends on parity. Consequently the classical closed
form `R_k = N+k-1` (`IdentityChain.lean`'s Algorithm 3) satisfies, for
*every* `n ≥ 2`,

  `R_k^n = (-1)^n + altSum n R_k · R_{k+1}`

exactly: `+1` inside the radical when `n` is even, `-1` when `n` is odd. The
even/odd distinction is thus a single sign, not a structural split, so both
cases are carried by one coefficient family and one set of theorems below,
branching only where the sign genuinely changes the argument
(`altSum_shift_ge_one`, and the final exact-limit closure).

## What's proven here

* `chainS_satisfies_recursion` / `chainS_hits_target`: the exact algebraic
  identity chain, any `n ≥ 2`, both parities uniformly (generalizes
  `IdentityChain.lean`).
* `truncRadicalNS_converges`: existence of a finite limit `L(N) ∈ [1,N]` for
  the truncated radical built from this family, any `n ≥ 2`, both parities
  (generalizes `UnboundedChain.lean`).
* `limitValNS_eq_self_even`: **`L(N) = N` exactly**, for *even* `n`
  (generalizes `HerschfeldClosure.lean`). The deficit-growth argument
  transfers essentially unchanged: the key global bound
  `δ(N+1)·(N-1) ≥ δ(N)·(N+1)` falls out of the same factorization
  `N^n - L(N)^n = (N - L(N))·S`, using only `L(N) ≥ 1` to bound `S` from
  below — and for even `n` this bound matches `altSum n N`'s own numerator
  exactly, reproducing the `n = 2` ratio `(N+1)/(N-1)` verbatim.
* `limitValNS_eq_self_odd`: **`L(N) = N` exactly**, for *odd* `n` as well
  (Part 4 below). For odd `n` the matching numerator is off by a constant
  from the even case (`altSum`'s is `N^n+1`, the bound from `L ≥ 1` alone
  gives `N^n-1`), so the clean ratio picks up an extra per-step shrink
  factor; this factor is shown to stay bounded below by a fixed positive
  constant uniformly in the step count, which keeps the deficit growth
  quadratic and closes the argument regardless of parity.
-/

namespace RamanujanNested

open Finset

/-! ## Part 0: the unifying polynomial -/

/-- The alternating-sign polynomial `x^{n-1} - x^{n-2} + ⋯ ± 1`, the same
polynomial for every `n` regardless of parity. -/
noncomputable def altSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ range n, x ^ i * (-1 : ℝ) ^ (n - 1 - i)

/-- **The unifying identity.** An instance of `geom_sum₂_mul` (Mathlib) with
`y = -1`. Even `n`: `altSum n x * (x+1) = x^n - 1`. Odd `n`:
`altSum n x * (x+1) = x^n + 1`. -/
theorem altSum_identity (n : ℕ) (x : ℝ) :
    altSum n x * (x + 1) = x ^ n - (-1 : ℝ) ^ n := by
  unfold altSum
  have h := geom_sum₂_mul x (-1 : ℝ) n
  rwa [sub_neg_eq_add] at h

/-! ## Part 1: the closed-form identity chain, both parities at once -/

/-- The closed form claimed by Algorithm 3, `R_k = N+k-1` (`IdentityChain.lean`). -/
noncomputable def chainClosedFormS (N k : ℕ) : ℝ := (N : ℝ) + (k : ℝ) - 1

theorem chainS_base (N d : ℕ) : chainClosedFormS N (d + 1) = (N : ℝ) + (d : ℝ) := by
  unfold chainClosedFormS; push_cast; ring

/-- **The identity chain, any root order `n ≥ 2`, both parities uniformly.**
The closed form `R_k = N+k-1` satisfies `R_k = ((-1)^n + altSum n R_k · R_{k+1})^{1/n}`
for every `k`: the radicand simplifies EXACTLY to `R_k^n` via `altSum_identity`
(since `R_{k+1} = R_k + 1`), and then `(R_k^n)^{1/n} = R_k` since `R_k ≥ 0`. -/
theorem chainS_satisfies_recursion {n : ℕ} (hn : 2 ≤ n) (N k : ℕ) (hN : 2 ≤ N) :
    chainClosedFormS N k =
      ((-1 : ℝ) ^ n + altSum n (chainClosedFormS N k) * chainClosedFormS N (k + 1)) ^
        (1 / (n : ℝ)) := by
  have hx_nonneg : 0 ≤ chainClosedFormS N k := by
    unfold chainClosedFormS
    have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hsucc : chainClosedFormS N (k + 1) = chainClosedFormS N k + 1 := by
    unfold chainClosedFormS; push_cast; ring
  rw [hsucc]
  have hid := altSum_identity n (chainClosedFormS N k)
  have hradicand : (-1 : ℝ) ^ n + altSum n (chainClosedFormS N k) * (chainClosedFormS N k + 1) =
      (chainClosedFormS N k) ^ n := by linarith [hid]
  have hn_ne : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    linarith
  have hpow_inv : (chainClosedFormS N k ^ n : ℝ) ^ (1 / (n : ℝ)) = chainClosedFormS N k := by
    rw [← Real.rpow_natCast (chainClosedFormS N k) n, ← Real.rpow_mul hx_nonneg, mul_one_div,
      div_self hn_ne, Real.rpow_one]
  rw [hradicand, hpow_inv]

theorem chainS_hits_target (N : ℕ) : chainClosedFormS N 1 = (N : ℝ) := by
  unfold chainClosedFormS; push_cast; ring

/-! ## Part 2: existence of a limit for the truncated radical, both parities -/

/-- `altSum n x ≥ 0` for `x ≥ 1`, from the identity plus `x^n ≥ 1 ≥ (-1)^n`. Holds
for every `n`, not only `n ≥ 2` — `altSum_identity` itself is unconditional in `n`. -/
theorem altSum_nonneg {n : ℕ} {x : ℝ} (hx : 1 ≤ x) : 0 ≤ altSum n x := by
  have hid := altSum_identity n x
  have hxp1_pos : (0 : ℝ) < x + 1 := by linarith
  have h1 : (-1 : ℝ) ^ n ≤ 1 := by
    have habs : |(-1 : ℝ) ^ n| = 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
    have hle := le_abs_self ((-1 : ℝ) ^ n)
    linarith [habs ▸ hle]
  have hxn_ge1 : (1 : ℝ) ≤ x ^ n := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hx n
    rwa [one_pow] at h
  have hxn_sub_nonneg : (0 : ℝ) ≤ x ^ n - (-1 : ℝ) ^ n := by linarith
  have hval : altSum n x = (x ^ n - (-1 : ℝ) ^ n) / (x + 1) :=
    (eq_div_iff (ne_of_gt hxp1_pos)).mpr hid
  rw [hval]
  exact div_nonneg hxn_sub_nonneg hxp1_pos.le

/-- **The invariant that makes the seed `T = 1` (not `0`) the right canonical
seed for this signed family.** `(-1)^n + altSum n x ≥ 1` for `x ≥ 2`: trivial
for even `n` (reduces to `altSum n x ≥ 0`); for odd `n` (`n ≥ 3`) needs
`altSum n x ≥ 2`, which follows from `x^n ≥ x^3 ≥ 2x+1`. This is exactly why
the odd-`n` forward evaluation from seed `0` fails numerically but seed `1`
(or any seed `≥ 1`) works: the radicand would go negative starting from `0`. -/
theorem altSum_shift_ge_one {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : 2 ≤ x) :
    (1 : ℝ) ≤ (-1 : ℝ) ^ n + altSum n x := by
  have hxp1_pos : (0 : ℝ) < x + 1 := by linarith
  have hid : altSum n x * (x + 1) = x ^ n - (-1 : ℝ) ^ n := altSum_identity n x
  rcases Nat.even_or_odd n with he | ho
  · have hsign : (-1 : ℝ) ^ n = 1 := he.neg_one_pow
    have hxn_ge1 : (1 : ℝ) ≤ x ^ n := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) ≤ x) n
      rwa [one_pow] at h
    have hgoal : (0 : ℝ) * (x + 1) ≤ altSum n x * (x + 1) := by
      rw [hid, hsign]; nlinarith [hxn_ge1]
    have hres := le_of_mul_le_mul_right hgoal hxp1_pos
    rw [hsign]; linarith [hres]
  · have hsign : (-1 : ℝ) ^ n = -1 := ho.neg_one_pow
    have hn3 : 3 ≤ n := by obtain ⟨m, hm⟩ := ho; omega
    have hx3 : x ^ 3 ≤ x ^ n := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ x) hn3
    have hcube : (2 : ℝ) * x + 1 ≤ x ^ 3 := by
      have key : (0 : ℝ) ≤ (x - 2) * (x ^ 2 + 2 * x) := by
        apply mul_nonneg
        · linarith
        · nlinarith
      nlinarith [key]
    have hgoal : (2 : ℝ) * (x + 1) ≤ altSum n x * (x + 1) := by
      rw [hid, hsign]; nlinarith [hx3, hcube]
    have hres := le_of_mul_le_mul_right hgoal hxp1_pos
    rw [hsign]; linarith [hres]

/-- The coefficient family `a_k = altSum n (N+k-1)`, real `N` (matching
`UnboundedChain.lean`'s `classicalCoeff`, not `IdentityChain.lean`'s nat `N`,
since the deficit-growth argument below needs to shift `N` by real amounts). -/
noncomputable def altCoeffR (n : ℕ) (N : ℝ) (k : ℕ) : ℝ := altSum n (N + (k : ℝ) - 1)

/-- The signed n-th-root nested radical recursion: `(-1)^n` in place of the
fixed `1` used by `NthRootChain.lean`'s `rollUpN` (that file's bounded-coefficient
family never needed anything else; this unbounded, sign-sensitive family does). -/
noncomputable def rollUpNS (n : ℕ) (a : ℕ → ℝ) (T : ℝ) : ℕ → ℝ
  | 0 => T
  | (k + 1) => ((-1 : ℝ) ^ n + a 1 * rollUpNS n (fun j => a (j + 1)) T k) ^ (1 / (n : ℝ))

theorem rollUpNS_succ (n : ℕ) (a : ℕ → ℝ) (T : ℝ) (k : ℕ) :
    rollUpNS n a T (k + 1) =
      ((-1 : ℝ) ^ n + a 1 * rollUpNS n (fun j => a (j + 1)) T k) ^ (1 / (n : ℝ)) := rfl

/-- **Moving-ceiling boundedness, signed family.** Unlike `NthRootChain.lean`,
the invariant tracked is `1 ≤ · ≤ N`, not `0 ≤ · ≤ N`: seed `T = 0` genuinely
breaks for odd `n` (the radicand can go negative), but seed `T ≥ 1` never
does, by `altSum_shift_ge_one`. -/
theorem rollUpNS_altCoeffR_bounded {n : ℕ} (hn : 2 ≤ n) :
    ∀ (d : ℕ) (N T : ℝ), 2 ≤ N → 1 ≤ T → T ≤ N →
      1 ≤ rollUpNS n (altCoeffR n N) T d ∧ rollUpNS n (altCoeffR n N) T d ≤ N := by
  intro d
  induction d with
  | zero => intro N T _ hT1 hTN; exact ⟨hT1, hTN⟩
  | succ m ih =>
    intro N T hN hT1 hTN
    have hN1 : 2 ≤ N + 1 := by linarith
    have hTN1 : T ≤ N + 1 := by linarith
    obtain ⟨hlo, hhi⟩ := ih (N + 1) T hN1 hT1 hTN1
    have hshift : (fun k => altCoeffR n N (k + 1)) = altCoeffR n (N + 1) := by
      funext k; unfold altCoeffR; congr 1; push_cast; ring
    have ha1_eq : altCoeffR n N 1 = altSum n N := by
      unfold altCoeffR; congr 1; push_cast; ring
    have ha1_nonneg : 0 ≤ altCoeffR n N 1 := by
      rw [ha1_eq]; exact altSum_nonneg (by linarith : (1 : ℝ) ≤ N)
    rw [rollUpNS_succ, hshift]
    have hradicand_le :
        (-1 : ℝ) ^ n + altCoeffR n N 1 * rollUpNS n (altCoeffR n (N + 1)) T m ≤ N ^ n := by
      rw [ha1_eq]
      have hmul : altSum n N * rollUpNS n (altCoeffR n (N + 1)) T m ≤ altSum n N * (N + 1) :=
        mul_le_mul_of_nonneg_left hhi (altSum_nonneg (by linarith : (1 : ℝ) ≤ N))
      have hid := altSum_identity n N
      linarith [hmul, hid]
    have hradicand_ge_one :
        (1 : ℝ) ≤ (-1 : ℝ) ^ n + altCoeffR n N 1 * rollUpNS n (altCoeffR n (N + 1)) T m := by
      rw [ha1_eq]
      have hmul : altSum n N * 1 ≤ altSum n N * rollUpNS n (altCoeffR n (N + 1)) T m :=
        mul_le_mul_of_nonneg_left hlo (altSum_nonneg (by linarith : (1 : ℝ) ≤ N))
      have hkey := altSum_shift_ge_one hn hN
      linarith [hmul, hkey]
    have hn_ne : (n : ℝ) ≠ 0 := by
      have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      linarith
    have hradicand_nonneg :
        (0 : ℝ) ≤ (-1 : ℝ) ^ n + altCoeffR n N 1 * rollUpNS n (altCoeffR n (N + 1)) T m := by
      linarith [hradicand_ge_one]
    constructor
    · calc (1 : ℝ) = (1 : ℝ) ^ (1 / (n : ℝ)) := (Real.one_rpow _).symm
        _ ≤ ((-1 : ℝ) ^ n + altCoeffR n N 1 * rollUpNS n (altCoeffR n (N + 1)) T m) ^
              (1 / (n : ℝ)) :=
          Real.rpow_le_rpow (by norm_num) hradicand_ge_one (by positivity)
    · calc ((-1 : ℝ) ^ n + altCoeffR n N 1 * rollUpNS n (altCoeffR n (N + 1)) T m) ^
              (1 / (n : ℝ))
          ≤ (N ^ n) ^ (1 / (n : ℝ)) :=
            Real.rpow_le_rpow hradicand_nonneg hradicand_le (by positivity)
        _ = N := by
            rw [← Real.rpow_natCast N n, ← Real.rpow_mul (by linarith : (0 : ℝ) ≤ N),
              mul_one_div, div_self hn_ne, Real.rpow_one]

/-- The paper's `R_1^{(N)}`, signed family: canonical seed `1`. -/
noncomputable def truncRadicalNS (n : ℕ) (N : ℝ) (d : ℕ) : ℝ := rollUpNS n (altCoeffR n N) 1 d

theorem truncRadicalNS_bounded {n : ℕ} (hn : 2 ≤ n) {N : ℝ} (hN : 2 ≤ N) (d : ℕ) :
    1 ≤ truncRadicalNS n N d ∧ truncRadicalNS n N d ≤ N :=
  rollUpNS_altCoeffR_bounded hn d N 1 hN (le_refl 1) (by linarith)

/-- **Depth-monotonicity, signed family.** Quantifying `N` inside the
induction (same shift trick as boundedness), using `altSum_shift_ge_one` for
the base case (this is the step that has no analogue in `NthRootChain.lean`,
since that file's `+1` convention makes the base case trivial regardless of
the coefficients' size). -/
theorem rollUpNS_altCoeffR_step_mono {n : ℕ} (hn : 2 ≤ n) :
    ∀ (d : ℕ) (N : ℝ), 2 ≤ N →
      rollUpNS n (altCoeffR n N) 1 d ≤ rollUpNS n (altCoeffR n N) 1 (d + 1) := by
  intro d
  induction d with
  | zero =>
    intro N hN
    rw [rollUpNS_succ]
    have h0 : rollUpNS n (fun k => altCoeffR n N (k + 1)) 1 0 = (1 : ℝ) := rfl
    rw [h0]
    have ha1_eq : altCoeffR n N 1 = altSum n N := by
      unfold altCoeffR; congr 1; push_cast; ring
    have hkey := altSum_shift_ge_one hn hN
    have hradicand : (-1 : ℝ) ^ n + altCoeffR n N 1 * 1 = (-1 : ℝ) ^ n + altSum n N := by
      rw [ha1_eq]; ring
    calc (1 : ℝ) = (1 : ℝ) ^ (1 / (n : ℝ)) := (Real.one_rpow _).symm
      _ ≤ ((-1 : ℝ) ^ n + altCoeffR n N 1 * 1) ^ (1 / (n : ℝ)) := by
          apply Real.rpow_le_rpow (by norm_num) _ (by positivity)
          rw [hradicand]; exact hkey
  | succ m ih =>
    intro N hN
    have hN1 : 2 ≤ N + 1 := by linarith
    have hshift : (fun k => altCoeffR n N (k + 1)) = altCoeffR n (N + 1) := by
      funext k; unfold altCoeffR; congr 1; push_cast; ring
    rw [rollUpNS_succ, rollUpNS_succ, hshift]
    have ha1_eq : altCoeffR n N 1 = altSum n N := by
      unfold altCoeffR; congr 1; push_cast; ring
    have ha1_nonneg : 0 ≤ altCoeffR n N 1 := by
      rw [ha1_eq]; exact altSum_nonneg (by linarith : (1 : ℝ) ≤ N)
    have hstep := ih (N + 1) hN1
    have hmul : altCoeffR n N 1 * rollUpNS n (altCoeffR n (N + 1)) 1 m ≤
        altCoeffR n N 1 * rollUpNS n (altCoeffR n (N + 1)) 1 (m + 1) :=
      mul_le_mul_of_nonneg_left hstep ha1_nonneg
    have hradicand_le :
        (-1 : ℝ) ^ n + altCoeffR n N 1 * rollUpNS n (altCoeffR n (N + 1)) 1 m ≤
        (-1 : ℝ) ^ n + altCoeffR n N 1 * rollUpNS n (altCoeffR n (N + 1)) 1 (m + 1) := by
      linarith
    have hb := rollUpNS_altCoeffR_bounded hn m (N + 1) 1 hN1 (le_refl 1) (by linarith)
    have hkey := altSum_shift_ge_one hn hN
    have hmul2 : altCoeffR n N 1 * 1 ≤ altCoeffR n N 1 * rollUpNS n (altCoeffR n (N + 1)) 1 m :=
      mul_le_mul_of_nonneg_left hb.1 ha1_nonneg
    have hradicand_nonneg :
        (0 : ℝ) ≤ (-1 : ℝ) ^ n + altCoeffR n N 1 * rollUpNS n (altCoeffR n (N + 1)) 1 m := by
      rw [ha1_eq] at hmul2 ⊢
      linarith [hmul2, hkey]
    exact Real.rpow_le_rpow hradicand_nonneg hradicand_le (by positivity)

theorem truncRadicalNS_monotone {n : ℕ} (hn : 2 ≤ n) {N : ℝ} (hN : 2 ≤ N) :
    Monotone (truncRadicalNS n N) := by
  apply monotone_nat_of_le_succ
  intro d
  exact rollUpNS_altCoeffR_step_mono hn d N hN

open Filter Topology

/-- **Existence of a limit, signed family, any root order `n ≥ 2`, both
parities.** Generalizes `UnboundedChain.lean`'s `classicalRadical_converges`
to arbitrary `n`, for the family that makes the identity chain (Part 1)
exact. -/
theorem truncRadicalNS_converges {n : ℕ} (hn : 2 ≤ n) {N : ℝ} (hN : 2 ≤ N) :
    ∃ L : ℝ, Tendsto (truncRadicalNS n N) atTop (𝓝 L) ∧ 1 ≤ L ∧ L ≤ N := by
  have hmono := truncRadicalNS_monotone hn hN
  have hbdd : BddAbove (Set.range (truncRadicalNS n N)) := by
    refine ⟨N, ?_⟩
    rintro x ⟨d, rfl⟩
    exact (truncRadicalNS_bounded hn hN d).2
  refine ⟨⨆ i, truncRadicalNS n N i, tendsto_atTop_ciSup hmono hbdd, ?_, ?_⟩
  · exact le_ciSup_of_le hbdd 0 (truncRadicalNS_bounded hn hN 0).1
  · apply ciSup_le
    intro d
    exact (truncRadicalNS_bounded hn hN d).2

/-! ## Part 3: the exact limit `L(N) = N`, for even root order

The argument mirrors `HerschfeldClosure.lean` verbatim in shape: a global
multiplicative growth bound on the deficit `δ(N) = N - L(N)` telescopes to a
quadratic-in-step lower bound, which outraces the trivial linear ceiling
`δ(N) ≤ N-1`. The one new ingredient is `deficitS_growth_even`, which derives
the SAME ratio `(N+1)/(N-1)` as the `n = 2` case from the factorization
`N^n - L(N)^n = (N - L(N)) · S` (`geom_sum₂_mul` again) together with the
bound `S ≥ (N^n-1)/(N-1)` (from `L(N) ≥ 1` alone) — which for even `n`
matches `altSum n N`'s own numerator `N^n - 1` exactly. -/

noncomputable def limitValNS (n : ℕ) (N : ℝ) : ℝ := ⨆ d, truncRadicalNS n N d

theorem limitValNS_tendsto {n : ℕ} (hn : 2 ≤ n) {N : ℝ} (hN : 2 ≤ N) :
    Tendsto (truncRadicalNS n N) atTop (𝓝 (limitValNS n N)) := by
  have hmono := truncRadicalNS_monotone hn hN
  have hbdd : BddAbove (Set.range (truncRadicalNS n N)) := by
    refine ⟨N, ?_⟩; rintro x ⟨d, rfl⟩; exact (truncRadicalNS_bounded hn hN d).2
  exact tendsto_atTop_ciSup hmono hbdd

theorem limitValNS_le {n : ℕ} (hn : 2 ≤ n) {N : ℝ} (hN : 2 ≤ N) : limitValNS n N ≤ N := by
  apply ciSup_le; intro d; exact (truncRadicalNS_bounded hn hN d).2

theorem limitValNS_ge_one {n : ℕ} (hn : 2 ≤ n) {N : ℝ} (hN : 2 ≤ N) : 1 ≤ limitValNS n N := by
  have h0 : truncRadicalNS n N 0 = (1 : ℝ) := rfl
  have hbdd : BddAbove (Set.range (truncRadicalNS n N)) := by
    refine ⟨N, ?_⟩; rintro x ⟨d, rfl⟩; exact (truncRadicalNS_bounded hn hN d).2
  rw [← h0]
  exact le_ciSup hbdd 0

private theorem stepS_identity {n : ℕ} (N : ℝ) (d : ℕ) :
    truncRadicalNS n N (d + 1) =
      ((-1 : ℝ) ^ n + altSum n N * truncRadicalNS n (N + 1) d) ^ (1 / (n : ℝ)) := by
  have hshift : (fun k => altCoeffR n N (k + 1)) = altCoeffR n (N + 1) := by
    funext k; unfold altCoeffR; congr 1; push_cast; ring
  have ha1_eq : altCoeffR n N 1 = altSum n N := by
    unfold altCoeffR; congr 1; push_cast; ring
  unfold truncRadicalNS
  rw [rollUpNS_succ, ha1_eq, hshift]

private theorem tendsto_succ_atTopS : Tendsto (fun d : ℕ => d + 1) atTop atTop :=
  tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)

/-- **The functional equation**, uniform in parity via `(-1)^n`. -/
theorem limitValNS_functional_eq {n : ℕ} (hn : 2 ≤ n) {N : ℝ} (hN : 2 ≤ N) :
    limitValNS n N = ((-1 : ℝ) ^ n + altSum n N * limitValNS n (N + 1)) ^ (1 / (n : ℝ)) := by
  have hN1 : 2 ≤ N + 1 := by linarith
  have hy0_pos : (0 : ℝ) < (-1 : ℝ) ^ n + altSum n N * limitValNS n (N + 1) := by
    have hk := altSum_shift_ge_one hn hN
    have hL1 := limitValNS_ge_one hn hN1
    have hanneg : 0 ≤ altSum n N := altSum_nonneg (by linarith : (1 : ℝ) ≤ N)
    have hmul : altSum n N * 1 ≤ altSum n N * limitValNS n (N + 1) :=
      mul_le_mul_of_nonneg_left hL1 hanneg
    nlinarith [hmul, hk]
  have hshift_tendsto : Tendsto (fun d => truncRadicalNS n N (d + 1)) atTop (𝓝 (limitValNS n N)) :=
    (limitValNS_tendsto hn hN).comp tendsto_succ_atTopS
  have heq : (fun d => truncRadicalNS n N (d + 1)) =
      (fun d => ((-1 : ℝ) ^ n + altSum n N * truncRadicalNS n (N + 1) d) ^ (1 / (n : ℝ))) := by
    funext d; exact stepS_identity N d
  rw [heq] at hshift_tendsto
  have haff : ContinuousAt (fun x : ℝ => (-1 : ℝ) ^ n + altSum n N * x) (limitValNS n (N + 1)) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
  have hcontAt : ContinuousAt
      (fun x : ℝ => ((-1 : ℝ) ^ n + altSum n N * x) ^ (1 / (n : ℝ))) (limitValNS n (N + 1)) :=
    haff.rpow_const (Or.inl (ne_of_gt hy0_pos))
  have hL4 : Tendsto (fun d => ((-1 : ℝ) ^ n + altSum n N * truncRadicalNS n (N + 1) d) ^
      (1 / (n : ℝ))) atTop
      (𝓝 (((-1 : ℝ) ^ n + altSum n N * limitValNS n (N + 1)) ^ (1 / (n : ℝ)))) :=
    hcontAt.tendsto.comp (limitValNS_tendsto hn hN1)
  exact tendsto_nhds_unique hshift_tendsto hL4

noncomputable def deficitS (n : ℕ) (N : ℝ) : ℝ := N - limitValNS n N

theorem deficitS_nonneg {n : ℕ} (hn : 2 ≤ n) {N : ℝ} (hN : 2 ≤ N) : 0 ≤ deficitS n N := by
  unfold deficitS; linarith [limitValNS_le hn hN]

theorem deficitS_le_ceiling {n : ℕ} (hn : 2 ≤ n) {N : ℝ} (hN : 2 ≤ N) :
    deficitS n N ≤ N - 1 := by
  unfold deficitS; linarith [limitValNS_ge_one hn hN]

/-- `N^n - L^n = (N-L) · S` with `S = ∑ i, N^i·L^{n-1-i}` (`geom_sum₂_mul`),
and `S ≥ (N^n-1)/(N-1)` termwise from `L ≥ 1` — fraction-free form. -/
private theorem geomSum_ge_of_ge_one {N x : ℝ} (hN0 : 0 ≤ N) (hx : 1 ≤ x) (n : ℕ) :
    (∑ i ∈ range n, N ^ i) ≤ ∑ i ∈ range n, N ^ i * x ^ (n - 1 - i) := by
  apply Finset.sum_le_sum
  intro i _
  have hxp : (1 : ℝ) ≤ x ^ (n - 1 - i) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hx (n - 1 - i)
    rwa [one_pow] at h
  have hNi : (0 : ℝ) ≤ N ^ i := by positivity
  calc N ^ i = N ^ i * 1 := (mul_one _).symm
    _ ≤ N ^ i * x ^ (n - 1 - i) := mul_le_mul_of_nonneg_left hxp hNi

private theorem geomFactor_ge_even' {N L : ℝ} (hN2 : 2 ≤ N) (hL1 : 1 ≤ L) (n : ℕ) :
    N ^ n - 1 ≤ (∑ i ∈ range n, N ^ i * L ^ (n - 1 - i)) * (N - 1) := by
  have hNge : (0 : ℝ) ≤ N := by linarith
  have hN1pos : (0 : ℝ) < N - 1 := by linarith
  have hsum_ge := geomSum_ge_of_ge_one hNge hL1 n
  have hgeom : (∑ i ∈ range n, N ^ i) * (N - 1) = N ^ n - 1 := by
    have h := geom_sum₂_mul N (1 : ℝ) n
    simpa using h
  have hmul := mul_le_mul_of_nonneg_right hsum_ge hN1pos.le
  linarith [hmul, hgeom]

private theorem factor_pow_sub (N L : ℝ) (n : ℕ) :
    (∑ i ∈ range n, N ^ i * L ^ (n - 1 - i)) * (N - L) = N ^ n - L ^ n :=
  geom_sum₂_mul N L n

/-- **The key global growth bound, even `n`.** Reproduces `HerschfeldClosure.lean`'s
`deficit_growth` ratio `(N+1)/(N-1)` exactly, from the factorization above
plus `altSum n N * (N+1) = N^n - 1` (the identity, even case). -/
theorem deficitS_growth_even {n : ℕ} (hn : 2 ≤ n) (hne : Even n) {N : ℝ} (hN : 2 ≤ N) :
    deficitS n N * (N + 1) ≤ deficitS n (N + 1) * (N - 1) := by
  have hNp1pos : (0 : ℝ) < N + 1 := by linarith
  have hL_ge1 := limitValNS_ge_one hn hN
  have hDnn : 0 ≤ deficitS n N := deficitS_nonneg hn hN
  have hsign : (-1 : ℝ) ^ n = 1 := hne.neg_one_pow
  have hFE := limitValNS_functional_eq hn hN
  rw [hsign] at hFE
  have hn_ne : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    linarith
  have hL1_nonneg : (0 : ℝ) ≤ 1 + altSum n N * limitValNS n (N + 1) := by
    have hL1' := limitValNS_ge_one hn (show 2 ≤ N + 1 by linarith)
    have hanneg : 0 ≤ altSum n N := altSum_nonneg (by linarith : (1 : ℝ) ≤ N)
    nlinarith [hL1', hanneg]
  have hLn : (limitValNS n N) ^ n = 1 + altSum n N * limitValNS n (N + 1) := by
    have hexp1 : (1 / (n : ℝ)) * (n : ℝ) = 1 := by field_simp
    rw [hFE, ← Real.rpow_natCast _ n, ← Real.rpow_mul hL1_nonneg, hexp1, Real.rpow_one]
  have hNn_eq : N ^ n = 1 + altSum n N * (N + 1) := by
    have hid := altSum_identity n N
    rw [hsign] at hid
    linarith [hid]
  have hsub : N ^ n - (limitValNS n N) ^ n = altSum n N * deficitS n (N + 1) := by
    unfold deficitS
    rw [hLn, hNn_eq]; ring
  have hfact := factor_pow_sub N (limitValNS n N) n
  have hNL : N - limitValNS n N = deficitS n N := rfl
  rw [hNL] at hfact
  have hfact2 : (∑ i ∈ range n, N ^ i * (limitValNS n N) ^ (n - 1 - i)) * deficitS n N =
      altSum n N * deficitS n (N + 1) := by linarith [hfact, hsub]
  have hSge := geomFactor_ge_even' hN hL_ge1 n
  have haltval : altSum n N * (N + 1) = N ^ n - 1 := by
    have hid := altSum_identity n N
    rw [hsign] at hid; linarith [hid]
  have hNnpos : (0 : ℝ) < N ^ n - 1 := by
    have h4 : (4 : ℝ) ≤ N ^ 2 := by nlinarith [hN]
    have hNn2 : N ^ 2 ≤ N ^ n := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ N) hn
    linarith [h4, hNn2]
  have hanpos : 0 < altSum n N := by
    by_contra hcon
    push_neg at hcon
    have hle0 : altSum n N * (N + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon hNp1pos.le
    linarith [haltval, hNnpos, hle0]
  have hstep1 : altSum n N * (N + 1) ≤
      (∑ i ∈ range n, N ^ i * (limitValNS n N) ^ (n - 1 - i)) * (N - 1) := by
    rw [haltval]; exact hSge
  have hstep2 : altSum n N * (N + 1) * deficitS n N ≤
      (∑ i ∈ range n, N ^ i * (limitValNS n N) ^ (n - 1 - i)) * (N - 1) * deficitS n N :=
    mul_le_mul_of_nonneg_right hstep1 hDnn
  have hreassoc : (∑ i ∈ range n, N ^ i * (limitValNS n N) ^ (n - 1 - i)) * (N - 1) *
      deficitS n N = altSum n N * deficitS n (N + 1) * (N - 1) := by
    rw [show (∑ i ∈ range n, N ^ i * (limitValNS n N) ^ (n - 1 - i)) * (N - 1) * deficitS n N =
        ((∑ i ∈ range n, N ^ i * (limitValNS n N) ^ (n - 1 - i)) * deficitS n N) * (N - 1) from
        by ring, hfact2]
  rw [hreassoc] at hstep2
  have hstep4 : altSum n N * ((N + 1) * deficitS n N) ≤
      altSum n N * (deficitS n (N + 1) * (N - 1)) := by
    have e1 : altSum n N * (N + 1) * deficitS n N = altSum n N * ((N + 1) * deficitS n N) := by
      ring
    have e2 : altSum n N * deficitS n (N + 1) * (N - 1) =
        altSum n N * (deficitS n (N + 1) * (N - 1)) := by ring
    rw [e1, e2] at hstep2
    exact hstep2
  have hfinal := le_of_mul_le_mul_left hstep4 hanpos
  have ecomm : (N + 1) * deficitS n N = deficitS n N * (N + 1) := by ring
  linarith [hfinal, ecomm]

private theorem quadS_step {n : ℕ} (hn : 2 ≤ n) (hne : Even n) {N₀ M : ℝ}
    (hN₀ : 2 ≤ N₀) (hM : 2 ≤ M)
    (ih : deficitS n N₀ * (M * (M - 1)) / (N₀ * (N₀ - 1)) ≤ deficitS n M) :
    deficitS n N₀ * ((M + 1) * M) / (N₀ * (N₀ - 1)) ≤ deficitS n (M + 1) := by
  have hMpos : (0 : ℝ) < M - 1 := by linarith
  have hN0pos : (0 : ℝ) < N₀ * (N₀ - 1) := by nlinarith
  have hratio_nonneg : (0 : ℝ) ≤ (M + 1) / (M - 1) := by positivity
  have hgrow : deficitS n M * (M + 1) / (M - 1) ≤ deficitS n (M + 1) := by
    rw [div_le_iff₀ hMpos]
    exact deficitS_growth_even hn hne hM
  have step : deficitS n N₀ * (M * (M - 1)) / (N₀ * (N₀ - 1)) * ((M + 1) / (M - 1)) ≤
      deficitS n M * ((M + 1) / (M - 1)) :=
    mul_le_mul_of_nonneg_right ih hratio_nonneg
  have eq1 : deficitS n N₀ * (M * (M - 1)) / (N₀ * (N₀ - 1)) * ((M + 1) / (M - 1)) =
      deficitS n N₀ * ((M + 1) * M) / (N₀ * (N₀ - 1)) := by
    field_simp
    ring
  have eq2 : deficitS n M * ((M + 1) / (M - 1)) = deficitS n M * (M + 1) / (M - 1) := by ring
  rw [eq1, eq2] at step
  exact le_trans step hgrow

theorem deficitS_quadratic_lower {n : ℕ} (hn : 2 ≤ n) (hne : Even n) {N₀ : ℝ} (hN₀ : 2 ≤ N₀) :
    ∀ j : ℕ, deficitS n N₀ * ((N₀ + (j : ℝ)) * (N₀ + (j : ℝ) - 1)) / (N₀ * (N₀ - 1)) ≤
      deficitS n (N₀ + (j : ℝ)) := by
  have hC0pos : (0 : ℝ) < N₀ * (N₀ - 1) := by nlinarith
  intro j
  induction j with
  | zero =>
    simp only [Nat.cast_zero, add_zero]
    rw [mul_div_assoc, div_self (ne_of_gt hC0pos), mul_one]
  | succ m ih =>
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hNm : (2 : ℝ) ≤ N₀ + (m : ℝ) := by linarith
    have hstep := quadS_step hn hne hN₀ hNm ih
    have hcast : (N₀ + ((m + 1 : ℕ) : ℝ)) = (N₀ + (m : ℝ)) + 1 := by push_cast; ring
    rw [hcast]
    have hsimp : (N₀ + (m : ℝ)) + 1 - 1 = N₀ + (m : ℝ) := by ring
    rw [hsimp]
    exact hstep

/-- **The closing theorem: `L(N) = N` exactly, for every even root order
`n ≥ 2`.** Same contradiction structure as `HerschfeldClosure.lean`: a
quadratic-in-`j` lower bound on `δ(N+j)` eventually exceeds the linear
ceiling `δ(N+j) ≤ N+j-1`. -/
theorem limitValNS_eq_self_even {n : ℕ} (hn : 2 ≤ n) (hne : Even n) {N : ℝ} (hN : 2 ≤ N) :
    limitValNS n N = N := by
  by_contra hne'
  have hlt : limitValNS n N < N := lt_of_le_of_ne (limitValNS_le hn hN) hne'
  have hδ0_pos : 0 < deficitS n N := by unfold deficitS; linarith
  have hN0pos : (0 : ℝ) < N * (N - 1) := by nlinarith
  obtain ⟨j, hj⟩ := exists_nat_gt (N * (N - 1) / deficitS n N - N)
  have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hNj : (2 : ℝ) ≤ N + (j : ℝ) := by linarith
  have hNjm1_pos : (0 : ℝ) < N + (j : ℝ) - 1 := by linarith
  have hlow := deficitS_quadratic_lower hn hne hN j
  have hceil := deficitS_le_ceiling hn hNj
  have hprod : N * (N - 1) < (N + (j : ℝ)) * deficitS n N := by
    have h1 : N * (N - 1) / deficitS n N < N + (j : ℝ) := by linarith
    rwa [div_lt_iff₀ hδ0_pos] at h1
  have hfinal : N + (j : ℝ) - 1 <
      deficitS n N * ((N + (j : ℝ)) * (N + (j : ℝ) - 1)) / (N * (N - 1)) := by
    rw [lt_div_iff₀ hN0pos]
    nlinarith [mul_lt_mul_of_pos_right hprod hNjm1_pos]
  linarith [hlow, hceil, hfinal]

/-! ## Part 4: the exact limit `L(N) = N`, odd root order

For odd `n` the identity gives `altSum n N * (N+1) = N^n + 1` instead of
`N^n - 1` — a constant gap of exactly `2` relative to the even case. This
means the per-step growth bound picks up an extra shrink factor
`shrinkFactor n N := 1 - 2/(N^n+1) = (N^n-1)/(N^n+1)` relative to the clean
ratio `(N+1)/(N-1)`. The product of these shrink factors over any number of
steps stays bounded below by a fixed positive constant (`1/2`, uniformly in
`N₀` and the step count) via a Weierstrass-type product-sum inequality
together with an elementary telescoping bound on `∑ 2/(N₀+i)^3`. This keeps
the deficit growth quadratic (merely scaled down by a fixed constant), which
still suffices to beat the linear ceiling in the closing contradiction. -/

/-- **Weierstrass-type product-sum inequality.** No direct match found in
Mathlib under `one_sub_sum_le_prod` / `Weierstrass` / `prod_one_sub`; proved
by hand via `Finset.induction_on`. -/
private theorem prod_one_sub_ge_one_sub_sum {ι : Type*} [DecidableEq ι] (x : ι → ℝ) :
    ∀ s : Finset ι, (∀ i ∈ s, 0 ≤ x i) → (∀ i ∈ s, x i ≤ 1) →
      1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert a s ha ih =>
    intro hx0 hx1
    have hx0' : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx0 i (Finset.mem_insert_of_mem hi)
    have hx1' : ∀ i ∈ s, x i ≤ 1 := fun i hi => hx1 i (Finset.mem_insert_of_mem hi)
    have hxa0 : 0 ≤ x a := hx0 a (Finset.mem_insert_self a s)
    have hxa1 : x a ≤ 1 := hx1 a (Finset.mem_insert_self a s)
    have ihs := ih hx0' hx1'
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hsum_nonneg : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hx0'
    have key : (1 - x a) * (1 - ∑ i ∈ s, x i) ≤ (1 - x a) * ∏ i ∈ s, (1 - x i) :=
      mul_le_mul_of_nonneg_left ihs (by linarith)
    have expand : (1 - x a) * (1 - ∑ i ∈ s, x i) =
        1 - x a - ∑ i ∈ s, x i + x a * ∑ i ∈ s, x i := by ring
    have hxa_sum_nonneg : 0 ≤ x a * ∑ i ∈ s, x i := mul_nonneg hxa0 hsum_nonneg
    nlinarith [key, expand, hxa_sum_nonneg]

/-- Elementary telescoping step: `2/k^3 ≤ 1/(k-1)^2 - 1/k^2` for `k ≥ 2`. -/
private theorem cube_reciprocal_step {k : ℝ} (hk : 2 ≤ k) :
    2 / k ^ 3 ≤ 1 / (k - 1) ^ 2 - 1 / k ^ 2 := by
  have hk1 : (0 : ℝ) < k - 1 := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  rw [← sub_nonneg]
  have heq : 1 / (k - 1) ^ 2 - 1 / k ^ 2 - 2 / k ^ 3 =
      (3 * k - 2) / ((k - 1) ^ 2 * k ^ 3) := by
    have hk0' : k ≠ 0 := ne_of_gt hk0
    have hk1' : k - 1 ≠ 0 := ne_of_gt hk1
    field_simp
    ring
  rw [heq]
  apply div_nonneg
  · linarith
  · positivity

/-- Uniform-in-`J` telescoped sum bound: `∑_{i<J} 2/(N₀+i)^3 ≤ 2/N₀^3 + 1/N₀^2`. -/
private theorem sum_two_over_cube_bound (N₀ : ℝ) (hN₀ : 2 ≤ N₀) :
    ∀ J : ℕ, ∑ i ∈ range J, 2 / (N₀ + (i : ℝ)) ^ 3 ≤ 2 / N₀ ^ 3 + 1 / N₀ ^ 2 := by
  have main : ∀ J : ℕ, ∑ i ∈ range (J + 1), 2 / (N₀ + (i : ℝ)) ^ 3 ≤
      2 / N₀ ^ 3 + 1 / N₀ ^ 2 - 1 / (N₀ + (J : ℝ)) ^ 2 := by
    intro J
    induction J with
    | zero =>
      simp only [zero_add, Finset.sum_range_one, Nat.cast_zero, add_zero]
      linarith
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hk : (2 : ℝ) ≤ N₀ + (m : ℝ) + 1 := by linarith
      have hstep := cube_reciprocal_step hk
      have heq1 : N₀ + (m : ℝ) + 1 - 1 = N₀ + (m : ℝ) := by ring
      rw [heq1] at hstep
      have hcastJ : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hcastJ]
      have hassoc : N₀ + ((m : ℝ) + 1) = N₀ + (m : ℝ) + 1 := by ring
      rw [hassoc]
      linarith [ih, hstep]
  intro J
  cases J with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  | succ m =>
    have hm := main m
    have hnn : (0 : ℝ) ≤ 1 / (N₀ + (m : ℝ)) ^ 2 := by positivity
    linarith [hm, hnn]

/-- The per-step shrink factor for odd `n`, relative to the clean
`(N+1)/(N-1)` ratio of the even case: `1 - 2/(N^n+1) = (N^n-1)/(N^n+1)`. -/
noncomputable def shrinkFactor (n : ℕ) (N : ℝ) : ℝ := 1 - 2 / (N ^ n + 1)

private theorem shrinkFactor_nonneg {n : ℕ} (hn : 2 ≤ n) {N : ℝ} (hN : 2 ≤ N) :
    0 ≤ shrinkFactor n N := by
  unfold shrinkFactor
  have hNnpos : (0 : ℝ) < N ^ n + 1 := by positivity
  rw [le_sub_iff_add_le, zero_add, div_le_one hNnpos]
  have h2 : (2 : ℝ) ≤ N ^ n := by
    have h4 : (4 : ℝ) ≤ N ^ 2 := by nlinarith
    have hNn2 : N ^ 2 ≤ N ^ n := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ N) hn
    linarith
  linarith

/-- **The key global growth bound, odd `n`.** Same factorization argument as
`deficitS_growth_even`, but `altSum n N * (N+1) = N^n + 1` (not `N^n - 1`)
picks up an extra `shrinkFactor n N = (N^n-1)/(N^n+1)` relative to the clean
ratio. -/
theorem deficitS_growth_odd {n : ℕ} (hn : 2 ≤ n) (hodd : Odd n) {N : ℝ} (hN : 2 ≤ N) :
    deficitS n N * (N + 1) * shrinkFactor n N ≤ deficitS n (N + 1) * (N - 1) := by
  have hNp1pos : (0 : ℝ) < N + 1 := by linarith
  have hL_ge1 := limitValNS_ge_one hn hN
  have hDnn : 0 ≤ deficitS n N := deficitS_nonneg hn hN
  have hsign : (-1 : ℝ) ^ n = -1 := hodd.neg_one_pow
  have hFE := limitValNS_functional_eq hn hN
  rw [hsign] at hFE
  have hn_ne : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    linarith
  have hkey := altSum_shift_ge_one hn hN
  rw [hsign] at hkey
  have hL1_nonneg : (0 : ℝ) ≤ -1 + altSum n N * limitValNS n (N + 1) := by
    have hL1' := limitValNS_ge_one hn (show 2 ≤ N + 1 by linarith)
    have hanneg : 0 ≤ altSum n N := altSum_nonneg (by linarith : (1 : ℝ) ≤ N)
    nlinarith [hL1', hanneg, hkey]
  have hLn : (limitValNS n N) ^ n = -1 + altSum n N * limitValNS n (N + 1) := by
    have hexp1 : (1 / (n : ℝ)) * (n : ℝ) = 1 := by field_simp
    rw [hFE, ← Real.rpow_natCast _ n, ← Real.rpow_mul hL1_nonneg, hexp1, Real.rpow_one]
  have hNn_eq : N ^ n = -1 + altSum n N * (N + 1) := by
    have hid := altSum_identity n N
    rw [hsign] at hid
    linarith [hid]
  have hsub : N ^ n - (limitValNS n N) ^ n = altSum n N * deficitS n (N + 1) := by
    unfold deficitS
    rw [hLn, hNn_eq]; ring
  have hfact := factor_pow_sub N (limitValNS n N) n
  have hNL : N - limitValNS n N = deficitS n N := rfl
  rw [hNL] at hfact
  have hfact2 : (∑ i ∈ range n, N ^ i * (limitValNS n N) ^ (n - 1 - i)) * deficitS n N =
      altSum n N * deficitS n (N + 1) := by linarith [hfact, hsub]
  have hSge := geomFactor_ge_even' hN hL_ge1 n
  have haltval : altSum n N * (N + 1) = N ^ n + 1 := by
    have hid := altSum_identity n N
    rw [hsign] at hid; linarith [hid]
  have hNnpos : (0 : ℝ) < N ^ n + 1 := by positivity
  have hanpos : 0 < altSum n N := by
    by_contra hcon
    push_neg at hcon
    have hle0 : altSum n N * (N + 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon hNp1pos.le
    linarith [haltval, hNnpos, hle0]
  have hstep2 : (N ^ n - 1) * deficitS n N ≤
      (∑ i ∈ range n, N ^ i * (limitValNS n N) ^ (n - 1 - i)) * (N - 1) * deficitS n N :=
    mul_le_mul_of_nonneg_right hSge hDnn
  have hreassoc : (∑ i ∈ range n, N ^ i * (limitValNS n N) ^ (n - 1 - i)) * (N - 1) *
      deficitS n N = altSum n N * deficitS n (N + 1) * (N - 1) := by
    rw [show (∑ i ∈ range n, N ^ i * (limitValNS n N) ^ (n - 1 - i)) * (N - 1) * deficitS n N =
        ((∑ i ∈ range n, N ^ i * (limitValNS n N) ^ (n - 1 - i)) * deficitS n N) * (N - 1) from
        by ring, hfact2]
  rw [hreassoc] at hstep2
  have hmul2 : (N ^ n - 1) * deficitS n N * (N + 1) ≤
      altSum n N * deficitS n (N + 1) * (N - 1) * (N + 1) :=
    mul_le_mul_of_nonneg_right hstep2 hNp1pos.le
  have hreassoc2 : altSum n N * deficitS n (N + 1) * (N - 1) * (N + 1) =
      (altSum n N * (N + 1)) * deficitS n (N + 1) * (N - 1) := by ring
  rw [hreassoc2, haltval] at hmul2
  have hshrink_eq : shrinkFactor n N = (N ^ n - 1) / (N ^ n + 1) := by
    unfold shrinkFactor
    have hNnpos' : (N ^ n + 1 : ℝ) ≠ 0 := ne_of_gt hNnpos
    field_simp
    ring
  rw [hshrink_eq, show deficitS n N * (N + 1) * ((N ^ n - 1) / (N ^ n + 1)) =
      deficitS n N * (N + 1) * (N ^ n - 1) / (N ^ n + 1) from by ring,
      div_le_iff₀ hNnpos]
  have hgoal_eq : deficitS n N * (N + 1) * (N ^ n - 1) =
      (N ^ n - 1) * deficitS n N * (N + 1) := by ring
  have htarget_eq : deficitS n (N + 1) * (N - 1) * (N ^ n + 1) =
      (N ^ n + 1) * deficitS n (N + 1) * (N - 1) := by ring
  rw [hgoal_eq, htarget_eq]
  exact hmul2

/-- **The product of shrink factors stays uniformly bounded below by `1/2`**,
for every `N₀ ≥ 2` and every step count `j` — the constant is independent of
both. Combines `prod_one_sub_ge_one_sub_sum` with `sum_two_over_cube_bound`. -/
private theorem prodShrink_ge_half {n : ℕ} (hn : 2 ≤ n) (hodd : Odd n) {N₀ : ℝ} (hN₀ : 2 ≤ N₀)
    (j : ℕ) : (1 : ℝ) / 2 ≤ ∏ i ∈ range j, shrinkFactor n (N₀ + (i : ℝ)) := by
  have hn3 : 3 ≤ n := by obtain ⟨k, hk⟩ := hodd; omega
  have hprod_eq : ∏ i ∈ range j, shrinkFactor n (N₀ + (i : ℝ)) =
      ∏ i ∈ range j, (1 - 2 / ((N₀ + (i : ℝ)) ^ n + 1)) := by
    apply Finset.prod_congr rfl
    intro i _
    rfl
  have hy0 : ∀ i ∈ range j, (0 : ℝ) ≤ 2 / ((N₀ + (i : ℝ)) ^ n + 1) := by
    intro i _; positivity
  have hy1 : ∀ i ∈ range j, 2 / ((N₀ + (i : ℝ)) ^ n + 1) ≤ 1 := by
    intro i _
    have hNi : (2 : ℝ) ≤ N₀ + (i : ℝ) := by
      have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i; linarith
    have h1 : (1 : ℝ) ≤ (N₀ + (i : ℝ)) ^ n := by
      calc (1 : ℝ) = 1 ^ n := (one_pow n).symm
        _ ≤ (N₀ + (i : ℝ)) ^ n := pow_le_pow_left₀ (by norm_num) (by linarith) n
    have hden : (0 : ℝ) < (N₀ + (i : ℝ)) ^ n + 1 := by positivity
    rw [div_le_one hden]
    linarith
  have hweier :=
    prod_one_sub_ge_one_sub_sum (fun (i : ℕ) => 2 / ((N₀ + (i : ℝ)) ^ n + 1)) (range j) hy0 hy1
  have hxbound : ∀ i ∈ range j, 2 / ((N₀ + (i : ℝ)) ^ n + 1) ≤ 2 / (N₀ + (i : ℝ)) ^ 3 := by
    intro i _
    have hNi : (2 : ℝ) ≤ N₀ + (i : ℝ) := by
      have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i; linarith
    have hpow : (N₀ + (i : ℝ)) ^ 3 ≤ (N₀ + (i : ℝ)) ^ n :=
      pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ N₀ + (i : ℝ)) hn3
    have hden1 : (0 : ℝ) < (N₀ + (i : ℝ)) ^ n + 1 := by positivity
    have hden2 : (0 : ℝ) < (N₀ + (i : ℝ)) ^ 3 := by positivity
    rw [div_le_div_iff₀ hden1 hden2]
    nlinarith [hpow]
  have hsum_le : ∑ i ∈ range j, 2 / ((N₀ + (i : ℝ)) ^ n + 1) ≤
      ∑ i ∈ range j, 2 / (N₀ + (i : ℝ)) ^ 3 := Finset.sum_le_sum hxbound
  have hsumbound := sum_two_over_cube_bound N₀ hN₀ j
  have hB_le_half : 2 / N₀ ^ 3 + 1 / N₀ ^ 2 ≤ (1 : ℝ) / 2 := by
    have hN0pos : (0 : ℝ) < N₀ := by linarith
    rw [← sub_nonneg]
    have heq : (1 : ℝ) / 2 - (2 / N₀ ^ 3 + 1 / N₀ ^ 2) =
        (N₀ ^ 3 - 2 * N₀ - 4) / (2 * N₀ ^ 3) := by
      have hN0ne : (N₀ : ℝ) ≠ 0 := ne_of_gt hN0pos
      field_simp
      ring
    rw [heq]
    have hpoly : N₀ ^ 3 - 2 * N₀ - 4 = (N₀ - 2) * (N₀ ^ 2 + 2 * N₀ + 2) := by ring
    have hfactor_nonneg : (0 : ℝ) ≤ (N₀ - 2) * (N₀ ^ 2 + 2 * N₀ + 2) := by
      apply mul_nonneg (by linarith)
      nlinarith [sq_nonneg (N₀ + 1)]
    rw [hpoly]
    apply div_nonneg hfactor_nonneg
    positivity
  have hsum_le_half : ∑ i ∈ range j, 2 / ((N₀ + (i : ℝ)) ^ n + 1) ≤ 1 / 2 := by
    linarith [hsum_le, hsumbound, hB_le_half]
  rw [hprod_eq]
  linarith [hweier, hsum_le_half]

/-- Single-step telescoping bound, odd `n`, carrying an abstract accumulated
shrink-factor product `P` alongside the quadratic ratio — mirrors `quadS_step`
with the extra multiplicative factor threaded through. -/
private theorem quadS_step_odd {n : ℕ} (hn : 2 ≤ n) (hodd : Odd n) {N₀ M P : ℝ}
    (hN₀ : 2 ≤ N₀) (hM : 2 ≤ M)
    (ih : deficitS n N₀ * (M * (M - 1)) / (N₀ * (N₀ - 1)) * P ≤ deficitS n M) :
    deficitS n N₀ * ((M + 1) * M) / (N₀ * (N₀ - 1)) * (P * shrinkFactor n M) ≤
      deficitS n (M + 1) := by
  have hMpos : (0 : ℝ) < M - 1 := by linarith
  have hN0pos : (0 : ℝ) < N₀ * (N₀ - 1) := by nlinarith
  have hshrink_nonneg := shrinkFactor_nonneg hn hM
  have hratio_nonneg : (0 : ℝ) ≤ (M + 1) / (M - 1) * shrinkFactor n M :=
    mul_nonneg (by positivity) hshrink_nonneg
  have hgrow := deficitS_growth_odd hn hodd hM
  have hgrow' : deficitS n M * ((M + 1) / (M - 1) * shrinkFactor n M) ≤ deficitS n (M + 1) := by
    have heq : deficitS n M * ((M + 1) / (M - 1) * shrinkFactor n M) =
        (deficitS n M * (M + 1) * shrinkFactor n M) / (M - 1) := by
      have hMne : (M - 1 : ℝ) ≠ 0 := ne_of_gt hMpos
      field_simp
      ring
    rw [heq, div_le_iff₀ hMpos]
    exact hgrow
  have step : deficitS n N₀ * (M * (M - 1)) / (N₀ * (N₀ - 1)) * P *
      ((M + 1) / (M - 1) * shrinkFactor n M) ≤
      deficitS n M * ((M + 1) / (M - 1) * shrinkFactor n M) :=
    mul_le_mul_of_nonneg_right ih hratio_nonneg
  have eq1 : deficitS n N₀ * (M * (M - 1)) / (N₀ * (N₀ - 1)) * P *
      ((M + 1) / (M - 1) * shrinkFactor n M) =
      deficitS n N₀ * ((M + 1) * M) / (N₀ * (N₀ - 1)) * (P * shrinkFactor n M) := by
    have hMne : (M - 1 : ℝ) ≠ 0 := ne_of_gt hMpos
    have hN0ne : (N₀ * (N₀ - 1) : ℝ) ≠ 0 := ne_of_gt hN0pos
    field_simp
    ring
  rw [eq1] at step
  exact le_trans step hgrow'

/-- **Quadratic-in-`j` lower bound on the deficit, odd `n`** — same shape as
`deficitS_quadratic_lower`, carrying the accumulated shrink-factor product
`∏ i < j, shrinkFactor n (N₀+i)` alongside the quadratic ratio. -/
theorem deficitS_quadratic_lower_odd {n : ℕ} (hn : 2 ≤ n) (hodd : Odd n) {N₀ : ℝ}
    (hN₀ : 2 ≤ N₀) :
    ∀ j : ℕ, deficitS n N₀ * ((N₀ + (j : ℝ)) * (N₀ + (j : ℝ) - 1)) / (N₀ * (N₀ - 1)) *
        (∏ i ∈ range j, shrinkFactor n (N₀ + (i : ℝ))) ≤ deficitS n (N₀ + (j : ℝ)) := by
  have hC0pos : (0 : ℝ) < N₀ * (N₀ - 1) := by nlinarith
  intro j
  induction j with
  | zero =>
    simp only [Nat.cast_zero, add_zero, range_zero, Finset.prod_empty, mul_one]
    rw [mul_div_assoc, div_self (ne_of_gt hC0pos), mul_one]
  | succ m ih =>
    have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hNm : (2 : ℝ) ≤ N₀ + (m : ℝ) := by linarith
    have hstep := quadS_step_odd hn hodd hN₀ hNm ih
    have hcast : (N₀ + ((m + 1 : ℕ) : ℝ)) = (N₀ + (m : ℝ)) + 1 := by push_cast; ring
    have hprod_succ : ∏ i ∈ range (m + 1), shrinkFactor n (N₀ + (i : ℝ)) =
        (∏ i ∈ range m, shrinkFactor n (N₀ + (i : ℝ))) * shrinkFactor n (N₀ + (m : ℝ)) :=
      Finset.prod_range_succ _ m
    rw [hcast, hprod_succ]
    have hsimp : (N₀ + (m : ℝ)) + 1 - 1 = N₀ + (m : ℝ) := by ring
    rw [hsimp]
    exact hstep

/-- **The closing theorem: `L(N) = N` exactly, for every odd root order
`n ≥ 2` (i.e. `n ≥ 3`).** Same contradiction structure as
`limitValNS_eq_self_even`, with the extra fixed factor `1/2` from
`prodShrink_ge_half` absorbed into a doubled threshold for `j`. -/
theorem limitValNS_eq_self_odd {n : ℕ} (hn : 2 ≤ n) (hodd : Odd n) {N : ℝ} (hN : 2 ≤ N) :
    limitValNS n N = N := by
  by_contra hne'
  have hlt : limitValNS n N < N := lt_of_le_of_ne (limitValNS_le hn hN) hne'
  have hδ0_pos : 0 < deficitS n N := by unfold deficitS; linarith
  have hN0pos : (0 : ℝ) < N * (N - 1) := by nlinarith
  obtain ⟨j, hj⟩ := exists_nat_gt (2 * (N * (N - 1) / deficitS n N) - N)
  have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hNj : (2 : ℝ) ≤ N + (j : ℝ) := by linarith
  have hNjm1_pos : (0 : ℝ) < N + (j : ℝ) - 1 := by linarith
  have hlowraw := deficitS_quadratic_lower_odd hn hodd hN j
  have hprodhalf := prodShrink_ge_half hn hodd hN j
  have hbase_nonneg :
      (0 : ℝ) ≤ deficitS n N * ((N + (j : ℝ)) * (N + (j : ℝ) - 1)) / (N * (N - 1)) := by
    apply div_nonneg
    · apply mul_nonneg (deficitS_nonneg hn hN)
      nlinarith [hNj, hNjm1_pos]
    · linarith [hN0pos]
  have hlow : deficitS n N * ((N + (j : ℝ)) * (N + (j : ℝ) - 1)) / (N * (N - 1)) * (1 / 2) ≤
      deficitS n (N + (j : ℝ)) := by
    have hmul : deficitS n N * ((N + (j : ℝ)) * (N + (j : ℝ) - 1)) / (N * (N - 1)) * (1 / 2) ≤
        deficitS n N * ((N + (j : ℝ)) * (N + (j : ℝ) - 1)) / (N * (N - 1)) *
          (∏ i ∈ range j, shrinkFactor n (N + (i : ℝ))) :=
      mul_le_mul_of_nonneg_left hprodhalf hbase_nonneg
    linarith [hmul, hlowraw]
  have hceil := deficitS_le_ceiling hn hNj
  have hprod : 2 * (N * (N - 1)) < (N + (j : ℝ)) * deficitS n N := by
    have h1 : 2 * (N * (N - 1) / deficitS n N) < N + (j : ℝ) := by linarith
    have heq : 2 * (N * (N - 1) / deficitS n N) = (2 * (N * (N - 1))) / deficitS n N := by ring
    rw [heq] at h1
    rwa [div_lt_iff₀ hδ0_pos] at h1
  have hfinal : N + (j : ℝ) - 1 <
      deficitS n N * ((N + (j : ℝ)) * (N + (j : ℝ) - 1)) / (N * (N - 1)) * (1 / 2) := by
    have hgoal_equiv : N + (j : ℝ) - 1 <
        deficitS n N * ((N + (j : ℝ)) * (N + (j : ℝ) - 1)) / (N * (N - 1)) * (1 / 2) ↔
        2 * (N + (j : ℝ) - 1) < deficitS n N * ((N + (j : ℝ)) * (N + (j : ℝ) - 1)) / (N * (N - 1)) := by
      constructor <;> intro h <;> linarith
    rw [hgoal_equiv, lt_div_iff₀ hN0pos]
    nlinarith [mul_lt_mul_of_pos_right hprod hNjm1_pos]
  linarith [hlow, hceil, hfinal]

end RamanujanNested
