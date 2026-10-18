import RamanujanNested.Defs

/-!
# IdentityChain.lean — Appendix A.1, Algorithm 3

"Verification of the identity chain": for an integer target `N ≥ 2` and depth
`d`, define `R_{d+1} = N + d` and, for `k` from `d` down to `1`,
`R_k = √(1 + (N+k-2)·R_{k+1})`. The paper claims (by "a direct computation")
that `R_k = N + k - 1` for every `k`, in particular `R_1 = N`.

Rather than encode the backward loop as a genuinely recursive Lean function
(which would just duplicate `rollUp` with a different coefficient/seed
convention), we formalize the claim exactly the way the paper states it: the
CLOSED FORM `R_k := N + k - 1` is exhibited, and we prove it satisfies the
stated recursion at every step. This is "a direct computation shows that
R_k = N+k-1", made precise and machine-checked.
-/

namespace RamanujanNested

/-- The closed form claimed by Algorithm 3. -/
noncomputable def chainClosedForm (N k : ℕ) : ℝ := (N : ℝ) + (k : ℝ) - 1

/-- The base case: `R_{d+1} = N + d`, matching Algorithm 3's initialization. -/
theorem chain_base (N d : ℕ) : chainClosedForm N (d + 1) = (N : ℝ) + (d : ℝ) := by
  unfold chainClosedForm
  push_cast
  ring

/-- **Algorithm 3, the identity chain.** The closed form `R_k = N+k-1` satisfies
the recursion `R_k = √(1 + (N+k-2)·R_{k+1})` for every `N ≥ 2` and every `k`
(the algebraic identity underneath, `(m-1)² = 1 + (m-2)·m` with `m = N+k`,
holds unconditionally in `k`; only `N ≥ 2` is needed so that `N+k-1 ≥ 0` and the
square root can be inverted). In particular (`k = 1`) this gives `R_1 = N`. -/
theorem chain_satisfies_recursion (N k : ℕ) (hN : 2 ≤ N) :
    chainClosedForm N k =
      Real.sqrt (1 + ((N : ℝ) + (k : ℝ) - 2) * chainClosedForm N (k + 1)) := by
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hpos : (0 : ℝ) ≤ (N : ℝ) + (k : ℝ) - 1 := by linarith
  have hsucc : chainClosedForm N (k + 1) = (N : ℝ) + (k : ℝ) := by
    unfold chainClosedForm; push_cast; ring
  rw [hsucc]
  have hcore : 1 + ((N : ℝ) + (k : ℝ) - 2) * ((N : ℝ) + (k : ℝ)) =
      ((N : ℝ) + (k : ℝ) - 1) ^ 2 := by ring
  unfold chainClosedForm
  rw [hcore]
  exact (Real.sqrt_sq hpos).symm

/-- In particular, `R_1 = N`: the identity chain closes exactly at the target,
which is the numerical phenomenon documented in Table 1 (the "Rolling
construction" column hitting the target `N` exactly at every depth). Holds for
every `N`, not only `N ≥ 2` — unlike `chain_satisfies_recursion`, no square
root needs inverting here. -/
theorem chain_hits_target (N : ℕ) :
    chainClosedForm N 1 = (N : ℝ) := by
  unfold chainClosedForm
  push_cast
  ring

end RamanujanNested
