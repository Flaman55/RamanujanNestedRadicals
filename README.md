# RamanujanNested

A Lean 4 / Mathlib formalization accompanying the paper **"Nested Radicals of
Ramanujan's Type with Arbitrary Coefficient Sequences"** (A. Flamandzki),
plus original extensions of the paper's own general framework to a case the
paper itself does not establish.

Builds cleanly against `lake build`, zero `sorry`.

The paper itself has been revised to a second version incorporating what this
formalization effort found (see "Errors this formalization caught" below).
It is published on Zenodo: <https://zenodo.org/records/18071173>
(DOI: 10.5281/zenodo.18071173), and that version's own new "Formal
Verification" section points back to this repository.

## What this repository formally verifies

The paper studies the recursion

```
R_k = √(1 + a_k · R_{k+1})
```

for an arbitrary coefficient sequence `(a_k)`. The classical Ramanujan
radical is the instance `a_k = k+1` (equivalently `N = 3` of the family
below), converging to `3`; the related sequence `a_k = k` is a *different*
instance (`N = 2`) converging to `2`, not to the classical value — see the
next section.

**Faithful to the paper (Section 4.1, Lemma 1, Appendix A):**

- **Boundedness and monotonicity** (`Bounds.lean`, `Monotone.lean`): if
  `a_k ≤ A` for a fixed ceiling `A`, every truncation of the radical lies in
  `[0, r*]` where `r* = (A+√(A²+4))/2`; if additionally `a_k ≥ 0`, the
  truncated sequence is monotone increasing in depth.
- **Convergence** (`Convergence.lean`): combining the two above, the
  truncated radical has a finite limit as depth `→ ∞` — the paper's actual
  stated conclusion for its main sufficient condition.
- **Lemma 1 — controlled negative coefficients** (`ControlledNegative.lean`):
  coefficients may dip negative (down to `-A₋`, `A₋ ≤ 1/r*`) and the radicand
  at every step is guaranteed nonnegative — made precise against Lean's
  `Real.sqrt`, which is total and would otherwise silently mask a
  well-definedness failure.
- **Algorithm 3, the closed-form identity chain** (`IdentityChain.lean`):
  `R_k = N+k-1` satisfies the recursion exactly, for any target `N ≥ 2`.
- **Algorithm 4, the general inverse construction** (`Reconstruction.lean`):
  for *any* target profile `R`, the coefficient `(R_k²-1)/R_{k+1}` makes `R`
  satisfy the recursion; Algorithm 3 is recovered as the special case
  `R_k = N+k-1`.
- **The oscillatory coefficient family** (`Oscillatory.lean`,
  `a_k = 1 + α sin k`, Appendix A.2): the paper's informal "provided α
  satisfies the admissibility constraints of Lemma 1" is made an explicit,
  checkable inequality (`α ≤ 1/r*(1+α)`) and discharged concretely at
  `α = 1/10`.
- **Arbitrary root order** (`NthRootChain.lean`): Section 4.1's boundedness,
  monotonicity and convergence result, generalized from `Real.sqrt` to
  `R_k = (1+a_k R_{k+1})^{1/n}` for any fixed `n ≥ 2`, for any bounded
  sequence `0 ≤ a_k ≤ A`.
- **Unbounded linear family, any root order** (`LinearChainNthRoot.lean`):
  existence of a limit for `linearCoeff m N` (slope `m ≥ 1`), at any root
  order `n ≥ 2`, combining `LinearChain.lean`'s moving-ceiling technique with
  `NthRootChain.lean`'s `rollUpN`.
- **The same, every slope and the tight bound** (`LinearChainGeneralNthRoot.lean`,
  `LinearChainTightNthRoot.lean`): existence for every `m > 0` (`L ≤ N+1`) and,
  for `0 < m ≤ 1`, the tight shift `L ≤ N+s(m)`, both at any root order `n ≥ 2`.
- **Primes, any root order** (`PrimeChainNthRoot.lean`): existence of a limit
  for `a_k = p_k` at any root order `n ≥ 2`, generalizing `PrimeChain.lean`'s
  geometric moving-ceiling argument.
- **Oscillatory family, any root order** (`OscillatoryNthRoot.lean`): the
  small-amplitude case is a direct corollary of `NthRootChain.lean`, no new
  argument needed.
- **Exact-target radical, any root order** (`TargetRadicalNthRoot.lean`):
  the constant-coefficient radical of `TargetRadical.lean` converging to a
  prescribed target `t` exactly generalizes to any root order `n ≥ 2`, via
  `targetCoeffN n t = (t^n-1)/t` and a generalized contraction rate
  `1-1/t^n` — unlike `IdentityChain.lean`, no `n=2`-specific obstruction.
- **The classical unbounded family, any root order** (`IdentityChainNthRoot.lean`):
  `IdentityChain.lean`, `UnboundedChain.lean` and `HerschfeldClosure.lean`
  generalized to any `n ≥ 2` in one file, since the even/odd cases differ
  only by a sign: `x=-1` is a root of exactly one of `x^n-1`, `x^n+1`
  depending on parity, giving one coefficient polynomial `altSum n x` and
  one identity valid for every `n`. Existence of a limit holds for every
  `n ≥ 2`; the exact value `L(N) = N` is proven for every `n ≥ 2`, EVEN and
  ODD alike — the odd case needed an extra ingredient (a fixed-constant
  lower bound on an infinite product of per-step shrink factors, via a
  hand-proved Weierstrass-type inequality) beyond the deficit-growth
  argument that closes the even case outright.

## Errors this formalization caught (now fixed in v2 of the paper)

Trying to state the paper's claims precisely enough to formalize them
surfaced two genuine issues in the original text — not literature-based
concerns, but concrete, checkable mistakes:

1. **A false attribution in Section 5.1.** The paper claimed the classical
   Ramanujan radical converges "by the general boundedness results
   established in Section 4.1." That theorem requires a fixed ceiling
   `a_k ≤ A`; the classical coefficients `a_k = k+1` have no such ceiling, so
   the attribution does not literally hold. Formalizing Section 4.1's actual
   hypothesis (`Bounds.lean`) is what exposed this — the gap was invisible
   until someone had to write down exactly what "the boundedness results"
   require. `UnboundedChain.lean` and `HerschfeldClosure.lean` (below) supply
   the missing proof instead of just flagging the hole.

2. **An indexing error in the paper's own displayed formula.** The
   introduction's headline equation,
   `R = √(1 + √(1 + 2√(1 + 3√(1 + ⋯))))`, has one extra layer relative to the
   well-known Ramanujan identity `3 = √(1+2√(1+3√(1+4√(1+⋯))))` — the paper's
   version wraps an additional `√(1+1·(⋯))` around the genuine classical
   radical. Since the inner expression already equals `3`, the paper's own
   formula evaluates to `√(1+3) = 2`, not `3`. This surfaced while integrating
   the Lean results back into the paper text (Section 5.1 stated
   `a_k = k`, which is consistent with the miscounted formula but not with
   the classical value) — checked by direct computation against the standard
   identity, not from secondary literature. Both the formula and the
   `a_k = k` attribution are corrected in v2.

## The unbounded-coefficient gap, and what this repository does about it

- **`TargetRadical.lean`** — sidesteps the gap rather than closing it. A
  *constant* coefficient `a = t - 1/t` is shown to make the radical converge
  to the target `t` exactly, with an explicit geometric error bound, using
  only the already-proven bounded-coefficient machinery. A different,
  structurally simpler, faster-converging construction reaching the same
  targets — not a fix for the classical radical itself.
- **`UnboundedChain.lean`** — extends Section 4.1 to the specific unbounded
  family `a_k = N+k-2` (the classical radical is `N=3`; `a_k=k` is `N=2`). A
  *moving-ceiling* induction (the bound at depth `d` is `N` itself, not a
  fixed constant) proves the truncated radical has a finite limit `L ≤ N`.
  Also formalizes Appendix A.1's Table 3 ("tail-independence") discussion:
  `rollUp_classicalCoeff_hits_target` restates `IdentityChain.lean`'s closed
  form as the exact `rollUp`-level identity `rollUp (classicalCoeff N) (N+d) d
  = N`, and `rollUp_classicalCoeff_le_of_tail_le` combines it with
  `Monotone.lean`'s new `rollUp_mono_seed` (monotonicity in the tail *seed*,
  complementing the existing monotonicity in depth) to show any tail policy
  `T(d) ≤ N+d` gives `rollUp (classicalCoeff N) T d ≤ N` — exactly the
  informal claim the table makes about all five tail policies it tabulates.
- **`HerschfeldClosure.lean`** — closes the gap for this family. Deriving a
  functional equation `L(N) = √(1+(N-1)·L(N+1))` from the recursion in the
  limit, then a deficit recursion and a global multiplicative growth bound
  (`δ(N+1) ≥ δ(N)·(N+1)/(N-1)`, valid everywhere, no arbitrary cutoff), the
  deficit `δ(N) = N - L(N)` is shown to grow quadratically in the step count
  against a merely linear ceiling — forcing `δ ≡ 0`. **`limitVal_eq_self`
  proves `L(N) = N` exactly** for this family: a genuine (if not previously
  published, to the author's knowledge) convergence theorem in the spirit of
  Herschfeld's classical result on infinite nested radicals, proved from
  scratch rather than cited.

The sequence `a_k = k` is already covered directly, with no reindexing
needed: it is exactly the `N = 2` instance of `a_k = N+k-2`, so
`HerschfeldClosure.lean`'s `limitVal_eq_self` applied at `N = 2` gives
`a_k = k` converging to `2`.

- **`PrimeChain.lean`** — an existence-only answer for the prime-coefficient
  example (`a_k = p_k`, Appendix A.2), the one case with a genuinely
  different, non-linear growth shape that the `N+k-2` family's technique
  doesn't reach (primes have no algebraic self-similarity under shifting).
  A general lemma, `rollUp_geomBounded`, shows that ANY coefficient sequence
  growing at most geometrically (`a_k ≤ r^k` for some fixed `r > 1`) already
  has a genuine, depth-independent ceiling, via a moving bound `A·r^i` that
  closes to a fixed constant at the top level. Primes satisfy `p_k ≤ 4^k`
  (`nth_prime_le_four_pow`), itself proved from Bertrand's postulate
  (Mathlib's `Nat.bertrand`). Result: **`primeRadical_converges`** — the
  truncated radical for `a_k = p_k` has SOME finite limit. Unlike
  `HerschfeldClosure.lean`, this does not pin down the exact value — existence
  is a substantially lower bar, and it's the bar the paper itself leaves open
  for this case.

With `PrimeChain.lean`, every coefficient family the paper mentions by name
now has at least an existence-of-convergence result; only the *exact value*
for `a_k = p_k` remains open, as it does in the paper itself.

- **`LinearChain.lean`** — generalizes `UnboundedChain.lean` from slope
  exactly `1` (`a_k = N+k-2`) to any slope `m ≥ 1`
  (`linearCoeff m N k = N+m(k-2)`), reusing the same moving-ceiling technique
  with a ceiling that shifts by `m` per layer instead of by a fixed `1`.
  `HerschfeldClosure.lean`'s exact-value argument only balances at `m² = 1`,
  so slope `1` remains the only slope with a known closed-form limit;
  `linearRadical_converges` gives existence only for general `m ≥ 1`, the
  same weaker guarantee as `PrimeChain.lean`. Motivation: not from the paper
  itself, but from checking whether a literature family with a *different*
  linear slope — Kusniec's difference-of-oblongs Radiciatory, coefficients
  linear in depth with slope `q-1` — reduces to the paper's framework. It
  does, for every `q ≥ 2`, with no new proof needed per value of `q`.

- **`LinearChainGeneral.lean`** — closes the remaining `0 < m < 1` range
  (i.e. `1 < q < 2` for the oblong family), and in fact covers all `m > 0`
  in one argument, via a looser ceiling `C(N) = N+1` in place of `C(N) = N`.
  The key inequality reduces to `0 ≤ N+m+m²`, unconditionally true for
  `m > 0` — no case split needed. Bound is weaker (`L ≤ N+1` instead of
  `L ≤ N`); use `LinearChain.lean` instead whenever `m ≥ 1` for the tight
  bound. Existence of a limit is now known across the entire positive-slope
  range, and Kusniec's oblong family is covered for every `q > 1`.

- **`LinearChainTight.lean`** — replaces `LinearChainGeneral.lean`'s loose
  `+1` slack with the exact minimal shift `s(m) = (√(5m²+4)-3m)/2`, the
  positive root of the equality case `s²+3ms+m²=1`. Gives the tightest bound
  possible for every `m` in `(0,1]`, `L ≤ N+s(m)`, matching `L ≤ N` exactly at
  `m=1`. Together with `LinearChain.lean`, this closes the entire
  positive-slope range with no remaining gap and the best bound available at
  every slope.

- **`NthRootChain.lean`** — a different axis of generalization: instead of
  the coefficients, the root order. `rollUpN n a T d` is the recursion
  `R_k = (1+a_k R_{k+1})^{1/n}` for any fixed root order `n ≥ 2`, and
  `truncRadicalN_converges` gives boundedness, monotonicity and convergence
  for ANY `n ≥ 2` together with ANY bounded sequence `0 ≤ a_k ≤ A` — the
  `Convergence.lean` conclusion, now for every root order at once. Mitra
  (arXiv:2404.04051) states a general-`n` identity schematically but proves
  convergence only for `n = 3` (cube roots); this covers arbitrary `n` for
  the bounded-coefficient case. The first file in this project to use
  `Real.rpow` instead of `Real.sqrt`.

- **`LinearChainNthRoot.lean`** — combines `LinearChain.lean` with
  `NthRootChain.lean`: existence of a limit for the unbounded linear family
  `linearCoeff m N` (slope `m ≥ 1`), at any root order `n ≥ 2`, via the same
  moving-ceiling technique, run against `rollUpN`. `n = 2` recovers
  `LinearChain.lean`'s own key inequality exactly, with no case split needed
  on `n`.

- **`LinearChainGeneralNthRoot.lean`** — the same generalization for
  `LinearChainGeneral.lean`: existence for EVERY slope `m > 0`, at any root
  order `n ≥ 2`, bound `L ≤ N+1`.

- **`LinearChainTightNthRoot.lean`** — the same generalization for
  `LinearChainTight.lean`: existence for `0 < m ≤ 1`, at any root order
  `n ≥ 2`, keeping the same tight shift `s(m) = (√(5m²+4)-3m)/2` (no longer
  claimed optimal at `n ≥ 3`, only valid).

- **`PrimeChainNthRoot.lean`** — generalizes `PrimeChain.lean`'s geometric
  moving-ceiling argument to any root order `n ≥ 2`: existence of a limit for
  `a_k = p_k`, same hypotheses and concrete instance (`r=4, A=17`) as
  `PrimeChain.lean`.

- **`OscillatoryNthRoot.lean`** — the small-amplitude oscillatory family
  (`0 ≤ α ≤ 1`) is bounded, so this is a one-line corollary of
  `NthRootChain.lean`'s `truncRadicalN_converges`.

- **`TargetRadicalNthRoot.lean`** — generalizes `TargetRadical.lean`'s
  constant-coefficient exact-target radical to any root order `n ≥ 2`.
  `targetCoeffN n t = (t^n-1)/t` solves the fixed-point equation `1+a·t=t^n`
  for any `n` (only ever solving for one constant, not a whole sequence, so
  unlike `IdentityChain.lean` it has no `n=2`-specific obstruction);
  `targetRadicalN_tendsto` proves convergence to `t` exactly via a
  generalized contraction rate `ρ_n=1-1/t^n` (numerically checked against
  the true asymptotic rate `(1-1/t^n)/n`; this bound is valid but not tight,
  same as the `n=2` case).

- **`IdentityChainNthRoot.lean`** — generalizes the classical unbounded
  family `R_k = N+k-1` from `n=2` to any root order `n ≥ 2`. The even and
  odd cases turn out to differ only by a sign, not by structure: `x=-1` is a
  root of exactly one of `x^n-1` (even `n`) or `x^n+1` (odd `n`), giving a
  single alternating-sign coefficient polynomial `altSum n x` and a single
  identity `R_k^n = (-1)^n + altSum n R_k · R_{k+1}` valid for every `n`.
  Existence of a finite limit `L(N) ∈ [1,N]` (`truncRadicalNS_converges`) is
  proven for every `n ≥ 2`, both parities — note the canonical seed here is
  `1`, not `0`: for odd `n` the seed `0` genuinely makes the radicand go
  negative, which is exactly why the earlier exploration of this family (for
  the linear/unbounded cases) needed a different starting point. The exact
  value `L(N) = N` is now proven for EVERY `n ≥ 2`, both parities:

  - **Even `n`** (`limitValNS_eq_self_even`): the same deficit-growth
    telescoping argument as `HerschfeldClosure.lean`, transferring essentially
    unchanged because, for even `n`, `altSum n N`'s numerator matches exactly
    the bound the factorization `N^n-L(N)^n=(N-L(N))·S` gives from `L(N) ≥ 1`
    alone.
  - **Odd `n`** (`limitValNS_eq_self_odd`): for odd `n` the same factorization
    gives numerator `N^n+1` instead of `N^n-1` — a constant gap of exactly
    `2` — so the clean ratio `(N+1)/(N-1)` picks up an extra per-step
    `shrinkFactor n N = (N^n-1)/(N^n+1)` (`deficitS_growth_odd`). The gap
    turns out not to be fatal: the product of these shrink factors over ANY
    number of steps stays bounded below by a fixed `1/2`, independent of the
    starting point and the step count (`prodShrink_ge_half`), via a
    hand-proved Weierstrass-type inequality `∏(1-xᵢ) ≥ 1-∑xᵢ` (no direct
    match found in Mathlib) combined with an elementary telescoping bound on
    `∑ 2/(N₀+i)³`. A fixed-factor-scaled deficit growth is still quadratic,
    so it still beats the linear ceiling (`deficitS_quadratic_lower_odd`),
    just needing a doubled threshold in the final contradiction.

**Not attempted:** the complex-valued extension mentioned in the paper's
conclusion.

## Repository structure

```
RamanujanNested.lean              -- root import + full status summary
RamanujanNested/
  Defs.lean                       -- the recursion, truncRadical, r*
  Bounds.lean                     -- Section 4.1, boundedness
  Monotone.lean                   -- Section 4.1, monotonicity
  Convergence.lean                -- Section 4.1, convergence
  ControlledNegative.lean         -- Lemma 1
  IdentityChain.lean               -- Appendix A.1, Algorithm 3
  Reconstruction.lean              -- Appendix A.1, Algorithm 4
  Oscillatory.lean                 -- Appendix A.2
  TargetRadical.lean                -- constant-coefficient exact-target radical
  UnboundedChain.lean                -- moving-ceiling existence for a_k = N+k-2
  HerschfeldClosure.lean              -- exact-value closure, L(N) = N
  PrimeChain.lean                     -- existence of a limit for a_k = p_k
  LinearChain.lean                    -- existence for any slope m >= 1
  LinearChainGeneral.lean              -- existence for any slope m > 0
  LinearChainTight.lean                 -- tight bound for 0 < m <= 1
  NthRootChain.lean                       -- bounded coeffs, any root order n >= 2
  LinearChainNthRoot.lean                    -- unbounded linear family, any n >= 2
  LinearChainGeneralNthRoot.lean                 -- unbounded, every slope m>0, any n
  LinearChainTightNthRoot.lean                     -- unbounded, tight bound 0<m<=1, any n
  PrimeChainNthRoot.lean                             -- a_k=p_k, any root order n >= 2
  OscillatoryNthRoot.lean                              -- oscillatory family, any n >= 2
  TargetRadicalNthRoot.lean                               -- exact-target radical, any n >= 2
  IdentityChainNthRoot.lean                                  -- classical unbounded family, any n >= 2
```

## Building

```sh
lake exe cache get
lake build
```

Pinned toolchain: `leanprover/lean4:v4.14.0`; Mathlib at `v4.14.0`.
