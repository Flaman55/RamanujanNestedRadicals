# Where the real difficulty was

`README.md` describes what this repository proves. This is a shorter,
narrower note on a different question: which parts of it were routine
bookkeeping, and which parts needed an actual mathematical idea before any
Lean could be written at all. The five points below are the latter.

## Primes have no algebraic self-similarity

The exact-value technique that closes the linear family `a_k = N+k-2`
(`HerschfeldClosure.lean`) works because shifting the coefficient sequence by
one index shifts the target `N` by exactly one — the family is
self-similar under shifting, and that self-similarity is what the whole
induction leans on. Primes have no such property: `p_{k+1}` is not `p_k`
plus a fixed amount, so the same technique gives no foothold at all.

The way in was to stop trying to match the linear family's exact ceiling and
use a looser but more robust one: any coefficient sequence growing at most
geometrically, `a_k \le r^k` for some fixed `r>1`, already admits a genuine,
depth-independent ceiling via a *moving* bound `A\cdot r^i` that still closes
to a fixed constant at the top level (`rollUp_geomBounded`,
`PrimeChain.lean`). Anchoring this on Bertrand's postulate — each prime is
less than twice the one before it, so `p_k \le 4^k` — gives existence of a
finite limit for `a_k = p_k` (concretely `r=4`, `A=17`). This settles
existence, not the exact value; unlike the linear family, there is no
evident closed form to aim for, and the exact value for primes stays open.

## One construction for both parities, not two

Generalizing the classical identity chain `R_k = N+k-1` from square roots to
an arbitrary root order `n` looked, at first, like two separate proofs:
`(x+1)^n - 1` factors differently depending on whether `n` is even or odd.
The fact that collapses this back into one proof is that `x=-1` is a root of
exactly one of `x^n-1` or `x^n+1`, according to the parity of `n` — so a
single alternating-sign coefficient polynomial (`altSum n x`,
`IdentityChainNthRoot.lean`) and a single identity, differing only by a
sign `(-1)^n`, cover every `n \ge 2` at once. Without this, the file would
have needed to duplicate the entire argument for even and odd `n`
separately.

## The bound that had to stay above 1/2

Once existence held for both parities, the exact value `L(N)=N` transferred
to even `n` essentially for free: the relevant factorization gives exactly
the numerator the `n=2` argument already needs. For odd `n` the same
factorization is off by a constant (`N^n+1` instead of `N^n-1`), which
introduces an extra shrink factor at every step of the telescoping argument.
If that per-step factor were allowed to decay toward `0`, the quadratic
growth that beats the linear ceiling could collapse, and the odd case would
stay open.

The actual work was showing this cannot happen: that the product of these
shrink factors, over *any* number of steps, stays bounded below by a fixed
constant — `1/2` — no matter where you start or how far you go
(`prodShrink_ge_half`). That needed a Weierstrass-type inequality,
`\prod(1-x_i) \ge 1-\sum x_i`, with no matching lemma anywhere in Mathlib, so
it had to be proved from scratch, together with an elementary telescoping
bound on `\sum 2/(N_0+i)^3`. Once that fixed floor was in hand, the odd case
closes by the same contradiction as the even one, just with a doubled
threshold.

## Finding the tightest possible ceiling, not just a working one

`UnboundedChain.lean`'s moving-ceiling technique generalizes cleanly from
slope `m=1` to any slope `m \ge 1` using the same ceiling shape. For
`0 < m < 1` that same ceiling is no longer enough, and the first working fix
(`LinearChainGeneral.lean`) papers over the gap with a generous `+1` slack —
correct, but not the best bound the technique can give.

Finding the *exact* minimal shift meant solving the equality case of the
key inequality, `s^2+3ms+m^2=1`, for its positive root:
`s(m) = (\sqrt{5m^2+4}-3m)/2` (`LinearChainTight.lean`). This is real algebra,
not bookkeeping, and it had to be checked against the one case already known
to be correct — at `m=1`, `s(1)=0` exactly, recovering
`LinearChain.lean`'s untightened bound — before trusting it as the general
answer.

## The estimate that failed, and what it took to see why

Before the argument that actually works, the first attempt at `L(N)=N`
tried to bound the *gap* between the forward evaluation (tail seeded at
`T=0`) and the rolling evaluation (tail seeded at `T=N+d`, which hits `N`
exactly at every depth by construction), using the same
conjugate-multiplication trick that closes the constant-coefficient family
in `TargetRadical.lean`. Worked all the way through (see
`UnboundedChain.lean`'s docstring), this estimate fails: the shrinking
telescoped product and the growing boundary gap almost exactly cancel,
leaving a bound that tends to a nonzero constant, `N-1`, not to `0` — no
depth is ever deep enough to rule out a real gap between `L(N)` and `N`.

The argument that does work, in `HerschfeldClosure.lean`, is not a
refinement of this estimate — it is a different strategy entirely: instead
of bounding a gap between two evaluations, it derives an exact functional
equation for the limit itself, `L(N) = \sqrt{1+(N-1)L(N+1)}`, and shows the
resulting deficit must grow at least quadratically in the number of steps,
which is incompatible with the trivial linear ceiling already available on
that same deficit. Seeing that the first estimate's failure meant "try a
structurally different argument" rather than "tighten this one" was as much
a part of the difficulty as the algebra that followed.
