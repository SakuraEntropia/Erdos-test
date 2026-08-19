# Phase 8, Step 4 — Problem Variants

> Legend: A = proven · B = computational · C = conjecture · D = AI hypothesis.
> Each variant is stated precisely, tested where possible, and its formalisation status recorded.

The main conjecture: **for every prime `p ≡ 1 (mod 4)` there are `x,y,z > 0` with
`4/p = 1/x+1/y+1/z`.** Variants below weaken or strengthen it along different axes.

---

## Variant W1 — the easy half of `n ≡ 1 (mod 4)`  [A]

**Statement.** For every `k ≥ 0`, `4/(8k+5) = 1/(2k+2) + 1/((8k+5)(k+1)) + 1/(2(8k+5)(k+1))`
(equivalently: every `n ≡ 5 (mod 8)` has a solution with the minimal `x = (n+3)/4`, i.e. `a = 3`).

- **Status: [A] verified** — `five_mod_eight_minimal` in `ACases.lean`.
- **Computational check:** all `p ≡ 5 (mod 8)`, `p ≤ 30000` admit `a = 3` (0 failures). [B, consistent]

## Variant E1 — equivalent: divisor certificate  [A]

**Statement.** `4/n = 1/x+1/y+1/z` has a positive solution iff there exist `x,a,d,e > 0` with
`a+n = 4x`, `a ∣ d+nx`, `a ∣ e+nx`, `d·e = (nx)²`.

- **Status: [A] verified** — `solvable_iff_certificate` in `Certificate.lean`.
- **Sub-case E1′ (minimal certificate):** `a = 3` solvable iff `∃ d,e` with `d·e = ((4k+1)(k+1))²`,
  `3 ∣ d+(4k+1)(k+1)`, `3 ∣ e+(4k+1)(k+1)` — **[A] verified** (`a3_iff_divisor`).

## Variant M1 — the `a = 3` characterisation  [A]

**Statement.** For prime `p ≡ 1 (mod 4)`: `a = 3` works ⟺ `p ≡ 2 (mod 3)` ∨ `(p+3)/4` has a prime
factor `≡ 2 (mod 3)`.

- **Status: [A] verified** — the full equivalence is `a3_solvable_iff_two_mod_three_or_factor`
  (`Theorems/A3Characterization.lean`), built on `a3_iff_divisor` (`MinimalCertificate.lean`) and
  `divisor_two_mod_three_iff` (`PrimeModThree.lean`). The referee's Claim-4 register violation
  ("`⟺ C` is B in both directions") is now resolved by **proof**, not relabelling: the `C`-bridge
  (`∃ d, d ∣ M² ∧ d % 3 = 2 ↔ ∃ q, q.Prime ∧ q ∣ M ∧ q % 3 = 2`) is a checked theorem.
- **Computational check (now a consistency test, not evidence):** 0 mismatches up to `p = 30000`,
  1611 primes. [B, redundant]
- **Refinement:** all `a = 3` failures are `p ≡ 1 (mod 8)`. For `p ≡ 1 (mod 8)`, `p ≤ 30000`:
  `a = 3` works for 584 primes, fails for 212 (first failures 73, 193, 241, 313, 409, 433, …).

## Variant S1 — stronger: `a = 3` always  [FALSE]

**Statement.** Every prime `p ≡ 1 (mod 4)` has a solution with `x = (p+3)/4` (`a = 3`).

- **Status: [FALSE]** — 212 primes `p ≤ 30000` fail (`73, 193, 241, …`). Refuted computationally.

## Variant S2 — stronger: minimal `a` bounded by a constant  [FALSE / D]

**Statement.** There is a constant `C` with `4·x_min(p) − p ≤ C` for all primes `p ≡ 1 (mod 4)`.

- **Status:** for `C = 23` this is **[FALSE]** — minimal `a = 31` at `p = 21169`. Distribution of minimal
  `a` for `p ≤ 30000`: `3` (1399), `7` (…), `11`, `15`, `19` (5), `23` (4), `31` (1).
- **Interpretation:** minimal `a` grows, slowly. The general statement "bounded by *some* constant" is
  **[D]** (unsupported) and is **much stronger than the conjecture** — likely false. The value is a *lens*:
  a solution's first denominator stays within a small multiple of `n/4` for `p ≤ 30000`.

## Variant W2 — weaker: existence with *any* `x ≤ p`  [C, implied by conjecture]

**Statement.** For every prime `p ≡ 1 (mod 4)`, there is a solution (no bound on `x`).

- **Status: [C]** — this *is* the conjecture, hence open. Included only to anchor the scale of the
  other variants.

## Variant A1 — asymptotic: density-one solvability  [A, published]

**Statement.** The set of `n ≤ N` with no solution has density 0 (Vaughan; quantitatively
`≤ N exp(−c (log N)^{2/3})`).

- **Status: [A]** (published), **not formalisable here** (large sieve absent from Mathlib).

## Variant F1 — finite: checkable to a bound  [B]

**Statement.** Every `n ≤ 30000` is solvable (trivially implied by existing verifications to `10^17`).

- **Status: [B]** — our certificate-based search confirms solvability for all primes `p ≡ 1 (mod 4)`,
  `p ≤ 30000`, via the *verified* bijection (a solution is produced as an explicit certificate).

---

## What these variants teach

- The `a = 3` story is **cleanly resolved**: `a = 3` is a *decidable* condition (W1/M1/E1′), provable
  without factorisation.
- The minimal-`a` story **does not collapse** to `a = 3` (S1 false, S2 false for small constants): the
  hard core leaks into larger `a`, so the minimal certificate alone cannot finish the conjecture.
- The **strongest true statement we now hold** is the bijection (E1) and its `a = 3` slice (E1′/M1),
  which are *reformulations*, not a crossing of the six-class core.
