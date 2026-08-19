# Phase 8, Step 3 & 5 — Proof-Search Log and Adversarial Verification

> Legend: A = proven · B = computational · C = conjecture · D = AI hypothesis.
> Every attempt below was checked with `lake build`; nothing is recorded as proved unless Lean accepts it.

---

## 1. Proof-search log

### Attempt P1 — `a3_iff_divisor` (the bidirectional `a=3` characterisation) — **SUCCESS**

- **Mathematical idea.** Specialise the certificate bijection `solvable_iff_certificate` to `a = 3`,
  `x = k+1` (`n = 4k+1`). Since `a = 4x−n = 3` is forced by `x = (n+3)/4`, the `a=3` case is exactly
  "solution with the minimal first denominator".
- **Result.** `theorem a3_iff_divisor (k) (hk : 1 ≤ k) : A3Solvable k ↔ A3Certificate k` — **VERIFIED**,
  where `A3Solvable k := ∃ y z, 0<y ∧ 0<z ∧ IsDecomposition (4k+1) (k+1) y z` and
  `A3Certificate k := ∃ d e, 0<d ∧ 0<e ∧ d·e = ((4k+1)(k+1))² ∧ 3∣d+(4k+1)(k+1) ∧ 3∣e+(4k+1)(k+1)`.
- **Composition.** The ⟸ direction is `a3_solution` (already verified); the ⟹ direction is the new
  `a3_solvable_gives_divisor` (extract the certificate from a solution, then read off `a = 3` from
  `a + (4k+1) = 4(k+1)` via `omega`).

### Attempt P2 — `x_ge_minimal` (minimal first denominator) — **SUCCESS (after fix)**

- **Idea.** `solution_bound` gives `n < 4x`; for `n = 4k+1` this is `k+1 ≤ x`, so `x = (n+3)/4` is minimal.
- **First attempt FAILED.** `solution_bound` requires `2 ≤ n`, but `n = 4k+1` needs `k ≥ 1`
  (for `k = 0`, `n = 1 < 2`). `omega` correctly reported `2 ≤ 4·0+1 = 1` is false.
- **Fix.** Thread a `hk : 1 ≤ k` hypothesis (equivalently `n ≥ 5`) through `x_ge_minimal` and
  `a3_solvable_gives_divisor`. **Learned:** the `a = 3` theory is intrinsically about `n ≥ 5`
  (`n ≡ 1 (mod 4)`, `n ≠ 1`), so `k ≥ 1` is a genuine (not accidental) precondition.

### Attempt P3 — `three_dvd_4k1_iff_three_dvd_k1` (mod-3 bridge) — **SUCCESS**

- **Idea.** `4k+1 = 3k + (k+1)`, so `3 ∣ 4k+1 ↔ 3 ∣ k+1`. Proved both directions with `omega`
  (witnesses `c−k` and `c+k`). **Purpose:** this is the bridge from "`3 ∣ d+M`" to the residue reading
  "`d ≡ −M ≡ 2 (mod 3)`" needed to connect `a3_iff_divisor` to the prime-factor condition in T1.

### Attempt P4 — full `a=3` prime-factor characterisation (⟹ via factorisation) — **NOT ATTEMPTED / deferred**

- The remaining step "`M²` has a divisor `≡ 2 (mod 3)` ⟺ `M` has a prime factor `≡ 2 (mod 3)`" needs
  Mathlib's prime-factorisation API (`Nat.factors`, `Nat.mem_factors`). Assessed as **medium effort** and
  deferred to the next phase; recorded as the top "missing infrastructure" item rather than a failed attempt.

---

## 2. Adversarial verification (Step 5)

Applied to the phase's main result `a3_iff_divisor` and the `a=3` characterisation.

1. **Is it stronger than known results?** **No.** It is a *specialisation* of the classical divisor
   parametrisation (Elsholtz–Tao / Swett), which is already published. It is not stronger than Obláth,
   Mordell, Vaughan, or Elsholtz–Tao. It *is* a **new formalisation** (no such statement exists in Mathlib),
   but not a new deep theorem.

2. **Hidden circular reasoning?** **None found.** The ⟹ direction uses only `solution_gives_certificate`
   (which itself uses only the cleared equation `4xyz = n(xy+yz+zx)`, proved independently in
   `isDecomposition_iff_cleared`); the ⟸ direction uses `a3_solution`, which is `divisor_construction`
   specialised. There is no appeal to the conjecture. The only subtlety — `a = 3` extracted from
   `a + (4k+1) = 4(k+1)` — is discharged by `omega`, not assumed.

3. **Is it just a reformulation?** **Yes, essentially.** `a3_iff_divisor` is the `a = 3` slice of the
   certificate bijection. Its value is that it *isolates the minimal certificate* and gives a clean,
   computable, factorisation-free criterion — but it does not reduce the difficulty of the conjecture,
   only re-states the `a = 3` case precisely. This is stated plainly, not disguised as progress on the core.

4. **Does the literature already contain it?** The *mathematical content* (divisor parametrisation) is
   classical. The *specific clean form* — "`a = 3` ⟺ complementary divisors of `M²` congruent to `2 (mod 3)`",
   together with the prime-factor version "`p ≡ 2 (mod 3)` or `(p+3)/4` has a `≡ 2 (mod 3)` factor" — was
   **not found** in the literature we read, but it is folklore-adjacent and we do **not** claim novelty of
   the underlying mathematics, only of the formalisation and the explicit computational characterisation.

5. **Can a counterexample be generated?** The *theorem* is verified in Lean (no counterexample exists for
   it). The *empirical claims* are finite: the characterisation was checked to 0 mismatches up to
   `p = 30000`; the minimal-`a` value 31 (at `p = 21169`) is a computation. The earlier over-claim
   "minimal `a ≤ 23`" **was** refuted by exactly this search — demonstrating the referee loop works.

**Verdict:** the result is a **B** (verified partial progress / clean formalisation), explicitly **not** a
solution, and not a strengthening of any known result. No claim of solving the open problem is made.
