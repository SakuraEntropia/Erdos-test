# Phase 5 — Known Results (theorems, with Mathlib status)

> **Legend:** **A** = proven · **B** = computational evidence · **C** = conjecture ·
> **D** = AI-generated hypothesis. For each theorem we give: statement, status, whether it is in
> Mathlib, and whether a simplified Lean formalisation is realistic.

---

## 1. Reduction to primes

**Statement.** If the conjecture holds for every prime `p`, it holds for every `n ≥ 2`:
`Conjecture ↔ (∀ p, Prime p → ∃ x y z > 0, IsDecomposition p x y z)`.

- **Status:** **[A]** — elementary, and **formally verified in this project**
  (`Theorems/MainResult.lean`, `reduction_to_primes`, together with the scaling lemma `scale`).
- **Mathlib:** not present as a named theorem (there is no Erdős–Straus formalisation in Mathlib),
  but every ingredient (`Nat.Prime`, strong induction, divisibility) is in Mathlib.

## 2. Even / `p ≡ 3 (mod 4)` cases

**Statement.** `4/(2k) = 1/k + 1/(2k) + 1/(2k)`; and for `n = 4k+3`,
`4/(4k+3) = 1/(k+1) + 1/(2(k+1)(4k+3)) + 1/(2(k+1)(4k+3))`. Combined with the `3∣n` and
`n ≡ 2 (mod 3)` identities, the conjecture holds unless `n ≡ 1 (mod 12)`.

- **Status:** **[A]** — **formally verified here** (`Theorems/Lemma1.lean`, `Lemma2.lean`).
- **Mathlib:** not present as such; ingredients in Mathlib.

## 3. Obláth (1950)

**Statement.** If `n+1` is divisible by a prime `≡ 3 (mod 4)`, then `4/n` has a solution. Since
the complement (those `n` with `n+1` having only prime factors `≡ 1 (mod 4)`) has density 0,
this settles the conjecture for **almost all `n`**.

- **Status:** **[A]** (published).
- **Mathlib:** not present. Ingredients (factorisation, primes `≡ 3 (mod 4)`) are in Mathlib;
  a formalisation is plausible but non-trivial (needs a density/almost-all notion).

## 4. Mordell's six-class reduction (≈1969)

**Statement.** The conjecture holds for all `n` except possibly those in
`{1, 121, 169, 289, 361, 529} (mod 840)`. These are exactly `1², 11², 13², 17², 19², 23² (mod 840)`;
equivalently the classes `p ≡ 1 (mod 24)` that are quadratic residues modulo both 5 and 7
(hence represented by `x² + 840y²`). The proof is a finite (but large) family of **modular
identities**.

- **Status:** **[A]** (published; the "6 classes" is the standard quoted form).
- **Mathlib:** not present. **Formalisable in principle** but needs ~200 explicit modular
  identities + CRT; that is exactly the kind of mechanical lemma pile this project is suited for,
  though substantial. *(Our Phase-4 experiment independently re-discovered the precursor
  reductions — even → `n≡1 (mod 12)` → affine barrier `n≡1 (mod 8)`.)*

## 5. Vaughan (1970) — density of exceptions

**Statement.** The number of `n ≤ N` with no solution is `≤ N·exp(−c (log N)^{2/3})` for an
absolute `c > 0`. In particular the exceptional set has **natural density 0**.

- **Status:** **[A]** (published; uses the **large sieve**).
- **Mathlib:** **large sieve is not in Mathlib** (verified by grep). Formalising Vaughan's theorem
  is a large analytic-number-theory project, out of scope here.

## 6. Elsholtz–Tao (2011/13) and Elsholtz–Planitzer (2018) — counting solutions

**Statement.** Let `f(n)` be the number of (positive, unordered) solutions to
`4/n = 1/x + 1/y + 1/z`. Then
`Σ_{p ≤ N} f(p) = N (log N)^{2+o(1)}`, and `f(p) ≤ p^{3/5+o(1)}` for all primes `p` (extended to
`f(n) ≤ n^{3/5+o(1)}` for all `n`); also `f(n) ≥ (log n)^{log 6+o(1)}` for almost all `n`.

- **Status:** **[A]** (published).
- **Mathlib:** not present. The divisor parametrisation `f(n) = …` (number of solutions in terms
  of divisors) **is** a good, provable *simplified* target (see §8).

## 7. Bright–Loughran (2020) — no Brauer–Manin obstruction

**Statement.** (i) For every `n`, there is **no Brauer–Manin obstruction** to the existence of a
natural-number solution on the Erdős–Straus surface. (ii) There **is** an obstruction to strong
approximation at `p`-adic places: for odd `n`, a solution must satisfy the Hilbert-symbol
condition `∏_{p∣n} (−u₁/u₃, −u₂/u₃)_p = −1`. This recovers Yamamoto's quadratic-reciprocity
conditions and Elsholtz–Tao's result on odd squares as special cases.

- **Status:** **[A]** (published).
- **Mathlib:** the **Brauer–Manin obstruction is not in Mathlib** (only the Brauer *group* is).
  Not a realistic formalisation target here. *However*, the underlying **quadratic reciprocity /
  Legendre symbol** is **in Mathlib** (`NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`),
  so the *Yamamoto-type* necessary conditions are a plausible simplified target.

---

## 8. Useful lemmas collected (and their Mathlib availability)

| Lemma / ingredient | Where used | In Mathlib? |
|---|---|---|
| `Nat.Prime`, `Nat.exists_prime_and_dvd`, strong induction | reduction to primes | ✅ (used in this project) |
| divisibility / scaling (`Nat.mul_div_cancel'`, `Nat.le_of_dvd`, …) | reduction to primes | ✅ |
| `field_simp`, `ring`, `positivity`, `norm_num` over `ℚ` | all identities | ✅ (tactics) |
| **Legendre symbol + quadratic reciprocity** | Yamamoto / Bright–Loughran | ✅ `NumberTheory/LegendreSymbol/…` |
| `ZMod` modular arithmetic, CRT | Mordell reduction | ✅ |
| primes `≡ 1 (mod m)` / `≡ 3 (mod 4)` | Obláth | partial (`PrimesCongruentOne.lean` for `≡1`) |
| Selberg sieve, Abel summation, Chebyshev | analytic estimates | ✅ (tools only; no large-sieve theorem) |
| **large sieve** | Vaughan, Elsholtz, Pomerance–W. | ❌ not in Mathlib |
| **Brauer–Manin obstruction** | Bright–Loughran | ❌ not in Mathlib |
| **circle method** | (none of the main results; often mentioned) | ❌ not in Mathlib |
| divisor-count reformulation `f(n)` | Elsholtz–Tao | ❌ (not formalised; elementary target) |

**Summary of formalisability.** The *elementary* layer (reduction to primes, modular identities,
the six-class reduction, the divisor-count formula) is a realistic Lean target. The *analytic*
layer (large sieve / circle method) and the *geometric* layer (Brauer–Manin) are beyond Mathlib's
current coverage.

---

## 9. Separation of registers (this file)

- **A (proven):** §§1–7 (each labelled), with §§1–2 additionally verified in this project's Lean.
- **B (computational):** Swett `10^14`, Salez `10^17`, claimed `10^18`; our own `brute_force.py`
  and `search_patterns.py` runs.
- **C (conjectural):** the conjecture itself; the belief that a finite polynomial cover does not
  exist (stated in §3 of `open_questions.md`, not here).
- **D (AI-generated hypotheses):** the "affine barrier at `n ≡ 1 (mod 8)`" observation from
  `identity_search.py` is a **bounded-search hypothesis**, not a theorem — see
  [`open_questions.md`](open_questions.md).
