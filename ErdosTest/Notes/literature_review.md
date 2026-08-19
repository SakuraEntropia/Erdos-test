# Phase 5 — Literature Review: the Erdős–Straus Conjecture

> **Legend (used throughout):**
> **A** = proven mathematics · **B** = computational evidence · **C** = conjecture / conjectural idea ·
> **D** = new AI-generated hypothesis (not independently established).

---

## 1. The problem and its origin

**Conjecture (Erdős 1948/1950; Straus).** For every integer `n ≥ 2` there exist positive integers
`x, y, z` with

```
4/n = 1/x + 1/y + 1/z.
```

The conjecture is stated in Erdős's 1950 paper

- P. Erdős, *Az 1/x₁ + 1/x₂ + … + 1/xₙ = a/b egyenlet egész számú megoldásairól (On a Diophantine
  equation)*, **Mat. Lapok 1** (1950), 192–210.

It is standard to attribute the problem to both **Erdős** and **E. G. Straus**. It is the `4/n`
case of the family of "Egyptian fraction" / unit-fraction problems
`m/n = 1/x₁ + ⋯ + 1/xₖ`. The `4/n` case with `k = 3` terms is the famous open one (the `5/n`
case, posed by Sierpiński, is likewise open with 3 terms).

**Reduction to primes.** If `n` is composite, `n = a·b` with `a, b > 1`, a solution for `a`
scales to a solution for `n`. Hence it suffices to prove the conjecture for **primes `p`**, and
in fact (by the even identity `4/(2k) = 1/k + 1/(2k) + 1/(2k)` and the `p ≡ 3 (mod 4)` identity)
for **primes `p ≡ 1 (mod 4)`**. *This reduction is now formally verified in this project
(`Theorems/MainResult.lean`, `reduction_to_primes`).* **[A]**

---

## 2. Timeline

| Year | Author(s) | Result | Technique |
|---|---|---|---|
| 1948 | Erdős, Straus | Conjecture stated | — |
| 1950 | Erdős | Original paper (Mat. Lapok 1) | — |
| 1950 | Obláth | True if `n+1` has a prime factor `≡ 3 (mod 4)`; hence for a set of density 1 | modular parametrisation |
| 1954 | Rosati | early modular identities | parametrisation |
| 1956 | Sierpiński | results for some classes; posed `5/n` analogue | parametrisation |
| ~1962 | Bernstein | modular identities | parametrisation |
| 1965 | Yamamoto | necessary conditions via quadratic reciprocity | quadratic reciprocity |
| ~1969 | Mordell | **reduction to 6 residue classes mod 840**: `n ≡ 1, 121, 169, 289, 361, 529 (mod 840)` | ~200 modular identities |
| 1970 | Vaughan | #exceptions ≤ N·exp(−c(log N)^{2/3}) ⇒ *almost all* `n` solvable | **large sieve** |
| ~1971 | Terzi | reduction to ~198 classes mod 120120 | more modular identities |
| 1999 | Swett | verified all `n < 10^14` | computer sieve, single modular equation |
| 2001 | Elsholtz | exceptional sets for sums of `k` unit fractions | large sieve |
| 2011/13 | Elsholtz–Tao | counting `f(p)`; `f(p) ≤ p^{3/5+o(1)}`; `Σ_{p≤N} f(p) = N(log N)^{2+o(1)}` | divisor structure |
| 2014 | Salez | verified up to `10^17` | complete set of modular equations |
| 2018 | Elsholtz–Planitzer | `f(n) ≤ n^{3/5+o(1)}` for all `n`; `f(n) ≥ (log n)^{log 6+o(1)}` a.a. `n` | divisor structure |
| 2020 | Bright–Loughran | **no Brauer–Manin obstruction**; but a `p`-adic (Hilbert-symbol) obstruction | arithmetic geometry |
| ~2021 | Bloom–Elsholtz | equivalent congruence-only formulation for primes | sieve / counting |
| 2025 | (various preprints) | verification claimed to `10^18`; several claimed "partial resolutions" | computer / new formulas |
| 2026 | Pomerance–Weingartner | exceptions to the general `m/n` (Erdős–Straus–Schinzel) problem, `m`-dependence explicit | large sieve |

> **Confidence note.** Entries with `~` have approximate/uncertain years. The 2025–2026
> "partial resolution" preprints are **unrefereed and not independently verified**; they are
> recorded here for completeness and flagged as unverified claims, not established results.

---

## 3. What is established (strongest known results)

These are the milestones; each is stated precisely in [`known_results.md`](known_results.md).

1. **Reduction to primes `p ≡ 1 (mod 4)`** — elementary; **[A]** and now formally verified here.
2. **Mordell's six-class reduction** — the conjecture is settled for every `n` except
   `n ≡ 1, 121, 169, 289, 361, 529 (mod 840)`. **[A]** (published; not yet in this Lean project).
3. **Vaughan's density bound** — the exceptional set has density 0, quantitatively. **[A]**
   (uses the large sieve).
4. **Elsholtz–Tao / Elsholtz–Planitzer counting** — sharp bounds on the number of solutions.
   **[A]**.
5. **Bright–Loughran** — no Brauer–Manin obstruction to the conjecture. **[A]**; and a
   `p`-adic necessary condition that *recovers* Yamamoto's and Elsholtz–Tao's conditions. **[A]**.
6. **Computational verification** up to `10^14` (Swett), `10^17` (Salez), `10^18` (claimed 2025).
   **[B]** — these are exhaustive computations, not proofs.

---

## 4. Sources

- Wikipedia: [Erdős–Straus conjecture](https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Straus_conjecture)
- MathWorld: [Erdős–Straus Conjecture](https://mathworld.wolfram.com/Erdos-StrausConjecture.html)
- Erdős Problems database: [Problem #242](https://www.erdosproblems.com/242)
- Elsholtz–Tao, *Counting the number of solutions…*, [arXiv:1107.1010](https://arxiv.org/abs/1107.1010)
- Elsholtz–Planitzer, *The number of solutions of the Erdős–Straus equation…*, [arXiv:1805.02945](https://arxiv.org/abs/1805.02945)
- Bright–Loughran, *Brauer–Manin obstruction for Erdős–Straus surfaces*, [arXiv:1908.02526](https://arxiv.org/abs/1908.02526)
- Salez, *The Erdős–Straus conjecture: new modular equations and checking to 10¹⁷*, [arXiv:1406.6307](https://arxiv.org/abs/1406.6307)
- Pomerance–Weingartner, *Exceptions to the Erdős–Straus–Schinzel conjecture*, [arXiv:2511.16817](https://arxiv.org/abs/2511.16817)
- OEIS [A292581](https://oeis.org/A292581) (record of the computational verification)

> **Disclaimers.** (i) Years marked `~` should be checked against MathSciNet/zbMATH before
> citation in a publication. (ii) The 2025–2026 preprints/Zenodo notes found by search
> ("Partial Resolution…", "Residual Divisor Certificates…", etc.) are **unrefereed**; this review
> does **not** treat them as results. (iii) No source claims a proof of the full conjecture.
