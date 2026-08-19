# Phase 8, Step 1–2 — Theorem Dependency Graph & Proof Candidates

> **Legend:** **VERIFIED** = Lean accepts the proof (`lake build` clean, no `sorry`) ·
> **PARTIAL** = some components proved · **UNKNOWN** = no proof · **FALSE** = counterexample found.
> Registers: **A** = proven · **B** = computational · **C** = conjecture · **D** = AI hypothesis.

---

## 1. Verified statement inventory

All in namespace `ErdosStraus` unless noted. Every entry is **VERIFIED** (built cleanly).

| Statement | File | Depends on | Relation to Erdős problem |
|---|---|---|---|
| `IsDecomposition`, `IsDecompositionCleared` (defs) | ErdosProblem | — | the two equivalent forms of `4/n = 1/x+1/y+1/z` |
| `isDecomposition_iff_cleared` | ErdosProblem | fraction/cleared defs | fraction form ⟺ cleared form |
| `two_has_decomposition` | ErdosProblem | — | base case `n = 2` |
| `even_decomposition` | ErdosProblem | — | even `n = 2k` solved |
| `two/three/four/five_has_solution` | Lemma1 | `two_has_decomposition` | base cases `n = 2..5` |
| `small_cases` | Lemma1 | the four above | `n ∈ {2,3,4,5}` solved |
| `three_divides` | Lemma2 | — | `n = 3k` solved |
| `two_mod_three` | Lemma2 | — | `n = 3k+2` solved |
| `three_mod_four` | Lemma2 | — | `n = 4k+3` solved |
| `even_solution` | Lemma2 | `even_decomposition` | wrapper for even case |
| `easy_classes` | Lemma2 | `even_decomposition`, `three_divides`, `three_mod_four` | `2∣n ∨ 3∣n ∨ n≡3(4)` solved |
| `scale`, `scale_of_solution` | MainResult | `isDecomposition_iff_cleared` | scaling invariance |
| `reduction_to_primes` | MainResult | `scale_of_solution` | **conjecture ⟺ prime version** |
| `cleared_iff_normalized` (A) | DivisorParam | `IsDecompositionCleared` | symmetric normalized form |
| `solution_bound` (B) | DivisorParam | `isDecomposition_iff_cleared` | any solution has `n < 4x` |
| `divisor_construction` (C) | DivisorParam | `isDecomposition_iff_cleared` | divisor certificate ⟹ solution |
| `five_mod_eight` (D) | DivisorParam | — | `n ≡ 5 (mod 8)` identity |
| `Solvable`, `HasCertificate` (defs) | Certificate | — | solution / certificate predicates |
| `solution_gives_certificate` (E) | Certificate | `solution_bound`, `isDecomposition_iff_cleared` | solution ⟹ certificate |
| `solvable_of_certificate` | Certificate | `divisor_construction` | certificate ⟹ solution |
| `certificate_of_solvable` | Certificate | `solution_gives_certificate` | solution ⟹ certificate (wrapped) |
| `solvable_iff_certificate` | Certificate | both directions | **solution ⟺ certificate** (bijection) |
| `two_odd_implies_sum_odd` | Certificate | — | parity lemma |
| `odd_solution_two_divides_pairwise_sum` | Certificate | `isDecomposition_iff_cleared`, `Nat.Coprime` | odd `n` ⟹ `2 ∣ xy+yz+zx` |
| `odd_solution_not_two_odd` | Certificate | `odd_solution_two_divides_pairwise_sum` | odd `n` ⟹ at most one odd denominator |
| `four_minus_recip_reduction` | ACases | — | `a=3` reduces to a 2-term problem |
| `five_mod_eight_minimal` | ACases | — | `n ≡ 5 (mod 8)` minimal (`a=3`) identity |
| `a3_solution` | ACases | `divisor_construction` | `a=3` certificate ⟹ solution |
| `x_ge_minimal` | MinimalCertificate | `solution_bound` | `x ≥ (n+3)/4` is minimal |
| `three_dvd_4k1_iff_three_dvd_k1` | MinimalCertificate | — | `3 ∣ 4k+1 ↔ 3 ∣ k+1` |
| `a3_solvable_gives_divisor` | MinimalCertificate | `solution_gives_certificate` | `a=3` solution ⟹ certificate |
| `a3_iff_divisor` | MinimalCertificate | `a3_solution`, `a3_solvable_gives_divisor` | **`a=3` solvable ⟺ certificate** |
| `erdos_szekeres` (ns `ErdosSzekeres`) | Szekeres | — | unrelated (separate classical result) |

---

## 2. Dependency graph (key edges)

```
                        IsDecomposition ── IsDecompositionCleared
                              │ (iff_cleared)
        ┌─────────────────────┼──────────────────────┐
   solution_bound     divisor_construction      scale ── reduction_to_primes
        │                     │
        └── solution_gives_certificate ──┐
                                         ├── solvable_iff_certificate
        a3_solution ◄─ divisor_construction
             │
   a3_solvable_gives_divisor ◄─ solution_gives_certificate
             │
        a3_iff_divisor  ◄── a3_solution + a3_solvable_gives_divisor
        x_ge_minimal    ◄── solution_bound
```

The single most load-bearing edge: **`solvable_iff_certificate`** reduces the entire conjecture to
existence of a divisor certificate. **`a3_iff_divisor`** (new this phase) is its `a = 3` specialisation,
which needs *no* prime factorisation.

---

## 3. UNKNOWN / PARTIAL / FALSE items (the actual targets)

| Item | Status | Notes |
|---|---|---|
| `Conjecture` (full Erdős–Straus) | **UNKNOWN** (open) | the conjecture itself |
| certificate *existence* for every `p ≡ 1 (mod 4)` | **UNKNOWN** | **equivalent to the conjecture**; the hard core — *not* attacked here |
| full `a=3` prime-factor characterisation (⟹ direction) | **PARTIAL** | `a3 ⟺ certificate` is **VERIFIED**; the step "`M²` has a divisor `≡2 (mod 3)` ⟺ `M` has a prime factor `≡2 (mod 3)`" needs prime factorisation — **UNKNOWN** |
| divisor-count formula `f(n) = …` | **UNKNOWN** | published (Elsholtz–Tao); not formalised |
| six-class reduction mod 840 | **UNKNOWN** | published (Mordell); not formalised |
| Obláth's theorem (`n+1` has a `≡3 (mod 4)` factor) | **UNKNOWN** | published; not formalised |
| "minimal `a` ≤ 23" (bounded minimal certificate) | **FALSE** | refuted: minimal `a = 31` at `p = 21169` |
| "minimal `a ∈ {3,7}`" (from `n ≤ 300`) | **FALSE** | refuted: `a ∈ {3,7,11,15,23,31}` |
| "no affine `(x,y)` identity covers `n ≡ 1 (mod 8)`" | **UNKNOWN** (D) | bounded-search hypothesis, not proven |

---

## 4. Proof candidates (Step 2)

For each UNKNOWN/PARTIAL target, candidate strategies.

### T1. Full `a=3` prime-factor characterisation (complete the PARTIAL item)

**Claim.** For prime `p ≡ 1 (mod 4)`: `a=3` works ⟺ `p ≡ 2 (mod 3)` ∨ `(p+3)/4` has a prime factor `≡ 2 (mod 3)`.

- **Strategy S1a — prime-factorisation lemma.** Prove in Lean: `(∃ d, d ∣ M² ∧ d ≡ 2 (mod 3)) ↔ (∃ q, q.Prime ∧ q ∣ M ∧ q ≡ 2 (mod 3))`.
  - Idea: `d ≡ 2 (mod 3)` ⟹ some prime `q ≡ 2 (mod 3)` divides `d` (hence `M`); conversely `q ∣ M ⟹ q ∣ M²`.
  - Tools: `Nat.primeFactorsList`, `Nat.mem_factors`, `ZMod 3` / `omega` for residues.
  - Obstacles: Mathlib's factorisation API is fiddly; the "odd-exponent" argument needs care.
  - Lean plan: build the lemma for `M = (4k+1)(k+1)`, compose with `a3_iff_divisor`.
- **Strategy S1b — avoid factorisation via a `% 3` sieve.** Show `M²` has a divisor `≡2 (mod 3)` iff `M % 3 ∈ {…}` computed by a finite residue analysis. Cheaper but less general.
- **Difficulty:** medium (factorisation), **value:** completes the characterisation as a verified theorem.

### T2. Divisor-count formula `f(n)` (published, elementary target)

- **Strategy S2a — injectivity/surjectivity of the certificate map.** Show the map
  `(x, d, e) ↦ solution` is a bijection onto solutions, giving `f(n) = #{(x,a,d,e) : …}`.
  - Idea: this is the Elsholtz–Tao parametrisation; `solvable_iff_certificate` already gives *some* certificate
    for *some* `x`; the count requires enumerating *all* `x` and all `(d,e)` per `x`.
  - Tools: `Finset` counting, the certificate bijection.
  - Obstacles: keeping track of `x` in the certificate (the current `HasCertificate` bundles `x`).
  - Lean plan: define `f n := #{x | ∃ d e, …}`; prove monotonicity / a lower bound `f(p) ≥ …`.
- **Difficulty:** medium–high; **value:** first *counting* result in Lean for ES.

### T3. Six-class reduction mod 840 (published; ~200 identities)

- **Strategy S3a — symbolic identity farm.** Reproduce the `identity_search.py` identities as Lean lemmas
  (`field_simp` + `ring`), then assemble CRT to prove "solvable for all `n` except 6 classes mod 840".
  - Tools: existing `field_simp`+`ring` pattern; `ZMod`/CRT.
  - Obstacles: ~200 mechanical identities; bookkeeping of the CRT cover.
  - Lean plan: generate identities *from* the Python search, emit Lean, verify.
- **Difficulty:** high (volume), **value:** reproduces a classical milestone as machine-checked.

### T4. Obláth's theorem (published)

- **Strategy S4a — parametrisation by a `≡3 (mod 4)` factor.** If `q ≡ 3 (mod 4)`, `q ∣ n+1`, give an
  explicit identity in `q, n`.
  - Tools: the classical identity (needs the exact formula from literature); `field_simp`+`ring`.
  - Obstacles: needs the correct published identity; not in front of us.
- **Difficulty:** low–medium once the identity is in hand; **value:** first "almost-all" ingredient.

### T5. Minimal-certificate growth (refuted "bounded" — now a *new* question)

- **Strategy S5a —** show `a` can be arbitrarily large is **not** currently provable; instead *quantify*
  empirically (done: reaches 31 by `p = 30000`). Turn into a conjecture "minimal `a` is unbounded" [D].
  - Not a Lean target yet.

**Selected for this phase:** **T1** (via `a3_iff_divisor`, the factorisation-free core — *completed*), and
the empirical backbone of **T5** (S2/W1 variants, *completed*). T1's factorisation step, T2, T3, T4 remain
as the next milestones.
