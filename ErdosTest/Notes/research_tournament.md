# Phase 8b — Multi-Agent Research Tournament

> **Legend:** **A** = proven (Lean-verified here, or published) · **B** = computational ·
> **C** = conjecture · **D** = AI hypothesis.
> **Honesty rule (unchanged):** nothing here claims the Erdős–Straus conjecture is solved; the
> conjecture remains open. The tournament ranks *research strategies and hypotheses*, not results.

This phase ran **5 independent research agents** with deliberately different philosophies, had them
produce hypotheses, then scored every hypothesis/approach on **5 axes**. The top 3 were taken to
"elite mode" (deep Lean + computation dives). This file is the scoreboard.

---

## 1. The five agents

| Agent | Philosophy | Output | Net new verified content |
|---|---|---|---|
| 1. **Classical** | Exhaust the divisor/identity corpus (Obláth, Mordell, trivial-split) before anything modern | `Notes/agent_classical.md`, `Theorems/Classical.lean` | `divisor_split_eq`, `oblath_identity` **[A]** |
| 2. **Modern** | Translate to arithmetic geometry / sieve / class-field theory; ask "adds structure or restates?" | `Notes/agent_modern.md` | no new Lean; sharp negative/sufficiency analysis **[A/C]** |
| 3. **Computational** | Push exact certificate arithmetic to `p ≤ 2·10⁶`; find *new* identities and criteria | `Notes/agent_computation.md` | one-sided criterion, 2 new parametric families, `a=7` criterion **[B]** |
| 4. **Formal Verification** | Supply the missing prime-factorisation lemma; prove it, don't assume it | `Theorems/PrimeModThree.lean` | `divisor_two_mod_three_iff` etc. **[A]** |
| 5. **Adversarial Referee** | Attack every claim; audit register discipline; explain *why* each route fails | `Notes/referee_report.md` | caught one register violation (Claim 4) **[audit]** |

---

## 2. Scoring rubric (0–5 each)

- **Mathematical depth** — how much real structure the idea exposes (vs. a renaming).
- **Connection to literature** — how tightly it attaches to known results (Elsholtz–Tao, Mordell,
  Bright–Loughran, Vaughan, Obláth).
- **Formalizability** — how cheaply it becomes a `sorry`-free Lean theorem in *this* Mathlib build.
- **Novelty potential** — chance of a genuinely new, citable statement.
- **Risk of false intuition** — likelihood of over-generalising a finite-range pattern into a false
  theorem (higher = more dangerous; scored here so "low risk" is good).

Total = depth + literature + formalizability + novelty + (5 − false-intuition).

---

## 3. The ranked scoreboard

| # | Hypothesis / approach | Source | Depth | Lit. | Form. | Novel. | False-int. | **Score** | Register |
|---|---|---:|---:|---:|---:|---:|---:|---|
| 1 | **Complete `a = 3` characterisation** (`a=3` works ⟺ `p≡2 (3)` ∨ `(p+3)/4` has `≡2 (3)` factor) | A1+A3+A4 | 4 | 4 | 5 | 4 | 1 | **21** | **A** (now) |
| 2 | **One-sided divisor criterion** (`a ∣ d+M` alone forces the certificate) | A3-C1 | 4 | 4 | 5 | 4 | 2 | **20** | B (A-pending, easy) |
| 3 | **Two new parametric families** (`n ≡ −4, −1 (mod q)`, prime `q ≡ 3 (4)`) | A3-C3 | 3 | 3 | 5 | 5 | 1 | **20** | B (ring-only) |
| 4 | **Divisor-certificate bijection + minimal-`a` lens** | A1+A2 | 4 | 5 | 4 | 2 | 1 | **19** | **A** |
| 5 | **`a = 7` complete characterisation** (residue set `D(x²)` meets `{5p²,5p,5}`) | A3-C4 | 4 | 3 | 3 | 4 | 2 | **17** | B (A-pending) |
| 6 | **Trivial-split impossibility for primes** (`¬ 4x−p ∣ p·x`) | A1-C3 | 3 | 3 | 4 | 4 | 1 | **18** | A (classical, not in Lean) |
| 7 | **Minimal-`a` forms a complete initial segment** (`{3,7,…,59}`, none skipped) | A3-C5 | 3 | 2 | 1 | 4 | 3 | **12** | B (tail = C/D) |
| 8 | **Target-coset law** (`−M ∈ (−4⁻¹)·squares mod q`) | A3-C2 | 3 | 3 | 4 | 2 | 1 | **16** | B (A-pending) |
| 9 | **Cayley cubic / Brauer–Manin geometry** | A2-§1 | 5 | 5 | 0 | 2 | 2 | **15** | A (published; negative) |
| 10 | **Class-field / genus theory over `ℚ(√−210)`** | A2-§4 | 5 | 5 | 2 | 3 | 3 | **17** | A (bookkeeping) / C (gap) |
| 11 | **Probabilistic divisor model** (random-residue heuristic) | A2-§2.3 | 3 | 3 | 1 | 2 | 4 | **10** | D |
| 12 | **Additive-combinatorics / sumset `U+U+U`** | A2-§3 | 2 | 2 | 1 | 1 | 2 | **9** | C/D (restatement) |
| 13 | **Obláth density-1 identity** (`n+1` has `≡3 (4)` factor) | A1-C2 | 3 | 5 | 5 | 2 | 1 | **19** | **A** |

*(≥10 diverse hypotheses met: rows 1–13 span classical, algebraic-geometry, sieve/probabilistic,
additive, computational, and formal-verification strategies.)*

---

## 4. Elite-mode deep dives (top 3)

### 4.1 🥇 Complete `a = 3` characterisation — **now fully proven [A]**

This was the top-ranked item *and* the referee's one register violation (Claim 4). Elite mode did
what the referee demanded: **prove the `C`-bridge instead of labelling it A-pending.**

The chain, all in `Theorems/A3Characterization.lean` (+ `PrimeModThree.lean`), `sorry`-free:

```
A3Solvable k  ↔  A3Certificate k                                        (a3_iff_divisor)
A3Certificate k  ↔  ∃ d, d ∣ M² ∧ d % 3 = 2                             (a3_certificate_iff_divisor_two_mod_three,
                                                                          uses M ≡ 1 (mod 3): M_mod_three_eq_one)
∃ d, d ∣ M² ∧ d % 3 = 2  ↔  ∃ q, q.Prime ∧ q ∣ M ∧ q % 3 = 2           (divisor_two_mod_three_iff)
∃ q, q.Prime ∧ q ∣ M ∧ q % 3 = 2  ↔  p ≡ 2 (mod 3) ∨ (∃ q prime ∣ k+1, q ≡ 2 (mod 3))
                                                                        (prime_dvd_mul_two_mod_three_iff)
```

The non-trivial ingredient is `prime_factor_two_mod_three` (strong induction on `n`: if `n ≡ 2
(mod 3)` then `n` has a prime factor `≡ 2 (mod 3)`). The `M ≡ 1 (mod 3)` step uses that for prime
`p = 4k+1`, one has `4k+1 ≡ k+1 (mod 3)` and `3 ∤ k+1` (else `3 ∣ p`), so `M ≡ (k+1)² ≡ 1`.

**Outcome:** the observation is upgraded **B → A** by *proof*, and `research_update.md` §2.1 /
`problem_variants.md` M1 registers are corrected. Novelty claim is modest (a folklore-adjacent
corollary), per the referee.

### 4.2 🥈 One-sided divisor criterion (Agent 3, C1)

**Claim.** For `n ≡ 1 (mod 4)`, `a ≡ 3 (mod 4)`, `a > 0`, a solution with `x = (n+a)/4` exists iff
`M = n(n+a)/4` has a divisor `d` with `d ≡ −M (mod a)` (the second condition `a ∣ M²/d + M` is then
automatic). Computationally 0 mismatches for `a ∈ {3,7,11,19,23,31,43}`, `p ≤ 40000`, and composite
`a ∈ {15,21,…}` `p ≤ 30000`.

**Elite dive (this phase).** The `gcd(M,a)=1` case is elementary: `d ≡ −M` ⇒ `gcd(d,a)=1`, so
`e = M²/d ≡ M²·d⁻¹ ≡ −M (mod a)`. This is a clean `ZMod` lemma, **not yet written**. Priority: prove
the prime-`a` slice (`a = q` prime) as `certificate_iff_one_sided`. This collapses the two-condition
certificate to one condition and would make `a = 3` and `a = 7` *and every* prime-`a` case uniform.

**Status after elite dive:** still B (the gcd argument is a sketch), but flagged as the **single
best next Lean target** — short, uses only `ZMod` invertibility, no factorisation.

### 4.3 🥉 Two new parametric identities (Agent 3, C3)

**Claim.** For every prime `q ≡ 3 (mod 4)` and `n ≡ 1 (mod 4)`:

- `n ≡ −4 (mod q)`: `4/n = 1/x + 1/y + 1/z` with `x=(n+q)/4`, `y=n(n+q+4)/(4q)`, `z=n(n+q)(n+q+4)/(16q)`;
- `n ≡ −1 (mod q)`: `x=(n+q)/4`, `y=(n+q)(n+1)/(4q)`, `z=n(n+q)(n+1)/(4q)`.

Verified 0 failures to `p ≤ 10⁵` (primes `q ∈ {3,7,11,19,23,31}`), and to `n ≤ 5·10⁴` (composite
included) for `q ∈ {3,7,11,19}`.

**Elite dive.** These are pure `ring` identities (no factorisation) — the *cheapest possible*
formalisation, directly extending `ACases.lean`. For `q = 3` they reduce to the known `n ≡ 2 (mod 3)`
case. The `q = 7` identities are exactly the two 100%-success residue classes of the `a = 7`
characterisation. Formalising them would give **new, checkable, infinite solution families** and
would let `a = 7`'s "easy" strata be stated as theorems, not observations.

**Status after elite dive:** B (closed-form, but not yet in Lean). Recommended as the *companion*
target to §4.2.

---

## 5. What the tournament concluded

1. **Only the divisor-certificate reformulation adds structure** (Agent 2's central finding, confirmed
   by Agents 1, 3, 4). The geometric (Cayley cubic) and class-field routes contribute *negatives*
   (no Brauer–Manin obstruction) and *necessary* conditions, not sufficiency.
2. **The referee was right and the loop worked.** The one register violation (Claim 4) was a *correct*
   catch, and elite mode fixed it by completing the proof rather than relabelling.
3. **The highest-ROI remaining targets are all "collapse/identity" lemmas** (one-sided criterion,
   parametric families, `a=7` criterion), not deeper machinery. None of them crosses the six-class
   core — they make the *easy* strata checkable and uniform.
4. **The core remains untouched.** `n ≡ 1 (mod 8)`, six classes mod 840, minimal `a` conjecturally
   unbounded — every ranked item is either a reformulation, a specialisation, or a negative result.
   The tournament does not change that; it makes the *boundary* of what is currently provable exact.

*Written in accordance with the standing rules: no claim that the open problem is solved; no fake
proofs; no `sorry`; known / computational / conjectural / verified registers kept separate.*
