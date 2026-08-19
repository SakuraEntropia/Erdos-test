# Phase 8b — Final Scientific-Standard Classification

> Classifies every *claimable* item this project has produced into the categories of a referee's
> verdict: **new theorem**, **known theorem (re-derived)**, **partial**, **conjecture**,
> **heuristic**, or **failed**. This is the scientific-standard audit that closes Phase 8b.
>
> **Registers:** **A** = proven (Lean-verified here or published) · **B** = computational ·
> **C** = conjecture · **D** = AI hypothesis.
>
> **Bottom line up front:** the conjecture is **not** solved; no claim of a solution is made. The
> project's net mathematical output is (i) a `sorry`-free Lean formalisation of the elementary layer,
> and (ii) **one new, now fully-proven, folklore-adjacent equivalence** (the `a = 3` characterisation).
> Everything else is re-derivation, negative result, or open direction.

---

## A. The one genuinely new *verified* statement

### A1. Complete `a = 3` characterisation — **NEW THEOREM (folklore-adjacent), [A]**

**Statement.** For prime `p ≡ 1 (mod 4)`, write `p = 4k+1`, `M = p·(k+1) = p(p+3)/4`. Then the
"minimal certificate" `a = 3` (i.e. a solution with `x = k+1`) exists **iff** `p ≡ 2 (mod 3)` or
`(p+3)/4` has a prime factor `≡ 2 (mod 3)`.

**Files.** `Theorems/A3Characterization.lean` (`a3_solvable_iff_two_mod_three_or_factor`,
`a3_solvable_iff_prime_factor`, `a3_certificate_iff_divisor_two_mod_three`),
`Theorems/PrimeModThree.lean` (`divisor_two_mod_three_iff`, `prime_factor_two_mod_three`),
`Theorems/MinimalCertificate.lean` (`a3_iff_divisor`).

**Classification rationale.**
- **Not new at the level of the conjecture**: it is a specialisation of the classical divisor
  parametrisation (Elsholtz–Tao / Swett / Salez), and the referee correctly judged it
  "folklore-adjacent … not a deep result."
- **New as a *stated and machine-checked* equivalence**: we did not find this exact `⟺` stated as a
  theorem in the literature we read, and it is now a `sorry`-free Lean theorem. So: **new theorem
  (minor), folklore-adjacent**, not a breakthrough.
- **It is not a step toward the conjecture**: it only decides the *easy* stratum (`a = 3`), which
  the referee notes is already covered for `n ≡ 5 (mod 8)` and `p ≡ 2 (mod 3)` by classical
  identities.

---

## B. Re-derivations (correct, not new) — **KNOWN THEOREMS, [A]**

| Item | File | Verdict |
|---|---|---|
| Reduction to primes + four congruence identities | `MainResult.lean`, `Lemma1/2.lean` | known, folklore **[A]** |
| Divisor-certificate bijection `solvable_iff_certificate` | `Certificate.lean` | known parametrisation; **linear change of variables**, no difficulty reduction **[A]** |
| Parity theorem (odd `n` ⇒ ≤ one odd denominator) | `Certificate.lean` | elementary, folklore **[A]** |
| `a3_iff_divisor` (solvable ⟺ certificate at `a=3`) | `MinimalCertificate.lean` | specialisation of the above **[A]** |
| Obláth density-1 identity | `Classical.lean` (`oblath_identity`) | published (Obláth 1950) **[A]** |
| Divisor-split `a·b = n², 4x = a+n, 2y = b+n` | `Classical.lean` (`divisor_split_eq`) | classical **[A]** |
| `divisor_two_mod_three_iff` (divisor `≡2 (3)` of `M²` ⟺ prime factor `≡2 (3)` of `M`) | `PrimeModThree.lean` | standard prime-factorisation fact, new *Lean* proof **[A]** |

**Significance verdict** (per referee): the bijection is *equivalent* to the conjecture —
`HasCertificate n` is exactly as hard as `Solvable n` — so these re-derivations reorganise without
reducing. Architectural value, not mathematical progress.

---

## C. Negative results — **[A] (some not yet in Lean)**

| Item | Verdict |
|---|---|
| No Brauer–Manin obstruction (Bright–Loughran 2020) | known **negative**; removes one counterexample route **[A]** |
| Yamamoto / Bright–Loughran `p`-adic Hilbert-symbol conditions are *necessary* only | known **[A]** |
| Trivial split `4x−p ∣ p·x` impossible for prime `p ≡ 1 (4)` | classical, **not yet in Lean** (Agent 1 C3) **[A]** |
| `a = 3` trick does **not** generalise to `a = 7` (no single residue, since `−M mod 7` ranges over 6 residues) | understood obstruction **[A]** |

---

## D. Computational observations — **[B]**

| Item | Verdict |
|---|---|
| `a = 3` characterisation, 0 mismatches to `p = 30000` | **now redundant** (superseded by A1 proof) **[B]** |
| One-sided divisor criterion, 0 mismatches to `p = 40000` | **B**, `gcd(M,a)=1` case A-pending **[B]** |
| Two new parametric identities `n ≡ −4, −1 (mod q)`, 0 failures | **B**, ring-only, easiest to formalise **[B]** |
| `a = 7` complete characterisation, 0 mismatches to `p = 10⁵` | **B**, A-pending **[B]** |
| Minimal-`a` value set `{3,7,…,59}` complete initial segment, `p ≤ 2·10⁶` | **B** (finite range) **[B]** |
| Refutation of "minimal `a ≤ 23`" / "minimal `a ∈ {3,7}`" | **failed over-claim**, correctly caught **[B→failed]** |

---

## E. Conjectures and heuristics — **[C] / [D]**

| Item | Verdict |
|---|---|
| Minimal `a` is unbounded (grows) | **C** (conjecture), supported by records `3,7,11,15,19,23,31,59` **[C]** |
| Every `a ≡ 3 (4)` occurs as a minimal `a` for some prime | **C/D** (not provable from data) |
| "No affine identity covers `n ≡ 1 (8)`" | **D** (bounded-search observation dressed in 2-adic language; parity theorem does *not* imply it — referee) |
| Probabilistic divisor model ⇒ `f(n) ≥ 1` for all `n` | **D** (model gives density-1 only, cannot deliver `∀`) |
| Genus→class gap over `ℚ(√−210)` *is* the conjecture | **C** (precise equivalence statement, not independent result) |
| Monotone descent / Vieta involution on the Cayley cubic | **D** (no such order is known to exist) |

---

## F. Failed (refuted) hypotheses

| Item | How it failed |
|---|---|
| "Minimal `a ≤ 23`" | refuted at `a = 31`, `p = 21169` (extending to 30000) |
| "Minimal `a ∈ {3,7}`" | refuted at `a = 11`, `p = 1129` |
| "Attainable divisor residues form the subgroup of `(Z/a)^×`" | refuted: exponents are *bounded* `0..2e_i`, so it is a bounded-exponent product set, not a subgroup (Agent 3 corrective note) |
| Degree-≤2 two-square parametrisation `4/(u²+v²)` | **D**, likely false (would solve the conjecture) |

---

## G. The standing conjecture itself

**The Erdős–Straus conjecture remains open [C].** Nothing in A–F implies it, and no such claim is
made. The verified content is a faithful formalisation of the *elementary* layer plus one minor new
theorem; the six-class core (`n ≡ 1 (mod 8)`, `{1,121,169,289,361,529} (mod 840)`) is untouched.

*Written in accordance with the standing rules: no claim that the open problem is solved; no fake
proofs; no `sorry`; known / computational / conjectural / verified registers kept separate.*
