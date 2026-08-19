# Erdos-test

A **`sorry`-free Lean 4 + Mathlib formalisation** of the elementary layer around the
**Erdős–Straus conjecture**, plus a disciplined, register-tagged research log. This is an
autonomous formal-mathematics research project: every claimed theorem is machine-checked, and
conjectural / computational / AI-generated material is kept strictly separate from proofs.

> **Status (honest, up front): the Erdős–Straus conjecture is NOT solved here.**
> No theorem in this repository implies the conjecture, and none claims to. What *is* here is a
> verified formalisation of the classical reductions and one folklore-adjacent new theorem, together
> with an explicit record of what remains open.

---

## The conjecture

For every integer `n ≥ 2`, the equation

```
4/n = 1/x + 1/y + 1/z
```

has a solution in positive integers `x, y, z`. It suffices to prove it for primes `p ≡ 1 (mod 4)`;
in fact (Phase 12) for primes `p ≡ 1 (mod 24)`. The hardest remaining classes are the six residue
classes `n ≡ 1, 121, 169, 289, 361, 529 (mod 840)` (Mordell's reduction).

## What is verified (register **A** — machine-checked, zero `sorry`)

- **Reduction to primes** — the conjecture holds iff it holds for all primes
  (`Theorems/MainResult.lean`), together with the even case and the `n ≡ 3 (mod 4)` case
  (`Theorems/Lemma1.lean`, `Lemma2.lean`).
- **Divisor–certificate bijection** — `4/n` is solvable iff there is a certificate
  `(a, d, e)` with `a + n = 4x`, `a ∣ d + nx`, `a ∣ e + nx`, `d·e = (nx)²`
  (`Theorems/Certificate.lean`, `solvable_iff_certificate`).
- **Parity structure** — for odd `n`, at most one of `x, y, z` is odd.
- **Complete `a = 3` characterisation** — for prime `p = 4k+1`, the minimal-certificate stratum
  `a = 3` is solvable iff `p ≡ 2 (mod 3)` **or** `(p+3)/4` has a prime factor `≡ 2 (mod 3)`
  (`Theorems/A3Characterization.lean`, `Theorems/PrimeModThree.lean`). This upgrades a computational
  observation to a verified theorem.
- **Obláth identity** — if `n+1` has a prime factor `≡ 3 (mod 4)`, then `4/n` is solvable
  (`Theorems/Classical.lean`).
- **One-sided divisor criterion** (Phase 9) — when `gcd(M, a) = 1`, the two certificate congruences
  collapse to one: `a ∣ d + M` alone forces `a ∣ M²/d + M` (`Theorems/NewStructures.lean`,
  `one_sided_certificate` / `certificate_iff_one_sided`). This unifies the `a = 3`, `a = 7`, … strata,
  and `gcd(M, a) = 1` is automatic for prime `a = q` when `n = p` is prime.
- **Partial theorems** (`Theorems/Phase11.lean`) — if `n` has a prime factor `≡ 3 (mod 4)` then `n`
  is solvable (so any counterexample has *all* prime factors `≡ 1 (mod 4)`); infinitely many `n` are
  solvable; and `d ∣ M²` iff every prime exponent of `d` is ≤ twice the exponent in `M`
  (the "bounded-exponent box" behind the divisor parametrisation).
- **Mordell reduction, first three steps** (`Theorems/Phase12.lean`) — the conjecture is equivalent
  to its restriction to primes `p ≡ 1 (mod 4)`, then to `p ≡ 1 (mod 12)`, then to `p ≡ 1 (mod 24)`
  (`reduction_to_primes_one_mod_four` / `_twelve` / `_twenty_four`). The mod-12 and mod-24 steps are
  genuine strengthenings: primes `p ≡ 5 (mod 12)` are covered by the `a = 3` stratum, and
  `n ≡ 5 (mod 8)` is always solvable via Mordell's identity (`solvable_of_five_mod_eight`). This
  pins the open core down to `p ≡ 1 (mod 24)`; the six hard classes `mod 840` are the remaining step.

## Register discipline

Every claim is tagged **A** (proven), **B** (computational evidence), **C** (conjecture), or
**D** (AI-generated hypothesis), and these are never mixed. Computational results live in
`Experiments/` (register **B**); conjectures and heuristics are labelled **C** / **D**.

## Layout

```
ErdosTest/
  Theorems/          # sorry-free Lean formalisation (imported by ErdosTest.lean)
    ErdosProblem.lean      # definitions + the conjecture
    Lemma1.lean, Lemma2.lean, MainResult.lean   # reduction to primes
    Certificate.lean       # divisor–certificate bijection + parity
    MinimalCertificate.lean, A3Characterization.lean, PrimeModThree.lean  # a = 3 theory
    Classical.lean, DivisorParam.lean, MinimalCertParam.lean, ACases.lean
    NewStructures.lean     # Phase 9: a-strata, divisor-residue set, one-sided criterion
    Phase11.lean           # Phase 11: partial theorems + divisor-exponent box
    Phase12.lean           # Phase 12: Mordell reduction mod 4 / 12 / 24
  Notes/             # research log (bottleneck, literature, tournament, stress test, …)
  Experiments/       # register-B Python computations
```

## Build

Requires [Lean 4](https://lean-lang.org/) with the toolchain pinned in `lean-toolchain`
(Lean `v4.33.0` + Mathlib `v4.33.0`).

```sh
lake build
```

The build is `sorry`-free and warning-free. CI (`.github/workflows/lean_action_ci.yml`) builds the
library on push.

## What remains open

The six-class core `n ≡ 1, 121, 169, 289, 361, 529 (mod 840)` is untouched by everything here. See
`Notes/bottleneck_analysis.md`, `Notes/final_classification.md`, and
`Notes/structure_stress_test.md` for the precise boundary of what is currently provable.

---

*No claim is made that the Erdős–Straus conjecture is solved; no `sorry`, `axiom`, or
`unsafe`-based proof is used anywhere in `Theorems/`.*
