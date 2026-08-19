# Phase 8, Step 6 — Research Score

> Legend: A = proven · B = computational · C = conjecture · D = AI hypothesis.
> Scores are 0–10, with a one-line justification each. Graded **honestly** against the standing rule:
> no claim that the open problem is solved.

---

## Scores for the Phase-8 contribution (the `a = 3` / minimal-certificate refinement)

| Axis | Score | Justification |
|---|---:|---|
| **Mathematical novelty** | **3 / 10** | The `a = 3` characterisation is a clean corollary of the *known* divisor parametrisation (Elsholtz–Tao / Swett). It is a new *observation* and a new *formalisation*, but not a new deep theorem, and it does not touch the hard core. |
| **Formal verification** | **8 / 10** | Five new lemmas/theorems machine-checked this phase (`a3_iff_divisor`, `a3_solvable_gives_divisor`, `x_ge_minimal`, `three_dvd_4k1_iff_three_dvd_k1`, plus the ACases set), all with no `sorry`, `lake build` clean (17424 jobs). The certificate bijection is now fully bidirectional in Lean. |
| **Connection to original Erdős problem** | **6 / 10** | Directly on the `p ≡ 1 (mod 4)` core and its *minimal* solutions; isolates `a = 3` exactly and shows it cannot finish the conjecture (minimal `a` grows). But it is a reformulation, not a reduction of difficulty. |
| **Potential research value** | **5 / 10** | The "minimal certificate" lens and the factorisation-free `a = 3` iff are a fresh, tractable scaffold for the next target (prime-factor characterisation, divisor-count formula). Moderate upside, not obviously decisive. |

**Overall: 5.5 / 10 (B).**

---

## Cumulative project score (across phases 0–8)

| Axis | Score | Justification |
|---|---:|---|
| Mathematical novelty | **3 / 10** | Reductions/parametrisations all formalise known mathematics; no new theorem. |
| Formal verification | **8 / 10** | A clean, growing, `sorry`-free Lean library: reduction to primes, congruence lemmas, divisor parametrisation (A–D), certificate bijection (E), parity theorem, minimal-certificate theory. |
| Connection to Erdős problem | **7 / 10** | Every verified lemma is about ES proper; the core is precisely located but un-crossed. |
| Potential research value | **5 / 10** | A solid verified scaffold for the elementary layer; the deep layer (large sieve, Brauer–Manin) is out of Mathlib reach. |

**Cumulative: 5.75 / 10 (B).**

---

## Termination criterion (Step 7)

**Met: B — a meaningful partial result was obtained.**

Specifically, this phase produced a **new Lean-verified theorem** — `a3_iff_divisor`, the bidirectional
minimal-certificate characterisation — together with `x_ge_minimal` and the mod-3 bridge. This is a
*meaningful partial result* (formalisation-grade progress), **not** a new deep mathematical theorem, and
**not** a step that crosses the six-class core. The phase also **refuted** two over-strong finite
conjectures ("minimal `a ≤ 23`", "minimal `a ∈ {3,7}`") by extending the search to `p = 30000`.

No statement of "solved" is made; the conjecture remains **open**.

---

*Written in accordance with the standing rules: no claim that the open problem is solved; no fake proofs;
no `sorry`; registers kept separate.*
