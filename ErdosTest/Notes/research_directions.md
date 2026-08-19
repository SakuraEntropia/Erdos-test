# Phase 6, Steps 2–4 — Research Directions, Selection, and Lemmas

> **Legend:** A = proven · B = computational · C = conjecture · D = AI-generated hypothesis.

---

## Step 2. Five research directions

### Direction 1 — Divisor-certificate reformulation

**Idea.** Prove a clean bijection between solutions `4/n = 1/x + 1/y + 1/z` and **divisor
certificates**: pairs `(d, e)` with `d·e = n²·x²` and congruences `d ≡ −nx (mod 4x−n)`,
`e ≡ −nx (mod 4x−n)`, together with `x > n/4`. This converts a 3-variable equation into a
1-variable + divisor question, and makes the mod-840 core a statement about divisors of `n²`.

**Related literature.** Elsholtz–Tao (counting), Swett (sieve), Mordell (identities are special
cases), all reduce through this parametrisation.

**Advantage.** It is the *unifying* language of every known method, it is elementary (ring +
divisibility), and it is where a genuinely new idea (a combinatorial/probabilistic certificate, or
a class-field input) would plug in.

**Obstruction.** The reformulation does not by itself solve anything; the divisor/condence
condition is hard to verify universally, and the hard core remains the hard core.

**Formalization difficulty.** **Low–medium** — very amenable to Lean (ring + `Nat` divisibility).

**Ranks:** feasibility **high**, novelty **medium**, depth **medium–high**.

### Direction 2 — Modular identity expansion

**Idea.** Systematically search (symbolically, as in `identity_search.py`) for higher-degree
identities and **formalize each one found**, pushing the elementary cover beyond `n ≡ 1 (mod 12)`
toward the full six-class reduction.

**Related literature.** Mordell, Rosati, Salez (modular equations), Terzi.

**Advantage.** Each proven identity is an immediate *verified* extension of `easy_classes`;
machine-checkable; the search is already prototyped.

**Obstruction.** By the classical structure this bottoms out at the six classes mod 840; it can
only *reproduce* known reductions, never cross the core.

**Formalization difficulty.** **Low** per identity (same `field_simp`+`ring` pattern).

**Ranks:** feasibility **high**, novelty **low**, depth **low–medium**.

### Direction 3 — Quadratic-form / class-field route

**Idea.** The six hard classes are exactly primes of the form `x² + 840y²`. Investigate whether
"`p = x² + 840y²`" is genuinely an obstruction by relating unit-fraction solutions to
representations of `p` by *other* (possibly genus-adjacent) quadratic forms, using quadratic
reciprocity / the Brauer–Manin necessary condition.

**Related literature.** Bright–Loughran (Brauer–Manin + Hilbert symbols), Yamamoto
(quadratic reciprocity conditions), classical genus theory.

**Advantage.** Attacks the *true* core from the arithmetic-geometry side; highest potential depth.

**Obstruction.** Likely very hard; class-field inputs are not in Mathlib; risk of rediscovering
the `p`-adic obstruction as necessary-but-not-sufficient.

**Formalization difficulty.** **Very high** (Brauer–Manin not in Mathlib; but Legendre symbol and
quadratic reciprocity *are*).

**Ranks:** feasibility **low**, novelty **high**, depth **high**.

### Direction 4 — 2-adic / valuation analysis of the core

**Idea.** Understand *exactly* why `n ≡ 1 (mod 8)` resists affine denominators (our Phase-4
observation), and try to convert the 2-adic obstruction into a *constructive* classification of
which `n` admit "small" solutions.

**Related literature.** Bright–Loughran (`p`-adic Hilbert-symbol condition), the classical
`n ≡ 1 (mod 8)` special-ness.

**Advantage.** Concrete and local; the failure mode is visible and testable; connects to the
divisor parametrisation via `v₂(4x−n)`.

**Obstruction.** May only re-derive the known necessary condition; turning necessity into
sufficiency is the whole problem.

**Formalization difficulty.** **Medium** (ZMod / valuation lemmas exist in Mathlib).

**Ranks:** feasibility **medium**, novelty **medium–high**, depth **medium**.

### Direction 5 — Exceptional-set structure + density

**Idea.** Combine Vaughan's density bound with a structural classification of hypothetical
exceptions to force the exceptional set to be finite/empty (e.g., show any exception must satisfy
two incompatible arithmetic conditions).

**Related literature.** Vaughan (1970), Pomerance–Weingartner (2026), Elsholtz (2001).

**Advantage.** If a gap/lower-bound argument closes the loop, it would *prove* the conjecture from
existing analytic machinery.

**Obstruction.** Requires the large sieve, which is **not in Mathlib**; the density gap argument is
not known to exist.

**Formalization difficulty.** **Very high** (no large sieve in Mathlib).

**Ranks:** feasibility **low**, novelty **medium**, depth **high**.

---

## Step 3. Selected direction

**Direction 1 — Divisor-certificate reformulation.**

*Why.* It is chosen **not** for simplicity but because it is the one reformulation under which
(i) the mod-840 core becomes an *explicit* arithmetic statement, (ii) every known deep result
(Elsholtz–Tao counting, Swett's sieve, Bright–Loughran's `p`-adic condition) is expressible, and
(iii) a new idea can be *tested computationally and formally*. The other four directions either
bottom out at the core (Direction 2), need machinery absent from Mathlib (Directions 3, 5), or are
special cases of this one (Direction 4). Establishing the bijection **in Lean** is a concrete,
verifiable milestone that unblocks all of them.

---

## Step 4. Concrete lemmas (for Direction 1)

**Lemma A — the symmetric (normalised) equivalent form.**
For all `n, x, y, z`,
`4xyz = n(xy + yz + zx)` ⟺ `(4x−n)(4y−n)(4z−n) = n²(4(x+y+z) − n)`.
*Classification:* **already known** (classical; appears implicitly throughout the literature).
*(A cleaner, purely-algebraic equivalent of the cleared form; proved by `ring`.)*

**Lemma B — the lower bound on any solution.**
If `4/n = 1/x + 1/y + 1/z` with `x, y, z > 0`, `n ≥ 2`, then `n < 4x` (equivalently `4x − n > 0`).
*Classification:* **already known / elementary** (necessary for the parametrisation to be valid).

**Lemma C — the divisor construction (sufficient direction).**
Let `n, x, d, e > 0` with `n < 4x`, `d·e = (nx)²`, and `(4x−n) ∣ (d + nx)`, `(4x−n) ∣ (e + nx)`.
Then, with `y = (d+nx)/(4x−n)` and `z = (e+nx)/(4x−n)`, we have
`4/n = 1/x + 1/y + 1/z`.
*Classification:* **already known** (this is the standard divisor parametrisation underlying
Elsholtz–Tao and Swett), *now formalized here*.

**Lemma D — a new (re-derived) identity covering `n ≡ 5 (mod 8)`.**
`4/(8k+5) = 1/(3k+2) + 1/(6k+4) + 1/(48k²+62k+20)`.
*Classification:* **already known** as part of the mod-840 reduction, but *discovered independently*
by our Phase-4 symbolic search; not previously in this project.

> All four are **provable** (Lemmas A, B, D by ring/arithmetic; Lemma C by ring + divisibility).
> **None is a new mathematical theorem** — they formalise/rediscover known structure. This is stated
> explicitly in `research_status.md`.
