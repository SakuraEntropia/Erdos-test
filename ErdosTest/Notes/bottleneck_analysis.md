# Phase 6, Step 1 — Bottleneck Analysis

> **Legend:** A = proven · B = computational · C = conjecture · D = AI-generated hypothesis.

---

## 1. What prevents current methods from solving the problem?

Every known method proves the conjecture **on a set of density 1** or **outside a small explicit
residue core**, but no method handles the core itself. Concretely:

**(a) Modular / parametric identities are not closed.** Each family of polynomial identities
`4/(mk+r) = 1/x(k) + 1/y(k) + 1/z(k)` eliminates some residue classes, always leaving others.
The classical bottom of this hierarchy is **Mordell's six classes** `mod 840`
(`n ≡ 1, 121, 169, 289, 361, 529`). Going to higher precision (Salez) replaces the six classes by
millions of classes mod a huge modulus, but never removes *all* of them. There is no known
*fixed-degree finite polynomial cover*. [A for the reductions; C for "no finite cover exists".]

**(b) Analytic methods give density, not totality.** Vaughan's large-sieve bound
`#exceptions ≤ N exp(−c(log N)^{2/3})` (and its generalisations) says the exceptional set has
density 0. It cannot exclude a *sparse infinite* exceptional set, which is what the conjecture
denies. [A]

**(c) Counting methods are one-sided.** Elsholtz–Tao / Planitzer bound `f(p) ≤ p^{3/5+o(1)}` and
`Σ f(p) = N(log N)^{2+o(1)}` — solutions are plentiful *on average*, but this cannot rule out a
prime with `f(p) = 0`. [A]

**(d) Geometric methods certify the *absence* of an obstruction.** Bright–Loughran show there is
no Brauer–Manin obstruction, i.e. this particular route to a *counterexample* is empty. A necessary
`p`-adic Hilbert-symbol condition exists, but it is far from sufficient. [A]

**In one sentence:** the problem is **stuck at the six-class core** `p ≡ 1, 121, 169, 289, 361, 529
(mod 840)` — equivalently primes `p ≡ 1 (mod 24)` that are quadratic residues mod 5 and mod 7 —
and every tool either *avoids* this core (identities), *ignores* it (density), or *explains why it
is special* without producing solutions (Brauer–Manin).

---

## 2. What assumptions would be sufficient for a proof?

Each of the following, if true and proved, would settle the conjecture (or a large part of it):

1. **A finite polynomial cover exists.** If, for some modulus `M`, every residue class `mod M`
   is covered by a (fixed-degree) polynomial identity, the conjecture follows immediately.
   *(Believed false in fixed degree; unproven either way.)* [C]

2. **A constructive converse to the `p`-adic obstruction.** If the Bright–Loughran necessary
   condition could be reversed — "no `p`-adic obstruction ⟹ a solution exists" — the conjecture
   would be a theorem. (This is essentially the conjecture itself restated.) [C]

3. **A uniform bound on solution "complexity".** If one could show that any solvable `n` has a
   solution with `max(x,y,z) ≤ C·n^α` for explicit `C, α`, then (combined with a finite search up
   to that bound) the problem reduces to a finite computation per `n` — turning it into a question
   of a *uniform* certificate. [C]

4. **A divisor-certificate criterion.** If one proves the equivalent form (see §3) that `4/n` is
   solvable ⟺ `n` admits a divisor `d ∣ n²` with a specified congruence, then any structure theorem
   about divisors of `n²` becomes a route to a proof. [C — this is the direction we develop in Step 2.]

5. **Exceptional-set structure theorem.** If the exceptional set (known to have density 0) could be
   shown to be *finite* (or empty), e.g. by combining Vaughan's bound with a lower bound on the gap
   between successive hypothetical exceptions. [C]

---

## 3. Which parts of the problem have the most unexplored structure?

1. **The divisor parametrisation.** Solutions of `4/n = 1/x + 1/y + 1/z` are governed by divisors
   of `n²`. This is the *only* reformulation under which the mod-840 core becomes a clean
   arithmetic statement, and it is exactly the structure used by Elsholtz–Tao, Swett, and every
   computational sieve. It is **under-formalised**: no clean bijective statement exists in Lean.

2. **The quadratic-form interpretation.** The six hard classes are precisely primes represented by
   `x² + 840y²` (equivalently, primes that are quadratic residues mod 840). The relation between
   "`p` represented by a small genus form" and "`4/p` has a solution" is suggestive and largely
   unexplored from the unit-fraction side. [C]

3. **The `2`-adic / valuation obstruction.** All six hard classes are `≡ 1 (mod 8)`. Our Phase-4
   search found affine-`(x,y)` identities cover `n ≡ 5 (mod 8)` but never `n ≡ 1 (mod 8)`. The
   exact 2-adic mechanism (why `v₂` changes at `n ≡ 1 mod 8`) is a concrete, tractable local
   question. [D]

4. **The counting function's divisor structure.** `f(n)` has a known expression in terms of the
   divisor-counting and a "modular" weight; Elsholtz–Tao exploit this for averages. The *pointwise*
   behaviour at the hard core is the frontier.

---

**Conclusion of Step 1.** The obstacle is **not** a lack of partial results but a **structural
wall** at the six-class core, which is best attacked through its **divisor parametrisation** — the
one reformulation that simultaneously (i) makes the core explicit, (ii) underlies all known methods,
and (iii) is elementary enough to formalise. This motivates the direction selected in Step 2.
