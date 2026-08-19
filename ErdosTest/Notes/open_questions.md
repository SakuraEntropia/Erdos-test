# Phase 5 — The Mathematical Bottleneck and Open Questions

> **Legend:** **A** = proven · **B** = computational evidence · **C** = conjecture ·
> **D** = new AI-generated hypothesis.

---

## 1. What is already solved?

- **Reduction to primes.** The conjecture is equivalent to its prime-only form, and (with the
  even and `p ≡ 3 (mod 4)` identities) to **primes `p ≡ 1 (mod 4)`**. **[A — verified in Lean]**
- **All residue classes except six.** By Mordell's identities, every `n` outside
  `{1, 121, 169, 289, 361, 529} (mod 840)` has a solution. **[A — published]**
- **Almost all `n`.** Vaughan (and generalisations) show the exceptional set has density 0.
  **[A — published]**
- **No local obstruction.** There is no Brauer–Manin obstruction; the only obstruction found is a
  `p`-adic *necessary condition*, not a counterexample. **[A — published]**
- **Very large finite range.** Verified for all `n < 10^14` (Swett), `10^17` (Salez), `10^18`
  (claimed). **[B]**

## 2. The exact open statement

**Conjecture (open).** For every prime `p ≡ 1 (mod 4)` there exist positive integers `x, y, z`
with `4/p = 1/x + 1/y + 1/z`.

Equivalently (cleared form): for every prime `p ≡ 1 (mod 4)` there are `x, y, z > 0` with
`4xyz = p(xy + yz + zx)`.

The **hardest unresolved core** is the set of primes in the six classes
`p ≡ 1, 121, 169, 289, 361, 529 (mod 840)` — i.e. primes `≡ 1 (mod 24)` that are quadratic
residues mod 5 and mod 7 (equivalently, primes of the form `x² + 840y²`).

## 3. Why existing methods fail (the bottleneck)

1. **Modular / parametric identities are not closed.** Each new family of polynomial identities
   covers more classes but always leaves a residue class (or, at higher precision, a family
   `p ≡ r (mod M)`) uncovered. There is no known **finite** set of *fixed-degree* polynomial
   identities that covers all classes; the six-class core `mod 840` is the classical point where
   the elementary identities bottom out. [Mordell; Salez's `mod 840` sieve; our Phase-4 search.]

2. **The surviving class is the one where the "obvious" parametrisations degenerate.** For
   `p ≡ 1 (mod 4)` the three denominators `x, y, z` must be spread over the divisor structure of
   `p²`, and the parity/`2`-adic behaviour changes: the affine-`(x,y)` identities cover
   `p ≡ 5 (mod 8)` but not `p ≡ 1 (mod 8)` **[D — bounded-search hypothesis; see §5]**. This is a
   genuine, recurring obstruction, not a coincidence of a handful of formulas.

3. **Counting methods are one-sided.** Elsholtz–Tao/Planitzer bound the number of solutions but
   cannot rule out that some prime has *zero* solutions; they show solutions are numerous *on
   average*, not that none vanish. **[A, but insufficient]**

4. **Analytic methods (large sieve / circle method) only give density results.** Vaughan-type
   theorems show "almost all", and cannot exclude a sparse infinite exceptional set — the
   conjecture needs *all*, not almost all. **[A, but insufficient]**

5. **Geometric methods (Brauer–Manin) certify no obstruction.** Bright–Loughran show this
   obstruction cannot disprove the conjecture, which *removes* a possible route to a
   counterexample but does not construct solutions. **[A, but insufficient]**

**In one sentence:** every known method proves the conjecture on a set of density 1, or on all
classes except a small explicit residue core, but **none handles the single remaining core of
primes `p ≡ 1 (mod 24)` quadratic-residue mod 5,7** — and there is a real (2-adic + quadratic
reciprocity) obstruction concentrated exactly there.

---

## 4. Open questions (ranked)

**Q1 (the conjecture itself).** Is `4/p = 1/x + 1/y + 1/z` solvable for *every* prime
`p ≡ 1 (mod 4)`?

**Q2 (finite polynomial cover).** Is there a finite set of *polynomial* identities covering all
residue classes mod some `M`? (If yes, the conjecture is proven; the six-class core suggests the
answer may be "no" for fixed degree, but this is **not** established.)

**Q3 (the exact core).** Can the core be pushed beyond `mod 840` — e.g. to a smaller set of
classes mod `lcm(840, …)` — by higher-degree identities? (Known: Salez pushes to `S₂₉`, leaving
~2×10⁶ classes mod a huge modulus; still finite and still not closed.)

**Q4 (necessary conditions).** Do the Bright–Loughran / Yamamoto quadratic-reciprocity conditions
admit a constructive converse — i.e. is the absence of a `p`-adic obstruction also *sufficient*?
(No; that would be the conjecture, and it is not known.)

**Q5 (formalisation).** Which published reduction can be pushed into Lean next? Concretely:
formalise (a) the divisor-count formula `f(n) = …`, and (b) the six-class reduction `mod 840`,
as the natural next verified milestones.

---

## 5. Separation of registers — summary for this phase

| Item | Register |
|---|---|
| Conjecture reduces to primes `p ≡ 1 (mod 4)` | **A** (Lean-verified here) |
| Even / `≡3 (mod 4)` / `≡0,2 (mod 3)` identities | **A** (Lean-verified here) |
| Mordell's six-class reduction `mod 840` | **A** (published; not yet in Lean) |
| Vaughan / Pomerance–Weingartner density bounds | **A** (published; large sieve not in Mathlib) |
| Elsholtz–Tao / Planitzer counting bounds | **A** (published) |
| Bright–Loughran no-Brauer–Manin | **A** (published) |
| Verified for `n < 10^14 / 10^17 / 10^18` | **B** (computation) |
| Our `brute_force.py` (n ≤ 60) and `search_patterns.py` (n ≤ 300) | **B** (computation) |
| "No affine `(x,y)` identity covers `n ≡ 1 (mod 8)`" | **D** (bounded-search hypothesis) |
| "No finite polynomial cover exists" | **C** (conjectural belief, not proven) |
| The Erdős–Straus conjecture itself | **C** (open) |

**Bottom line.** The frontier is precisely the six-class core `mod 840` (equivalently primes
`p ≡ 1 (mod 24)`, quadratic residues mod 5 and 7). Every route that is *provable today* stops at,
or just short of, this core; no route is known to cross it. This project's verified contribution
so far is the *reduction to primes* and the *elementary congruence lemmas*; the next verifiable
milestones are the divisor-count formula and the six-class reduction.
