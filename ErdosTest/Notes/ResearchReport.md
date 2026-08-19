# Phase 4 — Research Analysis: the Erdős–Straus Conjecture

> **Overall classification: B — partial progress with verified lemmas.**
> (Sub-results range from A to C; see §7. The conjecture itself remains **open**.)

This report reviews Phases 0–3 and one new Phase-4 experiment. Throughout we keep four
registers strictly separate, per the project rules:

- **Known mathematics** — results established in the literature / classical facts.
- **Experimental observations** — output of finite or bounded computations.
- **Conjectures** — statements we believe but have not proven.
- **Formally verified results** — statements accepted by Lean (`lake build` clean, no `sorry`).

---

## 1. Problem statement

**Erdős–Straus conjecture (1948).** For every integer `n ≥ 2` there exist **positive** integers
`x, y, z` such that

```
4/n = 1/x + 1/y + 1/z .
```

Equivalently (clearing denominators, over `ℚ`):

```
4xyz = n(xy + yz + zx).
```

The conjecture is verified computationally to very large `n` (in the literature up to ~10¹⁴),
but no proof is known. It is a special case of the more general question of which rationals are
sums of three unit fractions, and it is related to the deep theory of binary/ternary quadratic
forms.

---

## 2. Formalization

All in `ErdosTest/Theorems/`; the library root `ErdosTest.lean` imports them; `lake build` is
clean (17 416 jobs, no `sorry`/`admit`/`axiom` anywhere in the sources).

- `ErdosProblem.lean` — namespace `ErdosStraus`:
  - `IsDecomposition n x y z : Prop` — the fraction form over `ℚ`.
  - `IsDecompositionCleared n x y z : Prop` — the cleared form `4xyz = n(xy+yz+zx)`.
  - `Conjecture : Prop` — `∀ n, 2 ≤ n → ∃ x y z > 0, IsDecomposition n x y z`.
  - `isDecomposition_iff_cleared` — the two forms are equivalent (given `2 ≤ n`, `x,y,z > 0`).

The formalization uses `ℕ` for the object variables and `ℚ` for the equality, so positivity of
denominators (`x,y,z ≠ 0` over `ℚ`) is discharged by `positivity` and denominators are cleared
with `field_simp`. The only non-definitional work is this `iff` and a handful of algebraic
identities.

---

## 3. Computational evidence

All computations use exact rational arithmetic (`fractions.Fraction`) or exact integer
polynomial arithmetic; nothing is floating-point.

1. **Exhaustive enumeration** (`Experiments/brute_force.py`), `n = 2..60`:
   every `n` has a solution; 2 380 (order-normalized) solutions in total; no counterexample.
   *(Experimental, not a proof.)*

2. **Parametric identities, finite verification** (`Experiments/search_patterns.py`), `n ≤ 300`:
   four closed-form identities verified exactly on their residue classes — see §4.

3. **Symbolic identity search** (`Experiments/identity_search.py`) — **new in Phase 4**:
   a search for *parametric polynomial identities* `4/(mk+r) = 1/x + 1/y + 1/z` with `x, y`
   affine-linear in `k` and `z` forced (hence possibly quadratic), using **exact integer
   polynomial long division** (an identity is found only when the division of
   `nxy` by `4xy − n(x+y)` is exact with a nonnegative-integer quotient). This is a *symbolic*
   check: a found identity is **proven**, not merely sampled.

   Findings:

   - For moduli `m ≤ 12` it finds **33** covered residue classes, including several
     `n ≡ 1 (mod 4)` sub-classes (e.g. `n ≡ 5 (mod 8)` via `x=3k+2, y=6k+4, z=48k²+62k+20`,
     which specializes at `k=0` to the solution `(2,4,20)` of `n=5`).
   - Enlarging the coefficient bound to 60 still finds **no** affine-`(x,y)` identity covering
     `n ≡ 1 (mod 8)`, `n ≡ 1 (mod 12)`, `n ≡ 1 (mod 16)`, or `n ≡ 9 (mod 16)`.
     *(Bounded-search evidence, not a proof of impossibility.)*

   Interpretation (matches the classical structure): the elementary identities reduce the problem
   to `n ≡ 1 (mod 12)`; richer affine identities reduce it further to `n ≡ 1 (mod 8)`; and the
   known theory (see §6) pushes the hard core all the way to `n ≡ 1, 11², 13², 17², 19², 23²
   (mod 840)`.

---

## 4. Proven lemmas

These are all **formally verified in Lean** (class A individually).

| Lemma | Statement | Method |
|---|---|---|
| `two_has_decomposition` | `4/2 = 1/1 + 1/2 + 1/2` | `norm_num` |
| `even_decomposition` | `4/(2k) = 1/k + 1/(2k) + 1/(2k)` for `k>0` | `field_simp` + `ring` |
| `isDecomposition_iff_cleared` | fraction form ↔ cleared form | `field_simp` both ways |
| `two/three/four/five_has_solution`, `small_cases` | `n = 2,3,4,5` have solutions | explicit witnesses + `norm_num` |
| `three_divides` | `4/(3k) = 1/(2k)+1/(2k)+1/(3k)` | `field_simp` + `ring` |
| `two_mod_three` | `4/(3k+2) = 1/(k+1)+1/n+1/((k+1)n)` | `field_simp` + `ring` |
| `three_mod_four` | `4/(4k+3) = 1/(k+1)+1/(2(k+1)n)+1/(2(k+1)n)` | `field_simp` + `ring` |
| `easy_classes` | `2∣n ∨ 3∣n ∨ n%4=3` ⟹ solution exists | composition of the above |
| `scale` | a solution of `n` scales to a solution of `k·n` | cleared form + factoring `k³` |
| `scale_of_solution` | heredity packaged for `∃`-form | `scale` |
| `reduction_to_primes` | **`Conjecture ↔ ∀ prime p, solution exists`** | strong induction + heredity |

The last two are the structural core: the conjecture is *equivalent* to its restriction to
primes. Combined with `easy_classes`, the open problem is thereby reduced to **primes
`p ≡ 1 (mod 4)`** (even primes and `p ≡ 3 (mod 4)` are already settled).

---

## 5. Failed approaches

### 5.1 Covering congruences by polynomial identities (incomplete — the natural route)

**Idea.** If one could find, for some fixed modulus `M`, a *finite* set of parametric polynomial
identities covering **every** residue class `mod M`, then every `n ≥ 2` would lie in some covered
class and the conjecture would be proved outright. This is the "covering congruences" strategy
behind every known partial reduction.

**Why it might work.** It does produce a genuine, machine-checkable reduction: with finitely many
identities one eliminates all but a handful of residue classes. The four elementary identities
already eliminate everything except `n ≡ 1 (mod 12)`; the affine identities found in Phase 4
eliminate everything except `n ≡ 1 (mod 8)` (within the classes examined).

**The missing step.** Cover the surviving class `n ≡ 1 (mod 8)` — in particular `n ≡ 1 (mod 840)`
and the "square" classes `n ≡ 11², 13², 17², 19², 23² (mod 840)` — by polynomial identities.

**Test of the missing step.** I tested whether *affine* `(x,y)` identities can cover `n ≡ 1
(mod 8)`. With coefficients up to 40 (and separately up to 60), **no** such identity exists,
while nearby classes (`n ≡ 5 mod 8`, `n ≡ 9 mod 24`, `n ≡ 17 mod 24`) are covered. So the
barrier at `n ≡ 1 (mod 8)` is *real for affine denominators*, not an artifact of using only four
identities. *(This is bounded-search evidence, not a theorem.)*

**Why it fails to give a proof.** No finite polynomial cover has ever been found; the classical
identities bottom out at the six classes `mod 840` above, and it is *expected* (though not a
theorem we prove here) that no fixed-degree polynomial cover eliminates them all. The obstruction
is genuinely arithmetic, not combinatorial.

### 5.2 Naive guess `x = k+1` for `n = 4k+1` (fails)

Setting `x = k+1` (the natural affine choice for `n = 4k+1`) forces
`1/y + 1/z = 3/((4k+1)(k+1))`, i.e. `(3y − n(k+1))(3z − n(k+1)) = (n(k+1))²`, a divisor
condition on `n²`, not an identity in `k`. So a single fixed affine denominator cannot work for
the whole class; the solutions in `n ≡ 1 (mod 4)` are divisor-driven and irregular (cf. Phase 2,
observation 4), not polynomial.

### 5.3 Formalization pitfalls (Lean, not mathematics)

- `nlinarith` cannot close the *scaling* identity directly (degree-3 product); it had to be
  factored by hand (`k³·(4xyz) = k³·(n(xy+yz+zx))`) and closed by `ring`.
- `omega` cannot prove `2 ≤ k·n` from `2 ≤ n, 0 < k` (nonlinear product); this needed an explicit
  `n ≤ k·n` step via `Nat.mul_le_mul_left`.
- A local `have P : ℕ → Prop := …` used as an induction motive is opaque to `intro`/application;
  the motive had to be inlined for `Nat.strong_induction_on`.
- `Nat.mod_add_div` returns `n % 4 + 4·(n/4) = n` (not `… + (n/4)·4`); the order matters for `rw`.

These are recorded as reproducibility notes; none affects the mathematical content.

---

## 6. Possible future directions

1. **Formalize the new identities.** The Phase-4 symbolic search found several *provably valid*
   identities (e.g. the `n ≡ 5 (mod 8)` family) that are not yet in Lean. They would extend
   `Lemma2` and push `easy_classes` further, all in the same `field_simp + ring` style.

2. **Reproduce the mod-840 reduction formally.** Systematically search higher-degree identities
   and formalize enough of them to obtain, in Lean, the classical statement
   "Conjecture ⟸ solutions for all `n ≡ 1, 11², 13², 17², 19², 23² (mod 840)`". This would be a
   substantial but mechanical lemma pile, and a genuinely new *verified* reduction.

3. **Attack the hard core `n ≡ 1 (mod 8)`.** This is where elementary methods stop. Known partial
   progress uses the divisor reformulation
   `(4x−n)(4y−n)…`-type factorisations and counts solutions via divisors of `n²`; a Lean
   formalisation of even the *count* of solutions `4/n = 1/x+1/y+1/z` in terms of divisors of `n²`
   would be a useful, provable stepping stone.

4. **Connect to the 3-unit-fraction literature.** The conjecture is the `4/n` case of a family;
   results about `k/n = 1/x + 1/y + 1/z` (existence thresholds, exceptional sets) may be
   formalizable and would situate this project.

5. **Document the negative side rigorously.** Turn "no affine `(x,y)` identity covers
   `n ≡ 1 (mod 8)`" from a bounded search into a theorem (a 2-adic valuation argument), and
   formalize it — this would make the "barrier" a *proven* lemma rather than evidence.

---

## 7. Classification

| Result | Class |
|---|---|
| Formalization of the conjecture, equivalent forms (`ErdosProblem`) | **A** |
| Base cases `n = 2,3,4,5` (`Lemma1`) | **A** |
| Congruence identities & `easy_classes` (`Lemma2`) | **A** |
| Heredity `scale` and `reduction_to_primes` (`MainResult`) | **A** |
| New parametric identities found by `identity_search.py` | **A** (each identity symbolically proven; *not yet formalized in Lean*) |
| "No affine identity covers `n ≡ 1 (mod 8)`" | **C** (bounded search only) |
| Conjecture for all `n` | **C** (computational evidence only) — **open** |

**Overall: B — partial progress with verified lemmas.**

The project has rigorously established: the two equivalent formulations, finite base cases, four
parametric families, the heredity (scaling) property, and — most importantly — the **equivalence
of the conjecture to its prime-only form**, and (with the congruence lemmas) its reduction to
**primes `p ≡ 1 (mod 4)`**. The conjecture itself is **not** claimed solved, and no `sorry` or
unproven assertion appears anywhere in the formalization.
