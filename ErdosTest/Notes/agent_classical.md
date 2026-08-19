# Missing Classical Arguments for the Erdős–Straus Conjecture

> **Legend (used on every claim):**
> **A** = proven (Lean-verified in this repo, or published) ·
> **B** = computational evidence · **C** = conjecture / conjectural idea ·
> **D** = new AI-generated hypothesis (not independently established).
>
> **Honesty statement.** Nothing in this note claims to solve the conjecture. The conjecture
> (for every prime `p ≡ 1 (mod 4)` there are `x,y,z > 0` with `4/p = 1/x+1/y+1/z`) remains
> **open [C]**. The six-class core `p ≡ 1, 121, 169, 289, 361, 529 (mod 840)` remains un-crossed.
> Two classical identities below are **newly Lean-verified** (`Theorems/Classical.lean`); the
> rest are candidate arguments with honest feasibility assessments.

---

## 1. Where each classical method stops (precisely)

### 1.1 Elementary congruence identities → `n ≡ 1 (mod 12)` → `n ≡ 1 (mod 8)`

Four identities, all Lean-verified **[A]**:

| identity | class | file |
|---|---|---|
| `4/(2k) = 1/k + 1/(2k) + 1/(2k)` | `n ≡ 0 (2)` | `even_decomposition` |
| `4/(3k) = 1/(2k) + 1/(2k) + 1/(3k)` | `3 ∣ n` | `three_divides` |
| `4/(3k+2) = 1/(k+1) + 1/(3k+2) + 1/((k+1)(3k+2))` | `n ≡ 2 (3)` | `two_mod_three` |
| `4/(4k+3) = 1/(k+1) + 1/(2(k+1)n) + 1/(2(k+1)n)` | `n ≡ 3 (4)` | `three_mod_four` |

Together these cover all `n` except `n ≡ 1 (mod 12)` **[A]** (`easy_classes`). The affine-`(x,y)`
identity machine (`identity_search.py`, bounded coefficient search) then covers `n ≡ 5 (mod 8)`
and further sub-classes, but **stalls at `n ≡ 1 (mod 8)`** — no affine-`x,y` identity is found
there **[B** for the search, **D** for the extrapolated "no affine identity exists"**]**.
Note the first identity of the second row (`n ≡ 2 (mod 3)`) *is* the `q = 3` case of Obláth (1.2).

### 1.2 Obláth (1950): `n+1` has a prime factor `≡ 3 (mod 4)` ⟹ solvable

**Precise identity (derived here; Lean-verified, `oblath_identity`).** **[A]**
If `q = 4s+3` and `n + 1 = q·m` (i.e. `q ∣ n+1`), then

```
4/n = 1/((s+1)m) + 1/((s+1)n) + 1/((s+1)mn).
```

(For `q = 3`, i.e. `s = 0`, this is exactly `1/m + 1/n + 1/(mn)`, the `n ≡ 2 (mod 3)` identity.)
When `q` is prime `≡ 3 (mod 4)`, this shows every `n` with such a prime in `n+1` is solvable.

**Where it stops.** It fails precisely when `n+1` has *no* prime factor `≡ 3 (mod 4)`, i.e.
`n+1 = 2^α · (∏ qᵢ with all qᵢ ≡ 1 (mod 4))`. The first surviving prime is
`p = 73` (`73+1 = 2·37`, and `37 ≡ 1 (mod 4)`) **[A]**. The complement has natural density 0
(the count of `m ≤ X` all of whose prime factors are `≡ 1 (mod 4)` is `o(X)`), so Obláth covers
**density 1** but leaves an infinite sparse set, which contains primes **[A]**.

### 1.3 The divisor-split: `n²` has a divisor `≡ 3 (mod 4)` ⟹ solvable

**Lemma C1 (Lean-verified, `divisor_split_eq`).** **[A]**
If `a·b = n²`, `4x = a + n`, `2y = b + n` (all positive), then `4/n = 1/x + 1/y + 1/y`.

This is the **trivial split** `d = e = n·x` of the divisor parametrisation `(ay − nx)(az − nx) = (nx)²`
(from `DivisorParam.lean`), valid exactly when `a := 4x − n` divides `n·x`. Since `a ≡ −n (mod 4)`,
`a ∣ n·x ⟺ a ∣ n(a+n)/4 ⟺ a ∣ n²`.

**Corollary (classical).** **[A]** If `n ≡ 1 (mod 4)` and `n²` has a divisor `a ≡ 3 (mod 4)`,
then `4/n` is solvable, with `x = (a+n)/4`, `y = z = (b+n)/2`, `b = n²/a` (integrality from
`a ≡ 3`, `n ≡ 1 (mod 4)` forcing `4 ∣ a+n` and `2 ∣ b+n`).

**Where it stops.** `n²` has a divisor `≡ 3 (mod 4)` iff `n` has a prime factor `≡ 3 (mod 4)`.
So this handles every composite `n ≡ 1 (mod 4)` with a `≡ 3 (mod 4)` prime factor, and stalls at
`n ≡ 1 (mod 4)` all of whose prime factors are `≡ 1 (mod 4)` — and is **vacuous for primes
`p ≡ 1 (mod 4)`**, since `p²` has only the divisors `1, p, p²`, all `≡ 1 (mod 4)`. This is a
clean, checkable explanation of *why primes are the crux*.

### 1.4 The trivial split is impossible for primes (new clean lemma)

**Lemma C3 (classical; formalization sketched in §3.3).** **[A]** For a prime `p ≡ 1 (mod 4)`
there is **no** `x` with `4x − p ∣ p·x`.

*Proof sketch.* Let `a = 4x − p`. Then `a ≡ −p ≡ 3 (mod 4)`, so `a` is odd. If `a ∣ p·x =
p(a+p)/4`, then (as `gcd(a,4)=1`) `a ∣ p(a+p)`, and `a ∣ p·a` forces `a ∣ p²`. For prime `p`,
`a ∈ {1, p, p²}`, all `≡ 1 (mod 4)` — contradicting `a ≡ 3 (mod 4)`.

*Consequence.* The greedy/trivial split can **never** produce a solution for a prime `p ≡ 1 (mod 4)`;
primes force the *nontrivial* divisor machinery (e.g. the `a = 3` case, §3.4), which is exactly
where the difficulty concentrates.

### 1.5 Mordell's six-class reduction `mod 840`

**Statement.** **[A]** The conjecture holds for every `n` except possibly
`n ≡ 1, 121, 169, 289, 361, 529 (mod 840)`.

**Characterisation (checked by hand here).** **[A]** The six classes are precisely
- `n ≡ 1 (mod 24)`, `n ≡ 1,4 (mod 5)`, `n ≡ 1,2,4 (mod 7)` (that is `≡1 (mod 8)`, `≡1 (mod 3)`, quadratic residue mod 5 and mod 7); and
- perfect squares mod 840: `1², 11², 13², 17², 19², 23²`; and (per the literature / OEIS A139665)
- primes represented by `x² + 840y²`.

The proof is a finite family of ~200 modular identities; the `a = 3` and `a = 7` constructions
cover everything **outside** the simultaneous-quadratic-residue core (`(p/5) = (p/7) = 1`), and
any hard-class prime needing minimal certificate `a ≥ 11` lies in the six classes **[A / B]**.

### 1.6 Yamamoto (1965) / Bright–Loughran (2020) — necessary, not sufficient

**Statement.** **[A]** Yamamoto gives quadratic-reciprocity necessary conditions on a solution;
Bright–Loughran show there is **no Brauer–Manin obstruction**, and that any odd-`n` solution must
satisfy a `p`-adic Hilbert-symbol condition `∏_{p∣n} (−u₁/u₃, −u₂/u₃)_p = −1`.

**Where it stops.** These are **necessary** conditions (they certify that the obstruction route to
a *counterexample* is empty), far from sufficient. Reversing them would be the conjecture itself **[C]**.

### 1.7 Vaughan / Elsholtz–Tao — density, not totality

**Statement.** **[A]** Vaughan: `#exceptions ≤ N exp(−c(log N)^{2/3})` (large sieve).
Elsholtz–Tao / Planitzer: `f(p) ≤ p^{3/5+o(1)}`, `Σ f(p) = N(log N)^{2+o(1)}`.

**Where it stops.** Density / average statements cannot exclude a *sparse infinite* exceptional set,
which is exactly what the conjecture denies.

### 1.8 Synthesis: why the machine stalls at the six classes

The six classes are exactly the primes `p` that (i) are `≡ 1 (mod 8)` — killing every affine
identity (1.1) and the trivial split (1.4) — and (ii) are quadratic residues modulo 5 and 7 —
killing the `a = 3`/`a = 7` completions (1.5). Equivalently `p` "looks like a square" modulo every
prime dividing 840, so every *small-`a`* divisor construction degenerates. The elementary machine
stalls exactly where all the small moduli simultaneously treat `p` as a square **[A for the pieces,
C for "this is why it is hard" as an explanation]**.

---

## 2. Candidate missing classical arguments

### C1 — Divisor-split on `4x − n` ("`a ∣ n²`"). **Status: PROVEN, Lean-verified. [A]**

**Lemma.** `a·b = n²`, `4x = a+n`, `2y = b+n` (all `>0`) ⟹ `4/n = 1/x + 1/y + 1/y`.
Corollary: `n ≡ 1 (mod 4)` with a divisor `a ≡ 3 (mod 4)` of `n²` is solvable.

- **Proof attempt (done).** The equation is a pure `field_simp`+`ring`/`nlinarith` identity; the
  integrality of `x = (a+n)/4`, `y = (b+n)/2` is `mod 4` parity (`omega`). Verified:
  `Theorems/Classical.lean`, `divisor_split_eq`.
- **Why it is a step forward.** It converts the *unsolvability* question for `n ≡ 1 (mod 4)` into a
  single divisibility statement on `n²`, and cleanly localises the obstruction to primes (1.4).
- **Honest limit.** It does **not** touch primes `p ≡ 1 (mod 4)` — for them `p²` has no
  `≡ 3 (mod 4)` divisor, so the lemma is vacuous. It is a *reorganisation*, not a crossing of the core.
- **Lean-formalizability.** **Done** (identity only; the corollary is a short `omega`/`Nat.mul_le_mul`
  wrapper). `field_simp` + `ring` + `nlinarith` suffice; no sieve, no Brauer–Manin.

### C2 — Obláth's explicit identity. **Status: PROVEN, Lean-verified. [A]**

**Lemma.** `n + 1 = (4s+3)·m` ⟹ `4/n = 1/((s+1)m) + 1/((s+1)n) + 1/((s+1)mn)`.

- **Proof attempt (done).** Pure polynomial identity (verified `oblath_identity`).
- **Why it is a step forward.** It is the *correct, explicit* form of the density-1 result; the
  project previously only had the `q = 3` slice (`two_mod_three`). Now the full `q ≡ 3 (mod 4)`
  family is machine-checked.
- **Honest limit.** Density 1 only; leaves the sparse `n+1 = 2^α ∏ (≡1 mod 4 primes)` set, starting
  at `p = 73`.
- **Lean-formalizability.** **Done.** `field_simp` + `push_cast` + `ring` only.

### C3 — Trivial-split impossibility for primes. **Status: classical lemma, NOT yet in Lean. [A]**

**Lemma.** Prime `p ≡ 1 (mod 4)` ⟹ `∀ x, ¬ (4x − p ∣ p·x)`.

- **Proof attempt.** As in §1.4: `a = 4x−p ≡ 3 (mod 4)`; `a ∣ px ⟹ a ∣ p²` (using `a ∣ p(a+p)` and
  `a ∣ pa`); `a ∣ p² ⟹ a ∈ {1,p,p²}` (needs the divisor classification of `p²`); all `≡ 1 (mod 4)`.
- **Why it is a step forward.** It is the *clean negative* explaining why the greedy split dies at
  primes — a precise "missing" statement that the notes currently only gesture at ("affine barrier
  at `n ≡ 1 (mod 8)`" is a bounded-search D, whereas this is an unconditional A).
- **Honest limit.** Negative result; it tells us what *cannot* work, not what does.
- **Lean-formalizability.** **Medium (not done here).** Needs one factorization-flavoured lemma —
  `Nat.Prime p → d ∣ p² → d = 1 ∨ d = p ∨ d = p²` (via `Nat.Prime.dvd_of_dvd_pow` /
  `Nat.Prime.eq_one_or_self_of_dvd`), then `ZMod 4`/`omega` residues. `field_simp`/`ring` not
  needed. This is a realistic next verified milestone.

### C4 — Minimal-`a` six-class mechanism. **Status: CONJECTURE (partially A, partially B). [C]**

Let `p ≡ 1 (mod 4)` be prime, `x = (p+a)/4`, `M = p·x = p(p+a)/4`.

- **(a) [A, partially Lean]** `a = 3` works ⟺ `p ≡ 2 (mod 3)` **or** `(p+3)/4` has a prime factor
  `≡ 2 (mod 3)`. *(Sufficient direction Lean-verified via `a3_solution`; the `⟸` rest is the
  `M²` divisor `≡ 2 (mod 3)` ⟺ `M` has a `≡ 2 (mod 3)` prime-factor step.)*
- **(b) [C, with B support]** `a = 7` works whenever `p` is a non-residue mod 5 or mod 7.
- **(c) [C]** Consequently the minimal certificate `a` satisfies
  `a ≥ 11 ⟺ p ≡ 1, 121, 169, 289, 361, 529 (mod 840)`.

- **Proof attempt.** (a) is the divisor parametrisation at `a = 3` (done). (b) needs an explicit
  `a = 7` completion when `(p/5) = −1` or `(p/7) = −1` (the mod-840 sieve literature asserts this
  with residual `R = 3` or `R = 7`). (c) combines (a),(b) with `p ≡ 1 (mod 8)` (1.1).
- **Why it is a step forward.** It re-expresses the *entire* six-class wall in the minimal-`a`
  language, giving a single, testable, factorisation-light criterion whose components (a) are already
  partly machine-checked.
- **Honest limit.** This *is* Mordell's reduction in different dress: (c) does not cross the core,
  it re-locates it at `a ≥ 11`. The `a = 7` completion (b) is the one non-trivial new identity needed,
  and it is exactly the piece the literature states but does not spell out in the notes.
- **Lean-formalizability.** **Medium–high.** (a) needs the prime-factorisation lemma (deferred in the
  project, `proof_attempts.md` P4). (b) needs explicit `a = 7` identities + `ZMod`/Legendre-symbol
  residues (`NumberTheory/LegendreSymbol` **is** in Mathlib). No large sieve, no Brauer–Manin.

### (Rejected candidate, for completeness) C5 — a degree-≤2 "two-square" parametrisation

Since every hard prime is `p = u² + v²`, one might conjecture an identity
`4/(u²+v²) = 1/X(u,v) + 1/Y(u,v) + 1/Z(u,v)` with low-degree `X,Y,Z ∈ ℤ[u,v]`. **Assessment: D,
likely false.** Such an identity would solve the conjecture outright (every `p ≡ 1 (mod 4)`), and
none is known; the `a=3` analysis already shows the minimal `x` cannot be a fixed low-degree
function of `u,v` for all `p` **[D; honest]**.

---

## 3. Feasibility ranking

| Rank | Candidate | Feasibility | Value | Status |
|---|---|---|---|---|
| 1 | C1 divisor-split | **done** (`field_simp`+`ring`) | reorganises the obstacle to primes | **A, Lean-verified** |
| 2 | C2 Obláth identity | **done** (`field_simp`+`ring`) | explicit density-1 family | **A, Lean-verified** |
| 3 | C3 trivial-split impossibility | **high** (one divisor lemma + `omega`) | unconditional "why primes are hard" | **A (classical), not in Lean** |
| 4 | C4 minimal-`a` six-class | **medium** (`a=7` identity + Legendre symbol) | re-locates the wall at `a ≥ 11` | **C** (part A, part B) |

C3 is the single best *next* Lean target: it is a new, unconditional, elementary lemma that turns
the existing bounded-search heuristic ("no affine identity covers `n ≡ 1 (mod 8)`") into a theorem
about the greedy split, at the cost of one short prime-factorization lemma.

---

## 4. Register summary

| Item | Register |
|---|---|
| Four easy congruence identities + `n ≡ 1 (mod 12)` | **A** (Lean-verified) |
| Obláth identity `4/n = 1/((s+1)m) + …` (`n+1 = (4s+3)m`) | **A** (Lean-verified, `oblath_identity`) |
| Obláth covers density 1; stalls at `n+1 = 2^α ∏(≡1 mod 4 primes)`, first `p = 73` | **A** |
| Divisor-split `a·b = n², 4x = a+n, 2y = b+n ⟹ 4/n = 1/x+1/y+1/y` | **A** (Lean-verified, `divisor_split_eq`) |
| Corollary: `n²` has divisor `≡ 3 (mod 4)` ⟹ solvable; vacuous for primes `≡ 1 (mod 4)` | **A** |
| Trivial split impossible for primes `p ≡ 1 (mod 4)` | **A** (classical; formalization sketched) |
| Mordell six-class reduction `mod 840`; six classes = `≡1 (mod 24)` + QR mod 5,7 | **A** (published) |
| Six classes = `x²+840y²` primes | **A** (published / OEIS A139665) |
| Yamamoto / Bright–Loughran necessary conditions; no Brauer–Manin obstruction | **A** (published) |
| Vaughan / Elsholtz–Tao density + counting bounds | **A** (published) |
| `a=3` characterisation `p ≡ 2 (mod 3) ∨ (p+3)/4` has `≡2 (mod 3)` factor | **A** (⟸ Lean-verified) / **B** (⟹ computational) |
| `a=7` covers non-QR mod 5 or 7 | **C** (with **B** support) |
| Minimal `a ≥ 11` ⟺ six classes | **C** |
| Degree-≤2 two-square parametrisation | **D** (likely false) |
| The Erdős–Straus conjecture itself | **C** (open) |

---

## Sources

- Obláth's condition (`n+1` has a prime `≡ 3 (mod 4)`): [Erdős Problems #242 forum](https://www.erdosproblems.com/forum/thread/242)
- Mordell's six classes mod 840: [Erdős Problems #242](https://www.erdosproblems.com/forum/thread/242), OEIS [A139665](https://oeis.org/A139665)
- Salez, *new modular equations and checking to 10¹⁷*, [arXiv:1406.6307](https://arxiv.org/abs/1406.6307)
- Elsholtz–Tao, *Counting the number of solutions*, [arXiv:1107.1010](https://arxiv.org/abs/1107.1010)
- Bright–Loughran, *Brauer–Manin obstruction for Erdős–Straus surfaces*, [arXiv:1908.02526](https://arxiv.org/abs/1908.02526)

*Written in accordance with the standing rules: no claim that the open problem is solved; no fake
proofs; no `sorry`; the two Lean-verified lemmas compile under `lake build`.*
