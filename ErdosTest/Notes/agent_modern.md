# Transformations of Erdős–Straus into other mathematical languages

> **Legend (same as the rest of the project):**
> **A** = proven mathematics · **B** = computational evidence · **C** = conjecture / conjectural idea ·
> **D** = AI-generated hypothesis (not independently established).
>
> **Standing object.** For `n ≥ 2` let `f(n)` be the number of unordered positive solutions
> `(x,y,z)` to `4/n = 1/x + 1/y + 1/z`. Clearing denominators, this is
> `4xyz = n(xy + yz + zx)` **[A]**, and (Lemma A of `Theorems/DivisorParam.lean`) it is equivalent
> to the symmetric normalised form
> `(4x−n)(4y−n)(4z−n) = n²(4(x+y+z) − n)` **[A — verified in Lean]**.
>
> **Question asked of every transformation:** does it *add structure* (a reduction in the number
> of degrees of freedom, a new invariance, a new inequality, an actual `⟺` to a strictly simpler
> object), or does it *merely restate* (a rename of the same three integers)?

---

## 0. The one reduction that every other route passes through

Before the four "languages", record the single genuinely non-tautological equivalence, because
three of the four transformations below are only legible through it.

**Statement (divisor / "certificate" parametrisation).** Fix `n ≥ 2`. Then `4/n = 1/x + 1/y + 1/z`
has a positive solution **iff** there exist positive integers `x, d, e` with

```
n < 4x ,   d·e = n²x² ,   (4x−n) ∣ (d + nx) ,   (4x−n) ∣ (e + nx),
```

and then `y = (d+nx)/(4x−n)`, `z = (e+nx)/(4x−n)` **[A]**. (The `⟸` direction is Lemma C of
`Theorems/DivisorParam.lean`, already formalised; the `⟹` direction is the classical derivation
`a := 4x−n`, `a·y·z = n·x·(y+z)`, hence `(ay−nx)(az−nx) = n²x²`, so `d = ay−nx`, `e = az−nx`
are divisors of `n²x²` in the prescribed residue classes.)

**Why this is the load-bearing reformulation.** It replaces *three* free variables by *one* free
variable `x` plus *a divisor of `n²x²` lying in a single residue class mod `4x−n`*. This is a real
drop in degrees of freedom, and it is the language in which Elsholtz–Tao's counting, Swett's and
Salez's sieves, and the `p`-adic condition all become visible. **[A for the equivalence; A for
"every known method factors through it", as documented in `bottleneck_analysis.md` §3.]**

Everything below is judged against this benchmark: does the candidate transformation give more than
this does?

---

## 1. Arithmetic geometry: the Cayley cubic and its integral points

### 1.1 Precise form

Homogenise `4xyz = n(xy+yz+zx)` to the projective cubic surface

```
S_n :  4XYZ = nT(XY + YZ + ZX)   ⊂  P³.
```

**(a) `S_n` is `n`-independent up to `ℚ`-isomorphism:** the linear change `T ↦ (1/n)T` (equivalently
rescaling coordinates) identifies `S_n ≅ S_1` over `ℚ` for every `n ≠ 0` **[A — elementary]**.
So the *projective* geometry does not see `n`; all the `n`-dependence lives in the integrality
condition below.

**(b) `S_1` is the Cayley cubic.** Writing `S_1 : XYZ = T(XY+YZ+ZX)`, the four points
`(1:0:0:0)`, `(0:1:0:0)`, `(0:0:1:0)`, `(0:0:0:1)` are ordinary double points (check `∇F = 0` at
each), and these are the only singularities. A cubic surface with exactly 4 nodes is the **Cayley
cubic** (unique up to isomorphism). **[A — standard; the node check is a one-line Jacobian
computation.]**

**(c) Consequence: `S_n` is rational.** A cubic surface with a node is birational to `P²`
(projection from the node); the Cayley cubic is moreover **toric**. Hence rational points are
Zariski-dense and there is no shortage of them. **[A — standard.]**

**(d) The conjecture, translated.** `4/n` is representable **iff** `S_n` has an *integral* point
`(X:Y:Z:1)` with `X,Y,Z > 0` **and** `X,Y,Z` of the form `4·(positive integer)` — equivalently a
positive integral point of the affine chart `T=1`. In the `n`-independent model `S_1` this is: for
every `n` there is a `ℚ`-point `(X,Y,Z) = (4x/n, 4y/n, 4z/n)` with `x,y,z ∈ ℤ⁺` **[A — a
restatement]**. The surface `S_1` is nothing but `1/X + 1/Y + 1/Z = 1` after reciprocals.

### 1.2 Strongest adjacent theorem

**Bright–Loughran (2020).** (i) There is **no Brauer–Manin obstruction** to the existence of a
solution on `S_n` (more precisely `Br(S_n) = Br(ℚ)`, the transcendental Brauer group is trivial, so
the Brauer–Manin set equals the whole adelic set). (ii) There **is** a `p`-adic obstruction to
*strong approximation*: for odd `n`, a solution must satisfy the Hilbert-symbol product
`∏_{p∣n} (−u₁/u₃, −u₂/u₃)_p = −1`, which specialises to Yamamoto's quadratic-reciprocity
conditions and Elsholtz–Tao's odd-square condition. **[A — published; statement only, not
re-derived here.]**

### 1.3 Adds structure, or restates?

**Mostly restates, with two real bonuses.** The projective model adds a *canonical, `n`-independent*
birational object (the Cayley cubic), and it converts "why is the divisor formulation natural" into
a geometric fact: **`S_n` is a pencil of conics.** For fixed `x`, the fibre is
`(4x−n)·yz = nx(y+z)`, a conic (hyperbola) in `(y,z)`; integral points on each conic fibre are
parametrised by divisors of `n²x²`. So the geometry *explains* Section 0, but it does not add a new
counting variable or inequality — the geometry of a rational surface is *insensitive* to exactly the
integrality/positivity condition the conjecture asserts, and Bright–Loughran is the proof that the
standard geometric sufficiency route (Brauer–Manin) is **empty**. **[A for "pencil of conics";
A for "Bright–Loughran rules out Brauer–Manin".]**

There is one *genuinely geometric* extra structure worth naming, because it is where a new idea
could live: **descent.** Unlike the Markov surface `x²+y²+z² = 3xyz` (quadratic in each variable),
`S_1` is *linear* in each variable, so there is **no** quadratic Vieta involution — the only descent
available is the conic-fibre 2-descent, which is exactly the divisor parametrisation of Section 0.
A hypothetical *monotone* descent (a well-founded order on positive solutions along the fibres)
would prove the conjecture by infinite descent. **No such order is known to exist. [D — AI
hypothesis / gap, not a result.]**

### 1.4 What a proof would require; formalisability

A proof through this route would need either (a) a descent/height argument giving a monotone
well-ordering of positive solutions, or (b) a *sufficient* arithmetic-geometric certificate for
integral points on a rational singular cubic — both currently nonexistent and (b) is known to be
impossible at the level of Brauer groups **[A for the Brauer statement]**. In Lean: the **Brauer–Manin
obstruction is not in Mathlib** (only `Algebra/BrauerGroup` definitions exist); the Cayley
cubic/birational machinery is scheme theory far beyond current Mathlib. **Only the conic-fibre →
divisor reduction is formalisable, and it is already formalised (Lemma C).** Verdict: this route
sharpens and explains, it does not attack.

---

## 2. Divisor-sum / sieve formulation, and a probabilistic model of divisors

### 2.1 Precise form

By Section 0, `f(n)` is a **weighted divisor sum**:

```
f(n) = # { x ∈ ℤ⁺ : n < 4x, and ∃ d,e ∈ ℤ⁺ with de = n²x², d ≡ e ≡ −nx (mod 4x−n) }   [A].
```

Equivalently `f(n) = Σ_{x} #{ d | n²x² : d ≡ −nx (mod 4x−n), d ≤ n²x²/d }` (up to the symmetry
`d ↔ e`). This is a **divisor count with a modular (congruence) weight**, the form Elsholtz–Tao
count **[A — the identity is elementary; the cleanest version is their §4, not re-derived here]**.

**Implied local/necessary form.** For `n` prime `p`, all solutions force `x` into a short interval
and `d,e` to be divisors of `p²x²`, i.e. of the form `p^{ε}·(divisor of x²)`; this rigidity is why
`f(p)` is small. **[A — this is the mechanism behind Elsholtz–Tao's `p`-bound.]**

### 2.2 Strongest adjacent theorems

- **Elsholtz–Tao (2011/13):** `Σ_{p ≤ N} f(p) = N (log N)^{2+o(1)}`, and `f(p) ≤ p^{3/5+o(1)}`
  for every prime `p`. **[A]**
- **Elsholtz–Planitzer (2018):** `f(n) ≤ n^{3/5+o(1)}` for all `n`, and `f(n) ≥ (log n)^{log 6+o(1)}`
  for **almost all** `n`. **[A]**
- **Vaughan (1970):** the exceptional set `{n : f(n) = 0}` has `≤ N·exp(−c(log N)^{2/3})` elements
  up to `N`, hence density 0. **[A]**

### 2.3 Adds structure, or restates?

**This is the one transformation that adds substantial structure**, and it is *not* a restatement:
it reduces three variables to one free variable plus a divisor congruence (a genuine decrease in
degrees of freedom), and it exposes the **modular weight** (the residue class mod `4x−n`) that the
raw equation hides. All three theorems above, plus Swett's and Salez's sieves, are *only* provable
in this language. **[A — as a matter of mathematics, this equivalence is strictly more informative
than the original equation.]**

**The probabilistic model, stated honestly.** Model the residues `d mod (4x−n)` for divisors
`d | n²x²` as approximately independent uniform events. For `n` with rich divisor structure this
predicts `f(n) ≈ (log n)^{log 6+o(1)}` in agreement with Elsholtz–Planitzer **[A for the theorem,
D for the model as a *predictive* device]**. For prime `n` the model's variance blows up: the number
of candidate `(x,d)` is `≪ p^{3/5+o(1)}` and the model gives no pointwise lower bound. **The model
delivers the first moment (average abundance) but cannot certify `f(p) ≥ 1` for every `p`** — the
event `{f(p) = 0}` is rare in the model, and "rare at every `p` but possible at some" is exactly the
density-0-but-nonempty gap. **[C for the claim that the model is the honest obstruction; D for any
specific tail-bound conjecture.]**

### 2.4 What a proof would require; formalisability

A proof via this route requires a **pointwise lower bound `f(p) ≥ 1` for all primes `p`** — which is
the conjecture, so no progress is made *unless* the divisor structure can be forced by a new
theorem. Two specific (honestly labelled) gaps:

1. A *second-moment / variance* control at primes: if one could show, for each `p`, that the divisor
   count does not concentrate away from the congruence class, then `f(p) ≥ 1`. No such bound is known;
   the known bounds are first-moment. **[D]**
2. A *uniform certificate bound*: if every solvable `n` has a solution with `max(x,y,z) ≤ C·n^α`
   (explicit `C, α`), the problem becomes a finite per-`n` computation. **[C — stated in
   `bottleneck_analysis.md` §2(3), still open.]**

In Lean: the parametrisation identity **is already formalised (Lemma C)**; the full counting formula
`f(n)` as a finite sum over divisors is an elementary (but nontrivial) finite-sum lemma — **medium
difficulty, realistic**. The averages `Σ f(p) = N(log N)^{2+o(1)}` require the **large sieve, which is
not in Mathlib** (only `NumberTheory/SelbergSieve.lean` exists). Verdict: the structure is real and
formalisable at the level of the identity; the theorems that use it are beyond Mathlib's analytic layer.

---

## 3. Additive combinatorics / incidence / harmonic analysis

### 3.1 Precise form

Let `U = {1/m : m ∈ ℤ⁺}` be the set of unit fractions. The conjecture is:

```
for every n ≥ 2,   4/n ∈ U + U + U      (threefold Minkowski sumset).        [A — a restatement]
```

Scaling by `n` (so the dependence on `n` is removed from the *left* side):

```
for every n ≥ 2,   4 = n/x + n/y + n/z,  i.e.  4 ∈ D_n + D_n + D_n ,   D_n := { n/m : m ∈ ℤ⁺ }.
```

Incidence form: a solution is a **triangle** in the 3-uniform hypergraph on `ℤ⁺` whose hyperedges are
`{x,y,z}` with `4/n = 1/x+1/y+1/z`; the conjecture is that this hypergraph has a triangle in every
fibre over `n`. **[A — a restatement.]**

### 3.2 Strongest adjacent theorem

The only *substantive* adjacent result is the one reached by routing the sumset through the divisor
parametrisation: `f(n)` becomes a **shifted divisor convolution**
`Σ_x Σ_{d | n²x²} 1_{d ≡ −nx mod 4x−n}`, and the circle-method / large-sieve analysis of this
convolution **is Vaughan's theorem** (density 0 of exceptions). **[A.]** There is no *additive-
combinatorics* theorem (Freiman-type structure, sumset rigidity, `3SUM`-style incidence) that is
known to control `U+U+U`, because `U` is a *structured-but-thin* set: its 3-fold sumset is not a
rigid Freiman-structured object, and no known theorem forces a prescribed dense subset `{4/n}` to lie
in it.

### 3.3 Adds structure, or restates?

**Restates**, with one caveat. The sumset/hypergraph language is a faithful renaming and adds no new
invariance or inequality. Its value is only realised *after* passing to the divisor convolution, at
which point it becomes the analytic route of Section 2 (already fully exploited by Vaughan,
Elsholtz, Pomerance–Weingartner). The honest statement is: **the additive-combinatorics formulation
adds nothing that the divisor formulation does not already contain, and nothing that harmonic
analysis has not already extracted.** **[C for "no additive-combinatorics theorem can force
coverage" — an absence claim, hence conjectural; A for "Vaughan is the harmonic analysis of this
convolution".]**

### 3.4 What a proof would require; formalisability

A new additive-combinatorics or incidence input would have to show `{4/n}` lies in `U+U+U` *without*
using divisor structure — no such structural theorem for sums of reciprocals is known, and it is not
obviously easier than the original problem. **[C.]** In Lean: the sumset statement is a trivial
definition; the harmonic analysis (exponential sums over divisors, large sieve) is **not in Mathlib**.
Verdict: not a route; useful only as a vocabulary for the Section-2 convolution.

---

## 4. Class field / genus theory over `ℚ(√−210)` (folding in the `p`-adic local–global form)

### 4.1 Precise form

The six hard classes mod 840 are

```
{1, 121, 169, 289, 361, 529} = { r² mod 840 : gcd(r,840) = 1 }
 = { n ≡ 1 (mod 8), n ≡ 1 (mod 3), (n/5) = 1, (n/7) = 1 },          [A — CRT / Legendre symbols]
```

and these are exactly the primes represented by the form `x² + 840y²` **[A — given as fact (iii);
equivalent by classical genus theory / Cox's `x² + ny²` theory]**. Since Mordell's reduction settles
every `n` outside these six classes **[A]**, the conjecture is **equivalent** to:

```
(ES-cf)   every prime p represented by x² + 840y²   has   f(p) ≥ 1 .
```

The associated field: `ℚ(√−840) = ℚ(√−210)`, fundamental discriminant `−840`; the form `x²+840y²`
has discriminant `−3360 = 16·(−210)`, i.e. it lives in the order of conductor 2 of `ℚ(√−210)`. The
six classes form the **principal genus** of this form — the genus (class of `Cl/Cl²`) on which all
the quadratic-reciprocity / genus characters `(·/3),(·/5),(·/7)` and the `2`-adic character
`n ≡ 1 mod 8` simultaneously vanish. **[A for "the classes are a genus as described"; the precise
order/conductor bookkeeping should be checked against Cox before citation in print.]**

### 4.2 Strongest adjacent theorem

**Bright–Loughran (2020)** again, in its `p`-adic form: the Hilbert-symbol condition
`∏_{p∣n} (−u₁/u₃, −u₂/u₃)_p = −1` is a **necessary** condition on solutions for odd `n`, and it is
exactly a *genus character* — it recovers Yamamoto's quadratic-reciprocity conditions as the genus
characters `(·/5),(·/7)`. **[A.]** This is the correct *description* of *why* the six classes are the
hard ones: they are precisely the primes on which **all local genus-character obstructions vanish**,
so no local argument can exclude them — yet sufficiency is missing.

### 4.3 Adds structure, or restates?

**Adds bookkeeping structure, no sufficiency mechanism.** The class-field language accomplishes
three real things: (i) it gives a *canonical* description of the hard set as one genus (not an ad-hoc
list of six residues); (ii) it shows the known `p`-adic obstruction is a genus character, so
"no local obstruction" is *co-extensive with* "in the hard genus"; (iii) it localises the remaining
gap precisely: the difference between **genus** (the 2-part `Cl/Cl²`) and **class** (the full
`Cl(ℚ(√−210))`). The conjecture says: for primes in the principal genus, the corresponding
*class-group* subtlety always resolves in favour of a solution. That last step is **not** a theorem and
is equivalent to the conjecture. **[A for (i)–(iii) as reformulations; C for "the genus→class gap is
exactly the conjecture" — this is a precise statement of equivalence, flagged as a reformulation
rather than an independent result.]**

### 4.4 What a proof would require; formalisability

A proof here would need to use **actual ideal-class-group structure** (beyond genus theory), e.g. a
theorem that a specific family of ideals in the principal genus of `ℚ(√−210)` is always principal
after a canonical twist — thereby exhibiting a solution. No such theorem exists, and constructing one
is the same difficulty as the conjecture. **[C; the specific "twist" formulation is D — an AI
hypothesis, not literature.]**

In Lean: **quadratic reciprocity and Legendre symbols are in Mathlib**
(`NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`), and **`ClassGroup`/`classNumber` for
number fields are in Mathlib** (`NumberTheory/NumberField/ClassNumber.lean`). So the *Yamamoto-type
necessary conditions* are a realistic formalisation target (this matches `known_results.md` §7).
However, **genus theory, composition of binary quadratic forms (Cox's `x²+ny²`), and the Hilbert
symbol are not in Mathlib**, so the full class-field mechanism is not currently formalisable.
Verdict: excellent for *stating* the hard core correctly and for formalising the *necessary*
conditions; no route to sufficiency.

---

## 5. Synthesis

| Transformation | Adds structure? | Best available result | Route to sufficiency? | Formalisable in Mathlib? |
|---|---|---|---|---|
| 1. Cayley cubic / integral points | Partially (canonical model, pencil of conics, *negative* Brauer–Manin result) | Bright–Loughran: no Brauer–Manin obstruction **[A]** | No (descent gap, **[D]**) | No (Brauer–Manin not in Mathlib) |
| 2. Divisor-sum / sieve + probabilistic model | **Yes** (3 vars → 1 var + divisor congruence) | Elsholtz–Tao / Planitzer / Vaughan **[A]** | Only if pointwise `f(p) ≥ 1` is forced — that *is* the conjecture | Identity **already in Lean**; averages need large sieve (absent) |
| 3. Additive combinatorics / sumset | No (restatement) | Vaughan as divisor-convolution harmonic analysis **[A]** | No | No (large sieve absent) |
| 4. Class field / genus over `ℚ(√−210)` | Bookkeeping only (hard set = one genus; obstruction = genus character) | Bright–Loughran `p`-adic condition **[A]** | No (genus→class gap = conjecture) | Necessary conditions: yes (Legendre/QR, ClassGroup in Mathlib); genus theory: no |

**Bottom line.** Of the four languages, **only the divisor formulation (Section 2) increases
structure** in the strict sense: it is the unique place where the number of free variables drops and
where a *modular weight* appears, and it is the language of every deep known result. The geometric
(Section 1) and class-field (Section 4) languages each contribute one *definitive negative*
(no Brauer–Manin obstruction) and one *necessary* condition (the `p`-adic Hilbert-symbol/genus
character), i.e. they **sharpen the problem without adding a sufficiency mechanism**; they turn the
six-class core into a canonical object (a Cayley cubic / a genus) but do not produce solutions.
Additive combinatorics (Section 3) is a pure restatement.

**Consequence for the project.** The decision already recorded in `research_directions.md` (Step 3:
work on the divisor-certificate reformulation) is the correct one, and is *vindicated by this
comparison*: it is the single transformation that both (i) adds real structure and (ii) is
elementary enough to formalise (Lemma C is already in Lean). The geometric and class-field directions
remain valuable **only** as sources of *necessary conditions* (Yamamoto/Bright–Loughran) that can be
formalised at the Legendre-symbol/quadratic-reciprocity level, not as sufficiency routes.

**No claim here settles the conjecture.** Every statement above labelled **[C]** or **[D]** is an
open direction or an AI-generated hypothesis, and the conjecture itself remains open (verified only
to `~10^17`, **[B]**).

---

### References folded in (all already cited in `literature_review.md` / `known_results.md`)

- Elsholtz–Tao, *Counting the number of solutions…*, arXiv:1107.1010 — `f(p)` bounds, average.
- Elsholtz–Planitzer, arXiv:1805.02945 — pointwise upper bound, a.a. lower bound.
- Vaughan (1970) — density-0 exceptional set via the large sieve.
- Bright–Loughran, *Brauer–Manin obstruction for Erdős–Straus surfaces*, arXiv:1908.02526 — Cayley
  cubic geometry, empty Brauer–Manin obstruction, `p`-adic Hilbert-symbol condition.
- Cox, *Primes of the form x²+ny²* — genus theory for the form `x²+840y²`.
