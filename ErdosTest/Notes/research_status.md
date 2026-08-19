# Phase 6, Step 6 — Research Honesty Check

> **Legend:** **A** = proven (Lean-verified here, or published) · **B** = computational evidence ·
> **C** = conjecture · **D** = AI-generated hypothesis.

This file answers the honesty questions explicitly required by the project rules, and gives the
overall classification of the Phase-6 contribution.

---

## 1. Did we prove something new?

**No.** All four lemmas formalised in `Theorems/DivisorParam.lean` are **already known** mathematics
(possibly in a slightly different dress). We proved them *in Lean*, which is a **formalisation
contribution**, not a new theorem:

- **Lemma A** (`cleared_iff_normalized`): the symmetric/normalised equivalent form of the cleared
  equation is a classical, folklore identity.
- **Lemma B** (`solution_bound`): `n < 4x` for any solution is an elementary, standard observation.
- **Lemma C** (`divisor_construction`): the divisor-parametrisation sufficient direction is the
  standard tool of Elsholtz–Tao and Swett.
- **Lemma D** (`five_mod_eight`): the `n ≡ 5 (mod 8)` identity is a known special case of Mordell's
  mod-840 reduction — *rediscovered independently* by our Phase-4 symbolic search, but **not new**.

**Verdict: no new mathematics.** New *artefact*: a machine-checked statement of the divisor
parametrisation in Lean (which did not previously exist in Mathlib).

---

## 2. Did we rediscover something known?

**Yes, and this is expected and stated honestly.** Specifically:

- The normalised equivalent form (Lemma A) and the bound (Lemma B) are textbook.
- The divisor construction (Lemma C) is the backbone of the published counting results
  (Elsholtz–Tao 2011/13, Elsholtz–Planitzer 2018) and of the computational sieves (Swett, Salez).
- Lemma D is literally a piece of the classical six-class reduction mod 840 (Mordell), which our
  Phase-4 `identity_search.py` found from scratch.

We did **not** claim discovery: `research_directions.md` labels each lemma "already known" at
definition time, and this file reiterates it.

---

## 3. Is there a hidden assumption?

We checked each Lean lemma for exactly this. Findings:

- **Lemma A, B, D:** no hidden assumptions beyond positivity of the denominators (`x, y, z, n > 0`),
  which is explicit in the statements and discharged by `positivity` / `nlinarith` inside the proof.
- **Lemma C:** the only place where a hidden assumption *could* have crept in is the "division by
  `4x − n`" step. We **eliminated** the trap entirely by restating the lemma in **additive form**
  `a + n = 4x` with an explicit `0 < a` hypothesis (`ha`), so there is **no Nat-subtraction
  truncation** and **no division by a possibly-zero quantity**. The proof reduces to the identity
  `a·y·z = n·x·(y+z)`, which `nlinarith` proves from `a·y = d+nx`, `a·z = e+nx`, `d·e = (nx)²`
  *using* `a > 0` to divide. The positivity of `a` is a **stated** hypothesis, not hidden.

**Verdict:** no hidden assumption. (Note the deliberate design choice: the *published* form uses
`(4x−n) ∣ (d+nx)` with the subtraction; our formalised form trades that for `a+n = 4x` precisely so
that no truncation/divisibility subtlety is swept under the rug.)

---

## 4. Is there any unverified step?

- **Within the Lean file:** none. `lake build` completes cleanly, with no `sorry`, no `admit`, no
  `axiom`, and no unused-tactic warnings. Every lemma is fully closed by `nlinarith` / `ring` /
  `exact_mod_cast` / `rw` / `calc`.
- **Between the lemmas and the conjecture:** a **very large** gap remains. Lemma C is a
  *sufficient* direction of a parametrisation; it does **not** show that a valid `(d, e)` pair
  *exists* for every `n` (that existence is precisely the hard core of the conjecture). Lemma D
  covers one residue class. **None of A–D is claimed to imply the conjecture**; they are stepping
  stones, and they are labelled as such.

---

## 5. Overall classification of the Phase-6 contribution

| Item | Register |
|---|---|
| Lemmas A, B, C, D in `DivisorParam.lean` — proven in Lean, `lake build` clean | **A** (verified) |
| Their *mathematical content* — folklore / known | known, not new |
| Direction 1 (divisor-certificate reformulation) — as a *programme* | **D** (AI-generated strategy, untested beyond the four lemmas) |
| "Divisor construction ⟹ solution" (Lemma C) | **A** (verified) |
| "…⟸ converse holds for every `n`" | **C** (open — equivalent to the conjecture) |
| "Finite polynomial cover does not exist" | **C** (unproven belief) |
| "No affine `(x,y)` identity covers `n ≡ 1 (mod 8)`" | **D** (bounded-search observation) |
| The Erdős–Straus conjecture itself | **C** (open) |

**Overall grade for Phase 6: B** — solid **partial progress** with verified lemmas, but **no new
mathematical theorem** and **no step toward actually solving the conjecture**. The value is
architectural: the divisor parametrisation is now a *checked* piece of the project's library, and
the additive form `a+n = 4x` is a genuinely cleaner formal statement than the published
subtraction form.

---

## 6. What would it take to move from B to A?

A single lemma that is **currently missing** and would be the next real milestone:

> **Existence of a divisor certificate.** For every prime `p ≡ 1 (mod 4)`, there exist `x, d, e, a`
> with `a > 0`, `a + p = 4x`, `d·e = (px)²`, and `a ∣ d + px`, `a ∣ e + px`.

Proving this would (via Lemma C, already verified) settle the conjecture. It is **not** proven, it is
**not** implied by anything in this project, and — to be explicit — it is essentially the conjecture
in disguise. We do **not** claim it.

---

*Written in accordance with the standing rules: no claim that the open problem is solved; no fake
proofs; no `sorry`; known / computational / conjectural / verified registers kept separate.*
