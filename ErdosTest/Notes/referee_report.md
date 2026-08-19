# Hostile Referee Report — Erdős–Straus project

> Scope: attack every claim the project has made, and identify the most likely failure modes.
> Registers used throughout: **A** = proven · **B** = computational · **C** = conjecture · **D** = AI hypothesis.
> All file/line citations are against the current tree. I read every Notes file and every
> `Theorems/*.lean` file cited below, plus the three experiment scripts.

---

## TL;DR verdict

The project is, on its own admission, a **formalisation** exercise, not a mathematical
breakthrough. Its strongest *machine-checked* statements are all elementary and all either
(a) folklore, (b) a linear change of variables, or (c) a specialisation of a known
parametrisation. The single place where the notes go beyond "honest reformulation" — the `a = 3`
characterisation — is precisely the place where the **register labels are wrong**: the notes claim
a direction is "Lean-verified" (`[A]`) when no Lean proof exists for it, and the header label of
the same section contradicts its own body.

The conjecture is not solved; nothing here comes close; the project says so repeatedly and
correctly. The referee's job is therefore not to refute a false "solved" claim, but to (1) audit
the register discipline, and (2) explain *why the approaches cannot work*, so the project stops
investing in them.

---

## Claim 1 — The divisor-certificate bijection `solvable_iff_certificate`

Files: `Theorems/Certificate.lean` (defs lines 24–31, theorem lines 116–119);
`Theorems/DivisorParam.lean` (`divisor_construction` 53–82); notes `research_update.md` §1,
`research_status.md` §6.

**What is actually proved.** `Solvable n ↔ HasCertificate n` for `n ≥ 2`, where
`HasCertificate n := ∃ x a d e, x,a,d,e > 0 ∧ a+n = 4x ∧ a ∣ d+nx ∧ a ∣ e+nx ∧ d·e = (nx)²`.
The necessary direction (`solution_gives_certificate`, 34–85) sets
`a = 4x−n, d = a·y − n·x, e = a·z − n·x` and proves `d·e = (nx)²`; the sufficient direction
(`solvable_of_certificate`, 88–107) reconstructs `y = (d+nx)/a`, `z = (e+nx)/a`.

**(a) Trivially known / folklore?** Yes. This is the standard divisor parametrisation that
underlies Elsholtz–Tao, Elsholtz–Planitzer, Swett's sieve, and Salez's computation. The project
itself says so (`research_status.md` §2, `research_directions.md` §4). Not new.

**(b) Circular or vacuous?** *Neither*, technically. Neither direction appeals to the conjecture,
and both genuinely use the cleared equation (the key identity `a·y·z = n·x·(y+z)` is derived from
`4xyz = n(xy+yz+zx)`, `Certificate.lean` 52–58). So it is a real, non-vacuous bidirectional
theorem. **But it is a linear change of variables, nothing more.** `d` and `e` are linearly
determined by `y` and `z` (and vice-versa), and `a` is determined by `x`. `HasCertificate n` is
*exactly* as hard to decide as `Solvable n`. The project admits this outright:
"it is essentially the conjecture in disguise" (`research_status.md` 100–107).

**(c) Incorrectly/misleadingly stated?** One cosmetic looseness: `HasCertificate` records only
divisibility `a ∣ d+nx` (line 30), not the equality `a·y = d+nx` that the necessary direction
actually produces (lines 38–39). Harmless — divisibility suffices to reconstruct `y,z` — but it
means the "bijection" is a bijection between solutions and a *slightly weaker* predicate than the
one the notes describe. The framing "now fully bidirectional … not a one-sided reformulation"
(`research_update.md` §1) overstates the significance: upgrading from "one-sided" to
"bidirectional" costs one trivial `omega`/`nlinarith` step because the two directions are
inverse linear maps.

**(d) Hidden assumption.** `2 ≤ n` is explicit and used only to validate the cleared form
(`solution_bound` → `isDecomposition_iff_cleared`). No hidden assumption. The `a > 0` conclusion
follows from `n < 4x`. This part is clean.

**(e) Counterexample.** None — it is a verified theorem. The correct "counterexample" is not a
number but a *claim*: there is no `n` for which `HasCertificate n` is easier to verify than
`Solvable n`. The reformulation does not reduce the problem; it renames it.

**Register.** The theorem itself is **A** (verified). Its *significance* is **D/C** at best — it
is a restatement whose "hard part" (existence of a certificate) is the open problem
(`theorem_graph.md` §3 row 2).

---

## Claim 2 — The parity theorem (odd `n` ⇒ at most one odd denominator)

File: `Theorems/Certificate.lean` (`two_odd_implies_sum_odd` 122–126,
`odd_solution_two_divides_pairwise_sum` 130–145, `odd_solution_not_two_odd` 148–157).

**(a) Trivially known / folklore?** Yes. It is a two-line corollary of the cleared equation taken
mod 2: `4xyz ≡ 0`, and `n` odd gives `n(xy+yz+zx) ≡ xy+yz+zx`, so `xy+yz+zx` is even; if two of
`x,y,z` are odd then `xy+yz+zx` is odd. This is exactly what the Lean does (it proves
`2 ∣ xy+yz+zx` via `Nat.Coprime 2 n` then contradicts `Odd (xy+yz+zx)`). Elementary to the point
of being unremarkable; folklore-adjacent if not literally folklore.

**(b) Circular/vacuous?** No. It is a true, correctly proved lemma.

**(c) Incorrectly/misleadingly stated?** The *lemma* is correctly stated. The *interpretation* is
the problem. The file header (lines 15–16) and `research_update.md` §2.3 claim this "explains, at
the 2-adic level, why the `n ≡ 1 (mod 8)` core resists affine identities." **That is a
non-sequitur.** The parity constraint is symmetric in `x,y,z` and applies identically to
`n ≡ 5 (mod 8)`, where affine identities *do* exist (`five_mod_eight` in `DivisorParam.lean`,
`five_mod_eight_minimal` in `ACases.lean` — e.g. for `n = 8k+5`, `x = 3k+2` has the same
"≤ one odd" property). The parity theorem does **not** distinguish `n ≡ 1` from `n ≡ 5 (mod 8)`,
so it provides no mechanism for the affine-identity barrier. The "explains" claim is rhetorical
overreach, not mathematics.

**(d) Hidden assumption.** `2 ≤ n`, `Odd n`, positivity — all explicit. None hidden.

**(e) Counterexample.** To the *theorem*: none. To the *explanatory claim*: trivially — the
`n ≡ 5 (mod 8)` solutions satisfy the same parity constraint yet are covered by affine identities,
so parity does not explain the `n ≡ 1 (mod 8)` gap.

**Register.** The lemma is **A** (verified, trivial). The "explains the core" gloss is **D**
(unjustified AI-style narrative).

---

## Claim 3 — The `a = 3` "minimal certificate" characterisation `a3_iff_divisor`

Files: `Theorems/MinimalCertificate.lean` (`x_ge_minimal` 44–48, `a3_iff_divisor` 76–88,
`a3_solvable_gives_divisor` 63–73); `Theorems/ACases.lean` (`a3_solution` 52–73).

**(a) Trivially known?** Yes — it is `solvable_iff_certificate` specialised to `n = 4k+1`,
`x = k+1`. `a3_solvable_gives_divisor` calls `solution_gives_certificate` and then closes
`a = 3` by `omega` from `a + (4k+1) = 4(k+1)` (line 70). The project says this plainly
(`proof_attempts.md` §2 item 3: "Is it just a reformulation? Yes, essentially."). Not new.

**(b) Circular/vacuous?** No. It is a genuine specialisation; no appeal to the conjecture.

**(c) Incorrectly/misleadingly stated?** The phrase "`a = 3` is the minimal certificate" **is**
correctly stated for *all* solutions, not just a special form: `x_ge_minimal` proves that any
solution `(x,y,z)` of `4/(4k+1)` has `x ≥ k+1` (via `solution_bound`: `n < 4x`), so the first
denominator is minimised at `x₀ = (n+3)/4`, forcing `a = 3`, and since `a ≡ 3 (mod 4)` and
`a > 0`, `a = 3` is the minimum. This is sound and general. The one genuine precondition — `k ≥ 1`
(`n ≥ 5`, so `n = 1` is excluded) — is explicit and correctly flagged as intrinsic, not
accidental (`proof_attempts.md` P2).

**(d) Hidden assumption.** `k ≥ 1` (`n ≥ 5`). Explicit. None hidden.

**(e) Counterexample.** None (verified theorem). The relevant failure is conceptual: isolating
the *minimal* certificate does not move the conjecture, because "minimal `a = 3` works" is only
one slice of `Solvable`.

**Register.** **A** (verified), but with **zero** new mathematical content — it is a
specialisation of a restatement.

---

## Claim 4 — The computational `a = 3` characterisation
`a = 3` works ⟺ `p ≡ 2 (mod 3)` OR `(p+3)/4` has a prime factor `≡ 2 (mod 3)`.

Files: notes `research_update.md` §2.1 (42–57), `problem_variants.md` M1 (28–37),
`theorem_graph.md` T1 (95–103), `proof_attempts.md` §2 item 5; scripts
`certificate_conjectures.py` (line 51 `N = 5000`), `problem_variants.py` (line 46 `N = 30000`).

**The mathematical content is correct** (I checked it independently): for prime
`p ≡ 1 (mod 4)`, `M = p(p+3)/4`, one has `M ≡ 1 (mod 3)` always (since `p ≠ 3` and
`4⁻¹ ≡ 1 (mod 3)`), so `3 ∣ d+M ∧ 3 ∣ e+M` forces `d ≡ e ≡ 2 (mod 3)`, and this is satisfied
iff `M²` has a divisor `≡ 2 (mod 3)`, iff `M` has a prime factor `≡ 2 (mod 3)`, iff
`p ≡ 2 (mod 3)` or `(p+3)/4` has a `≡ 2 (mod 3)` factor. This is an elementary, folklore-adjacent
corollary — *and it is fully provable with only prime-factorisation machinery*. It is **not** a
deep result, and the project says so.

The attacks are about **status and labelling**, and here the project fails:

**(c) The ⟸ direction is NOT Lean-verified, despite the notes saying it is.** This is the
strongest concrete error in the project.

- `research_update.md` line 52: *"the `⟸` (sufficient) direction is Lean-verified
  (`a3_solution`, §3)"*.
- `problem_variants.md` line 33: *"the `⟸` (sufficient) direction is `[A]` verified (via
  `a3_iff_divisor` + the divisor `d = q` argument)"*.

What `a3_solution` (`ACases.lean` 52–73) actually proves is
`A3Certificate k ⇒ A3Solvable k`, i.e. **"there exist complementary divisors `d,e` with
`3 ∣ d+M, 3 ∣ e+M` ⇒ a solution exists"**. It does **not** prove the claimed sufficient direction
of the characterisation, which is **"`p ≡ 2 (mod 3)` or `(p+3)/4` has a `≡ 2 (mod 3)` factor ⇒
a solution exists"**. The missing bridge — "residue/prime-factor condition ⇒ a certificate
`(d,e)` exists" — is exactly the step that needs `Nat.factors`/prime-factorisation, and there is
**no Lean lemma anywhere in `Theorems/`** connecting `q.Prime ∧ q ≡ 2 (mod 3) ∧ q ∣ M` to
`A3Solvable` or `A3Certificate`. I grepped; the only `Nat.Prime` in `Theorems/` is inside
`reduction_to_primes` (`MainResult.lean`), which is unrelated. The "divisor `d = q` argument" is
a *hand-waved proof sketch*, not a Lean theorem. Claiming it as `[A] verified` is a register
violation.

**(c′) The section header contradicts its own body.** `research_update.md` line 42 labels the
whole observation `[B, with A-pending "⟸"]`, while the body (line 52) says `⟸` *is* verified and
`⟹` is pending. The two directions are scrambled. The honest status is: **`a = 3` solvable ⟺
certificate** is `[A]` (verified, `a3_iff_divisor`); **`a = 3` solvable ⟺ the residue/prime-factor
condition `C`** is `[B]` in *both* directions, because the `C`-bridge (divisor `≡2 mod 3` ⟺ prime
factor `≡2 mod 3`) is unformalised in both.

**(c″) The `⟹` direction is elementary and provable, so deferring it is a choice, not a wall.**
The step "`M²` has a divisor `≡2 (mod 3)` ⟺ `M` has a prime factor `≡2 (mod 3)`" is a standard
`Nat.primeFactorsList` argument (`theorem_graph.md` S1a sketches it correctly). It is fiddly, not
hard. Labeling it "A-pending" while simultaneously running a finite "0-mismatch" check
substitutes computation for a proof that is within reach. That inverts the project's own
"no computation where a proof is cheap" discipline.

**(a)/(b) and the "0 mismatches to 30000" evidence.** The criterion is folklore-adjacent and the
`⟺` is not circular (it is a real, provable equivalence). But the *evidence* is weaker than
advertised and slightly circular:

- The "direct search" in the *committed* script `certificate_conjectures.py` stops at
  `N = 5000` (line 51), **not** 30000. The "0 mismatches up to `p = 30000`, 1611 primes" figure
  cited in `proof_attempts.md` §2 and `problem_variants.md` M1 is produced by a *different*
  script, `problem_variants.py` (line 46), which is **not the script the notes cite** for the
  a=3 test (`research_update.md` line 51 cites `certificate_conjectures.py`). Reproducibility gap.
- More importantly, `problem_variants.py`'s `a_works(p,3)` is computed **via the certificate /
  divisor-of-`M²` method** (`a_works`, lines 16–34), not by an actual solution search. So its
  "0 mismatches" is really a comparison of *two derived forms of the same unproven equivalence*
  (divisor criterion vs. prime-factor criterion), not an independent test against solutions. It
  is a consistency check between two branches of a proof sketch, not independent evidence.
- The one genuinely independent check (brute-force `y`-search) is only in
  `certificate_conjectures.py`, and only to `N = 5000`.

**(e) Counterexample.** To the `⟺`: none known ≤ 30000 (B), but the `⟹` direction is unproven, so
a counterexample is not mathematically excluded. A counterexample would be a prime
`p ≡ 1 (mod 4)` with `p ≡ 1 (mod 3)` and `(p+3)/4` having *no* `≡ 2 (mod 3)` factor, yet `a = 3`
still working (or the reverse). Note this would also refute the "all `a=3` failures are
`p ≡ 1 (mod 8)`" refinement, which is itself *provable* (if `p ≡ 5 (mod 8)` then `(p+3)/4` is
even, giving the factor `2 ≡ 2 (mod 3)`, which is just `five_mod_eight_minimal` in another dress)
— yet the notes present it only as a computational observation.

**Register.** `a3_iff_divisor`: **A**. The `⟺ C` characterisation: **B** in both directions
(and *mislabeled* as partly **A** in two notes files). The criterion itself: **A**-provable
elementary, currently **B**.

---

## Claim 5 — "minimal `a` grows"

Files: `research_update.md` §2.4 (76–89), `problem_variants.md` S2 (45–53),
`theorem_graph.md` §3 (85–87), `proof_attempts.md` §2 item 5.

**(a)/(b)/(c) Classification.**

- "minimal `a ≤ 31`" (max over `p ≤ 30000`, attained at `p = 21169`) is a **finite-search
  artifact** — **B**, not a theorem. The notes label it correctly.
- "minimal `a` is unbounded" is a **conjecture** — **D/C**, not a fact. The notes label it
  correctly (`theorem_graph.md` S5a, `research_update.md` §2.4 caveat, `problem_variants.md` S2).
- The project *correctly* refuted its own earlier over-claims ("minimal `a ≤ 23`", "minimal
  `a ∈ {3,7}`") by extending the search — this is the referee loop working as intended.

**(d) Hidden assumption in the computation.** `problem_variants.py` S2 searches only
`a ∈ {3,7,…,399}` (`range(3, 400, 4)`, line 76). A prime with minimal `a ≥ 400` in range would be
silently reported as "NO solution" (`no_solution`), misclassifying it. This bounded-search caveat
is not surfaced in the notes. Practically harmless at `p ≤ 30000`, but it is a real bound the
notes omit.

**(e) Counterexample.** To "bounded minimal `a`": already found — `a = 31` at `p = 21169`
refutes `≤ 23`. This is exactly the kind of "slow growth, then jump" behaviour that should make
anyone skeptical of *any* finite bound: the sequence of new records `3, 7, 11, 15, 19, 23, 31`
over `p ≤ 30000` gives no evidence whatsoever for boundedness, and the unboundedness claim is
pure conjecture.

**Minor documentation drift.** `research_update.md` §2.4 (the `p ≤ 5000` table) lists
`a ∈ {3,7,11,15,23}` and omits `19` and `31`, which `problem_variants.md` S2 (the `p ≤ 30000`
run) reports with counts `19 → 5`, `31 → 1`. Not an error, but the two files describe different
searches without saying so, which is how "minimal `a ≤ 23`" got asserted in the first place.

**Register.** "≤ 31 for `p ≤ 30000`": **B**. "unbounded": **D** (conjecture).

---

## Other claims found on close reading

1. **`Szekeres.lean` is a foreign object.** `ErdosTest/Szekeres.lean` proves the *Erdős–Szekeres
   monotone-subsequence theorem* (1935), which is **completely unrelated** to the Erdős–Straus
   unit-fraction conjecture. It is listed in the verified-theorem inventory
   (`theorem_graph.md` line 47, "unrelated") and, presumably, in the job counts
   (`progress_score.md` "17424 jobs"; `ResearchReport.md` says "17 416 jobs" — also
   inconsistent). This is a namesake collision (Erdős–Szekeres vs. Erdős–Straus) that pads the
   "verified theorems" tally with material that has nothing to do with the stated problem. It
   should be quarantined or removed from the Erdős–Straus accounting.

2. **The "affine barrier at `n ≡ 1 (mod 8)`" is `[D]` and stays `[D]`.** Correctly labelled as a
   bounded-search observation (`identity_search.py`, coefficient bound 60). The claim that this
   barrier "has a real 2-adic explanation" (`open_questions.md` §3 item 2) is *not* supplied by
   the parity theorem (§Claim 2 above), and no valuation argument is given. It remains a
   numerical observation dressed in 2-adic language.

3. **`known_results.md` Mordell reduction details.** The statement "six classes
   `{1,121,169,289,361,529} (mod 840)` = `1²,11²,13²,17²,19²,23²` = primes `≡1 (mod 24)` that are
   quadratic residues mod 5 and 7" checks out (QR mod 5 = {1,4}, QR mod 7 = {1,2,4}; all six are
   `≡1 (mod 24)`). This is correctly reported `[A]`-published.

4. **`reduction_to_primes` and the elementary identities** (`MainResult.lean`, `Lemma1/2.lean`)
   are correctly proved and correctly labelled `[A]`. The `p ≡ 3 (mod 4)` identity
   `1/(k+1) + 1/(2(k+1)(4k+3)) + 1/(2(k+1)(4k+3))` verifies. No issue found.

---

## Most likely ways each proposed approach fails

**(i) Modular identity expansion.** Each polynomial identity `4/(mk+r) = 1/x(k)+1/y(k)+1/z(k)`
removes finitely many residue classes and always leaves some. The classical bottom is Mordell's
six classes `mod 840`; going to higher precision (Salez) merely trades six classes for ~2×10⁶
classes mod a huge modulus — the exceptional set shrinks but never vanishes. There is no known
finite fixed-degree polynomial cover, and it is widely believed none exists
(`bottleneck_analysis.md` §1, `open_questions.md` Q2). **Failure mode:** this route is
*exhausted* — it reproduces a 1969 result as a ~200-identity Lean lemma-pile with zero novelty,
and cannot cross the six-class core because the remaining obstruction is *divisor structure*, not
polynomial structure. The project's own search (coefficient bound 60) found nothing covering
`n ≡ 1 (mod 8)`, and no amount of higher-degree search will change that.

**(ii) Divisor-certificate / minimal-`a`.** The bijection is a restatement: `HasCertificate n` is
exactly as hard as `Solvable n`. The minimal-`a` lens only collapses the *easy* strata — `a = 3`
works for `n ≡ 5 (mod 8)` and `p ≡ 2 (mod 3)`, which are already covered by classical identities.
The genuinely hard core (`n ≡ 1 (mod 8)`, the six classes) leaks into `a = 7, 11, 15, 19, 23, 31,
…` with **no uniform characterisation** (the notes themselves observe `a = 7` has no single
residue because `−M (mod 7)` ranges over all six nonzero residues — `research_update.md` §4 item
4). Since minimal `a` is conjecturally **unbounded** (§Claim 5), no finite stratification over
`a` can finish the problem. **Failure mode:** every reduction terminates in "prove that `n²` has
a divisor in a specified residue class", which is the open problem wearing a costume. The
approach *explains* the problem cleanly but cannot *decide* it.

**(iii) Geometric / Brauer–Manin.** Bright–Loughran already establish there is **no** Brauer–Manin
obstruction. That result is a *negative* certificate: it removes a possible route to a
counterexample but provides no route to a proof. The remaining `p`-adic Hilbert-symbol condition
is necessary, not sufficient, and its converse ("no `p`-adic obstruction ⇒ solution") is literally
the conjecture (`bottleneck_analysis.md` §2 item 2, `research_status.md` §2 item 2). Brauer–Manin
machinery is also absent from Mathlib (`known_results.md` §7). **Failure mode:** the approach can
only *explain why the six classes are special* (they satisfy the quadratic-reciprocity conditions)
without ever *constructing* a solution; a sufficiency direction is the whole problem and is
nowhere in sight.

**(iv) Analytic / large-sieve.** Vaughan-type bounds give `#exceptions ≤ N exp(−c (log N)^{2/3})`,
i.e. density 0. This is fully compatible with an infinite sparse exceptional set — which is
exactly what the conjecture denies. No lower bound on the gap between hypothetical exceptions is
known, so no "gap + density" argument closes the loop (`research_directions.md` Direction 5,
`bottleneck_analysis.md` §2 item 5). The large sieve is not in Mathlib
(`known_results.md` §5). **Failure mode:** "almost all" is not "all"; the analytic machinery is
provably unable to exclude a lacunary infinite exceptional set, and that is the entire problem.
70 years of failure here is not an accident.

**(v) Probabilistic divisor model.** This is essentially *undeveloped* in the project — it
appears only as a passing phrase ("a combinatorial/probabilistic certificate",
`research_directions.md` line 20). If pursued, its failure modes are textbook: (a) a random-divisor
heuristic predicts each `n` is solvable with positive probability, yielding only "almost surely
solvable" (density 1), which is already known and is not the conjecture; (b) the divisors of
`n²` are **correlated** (multiplicative structure), so i.i.d. independence assumptions are
invalid precisely at the hard primes — the six classes are hard *because* of this correlation;
(c) any "solvable with high probability" statement has no mechanism to rule out a measure-zero
lacunary set of counterexamples, the same gap as (iv). **Failure mode:** a probabilistic argument
can never deliver the `∀` that the conjecture requires; it is the analytic obstruction in
disguise.

---

## Register summary (as the referee reads the current tree)

| Claim | Project label | Referee's label | Notes |
|---|---|---|---|
| Reduction to primes / elementary identities | A | **A** (verified, folklore) | correct |
| `solvable_iff_certificate` | A | **A** (verified), restatement | correct proof; zero reduction of difficulty |
| Parity theorem | A | **A** (verified, trivial) | the "explains the core" gloss is **D** |
| `a3_iff_divisor` (solvable ⟺ certificate) | A | **A** (verified), specialisation | correct; not new |
| `a=3` ⟺ prime-factor condition `C` | "[B, with A-pending ⟸]" / "⟸ [A] verified" | **B** both directions | **label wrong**: no Lean proof of the `C`-bridge exists; header contradicts body |
| "0 mismatches to 30000" | B | **B** (weaker than stated) | 30000 run not in cited script; "direct" check is itself the certificate method |
| minimal `a ≤ 31` (p ≤ 30000) | B | **B** (artifact) | correct |
| minimal `a` unbounded | D | **D** (conjecture) | correct |
| "no affine identity covers `n ≡ 1 (mod 8)`" | D | **D** (bounded search) | correct |
| `Szekeres.lean` content | (inventory) | **unrelated** | Erdős–Szekeres ≠ Erdős–Straus; remove from ES accounting |

**Bottom line.** No false "solved" claim is made anywhere, and the project's self-correction
(refuting "≤ 23", "∈{3,7}") is genuine. The one place where the register discipline breaks is the
`a = 3` characterisation: a hand-waved prime-factorisation step is reported as `[A]`-verified in
two notes files, and a section header says the opposite of its body. The deeper problem is
strategic, not tactical: every direction the project has selected is a restatement, a
specialisation, or an already-closed analytic/geometric avenue, and none of them can cross the
six-class core. The value delivered so far is architectural (a clean, `sorry`-free Lean
formalisation of the elementary layer), not mathematical.
