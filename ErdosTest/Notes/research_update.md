# Research Refinement — Update

> **Legend:** **A** = proven (Lean-verified here, or published) · **B** = computational evidence ·
> **C** = conjecture · **D** = AI-generated hypothesis.
>
> This phase refines the Direction-1 programme selected in Phase 6. The concrete new deliverables
> are (i) the **bidirectional** divisor-certificate bijection (`solvable_iff_certificate`),
> (ii) a clean **parity theorem**, and (iii) an explicit analysis of the **minimal certificate
> `a = 3`** case, including a new computable characterization. Nothing here solves the conjecture.

---

## 1. Current strongest idea

**The divisor-certificate reformulation, now fully bidirectional, with a "minimal certificate" lens.**

Phase 6 established the *sufficient* direction (`divisor_construction`). This phase proved the
*necessary* direction and combined them:

> `Solvable n ⟺ HasCertificate n`  (for `n ≥ 2`),  — `solvable_iff_certificate`.

So `4/n = 1/x+1/y+1/z` is *equivalent* to the existence of `x, a, d, e > 0` with
`a + n = 4x`, `a ∣ d + nx`, `a ∣ e + nx`, `d·e = (nx)²`. This is now a **checked bijection**,
not a one-sided reformulation.

The **refinement** of this phase is to stratify certificates by their parameter `a = 4x − n` and
study the *minimal* one. For `n ≡ 1 (mod 4)` the smallest feasible `x` is `x₀ = (n+3)/4`, forcing
`a = 3` (since `a = 4x − n ≡ −n ≡ 3 (mod 4)` and `a > 0`, the smallest is `3`). The `a = 3` case
is special because it reduces the 3-variable equation to a **2-variable** one:

> `4/(4k+1) = 1/(k+1) + 3/((4k+1)(k+1))`,  i.e. `1/y + 1/z = 3/(nx)`.

**Why this is the strongest direction.** (a) It is the only reformulation under which the mod-840
core is an *explicit* divisor statement; (b) it underlies every known deep result; (c) the minimal
`a` gives a *finite* (small) search parameter per `n`; and (d) it is elementary enough to
formalise in Lean — as this phase demonstrated.

---

## 2. New mathematical observations

### 2.1 The `a = 3` characterization — the main new observation  [A, fully Lean-verified]

For prime `p ≡ 1 (mod 4)`, set `x = (p+3)/4` (so `a = 3`) and `M = p·x = p(p+3)/4`. The remainder
`1/y + 1/z = 3/M` has positive-integer solutions **iff** `M²` has a divisor `d ≡ 2 (mod 3)`.
Since `M ≡ p² ≡ 1 (mod 3)`, this holds iff `M` has a prime factor `≡ 2 (mod 3)`. As `M = p·(p+3)/4`:

> **`a = 3` works  ⟺  `p ≡ 2 (mod 3)`  OR  `(p+3)/4` has a prime factor `≡ 2 (mod 3)`.**

- **Computational status:** verified **0 mismatches** against direct search for all primes
  `p ≡ 1 (mod 4)`, `p ≤ 5000` (`certificate_conjectures.py`). [B]
- **Formal status:** the **complete equivalence is now Lean-verified** (`Theorems/A3Characterization.lean`,
  `a3_solvable_iff_two_mod_three_or_factor`), with no `sorry`. The chain is
  `A3Solvable k ↔ A3Certificate k` (`a3_iff_divisor`) → `A3Certificate k ↔ ∃ d, d ∣ M² ∧ d % 3 = 2`
  (uses `M ≡ 1 (mod 3)` for prime `p = 4k+1`, `M_mod_three_eq_one`) → `∃ d, d ∣ M² ∧ d % 3 = 2 ↔
  ∃ q, q.Prime ∧ q ∣ M ∧ q % 3 = 2` (`divisor_two_mod_three_iff`). This closes the referee's Claim-4
  register violation (the unformalised `C`-bridge) by *proof*, not relabelling. [A]
- **Novelty:** this is a clean *corollary* of the classical divisor parametrisation (Elsholtz–Tao/Swett),
  not a deep new theorem; it does not appear to be stated in this exact form in the literature we read,
  but it is folklore-adjacent. We claim it as a **new observation**, not a breakthrough.

### 2.2 `n ≡ 5 (mod 8)` always has the minimal `a = 3` solution  [A]

`4/(8k+5) = 1/(2k+2) + 1/((8k+5)(k+1)) + 1/(2(8k+5)(k+1))`.

This is the *even-split* of `3/M` (`M = (8k+5)(k+1)` is even): `3/M = 1/(M/2) + 1/M`. It is a
**strictly smaller** `x` than Phase-6's `five_mod_eight` (`x = 3k+2` vs `x = 2k+2`) for the same class.
Proved in Lean (`five_mod_eight_minimal`). [A]

### 2.3 The parity obstruction is a theorem  [A]

For odd `n`, any solution has at most **one** odd denominator among `x, y, z`. Reason: the cleared
equation `4xyz = n(xy + yz + zx)` forces `2 ∣ xy + yz + zx` (since `4xyz` is even and `gcd(2,n)=1`),
but two odd denominators make `xy + yz + zx` odd. This explains, at the `2`-adic level, why the
`n ≡ 1 (mod 8)` core resists affine identities. Proved in Lean (§3).

### 2.4 The minimal certificate `a` is small — but *not* always 3  [B]

Distribution of minimal `a = 4·x_min − p` over all primes `p ≡ 1 (mod 4)`, `p ≤ 5000`:

| `a` | 3 | 7 | 11 | 15 | 23 |
|---|---|---:|---:|---:|---:|
| count | 283 | 37 | 6 | 1 | 2 |

- `a = 3` works for 283/329 ≈ 86% of such primes.
- The primes where `a = 3` **and** `a = 7` both fail (minimal `a ≥ 11`) are:
  `1129, 1201, 2521, 2689, 3049, 3889, 4201, 4561, 4729`.
- **Honest caveat:** "minimal `a ≤ 23` for all `p ≤ 5000`" is *finite evidence only*. The statement
  "minimal `a` is bounded by an absolute constant" would be **far stronger** than the conjecture
  itself (a uniform small-solution bound), is **not** supported for large primes, and is likely false.
  We record the small-`a` pattern as a *lens*, not a theorem. [B / a bounded-minimal-`a` claim would be D]

---

## 3. Lean verified results  (all built cleanly, `lake build`, no `sorry`)

New in this phase:

| Lemma / theorem | File | Statement (sketch) | Register |
|---|---|---|---|
| `solution_gives_certificate` | `Theorems/Certificate.lean` | solution ⟹ divisor certificate (necessary direction) | **A** |
| `solvable_of_certificate` | `Theorems/Certificate.lean` | certificate ⟹ solution | **A** |
| `solvable_iff_certificate` | `Theorems/Certificate.lean` | `Solvable n ↔ HasCertificate n` | **A** |
| `two_odd_implies_sum_odd` | `Theorems/Certificate.lean` | `x, y` odd ⟹ `xy+yz+zx` odd | **A** |
| `odd_solution_two_divides_pairwise_sum` | `Theorems/Certificate.lean` | `n` odd ⟹ `2 ∣ xy+yz+zx` | **A** |
| `odd_solution_not_two_odd` | `Theorems/Certificate.lean` | `n` odd ⟹ not (`x` odd ∧ `y` odd) | **A** |
| `four_minus_recip_reduction` | `Theorems/ACases.lean` | `4/(4k+1) = 1/(k+1) + 3/((4k+1)(k+1))` | **A** |
| `five_mod_eight_minimal` | `Theorems/ACases.lean` | `a = 3` identity for `n ≡ 5 (mod 8)` | **A** |
| `a3_solution` | `Theorems/ACases.lean` | sufficient condition: complementary `d, e` with `3 ∣ d+nx`, `3 ∣ e+nx` ⟹ solution | **A** |
| `divisor_two_mod_three_iff` | `Theorems/PrimeModThree.lean` | `(∃ d, d ∣ M² ∧ d % 3 = 2) ↔ (∃ q, q.Prime ∧ q ∣ M ∧ q % 3 = 2)` | **A** |
| `a3_certificate_iff_divisor_two_mod_three` | `Theorems/A3Characterization.lean` | `A3Certificate k ↔ ∃ d, d ∣ M² ∧ d % 3 = 2` (prime `p = 4k+1`) | **A** |
| `a3_solvable_iff_prime_factor` | `Theorems/A3Characterization.lean` | `A3Solvable k ↔ ∃ q, q.Prime ∧ q ∣ M ∧ q % 3 = 2` | **A** |
| `a3_solvable_iff_two_mod_three_or_factor` | `Theorems/A3Characterization.lean` | `a = 3` works ⟺ `p ≡ 2 (mod 3)` ∨ `(p+3)/4` has a prime factor `≡ 2 (mod 3)` | **A** |

`a3_solution` is the formalised **sufficient direction** of observation 2.1. Together these give:
the certificate bijection is a checked theorem, the parity obstruction is a checked theorem, and the
`a = 3` reduction + sufficiency are checked theorems.

---

## 4. Failed approaches / honest obstacles

1. **`nlinarith` cannot factor nonlinear products.** Deriving `a·y·z = n·x·(y+z)` (the key identity
   behind the certificate) from `4x = a+n` and the cleared equation **fails** in `nlinarith`; it was
   done with an explicit `calc` + `ring` + `rw`. Similarly, proving `nx < ay` needed explicit
   product-positivity hypotheses (`n·x·y > 0`) and a two-step linear `nlinarith`; a single `nlinarith`
   over all four positivity hypotheses diverged. [tooling limitation, not a mathematical wall]
2. **`not_even_iff_odd` is not root-accessible** in this Mathlib build; the parity contradiction was
   instead closed with `rcases` + `omega`. [missing/wrong-name infrastructure, worked around]
3. **The "`a ∈ {3,7}`" conjecture (from `n ≤ 300`) was refuted** by extending to `5000`: minimal `a`
   is also `11, 15, 23`. This is exactly the kind of finite-range over-generalisation the referee step
   is meant to catch. [referee success]
4. **`a = 7` has no equally clean characterization.** The analogous criterion is "`M²` has a divisor
   `≡ −M (mod 7)`", but `−M (mod 7)` ranges over all six nonzero residues, so there is no single
   residue (unlike `a = 3`, where `−M ≡ 2` always). This is *why* `a = 3` is special, and it means the
   `a = 3` trick does not generalise uniformly. [obstruction, understood]
5. ~~The full `a = 3` iff is not yet formalised~~ **Resolved in Phase 8b.** The necessary direction
   and the "divisor `≡ 2 mod 3` of `M²` ⟺ prime factor `≡ 2 mod 3` of `M`" step are now proven
   (`Theorems/PrimeModThree.lean` + `Theorems/A3Characterization.lean`). The referee was right that
   this was "a choice, not a wall": it needed one strong-induction lemma (`prime_factor_two_mod_three`)
   and a `M ≡ 1 (mod 3)` congruence (`M_mod_three_eq_one`), both now machine-checked. [A]

---

## 5. Next experiments

1. **Characterise `a = 7` combinatorially.** Instead of a single residue, enumerate which residue
   classes of `−M (mod 7)` are "easy" (realisable as a divisor of `M²`) and count their density;
   compare against the observed 79% success rate. [leads to a quantitative, not binary, criterion]
2. **Test whether minimal `a` stays small.** Extend `certificate_conjectures.py` to `p ≤ 10⁵` (or
   `10⁶`, via a sieve) and record the largest minimal `a`. Distinguish "bounded" from "slowly
   growing". Expect it to grow — this bounds how far the `a = 3` lens reaches. [B]
3. ~~Formalise the full `a = 3` iff.~~ **Done** — `a3_solvable_iff_two_mod_three_or_factor`
   (`Theorems/A3Characterization.lean`). Uses a `Nat`-level strong-induction prime-factor lemma
   (`prime_factor_two_mod_three`) rather than `ZMod`; the `M ≡ 1 (mod 3)` congruence for prime
   `p = 4k+1` is `M_mod_three_eq_one`. [A]
4. **Push the parity theorem to higher `p`-adic depth.** The current theorem is the `2`-adic first
   layer. Ask whether a `3`-adic or `p`-adic analogue constrains the *minimal certificate* further,
   and whether that gives a genuinely new obstruction at the six-class core. [C/D]

---

## 6. Honest assessment

**Overall grade: B (partial progress).**

- **Verified and real:** the solution ⟺ certificate **bijection** (both directions), the parity
  theorem, and the `a = 3` reduction **plus its complete characterisation** are now machine-checked;
  `lake build` is clean with no `sorry`. This turns Direction 1 from a *programme* into a *checked
  reformulation*, and resolves the referee's one register violation (Claim 4) by completing the proof.
- **New but modest:** the `a = 3` characterization (2.1) is a clean, computable, now **fully**
  formally-proven corollary of known divisor theory. It is a **new observation**, not a new deep
  theorem, and it does **not** come close to settling the conjecture.
- **No step toward the core.** The bijection is *equivalent* to the conjecture (the existence of a
  certificate is the hard part — `research_status.md` §6 already flags this). The `a = 3` lens covers
  the *easy* sub-case (`n ≡ 5 mod 8`) and a large fraction of primes, but the genuinely hard core
  (`n ≡ 1 (mod 8)`, six classes mod 840) is untouched.
- **The open problem remains open.** Nothing in this phase is claimed to imply the Erdős–Straus
  conjecture, and no such claim is made.

*Written in accordance with the standing rules: no claim that the open problem is solved; no fake
proofs; no `sorry`; known / computational / conjectural / verified registers kept separate.*
