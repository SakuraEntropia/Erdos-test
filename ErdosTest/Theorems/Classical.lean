import ErdosTest.Theorems.ErdosProblem

/-!
# Classical divisor-split and Obláth identities

Two classical elementary identities behind the "divisibility argument on `4x − n`" and
Obláth's density-one result. Neither settles the conjecture; both are recorded here as
*verified* pieces of the elementary layer, in the spirit of the missing-classical-arguments
note `Notes/agent_classical.md`.

1. `divisor_split_eq` (Lemma C1 of the note): if `a·b = n²`, `4x = a + n`, `2y = b + n`, then
   `(x, y, y)` is a solution of `4/n = 1/x + 1/y + 1/z`. This is the **trivial split**
   `d = e = n·x` of the divisor parametrisation, valid exactly when `a = 4x − n` divides `n·x`
   (equivalently `a ∣ n²`). The congruence conditions `n ≡ 1 (mod 4)`, `a ≡ 3 (mod 4)` are
   *not* needed for the equation — they are only what makes `x = (a+n)/4` and `y = (b+n)/2`
   integers (see the corollary in the note).

2. `oblath_identity` (Lemma C2 of the note): if `n + 1 = (4s+3)·m` (so `n+1` is divisible by the
   odd number `q = 4s+3`), then
   `4/n = 1/((s+1)m) + 1/((s+1)n) + 1/((s+1)mn)`. This is Obláth's explicit parametrisation;
   when `q` is a prime `≡ 3 (mod 4)` it shows every `n` with such a prime dividing `n+1` is
   solvable, which is a set of natural density 1.

All proofs use only `field_simp` / `push_cast` / `ring` / `nlinarith` / `omega`; no `sorry`.
-/

namespace ErdosStraus

/-- **Lemma C1** (the divisor split, pure identity). If `a·b = n²`, `4x = a+n`, `2y = b+n`,
with `n, x, y > 0`, then `4/n = 1/x + 1/y + 1/y`. The mod-4 congruence hypotheses are
deliberately absent: they are only needed to *realise* such `x, y` as naturals. -/
lemma divisor_split_eq {n a b x y : ℕ} (hab : a * b = n * n)
    (hn : 0 < n) (hx0 : 0 < x) (hy0 : 0 < y)
    (hx : 4 * x = a + n) (hy : 2 * y = b + n) :
    IsDecomposition n x y y := by
  unfold IsDecomposition
  have hnq : (n : ℚ) ≠ 0 := by positivity
  have hxq0 : (x : ℚ) ≠ 0 := by positivity
  have hyq0 : (y : ℚ) ≠ 0 := by positivity
  have han : ((a : ℚ) + (n : ℚ)) ≠ 0 := by
    have h : 0 < a + n := by
      rw [← hx]
      exact Nat.mul_pos (by norm_num : 0 < 4) hx0
    exact_mod_cast (show a + n ≠ 0 by omega)
  have hbn : ((b : ℚ) + (n : ℚ)) ≠ 0 := by
    have h : 0 < b + n := by
      rw [← hy]
      exact Nat.mul_pos (by norm_num : 0 < 2) hy0
    exact_mod_cast (show b + n ≠ 0 by omega)
  have hxq : (x : ℚ) = ((a : ℚ) + (n : ℚ)) / 4 := by
    have h : (4 : ℚ) * (x : ℚ) = ((a : ℚ) + (n : ℚ)) := by exact_mod_cast hx
    nlinarith
  have hyq : (y : ℚ) = ((b : ℚ) + (n : ℚ)) / 2 := by
    have h : (2 : ℚ) * (y : ℚ) = ((b : ℚ) + (n : ℚ)) := by exact_mod_cast hy
    nlinarith
  have habq : (a : ℚ) * (b : ℚ) = (n : ℚ) * (n : ℚ) := by exact_mod_cast hab
  rw [hxq, hyq]
  field_simp [hnq, han, hbn]
  nlinarith [habq]

/-- **Lemma C2** (Obláth identity, pure identity). If `n + 1 = (4s+3)·m`, then
`4/n = 1/((s+1)m) + 1/((s+1)n) + 1/((s+1)mn)`. -/
lemma oblath_identity {n s m : ℕ} (hm : 1 ≤ m) (hn : n + 1 = (4 * s + 3) * m) :
    (4 : ℚ) / (n : ℚ) =
      (1 : ℚ) / (((s + 1) * m : ℕ) : ℚ) +
      (1 : ℚ) / (((s + 1) * n : ℕ) : ℚ) +
      (1 : ℚ) / (((s + 1) * m * n : ℕ) : ℚ) := by
  have h4s3 : 3 ≤ 4 * s + 3 := by omega
  have hprod_ge3 : 3 ≤ (4 * s + 3) * m := by
    have hmul : 3 * 1 ≤ (4 * s + 3) * m := Nat.mul_le_mul h4s3 hm
    simpa using hmul
  have hn2 : 2 ≤ n := by omega
  have hnpos : 0 < n := by omega
  have hs1 : 0 < s + 1 := Nat.succ_pos s
  have hm0 : 0 < m := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hm
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hx0 : (((s + 1) * m : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (Nat.ne_of_gt hs1) (Nat.ne_of_gt hm0))
  have hy0 : (((s + 1) * n : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (Nat.ne_of_gt hs1) (Nat.ne_of_gt hnpos))
  have hz0 : (((s + 1) * m * n : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.ne_of_gt hs1) (Nat.ne_of_gt hm0)) (Nat.ne_of_gt hnpos))
  have hnq : (n : ℚ) = (4 * (s : ℚ) + 3) * (m : ℚ) - 1 := by
    have h := congrArg (fun t : ℕ => (t : ℚ)) hn
    push_cast at h
    nlinarith
  field_simp [hn0, hx0, hy0, hz0]
  push_cast
  rw [hnq]
  ring

end ErdosStraus
