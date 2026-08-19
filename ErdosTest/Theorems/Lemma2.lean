import ErdosTest.Theorems.ErdosProblem

/-!
# Lemma 2：特殊模类下的参数化解

对若干模类，给出 `4/n` 作为三个单位分数之和的**参数化恒等式**（见
`Experiments/results.md` 观察 2）。这些恒等式对所有 `k` 成立，故对应的 `n` 满足猜想。

- `n ≡ 0 (mod 2)`：偶数（已在 `ErdosProblem.lean` 证明为 `even_decomposition`）。
- `n ≡ 0 (mod 3)`：`4/(3k) = 1/(2k) + 1/(2k) + 1/(3k)`。
- `n ≡ 2 (mod 3)`：`4/(3k+2) = 1/(k+1) + 1/(3k+2) + 1/((k+1)(3k+2))`。
- `n ≡ 3 (mod 4)`：`4/(4k+3) = 1/(k+1) + 1/(2(k+1)(4k+3)) + 1/(2(k+1)(4k+3))`。

每条都由 `field_simp`（去分母）+ `push_cast` + `ring` 证明，不使用 `sorry`。
-/

namespace ErdosStraus

/-- `n ≡ 0 (mod 3)`：`n = 3k` 时 `(2k, 2k, 3k)` 是解。 -/
lemma three_divides {k : ℕ} (hk : 0 < k) : IsDecomposition (3 * k) (2 * k) (2 * k) (3 * k) := by
  unfold IsDecomposition
  have hk0 : (k : ℚ) ≠ 0 := by positivity
  have h2k0 : ((2 * k : ℕ) : ℚ) ≠ 0 := by positivity
  have h3k0 : ((3 * k : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp [hk0, h2k0, h3k0]
  push_cast
  ring

/-- `n ≡ 2 (mod 3)`：`n = 3k+2` 时 `(k+1, n, (k+1)n)` 是解。 -/
lemma two_mod_three {k : ℕ} :
    IsDecomposition (3 * k + 2) (k + 1) (3 * k + 2) ((k + 1) * (3 * k + 2)) := by
  unfold IsDecomposition
  have hk1 : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hn : ((3 * k + 2 : ℕ) : ℚ) ≠ 0 := by positivity
  have hk1n : (((k + 1) * (3 * k + 2) : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp [hk1, hn, hk1n]
  push_cast
  ring

/-- `n ≡ 3 (mod 4)`：`n = 4k+3` 时 `(k+1, 2(k+1)n, 2(k+1)n)` 是解。 -/
lemma three_mod_four {k : ℕ} :
    IsDecomposition (4 * k + 3) (k + 1) (2 * (k + 1) * (4 * k + 3)) (2 * (k + 1) * (4 * k + 3)) := by
  unfold IsDecomposition
  have hk1 : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hn : ((4 * k + 3 : ℕ) : ℚ) ≠ 0 := by positivity
  have hy : ((2 * (k + 1) * (4 * k + 3) : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp [hk1, hn, hy]
  push_cast
  ring

/-- 偶数情形（`n = 2k`）的引用包装：`(k, 2k, 2k)` 是解。 -/
lemma even_solution {k : ℕ} (hk : 0 < k) : IsDecomposition (2 * k) k (2 * k) (2 * k) :=
  even_decomposition hk

/-- 综合：`n` 被 2 或 3 整除、或 `n ≡ 3 (mod 4)` 时，猜想对 `n` 成立。 -/
lemma easy_classes (n : ℕ) (hn : 2 ≤ n) :
    (2 ∣ n ∨ 3 ∣ n ∨ n % 4 = 3) →
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ IsDecomposition n x y z := by
  intro h
  rcases h with h2 | h3 | h4
  · rcases h2 with ⟨k, rfl⟩
    have hk : 0 < k := by omega
    refine ⟨k, 2 * k, 2 * k, hk, by positivity, by positivity, even_solution hk⟩
  · rcases h3 with ⟨k, rfl⟩
    have hk : 0 < k := by omega
    refine ⟨2 * k, 2 * k, 3 * k, by positivity, by positivity, by positivity, three_divides hk⟩
  · refine ⟨n / 4 + 1, 2 * (n / 4 + 1) * n, 2 * (n / 4 + 1) * n,
        by positivity, by positivity, by positivity, ?_⟩
    have hn_eq : n = 4 * (n / 4) + 3 := by
      have hdiv : n % 4 + 4 * (n / 4) = n := Nat.mod_add_div n 4
      rw [h4] at hdiv
      omega
    simpa [← hn_eq] using (three_mod_four (k := n / 4))

end ErdosStraus
