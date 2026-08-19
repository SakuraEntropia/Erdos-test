import ErdosTest.Theorems.ErdosProblem

/-!
# MainResult：伸缩不变性与素数约化

这是本次形式化最核心的**结构约化**：

1. **伸缩不变性**（`scale`）：若 `n` 有正解 `(x, y, z)`，则任意正倍数 `k·n` 也有正解
   `(k·x, k·y, k·z)`（把每个单位分数的分母都乘以 `k`）。
2. **素数约化**（`reduction_to_primes`）：由强归纳 + 伸缩不变性，猜想等价于“对所有素数成立”。

这解释了为什么 Erdős–Straus 猜想通常只需对素数检验。
-/

namespace ErdosStraus

/-- 伸缩不变性：`n` 有正解 ⇒ `k·n` 有正解（核心代数步骤）。 -/
lemma scale {n k x y z : ℕ} (hn : 2 ≤ n) (hk : 0 < k) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : IsDecomposition n x y z) : IsDecomposition (k * n) (k * x) (k * y) (k * z) := by
  rw [isDecomposition_iff_cleared hn hx hy hz] at h
  have hk1 : 1 ≤ k := by omega
  have hn_le : n ≤ k * n := by
    have h : n * 1 ≤ n * k := Nat.mul_le_mul_left n hk1
    simpa [Nat.mul_comm] using h
  have h2le : 2 ≤ k * n := le_trans hn hn_le
  rw [isDecomposition_iff_cleared h2le (Nat.mul_pos hk hx) (Nat.mul_pos hk hy) (Nat.mul_pos hk hz)]
  unfold IsDecompositionCleared at h ⊢
  push_cast at h ⊢
  calc
    (4 : ℚ) * ((k : ℚ) * (x : ℚ)) * ((k : ℚ) * (y : ℚ)) * ((k : ℚ) * (z : ℚ))
        = (k : ℚ) * (k : ℚ) * (k : ℚ) * ((4 : ℚ) * (x : ℚ) * (y : ℚ) * (z : ℚ)) := by ring
    _ = (k : ℚ) * (k : ℚ) * (k : ℚ) * ((n : ℚ) * ((x : ℚ) * (y : ℚ) + (y : ℚ) * (z : ℚ) + (z : ℚ) * (x : ℚ))) := by rw [h]
    _ = (k : ℚ) * (n : ℚ) * (((k : ℚ) * (x : ℚ)) * ((k : ℚ) * (y : ℚ)) + ((k : ℚ) * (y : ℚ)) * ((k : ℚ) * (z : ℚ)) + ((k : ℚ) * (z : ℚ)) * ((k : ℚ) * (x : ℚ))) := by ring

/-- 有正解 ⇒ 任意正倍数有正解。 -/
lemma scale_of_solution {n : ℕ} (hn : 2 ≤ n) {k : ℕ} (hk : 0 < k)
    (h : ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ IsDecomposition n x y z) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ IsDecomposition (k * n) x y z := by
  rcases h with ⟨x, y, z, hx, hy, hz, hxyz⟩
  refine ⟨k * x, k * y, k * z, Nat.mul_pos hk hx, Nat.mul_pos hk hy, Nat.mul_pos hk hz, ?_⟩
  exact scale hn hk hx hy hz hxyz

/-- **素数约化**：猜想等价于其“素数版本”——只需对所有素数 `p` 成立。 -/
theorem reduction_to_primes :
    Conjecture ↔ ∀ p : ℕ, Nat.Prime p →
      ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ IsDecomposition p x y z := by
  constructor
  · intro hC p hp
    exact hC p (Nat.Prime.two_le hp)
  · intro hP n hn
    have hind : ∀ m, (∀ t, t < m → (2 ≤ t → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ IsDecomposition t x y z)) →
        2 ≤ m → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ IsDecomposition m x y z := by
      intro m ih hm
      by_cases hp : Nat.Prime m
      · exact hP m hp
      · rcases Nat.exists_prime_and_dvd (by omega : m ≠ 1) with ⟨p, hpp, hpdvd⟩
        have hp_le : p ≤ m := Nat.le_of_dvd (by omega : 0 < m) hpdvd
        have hp_pos : 0 < p := Nat.Prime.pos hpp
        have hp_lt_m : p < m := Nat.lt_of_le_of_ne hp_le (by
          intro hpm
          exact hp (hpm ▸ hpp))
        have hm_eq : p * (m / p) = m := Nat.mul_div_cancel' hpdvd
        have hm_ge2 : 2 ≤ m / p := by
          by_contra hnot
          have hm_le1 : m / p ≤ 1 := by omega
          have hm_pos : 0 < m / p := by
            rw [Nat.div_pos_iff]
            exact ⟨hp_pos, hp_le⟩
          have hm_eq1 : m / p = 1 := by omega
          have hm_eq_p : m = p := by
            rw [← hm_eq, hm_eq1, Nat.mul_one]
          omega
        have hm_lt : m / p < m := by
          have hlt' : m / p < p * (m / p) := by
            calc
              m / p = 1 * (m / p) := by rw [one_mul]
              _ < p * (m / p) :=
                Nat.mul_lt_mul_of_pos_right (Nat.Prime.one_lt hpp) (by omega : 0 < m / p)
          simpa [hm_eq] using hlt'
        rcases ih (m / p) hm_lt hm_ge2 with ⟨x, y, z, hx, hy, hz, hxyz⟩
        have hsol := scale_of_solution hm_ge2 hp_pos ⟨x, y, z, hx, hy, hz, hxyz⟩
        simpa [hm_eq] using hsol
    exact Nat.strong_induction_on
      (p := fun m => 2 ≤ m → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ IsDecomposition m x y z)
      n hind hn

end ErdosStraus
