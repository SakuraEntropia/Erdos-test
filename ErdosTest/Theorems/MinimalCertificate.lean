import ErdosTest.Theorems.ErdosProblem
import ErdosTest.Theorems.DivisorParam
import ErdosTest.Theorems.Certificate
import ErdosTest.Theorems.ACases

/-!
# 最小证书（`a = 3`）的完全刻画

本文件把 Phase 7/8 的「最小证书」观察推进为**双向**的机器验证定理：

1. `x_ge_minimal`：对 `n ≡ 1 (mod 4)`（`n = 4k+1`），任何解的第一个分母 `x` 都满足
   `x ≥ k+1 = (n+3)/4`。即 `x₀ = (n+3)/4` 确实是**最小可能**的 `x`，故 `a = 4x−n = 3`
   是**最小可能的证书参数**。

2. `three_dvd_4k1_iff_three_dvd_k1`：`3 ∣ 4k+1 ↔ 3 ∣ k+1`（它们相差 `3k`），
   这是把「`3 ∣ d+M`」读作「`d ≡ −M ≡ 2 (mod 3)`」所需的模-3 桥梁。

3. `a3_solvable_gives_divisor`（**必要方向**，本阶段新增）与 `a3_solution`（充分方向，
   见 `ACases.lean`）合起来给出：

4. `a3_iff_divisor`（**主定理**）：对 `k ≥ 1`（即 `n = 4k+1 ≥ 5`），
   `4/(4k+1)` 有解 `(k+1, y, z)`（即 `a = 3` 可解）当且仅当存在互补因子 `d, e` 满足
   `d·e = ((4k+1)(k+1))²` 且 `3 ∣ d+(4k+1)(k+1)`、`3 ∣ e+(4k+1)(k+1)`。

   这是 `solvable_iff_certificate` 在 `a = 3`、`x = k+1` 上的**精确特化**，把 `a = 3`
   可解性化为一个纯因子/同余条件，无需素因子分解。

不声称猜想成立。证明只用 `omega` / `simpa` / `ring` / 整除，不用 `sorry`。
-/

namespace ErdosStraus

/-- `a = 3` 可解：存在 `y, z > 0` 使 `4/(4k+1) = 1/(k+1) + 1/y + 1/z`（`x = k+1` 取最小）。 -/
def A3Solvable (k : ℕ) : Prop :=
  ∃ y z : ℕ, 0 < y ∧ 0 < z ∧ IsDecomposition (4 * k + 1) (k + 1) y z

/-- `a = 3` 证书：互补因子 `d, e` 满足 `d·e = M²` 与 `3 ∣ d+M`、`3 ∣ e+M`，`M = (4k+1)(k+1)`。 -/
def A3Certificate (k : ℕ) : Prop :=
  ∃ d e : ℕ, 0 < d ∧ 0 < e ∧
    d * e = ((4 * k + 1) * (k + 1)) * ((4 * k + 1) * (k + 1)) ∧
    3 ∣ d + (4 * k + 1) * (k + 1) ∧ 3 ∣ e + (4 * k + 1) * (k + 1)

/-- 对 `n ≡ 1 (mod 4)`，任何解的第一个分母 `x ≥ (n+3)/4 = k+1`（最小 `x`）。 -/
lemma x_ge_minimal {k x y z : ℕ} (hk : 1 ≤ k) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : IsDecomposition (4 * k + 1) x y z) : k + 1 ≤ x := by
  have hb : 4 * k + 1 < 4 * x :=
    solution_bound (n := 4 * k + 1) (by omega) hx hy hz h
  omega

/-- `3 ∣ 4k+1 ↔ 3 ∣ k+1`（两者相差 `3k`）。 -/
lemma three_dvd_4k1_iff_three_dvd_k1 (k : ℕ) : 3 ∣ 4 * k + 1 ↔ 3 ∣ k + 1 := by
  constructor
  · intro h
    rcases h with ⟨c, hc⟩
    use c - k
    omega
  · intro h
    rcases h with ⟨c, hc⟩
    use c + k
    omega

/-- **必要方向**：`a = 3` 解 ⇒ `a = 3` 证书（互补因子 `d, e`）。 -/
lemma a3_solvable_gives_divisor {k y z : ℕ} (hk : 1 ≤ k) (hy : 0 < y) (hz : 0 < z)
    (h : IsDecomposition (4 * k + 1) (k + 1) y z) :
    A3Certificate k := by
  have hn : 2 ≤ 4 * k + 1 := by omega
  have hx : 0 < k + 1 := by omega
  rcases solution_gives_certificate (n := 4 * k + 1) (x := k + 1) hn hx hy hz h with
    ⟨a, d, e, _ha, hd, he, h4x, hAy, hAz, hde⟩
  have ha_eq3 : a = 3 := by omega
  refine ⟨d, e, hd, he, hde, ?_, ?_⟩
  · exact ⟨y, by simpa [ha_eq3] using hAy.symm⟩
  · exact ⟨z, by simpa [ha_eq3] using hAz.symm⟩

/-- **主定理**：`a = 3` 可解 ⟺ `a = 3` 证书（最小证书的完全刻画）。 -/
theorem a3_iff_divisor (k : ℕ) (hk : 1 ≤ k) : A3Solvable k ↔ A3Certificate k := by
  constructor
  · intro h
    rcases h with ⟨y, z, hy, hz, hxyz⟩
    exact a3_solvable_gives_divisor hk hy hz hxyz
  · intro h
    rcases h with ⟨d, e, hd, he, hde, h3d, h3e⟩
    refine ⟨(d + (4 * k + 1) * (k + 1)) / 3, (e + (4 * k + 1) * (k + 1)) / 3, ?_, ?_, ?_⟩
    · rw [Nat.div_pos_iff]
      exact ⟨by norm_num, Nat.le_of_dvd (by omega : 0 < d + (4 * k + 1) * (k + 1)) h3d⟩
    · rw [Nat.div_pos_iff]
      exact ⟨by norm_num, Nat.le_of_dvd (by omega : 0 < e + (4 * k + 1) * (k + 1)) h3e⟩
    · exact a3_solution hk hd he hde h3d h3e

end ErdosStraus
