import ErdosTest.Theorems.ErdosProblem
import ErdosTest.Theorems.DivisorParam

/-!
# `a = 3` 情形：最小证书的显式结构

对 `n ≡ 1 (mod 4)`，令 `x = (n+3)/4`（即证书参数 `a = 4x − n = 3`，这是 `n ≡ 1 (mod 4)`
下**最小可能**的 `a`）。此时有精确的约化：

    4/n = 1/x + 3/(n·x)  （即 1/y + 1/z = 3/(n·x)，一个「两项」单位分数分解）。

本文件形式化：

1. `four_minus_recip_reduction`：`4/(4k+1) = 1/(k+1) + 3/((4k+1)(k+1))`。
2. `five_mod_eight_minimal`：`n ≡ 5 (mod 8)` 时 `a = 3` 的**显式解**
   `(2k+2, (8k+5)(k+1), 2(8k+5)(k+1))`（比 `five_mod_eight` 的 `x = 3k+2` 更小）。
3. `a3_solution`：`a = 3` 情形的**充分条件**——若 `d·e = (n·x)²` 且
   `3 ∣ d + n·x`、`3 ∣ e + n·x`，则 `(x, (d+nx)/3, (e+nx)/3)` 是解。
   （这是 `divisor_construction` 在 `a = 3` 的直接推论。）

计算证据（`Experiments/certificate_conjectures.py`，register B）确认：对素数 `p ≡ 1 (mod 4)`
`a = 3` 有解 ⟺ `p ≡ 2 (mod 3)` 或 `(p+3)/4` 有素因子 `≡ 2 (mod 3)`。本文件的
`a3_solution` 是「充分方向」的形式化；「必要条件」需要素因子分解，未在本文件证明。
-/

namespace ErdosStraus

/-- `4/(4k+1) = 1/(k+1) + 3/((4k+1)(k+1))`：`a = 3` 情形的精确约化。 -/
lemma four_minus_recip_reduction {k : ℕ} :
    (4 : ℚ) / ((4 * k + 1 : ℕ) : ℚ) =
      (1 : ℚ) / ((k + 1 : ℕ) : ℚ) + (3 : ℚ) / (((4 * k + 1) * (k + 1) : ℕ) : ℚ) := by
  have hn : ((4 * k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hx : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hM : (((4 * k + 1) * (k + 1) : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp [hn, hx, hM]
  push_cast
  ring

/-- `n ≡ 5 (mod 8)`：`a = 3` 的显式解（`x = 2k+2` 是最小的 `x > n/4`）。 -/
lemma five_mod_eight_minimal {k : ℕ} :
    IsDecomposition (8 * k + 5) (2 * k + 2) ((8 * k + 5) * (k + 1)) (2 * ((8 * k + 5) * (k + 1))) := by
  unfold IsDecomposition
  have hn : ((8 * k + 5 : ℕ) : ℚ) ≠ 0 := by positivity
  have hx : ((2 * k + 2 : ℕ) : ℚ) ≠ 0 := by positivity
  have hy : (((8 * k + 5) * (k + 1) : ℕ) : ℚ) ≠ 0 := by positivity
  have hz : ((2 * ((8 * k + 5) * (k + 1)) : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp [hn, hx, hy, hz]
  push_cast
  ring

/-- **`a = 3` 充分条件**：给出一对互补因子 `d, e` 且 `3 ∣ d + nx`、`3 ∣ e + nx`，则得到解。 -/
lemma a3_solution {k d e : ℕ}
    (hk : 1 ≤ k) (hd : 0 < d) (he : 0 < e)
    (hde : d * e = ((4 * k + 1) * (k + 1)) * ((4 * k + 1) * (k + 1)))
    (h3d : 3 ∣ d + (4 * k + 1) * (k + 1))
    (h3e : 3 ∣ e + (4 * k + 1) * (k + 1)) :
    IsDecomposition (4 * k + 1) (k + 1) ((d + (4 * k + 1) * (k + 1)) / 3)
      ((e + (4 * k + 1) * (k + 1)) / 3) := by
  have hn : 2 ≤ 4 * k + 1 := by omega
  have hx : 0 < k + 1 := by omega
  have ha : 0 < 3 := by norm_num
  have h4x : 3 + (4 * k + 1) = 4 * (k + 1) := by ring
  have hay : 3 * ((d + (4 * k + 1) * (k + 1)) / 3) = d + (4 * k + 1) * (k + 1) := by
    exact Nat.mul_div_cancel' h3d
  have haz : 3 * ((e + (4 * k + 1) * (k + 1)) / 3) = e + (4 * k + 1) * (k + 1) := by
    exact Nat.mul_div_cancel' h3e
  have hy : 0 < (d + (4 * k + 1) * (k + 1)) / 3 := by
    rw [Nat.div_pos_iff]
    exact ⟨ha, Nat.le_of_dvd (by omega : 0 < d + (4 * k + 1) * (k + 1)) h3d⟩
  have hz : 0 < (e + (4 * k + 1) * (k + 1)) / 3 := by
    rw [Nat.div_pos_iff]
    exact ⟨ha, Nat.le_of_dvd (by omega : 0 < e + (4 * k + 1) * (k + 1)) h3e⟩
  exact divisor_construction hn hx hy hz ha h4x hay haz hde

end ErdosStraus
