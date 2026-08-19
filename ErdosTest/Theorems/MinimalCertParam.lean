import ErdosTest.Theorems.Certificate
import ErdosTest.Theorems.MinimalCertificate

/-!
# 最小证书参数的精确刻画：`a = 3` 确为最小

本文件补齐「最小证书」叙述的最后一块：对 `n ≡ 1 (mod 4)`（即 `n = 4k+1`），证书参数
`a = 4x − n` 的**精确同余与下界**。

`Certificate.lean` 中的 `solution_gives_certificate` 把任意解 `(x, y, z)` 对应到一个
因子证书 `(a, d, e)`，其中 `a = 4x − n`（加法形式 `a + n = 4x`）。`MinimalCertificate.lean`
的 `x_ge_minimal` 证明了对任何解都有 `x ≥ k+1`（故 `a = 4x − n ≥ 3`）。本文件证明：

1. `certificate_param_mod_four`：`4x − (4k+1) = 4·(x − k − 1) + 3`，即 `a ≡ 3 (mod 4)`。
   这是「证书参数必 ≡ 3 (mod 4)」的干净形式（显式给出商 `t = x − k − 1`）。
2. `certificate_param_mod_eq_three`：同一事实的模运算形式 `(4x − (4k+1)) % 4 = 3`。
3. `certificate_param_ge_three`：`3 ≤ 4x − (4k+1)`（故 `3` 是下界）。
4. `certificate_param_eq_three_iff`：`a = 3 ⟺ x = k+1`（`3` 恰在最小 `x` 处取到）。
5. `certificate_param_minimal`：对任何解，证书参数 `a` 满足 `∃ t, a = 4t + 3` 且 `3 ≤ a`，
   即 `a = 3` 是**最小可能**的证书参数（因为 `a ≡ 3 (mod 4)` 且 `a > 0`）。

综合 3 与 4：`a` 的取值集合是 `{4t + 3 | t ≥ 0} = {3, 7, 11, …}`，且 `a = 3` 恰好对应
`x = k+1`（`MinimalCertificate` 中 `A3Solvable` 所取的最小 `x`）。故「最小证书」名副其实。

证明只用 `omega`（与一次 `Nat.add_mul_mod_self_left`），不用 `sorry`。

（关于本文件之外的尝试：目标 (A) 的素数因子刻画与目标 (B) 的新模类恒等式，见文件尾
 `# 记录` 注记与 `PrimeModThree.lean`。本文件不含任何未完成证明。）
-/

namespace ErdosStraus

/-- `n = 4k+1` 且 `x ≥ k+1` 时，证书参数 `a = 4x − n` 等于 `4t + 3`（`t = x − k − 1`），即 `a ≡ 3 (mod 4)`。 -/
lemma certificate_param_mod_four {k x : ℕ} (hx : k + 1 ≤ x) :
    4 * x - (4 * k + 1) = 4 * (x - (k + 1)) + 3 := by
  omega

/-- 同一定理的模运算形式：`(4x − (4k+1)) % 4 = 3`。 -/
lemma certificate_param_mod_eq_three {k x : ℕ} (hx : k + 1 ≤ x) :
    (4 * x - (4 * k + 1)) % 4 = 3 := by
  rw [certificate_param_mod_four hx]
  rw [show 4 * (x - (k + 1)) + 3 = 3 + 4 * (x - (k + 1)) by omega]
  rw [Nat.add_mul_mod_self_left]

/-- `n = 4k+1` 且 `x ≥ k+1` 时，证书参数 `a = 4x − n ≥ 3`。 -/
lemma certificate_param_ge_three {k x : ℕ} (hx : k + 1 ≤ x) :
    3 ≤ 4 * x - (4 * k + 1) := by
  omega

/-- 证书参数 `a = 4x − n` 取到最小值 `3` 当且仅当 `x = k+1`（即取最小 `x`）。 -/
lemma certificate_param_eq_three_iff {k x : ℕ} (hx : k + 1 ≤ x) :
    4 * x - (4 * k + 1) = 3 ↔ x = k + 1 := by
  constructor <;> omega

/-- **最小证书主引理**：对 `n = 4k+1` 的任意解 `(x, y, z)`，证书参数 `a = 4x − n` 满足
`a ≡ 3 (mod 4)`（即 `∃ t, a = 4t + 3`）且 `3 ≤ a`。因 `a = 3` 恰在 `x = k+1` 处取到
（`certificate_param_eq_three_iff`），故 `3` 是**最小可能**的证书参数。 -/
lemma certificate_param_minimal {k x y z : ℕ} (hk : 1 ≤ k) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (h : IsDecomposition (4 * k + 1) x y z) :
    (∃ t : ℕ, 4 * x - (4 * k + 1) = 4 * t + 3) ∧ 3 ≤ 4 * x - (4 * k + 1) := by
  have hxge : k + 1 ≤ x := x_ge_minimal hk hx hy hz h
  exact ⟨⟨x - (k + 1), certificate_param_mod_four hxge⟩, certificate_param_ge_three hxge⟩

/-- **推论**：证书参数 `a = 4x − n` 的模 4 余数恒为 `3`，且 `a` 严格大于 `0`（因 `3 ≤ a`）。
因此 `a` 的取值被限制在 `{3, 7, 11, …}`，最小值为 `3`。 -/
lemma certificate_param_bounds {k x y z : ℕ} (hk : 1 ≤ k) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (h : IsDecomposition (4 * k + 1) x y z) :
    (4 * x - (4 * k + 1)) % 4 = 3 ∧ 3 ≤ 4 * x - (4 * k + 1) := by
  have hxge : k + 1 ≤ x := x_ge_minimal hk hx hy hz h
  exact ⟨certificate_param_mod_eq_three hxge, certificate_param_ge_three hxge⟩

end ErdosStraus

/-!
# 记录：本文件之外尝试的目标与失败原因

* **目标 (B)（新模类恒等式）**：尝试为 `n ≡ 9 (mod 16)`、`n ≡ 1 (mod 24)`、`n ≡ 1 (mod 8)`
  寻找形如 `4/n = 1/x + 1/y + 1/z` 的参数化多项式恒等式（用 `sympy` 对 `x, y, z` 为
  `k` 的小系数低次多项式做符号搜索）。结果：**没有找到**任何整系数多项式恒等式。
  这与文献一致——`n ≡ 1 (mod 8)` 正是 Erdős–Straus 猜想的困难情形：对称 `y = z` 分支
  只有 `a = 4x − n` 整除 `2nx` 时成立，而 `n ≡ 1 (mod 8)` 时 `a ≡ 3 (mod 4)` 的最小值
  `a = 3` 迫使 `x = (n+3)/4`，此时 `M = n·x ≡ 1 (mod 3)`（因 `n ≡ x ≡ 1 (mod 3)`），
  `a = 3` 无法给出整解；更大的 `a = 4t − 1` 不整除 `2nx` 的多项式部分。故这些模类
  **不存在**简单的单参数多项式恒等式，需素因子分解（即目标 (A)）或非多项式约化。
* **目标 (A)（素数因子刻画）**：见 `PrimeModThree.lean` 的尝试记录；核心障碍是
  `Nat.factors`/`Nat.factorization` 与 `ZMod 3` 之间的乘积-同余桥梁在 Mathlib 中缺乏
  现成的一步到位引理，需手工归纳。

本文件（目标 (C)）全部用 `omega` 完成，无 `sorry`。
-/
