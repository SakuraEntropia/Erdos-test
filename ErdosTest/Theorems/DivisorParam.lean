import ErdosTest.Theorems.ErdosProblem

/-!
# 因子参数化（Divisor Parametrization）

这是 Phase 6 所选方向「因子证书重构」的核心形式化。目标：把三变量方程
`4/n = 1/x + 1/y + 1/z` 归结为一个关于 `n²` 的因子的算术问题。

**Lemma A**：对称（归一化）等价形式
`4xyz = n(xy+yz+zx) ↔ (4x−n)(4y−n)(4z−n) = n²(4(x+y+z)−n)`。

**Lemma B**：任何解满足 `n < 4x`（即 `4x−n > 0`），这是参数化合法性的前提。

**Lemma C**：因子构造（充分方向）。若 `a+n = 4x`、`a·y = d + nx`、`a·z = e + nx`、
`d·e = (nx)²`，则 `(x, y, z)` 是解。这是 Elsholtz–Tao / Swett 使用的标准参数化，
用**加法形式** `a+n = 4x` 表述以避免自然数减法的截断。

**Lemma D**：Phase-4 符号搜索独立发现的 `n ≡ 5 (mod 8)` 恒等式
`4/(8k+5) = 1/(3k+2) + 1/(6k+4) + 1/(48k²+62k+20)`。

所有证明只用 `nlinarith` / `ring` / 整除，不用 `sorry`。
-/

namespace ErdosStraus

/-- **Lemma A**：去分母形式等价于对称的“归一化”形式（纯代数，对任意 n,x,y,z 成立）。 -/
lemma cleared_iff_normalized {n x y z : ℕ} :
    IsDecompositionCleared n x y z ↔
      ((4 : ℚ) * (x : ℚ) - (n : ℚ)) * ((4 : ℚ) * (y : ℚ) - (n : ℚ)) *
          ((4 : ℚ) * (z : ℚ) - (n : ℚ)) =
        (n : ℚ) * (n : ℚ) * ((4 : ℚ) * ((x : ℚ) + (y : ℚ) + (z : ℚ)) - (n : ℚ)) := by
  unfold IsDecompositionCleared
  constructor <;> intro h <;> nlinarith

/-- **Lemma B**：任何解都有 `n < 4x`（所以 `4x − n > 0`）。 -/
lemma solution_bound {n x y z : ℕ} (hn : 2 ≤ n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : IsDecomposition n x y z) : n < 4 * x := by
  have hc : IsDecompositionCleared n x y z := (isDecomposition_iff_cleared hn hx hy hz).1 h
  unfold IsDecompositionCleared at hc
  have hnq : (0 : ℚ) < (n : ℚ) := by positivity
  have hxyq : (0 : ℚ) < (x : ℚ) * (y : ℚ) := by positivity
  have hxzq : (0 : ℚ) < (x : ℚ) * (z : ℚ) := by positivity
  have hsum_gt : (y : ℚ) * (z : ℚ) < (x : ℚ) * (y : ℚ) + (y : ℚ) * (z : ℚ) + (z : ℚ) * (x : ℚ) := by
    nlinarith [hxyq, hxzq]
  have hlt : (n : ℚ) * ((y : ℚ) * (z : ℚ)) < (4 : ℚ) * (x : ℚ) * (y : ℚ) * (z : ℚ) := by
    nlinarith [hc, hsum_gt, hnq]
  have hyzq : (0 : ℚ) < (y : ℚ) * (z : ℚ) := by positivity
  have hxlt : (n : ℚ) < (4 : ℚ) * (x : ℚ) := by
    nlinarith [hlt, hyzq]
  exact_mod_cast hxlt

/-- **Lemma C**：因子构造（充分方向）。用加法形式 `a + n = 4x` 避免自然数减法截断。 -/
lemma divisor_construction {n x y z d e a : ℕ}
    (hn : 2 ≤ n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ha : 0 < a)
    (h4x : a + n = 4 * x)
    (hay : a * y = d + n * x)
    (haz : a * z = e + n * x)
    (hde : d * e = (n * x) * (n * x)) :
    IsDecomposition n x y z := by
  have hc : IsDecompositionCleared n x y z := by
    unfold IsDecompositionCleared
    -- 目标：4·x·y·z = n·(x·y + y·z + z·x)，由以下 ℚ 等式推出
    have h4xq : (a : ℚ) + (n : ℚ) = (4 : ℚ) * (x : ℚ) := by
      exact_mod_cast h4x
    have hayq : (a : ℚ) * (y : ℚ) = (d : ℚ) + (n : ℚ) * (x : ℚ) := by
      exact_mod_cast hay
    have hazq : (a : ℚ) * (z : ℚ) = (e : ℚ) + (n : ℚ) * (x : ℚ) := by
      exact_mod_cast haz
    have hdeq : (d : ℚ) * (e : ℚ) = (n : ℚ) * (x : ℚ) * ((n : ℚ) * (x : ℚ)) := by
      have h := congrArg (fun t : ℕ => (t : ℚ)) hde
      simpa [Nat.cast_mul] using h
    have haq : (0 : ℚ) < (a : ℚ) := by positivity
    -- 关键恒等式：a·y·z = n·x·(y + z)
    have hkey : (a : ℚ) * (y : ℚ) * (z : ℚ) = (n : ℚ) * (x : ℚ) * ((y : ℚ) + (z : ℚ)) := by
      nlinarith [hayq, hazq, hdeq, haq]
    calc
      (4 : ℚ) * (x : ℚ) * (y : ℚ) * (z : ℚ)
          = ((a : ℚ) + (n : ℚ)) * (y : ℚ) * (z : ℚ) := by rw [← h4xq]
      _ = (a : ℚ) * (y : ℚ) * (z : ℚ) + (n : ℚ) * (y : ℚ) * (z : ℚ) := by ring
      _ = (n : ℚ) * (x : ℚ) * ((y : ℚ) + (z : ℚ)) + (n : ℚ) * (y : ℚ) * (z : ℚ) := by rw [hkey]
      _ = (n : ℚ) * ((x : ℚ) * (y : ℚ) + (y : ℚ) * (z : ℚ) + (z : ℚ) * (x : ℚ)) := by ring
  exact (isDecomposition_iff_cleared hn hx hy hz).2 hc

/-- **Lemma D**：`n ≡ 5 (mod 8)` 的恒等式（Phase-4 符号搜索发现；属于 mod-840 约化的一个特例）。 -/
lemma five_mod_eight {k : ℕ} :
    IsDecomposition (8 * k + 5) (3 * k + 2) (6 * k + 4) (48 * k * k + 62 * k + 20) := by
  unfold IsDecomposition
  have hn : ((8 * k + 5 : ℕ) : ℚ) ≠ 0 := by positivity
  have hx : ((3 * k + 2 : ℕ) : ℚ) ≠ 0 := by positivity
  have hy : ((6 * k + 4 : ℕ) : ℚ) ≠ 0 := by positivity
  have hz : ((48 * k * k + 62 * k + 20 : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp [hn, hx, hy, hz]
  push_cast
  ring

end ErdosStraus
