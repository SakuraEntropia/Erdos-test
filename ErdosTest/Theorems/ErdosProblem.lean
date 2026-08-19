import Mathlib

/-!
# Erdős–Straus 猜想（Erdős–Straus, 1948）

**猜想**：对每个整数 `n ≥ 2`，丢番图方程
```
4/n = 1/x + 1/y + 1/z
```
存在**正整数**解 `x, y, z`。

## 对象与量词
- 对象：`n x y z : ℕ`，其中 `n ≥ 2`，`x, y, z > 0`。
- 等式在有理数 `ℚ` 上成立（`(4 : ℚ) / (n : ℚ)` 等）。
- 量词：`∀ n ≥ 2, ∃ x y z > 0, 4/n = 1/x + 1/y + 1/z`。

## 已知等价形式
1. **分数形式**（主定义 `IsDecomposition`）。
2. **去分母形式** `4xyz = n(xy + yz + zx)`（`IsDecompositionCleared`，由
   `isDecomposition_iff_cleared` 证明与分数形式等价）。
3. （已知、未在此形式化）猜想可约化到**素数** `n`，且难点集中在 `n ≡ 1 (mod 4)` 的素数。

## 状态
猜想已用计算验证到很大的 `n`，但**至今未被证明**。本文件只陈述并形式化该猜想，
不声称任何进展，且不使用 `sorry`。
-/

noncomputable section

namespace ErdosStraus

/-- 分数形式：`4/n = 1/x + 1/y + 1/z`（在 `ℚ` 上）。 -/
def IsDecomposition (n x y z : ℕ) : Prop :=
  (4 : ℚ) / (n : ℚ) = (1 : ℚ) / (x : ℚ) + (1 : ℚ) / (y : ℚ) + (1 : ℚ) / (z : ℚ)

/-- 去分母形式：`4xyz = n(xy + yz + zx)`（在 `ℚ` 上）。 -/
def IsDecompositionCleared (n x y z : ℕ) : Prop :=
  (4 : ℚ) * (x : ℚ) * (y : ℚ) * (z : ℚ) =
    (n : ℚ) * ((x : ℚ) * (y : ℚ) + (y : ℚ) * (z : ℚ) + (z : ℚ) * (x : ℚ))

/-- **Erdős–Straus 猜想**：每个 `n ≥ 2` 都存在正整数 `x, y, z` 使 `4/n = 1/x + 1/y + 1/z`。 -/
def Conjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ IsDecomposition n x y z

/-- `n = 2` 的显式解：`4/2 = 1/1 + 1/2 + 1/2`。 -/
lemma two_has_decomposition : IsDecomposition 2 1 2 2 := by
  norm_num [IsDecomposition]

/-- 偶数 `n = 2k` 总有解 `(k, 2k, 2k)`：`4/(2k) = 1/k + 1/(2k) + 1/(2k)`。 -/
lemma even_decomposition {k : ℕ} (hk : 0 < k) : IsDecomposition (2 * k) k (2 * k) (2 * k) := by
  unfold IsDecomposition
  have hk0 : (k : ℚ) ≠ 0 := by positivity
  have h2k0 : ((2 * k : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp [hk0, h2k0]
  push_cast
  ring

/-- 分数形式与去分母形式等价（需 `n ≥ 2` 且 `x, y, z > 0`）。 -/
lemma isDecomposition_iff_cleared {n x y z : ℕ} (hn : 2 ≤ n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    IsDecomposition n x y z ↔ IsDecompositionCleared n x y z := by
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have hx0 : (x : ℚ) ≠ 0 := by positivity
  have hy0 : (y : ℚ) ≠ 0 := by positivity
  have hz0 : (z : ℚ) ≠ 0 := by positivity
  constructor
  · intro h
    unfold IsDecompositionCleared
    unfold IsDecomposition at h
    have h' : (4 : ℚ) * (x : ℚ) * (y : ℚ) * (z : ℚ) =
        (n : ℚ) * ((x : ℚ) * (y : ℚ) + (y : ℚ) * (z : ℚ) + (z : ℚ) * (x : ℚ)) := by
      field_simp [hn0, hx0, hy0, hz0] at h
      ring_nf at h ⊢
      exact h
    exact h'
  · intro h
    unfold IsDecomposition
    unfold IsDecompositionCleared at h
    field_simp [hn0, hx0, hy0, hz0]
    ring_nf at h ⊢
    exact h

end ErdosStraus
