import ErdosTest.Theorems.ErdosProblem

/-!
# Lemma 1：有限基准情形

对最小的几个 `n`，给出 `4/n = 1/x + 1/y + 1/z` 的**显式正整数解**。

这些是猜想的“有限基准情形”。它们只是具体的有限实例，不涉及任何未证事实；
每个 `IsDecomposition n x y z` 都由 `norm_num` 直接判定。
-/

namespace ErdosStraus

/-- `n = 2`：`4/2 = 1/1 + 1/2 + 1/2`。 -/
lemma two_has_solution : ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ IsDecomposition 2 x y z := by
  refine ⟨1, 2, 2, by norm_num, by norm_num, by norm_num, ?_⟩
  exact two_has_decomposition

/-- `n = 3`：`4/3 = 1/2 + 1/2 + 1/3`。 -/
lemma three_has_solution : ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ IsDecomposition 3 x y z := by
  refine ⟨2, 2, 3, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num [IsDecomposition]

/-- `n = 4`：`4/4 = 1/2 + 1/3 + 1/6`。 -/
lemma four_has_solution : ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ IsDecomposition 4 x y z := by
  refine ⟨2, 3, 6, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num [IsDecomposition]

/-- `n = 5`：`4/5 = 1/2 + 1/5 + 1/10`。 -/
lemma five_has_solution : ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ IsDecomposition 5 x y z := by
  refine ⟨2, 5, 10, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num [IsDecomposition]

/-- 前四个 `n`（2, 3, 4, 5）都满足猜想（即存在正整数解）。 -/
lemma small_cases : ∀ n : ℕ, n ∈ ({2, 3, 4, 5} : Finset ℕ) →
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ IsDecomposition n x y z := by
  intro n hn
  fin_cases hn <;> first | exact two_has_solution | exact three_has_solution |
    exact four_has_solution | exact five_has_solution

end ErdosStraus
