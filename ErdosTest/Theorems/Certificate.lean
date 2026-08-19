import ErdosTest.Theorems.ErdosProblem
import ErdosTest.Theorems.DivisorParam

/-!
# 因子证书的双射与奇偶结构

本文件完成 Phase 6 所选方向「因子证书重构」的**充分且必要**两个方向：

1. **Lemma E（必要性）** `solution_gives_certificate`：每个解 `(x, y, z)` 都给出一个
   「因子证书」 `(a, d, e)`，满足 `a + n = 4x`、`a·y = d + n·x`、`a·z = e + n·x`、
   `d·e = (n·x)²`。与 `DivisorParam.lean` 中的 `divisor_construction`（充分方向）合起来，
   得到 **解 ⟺ 证书** 的完整双射 `solvable_iff_certificate`。

2. **奇偶结构**：`n` 为奇数时，任何解满足 `2 ∣ x·y + y·z + z·x`，即 `x, y, z` 中至多
   一个为奇数（否则 `x·y + y·z + z·x` 为奇，矛盾）。这是 2-进障碍的干净形式，解释了
   Phase-4 观察到「仿射恒等式无法覆盖 `n ≡ 1 (mod 8)`」背后的一个必然奇偶约束。

不声称猜想成立。全部证明用 `ring` / `nlinarith` / 整除 / `omega`，不用 `sorry`。
-/

namespace ErdosStraus

/-- 可解性：`4/n` 可写成三个（正）单位分数之和。 -/
def Solvable (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ IsDecomposition n x y z

/-- 因子证书：存在 `x, a, d, e` 满足加法恒等式与整除/因子条件。 -/
def HasCertificate (n : ℕ) : Prop :=
  ∃ x a d e : ℕ, 0 < x ∧ 0 < a ∧ 0 < d ∧ 0 < e ∧
    a + n = 4 * x ∧ a ∣ (d + n * x) ∧ a ∣ (e + n * x) ∧
    d * e = (n * x) * (n * x)

/-- **Lemma E（必要性）**：解 ⇒ 因子证书（加法形式，避免自然数减法截断）。 -/
lemma solution_gives_certificate {n x y z : ℕ}
    (hn : 2 ≤ n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : IsDecomposition n x y z) :
    ∃ a d e : ℕ, 0 < a ∧ 0 < d ∧ 0 < e ∧
      a + n = 4 * x ∧ a * y = d + n * x ∧ a * z = e + n * x ∧
      d * e = (n * x) * (n * x) := by
  let a := 4 * x - n
  let d := a * y - n * x
  let e := a * z - n * x
  have hnx : n < 4 * x := solution_bound hn hx hy hz h
  have ha : 0 < a := by omega
  have h4x : a + n = 4 * x := by omega
  have hc : IsDecompositionCleared n x y z := (isDecomposition_iff_cleared hn hx hy hz).1 h
  have h4xq : (a : ℚ) + (n : ℚ) = (4 : ℚ) * (x : ℚ) := by exact_mod_cast h4x
  have hcq : (4 : ℚ) * (x : ℚ) * (y : ℚ) * (z : ℚ) =
      (n : ℚ) * ((x : ℚ) * (y : ℚ) + (y : ℚ) * (z : ℚ) + (z : ℚ) * (x : ℚ)) := by
    unfold IsDecompositionCleared at hc
    exact hc
  have hkey : (a : ℚ) * (y : ℚ) * (z : ℚ) = (n : ℚ) * (x : ℚ) * ((y : ℚ) + (z : ℚ)) := by
    calc
      (a : ℚ) * (y : ℚ) * (z : ℚ)
          = ((a : ℚ) + (n : ℚ)) * (y : ℚ) * (z : ℚ) - (n : ℚ) * (y : ℚ) * (z : ℚ) := by ring
      _ = (4 : ℚ) * (x : ℚ) * (y : ℚ) * (z : ℚ) - (n : ℚ) * (y : ℚ) * (z : ℚ) := by rw [h4xq]
      _ = (n : ℚ) * ((x : ℚ) * (y : ℚ) + (y : ℚ) * (z : ℚ) + (z : ℚ) * (x : ℚ)) - (n : ℚ) * (y : ℚ) * (z : ℚ) := by rw [hcq]
      _ = (n : ℚ) * (x : ℚ) * ((y : ℚ) + (z : ℚ)) := by ring
  have hnq : (0 : ℚ) < (n : ℚ) := by positivity
  have hxq : (0 : ℚ) < (x : ℚ) := by positivity
  have hyq : (0 : ℚ) < (y : ℚ) := by positivity
  have hzq : (0 : ℚ) < (z : ℚ) := by positivity
  have hnxy : (0 : ℚ) < (n : ℚ) * (x : ℚ) * (y : ℚ) := by positivity
  have hnxz : (0 : ℚ) < (n : ℚ) * (x : ℚ) * (z : ℚ) := by positivity
  have hay_gt : (n : ℚ) * (x : ℚ) < (a : ℚ) * (y : ℚ) := by
    have h1 : (n : ℚ) * (x : ℚ) * (z : ℚ) < (a : ℚ) * (y : ℚ) * (z : ℚ) := by
      nlinarith [hkey, hnxy]
    nlinarith [h1, hzq]
  have haz_gt : (n : ℚ) * (x : ℚ) < (a : ℚ) * (z : ℚ) := by
    have h1 : (n : ℚ) * (x : ℚ) * (y : ℚ) < (a : ℚ) * (z : ℚ) * (y : ℚ) := by
      nlinarith [hkey, hnxz]
    nlinarith [h1, hyq]
  have hnx_lt_ay : n * x < a * y := by exact_mod_cast hay_gt
  have hnx_lt_az : n * x < a * z := by exact_mod_cast haz_gt
  have hd : 0 < d := by dsimp [d]; omega
  have he : 0 < e := by dsimp [e]; omega
  have hAy : a * y = d + n * x := by dsimp [d]; omega
  have hAz : a * z = e + n * x := by dsimp [e]; omega
  have hde : d * e = (n * x) * (n * x) := by
    have hAyq : (a : ℚ) * (y : ℚ) = (d : ℚ) + (n : ℚ) * (x : ℚ) := by exact_mod_cast hAy
    have hAzq : (a : ℚ) * (z : ℚ) = (e : ℚ) + (n : ℚ) * (x : ℚ) := by exact_mod_cast hAz
    have hdeq : (d : ℚ) * (e : ℚ) = (n : ℚ) * (x : ℚ) * ((n : ℚ) * (x : ℚ)) := by
      nlinarith [hAyq, hAzq, hkey]
    exact_mod_cast hdeq
  refine ⟨a, d, e, ha, hd, he, h4x, hAy, hAz, hde⟩

/-- **充分方向**：证书 ⇒ 解（由 `DivisorParam.divisor_construction` 重建 `y, z`）。 -/
lemma solvable_of_certificate {n : ℕ} (hn : 2 ≤ n) (h : HasCertificate n) : Solvable n := by
  rcases h with ⟨x, a, d, e, hx, ha, hd, he, h4x, hdvdy, hdvde, hde⟩
  let y := (d + n * x) / a
  let z := (e + n * x) / a
  have hay : a * y = d + n * x := by
    dsimp [y]
    exact Nat.mul_div_cancel' hdvdy
  have haz : a * z = e + n * x := by
    dsimp [z]
    exact Nat.mul_div_cancel' hdvde
  have hy : 0 < y := by
    dsimp [y]
    rw [Nat.div_pos_iff]
    exact ⟨ha, Nat.le_of_dvd (by omega : 0 < d + n * x) hdvdy⟩
  have hz : 0 < z := by
    dsimp [z]
    rw [Nat.div_pos_iff]
    exact ⟨ha, Nat.le_of_dvd (by omega : 0 < e + n * x) hdvde⟩
  refine ⟨x, y, z, hx, hy, hz, ?_⟩
  exact divisor_construction hn hx hy hz ha h4x hay haz hde

/-- **必要性方向**：解 ⇒ 证书。 -/
lemma certificate_of_solvable {n : ℕ} (hn : 2 ≤ n) (h : Solvable n) : HasCertificate n := by
  rcases h with ⟨x, y, z, hx, hy, hz, hxyz⟩
  rcases solution_gives_certificate hn hx hy hz hxyz with ⟨a, d, e, ha, hd, he, h4x, hAy, hAz, hde⟩
  refine ⟨x, a, d, e, hx, ha, hd, he, h4x, ⟨y, hAy.symm⟩, ⟨z, hAz.symm⟩, hde⟩

/-- **双射**：`n` 可解 ⟺ `n` 有因子证书。 -/
theorem solvable_iff_certificate (n : ℕ) (hn : 2 ≤ n) : Solvable n ↔ HasCertificate n := by
  constructor
  · exact certificate_of_solvable hn
  · exact solvable_of_certificate hn

/-- 若 `x, y` 为奇，则 `x·y + y·z + z·x` 为奇（对任意 `z`）。 -/
lemma two_odd_implies_sum_odd {x y z : ℕ} (hx : Odd x) (hy : Odd y) :
    Odd (x * y + y * z + z * x) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  use 2 * a * b + a + b + a * z + b * z + z
  ring

/-- `n` 为奇数时，任何解满足 `2 ∣ x·y + y·z + z·x`。 -/
lemma odd_solution_two_divides_pairwise_sum {n x y z : ℕ}
    (hn : 2 ≤ n) (hn_odd : Odd n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : IsDecomposition n x y z) :
    2 ∣ x * y + y * z + z * x := by
  have hcleared_nat : 4 * x * y * z = n * (x * y + y * z + z * x) := by
    have hc : IsDecompositionCleared n x y z := (isDecomposition_iff_cleared hn hx hy hz).1 h
    unfold IsDecompositionCleared at hc
    exact_mod_cast hc
  have h4dvd : 2 ∣ 4 * x * y * z := by
    use 2 * x * y * z
    ring
  have hdiv : 2 ∣ n * (x * y + y * z + z * x) := by
    rw [← hcleared_nat]
    exact h4dvd
  have hcop : Nat.Coprime 2 n := Nat.coprime_two_left.2 hn_odd
  exact hcop.dvd_of_dvd_mul_left hdiv

/-- `n` 为奇数时，任何解都不会同时有两个奇分母（即 `x, y, z` 中至多一个为奇）。 -/
lemma odd_solution_not_two_odd {n x y z : ℕ}
    (hn : 2 ≤ n) (hn_odd : Odd n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : IsDecomposition n x y z) :
    ¬ (Odd x ∧ Odd y) := by
  intro hxy
  have hS : 2 ∣ x * y + y * z + z * x := odd_solution_two_divides_pairwise_sum hn hn_odd hx hy hz h
  have hodd : Odd (x * y + y * z + z * x) := two_odd_implies_sum_odd hxy.1 hxy.2
  rcases hodd with ⟨k, hk⟩
  rcases hS with ⟨c, hc⟩
  omega

end ErdosStraus
