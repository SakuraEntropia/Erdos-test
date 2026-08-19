import ErdosTest.Theorems.MinimalCertificate

/-!
# Phase 9 — 数学工具发明：可验证的新结构（诚实分类，绝不声称猜想已解决）

本文件是「数学工具发明模式」的**可验证**交付。它**不**直接求解 Erdős–Straus 猜想，
而是考察：是否存在一个新的**数学语言 / 抽象 / 不变量 / 表示**，能把问题重新表述得更简单。
重大进展往往不来自「证明更多旧定理」，而来自「发现让旧定理变得平凡的正确概念」
（Grothendieck 的精神）。

本文件只形式化**通过了 Grothendieck 检验**（「换个名字」vs.「真正增加结构」）的对象，
全部经 `lake build` 验证、零 `sorry`。三个对象：

1. **`AstratumSolvable n a`（a-层分解）** — *有用的重构（第 4 类）*。
   把「`n` 可解」分解为「存在证书参数 `a = 4x−n` 的层可解」。`a = 3` 层正是最小证书层。
   这把此前只在计算里出现的「最小证书 `a`」变成正式定义，并使 `a=3`、`a=7` 等
   判定统一为「某个 `a`-层可解」。

2. **`divisorResidueSet M a`（除子余数集）** — *新定义（第 1 类）*。
   `M²` 的所有因子模 `a` 取得的余数集合。证书条件被压缩成一个**成员测试**：
   「目标余数 `(−M mod a)` 是否落在该集合中」。

3. **`one_sided_certificate` / `certificate_iff_one_sided`（单边除子判据）** — *新定理（第 3 类）*。
   当 `gcd(M,a)=1` 时，证书的两条同余条件 `a ∣ d+M` 与 `a ∣ e+M`（`e = M²/d`）
   **坍缩为一条** `a ∣ d+M`。这把 Agent 3 的计算观察（C1，B 注册）升级为机器验证定理，
   并统一了 `a=3`、`a=7` 及一切素 `a` 层的判定。

**诚实的底线（不变）**：以上是三个不触及六类核心的新工具；它们不蕴含、也不声称蕴含猜想。
证明只用 `ring` / `omega` / `rw` / 整除与互素的基本引理，无 `sorry`。
-/

namespace ErdosStraus

/-! ## 1. a-层分解（有用的重构） -/

/-- `a`-层可解：存在解 `(x, y, z)` 使得 `a + n = 4x`（即 `a = 4x − n` 是证书参数）。
`a = 3` 层恰好是「最小第一分母」层（`x = (n+3)/4`）。 -/
def AstratumSolvable (n a : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ a + n = 4 * x ∧ IsDecomposition n x y z

/-- `n` 可解 ⟺ 存在某个正参数 `a` 的层可解（把可解性分解为层）。 -/
theorem solvable_iff_exists_stratum {n : ℕ} (hn : 2 ≤ n) :
    Solvable n ↔ ∃ a : ℕ, 0 < a ∧ AstratumSolvable n a := by
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, hxyz⟩
    have hb : n < 4 * x := solution_bound hn hx hy hz hxyz
    refine ⟨4 * x - n, by omega, x, y, z, hx, hy, hz, by omega, hxyz⟩
  · rintro ⟨a, _ha, x, y, z, hx, hy, hz, _hax, hxyz⟩
    exact ⟨x, y, z, hx, hy, hz, hxyz⟩

/-- `a = 3` 层等价于既有定义 `A3Solvable`（最小证书层，`x = k+1`）。 -/
theorem a3_stratum_iff (k : ℕ) : AstratumSolvable (4 * k + 1) 3 ↔ A3Solvable k := by
  constructor
  · rintro ⟨x, y, z, _hx, hy, hz, hax, hxyz⟩
    have hx_eq : x = k + 1 := by omega
    subst x
    exact ⟨y, z, hy, hz, hxyz⟩
  · rintro ⟨y, z, hy, hz, hxyz⟩
    refine ⟨k + 1, y, z, by omega, hy, hz, by omega, hxyz⟩

/-! ## 2. 除子余数集（新定义）与单边除子判据（新定理） -/

/-- 除子余数集 `R(M,a)`：`M²` 的因子模 `a` 取得的余数全体。
证书条件「`∃ d,e, d·e=M² ∧ a∣d+M ∧ a∣e+M`」在 `gcd(M,a)=1` 时等价于
「目标余数 `(−M mod a)` 落在该集合中」（见 `certificate_iff_one_sided` 的右端）。 -/
def divisorResidueSet (M a : ℕ) : Set ℕ :=
  { r | ∃ d : ℕ, d ∣ M * M ∧ d % a = r }

/-- **单边除子判据（新定理，核心）**：若 `d ∣ M²` 且 `a ∣ d+M`，则补因子 `e = M²/d`
自动满足 `a ∣ e+M`（无需第二条同余）。证明：
`e(d+M) = ed + eM = M² + eM = M(e+M)`，故 `a ∣ e(d+M)` 即 `a ∣ M(e+M)`，
再由 `gcd(M,a)=1` 得 `a ∣ e+M`。 -/
theorem one_sided_certificate {M a d : ℕ} (hcop : Nat.Coprime M a)
    (hd : d ∣ M * M) (hres : a ∣ d + M) :
    a ∣ (M * M / d) + M := by
  let e := M * M / d
  have hde : d * e = M * M := Nat.mul_div_cancel' hd
  have hdem : e * (d + M) = M * (e + M) := by
    calc
      e * (d + M) = e * d + e * M := by ring
      _ = M * M + e * M := by rw [Nat.mul_comm e d, hde]
      _ = M * (e + M) := by ring
  have hdvd_dem : a ∣ e * (d + M) := dvd_mul_of_dvd_right hres e
  have hdvd_MeM : a ∣ M * (e + M) := by
    rw [← hdem]
    exact hdvd_dem
  exact hcop.symm.dvd_of_dvd_mul_left hdvd_MeM

/-- **证书坍缩（有用的重构 + 新定理）**：`gcd(M,a)=1` 时，两条同余的证书存在 ⟺
单条同余 `a ∣ d+M` 的除子存在。这统一了 `a=3`、`a=7` 及一切素 `a` 层的判定。 -/
theorem certificate_iff_one_sided {M a : ℕ} (hM : 0 < M) (hcop : Nat.Coprime M a) :
    (∃ d e : ℕ, 0 < d ∧ 0 < e ∧ d * e = M * M ∧ a ∣ d + M ∧ a ∣ e + M) ↔
      (∃ d : ℕ, 0 < d ∧ d ∣ M * M ∧ a ∣ d + M) := by
  constructor
  · rintro ⟨d, e, hdpos, _hepos, hde, hdvd, _hdve⟩
    exact ⟨d, hdpos, ⟨e, hde.symm⟩, hdvd⟩
  · rintro ⟨d, hdpos, hd, hres⟩
    let e := M * M / d
    have hde : d * e = M * M := Nat.mul_div_cancel' hd
    have he_pos : 0 < e := by
      dsimp [e]
      rw [Nat.div_pos_iff]
      exact ⟨hdpos, Nat.le_of_dvd (Nat.mul_pos hM hM) hd⟩
    have hdvd_e : a ∣ e + M := by
      simpa [e] using one_sided_certificate hcop hd hres
    exact ⟨d, e, hdpos, he_pos, hde, hres, hdvd_e⟩

end ErdosStraus
