import ErdosTest.Theorems.NewStructures
import ErdosTest.Theorems.MainResult
import ErdosTest.Theorems.Lemma2

/-!
# Phase 11 — 攻击面发现：可验证的部分定理与「除子指数盒」

本文件是 Phase 11（Attack Surface Discovery）的**可验证**交付。它**不**声称 Erdős–Straus
猜想已解决；它只把「不可约核心」里*可机器验证*的那几件事写成定理，并把难度精确地**定位**
到尚不可证的那一步。

四条定理（全部 `lake build` 验证、零 `sorry`）：

1. `solvable_of_one_sided_divisor` — **攻击面的最小形式（充分判据）**。把 Phase 9/10 的
   单边除子判据 `certificate_iff_one_sided` 打包成 `Solvable` 层的一个充分条件：只要存在
   `x, a, d` 使 `a = 4x − n > 0`、`gcd(n·x, a) = 1`、`d ∣ (n·x)²`、`a ∣ d + n·x`，则 `n` 可解。
   （必要性方向需要 `gcd = 1`，对复合 `a` 不自动成立——见 `structure_stress_test.md` 的反例。）

2. `solvable_of_exists_prime_three_mod_four` — **部分定理**。若 `n` 有素因子 `≡ 3 (mod 4)`，
   则 `n` 可解。于是「潜在反例」必须**全部**素因子 `≡ 1 (mod 4)`（结合偶 / `3∣n` 的约化，
   真正难的是只用 `≡ 1 (mod 4)` 的素数构造的 `n`）。

3. `infinitely_many_solvable` — **部分定理**。有无穷多个可解的 `n`（事实上所有 `n ≡ 3 (mod 4)`）。

4. `divisor_of_square_iff_exponent_le` — **结构定理（Track C 的骨干）**。`d ∣ M²` 当且仅当
   `d` 的每个素因子指数 ≤ `2 ·`(`M` 中该素因子的指数)。这就是「有界指数乘积集」`R(M,a)` 的
   严格数学内容：`M²` 的因子全体 = 指数盒 `[0, 2v₁] × ⋯ × [0, 2vᵣ]` 在
   `(f₁,…,fᵣ) ↦ ∏ p_i^{f_i}` 下的像。难度不在「这是什么集合」，而在「这个盒的像是否命中
   目标剩余类 `−M (mod a)`」。

**诚实的底线（不变）**：以上四条不蕴含、也不声称蕴含猜想；`solvable_of_one_sided_divisor`
的*必要性*方向（`Solvable → one-sided`）在一般 `a` 下是**假**的（`gcd` 不自动成立），所以这里
只陈述**充分**方向。证明只用 `ring` / `omega` / `rw` / 整除、互素与 `Nat.factorization` 的
基本引理，无 `sorry`。
-/

namespace ErdosStraus

/-! ## 1. 攻击面的最小形式（充分判据） -/

/-- **充分判据（Phase 9/10 单边除子判据的 `Solvable` 层包装）**。若存在 `x, a, d` 使
`a + n = 4x`、`gcd(n·x, a) = 1`、`d ∣ (n·x)²`、`a ∣ d + n·x`，则 `n` 可解。
（`M = n·x`，`d` 是 `M²` 的因子且落在剩余类 `−M (mod a)`。） -/
theorem solvable_of_one_sided_divisor {n : ℕ} (hn : 2 ≤ n) {x a d : ℕ}
    (hx : 0 < x) (ha : 0 < a) (hd : 0 < d) (hax : a + n = 4 * x)
    (hcop : Nat.Coprime (n * x) a) (hdiv : d ∣ (n * x) * (n * x)) (hres : a ∣ d + n * x) :
    Solvable n := by
  have hnpos : 0 < n := by omega
  have hM : 0 < n * x := Nat.mul_pos hnpos hx
  have hone : ∃ d e : ℕ, 0 < d ∧ 0 < e ∧ d * e = (n * x) * (n * x) ∧
      a ∣ d + n * x ∧ a ∣ e + n * x :=
    (certificate_iff_one_sided hM hcop).2 ⟨d, hd, hdiv, hres⟩
  rcases hone with ⟨d', e, hd', he, hde, hdvd, hdve⟩
  have hcert : HasCertificate n := ⟨x, a, d', e, hx, ha, hd', he, hax, hdvd, hdve, hde⟩
  exact solvable_of_certificate hn hcert

/-! ## 2. 部分定理：素因子 `≡ 3 (mod 4)` 即可解 -/

/-- **部分定理**。若 `n ≥ 2` 有素因子 `p ≡ 3 (mod 4)`，则 `n` 可解。
（证明：`p` 自身可解（`easy_classes` 的 `n % 4 = 3` 情形），再由伸缩 `scale_of_solution` 得
`n = p · (n/p)` 可解。） -/
theorem solvable_of_exists_prime_three_mod_four {n : ℕ} (hn : 2 ≤ n)
    (h : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p % 4 = 3) : Solvable n := by
  rcases h with ⟨p, hp, hpd, hp4⟩
  have hsolp : Solvable p :=
    easy_classes p (Nat.Prime.two_le hp) (Or.inr (Or.inr hp4))
  have hk : 0 < n / p := by
    rw [Nat.div_pos_iff]
    exact ⟨Nat.Prime.pos hp, Nat.le_of_dvd (by omega : 0 < n) hpd⟩
  have hscale : Solvable ((n / p) * p) :=
    scale_of_solution (Nat.Prime.two_le hp) hk hsolp
  have hn_eq' : (n / p) * p = n := by
    rw [Nat.mul_comm, Nat.mul_div_cancel' hpd]
  simpa [hn_eq'] using hscale

/-! ## 3. 部分定理：无穷多个可解的 `n` -/

/-- **部分定理**。有无穷多个可解的 `n`（事实上所有 `n ≡ 3 (mod 4)`，
由 `three_mod_four` 的参数化恒等式）。 -/
theorem infinitely_many_solvable : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Solvable n := by
  intro N
  refine ⟨4 * N + 3, by omega, N + 1, 2 * (N + 1) * (4 * N + 3), 2 * (N + 1) * (4 * N + 3),
    by positivity, by positivity, by positivity, ?_⟩
  exact three_mod_four (k := N)

/-! ## 4. 结构定理（Track C）：除子指数盒 -/

/-- **结构定理（Track C 的骨干）**。`d ∣ M²` 当且仅当 `d` 的每个素因子指数 ≤ `2 ·`（`M` 中该
素因子的指数）。这是「有界指数乘积集」`R(M,a)` 的严格内容：`M²` 的因子全体正是指数盒
`[0, 2v₁] × ⋯ × [0, 2vᵣ]` 的像。难度在盒的像是否命中目标剩余类，不在盒子本身。 -/
theorem divisor_of_square_iff_exponent_le {M d : ℕ} (hM : M ≠ 0) (hd : d ≠ 0) :
    d ∣ M * M ↔ ∀ p : ℕ, d.factorization p ≤ 2 * M.factorization p := by
  rw [← Nat.factorization_le_iff_dvd hd (mul_ne_zero hM hM)]
  have hmul (p : ℕ) : (M * M).factorization p = 2 * M.factorization p := by
    rw [Nat.factorization_mul hM hM]
    simp [two_mul]
  constructor
  · intro h p
    have hp : d.factorization p ≤ (M * M).factorization p := h p
    rw [hmul p] at hp
    exact hp
  · intro h p
    rw [hmul p]
    exact h p

end ErdosStraus
