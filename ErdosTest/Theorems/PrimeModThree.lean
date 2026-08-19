import ErdosTest.Theorems.ErdosProblem

/-!
# 模 3 的素因子刻画：`a = 3` 证书的“缺失基础设施”

本文件给出 `MinimalCertificate.lean` 中 `a3_iff_divisor` 叙述里一直缺失的**素因子方向**
（即任务书里的目标 (A)）：一个数 `M` 是否有因子 `d ∣ M²` 且 `d ≡ 2 (mod 3)`，等价于 `M`
是否有素因子 `≡ 2 (mod 3)`。

具体结果：

1. `mul_mod_three_eq_two`：若 `(a·b) % 3 = 2`，则 `a % 3 = 2` 或 `b % 3 = 2`
   （在 `ℤ/3` 中 `2 = −1`，两个非零元乘积为 `−1` 当且仅当恰有一个因子为 `−1`）。
2. `prime_factor_two_mod_three`：**核心引理**。若 `n % 3 = 2`，则存在素数 `p ∣ n`
   且 `p % 3 = 2`。证明用对 `n` 的强归纳：素数情形取 `p = n`；合数情形把 `n = a·b`
   分解为两个真因子，由 `mul_mod_three_eq_two` 归约到某个真因子，再用归纳假设。
   （这是「若所有素因子都 ≡ 1 (mod 3) 则 n ≡ 1 (mod 3)」的对偶命题。）
3. `divisor_two_mod_three_iff`：**主定理**（目标 (A) 的干净形式）。`(∃ d, d ∣ M² ∧ d % 3 = 2)
   ↔ (∃ q, q.Prime ∧ q ∣ M ∧ q % 3 = 2)`。
   - 正向：由 `prime_factor_two_mod_three` 取 `d` 的素因子 `p`，再由 `p ∣ d ∣ M²` 与
     素数的 `p ∣ M² ⇒ p ∣ M`（`Nat.Prime.dvd_of_dvd_pow`）得到 `p ∣ M`。
   - 反向：取 `d = q`（`q ∣ M ⇒ q ∣ M²`）。
4. `divisor_two_mod_three_iff_of_not_three_dvd`：任务原话中带 `3 ∤ M` 假设的版本，
   是上面主定理的直接推论（该假设实际不需要）。

结合 `MinimalCertificate.a3_iff_divisor`：`a = 3` 证书的存在性 ⇔ 存在 `d ∣ ((4k+1)(k+1))²`
且 `d ≡ 2 (mod 3)` ⇔ `(4k+1)(k+1)` 有素因子 `≡ 2 (mod 3)`。这正是
`Experiments/certificate_conjectures.py` 观察到的「`a = 3` 有解 ⟺ `M` 有素因子 `≡ 2 (mod 3)`」
的机器验证证明（在 `M ≡ 1 (mod 3)` 的情形下成立，见文件尾注记）。

证明所用基础设施：`Nat.exists_dvd_of_not_prime`、`Nat.Prime.dvd_of_dvd_pow`、
`Nat.mod_add_div`、`Nat.mul_mod`、`Nat.div_lt_self`，以及有限情形分析 `interval_cases`。
不用 `sorry`。
-/

namespace ErdosStraus

/-- `(a·b) % 3 = 2 ⇒ a % 3 = 2 ∨ b % 3 = 2`：模 3 的乘积为 `2`（即 `−1`）当且仅当恰一个因子为 `2`。 -/
lemma mul_mod_three_eq_two {a b : ℕ} (h : (a * b) % 3 = 2) : a % 3 = 2 ∨ b % 3 = 2 := by
  have hab : (a % 3 * b % 3) % 3 = 2 := by
    simpa [Nat.mul_mod] using h
  have ha : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hb : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
  all_goals simp [ha, hb] at hab ⊢

/-- **核心引理**：若 `n % 3 = 2`，则存在素数 `p ∣ n` 且 `p % 3 = 2`。 -/
lemma prime_factor_two_mod_three {n : ℕ} (hn : n % 3 = 2) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p % 3 = 2 := by
  have hstep : ∀ m, (∀ k, k < m → k % 3 = 2 → ∃ p : ℕ, p.Prime ∧ p ∣ k ∧ p % 3 = 2) →
      (m % 3 = 2 → ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ p % 3 = 2) := by
    intro m ih hm
    by_cases hprime : Nat.Prime m
    · exact ⟨m, hprime, dvd_rfl, hm⟩
    · have hm_eq : m = 3 * (m / 3) + 2 := by
        have hdiv : m % 3 + 3 * (m / 3) = m := Nat.mod_add_div m 3
        rw [hm] at hdiv
        omega
      have hm2 : 2 ≤ m := by omega
      rcases Nat.exists_dvd_of_not_prime hm2 hprime with ⟨a, ha_dvd, ha_ne1, ha_ne_m⟩
      have ha_pos : 0 < a := Nat.pos_of_dvd_of_pos ha_dvd (by omega : 0 < m)
      have ha_gt1 : 1 < a := by omega
      have ha_le : a ≤ m := Nat.le_of_dvd (by omega : 0 < m) ha_dvd
      have ha_lt_m : a < m := Nat.lt_of_le_of_ne ha_le ha_ne_m
      let b := m / a
      have hab_mul : a * b = m := Nat.mul_div_cancel' ha_dvd
      have hb_lt_m : b < m := by
        dsimp [b]
        exact Nat.div_lt_self (by omega : 0 < m) ha_gt1
      have hmod : (a * b) % 3 = 2 := by
        rw [hab_mul]
        exact hm
      rcases mul_mod_three_eq_two hmod with (ha3 | hb3)
      · rcases ih a ha_lt_m ha3 with ⟨p, hp, hpa, hp3⟩
        exact ⟨p, hp, dvd_trans hpa ha_dvd, hp3⟩
      · rcases ih b hb_lt_m hb3 with ⟨p, hp, hpb, hp3⟩
        have hb_dvd : b ∣ m := ⟨a, by simpa [Nat.mul_comm] using hab_mul.symm⟩
        exact ⟨p, hp, dvd_trans hpb hb_dvd, hp3⟩
  exact Nat.strong_induction_on
    (p := fun m => m % 3 = 2 → ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ p % 3 = 2)
    n hstep hn

/-- **主定理（目标 A 的干净形式）**：`M` 有因子 `d ∣ M²` 且 `d ≡ 2 (mod 3)`
当且仅当 `M` 有素因子 `q` 且 `q ≡ 2 (mod 3)`。 -/
theorem divisor_two_mod_three_iff {M : ℕ} :
    (∃ d : ℕ, d ∣ M * M ∧ d % 3 = 2) ↔ (∃ q : ℕ, q.Prime ∧ q ∣ M ∧ q % 3 = 2) := by
  constructor
  · intro h
    rcases h with ⟨d, hd, hd3⟩
    rcases prime_factor_two_mod_three hd3 with ⟨p, hp, hpd, hp3⟩
    have hpMM : p ∣ M * M := dvd_trans hpd hd
    have hpM : p ∣ M := hp.dvd_of_dvd_pow (m := M) (n := 2) (by simpa [pow_two] using hpMM)
    exact ⟨p, hp, hpM, hp3⟩
  · intro h
    rcases h with ⟨q, hq, hqd, hq3⟩
    exact ⟨q, dvd_trans hqd (dvd_mul_right M M), hq3⟩

/-- 任务原话的版本：`3 ∤ M` 假设下结论同样成立（该假设实际上不需要，见主定理）。 -/
theorem divisor_two_mod_three_iff_of_not_three_dvd {M : ℕ} (_hM : ¬ 3 ∣ M) :
    (∃ d : ℕ, d ∣ M * M ∧ d % 3 = 2) ↔ (∃ q : ℕ, q.Prime ∧ q ∣ M ∧ q % 3 = 2) :=
  divisor_two_mod_three_iff

end ErdosStraus

/-!
# 记录：本文件之外的尝试、失败与缺失基础设施

## 已证明（无 `sorry`）
- `mul_mod_three_eq_two`、`prime_factor_two_mod_three`、`divisor_two_mod_three_iff`、
  `divisor_two_mod_three_iff_of_not_three_dvd`。

## 尝试过但放弃/绕开的路线
1. **用 `Nat.factors` / `Nat.factorization` / `Nat.mem_factors` + `ZMod 3` 直证**
   （任务书建议的路线）。思路：`n.factors.prod = n`，把 `n % 3 = 2` 读作
   `(n : ZMod 3) = 2`，再证「若所有素因子都 ≠ 2（mod 3）则乘积 = 1」的矛盾。**障碍**：
   Mathlib 缺乏把 `List.prod (Nat.factors n)` 的模 3 余数与每个因子模 3 余数一步相连的
   现成引理（需要 `List.prod_hom` + `ZMod` 手工搭桥，或对 `Nat.factors` 的递归定义做
   归纳，且 `Nat.factors` 是 `List ℕ` 需处理 `List.prod` 的 `simp` 规约）。**解决**：改用
   对 `n` 的强归纳 + `mul_mod_three_eq_two`，证明更短且完全绕开因子列表 API。
2. **把 `A3Certificate` 与「`∃ d, d ∣ M² ∧ d % 3 = 2`」无条件地等价**（`a = 3` 故事的最后
   一步）。**障碍**：`A3Certificate` 的条件是 `3 ∣ d + M` 与 `3 ∣ e + M`，即
   `d ≡ e ≡ −M (mod 3)`。要把它读成 `d ≡ 2 (mod 3)` 需要 `M ≡ 1 (mod 3)`（`−1 ≡ 2`）；
   若 `M ≡ 0` 或 `2 (mod 3)` 则判据变成别的余数。故这一步**需要**假设 `M % 3 = 1`
   （等价于 `(4k+1)(k+1) % 3 = 1`），不能无条件写。本文件不提供这个带额外假设的版本，
   以免与 `a3_iff_divisor` 的余数讨论混淆；正确的无条件桥梁就是 `divisor_two_mod_three_iff`。

## 缺失的 Mathlib 基础设施（确认为缺口）
- 没有「`List.prod (Nat.factors n) % m` 与各因子 `% m` 直接相连」的 `simp`/`ring_nf` 友好
  引理（上文 1）。
- `omega` 不直接支持 `%`；处理 `n % 3 = 2` 的蕴含需先经 `Nat.mod_add_div` 化成线性等式
  `n = 3·(n/3) + 2`（上文 `prime_factor_two_mod_three` 的 `hm_eq` 处）。

以上为诚实记录；正式交付（无 `sorry`）是上述四条定理。
-/
