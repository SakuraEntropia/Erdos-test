import ErdosTest.Theorems.MinimalCertificate
import ErdosTest.Theorems.PrimeModThree

/-!
# `a = 3` 最小证书的完全素因子刻画（补上 referee 指出的缺失方向）

本文件把「`a = 3` 可解」这个最小证书条件彻底约化为一个**素因子条件**，从而把
`Experiments/*.py` 里只有计算证据（register B）的观察升级为机器验证定理（register A）。

关键桥梁（此前缺失、被 referee 记为 register violation 的正是这一步）：

  `A3Solvable k  ↔  A3Certificate k`                  （`a3_iff_divisor`）
  `A3Certificate k  ↔  ∃ d, d ∣ ((4k+1)(k+1))² ∧ d % 3 = 2`   （本文件，需 (4k+1) 素数）
  `(∃ d, d ∣ M² ∧ d % 3 = 2) ↔ (∃ q, q.Prime ∧ q ∣ M ∧ q % 3 = 2)`  （`divisor_two_mod_three_iff`）

中间那条的要点是：对素数 `p = 4k+1`（从而 `p ≠ 3`），`M = p·(k+1)` 满足 `M ≡ 1 (mod 3)`，
于是 `3 ∣ d+M` 读作 `d ≡ −M ≡ 2 (mod 3)`，而 `d % 3 = 2` 反过来也给出 `3 ∣ d+M`。

主定理（register A）：

  `a3_solvable_iff_prime_factor`：对素数 `p = 4k+1`，`a = 3` 可解 ⟺
  `M = p(p+3)/4` 有素因子 `≡ 2 (mod 3)`。

  再加上 `prime_dvd_mul_two_mod_three_iff` 的拆分，得到 `Experiments` 里观察的精确形式：
  `a = 3` 可解 ⟺ `p ≡ 2 (mod 3)` 或 `(p+3)/4` 有素因子 `≡ 2 (mod 3)`。

不声称猜想成立。证明只用 `omega` / `norm_num` / 模 3 的有限情形分析，不用 `sorry`。
-/

namespace ErdosStraus

/-! ## 1. 模 3 的有限情形小引理 -/

/-- 若 `3 ∣ d + M` 且 `M ≡ 1 (mod 3)`，则 `d ≡ 2 (mod 3)`。 -/
lemma mod_three_eq_two_of_add_dvd {d M : ℕ} (hM : M % 3 = 1) (h : 3 ∣ d + M) : d % 3 = 2 := by
  have hmod : (d + M) % 3 = 0 := (Nat.dvd_iff_mod_eq_zero).mp h
  have hadd : (d % 3 + M % 3) % 3 = 0 := by
    simpa [Nat.add_mod] using hmod
  rw [hM] at hadd
  have hlt : d % 3 < 3 := Nat.mod_lt d (by norm_num)
  have hd3 : d % 3 = 0 ∨ d % 3 = 1 ∨ d % 3 = 2 := by omega
  rcases hd3 with h0 | h1 | h2
  · rw [h0] at hadd; norm_num at hadd
  · rw [h1] at hadd; norm_num at hadd
  · exact h2

/-- 若 `d ≡ 2 (mod 3)` 且 `(d * e) ≡ 1 (mod 3)`，则 `e ≡ 2 (mod 3)`（`2 · 2 = 4 ≡ 1`）。 -/
lemma mod_three_eq_two_of_mul_mod {d e : ℕ} (hd : d % 3 = 2) (h : (d * e) % 3 = 1) : e % 3 = 2 := by
  have hmul : ((d % 3) * (e % 3)) % 3 = 1 := by
    simpa [Nat.mul_mod] using h
  rw [hd] at hmul
  have hlt : e % 3 < 3 := Nat.mod_lt e (by norm_num)
  have he3 : e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2 := by omega
  rcases he3 with h0 | h1 | h2
  · rw [h0] at hmul; norm_num at hmul
  · rw [h1] at hmul; norm_num at hmul
  · exact h2

/-- 若 `M ≡ 1 (mod 3)` 且 `d ≡ 2 (mod 3)`，则 `3 ∣ d + M`（`2 + 1 = 3 ≡ 0`）。 -/
lemma dvd_add_mod_three_of_eq_two {d M : ℕ} (hM : M % 3 = 1) (hd : d % 3 = 2) : 3 ∣ d + M := by
  have hadd : (d % 3 + M % 3) % 3 = 0 := by simp [hd, hM]
  have hmod : (d + M) % 3 = 0 := by
    simpa [Nat.add_mod] using hadd
  exact (Nat.dvd_iff_mod_eq_zero).mpr hmod

/-! ## 2. 对素数 `p = 4k+1`，`M = p·(k+1) ≡ 1 (mod 3)` -/

/-- 若 `4k+1` 是素数，则 `3 ∤ 4k+1`（因为 `4k+1 = 3` 无自然数解）。 -/
lemma not_three_dvd_fourk1_of_prime {k : ℕ} (hp : (4 * k + 1).Prime) :
    ¬ 3 ∣ 4 * k + 1 := by
  intro h
  have h3 : 3 = 1 ∨ 3 = 4 * k + 1 := (Nat.dvd_prime hp).mp h
  rcases h3 with h31 | h3p
  · norm_num at h31
  · omega

/-- 对素数 `p = 4k+1`，`M = (4k+1)(k+1) ≡ 1 (mod 3)`（`p` 素性自动排除 `k = 0`）。 -/
lemma M_mod_three_eq_one {k : ℕ} (hp : (4 * k + 1).Prime) :
    ((4 * k + 1) * (k + 1)) % 3 = 1 := by
  have hnd2 : ¬ 3 ∣ k + 1 := by
    intro h
    exact not_three_dvd_fourk1_of_prime hp ((three_dvd_4k1_iff_three_dvd_k1 k).2 h)
  -- 4k+1 ≡ k+1 (mod 3)，故 M ≡ (k+1)^2 (mod 3)
  have hcong : (4 * k + 1) % 3 = (k + 1) % 3 := by
    rw [show 4 * k + 1 = (k + 1) + 3 * k by ring]
    rw [Nat.add_mul_mod_self_left]
  have hk1 : (k + 1) % 3 = 1 ∨ (k + 1) % 3 = 2 := by
    have hlt : (k + 1) % 3 < 3 := Nat.mod_lt (k + 1) (by norm_num)
    have hne : (k + 1) % 3 ≠ 0 := by
      intro hz
      exact hnd2 ((Nat.dvd_iff_mod_eq_zero).mpr hz)
    omega
  rw [Nat.mul_mod]
  rw [hcong]
  rcases hk1 with r1 | r2
  · norm_num [r1]
  · norm_num [r2]

/-! ## 3. 证书 ⟺ 单个模 3 除子条件 -/

/-- **桥梁**：对素数 `p = 4k+1`，`a = 3` 证书存在 ⟺ `M²` 有因子 `d ≡ 2 (mod 3)`。 -/
lemma a3_certificate_iff_divisor_two_mod_three {k : ℕ} (hp : (4 * k + 1).Prime) :
    A3Certificate k ↔ ∃ d : ℕ, d ∣ ((4 * k + 1) * (k + 1)) * ((4 * k + 1) * (k + 1)) ∧ d % 3 = 2 := by
  have hM : ((4 * k + 1) * (k + 1)) % 3 = 1 := M_mod_three_eq_one hp
  constructor
  · rintro ⟨d, e, hd, he, hde, h3d, h3e⟩
    refine ⟨d, ⟨e, hde.symm⟩, mod_three_eq_two_of_add_dvd hM h3d⟩
  · rintro ⟨d, hdM, hd3⟩
    rcases hdM with ⟨e, he⟩
    have hde : d * e = ((4 * k + 1) * (k + 1)) * ((4 * k + 1) * (k + 1)) := he.symm
    have hMpos : 0 < (4 * k + 1) * (k + 1) := by positivity
    have hd_pos : 0 < d := by
      by_contra hneg
      have hd0 : d = 0 := by omega
      rw [hd0] at hd3; norm_num at hd3
    have he_pos : 0 < e := by
      by_contra hneg
      have he0 : e = 0 := by omega
      have hMsq0 : ((4 * k + 1) * (k + 1)) * ((4 * k + 1) * (k + 1)) = 0 := by
        simp [← hde, he0]
      have hM0 : (4 * k + 1) * (k + 1) = 0 := by
        rcases Nat.mul_eq_zero.mp hMsq0 with h | h <;> exact h
      omega
    have hMsq : (((4 * k + 1) * (k + 1)) * ((4 * k + 1) * (k + 1))) % 3 = 1 := by
      simp [Nat.mul_mod, hM]
    have hde_mod : (d * e) % 3 = 1 := by
      simpa [hde] using hMsq
    have he3 : e % 3 = 2 := mod_three_eq_two_of_mul_mod hd3 hde_mod
    exact ⟨d, e, hd_pos, he_pos, hde, dvd_add_mod_three_of_eq_two hM hd3,
      dvd_add_mod_three_of_eq_two hM he3⟩

/-! ## 4. 主定理：`a = 3` 可解 ⟺ 素因子条件 -/

/-- **主定理**：对素数 `p = 4k+1`（`k ≥ 1`），`a = 3` 可解 ⟺ `M = p(p+3)/4` 有素因子 `≡ 2 (mod 3)`。 -/
theorem a3_solvable_iff_prime_factor (k : ℕ) (hk : 1 ≤ k) (hp : (4 * k + 1).Prime) :
    A3Solvable k ↔ ∃ q : ℕ, q.Prime ∧ q ∣ (4 * k + 1) * (k + 1) ∧ q % 3 = 2 := by
  rw [a3_iff_divisor k hk]
  rw [a3_certificate_iff_divisor_two_mod_three hp]
  exact divisor_two_mod_three_iff

/-- **拆分**：`M = p·(k+1)` 有素因子 `≡ 2 (mod 3)` ⟺ `p ≡ 2 (mod 3)` 或 `(p+3)/4 = k+1` 有素因子 `≡ 2 (mod 3)`。 -/
lemma prime_dvd_mul_two_mod_three_iff {k : ℕ} (hp : (4 * k + 1).Prime) :
    (∃ q : ℕ, q.Prime ∧ q ∣ (4 * k + 1) * (k + 1) ∧ q % 3 = 2) ↔
      ((4 * k + 1) % 3 = 2 ∨ ∃ q : ℕ, q.Prime ∧ q ∣ (k + 1) ∧ q % 3 = 2) := by
  constructor
  · rintro ⟨q, hq, hqd, hq3⟩
    rcases hq.dvd_mul.mp hqd with hq1 | hq2
    · left
      have hqeq : q = 4 * k + 1 := by
        rcases (Nat.dvd_prime hp).mp hq1 with hqeq1 | hqeqp
        · exact (hq.ne_one hqeq1).elim
        · exact hqeqp
      rwa [← hqeq]
    · right
      exact ⟨q, hq, hq2, hq3⟩
  · rintro (h1 | h2)
    · refine ⟨4 * k + 1, hp, dvd_mul_right (4 * k + 1) (k + 1), h1⟩
    · rcases h2 with ⟨q, hq, hqd, hq3⟩
      exact ⟨q, hq, dvd_mul_of_dvd_right hqd (4 * k + 1), hq3⟩

/-- **最终形式（与 `Experiments` 观察一致）**：对素数 `p = 4k+1`，`a = 3` 可解 ⟺
`p ≡ 2 (mod 3)` 或 `(p+3)/4` 有素因子 `≡ 2 (mod 3)`。 -/
theorem a3_solvable_iff_two_mod_three_or_factor (k : ℕ) (hk : 1 ≤ k) (hp : (4 * k + 1).Prime) :
    A3Solvable k ↔
      ((4 * k + 1) % 3 = 2 ∨ ∃ q : ℕ, q.Prime ∧ q ∣ (k + 1) ∧ q % 3 = 2) := by
  rw [a3_solvable_iff_prime_factor k hk hp]
  exact prime_dvd_mul_two_mod_three_iff hp

end ErdosStraus
