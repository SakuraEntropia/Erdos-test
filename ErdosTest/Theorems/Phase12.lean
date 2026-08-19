import ErdosTest.Theorems.NewStructures
import ErdosTest.Theorems.MainResult
import ErdosTest.Theorems.Lemma2
import ErdosTest.Theorems.Lemma1
import ErdosTest.Theorems.A3Characterization
import ErdosTest.Theorems.ACases

/-!
# Phase 12 — Mordell 六类约化的第一步：模 4 与模 12 约化

本文件把 `Notes/irreducible_core.md` 里标注为「published [A]」的约化链条的前两步升级为
**本仓库 [A]**（`sorry`-free，`lake build` 验证）：

```
Conjecture  (∀ n ≥ 2)
   ↓ [A] reduction_to_primes              （MainResult.lean，已验）
   ↓ [A] reduction_to_primes_one_mod_four （本文件）
   ↓ [A] reduction_to_primes_one_mod_twelve（本文件，用 a=3 层加强）
   ↓  只差素数 p ≡ 1 (mod 12)
```

`reduction_to_primes_one_mod_twelve` 是一个**真正的加强**：它把「只需 p ≡ 1 (mod 4)」进一步
收紧为「只需 p ≡ 1 (mod 12)」，因为素数 `p ≡ 5 (mod 12)`（即 `p ≡ 1 (mod 4)` 且
`p ≡ 2 (mod 3)`）由本仓库自己的 `a=3` 层刻画 `a3_solvable_iff_two_mod_three_or_factor` 直接命中。

**不声称解决 Erdős–Straus 猜想**：这只是把「还差什么」钉得更死。六类核心
`p ≡ 1, 121, 169, 289, 361, 529 (mod 840)` 仍未触及（这是后续阶段的约化对象）。

-/

namespace ErdosStraus

/-! ## 1. `a = 3` 层命中：素数 `p ≡ 1 (mod 4)` 且 `p ≡ 2 (mod 3)`（即 `p ≡ 5 (mod 12)`）可解 -/

/-- 素数 `p = 4k+1` 且 `p ≡ 2 (mod 3)` 时可解：`a = 3` 层直接命中。
这是 `a3_solvable_iff_two_mod_three_or_factor` 的第一个析取支在 `Solvable` 层的包装。 -/
theorem solvable_of_prime_one_mod_four_two_mod_three {k : ℕ} (hk : 1 ≤ k)
    (hp : (4 * k + 1).Prime) (hp3 : (4 * k + 1) % 3 = 2) : Solvable (4 * k + 1) := by
  have ha3 : A3Solvable k := (a3_solvable_iff_two_mod_three_or_factor k hk hp).2 (Or.inl hp3)
  have hstratum : AstratumSolvable (4 * k + 1) 3 := (a3_stratum_iff k).2 ha3
  rcases hstratum with ⟨x, y, z, hx, hy, hz, _hax, hxyz⟩
  exact ⟨x, y, z, hx, hy, hz, hxyz⟩

/-- `p ≡ 1 (mod 4)` 且 `p ≡ 2 (mod 3)` 的素数可解（把上式写成按 `p` 而非 `k` 的形态）。 -/
theorem solvable_of_prime_mod_four_one_mod_three_two {p : ℕ} (hp : Nat.Prime p)
    (hp4 : p % 4 = 1) (hp3 : p % 3 = 2) : Solvable p := by
  have hp_eq : p = 4 * (p / 4) + 1 := by
    have h := Nat.mod_add_div p 4
    rw [hp4] at h
    omega
  have hk : 1 ≤ p / 4 := by
    rw [Nat.succ_le_iff, Nat.div_pos_iff]
    constructor
    · norm_num
    · by_cases hple3 : p ≤ 3
      · have hp2 : 2 ≤ p := Nat.Prime.two_le hp
        have hpeq : p = 2 ∨ p = 3 := by omega
        rcases hpeq with h2 | h3 <;> subst p <;> norm_num at hp4
      · omega
  have hs : Solvable (4 * (p / 4) + 1) :=
    solvable_of_prime_one_mod_four_two_mod_three hk (hp_eq ▸ hp) (hp_eq ▸ hp3)
  exact hp_eq.symm ▸ hs

/-! ## 2. 模 4 约化 -/

/-- **模 4 约化（Mordell 第一步，本仓库 [A]）**：猜想等价于其对所有 `p ≡ 1 (mod 4)` 的素数
成立。其余素数 `p`：`p = 2` 有解，奇素数 `p ≡ 3 (mod 4)` 由 `easy_classes` 覆盖。 -/
theorem reduction_to_primes_one_mod_four :
    Conjecture ↔ ∀ p : ℕ, Nat.Prime p → p % 4 = 1 → Solvable p := by
  rw [reduction_to_primes]
  constructor
  · intro hP p hp hp4
    exact hP p hp
  · intro hP p hp
    rcases hp.eq_two_or_odd with h2 | hodd
    · subst p
      exact two_has_solution
    · rcases (Nat.odd_mod_four_iff.mp hodd) with hp1 | hp3
      · exact hP p hp hp1
      · exact easy_classes p (Nat.Prime.two_le hp) (Or.inr (Or.inr hp3))

/-! ## 3. 模 12 约化（用 `a = 3` 层加强） -/

/-- 若 `r < 12` 且 `r ≡ 1 (mod 4)`，则 `r ∈ {1, 5, 9}`。有限枚举。 -/
lemma mod_four_eq_one_below_twelve {r : ℕ} (hlt : r < 12) (h4 : r % 4 = 1) :
    r = 1 ∨ r = 5 ∨ r = 9 := by
  have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨
      r = 9 ∨ r = 10 ∨ r = 11 := by omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num at h4
  · left; norm_num
  · norm_num at h4
  · norm_num at h4
  · norm_num at h4
  · right; left; norm_num
  · norm_num at h4
  · norm_num at h4
  · norm_num at h4
  · right; right; norm_num
  · norm_num at h4
  · norm_num at h4

/-- 素数 `p ≡ 1 (mod 4)` 时，`p mod 12` 只能是 `1` 或 `5`（`9` 会导致 `3 ∣ p`，与素性矛盾）。 -/
lemma prime_mod_twelve_of_one_mod_four {p : ℕ} (hp : Nat.Prime p) (hp4 : p % 4 = 1) :
    p % 12 = 1 ∨ p % 12 = 5 := by
  have hlt : p % 12 < 12 := Nat.mod_lt p (by norm_num)
  have hmod4 : (p % 12) % 4 = 1 := by
    rw [Nat.mod_mod_of_dvd p (by norm_num : 4 ∣ 12)]
    exact hp4
  rcases mod_four_eq_one_below_twelve hlt hmod4 with h1 | h5 | h9
  · exact Or.inl h1
  · exact Or.inr h5
  · exfalso
    have hp30 : p % 3 = 0 := by
      rw [← Nat.mod_mod_of_dvd p (by norm_num : 3 ∣ 12), h9]
    have h3dvd : 3 ∣ p := (Nat.dvd_iff_mod_eq_zero).mpr hp30
    have h3 : 3 = 1 ∨ 3 = p := (Nat.dvd_prime hp).mp h3dvd
    rcases h3 with h31 | h3p
    · norm_num at h31
    · subst p
      norm_num at hp4

/-- **模 12 约化（本仓库 [A]，加强版）**：猜想等价于其对所有 `p ≡ 1 (mod 12)` 的素数成立。
素数 `p ≡ 5 (mod 12)`（`p ≡ 1 (mod 4)` 且 `p ≡ 2 (mod 3)`）由 `a = 3` 层命中，无需假设。 -/
theorem reduction_to_primes_one_mod_twelve :
    Conjecture ↔ ∀ p : ℕ, Nat.Prime p → p % 12 = 1 → Solvable p := by
  constructor
  · intro hC p hp hp12
    exact hC p (Nat.Prime.two_le hp)
  · intro hP
    apply reduction_to_primes_one_mod_four.mpr
    intro p hp hp4
    rcases prime_mod_twelve_of_one_mod_four hp hp4 with h1 | h5
    · exact hP p hp h1
    · have hp3 : p % 3 = 2 := by
        rw [← Nat.mod_mod_of_dvd p (by norm_num : 3 ∣ 12), h5]
      exact solvable_of_prime_mod_four_one_mod_three_two hp hp4 hp3

/-! ## 4. 模 24 约化（用 `n ≡ 5 (mod 8)` 恒等式加强） -/

/-- `n ≡ 5 (mod 8)` 时恒可解：`five_mod_eight_minimal`（Mordell 恒等式）给出的显式解
`(2k+2, (8k+5)(k+1), 2(8k+5)(k+1))`。这是 `Solvable` 层的包装。 -/
theorem solvable_of_five_mod_eight {k : ℕ} : Solvable (8 * k + 5) := by
  refine ⟨2 * k + 2, (8 * k + 5) * (k + 1), 2 * ((8 * k + 5) * (k + 1)),
    by positivity, by positivity, by positivity, ?_⟩
  exact five_mod_eight_minimal (k := k)

/-- `p ≡ 1 (mod 12)` 时，`p mod 24` 只能是 `1` 或 `13`（`(p%24) % 12 = 1` 且 `p%24 < 24`）。 -/
lemma mod_twenty_four_of_one_mod_twelve {p : ℕ} (hp12 : p % 12 = 1) :
    p % 24 = 1 ∨ p % 24 = 13 := by
  have hlt : p % 24 < 24 := Nat.mod_lt p (by norm_num)
  have hmod12 : (p % 24) % 12 = 1 := by
    rw [Nat.mod_mod_of_dvd p (by norm_num : 12 ∣ 24)]
    exact hp12
  omega

/-- **模 24 约化（本仓库 [A]）**：猜想等价于其对所有 `p ≡ 1 (mod 24)` 的素数成立。
素数 `p ≡ 13 (mod 24)`（即 `p ≡ 5 (mod 8)`）由 `n ≡ 5 (mod 8)` 恒等式覆盖，无需假设。 -/
theorem reduction_to_primes_one_mod_twenty_four :
    Conjecture ↔ ∀ p : ℕ, Nat.Prime p → p % 24 = 1 → Solvable p := by
  constructor
  · intro hC p hp hp24
    exact hC p (Nat.Prime.two_le hp)
  · intro hP
    apply reduction_to_primes_one_mod_twelve.mpr
    intro p hp hp12
    rcases mod_twenty_four_of_one_mod_twelve hp12 with h1 | h13
    · exact hP p hp h1
    · have hp8 : p % 8 = 5 := by
        rw [← Nat.mod_mod_of_dvd p (by norm_num : 8 ∣ 24), h13]
      have hp_eq : p = 8 * (p / 8) + 5 := by
        have h := Nat.mod_add_div p 8
        rw [hp8] at h
        omega
      have hs : Solvable (8 * (p / 8) + 5) := solvable_of_five_mod_eight (k := p / 8)
      exact hp_eq.symm ▸ hs

end ErdosStraus
