# Phase 12 — Mordell 六类约化的形式化：模 4 → 模 12 → 模 24

> **Legend（项目注册表，不变）:** A = proven · B = computational · C = conjecture · D = AI hypothesis.
> **Honesty rule（不变）:** 本文件不声称 Erdős–Straus 猜想已解决。以下所有定理均为 **A**
> （Lean 验证，零 `sorry`，`lake build` 通过），且**绝不把「约化」说成「解决」**。

---

## 0. 这一阶段做了什么

把 `Notes/irreducible_core.md` §1 约化链条里标注为「published [A]」的前三步，从**文献引用**升级为
**本仓库 [A]**（`Theorems/Phase12.lean`，零 `sorry`）：

```
Conjecture  (∀ n ≥ 2)
   ↓ [A] reduction_to_primes                    （MainResult.lean，既有）
   ↓ [A] reduction_to_primes_one_mod_four       （Phase12，新）
   ↓ [A] reduction_to_primes_one_mod_twelve     （Phase12，新，加强）
   ↓ [A] reduction_to_primes_one_mod_twenty_four（Phase12，新，加强）
   ↓  只差素数 p ≡ 1 (mod 24)
```

**尚未完成**（诚实标注）：最后一步——从 `p ≡ 1 (mod 24)` 再约化到六类核心
`p ≡ 1, 121, 169, 289, 361, 529 (mod 840)`——需要 Mordell 的模 5 / 模 7 参数化恒等式
（约 834 个剩余类的覆盖 + CRT），是**更大、更机械**的一步，本阶段未做。

---

## 1. 新定理清单（`Theorems/Phase12.lean`，全部 **A**）

| 定理 | 陈述 | 性质 |
|---|---|---|
| `solvable_of_prime_one_mod_four_two_mod_three` | `p=4k+1` 素且 `p≡2(3)` ⟹ `Solvable p` | `a=3` 层命中（用既有 `a3_solvable_iff_two_mod_three_or_factor`） |
| `solvable_of_prime_mod_four_one_mod_three_two` | 同上，按 `p`（`p%4=1, p%3=2`）形态 | 同一事实的易用包装 |
| `reduction_to_primes_one_mod_four` | `Conjecture ↔ ∀ 素 p, p%4=1 → Solvable p` | **模 4 约化**（Mordell 第一步） |
| `reduction_to_primes_one_mod_twelve` | `Conjecture ↔ ∀ 素 p, p%12=1 → Solvable p` | **模 12 约化（加强）**：`p≡5(12)` 由 `a=3` 命中 |
| `solvable_of_five_mod_eight` | `Solvable (8k+5)` | **`n≡5(8)` 恒可解**（Mordell 恒等式 `five_mod_eight_minimal` 的包装） |
| `reduction_to_primes_one_mod_twenty_four` | `Conjecture ↔ ∀ 素 p, p%24=1 → Solvable p` | **模 24 约化（加强）**：`p≡13(24)` 即 `p≡5(8)`，恒可解 |

辅助引理（非「定理」，但亦 **A**）：`mod_four_eq_one_below_twelve`、
`mod_twenty_four_of_one_mod_twelve`（模 12 / 模 24 的有限剩余分类）。

---

## 2. 为什么这是「真正的加强」而不仅是重述

- **模 4 约化**是标准事实：`easy_classes` 已覆盖 `2∣n ∨ 3∣n ∨ n≡3(4)`，所以只剩 `p≡1(4)`。
  这一步把「published」升级为「本仓库 A」，但**内容等价**。
- **模 12 约化**是**真加强**：它额外消灭了素数 `p ≡ 5 (mod 12)`（即 `p≡1(4)` 且 `p≡2(3)`），
  用的是**本仓库自己的** `a=3` 层刻画 `a3_solvable_iff_two_mod_three_or_factor`（`p≡2(3)` ⟹
  `a=3` 可解）。这不是文献的标准约化，是本仓库 `a=3` 理论的推论。
- **模 24 约化**也是**真加强**：它额外消灭了 `p ≡ 13 (mod 24)`（即 `p≡5(8)`），用的是 Mordell 的
  `n≡5(8)` 恒等式 `five_mod_eight_minimal`。

每步都把「还需检查的素数」收紧一档：`p≡1(4)` → `p≡1(12)` → `p≡1(24)`。六类核心
`1,121,169,289,361,529 (mod 840)` 全部满足 `p≡1(24)`，所以这三步**没有**碰到六类核心本身——
它们只是把「易解的部分」在素数域上钉死得更干净。

---

## 3. 与六类核心的距离（诚实）

`p ≡ 1 (mod 24)` 之下还分两类：

```
p ≡ 1 (mod 24)：
   ├─ p ≡ 1 (mod 5) 且 p ≡ 1,2,4 (mod 7) 等「易」类  ── 模 5/7 恒等式可覆盖（未做）
   └─ p ≡ 1²,11²,13²,17²,19²,23² (mod 840)          ── 六类核心（真正的困难）
```

所以下一阶段要攻的是**模 5、模 7 的二次剩余约束**：证明当 `p` 模 5 或模 7 是**非剩余**（或落在
某些类）时，`4/p` 由 Mordell 恒等式覆盖。这一步是**可完成的、机械的**（大量有限模恒等式 + CRT），
但工作量远大于本阶段三步之和。**本阶段没有做，也不声称做了。**

---

## 4. 关键技术要点（供后续阶段复用）

- Lean 4 v4.33.0 的 `omega` **已原生支持 `Nat.div` / `Nat.mod`**（对有限有界剩余分类直接 `omega`
  即可，无需手写枚举）。本阶段的 `mod_twenty_four_of_one_mod_twelve` 即靠 `omega` 一步完成。
- 模的「降模」用 `Nat.mod_mod_of_dvd a (h : c ∣ b) : a % b % c = a % c`；升模反向用 `←`。
- 素数模分类的「排除」用 `(Nat.dvd_prime hp).mp h : m=1 ∨ m=p`（`h : m∣p`）。
- `Conjecture` 的约化链用 `reduction_to_*  .mpr` 层层套用，与 `irreducible_core.md` 的箭头一一对应。

---

## 5. 结论

本阶段交付了 **6 条 A 级定理**（模 4 / 模 12 / 模 24 三层约化 + `n≡5(8)` 恒可解），把 Mordell
约化的**前三步**从文献升级为本仓库的机器验证定理。这是诚实、确定、非平凡的一步：它把猜想钉死到
「素 `p ≡ 1 (mod 24)`」，但**六类核心仍未触及**——那是下一步（模 5/7 恒等式 + CRT）的工作。

*不声称 Erdős–Straus 猜想已解决；本文件只精确记录「约化做到哪一步」。*
