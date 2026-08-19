import Mathlib

/-!
# 简单示例：Lean 4 + Mathlib

这个文件演示了 Lean 的基础用法：定义、求值，以及用不同策略（tactic）做证明。
-/

namespace ErdosTest

-- 递归定义：斐波那契数列
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

-- 平方和：0^2 + 1^2 + ... + (n-1)^2
def sumSquares (n : Nat) : Nat :=
  (Finset.range n).sum fun k => k * k

-- 用 `ring` 证明平方差公式 (a+b)(a-b) = a² - b²
theorem square_diff (a b : Int) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

-- 用 `omega` 证明线性算术：n + 3 = 10 推出 n = 7
theorem three_plus_seven (n : Nat) (h : n + 3 = 10) : n = 7 := by
  omega

-- 用归纳法证明 n + 0 = n
theorem add_zero (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.succ_add, ih]

-- 用 `decide` 证明 7 是素数
theorem seven_is_prime : Nat.Prime 7 := by
  decide

end ErdosTest

-- 直接求值查看结果
#eval ErdosTest.fib 10        -- 55
#eval ErdosTest.sumSquares 10 -- 285
