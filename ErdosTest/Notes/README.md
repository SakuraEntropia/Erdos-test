# 研究笔记（Research Notebook）

> 目标：用形式数学 + 计算实验，研究一个 **Erdős 开放问题**。

## 待研究的问题

- **问题陈述**：（待填写 —— 选定具体问题后补充，包括精确表述与已知边界）
- **文献 / 来源**：（待填写 —— 论文、MathOverflow、OEIS 等）
- **当前已知的最佳结果**：（待填写）

## 记录分类

严格区分以下四类，且**只有第 4 类**能宣称“已证明”：

1. **已知数学（known mathematics）**
   - 已被社区证明、且本仓库未重新形式化的结果。

2. **实验观察（experimental observations）**
   - 来自 `ErdosTest/Experiments/` 的计算结果，仅对已枚举的有限范围成立。

3. **猜想（conjectures）**
   - 尚未证明、也无反例的陈述。注明提出动机（来自哪些观察）。

4. **形式化验证结果（formally verified results）**
   - 在 `ErdosTest/Theorems/` 中，经 `lake build` 验证、无 `sorry` 的定理。

## 日志

| 日期 | 类型 | 内容 | 关联文件 |
|------|------|------|----------|
| 2026-08-18 | verified | Erdős–Szekeres 单调子序列定理（弱版本） | `ErdosTest/Szekeres.lean` |
