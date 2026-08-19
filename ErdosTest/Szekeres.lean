import Mathlib

/-!
# Erdős–Szekeres 单调子序列定理（Erdős–Szekeres, 1935）

任意长度为 `n * n + 1` 的自然数序列，必含有一个长度为 `n + 1` 的（弱）单调子序列。

证明是经典的鸽笼原理论证：对每个位置 `i`，记
- `up a i`  = 以 `i` 结尾的最长弱递增子序列的长度，
- `down a i` = 以 `i` 结尾的最长弱递减子序列的长度。

若 `i < j` 且 `a i ≤ a j`，则 `up a i < up a j`；若 `a i ≥ a j`，则 `down a i < down a j`。
因此映射 `i ↦ (up a i, down a i)` 是单射。若所有 `up a i ≤ n` 且 `down a i ≤ n`，
则这个单射把 `n * n + 1` 个指标送进 `n * n` 个格子，矛盾。

这里是弱版本（不要求序列各项互异），因此结论是弱单调（非严格单调）。
-/

noncomputable section

open Classical

namespace ErdosSzekeres

variable {m : ℕ}
variable {a : Fin m → ℕ}

/-- 序列 `a` 中存在以指标 `i` 结尾、长度为 `k` 的弱递增子序列（`k = 0` 恒假）。 -/
def HasIncEnding (a : Fin m → ℕ) (i : Fin m) : ℕ → Prop
  | 0 => False
  | k + 1 => ∃ f : Fin (k + 1) → Fin m, StrictMono f ∧ f (Fin.last k) = i ∧ Monotone (a ∘ f)

/-- 序列 `a` 中存在以指标 `i` 结尾、长度为 `k` 的弱递减子序列（`k = 0` 恒假）。 -/
def HasDecEnding (a : Fin m → ℕ) (i : Fin m) : ℕ → Prop
  | 0 => False
  | k + 1 => ∃ f : Fin (k + 1) → Fin m, StrictMono f ∧ f (Fin.last k) = i ∧ Antitone (a ∘ f)

/-- 以 `i` 结尾的最长弱递增子序列的长度。 -/
noncomputable def up (a : Fin m → ℕ) (i : Fin m) : ℕ :=
  Nat.findGreatest (HasIncEnding a i) m

/-- 以 `i` 结尾的最长弱递减子序列的长度。 -/
noncomputable def down (a : Fin m → ℕ) (i : Fin m) : ℕ :=
  Nat.findGreatest (HasDecEnding a i) m

/-- 单点序列是长度为 1 的（既递增又递减的）子序列。 -/
lemma hasIncEnding_one (a : Fin m → ℕ) (i : Fin m) : HasIncEnding a i 1 := by
  refine ⟨fun _ => i, ?_, rfl, ?_⟩
  · intro x y hxy
    exfalso
    have hxv : x.val < 1 := x.isLt
    have hyv : y.val < 1 := y.isLt
    have hxy' : x.val < y.val := hxy
    omega
  · intro x y _
    simp

/-- 单点序列是长度为 1 的递减子序列。 -/
lemma hasDecEnding_one (a : Fin m → ℕ) (i : Fin m) : HasDecEnding a i 1 := by
  refine ⟨fun _ => i, ?_, rfl, ?_⟩
  · intro x y hxy
    exfalso
    have hxv : x.val < 1 := x.isLt
    have hyv : y.val < 1 := y.isLt
    have hxy' : x.val < y.val := hxy
    omega
  · intro x y _
    simp

/-- 对 `Fin (n + 1)` 中任意指标，`up` 与 `down` 至少为 1。 -/
lemma up_ge_one (a : Fin m → ℕ) (i : Fin m) : 1 ≤ up a i := by
  have hi : i.val < m := i.isLt
  have hm1 : 1 ≤ m := by omega
  exact Nat.le_findGreatest hm1 (hasIncEnding_one a i)

lemma down_ge_one (a : Fin m → ℕ) (i : Fin m) : 1 ≤ down a i := by
  have hi : i.val < m := i.isLt
  have hm1 : 1 ≤ m := by omega
  exact Nat.le_findGreatest hm1 (hasDecEnding_one a i)

/-- 把一个严格递增的指标序列 `f` 延长一位（末位取 `j`），保持严格递增，
前提是 `f` 的最后一个值仍小于 `j`。 -/
lemma strictMono_lastCases {k : ℕ} (f : Fin (k + 1) → Fin m) (hf : StrictMono f)
    {j : Fin m} (hj : f (Fin.last k) < j) : StrictMono (Fin.lastCases j f) := by
  intro x y hxy
  rcases Fin.eq_castSucc_or_eq_last x with ⟨x', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last y with ⟨y', rfl⟩ | rfl
    · simpa using hf ((Fin.castSucc_lt_castSucc_iff).mp hxy)
    · simpa using (hf.le_iff_le.mpr (Fin.le_last x')).trans_lt hj
  · rcases Fin.eq_castSucc_or_eq_last y with ⟨y', rfl⟩ | rfl
    · exact (lt_irrefl _ (hxy.trans (Fin.castSucc_lt_last y'))).elim
    · exact (lt_irrefl _ hxy).elim

/-- 若 `f` 使 `a ∘ f` 弱递增，且末位值 `a (f (last k)) ≤ a j`，
则延长一位后 `a ∘ (Fin.lastCases j f)` 仍弱递增。 -/
lemma monotone_lastCases {k : ℕ} (f : Fin (k + 1) → Fin m) (hf : Monotone (a ∘ f))
    {j : Fin m} (hj : a (f (Fin.last k)) ≤ a j) : Monotone (a ∘ Fin.lastCases j f) := by
  intro x y hxy
  rcases Fin.eq_castSucc_or_eq_last x with ⟨x', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last y with ⟨y', rfl⟩ | rfl
    · simpa using hf hxy
    · simpa using (hf (Fin.le_last x')).trans hj
  · rcases Fin.eq_castSucc_or_eq_last y with ⟨y', rfl⟩ | rfl
    · exact (lt_irrefl _ (lt_of_lt_of_le (Fin.castSucc_lt_last y') hxy)).elim
    · exact le_rfl

/-- 若 `f` 使 `a ∘ f` 弱递减，且末位值 `a j ≤ a (f (last k))`，
则延长一位后 `a ∘ (Fin.lastCases j f)` 仍弱递减。 -/
lemma antitone_lastCases {k : ℕ} (f : Fin (k + 1) → Fin m) (hf : Antitone (a ∘ f))
    {j : Fin m} (hj : a j ≤ a (f (Fin.last k))) : Antitone (a ∘ Fin.lastCases j f) := by
  intro x y hxy
  rcases Fin.eq_castSucc_or_eq_last x with ⟨x', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last y with ⟨y', rfl⟩ | rfl
    · simpa using hf hxy
    · simpa using hj.trans (hf (Fin.le_last x'))
  · rcases Fin.eq_castSucc_or_eq_last y with ⟨y', rfl⟩ | rfl
    · exact (lt_irrefl _ (lt_of_lt_of_le (Fin.castSucc_lt_last y') hxy)).elim
    · exact le_rfl

/-- 递增子序列的“延伸”引理：若 `i < j` 且 `a i ≤ a j`，则以 `i` 结尾的长度 `k ≥ 1`
递增子序列可延伸到以 `j` 结尾的长度 `k + 1` 递增子序列。 -/
lemma hasIncEnding_succ {i j : Fin m} (hij : i < j) (hval : a i ≤ a j) {k : ℕ}
    (h : HasIncEnding a i k) (hk : 1 ≤ k) : HasIncEnding a j (k + 1) := by
  cases k with
  | zero => omega
  | succ k =>
    rcases h with ⟨f, hf_mono, hf_last, hf_val⟩
    let g : Fin (k + 2) → Fin m := Fin.lastCases j f
    refine ⟨g, ?_, ?_, ?_⟩
    · exact strictMono_lastCases f hf_mono (by simpa [hf_last] using hij)
    · simp [g]
    · exact monotone_lastCases (a := a) f hf_val (by simpa [hf_last] using hval)

/-- 递减子序列的“延伸”引理。 -/
lemma hasDecEnding_succ {i j : Fin m} (hij : i < j) (hval : a j ≤ a i) {k : ℕ}
    (h : HasDecEnding a i k) (hk : 1 ≤ k) : HasDecEnding a j (k + 1) := by
  cases k with
  | zero => omega
  | succ k =>
    rcases h with ⟨f, hf_mono, hf_last, hf_val⟩
    let g : Fin (k + 2) → Fin m := Fin.lastCases j f
    refine ⟨g, ?_, ?_, ?_⟩
    · exact strictMono_lastCases f hf_mono (by simpa [hf_last] using hij)
    · simp [g]
    · exact antitone_lastCases (a := a) f hf_val (by simpa [hf_last] using hval)

/-- 若 `i < j` 且 `a i ≤ a j`，则 `up a i < up a j`。 -/
lemma up_lt_up (a : Fin m → ℕ) {i j : Fin m} (hij : i < j) (hval : a i ≤ a j) :
    up a i < up a j := by
  have hspec : HasIncEnding a i (up a i) := by
    apply Nat.findGreatest_spec (P := HasIncEnding a i) (m := 1) (n := m)
    · omega
    · exact hasIncEnding_one a i
  have hnext : HasIncEnding a j (up a i + 1) :=
    hasIncEnding_succ (a := a) hij hval hspec (up_ge_one a i)
  have hbound : up a i + 1 ≤ m := by
    rcases hnext with ⟨f, hf, _, _⟩
    simpa using Fintype.card_le_of_injective f hf.injective
  have hle : up a i + 1 ≤ up a j :=
    Nat.le_findGreatest hbound hnext
  omega

/-- 若 `i < j` 且 `a i ≥ a j`，则 `down a i < down a j`。 -/
lemma down_lt_down (a : Fin m → ℕ) {i j : Fin m} (hij : i < j) (hval : a j ≤ a i) :
    down a i < down a j := by
  have hspec : HasDecEnding a i (down a i) := by
    apply Nat.findGreatest_spec (P := HasDecEnding a i) (m := 1) (n := m)
    · omega
    · exact hasDecEnding_one a i
  have hnext : HasDecEnding a j (down a i + 1) :=
    hasDecEnding_succ (a := a) hij hval hspec (down_ge_one a i)
  have hbound : down a i + 1 ≤ m := by
    rcases hnext with ⟨f, hf, _, _⟩
    simpa using Fintype.card_le_of_injective f hf.injective
  have hle : down a i + 1 ≤ down a j :=
    Nat.le_findGreatest hbound hnext
  omega

/-- 指标到 `(up, down)` 对的映射是单射。 -/
lemma pair_inj (a : Fin m → ℕ) : Function.Injective (fun i => (up a i, down a i)) := by
  intro i j h
  have h' : (up a i, down a i) = (up a j, down a j) := by simpa using h
  rcases lt_trichotomy i j with hij | rfl | hji
  · rcases le_total (a i) (a j) with hval | hval
    · have hlt : up a i < up a j := up_lt_up a hij hval
      have heq : up a i = up a j := by simpa using congrArg Prod.fst h'
      omega
    · have hlt : down a i < down a j := down_lt_down a hij hval
      have heq : down a i = down a j := by simpa using congrArg Prod.snd h'
      omega
  · rfl
  · rcases le_total (a j) (a i) with hval | hval
    · have hlt : up a j < up a i := up_lt_up a hji hval
      have heq : up a i = up a j := by simpa using congrArg Prod.fst h'
      omega
    · have hlt : down a j < down a i := down_lt_down a hji hval
      have heq : down a i = down a j := by simpa using congrArg Prod.snd h'
      omega

/-- `1 ≤ x` 且 `x ≤ n` 蕴含 `x - 1 < n`。 -/
lemma pred_lt_of_ge_one_le {x n : ℕ} (h1 : 1 ≤ x) (h2 : x ≤ n) : x - 1 < n := by
  omega

/-- 把 `Fin n` 嵌入 `Fin K`（当 `n ≤ K`），保持严格单调。 -/
lemma strictMono_fin_take {n K : ℕ} (h : n ≤ K) :
    StrictMono (fun x : Fin n => (⟨x.val, Nat.lt_of_lt_of_le x.isLt h⟩ : Fin K)) := by
  intro x y hxy
  simpa using hxy

/-- 把 `Fin n` 嵌入 `Fin K`（当 `n ≤ K`），保持单调。 -/
lemma monotone_fin_take {n K : ℕ} (h : n ≤ K) :
    Monotone (fun x : Fin n => (⟨x.val, Nat.lt_of_lt_of_le x.isLt h⟩ : Fin K)) := by
  intro x y hxy
  simpa using hxy

/-- 若存在以 `i` 结尾、长度 `K ≥ n + 1` 的递增子序列，则存在长度 `n + 1` 的递增子序列。 -/
lemma monotone_of_has {n : ℕ} (a : Fin m → ℕ) {i : Fin m} {K : ℕ} (hK : n + 1 ≤ K)
    (h : HasIncEnding a i K) : ∃ f : Fin (n + 1) → Fin m, StrictMono f ∧ Monotone (a ∘ f) := by
  cases K with
  | zero => omega
  | succ K =>
    rcases h with ⟨f, hf, _, hfv⟩
    let take : Fin (n + 1) → Fin (K + 1) := fun x => ⟨x.val, Nat.lt_of_lt_of_le x.isLt hK⟩
    refine ⟨f ∘ take, hf.comp (strictMono_fin_take hK), hfv.comp (monotone_fin_take hK)⟩

/-- 若存在以 `i` 结尾、长度 `K ≥ n + 1` 的递减子序列，则存在长度 `n + 1` 的递减子序列。 -/
lemma antitone_of_has {n : ℕ} (a : Fin m → ℕ) {i : Fin m} {K : ℕ} (hK : n + 1 ≤ K)
    (h : HasDecEnding a i K) : ∃ f : Fin (n + 1) → Fin m, StrictMono f ∧ Antitone (a ∘ f) := by
  cases K with
  | zero => omega
  | succ K =>
    rcases h with ⟨f, hf, _, hfv⟩
    let take : Fin (n + 1) → Fin (K + 1) := fun x => ⟨x.val, Nat.lt_of_lt_of_le x.isLt hK⟩
    refine ⟨f ∘ take, hf.comp (strictMono_fin_take hK), hfv.comp_monotone (monotone_fin_take hK)⟩

/-- **Erdős–Szekeres 定理**：任意长度 `n * n + 1` 的自然数序列都含有长度 `n + 1` 的
弱单调子序列。 -/
theorem erdos_szekeres (n : ℕ) (a : Fin (n * n + 1) → ℕ) :
    ∃ f : Fin (n + 1) → Fin (n * n + 1),
      StrictMono f ∧ (Monotone (a ∘ f) ∨ Antitone (a ∘ f)) := by
  let m := n * n + 1
  by_contra h
  have hup_le : ∀ i : Fin m, up a i ≤ n := by
    intro i
    by_contra hnot
    have hK : n + 1 ≤ up a i := by omega
    have hspec : HasIncEnding a i (up a i) := by
      apply Nat.findGreatest_spec (P := HasIncEnding a i) (m := 1) (n := m)
      · omega
      · exact hasIncEnding_one a i
    obtain ⟨f, hf, hfv⟩ := monotone_of_has (n := n) a hK hspec
    exact h ⟨f, hf, Or.inl hfv⟩
  have hdown_le : ∀ i : Fin m, down a i ≤ n := by
    intro i
    by_contra hnot
    have hK : n + 1 ≤ down a i := by omega
    have hspec : HasDecEnding a i (down a i) := by
      apply Nat.findGreatest_spec (P := HasDecEnding a i) (m := 1) (n := m)
      · omega
      · exact hasDecEnding_one a i
    obtain ⟨f, hf, hfv⟩ := antitone_of_has (n := n) a hK hspec
    exact h ⟨f, hf, Or.inr hfv⟩
  let g : Fin m → Fin n × Fin n := fun i =>
    (⟨up a i - 1, pred_lt_of_ge_one_le (up_ge_one a i) (hup_le i)⟩,
     ⟨down a i - 1, pred_lt_of_ge_one_le (down_ge_one a i) (hdown_le i)⟩)
  have hg_inj : Function.Injective g := by
    intro x y hxy
    have hux : up a x - 1 = up a y - 1 := congrArg Fin.val (congrArg Prod.fst hxy)
    have hdx : down a x - 1 = down a y - 1 := congrArg Fin.val (congrArg Prod.snd hxy)
    apply pair_inj a
    change (up a x, down a x) = (up a y, down a y)
    apply Prod.ext
    · have hu1 : 1 ≤ up a x := up_ge_one a x
      have hu2 : 1 ≤ up a y := up_ge_one a y
      omega
    · have hd1 : 1 ≤ down a x := down_ge_one a x
      have hd2 : 1 ≤ down a y := down_ge_one a y
      omega
  have hcard : n * n + 1 ≤ n * n := by
    have hc := Fintype.card_le_of_injective g hg_inj
    simp [m] at hc
  omega

end ErdosSzekeres
