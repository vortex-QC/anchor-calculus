import Mathlib

/-!
# 锚的构造学 · 测度分配律测度论层形式化（2026-09-30 挂账 15 大件）

对应: papers/锚的构造学_连续分配几何记账律_v0.1.md §四 挂账 15
上游: 连续分配几何记账律（三层形态：测度分配/边界承载/指派不可逆）+ AnchorOperations.lean（定理七分配史不可复原·离散版）

内容（记账律三律的测度论形式化·单位区间概率模型）:

  守恒层·测度分配律:
    basin f d = f ⁻¹' {d}（命运盆地=原像·逆读=原像的定义句）
    basin_union / basin_disjoint / basin_eq_compl（原像划分·初值空间的命运分块）
    **measure_basin_add**: 概率空间上两盆地测度和 = 1（质量守恒的分配版）
    三体数值实例（单位区间）: 收敛盆地 Iic 0.138 的测度 = 13.8%·补盆地 = 86.2%
      ——三体 CRTBP 600×600 实测（8-10 在案 24 点）的测度论形式承载
  约束层·边界承载律:
    **measure_frontier_add**: 边界账公式 μ(interior B) + μ(∂B) = μ(closure B)
    zero_frontier: μ(∂B) = 0 → 内域测度=闭包测度（分配"除边界外无成本"判据）
    undetBand mono: 未定带（边界的 ε-加厚·thickening）测度随 ε 单调
      ——未定带 ~ε^(2−D) 标度关系的测度论载体（D 的盒计数形式化=挂账 14 数值侧·正交不硬造）
  方向层·指派不可逆律:
    fateMap: 初值→命运指派（阈值映射）·正读可计算（定义句）
    basin_fateMap_zero: 阈值指派的塌盆地 = 下区间
    **basin_infinite**: 塌盆地无穷（**集合非点**·逆读不能回到初值的存在性实例）
    two_initials_one_fate: ∃ x₁ ≠ x₂ 同命运（核非平凡·**定理七的连续对应**：分配史不可复原）
    不可复原的量=盆地测度（μ(basin)·与守恒层闭环——两盆地测度和=1 已证）

诚实边界: 两盆地（Fin 2 命运集）判例形式化——n 盆地推广=直接后续；盒计数维数 D 的形式化
  不在本件（挂账 14 数值侧的正交面·不硬造）；盆地取可测集承载测度（阈值映射的原像=区间
  可测 ✓ 如实标注）。零 sorry。
-/

namespace GeoAnchorMeasure

open MeasureTheory Measure Set Metric
open scoped unitInterval

/-- Fin 2 恰有两值（0 或 1）——两命运模型的穷尽句。 -/
theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  obtain ⟨v, hv⟩ := i
  have h : v = 0 ∨ v = 1 := by omega
  rcases h with h | h <;>
    [left; right] <;> exact Fin.ext h

/-! ### 第一部分 · 命运指派的语法面（纯集合层·逆读=原像） -/

/-- 命运盆地：初值空间按命运标签的原像——**逆读=原像**（集合非点的载体）。 -/
def basin (f : X → Fin 2) (d : Fin 2) : Set X := f ⁻¹' {d}

theorem mem_basin (f : X → Fin 2) (d : Fin 2) (x : X) : x ∈ basin f d ↔ f x = d := by
  simp [basin]

/-- **原像划分**：初值空间 = 两命运盆地之并（逆读的全部信息=盆地集合）。 -/
theorem basin_union (f : X → Fin 2) : basin f 0 ∪ basin f 1 = univ := by
  ext x
  have h : f x = 0 ∨ f x = 1 := fin2_cases _
  cases h with
  | inl h => simp [basin, h]
  | inr h => simp [basin, h]

/-- 两盆地互斥（命运互斥·分流的结构面）。 -/
theorem basin_disjoint (f : X → Fin 2) : Disjoint (basin f 0) (basin f 1) := by
  have h01 : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
  refine Set.disjoint_left.mpr fun a ha hb => ?_
  simp only [basin, Set.mem_preimage, Set.mem_singleton_iff] at ha hb
  exact h01 (ha.symm.trans hb)

/-- 逃逸盆地 = 塌盆地的补（Fin 2 两命运）。 -/
theorem basin_eq_compl (f : X → Fin 2) : basin f 1 = (basin f 0)ᶜ := by
  ext x
  have h : f x = 0 ∨ f x = 1 := fin2_cases _
  simp only [basin, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff]
  rcases h with h | h
  · rw [h]
    decide
  · rw [h]
    decide

/-! ### 第二部分 · 守恒层：测度分配律（概率空间·两盆地测度和 = 1） -/

/-- **测度分配律**：概率空间上两命运盆地的测度和 = 1——质量守恒的分配版
    （三体判例：收敛 13.8% + 弥散 86.2% = 100% 的形式承载）。 -/
theorem measure_basin_add {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] (f : X → Fin 2) (hb : MeasurableSet (basin f 0)) :
    μ (basin f 0) + μ (basin f 1) = 1 := by
  have h1 : basin f 1 = (basin f 0)ᶜ := basin_eq_compl f
  have hfin : μ (basin f 0) ≠ ⊤ := (measure_lt_top μ _).ne
  have huniv : μ univ = 1 := IsProbabilityMeasure.measure_univ
  have hle : μ (basin f 0) ≤ 1 := by
    have h2 : μ (basin f 0) ≤ μ univ := measure_mono (Set.subset_univ _)
    rw [huniv] at h2
    exact h2
  rw [h1, measure_compl hb hfin, huniv, add_comm]
  exact tsub_add_cancel_of_le hle

/-! ### 第三部分 · 三体数值实例（单位区间概率模型） -/

/-- 三体收敛盆地：初值 ≤ 0.138（13.8% 收敛·CRTBP 600×600 实测在案转写）。 -/
noncomputable def collapseBasin : Set I := Set.Iic (⟨0.138, by norm_num [Set.mem_Icc]⟩ : I)

theorem measurableSet_collapseBasin : MeasurableSet collapseBasin := by
  unfold collapseBasin
  exact measurableSet_Iic

/-- **三体收敛盆地测度 = 13.8%**。 -/
theorem sanTi_collapsed_measure : volume collapseBasin = ENNReal.ofReal 0.138 := by
  unfold collapseBasin
  exact unitInterval.volume_Iic ⟨0.138, by norm_num [Set.mem_Icc]⟩

/-- 三体读数的算术面：13.8% + 86.2% = 100%。 -/
theorem sanTi_split : ENNReal.ofReal 0.138 + ENNReal.ofReal 0.862 = 1 := by
  have h : (0.138 + 0.862 : ℝ) = 1 := by norm_num
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), h, ENNReal.ofReal_one]

/-- **三体弥散盆地测度 = 86.2%**（收敛盆地的补·measure_compl）。 -/
theorem sanTi_escaped_measure : volume collapseBasinᶜ = ENNReal.ofReal 0.862 := by
  have hfin : volume collapseBasin ≠ ⊤ := (measure_lt_top volume collapseBasin).ne
  rw [measure_compl measurableSet_collapseBasin hfin, sanTi_collapsed_measure,
    IsProbabilityMeasure.measure_univ]
  have h2 : (1 : ENNReal) - ENNReal.ofReal 0.138 = ENNReal.ofReal 0.862 := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 0.138)]
    congr 1
    norm_num
  rw [h2]

/-! ### 第四部分 · 约束层：边界承载律（边界账公式+未定带） -/

/-- **边界账公式**：μ(interior B) + μ(∂B) = μ(closure B)——
    分配的几何承载=盆地边界；边界测度=分配的测度论成本读数。 -/
theorem measure_frontier_add (B : Set I) :
    volume (interior B) + volume (frontier B) = volume (closure B) := by
  have hcover : closure B = interior B ∪ frontier B := by
    ext x
    constructor
    · intro h
      by_cases hmem : x ∈ interior B
      · exact Or.inl hmem
      · exact Or.inr ⟨h, hmem⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact interior_subset.trans subset_closure h
      · exact h1
  have hdisj : Disjoint (interior B) (frontier B) :=
    Set.disjoint_left.mpr fun a ha hb => by
      simp only [frontier, Set.mem_sdiff] at hb
      exact hb.2 ha
  have hmeas : MeasurableSet (frontier B) :=
    (isClosed_closure.measurableSet).diff isOpen_interior.measurableSet
  calc volume (interior B) + volume (frontier B)
      = volume (interior B ∪ frontier B) :=
        (measure_union hdisj hmeas).symm
    _ = volume (closure B) := by rw [hcover]

/-- **零测边界判据**：μ(∂B) = 0 → μ(interior B) = μ(closure B)——
    分配"除边界外无成本"的形式句（光滑边界盆地 D→1 端的测度论面）。 -/
theorem zero_frontier (B : Set I) (h0 : volume (frontier B) = 0) :
    volume (interior B) = volume (closure B) := by
  have h := measure_frontier_add B
  rw [h0, add_zero] at h
  exact h

/-- **未定带**：盆地边界的 ε-加厚——距边界 <ε 的初值带（命运未定带的测度论载体）。 -/
noncomputable def undetBand (B : Set I) (ε : ℝ) : Set I :=
  Metric.thickening ε (frontier B)

/-- 未定带单调：ε 越大未定带越大（测度账随之单调）——
    D 越大任意分辨率下未定带越宽的测度论骨架（ε^(2−D) 标度=挂账 14 数值侧）。 -/
theorem undetBand_mono (B : Set I) {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    volume (undetBand B ε₁) ≤ volume (undetBand B ε₂) :=
  measure_mono (Metric.thickening_mono h _)

/-! ### 第五部分 · 方向层：指派不可逆律（正读可计算/逆读=集合非点） -/

/-- 阈值命运指派：正读可计算（if 判读·积分方程的离散形式句）。 -/
noncomputable def fateMap (c : I) : I → Fin 2 := fun x => if x ≤ c then 0 else 1

/-- 阈值指派的塌盆地 = 下区间（正读的形式句）。 -/
theorem basin_fateMap_zero (c : I) : basin (fateMap c) 0 = Set.Iic c := by
  ext x
  by_cases h : x ≤ c
  · simp [basin, fateMap, h]
  · simp [basin, fateMap, h]

/-- **盆地无穷**（集合非点·存在性实例）：塌盆地含无穷多初值——
    逆读从命运标签只能回到整个盆地不能回到初值。 -/
theorem basin_infinite (c : I) (hc0 : (0 : I) < c) (hc1 : c < 1) :
    (basin (fateMap c) 0).Infinite := by
  rw [basin_fateMap_zero]
  refine Set.Infinite.mono (fun x hx => le_of_lt hx.2) (Set.Ioo_infinite hc0)

/-- **定理七连续对应**：∃ x₁ ≠ x₂ 同命运——核非平凡（分配史不可复原的连续形式句：
    同一命运标签由不同初值映射而来·逆读不能区分 x₁ 与 x₂·稠密序取中间点）。 -/
theorem two_initials_one_fate (c : I) (hc0 : (0 : I) < c) :
    ∃ x₁ x₂ : I, x₁ ≠ x₂ ∧ fateMap c x₁ = fateMap c x₂ := by
  obtain ⟨y, hy0, hyc⟩ := exists_between hc0
  refine ⟨0, y, ?_, ?_⟩
  · intro h
    have hv : (0 : I) < (0 : I) := h ▸ hy0
    exact lt_irrefl _ hv
  · simp only [fateMap, if_pos hc0.le, if_pos (le_of_lt hyc)]

/-- **三律闭环主定理**（记账律连续总形态的形式句）：
    守恒层（两盆地测度和=1）∧ 约束层（边界账公式对任意盆地成立）∧
    方向层（同命运初值对存在+盆地无穷·核非平凡）——三层齐而全局守恒量仍不存在
    （守恒的是测度和不是"信息"·与离散判定一致）。 -/
theorem ledger_main (c : I) (hc0 : (0 : I) < c) (hc1 : c < 1) :
    (∀ f : I → Fin 2, MeasurableSet (basin f 0) →
      volume (basin f 0) + volume (basin f 1) = 1) ∧
    (∀ B : Set I, volume (interior B) + volume (frontier B) = volume (closure B)) ∧
    (∃ x₁ x₂ : I, x₁ ≠ x₂ ∧ fateMap c x₁ = fateMap c x₂) ∧
    (basin (fateMap c) 0).Infinite :=
  ⟨fun f hf => measure_basin_add f hf, fun B => measure_frontier_add B,
    two_initials_one_fate c hc0, basin_infinite c hc0 hc1⟩

end GeoAnchorMeasure
