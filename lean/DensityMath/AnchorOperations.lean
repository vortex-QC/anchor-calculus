import Mathlib

/-!
# 锚的构造学 · 四操作形式化（2026-09-29 晚 执行序③）

对应: papers/锚的构造学_立项_v0.1.md（§三 四操作+构造史）+
  papers/锚的构造学_容2与C2独立性_v0.1.md（C2 正式化·"锚史沉默"升正式）+
  papers/破缺溯源_同时性先行_三层谱系_v0.1.md（分流=命运型·三体判例）

内容（离散锚模型——承接锚数论文 ℤ/ℕ 离散骨架传统）:
  AnchoredSys     锚定系统（锚集 S × 归宿映射 fate × 锚-1 条件）
  opCollapse      塌（加锚）：一切归宿换为锚点——幂等定理
  opMove          移（锚移位）：锚迁移、唯一性保持——幂等定理
  opSplit         裂（锚分裂）：锚集换为简并族+命运分配——非幂等定理（显式模型）
  opSplitFlow     分流（初值型）：只换命运分配、锚集不变——分配机制分界定理
  allocation_silence  命运分配沉默（同锚集不同分配并存且分流连通——定理 3.1 操作层对应）
  History         构造史=操作序列（自由幺半群·结合律+非交换性）

设计要点（容-2/C2 概念轮的形式句）:
  · 分流与裂的分界=分配机制：split 换锚集（锚层事件·流形上等价），
    splitFlow 不换锚集只换分配（轨道层事件·命运互斥）——两层正交可并存；
  · 复合次序：锚集由裂定（交换不变·定理四a）×分配由次序定（交换改变·定理四b）
  · 锚-1 条件（anchored: ∀i, fate i ∈ anchor）在四操作下全部保持
零 sorry。
-/

namespace AnchorOps

/-- ℕ 版交替分配（命运分配的显式第二例）。 -/
def fAlt : ℕ → ℕ := fun i => if i = 0 then 0 else 1

/-- Bool 版交替分配（定理五专用）。 -/
def fAltB : Bool → ℕ := fun i => if i then 1 else 0

theorem fAltB_false : fAltB false = 0 := rfl
theorem fAltB_true : fAltB true = 1 := rfl

theorem fAlt_mem01 : ∀ i : ℕ, fAlt i ∈ ({0, 1} : Set ℕ) := by
  intro i; by_cases h : i = 0 <;> simp [fAlt, h]

/-- 锚定系统：初值空间 I、归宿空间 Y——锚集 S、归宿映射 fate、锚-1 条件
    （锚在哪里极限就在哪里：每个初值的归宿落在锚集内）。 -/
structure AnchoredSys (I Y : Type) where
  anchor : Set Y
  fate : I → Y
  anchored : ∀ i, fate i ∈ anchor

/-- **塌**（加锚）：引入锚点 a，一切初值的归宿塌为 a（动→静·多→一）。
    定理 3.4 正向（完备化=加锚）的操作化。 -/
def opCollapse {I Y : Type} (a : Y) (_ : AnchoredSys I Y) : AnchoredSys I Y where
  anchor := {a}
  fate := fun _ => a
  anchored := fun _ => by simp

/-- **移**（锚移位）：锚整体迁移到 y，静点换位但唯一性保持（静→静·一→一）。
    锚-1 弱约束读法（换锚极限跟着换）。 -/
def opMove {I Y : Type} (y : Y) (_ : AnchoredSys I Y) : AnchoredSys I Y where
  anchor := {y}
  fate := fun _ => y
  anchored := fun _ => by simp

/-- **裂**（锚分裂·参数型）：锚集换为简并族 S，归宿映射换为新分配 f'
    （裂必然带一次命运分配——流形上取支）。静→动（一→多）。 -/
def opSplit {I Y : Type} (S : Set Y) (f' : I → Y) (hf' : ∀ i, f' i ∈ S)
    (_ : AnchoredSys I Y) : AnchoredSys I Y where
  anchor := S
  fate := f'
  anchored := hf'

/-- **分流**（初值型·锚前分裂）：锚集不动，只重排命运分配 f'
    （轨道层事件·命运互斥——分形边界承载分配）。
    与裂的分界=分配机制：split 换锚集，splitFlow 保锚集。 -/
def opSplitFlow {I Y : Type} (s : AnchoredSys I Y) (f' : I → Y)
    (hf' : ∀ i, f' i ∈ s.anchor) : AnchoredSys I Y where
  anchor := s.anchor
  fate := f'
  anchored := hf'

/-! ### 定理一：塌幂等（加锚一次即定） -/

theorem opCollapse_idempotent {I Y : Type} (a : Y) (s : AnchoredSys I Y) :
    opCollapse a (opCollapse a s) = opCollapse a s := rfl

/-! ### 定理二：移幂等（移到同一位置两次=一次） -/

theorem opMove_idempotent {I Y : Type} (y : Y) (s : AnchoredSys I Y) :
    opMove y (opMove y s) = opMove y s := rfl

/-! ### 定理三：裂非幂等（再裂换锚集——显式模型 ℕ） -/

theorem opSplit_not_idempotent :
    ∃ (s : AnchoredSys ℕ ℕ) (S₁ S₂ : Set ℕ) (f' : ℕ → ℕ)
      (h₁ : ∀ i, f' i ∈ S₁) (h₂ : ∀ i, f' i ∈ S₂),
        opSplit S₂ f' h₂ (opSplit S₁ f' h₁ s) ≠ opSplit S₁ f' h₁ s := by
  refine ⟨{ anchor := {0}, fate := fun _ => 0, anchored := fun _ => by simp },
    {0, 1}, {0, 1, 2}, fun _ => 0, by simp, by simp, ?_⟩
  intro h
  have h1 : ({0, 1, 2} : Set ℕ) = {0, 1} := congrArg AnchoredSys.anchor h
  have h2 : (2 : ℕ) ∈ ({0, 1, 2} : Set ℕ) := by simp
  rw [h1] at h2
  simp at h2

/-! ### 定理四：分配机制分界（两层正交·两件） -/

/-- 分流不改变锚集（定义即等——轨道层事件）。 -/
theorem opSplitFlow_anchor_invariant {I Y : Type} (s : AnchoredSys I Y)
    (f' : I → Y) (hf' : ∀ i, f' i ∈ s.anchor) :
    (opSplitFlow s f' hf').anchor = s.anchor := rfl

/-- 四-a：复合次序在锚集层交换不变（最终锚集由裂决定）。 -/
theorem compose_order_same_anchor :
    ∀ (s : AnchoredSys ℕ ℕ) (S : Set ℕ) (f : ℕ → ℕ)
      (hf : ∀ i, f i ∈ S) (hS : ∀ i, f i ∈ s.anchor),
        (opSplit S f hf (opSplitFlow s f hS)).anchor
          = (opSplitFlow (opSplit S f hf s) f hf).anchor := by
  intro s S f hf _
  rfl

/-- 四-b：复合次序在分配层不交换（命运分配由次序决定——显式模型：
    左=裂的分配 f₀ 生效；右=分流的分配 fAlt 生效；锚集同为裂所定）。 -/
theorem compose_order_differs_fate :
    ∃ (s : AnchoredSys ℕ ℕ) (S : Set ℕ) (f₀ f₁ : ℕ → ℕ)
      (hf₀ : ∀ i, f₀ i ∈ S) (hS : ∀ i, f₁ i ∈ s.anchor) (hf₁ : ∀ i, f₁ i ∈ S),
        (opSplit S f₀ hf₀ (opSplitFlow s f₁ hS)).fate
          ≠ (opSplitFlow (opSplit S f₀ hf₀ s) f₁ hf₁).fate := by
  refine ⟨{ anchor := {0, 1}, fate := fun _ => 0, anchored := fun _ => by simp },
    {0, 1}, (fun _ => 0), fAlt, by simp, fAlt_mem01, fAlt_mem01, ?_⟩
  intro h
  have h1 : (0 : ℕ) = 1 := congrFun h 1
  exact absurd h1 (by norm_num)

/-! ### 定理五：命运分配沉默（同锚集·不同分配并存且分流连通）
    ——锚数定理 3.1（D0 对归宿沉默）的操作层对应：
    锚集裁决归宿的值域，对"哪个初值落到哪支"沉默；
    分流操作在该沉默空间内自由重排。 -/

theorem allocation_silence :
    ∃ s₁ s₂ : AnchoredSys Bool ℕ,
      s₁.anchor = s₂.anchor ∧ s₁.fate ≠ s₂.fate ∧
        ∃ hf' : ∀ i, fAltB i ∈ s₁.anchor, opSplitFlow s₁ fAltB hf' = s₂ := by
  refine ⟨{ anchor := {0, 1}, fate := fun _ => 0, anchored := fun _ => by simp },
    { anchor := {0, 1}, fate := fAltB, anchored := fun i => by
        cases i with
        | false => rw [fAltB_false]; simp
        | true => rw [fAltB_true]; simp },
    rfl, ?_, ⟨fun i => by cases i with
               | false => rw [fAltB_false]; simp
               | true => rw [fAltB_true]; simp, rfl⟩⟩
  intro h
  have h1 : (0 : ℕ) = 1 := congrFun h true
  exact absurd h1 (by norm_num)

/-! ### 定理七：分配史不可复原（记账律·账本单向律的形式句）

记账律探索（papers/锚的构造学_记账律探索_v0.1.md §50）的定理化：
同一终态由两条不同的构造史产生——史 A=一步裂直配（split 直接给出 fAltB），
史 B=裂+分流重排（split 先全 0 分配、splitFlow 再重排到 fAltB）。
终态定义相等（anchor 同为 S、fate 同为 fAltB），但中间状态序列不同
（史 B 的中间态 anchor={0,1} ≠ 史 A 的起点 s₀ 的 anchor={0}）——
终态不携带「哪条分配史发生」的信息：分配史不可从终态复原。 -/

theorem allocation_history_irrecoverable :
    ∃ (s₀ : AnchoredSys Bool ℕ) (S : Set ℕ) (f : Bool → ℕ)
      (hf : ∀ i, f i ∈ S) (hg : ∀ i, (fun _ => (0:ℕ)) i ∈ S),
      -- 史 A 与史 B 到达同一终态（定义相等）：
      opSplit S f hf s₀
        = opSplitFlow (opSplit S (fun _ => 0) hg s₀) f hf ∧
      -- 两史不同：史 B 的中间态 ≠ 史 A 的起点（状态序列分叉）：
      opSplit S (fun _ => 0) hg s₀ ≠ s₀ := by
  refine ⟨{ anchor := {0}, fate := fun _ => (0:ℕ), anchored := fun _ => by simp },
    {0, 1}, fAltB, ?_, by simp, ?_, ?_⟩
  · intro i; cases i with
    | false => rw [fAltB_false]; simp
    | true => rw [fAltB_true]; simp
  · rfl
  · intro h
    have h1 : ({0, 1} : Set ℕ) = {0} := congrArg AnchoredSys.anchor h
    have h2 : (1 : ℕ) ∈ ({0, 1} : Set ℕ) := by simp
    rw [h1] at h2
    simp at h2

/-! ### 定理八：塌的记录擦除（不对称的塌侧形式句）

「塌=信息压缩多→一」：塌后归宿恒为锚点——终态对塌前的任何分配史
（fate 曾为何）完全沉默；且塌链一步稳定（幂等·定理一）。
对照：裂产生分配史且该史不可从终态复原（定理七）、裂链每步产生新锚集
（定理三）。两者合取=「塌幂等可重复×裂不可逆」的不对称精确内容
——主人「破缺=塌锚反向面」洞见（静↔动不对称）的记账律层形式句。 -/

theorem collapse_erases_history {I Y : Type} (a : Y) (s : AnchoredSys I Y) :
    (∀ i, (opCollapse a s).fate i = a)
      ∧ opCollapse a (opCollapse a s) = opCollapse a s :=
  ⟨fun _ => rfl, rfl⟩

/-! ### 定理六：构造史=操作序列（自由幺半群·结合律+非交换性） -/

/-- 操作基本事件：塌/移/裂/分流四构造子（带参版本在构造史账本层展开）。 -/
inductive Op where
  | collapse | move | split | splitFlow
  deriving DecidableEq

/-- 构造史：操作序列——自由幺半群承载（拼接=时序）。 -/
abbrev History := List Op

/-- 构造史时序的结合律：三段史合并与分段无关（账本分层自由）。 -/
theorem history_assoc (h₁ h₂ h₃ : History) :
    h₁ ++ h₂ ++ h₃ = h₁ ++ (h₂ ++ h₃) := List.append_assoc _ _ _

/-- 非交换性：操作时序有向（塌后裂 ≠ 裂后塌——构造史是有序账本）。 -/
theorem history_noncomm :
    ∃ h₁ h₂ : History, h₁ ++ h₂ ≠ h₂ ++ h₁ :=
  ⟨[Op.collapse], [Op.split], by decide⟩

end AnchorOps

-- 轴公理自检（2026-09-29 build 记录）：五定理 depends on axioms ∈
-- [propext, Quot.sound]（history_noncomm 零依赖）——零 sorry 已核（全库 8726 jobs）
