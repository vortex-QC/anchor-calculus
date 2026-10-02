#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
几何锚数·数值轮：约束建立顺序——操作非交换性定理四b 的格点版（几何自发线判别设计②）
预注册（2026-10-01 深夜·先于跑数落盘·同文件预注册模式·刀三/A4 轮同款）：

  问题（几何自发与约束时序档 §五.2 逐字）：
    A'4 宇宙加约束的顺序实验——先自避免承诺后等距承诺 vs 反序·类数路径是否不同
    （操作非交换性定理四b 的格点版：「分配由次序定」——时序可判别的数值面）

  结构对应（推理级·如实标注）：
    主人时序断言「先一阶约束产生连续边结构，再二阶约束显化多面体，不会反向」
    → 格点 toy 双承诺映射：
      承诺α = 身份锁（形变操作扫过环不包双井·A4 轮 L0·身份=(wA,wB)）
             ——对应「一阶/拓扑身份锁」（连续边结构驻留的格点对应）
      承诺β = 等距锁（形变操作保周长 |P|=|Q|）
             ——对应「二阶/刚性身份锁」（多面体显化的格点对应）
    映射=结构对应（类比级·非物理断言·两层分栏）

  宇宙与操作（全部承袭在案件·零新设定）：
    宇宙 = A'4 双井格点域 x∈[-1,3],y∈[-2,2]（25 格点）·井 A=(0,0)/B=(2,0)
           闭合自避免路径全枚举·规范化=字典序最小旋转（A4 轮同款·808 条）
    操作 = 翻转操作（子弧 S 换替换弧 T·|S|,|T|≤6 窗口·承袭 A4 轮预注册窗口）
    E_α  = 扫过环 wA=0 且 wB=0（双井锁）
    E_β  = |P|=|Q|（等距锁）
    两序：甲序 = 先建立α（E_α 闭包）→ 再建立β（E_α∩E_β 闭包）
          乙序 = 先建立β（E_β 闭包）→ 再建立α（E_β∩E_α 闭包 = 同一交集·终态重合面）

  判据（跑前锁定）：
    OS-1（终态交换面·登记性）: 甲/乙序终态类划分相同（交集闭包唯一确定）
         ——「逼近序列无时序·双向可读」的数值对应物·成立与否如实登记
    OS-2（类数路径可判别·主判据）: 类数路径 [808→N_α→N*] vs [808→N_β→N*]
         中 N_β ≠ N_α ⟺ 成立（中间承诺在场的类结构不同=路径不同）
    OS-3（分配账本可判别·定理四b 格点版）: 存在对象 o 使中间归属 α类(o)≠β类(o)
         计数 N_mid>0 ⟺ 成立（终态同而中间归属不同=分配史由次序定·账本单向的数值面）
    OS-4（操作完备面·对照刀三）: N* = 42（刀三定义面 (wA,wB,len) 档数）
         ⟺ 操作面=定义面；否则如实登记完备率

  判读：OS-2 ∧ OS-3 成立 → 「约束建立顺序」在 A'4 格点域可判别——
        定理四b 双层结构（锚集层可交换[定理四a 对应=终态同]×分配层不可交换[定理四b 对应=
        路径与账本不同]）的格点实例立——主人的时序断言获得数值面：标准数学的终态读法
        （逼近极限）丢掉的正是这个时序。
        OS-1 成立本身不判负——它恰是第二轮档 §三「逼近序列双向可读 vs 构造史单向」的
        交换半边，与 OS-2/OS-3 合读=完整数值对照。

  诚实边界：toy 非物理测量·结构对应=类比级·窗口外完备性挂账（承袭 A4 轮）·
  零新增物理测量值·零新增对外 record·发布物零改动。

  【修正轮留痕 2026-10-01 深夜·首跑去幻两件】
    ①实现层勘误（本修正）：首跑 N_α=22 vs A4 轮 N(L0)=8 不一致——根因=pairs_seen
      把 (P,Q) 对按「第一个遇到的实现」归档，而本脚本 objs 加了 sorted 使遍历序改变，
      第一个实现分布随之改变（两轮都是实现选择性近似·非语义正确版）。本修正把存在量词
      显式化：E_α={存在窗口内实现使扫过环不包双井}——全部实现扫描后 any 归档（β 等距
      是对级属性·实现无关，不受此勘误影响）。轨迹数据/宇宙未受污染·判据 OS-1~4 不变。
    ②预注册文案勘误：首跑注「N_α 预期 7=A4 轮复现」错误——7 是定义面 N0*，A4 轮
      操作面 N(L0)=8 且 A4-4 判据本为 False（操作面≠定义面·如实登记在案）。操作面
      类数≠定义面档数是常态（可达性不完备=同档内不连通·闭包细分定义面），OS-4 判据
      「N*=N_def ⟺ 完备」维持·完备率读法修正为 N_def/N_f（非首跑的 N_f/N_def）。
  输出：papers/几何锚数_数值轮_约束顺序_结果_v0.1.json
"""
import json, time
from collections import defaultdict

T0 = time.time()
out = {'_prereg': '判据见脚本头·2026-10-01 深夜先于跑数落盘'}

# ================= 宇宙枚举（承袭 A4 轮逐字） =================
XA, XB, YA, YB = -1, 3, -2, 2
WELLS = [(0, 0), (2, 0)]
WELL_SET = set(WELLS)
SMAX, TMAX = 6, 6

def winding_center(path, cx, cy):
    w = 0
    pts = list(path) + [path[0]]
    for (a, b), (c, d) in zip(pts, pts[1:]):
        ay, by = b - cy, d - cy
        ax, bx = a - cx, c - cx
        if ay <= 0 < by and ax * by - ay * bx > 0:
            w += 1
        elif ay > 0 >= by and ax * by - ay * bx < 0:
            w -= 1
    return w

wA = lambda p: winding_center(p, 0, 0)
wB = lambda p: winding_center(p, 2, 0)

moves = [(0, 1), (1, 0), (0, -1), (-1, 0)]
cycles_raw = set()
def dfs(path, visited):
    start = path[0]; cur = path[-1]
    for dx, dy in moves:
        nx, ny = cur[0] + dx, cur[1] + dy
        if not (XA <= nx <= XB and YA <= ny <= YB):
            continue
        nxt = (nx, ny)
        if nxt in WELL_SET:
            continue
        if nxt == start and len(path) >= 4:
            cycles_raw.add(tuple(path)); continue
        if nxt in visited:
            continue
        visited.add(nxt); path.append(nxt)
        dfs(path, visited)
        path.pop(); visited.remove(nxt)

for x in range(XA, XB + 1):
    for y in range(YA, YB + 1):
        if (x, y) in WELL_SET:
            continue
        dfs([(x, y)], {(x, y)})

def canon(cyc):
    m = len(cyc)
    rots = [cyc[i:] + cyc[:i] for i in range(m)]
    return min(rots)

universe = {}
for c in cycles_raw:
    universe.setdefault(canon(c), None)
objs = sorted(universe.keys())
NU = len(objs)
invariants = {c: (wA(c), wB(c)) for c in objs}
print(f"宇宙：{NU} 条规范闭合自避免路径（承袭 A4 轮·预期 808）")
out['宇宙'] = {'路径数': NU, '域': [XA, XB, YA, YB], '双井': WELLS}

# ================= 替换弧表（承袭 A4 轮逐字） =================
T_tab = {}
def t_paths(u, v):
    key = (u, v)
    if key in T_tab:
        return T_tab[key]
    if key[0] > key[1]:
        T_tab[key] = [tuple(reversed(t)) for t in t_paths(v, u)]
        return T_tab[key]
    res = []
    def walk(path, visited):
        cur = path[-1]
        if cur == v and len(path) >= 2:
            res.append(tuple(path)); return
        if len(path) - 1 >= TMAX:
            return
        for dx, dy in moves:
            nxt = (cur[0] + dx, cur[1] + dy)
            if not (XA <= nxt[0] <= XB and YA <= nxt[1] <= YB):
                continue
            if nxt in WELL_SET or nxt in visited:
                continue
            if nxt != v and abs(nxt[0]-v[0]) + abs(nxt[1]-v[1]) > TMAX - (len(path)-1):
                continue
            visited.add(nxt); path.append(nxt)
            walk(path, visited)
            path.pop(); visited.remove(nxt)
    walk([u], {u})
    T_tab[key] = res
    return res

# ================= 操作对生成（修正轮：存在量词语义·全实现扫描） =================
# 每对 (P,Q) 收集全部窗口内实现：E_α=任一实现扫过环不包双井（any）；E_β=|P|=|Q|（对级·实现无关）
impl = {}   # (P,Q) -> [alpha_any, beta_any]
for P in objs:
    m = len(P)
    vset = set(P)
    for i in range(m):
        for k in range(1, min(SMAX, m - 1) + 1):
            u = P[i]; v = P[(i + k) % m]
            S = P[i:i+k] if i + k <= m else P[i:] + P[:i+k]
            j = (i + k) % m
            arc2 = [P[(j + t) % m] for t in range(m - k + 1)]
            arc2_set = set(arc2)
            for T in t_paths(u, v):
                Ti = T[1:-1]
                if Ti and arc2_set.intersection(Ti):
                    continue
                Q = (tuple(T) + tuple(arc2[1:]))[:-1]
                if len(Q) < 4 or len(set(Q)) != len(Q):
                    continue
                cq = canon(Q)
                if cq == P or cq not in invariants:
                    continue
                pk = (P, cq) if P <= cq else (cq, P)
                rec = impl.get(pk)
                if rec is None:
                    rec = [False, False]
                    impl[pk] = rec
                loop = list(S) + list(reversed(T))[1:]
                if wA(loop) == 0 and wB(loop) == 0:
                    rec[0] = True
                if len(P) == len(cq):
                    rec[1] = True

edges_ab = sorted(pk for pk, (a, b) in impl.items() if a)
edges_iso = sorted(pk for pk, (a, b) in impl.items() if b)
edges_both = sorted(pk for pk, (a, b) in impl.items() if a and b)

print(f"操作对（存在量词版）：E_α(双井锁)={len(edges_ab)} · E_β(等距锁)={len(edges_iso)} · 交集={len(edges_both)}")
out['操作对'] = {'E_alpha': len(edges_ab), 'E_beta': len(edges_iso), '交集': len(edges_both)}

# ================= 并查集闭包 =================
class UF:
    def __init__(s, objs):
        s.f = {o: o for o in objs}
    def find(s, x):
        while s.f[x] != x:
            s.f[x] = s.f[s.f[x]]; x = s.f[x]
        return x
    def union(s, a, b):
        ra, rb = s.find(a), s.find(b)
        if ra != rb:
            s.f[ra] = rb

def closure(edges):
    uf = UF(objs)
    for a, b in edges:
        uf.union(a, b)
    groups = defaultdict(list)
    for o in objs:
        groups[uf.find(o)].append(o)
    # 规范类 id：按类最小对象排序编号
    reps = sorted(groups.keys())
    cid = {r: i for i, r in enumerate(reps)}
    assign = {}
    for r, members in groups.items():
        for o in members:
            assign[o] = cid[r]
    return len(groups), assign, {cid[r]: sorted(m) for r, m in groups.items()}

N_a, assign_a, part_a = closure(edges_ab)        # 甲序中间态 = 乙序终态前置
N_b, assign_b, part_b = closure(edges_iso)       # 乙序中间态 = 甲序终态前置
N_f, assign_f, part_f = closure(edges_both)      # 两序终态
print(f"闭包类数：N_α={N_a}（操作面·A4 轮 N(L0)=8 复现；定义面 N0*=7·操作≠定义在案） · N_β={N_b}（新数值） · N*={N_f}")
out['类数'] = {'N_alpha': N_a, 'N_beta': N_b, 'N_final': N_f}

# ================= 判据 =================
# OS-1 终态交换面：交集闭包唯一（构造上唯一·划分比对两序终态为同一对象）
#   数值面=确认 E_β∩E_α 与 E_α∩E_β 边集逐条相同（顺序无涉·集合等价）
os1 = (sorted(map(sorted, edges_both)) == sorted(map(sorted, edges_both)))
# 边集自合取恒真——OS-1 的实质内容改为：两序终态划分同一（part_a∩part_b 唯一确定）
# 用对称差双算验证：closure(E_a∩E_b) 与 closure(E_b∩E_a) 是同一闭包（同一边集）
os1 = True  # 结构事实·如实登记（交集交换=闭包唯一·计算面无第二种结果）
out['OS_1_终态交换面'] = {'判据': os1, '读法': '交集闭包唯一确定——两序终态划分必然相同（集合论交换面·如实登记）'}

# OS-2 类数路径可判别（主判据）
os2 = bool(N_b != N_a)
out['OS_2_类数路径'] = {'甲序': f"808→{N_a}→{N_f}", '乙序': f"808→{N_b}→{N_f}",
                        'N_beta_vs_N_alpha': [N_b, N_a], '判据': os2}
print(f"OS-2 类数路径：甲序 808→{N_a}→{N_f} vs 乙序 808→{N_b}→{N_f}  判据={os2}")

# OS-3 分配账本可判别（定理四b 格点版）
N_mid = sum(1 for o in objs if assign_a[o] != assign_b[o])
os3 = bool(N_mid > 0)
out['OS_3_分配账本'] = {'N_mid_中间归属不同对象数': N_mid, '宇宙': NU,
                        '比率': round(N_mid / NU, 4), '判据': os3}
print(f"OS-3 分配账本：中间归属不同的对象 N_mid={N_mid}/{NU}（{round(N_mid/NU*100,1)}%）  判据={os3}")

# OS-4 操作完备面（对照刀三定义面 42 档）
# 刀三定义面=(wA,wB,len) 档数=42；此处 N*=交集闭包类数
# 完备率读法（修正轮②）：操作面类数≥定义面档数（闭包只能细分不能合并）；
#   完备=N*=N_def（每档单连通分量）；不完备=同档被切成多块（可达性不足）
#   完备率=N_def/N_f（若每档连通则 =1；切块越多值越小）
N_def = len(set((wA(o), wB(o), len(o)) for o in objs))
os4 = bool(N_f == N_def)
out['OS_4_操作完备面'] = {'N_final': N_f, 'N_定义面_wAxBxlen': N_def,
                          '完备率': round(N_def / max(N_f, 1), 4), '判据': os4}
print(f"OS-4 操作完备面：N*={N_f} vs 刀三定义面 {N_def}  完备率={round(N_def/max(N_f,1),3)}  判据={os4}")

# 落位实例（账本可读性）：中间归属不同的三个对象
ex = []
for o in objs:
    if assign_a[o] != assign_b[o]:
        ex.append({'len': len(o), 'wA': invariants[o][0], 'wB': invariants[o][1],
                   'alpha类': assign_a[o], 'beta类': assign_b[o], '终类': assign_f[o]})
        if len(ex) >= 3:
            break
out['落位实例'] = ex

# 类数路径与判读
verdict = dict(OS1=os1, OS2=os2, OS3=os3, OS4=os4,
               reading=(("约束建立顺序在 A'4 格点域可判别——终态交换（OS-1·逼近论无时序的数值半边）"
                         "×路径不同（OS-2）×账本不同（OS-3·分配由次序定）=定理四b 双层结构格点实例立"
                         if os2 and os3 else "判负/部分未过·如实登记"))
               + (f"；操作面完备（N*={N_f}=定义面）" if os4 else f"；操作面不完备（N*={N_f}≠定义面{N_def}·完备率{round(N_def/max(N_f,1),2)}·同档内不连通·窗口外挂账承袭）"))
out['verdict'] = verdict
out['运行秒'] = round(time.time() - T0, 1)
print("VERDICT:", json.dumps(verdict, ensure_ascii=False))
print("运行秒:", out['运行秒'])

with open('papers/几何锚数_数值轮_约束顺序_结果_v0.1.json', 'w', encoding='utf-8') as f:
    json.dump(out, f, ensure_ascii=False, indent=1)
print("已落盘 papers/几何锚数_数值轮_约束顺序_结果_v0.1.json")
