# connect — R 上连通子集 = 区间 — Coq 形式化

实数线上"连通"与"区间（凸性）"的等价性形式化。

**状态**: **完全证明 — 0 Admitted，0 Axiom，0 Parameter**。
3 个主定理全部 `Qed`。本仓库中少数真正闭合的模块之一。

## 文件结构

| 文件 | 行数 | 内容 |
|---|---|---|
| `ConnectedSubset.v` | 325 | 连通子集、区间性质、双向等价（11 个声明） |
| `_CoqProject` | — | `-R <...>/rocq-stdlib.9.0.0/theories/ Stdlib` |

导入：Stdlib `Reals`, `Rtopology`, `Lra`, `RIneq`, `Raxioms`, `Classical`。

## 最重要的定理

1. **`connected_subset_interval_equiv`** — `ConnectedSubset.v:318`（**Qed**）
   `E ⊆ R` 连通 ⇔ `E` 满足区间（凸性）性质。目标定理。
2. **`interval_impl_connected`** — `ConnectedSubset.v:286`（**Qed**）
   区间 ⇒ 连通。Rudin 式论证：取区间与开集的最小交点。
3. **`connected_impl_interval`** — `ConnectedSubset.v:257`（**Qed**）
   连通 ⇒ 区间。
4. **`interval_open_sets_intersection`** — `ConnectedSubset.v:114`
   **已证**，约 140 行，整个文件体积的主体，也是 `interval_impl_connected`
   的全部技术工作所在。
5. **`interval_contains_closed_interval`** — `ConnectedSubset.v:81`（Qed）
6. **`Rabs_lt_between`** — `ConnectedSubset.v:42`（Qed）
7. **`open_set_lt` / `open_set_gt`** — `:53` / `:67`（Qed）
8. **`Rmin_pos_R`** — `:99`（Qed）

## 当前最大的困难

**无阻塞** — 全模块已闭合。剩余工作仅是工程性：

1. **无共享基础层**
   自包含开发，未复用 `theories/ZornsLemma` 或 `topology/` 的拓扑定义。
2. **`_CoqProject` 指向 opam 源码路径**
   硬编码了 `-R /Users/luoxing/.opam/default/.opam-switch/sources/
   rocq-stdlib.9.0.0/theories/ Stdlib`，换机器需改路径。
3. **目录卫生**
   本目录在 git 中以 **gitlink 记录（commit `5b5d211`），无 `.gitmodules`**，
   上游独立演进。
4. **可提升项**：`connected_subset_interval_equiv` 是当前唯一以 R 为底空间的
   连通性刻画；推广到 R^n（配合 `topology/`）尚未开始。

## 构建

```bash
cd connect
coqc -R /path/to/rocq-stdlib/theories/ Stdlib ...
coqc ConnectedSubset.v
```

## 相关

- R^n 紧致性与 Heine-Borel：`../topology/`
- 度量空间基础草稿：仓库根 `../analysis.v`
