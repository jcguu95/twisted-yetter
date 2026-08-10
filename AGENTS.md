# AGENTS.md

## 溝通

- 只用繁體中文與使用者溝通；數學符號、程式碼與必要的技術名稱可保留原文。

## 研究真相來源

- Normative research state 只以 CTL current graph、admitted objective notes 與
  machine-readable JSON artifacts 為準。
- 查詢 current state 前，必須先以 `ctl_store.py verify` replay CTL current root；
  再以 `lookup-current`、`list-current-bindings` 或其他 current-read tooling 查詢。
- `rg`、filesystem search、loose preimage、legacy prose、聊天與舊 payload 只能用於
  archaeology，不得提升為 current truth、evidence 或 theorem。
- 會影響未來判斷的研究內容必須保存為 repo-local JSON artifact；必要時正式
  admission 成 CTL objective note 或 claim，不得只留在聊天、notebook 或散落 prose。

## 誠實與證據

- 嚴格區分 `ESTABLISHED`、`INFERENCE`、`CONJECTURAL`、`INCONCLUSIVE` 與
  `BLOCKED`；不得把 conjecture、heuristic、numerical coincidence 或未完成計算
  寫成 theorem。
- Formal claim 必須明列 exact scope、equivalence sense、denominator、未涵蓋範圍與
  non-claims。缺資料或證書時必須 fail closed，不得猜測、跳過或 silent fail。
- 引用外部結果必須有可追溯 reference record，並標示 page、theorem、proposition
  或 definition locator；不得只憑記憶轉述。
- 錯誤、過時或只在有限範圍安全的 reusable resource，必須留下明確的 safety status。

## 長計算

- 長計算不得直接以 monolithic job 開跑；必須先拆成 atomic、restartable、
  checkpointed chunks。
- 依 difficulty ranking 將 chunks 分成 10 個 deciles；全面部署前，先跑每個
  decile 中最難的 sentinel。
- Sentinel 必須用來估算 worker-hours、wall time、peak memory 與 artifact size；
  只有確認最壞 chunk 可控後，才能全面部署。
- 執行期間必須持續校正 difficulty ranking、每類成本與剩餘 worker-hours。若
  sentinel 爆掉，立即回報並進一步細分 chunk，不得盲目續跑。
- 必須持續收割並驗證完成的 artifacts；completed chunks 絕不重跑，除非其 hash、
  provenance 或 validator 明確失效。
- 每次計算必須明確封閉一個 mathematical obligation，並完整保存 provenance 與
  reproducibility metadata：timestamp、context、git commit、dirty state、輸入與輸出
  hashes、reproduce command、execution environment，以及 Python、Sage、Julia、Lean、
  OS 與其他相關工具版本。

## 本機資源

- 本機同時最多執行 2 個 Lean processes。若其他 project 正在使用 Lean，本 project
  最多只能執行 1 個；啟動前與結束後都必須檢查 process table，且不得碰觸其他
  project 的 process。
- 不得自行編譯 Mathlib；使用已下載的 toolchain、cache 或 binary artifacts。

## Git 與變更控制

- 除 `AGENTS.md` 與 `paper/` 外，不得新增 prose-only 純文字檔（如 `.txt`、`.tex`、`.md`、`.org`）。
- 不得刪除、覆寫、revert 或重排使用者及其他 agent 的既有改動；只能處理本任務
  必要範圍。不得使用 destructive Git commands。
- Commit 必須對應單一、可理解、可驗證且可重現的研究狀態。Merge 一律使用
  `--no-ff`；若不適合，先停下來詢問使用者。
- 修改本 `AGENTS.md` 前，必須取得使用者至少三次明確確認；兩次不夠。
