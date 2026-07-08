# AGENTS.md

## Communication

- 預設用繁體中文與使用者溝通；數學與技術術語可保留英文。

## Source of Truth

- Normative research state 以 CTL current graph、admitted objective notes 與
  machine-readable JSON artifacts 為準。
- 查詢 CTL current state 時，必須先用 current-read tooling replay current root，
  不可用 `rg` / `grep` / filesystem search 直接搜尋 `ctl-dogfood/` 來當答案來源。
  `rg` 只能作為 archaeology 或找檔案的輔助，不能取代 CTL current binding lookup。
- 舊 `twisted-yetter.org`、`legacy-archives/` 與其他 legacy prose 只作歷史 archive；
  不可當作 current state、roadmap、evidence 或 theorem source。
- 不要把重要研究內容只留在聊天、final answer、notebook 或散落 prose 裡。
  會影響未來判斷的內容應寫成 repo-local JSON artifact；必要時 admission 成
  CTL objective note / claim。

## Prose Policy

- 新的 experiment history、lab note、reference ledger、roadmap、working understanding、
  current status 與數學證據，不應寫成散落的 `.org` / `.md` / `.txt`。
- 允許的 prose 只限少數入口與規約檔，例如 `AGENTS.md`、工具 `README`。
  這些 prose 只作導覽，不是 normative record。

## Repo Map

- `ctl-dogfood/`：CTL object store、admission manifests、objective notes、policy claims。
- `ctl-dogfood/lab-notes/*.json`：objective lab-note preimage；admitted CTL claim
  才是 normative record。
- `experiments/`、`experiments/results/`：generated artifacts、JSON certificates、
  run logs、reproducible outputs。
- `experiments/inputs/`：machine-readable inputs，例如 Kirby / crossing / link data。
- `legacy-archives/`：舊 prose 的 faithful archive；只保存歷史 bytes。
- `src/`：穩定程式碼。
- `notebooks/`：探索用；重要結果穩定後要搬成 script + JSON artifact。

## New Agent Entry

1. 先讀本檔。
2. 驗證 CTL current root，並把後續 current-state 查詢建立在這個 replayed root 上：

   ```sh
   CTL_META_ROOT=/Users/jin/data/local/projects/ctl-meta \
   python ctl-dogfood/scripts/ctl_store.py verify
   ```

3. 查 current status / subject / lab note / claim 時，優先用：

   ```sh
   python ctl-dogfood/scripts/ctl_store.py lookup-current <logical-id>
   python ctl-dogfood/scripts/ctl_store.py list-current-bindings
   python ctl-dogfood/scripts/ctl_store.py search-current "<query>"
   python ctl-dogfood/scripts/ctl_store.py manifest-lookup --logical-id <logical-id>
   ```

   `lookup-current` 回傳 `current-ctl-object` 才可作為 current object 來源。
   `search-current` 的結果是 `current-discovery-only`，只能說明 active payload
   裡有命中；回答前仍要 inspect 對應 current object。
4. 查 decision graph 時，可讀 CTL current graph projection：

   ```sh
   CTL_META_ROOT=/Users/jin/data/local/projects/ctl-meta \
   python ctl-dogfood/scripts/show_current_graph.py --json
   ```

5. 不可用 `rg` / `grep` over `ctl-dogfood/lab-notes/`、`ctl-dogfood/objects/`、
   `ctl-dogfood/manifests/`、`ctl-dogfood/graphs/` 來回答 current-state 問題；
   舊 payload、loose preimage、inactive manifest 命中都不能提升成 current truth。
6. 查舊 prose 歷史時，先讀 `legacy-archives/*.manifest.json`，再按需解包；
   archive prose 不可提升為 normative source。
7. 跑 code 前讀 `pyproject.toml`、`flake.nix`、`uv.lock` 與相關 JSON artifacts。

## Objective Notes / Artifacts

重要 objective note 或 generated artifact 至少應記錄：

- 日期、目的、狀態標籤。
- git commit 與 dirty 狀態。
- 環境、工具版本、reproduce command。
- 輸入來源，例如 Kirby diagram、category data、文獻頁碼、reference record。
- 輸出 artifact 路徑與 hash / git blob hash。
- sanity checks，例如 linking matrix、signature、Euler characteristic、handle count、
  `alpha=0` ordinary invariant、handle-slide consistency。
- failure / inconclusive 結果，避免未來 agent 重複踩坑。

Generated JSON artifact 頂層應盡量包含 `schema`、`status`、`generator_script`、`argv`、
`reproduce_command`、UTC start/finish、elapsed seconds、repo root、git commit、
dirty flag、tool versions。

## References / Evidence

- 文獻、PDF、web page、arXiv、local snapshot、email、generated certificate 都應有
  repo-local JSON reference record 或 CTL objective note。
- 正文優先引用 `ref:<short-id>`，不要只寫 URL 或絕對路徑。
- Reference record 應保存 canonical metadata、capture time、locator、content hash
  或 git blob hash。
- 引用文獻命題時必須附 page / theorem / proposition / definition 編號。
  尤其是 Yetter definition、normalization、surgery formula、Kirby move proof，
  不可憑記憶轉述。

## Reproducibility

- Python dependencies 優先用 `uv`。
- 需要 SageMath、Typst、LaTeX、system packages 或固定工具版本時，優先用 `nix`
  或清楚記錄 Nix shell / flake 路線。
- Sage 預設使用 repo-local cache：

  ```sh
  DOT_SAGE="$PWD/.sage" sage --python ...
  ```

- 預設接受 floating-point arithmetic；不要隨便改用 exact arithmetic。
  只有在需要 machine-checkable proof、正式 certificate，或必須排除數值誤差時，
  才使用 exact arithmetic、cyclotomic field、minimal polynomial comparison 等方法。

## Long-running Computation / Tests

- 若 computation 或 test 可能遇到很久的節點，不要直接跑單一大型 job。
- 先拆成許多 very small、可獨立重跑、可逐步驗證的 chunks，再 aggregate 結果。
- 每個 chunk 應留下足夠 metadata，使失敗時不必重跑全部工作。

## Mathematical Status

- 所有 notes / artifacts 應清楚標示狀態，例如 `ESTABLISHED`、`INFERENCE`、
  `CONJECTURAL`。
- 不得把 conjecture、heuristic、numerical coincidence 或 legacy prose 寫成 theorem。

## Git / Working Style

- 不要刪除或重寫使用者未要求改動的資料。
- 大型研究步驟開始前，先留下 JSON artifact / objective note，或更新 CTL graph。
- Commit 應對應可理解、可重現的研究狀態，例如 environment scaffolding、
  reference matrix、diagram data、calculation artifact、theory note。
- 新增重要 artifact 時，盡量同時新增 JSON reference record，或在 objective note
  中建立可追溯引用。
- Always merge with no-ff. 除非你強烈覺得不應該這麼做，那你停下來問使用者。
- 每次要修改本檔 AGENTS.md 時，必須要重複和使用者確認。
