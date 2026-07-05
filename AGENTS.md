# Codex / Agent 交接規則

現行 normative research state以 CTL current graph、admitted objective notes 與
machine-readable JSON artifacts為準；舊 `twisted-yetter.org` 只作為 legacy
archive material。本文說明在這個 repo中應該如何溝通、記錄、保存證據、管理可重
現環境，以及避免把猜想誤寫成定理。

## 語言與溝通

- 預設用繁體中文與使用者溝通, 術語可以用英文。

## 專案目標

本 repo 研究 homologically twisted Crane-Yetter / Yetter invariant，尤其是帶
`H_2` marking 的版本是否可能偵測 exotic smooth 4-manifolds。

理想的 positive outcome 是：

1. 找到一組已知 orientation-preservingly homeomorphic but non-diffeomorphic 的
   closed smooth 4-manifold pair；
2. 建立可審計的 `H_2` marking / homeomorphism comparison；
3. 用 twisted Yetter invariant 的 exact calculation 證明兩邊不同；
4. 排除 normalization、basis artifact、diagram artifact、浮點誤差與 marking 混淆。

若 twisted Yetter 對 exotic pair 註定失敗，本 repo 仍應產出有價值的結果：

- decorated Reutter-style no-go theorem 或清楚的 obstruction audit；
- 對許多 known exotic pairs / known categories 的 systematic negative evidence；
- 一般 decorated Kirby formula 的成立範圍或失敗點；
- semisimple / modular / premodular / non-semisimple 路線的分類式篩選；
- 可重現的 Kirby-diagram、category-data、Fourier-sector、exact-arithmetic 工具鏈。

不要把「Reutter 原文沒有直接涵蓋 decorated theory」寫成「已繞過 Reutter」。
真正要研究的是 decorated stabilization behavior。

## CTL Objective Notes 與 repo 結構

本 repo 的實驗歷史、lab note、reference record、roadmap、working understanding
不可再寫成散落的 `.org` / `.md` / `.txt` prose 檔。這些內容必須寫成
machine-readable JSON artifact，並在重要時透過 `ctl-dogfood` admission 成為 CTL
objective lab note / claim。

允許存在的 prose 檔只限極小白名單，例如本檔 `AGENTS.md` 與少數工具入口
`README`。白名單 prose 只用於人類入口、工具導覽或 agent 規約；它們不是
experiment history、lab note、reference ledger、roadmap、working understanding
或數學證據來源。

- `ctl-dogfood/`：CTL object store、admission manifests、objective notes、policy claims。
- `ctl-dogfood/lab-notes/*.json`：objective lab-note preimage；admitted 後的 CTL claim
  才是 normative record。
- `experiments/` / `experiments/results/`：generated machine artifacts、JSON certificates、
  run logs 與 reproducible outputs。
- `experiments/inputs/`：machine-readable inputs，例如 Kirby/crossing/link data。
- `legacy-archives/`：舊 human prose 的 faithful archive（tar + manifest）。archive
  只保存歷史 bytes，不提升內容為 normative source。
- `src/`：穩定程式碼。
- `notebooks/`：探索用；重要結果穩定後要搬成 script + JSON artifact，不要只留 notebook。

新的重要研究紀錄不要只放在 final answer 或聊天記憶裡。能影響未來判斷的內容應寫入
repo-local JSON artifact，必要時用 `ctl-dogfood/scripts/admit_claim.py` admission 成
CTL objective note。

## Objective Lab Note 最低內容

每篇重要 objective lab note / artifact 至少應包含：

- 日期、目的、狀態標籤。
- 當前 git commit 與 dirty 狀態。
- 使用的環境與工具版本，或指向 machine-readable reproducibility artifact。
- 重現指令，包含 `uv` / `nix` / `sage` / exact arithmetic backend。
- 輸入資料來源，例如 Kirby diagram、category data、文獻頁碼、reference record。
- 輸出 artifact 路徑與 hash / git blob hash。
- sanity checks，例如 linking matrix、signature、Euler characteristic、handle count、
  `alpha=0` 是否回到 ordinary invariant、handle-slide 前後是否一致。
- 明確的 failure / inconclusive 記錄，避免未來 agent 重踩同一條路。

## References 與 Evidence

- 外部文獻、PDF、web page、arXiv、local file snapshot、email、generated certificate 都應建立
  repo-local JSON reference record 或 CTL objective note。
- 正文優先引用 `ref:<short-id>`，不要只寫 URL 或絕對路徑。
- reference record 應保存 canonical metadata payload、capture time、locator、content hash
  或 git blob hash。
- 文獻命題必須附來源頁碼 / theorem / proposition / definition 編號。尤其是 Yetter 原文的
  definition、normalization、surgery formula、Kirby move proof，不可只憑記憶轉述。

## 可重現環境

- 優先使用 `uv` 管理 Python dependencies。
- 若需要 SageMath、Typst、LaTeX、system packages 或特定工具版本，優先用 `nix` 或清楚記錄
  Nix shell / flake 路線。
- 若使用 Sage，預設採用 repo-local cache：

```sh
DOT_SAGE="$PWD/.sage" sage --python ...
```

- 重要 generated artifacts，尤其是 `experiments/data/**/*.json`，應在 artifact 頂層保存：
  `schema`、`status`、`generator_script`、`argv`、`reproduce_command`、UTC start/finish、
  elapsed seconds、repo root、git commit、dirty flag、tool versions。
- 浮點近似只能作為 debug / exploration。正式「兩值不同」必須回到 exact arithmetic、
  cyclotomic field、minimal polynomial comparison，或其他可審計 certificate。

## 數學信任邊界

- 舊 `twisted-yetter.org` 已屬 legacy prose archive。它可作歷史材料，但不是當前
  normative research plan；當前狀態以 CTL current graph、objective notes 與 JSON
  artifacts 為準。
- `ESTABLISHED`、`INFERENCE`、`CONJECTURAL UNTIL PROVED` 等分層要延續到所有
  objective notes / artifacts。
- 候選 formula
  `Omega_a = sum_i d_i lambda_i(a) X_i`
  在一般 category 中是待證命題，不是可直接使用的定理。
- Kirby formula 必須逐項處理 handle slide、1/2 cancellation、2/3 cancellation、
  basis change、orientation convention、normalization、signature anomaly 與 implicit
  3-handles。
- 若只證明 2-handlebody invariant，不可宣稱已得到 closed 4-manifold invariant。
- exotic detection 的宣稱至少要分清：
  marked distinction、cork-canonical distinction、unmarked total-function distinction、
  orbit / multiset distinction。
- modular 或 low-rank semisimple categories 先視為 negative controls；不要因為第一個
  example 沒差異就宣稱整個 theory 無效。

## 計算與資料原則

- Kirby diagrams 必須 machine-readable：PD code、braid word、component IDs、framings、
  dotted status、orientation、basis-change matrices。
- 每次 handle slide / simplification 都要保存整數 basis matrix 與 component lineage。
- 對 exotic pair，必須能重建 intersection form、signature、Euler characteristic、
  `H_2` identification matrix。
- 不要對每個 decoration 重算整個 link evaluation；優先建立 sector amplitudes，再用
  finite Fourier transform。
- 對 `SU(2)_2`、`S^4`、`CP^2`、`S^2 x S^2`、handle-slide toy examples 建立小型測試後，
  再進入 Dolgachev / R8 等大型 pair。
- 若 computation 失敗或超時，保存 run log、輸入、已完成 partial sectors 與下一步建議。

## 建議讀取順序

新 agent 進入 repo 時：

1. 讀本檔 `AGENTS.md`。
2. 用 `CTL_META_ROOT=/Users/jin/data/local/projects/ctl-meta python ctl-dogfood/scripts/show_current_graph.py --json`
   讀 CTL current graph。
3. 若要找舊 prose 歷史，只讀 `legacy-archives/*.manifest.json`，再按需解包 archive；
   不要把 archive prose 當 normative source。
4. 若要回答 current-status 問題，先找 CTL current graph / admitted objective notes /
   status artifacts，不要依賴 legacy prose。
5. 若要跑 code，先讀 `pyproject.toml` / `flake.nix` / `uv.lock` 與相關 JSON artifacts。

## Git 與工作方式

- 不要刪除或重寫使用者未要求改動的資料。
- 對大型研究步驟，先留下 CTL objective note / JSON artifact 或更新 CTL graph，再開始長時間 computation。
- Commit 應該對應一個可理解的研究狀態：環境 scaffolding、文獻矩陣、diagram data、
  calculation artifact、theory note 等。
- 若新增重要 artifact，盡量同時新增 JSON reference record 或 objective note 中建立可追溯引用。
