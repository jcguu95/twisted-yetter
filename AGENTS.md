# Codex / Agent 交接規則

這份文件是給未來研究代理的 repo-local 工作規約。它不取代
`twisted-yetter.org` 的研究計畫，而是說明在這個 repo 中應該如何溝通、記錄、
保存證據、管理可重現環境，以及避免把猜想誤寫成定理。

## 語言與溝通

- 預設主要使用繁體中文與使用者溝通，因為使用者閱讀繁中明顯較快。
- 數學、拓撲、category theory、TQFT、Kirby calculus、程式與工具鏈術語可保留英文；
  不要為了翻譯而犧牲精確性。
- 若英文原詞是文獻中的固定術語，第一次可用「繁中說明 + English term」並列，之後可直接使用英文術語。
- 對研究狀態要明確使用狀態語言，例如：
  `working understanding`、`computed evidence`、`conjectural`、
  `non-formal proof sketch`、`certificate-level observation`、`proved in source`。

## 專案目標

本 repo 研究 homologically twisted Crane-Yetter / Yetter invariant，尤其是帶
`H_2` marking 或 `K(A,2)` background 的版本是否可能偵測 exotic smooth
4-manifolds。

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

## Lab Notes 與 repo 結構

本 repo 應採用類似 `/Users/jin/data/local/projects/VOA-computation/` 的長期研究記錄方式：

- `wiki/`：主要 human-readable 研究 wiki。
- `wiki/index.org`：入口與讀取順序。
- `wiki/lab-notes/YYYY-MM-DD.org`：日期式 lab notes。記錄當天做了什麼、為何做、
  使用哪些 artifact、得到什麼、哪些事情失敗或仍不確定。
- `wiki/understandings/`：穩定下來的 working understanding，不要塞進每日流水帳。
- `wiki/roadmaps/`：可變動的研究路線、go/no-go tree、sprint plan。
- `wiki/env/reproducibility.org`：環境、工具版本、重現指令。
- `wiki/references/`：文獻、PDF、網頁快照、外部路徑、generated artifacts 的 metadata records。
- `research_graph/`：若研究分支變多，建立 current-view overlay，幫未來 agent 不必讀完整歷史。
- `experiments/` 或 `results/`：generated artifacts、JSON certificates、run logs。
- `src/`：穩定程式碼。
- `notebooks/`：探索用；重要結果穩定後要搬成 script + artifact，不要只留 notebook。

新的重要研究紀錄不要只放在 final answer 或聊天記憶裡。能影響未來判斷的內容應寫入
repo-local org / artifact。

## Lab Note 最低內容

每篇重要 lab note 至少應包含：

- 日期、目的、狀態標籤。
- 當前 git commit 與 dirty 狀態。
- 使用的環境與工具版本，或指向 `wiki/env/reproducibility.org`。
- 重現指令，包含 `uv` / `nix` / `sage` / exact arithmetic backend。
- 輸入資料來源，例如 Kirby diagram、category data、文獻頁碼、reference record。
- 輸出 artifact 路徑與 hash / git blob hash。
- sanity checks，例如 linking matrix、signature、Euler characteristic、handle count、
  `alpha=0` 是否回到 ordinary invariant、handle-slide 前後是否一致。
- 明確的 failure / inconclusive 記錄，避免未來 agent 重踩同一條路。

## References 與 Evidence

- 外部文獻、PDF、web page、arXiv、local file snapshot、email、generated certificate 都應建立
  repo-local reference record。
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

- `twisted-yetter.org` 中的 `ESTABLISHED`、`INFERENCE`、`CONJECTURAL UNTIL PROVED`
  分層要延續到所有筆記。
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
2. 讀 `twisted-yetter.org` 的核心研究計畫。
3. 若 `wiki/index.org` 存在，照它的讀取順序走。
4. 若 `research_graph/current_view.json` 存在，先讀 current view，再讀 active nodes。
5. 若要回答 current-status 問題，不要只 grep 歷史 lab notes；先找 current-view / status artifact。
6. 若要跑 code，先讀 `wiki/env/reproducibility.org` 或 `pyproject.toml` / `flake.nix` / `uv.lock`。

## Git 與工作方式

- 不要刪除或重寫使用者未要求改動的資料。
- 對大型研究步驟，先留下 lab note 或更新 roadmap，再開始長時間 computation。
- Commit 應該對應一個可理解的研究狀態：環境 scaffolding、文獻矩陣、diagram data、
  calculation artifact、theory note 等。
- 若新增重要 artifact，盡量同時新增 reference record 或在 lab note 中建立可追溯引用。
