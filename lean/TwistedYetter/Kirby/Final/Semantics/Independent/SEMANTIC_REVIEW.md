# Final Theorem 語義審查流程

這份流程追蹤「人類究竟審過哪一個 exact Lean declaration」。它不是新的數學
semantics，也不把 proof fields 改名成另一套 assumptions package。

## 真相規則

- 人類核准只對被審查當時的 declaration SHA-256 有效。
- declaration 內任何 field、type、statement、proof 或註解改動，都會使該筆審查
  顯示為 `STALE`。這是刻意採用的保守策略。
- 聊天、舊 prose 與無 exact hash 的歷史紀錄不自動算作核准。
- structure 裡的資料、domain laws 與 kernel-checked certificates 分類保存，不因
  `#print axioms` 看不見它們便從 ledger 消失。
- `UNREVIEWED` 不代表錯誤；它只表示目前沒有可驗證的人工核准紀錄。

## 檔案

- `semantic-review-scope-v1.json`：Final Theorem 入口、核心 definitions、field
  分類，以及最後一次 kernel axiom closure 的來源。
- `semantic-review-ledger-v1.json`：由工具產生的 import closure、source locator、
  declaration hash 與人工審查狀態。
- `scripts/lean_semantic_review_ledger.py`：產生、檢查與記錄審查結果。

## 檢查

```bash
python3 scripts/lean_semantic_review_ledger.py check \
  --ledger lean/TwistedYetter/Kirby/Final/Semantics/Independent/semantic-review-ledger-v1.json
```

若 declaration 被新增、刪除或修改，檢查會失敗並列出 exact IDs。重新產生 snapshot
不會讓舊核准重新有效；其 reviewed hash 與新 hash 不同時仍是 `STALE`。

## 記錄人工核准

只有實際看完 exact declaration 後才可執行：

```bash
python3 scripts/lean_semantic_review_ledger.py review \
  --ledger lean/TwistedYetter/Kirby/Final/Semantics/Independent/semantic-review-ledger-v1.json \
  --declaration 'lean/path/File.lean::Full.Namespace.declaration' \
  --decision HUMAN_APPROVED \
  --reviewer 'reviewer-name' \
  --evidence 'review note, commit, or admitted CTL locator'
```

目前 baseline 刻意將所有項目設為 `UNREVIEWED`：現有環境無法 replay CTL current
root，因此不能可靠地把先前聊天中的「可以過」遷移成正式核准。
