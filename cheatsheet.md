# Connectives

| Name                    | Notation     | Introduction                      | Elemination    |
| ----------------------- | ------------ | --------------------------------- | -------------- |
| `bi_and`                | `P ∧ Q`      | `iSplit`                          |                |
| `bi_or`                 | `P ∨ Q`      | `iLeft`, `iRight`                 | `"[HP \| HQ]"` |
| `bi_sep`                | `P ∗ Q`      | `iSplitL`, `iSplitR`              | `"[HP HQ]"`    |
| `bi_wand`               | `P -∗ Q`     | `iIntros`                         | `iApply`       |
| `bi_pure`               | `⌜ ϕ ⌝`      | `"!%"`, `iPureIntro`, `iModIntro` | `%ϕ`           |
| `bi_exists`             | `∃ x : A, P` | `iExists`                         | `"[%x HP]"`    |
| `bi_forall`             | `∀ x : A, P` | `"%x"`, `iIntros (x)`             | `iApply`       |
| `bi_intuitionistically` | `□ P`        | `"!>"`, `iModIntro`               | `"#HP"`        |
| `bi_later`              | `▷ P`       | `"!>"`, `iNext`, `iModIntro`      | `">HP"`        |

