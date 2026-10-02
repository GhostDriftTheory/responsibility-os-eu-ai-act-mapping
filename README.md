# Responsibility OS × EU AI Act

**Repository:** `GhostDriftTheory/responsibility-os-eu-ai-act-mapping`

Selected formal assurance profiles for Articles **11, 12, 14, 19, 43 and 72**, built
on the unchanged [Responsibility OS Kernel](https://github.com/GhostDriftTheory/responsibility-os-kernel).
One theory file connects a recorded decision to its context, documentation,
retention policy, inspectable evidence and versioned monitoring plan.

**Verification status:** the delivery environment could not run Lean. A passing
build is **not** claimed in advance. The `Lean verification / verify` Actions
result for the exact commit is the authority for this repository's build and
axiom-audit status. GitHub Actions has not been run on the user's account as part
of this delivery.

## Five files; no kernel changes

```text
EUAIActMapping.lean           # All application definitions, proofs and examples
lakefile.toml                # Exact external kernel/mathlib revisions
lean-toolchain               # Lean 4.26.0
README.md                    # Scope, article mapping and setup
.github/workflows/lean.yml   # Build, strict source check and theorem-axiom audit
```

`import ResponsibilityOS` imports the external kernel; no copied or modified
kernel is bundled. Additional disclosure is limited to public context/version
keys, a logical allow/withhold/stop gate, recorded events, deadline filtering,
document/plan binding and a lossless monitoring partition. No private ADIC
implementation, certificate-checker internals or physical controller is included.

## What the mapping establishes

Article numbers identify **selected technical contributions**, not proofs that an
entire article or a deployed AI system is legally satisfied. All declaration
names below are prefixed by `EUAIActMapping.`.

| Reference | Formal contribution | Main declarations |
|---|---|---|
| [Art.11(1)](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-11) | Evidence and document metadata must match the current context; a different document version fails the support check. The document identifies its monitoring-plan version. | `Art11.document_binding_is_exact`, `Art11.stale_document_is_rejected` |
| [Art.12(1)–(2)](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-12) | Every reference transition records an outcome and preserves previous records. Kernel tracing retains operations and supplied policy distinctions. | `Art12.every_step_is_recorded`, `Art12.standard_trace_preserves_policy` |
| [Art.14(4)(d)–(e)](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-14) | A logical stop dominates readiness; withholding prevents execution; execution requires current context and an allow request. | `Art14.stop_always_halts`, `Art14.execution_requires_current_context` |
| [Art.19(1)](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-19) | The reference filter retains recorded events through their supplied retention deadlines. | `Art19.no_early_deletion`, `Art19.fresh_record_survives_pruning` |
| [Art.43](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-43) | An export with a proved left inverse preserves required evidence distinctions; the kernel supplies structural backward-audit factorization. | `Art43.recoverable_export_preserves_policy`, `Art43.backward_audit_factorization` |
| [Art.72(1)–(3)](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-72) | Monitoring is bound to a current document and its referenced plan. Every supplied record is classified once; repeated occurrences are counted. Version/context mismatches and failed checks trigger review. | `Art72.monitoring_complete`, `Art72.monitoring_preserves_occurrences`, `Art72.unmatched_plan_flags_all`, `Art72.outdated_document_flags_all` |

### Strengthening Articles 11 and 72

`Art11.Documentation` explicitly binds document metadata to `Context` and records
`monitoringPlanVersion`. `Context.documentation` already identifies the document
version; it is reused rather than duplicated. The support check rejects a document
whose version is not the current profile's version. An old record can still be
valid evidence for its **historical** context; the check prevents silent reuse as
current evidence.

`Art72.MonitoringPlan` adds only its context, version and supplied check.
`passesPlan` checks the plan against the current profile and the document's plan
reference, checks the document/event/profile binding, then applies that check.
`normalRecords` and `reviewRecords` form an exhaustive, mutually exclusive
classification of the **supplied history**, with occurrence-count preservation.
Even an always-true supplied check cannot clear records under a mismatched plan
version or outdated document. “Normal” means this selected profile's checks
passed, **not** that the system is safe or legally compliant.

These are public reference-model checks, not an implementation of the document's
contents or a claim that its version identifiers are authentic. The new document
check is used for evidence support and monitoring; it does **not** add a separate
production document-loading gate to `advance`.

### One evidence chain

`evidence_chain` uses **one captured record** for document/context consistency,
recording/retention, necessary execution permission, policy-preserving export,
exclusive monitoring classification and review on a failed supplied check.
It has explicit event/document-context, retention and export-round-trip premises.
It does **not** assume the monitoring plan version matches: mismatches result in
review. The strengthened theorem takes document and plan arguments; the older
`Art72.reviewQueue` helpers remain available, but the integrated theorem now uses
the plan-bound partition.

The original positive witness uses the kernel's nonempty `traceA`/`traceB`
relevance policy. Its negative witness shows that an operation-only view loses
that distinction. An empty policy is not treated as evidence of coverage.

## GitHub setup — 日本語

新しいリポジトリ名は **`responsibility-os-eu-ai-act-mapping`** です。
ZIPを解凍し、上記5ファイルをフォルダ構造のままリポジトリ直下に置いてください。
**ZIPそのものをアップロードするのではありません。** `EUAIActMapping.lean` と
`lakefile.toml` が直下にあり、ワークフローが必ず
**`.github/workflows/lean.yml`** にある状態にします。

Actionsが有効なら、push・pull requestで `Lean verification` が実行されます。
手動実行は **Actions → Lean verification → Run workflow** です（ワークフローを
既定ブランチに配置した後に利用できます）。公開Kernelの取得に
専用トークンやSecretsの設定は不要です。所属組織でActionsが制限されている場合は、
使用するActionsの許可が必要です。

`verify` 全体の成功が、ビルド・直接ソース検査・全定理の公理監査の合格です。
**ビルドのステップだけが成功しても、検証全体の合格ではありません。**
結果と依存関係の確定値は実行画面のArtifactsに保存されます。
失敗時はその実行ログが正本です。未実行・失敗状態を「Lean検証済み」と表示しないでください。

実際のLeanコンパイルは、この作成環境では実行できていません。
YAML・設定・監査スクリプトの確認は、Leanコンパイルの代替ではありません。

## Verification details

The workflow uses the official [Lean Action](https://github.com/leanprover/lean-action)
to install the toolchain, obtain mathlib's cache and build the named library.
It then checks the source with warnings as errors and uses `#print axioms` on
**every named mapping theorem**, including its transitive proof dependencies.
Proof gaps, custom axioms, `native_decide` and `unsafe` in the mapping source are
rejected. Only Lean's standard `propext`, `Classical.choice` and `Quot.sound` are
allowed as theorem axiom dependencies. Theorem parameters remain assumptions;
this audit does not turn them into proved deployment facts.

The auditor is embedded in the workflow to avoid a separate `check.py`. A temporary
Lean audit file, logs, `report.json` and `lake-manifest.json` are generated only at
verification time; they are not additional required source files. The report
records the repository commit, source SHA-256, resolved dependencies and theorem
axioms. It emits `LEAN_BUILD_AND_AXIOM_AUDIT_PASSED` only after all its checks pass.
The source contains no string literals outside comments; the small auditor fails
closed if future source changes introduce them rather than silently misparsing.

The core dependency revisions are fixed in `lakefile.toml`:

- Kernel: `9b4e7d25572f3a1e114508bdf1a2d62349e83993`.
- mathlib: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).
- Toolchain: `leanprover/lean4:v4.26.0`.

The kernel commit was obtained from the upstream [commit history](https://github.com/GhostDriftTheory/responsibility-os-kernel/commits/main/).
Its [Lake configuration](https://github.com/GhostDriftTheory/responsibility-os-kernel/blob/main/lakefile.lean)
requires mathlib v4.26.0; the mathlib pin identifies the corresponding
[release](https://github.com/leanprover-community/mathlib4/releases/tag/v4.26.0).
This is an explicit dependency baseline, not a promise to follow the latest upstream commit.
Transitive revisions are resolved by Lake and recorded in the generated manifest;
save the CI artifact to reproduce the exact resolved environment. To update a
baseline intentionally, change both `lakefile.toml` and the workflow's expected
revisions, then re-run verification. No manual pin editing is needed for initial setup.

For a local **build and source check**, install Git and
[elan](https://github.com/leanprover/elan), then run:

```sh
lake update
lake exe cache get
lake build EUAIActMapping
lake env lean -DwarningAsError=true EUAIActMapping.lean
```

These commands alone do not perform the extra axiom audit; the supplied GitHub
workflow performs that audit. Do not upload locally generated `.lake/` or compiler
outputs as source files.

## Interpretation and deployment boundary

The legal-to-formal interpretation is external. The baseline is the selected
technical subject matter of Regulation (EU) 2024/1689, as originally adopted,
not a version-certified map of every current amendment. As consulted on
**2 October 2026**, the Commission's Article 11 and 72 pages display amendment/update
notices. Consult the applicable official consolidated text for a deployment.
No application dates, conformity-assessment route or calendar-month conversion
are encoded here. [Annex IV](https://ai-act-service-desk.ec.europa.eu/en/ai-act/annex-4)
contains document-content requirements beyond this metadata model.

The model does not establish complete technical documentation, complete real-world
event capture, authentic version keys, suitable risk checks, correct retention
deadlines, durable storage, usable human interfaces, actual safe stopping or
organizational follow-up. History partitioning does not prove active collection
of events that were never supplied. Exact context equality is a conservative
reference policy, not a claim that the Act requires this exact data structure.

The kernel's faithfulness is not automatic logging, and its unique backward-audit
factorization is not executable replay. The logical `executed` outcome is not a
claim of physical execution. Actual deployment must prevent gate bypass, bind
authentic inputs to the model and connect logical stop to a justified safe-state
mechanism. Article 43 mapping supports inspectable assessment evidence; it does
not perform conformity assessment or assume that every assessment uses a third
party. These are limits of this **minimal public profile**, not limits on the
scope of Responsibility OS or its possible applications.
