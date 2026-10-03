# Responsibility OS × EU AI Act

[![Lean verification](https://github.com/GhostDriftTheory/responsibility-os-eu-ai-act-mapping/actions/workflows/lean.yml/badge.svg)](https://github.com/GhostDriftTheory/responsibility-os-eu-ai-act-mapping/actions/workflows/lean.yml)


**Repository:** `GhostDriftTheory/responsibility-os-eu-ai-act-mapping`

Selected formal assurance profiles for Articles **11, 12, 14, 19, 43 and 72**, built
on the unchanged [Responsibility OS Kernel](https://github.com/GhostDriftTheory/responsibility-os-kernel).
One theory file connects recorded decisions to their context, documentation,
retention policy, inspectable evidence and versioned monitoring plan. Its
history-wide result compares interleaved execution/pruning/profile changes
with an execution that retains the full history until the final audit.

**Verification status:** CI builds `EUAIActMapping.lean` with Lean 4.26.0 and checks
its source with warnings treated as errors. The badge links to the workflow;
the `Lean verification / verify` result for the **exact commit** is authoritative.
Treat a revision as machine-checked only when both `Build mapping` and
`Verify source with warnings as errors` succeed for that revision. A successful
run for an earlier revision does not certify newly changed files.


## Five files; no kernel changes

```text
EUAIActMapping.lean           # All application definitions, proofs and examples
lakefile.toml                # Exact external kernel/mathlib revisions
lean-toolchain               # Lean 4.26.0
README.md                    # Scope, article mapping and setup
.github/workflows/lean.yml   # Build and strict source verification
```

`import ResponsibilityOS` imports the external kernel; no copied or modified
kernel is bundled. Additional disclosure is limited to public context/version
keys, a logical allow/withhold/stop gate, recorded events, deadline filtering,
document/plan binding, a lossless monitoring partition and a sequence runner over
these same reference operations. No private ADIC
implementation, certificate-checker internals or physical controller is included.

## What the mapping establishes

Article numbers identify **selected technical contributions**, not proofs that an
entire article or a deployed AI system is legally satisfied. All declaration
names below are prefixed by `EUAIActMapping.`.

The table separates the **legal requirement**, **our reference design choice**,
**the formal proposition** and **what still needs external assessment**.
Requirements are paraphrased from the selected subject matter of the original
[Regulation (EU) 2024/1689](https://eur-lex.europa.eu/eli/reg/2024/1689/oj/eng),
not a claim to encode every subsequent amendment. Article links lead to the
Commission's Service Desk; its update notices must be read with the text.

| Legal source and selected requirement | Reference predicate / design rationale | Lean declarations | Outside this profile |
|---|---|---|---|
| [Art.11(1)](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-11): prepare technical documentation before placing on the market or putting into service, and keep it current. | `Art11.supportsRecord` binds document, event and profile context, preventing use of mismatched documentation as current support. Exact key equality is our conservative implementation choice, not statutory wording. | `Art11.document_binding_is_exact`, `Art11.stale_document_is_rejected`; the normal-record implication in `history_evidence_chain`. | Document preparation timing, authenticity, actual contents, Annex IV completeness and legal sufficiency. |
| [Art.12(1)–(2)](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-12): enable automatic event logging over the system lifetime, including events useful for monitoring and risk-related traceability. | `advance` records every supplied attempt. `History.SameAt` relates an interleaved run to a full-history reference run, so retention processing cannot silently change the final live sequence. | `Art12.every_step_is_recorded`, `Art12.standard_trace_preserves_policy`, `History.run_without_pruning`. | Completeness of real event capture, whether recorded fields cover relevant risks, biometric-specific requirements and durable storage. |
| [Art.14(4)(d)–(e)](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-14): enable the assigned person to disregard/override/reverse outputs and to intervene or stop safely, as appropriate. | `gate` gives logical stop priority and prevents execution after withholding. `History.Permission` refers to the context recorded at execution; profile changes do not restart a stopped controller. | `Art14.withhold_never_executes`, `Art14.stop_always_halts`, `History.run_permission`, `History.stopped_run_stays_stopped`. | Human identity/authority, usability, competence, reversal of physical effects and actual safe stopping. The no-restart policy is our reference choice. |
| [Art.19(1)](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-19): retain provider-controlled automatic logs for the applicable purpose-appropriate period, with a six-month minimum unless applicable law provides otherwise. | `Art19.pruneExpired` applies an externally justified deadline. `History.CutoffsWithin` excludes deletion using a cutoff later than the final audit time. | `Art19.no_early_deletion`, `History.prune_twice`, `History.run_without_pruning`, `History.future_cutoff_counterexample`. | Selecting lawful deadlines, calendar-month conversion, provider control, exceptions, retention extensions and storage availability. No fixed day-count is substituted for months. |
| [Art.43](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-43): follow the applicable conformity-assessment procedure; the route depends on the system and applicable conditions. | `ResponsibilityOS.PreservesPolicy` describes evidence distinctions that an assessment view must retain under a supplied policy. A left inverse is a sufficient technical construction, not a legal obligation. | `Art43.recoverable_export_preserves_policy`, `Art43.backward_audit_factorization`; the per-record export conclusion in `history_evidence_chain`. | Selection/performance of the assessment procedure, acceptance by an assessor, completeness of evidence, actual exporter correctness and execution replay. |
| [Art.72(1)–(3)](https://ai-act-service-desk.ec.europa.eu/en/ai-act/article-72): establish documented post-market monitoring, collect/document/analyse relevant data systematically, and include the monitoring plan in technical documentation. | `Art72.passesPlan` binds the current document, its referenced plan and the supplied check. The history theorem classifies all final live records without losing order or duplicate occurrences through preceding retention steps. | `Art72.monitoring_complete`, `Art72.monitoring_preserves_occurrences`, `Art72.unmatched_plan_flags_all`, `Art72.outdated_document_flags_all`, `history_evidence_chain`. | Active collection of missing data, adequacy of risk checks, organisational follow-up, mandatory plan contents and analysis of interactions with other systems. |

The cross-article connection is not based only on naming: Art.12(2)(b) expressly
connects logging to Art.72 monitoring, Art.19(1) refers to Art.12 logs, and
Art.72(3) connects the plan to technical documentation. [Recital 71](https://ai-act-service-desk.ec.europa.eu/en/ai-act/recital-71)
also explains the roles of records and documentation in traceability, assessment
and monitoring. These references motivate the architecture; they do **not**
prove that our chosen predicates are legally sufficient. The correspondence is
explicit and reviewable; Lean checks the model, not the legal adequacy of this
interpretation.

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

### History-wide evidence chain

The existing `evidence_chain` and all previous public declarations remain intact.
`History.Command` adds only `attempt`, `prune` and `reprofile`; the first two reuse
`advance` and `Art19.pruneExpired`, while the last changes the profile without
clearing history or the stopped flag. Commands are processed in supplied order;
records remain newest-first, as in the original model. Authorisation of profile
updates is external to this reference runner.

`History.run_without_pruning` proves a relational invariant over **arbitrary finite
command sequences**. Provided every intermediate pruning cutoff is no later than
the final audit cutoff, the actual run and the no-deletion reference run have the
same final profile and stopped flag, and **exactly the same final live record list**.
This is list equality, not merely membership or a count: order and repeated
occurrences are preserved. The record-retention result is derived through the
interleaved transitions, not supplied as a premise.

`history_evidence_chain` starts from an empty history and combines that invariant
with execution-time permission, current document support for normal records,
exclusive monitoring classification, review on any failed plan predicate, and
preservation of each retained trace's policy-relevant distinctions by an export
satisfying the stated round-trip law. `History.run_permission` also supports a
nonempty initial history when its permission invariant has already been established.
No assumption says that all records execute or pass monitoring.

**Historical permission and current evidence support are different.** An earlier
executed record retains the profile context captured at that time. After a profile
change, a record mismatching the current document/profile is reviewed rather than
silently recertified; the theorem does not retrospectively invalidate that earlier
execution. Nor does it make document loading a prerequisite of `advance`.

`History.live_execution_survives_pruning` supplies a positive execution case.
`History.future_cutoff_counterexample` shows why the time premise matters: pruning
at a record's deadline plus one can erase a record that would still be retained
at its deadline. `History.stopped_run_stays_stopped` covers every command suffix,
including profile changes. These are reference-model results, not deployment tests.

For a concrete reference scenario, record an allowed operation under context A
with retention deadline 10, prune at 5, switch to B, record an allowed operation
under B with deadline 20, and prune at 6. At audit cutoff 8, both records remain;
a current B document/plan with a successful check can classify the B record as
normal, but must review the A record. This illustrates prevention of evidence
loss and stale-context reuse, not a measured reduction in audit labour.

The reference control decision does not depend on the pruned history. A deployed
controller that does depend on it needs a separate correspondence/refinement
argument; the theorem does not silently cover a different transition function.

## GitHub setup — 日本語

新しいリポジトリ名は **`responsibility-os-eu-ai-act-mapping`** です。
初回配置では上記5ファイルをフォルダ構造のままリポジトリ直下に置いてください。
今回の更新用ZIPには `EUAIActMapping.lean` と `README.md` の2ファイルだけを含めています。
既存リポジトリではこの2ファイルだけ置換し、他の3ファイルはそのままにしてください。
**ZIPそのものをアップロードするのではありません。** `EUAIActMapping.lean` と
`lakefile.toml` が直下にあり、ワークフローが必ず
**`.github/workflows/lean.yml`** にある状態にします。

Actionsが有効なら、push・pull requestで `Lean verification` が実行されます。
手動実行は **Actions → Lean verification → Run workflow** です（ワークフローを
既定ブランチに配置した後に利用できます）。公開Kernelの取得に
専用トークンやSecretsの設定は不要です。所属組織でActionsが制限されている場合は、
使用するActionsの許可が必要です。

## Verification details

GitHub Actions installs Lean 4.26.0 through elan, resolves the pinned dependencies,
builds `EUAIActMapping`, and checks the source with warnings treated as errors.

A green `Lean verification / verify` result means that the published mapping
successfully compiles against the pinned Responsibility OS Kernel and mathlib baseline.

This CI verifies the Lean source and proofs accepted by Lean; it does not perform
a separate `#print axioms` audit or publish an audit report artifact. The theorem
premises still need justification in an application. This is not legal certification
or proof of complete EU AI Act compliance.

The core dependency revisions are fixed in `lakefile.toml`:

- Kernel: `9b4e7d25572f3a1e114508bdf1a2d62349e83993`.
- mathlib: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).
- Toolchain: `leanprover/lean4:v4.26.0`.

The kernel commit was obtained from the upstream [commit history](https://github.com/GhostDriftTheory/responsibility-os-kernel/commits/main/).
Its [Lake configuration](https://github.com/GhostDriftTheory/responsibility-os-kernel/blob/main/lakefile.lean)
requires mathlib v4.26.0; the mathlib pin identifies the corresponding
[release](https://github.com/leanprover-community/mathlib4/releases/tag/v4.26.0).
This is an explicit dependency baseline, not a promise to follow the latest upstream commit.
Transitive revisions are resolved by Lake and recorded in `lake-manifest.json`
during a build. The current workflow does not upload that manifest as an artifact.
Keep a copy from a reproduced build when recording the resolved environment.
An intentional dependency update changes `lakefile.toml` and, when needed,
`lean-toolchain`, followed by a new verification run. This revision requires no
changes to those files or to the workflow.

For an authorised local **build and source check**, install Git and
[elan](https://github.com/leanprover/elan), then run:

```sh
lake update
lake exe cache get
lake build EUAIActMapping
lake env lean -DwarningAsError=true EUAIActMapping.lean
```

## License

© 2026 AI Assurance, Inc. All rights reserved.

No license is granted to use, copy, modify, distribute, sublicense, or create
derivative works from the source code in this repository except with prior
written permission from the copyright holder.

This reservation does not restrict rights arising under applicable law or
[GitHub's Terms of Service](https://docs.github.com/en/site-policy/github-terms/github-terms-of-service),
including their provisions for public repositories. Third-party dependencies
remain governed by their respective licenses; this notice does not relicense them.
No patent license is granted by this notice.

## Interpretation and deployment boundary

The legal-to-formal interpretation is external. The baseline is the selected
technical subject matter of Regulation (EU) 2024/1689, as originally adopted,
not a version-certified map of every current amendment. The Commission's Service
Desk pages include amendment/update notices; the table above is limited to the
stated original-baseline subject matter. Consult the applicable official
consolidated text and the relevant assessment route before using it for a deployment.
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

