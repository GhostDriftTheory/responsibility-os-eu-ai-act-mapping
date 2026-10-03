import ResponsibilityOS

/-!
# EU AI Act — selected formal assurance profiles

A small application layer; the imported Responsibility OS Kernel is unchanged.
Targets: Lean/mathlib 4.26.0 and the public `ResponsibilityOS` API.

Article numbers identify *selected technical contributions*, not definitions of
legal compliance. The legal-to-formal interpretation is external to Lean.
Reference baseline: Regulation (EU) 2024/1689, original Articles 11(1), 12(1)-(2),
14(4)(d)-(e), 19(1), 43 and 72(1)-(3); consult the applicable amended text before
using the mapping for a deployment. No application dates are encoded.

Added disclosure: version keys, a logical stop/withhold gate, and a typed event
log with deadline filtering, explicit document/monitoring-plan version binding,
and a lossless monitoring partition. No ADIC implementation,
private checker, numerical certificate format or physical controller is added.

Assumptions not discharged here:
* the chosen policy/context adequately represents applicable requirements;
* observed events, human commands and readiness inputs are authentic/complete;
* deployed execution cannot bypass `advance`, and its logical halt is connected
  to an appropriate physical safe-state mechanism;
* clocks/deadlines, durable storage and document identifiers are correctly bound;
* an audit exporter/recoverer satisfies the explicitly supplied round-trip law;
* the chosen monitoring check detects the relevant real-world risks.

In particular, category faithfulness does NOT prove automatic logging, storage
retention, real-world safety or executable replay. The new reference transition
proves recording/stop properties only for its own mathematical model.

Build status is established by the CI run for the exact repository commit.
The creation environment could not execute Lean. The accompanying five-file
repository builds this source and audits every mapping theorem's axioms.
-/

universe uE vE uV vV uO vO uF vF

open CategoryTheory

namespace EUAIActMapping

attribute [local instance] ResponsibilityOS.IndexedAssurance.fiberCategory

/-- Opaque deployment/document keys, not hashes or a model of Annex IV contents. -/
structure Context where
  system : Nat
  release : Nat
  specification : Nat
  boundary : Nat
  documentation : Nat
  deriving DecidableEq, Repr

/-- An interpreted technical profile, not a legal-compliance certificate. -/
structure Profile (E : Type uE) [Category.{vE} E] where
  context : Context
  policy : ResponsibilityOS.ObservationPolicy E

inductive Request where
  | allow | withhold | stop
  deriving DecidableEq, Repr

inductive Decision where
  | executed | held | stopped
  deriving DecidableEq, Repr

/-- Stop dominates readiness; a withheld output never executes in this model. -/
def gate (halted ready : Bool) (request : Request) : Decision :=
  match halted, request with
  | true, _ => .stopped
  | false, .stop => .stopped
  | false, .withhold => .held
  | false, .allow => if ready then .executed else .held

def Decision.isStopped : Decision → Bool
  | .stopped => true
  | _ => false

/-- One supplied evidence-bearing event. Times are abstract ordered ticks.
`retainUntil` is supplied under the applicable retention policy; this file does
not equate six calendar months with a fixed number of days. -/
structure Event (E : Type uE) [Category.{vE} E] where
  context : Context
  source : E
  target : E
  trace : source ⟶ target
  createdAt : Nat
  retainUntil : Nat
  validWindow : createdAt ≤ retainUntil

/-- A reference-model record of an attempted operation and its gate outcome. -/
structure Record (E : Type uE) [Category.{vE} E] where
  event : Event E
  profileContext : Context
  request : Request
  ready : Bool
  haltedBefore : Bool
  decision : Decision

structure State (E : Type uE) [Category.{vE} E] where
  profile : Profile E
  halted : Bool
  history : List (Record E)

variable {E : Type uE} [Category.{vE} E]

def capture (s : State E) (e : Event E) (request : Request)
    (ready : Bool) : Record E where
  event := e
  profileContext := s.profile.context
  request := request
  ready := ready
  haltedBefore := s.halted
  decision := gate s.halted (ready && decide (e.context = s.profile.context)) request

/-- The context-guarded reference transition. Every attempted step, including hold/stop,
prepends its computed record. This is not a durable-storage implementation. -/
def advance (s : State E) (e : Event E) (request : Request)
    (ready : Bool) : State E :=
  let r := capture s e request ready
  { profile := s.profile, halted := r.decision.isStopped, history := r :: s.history }

namespace Art11

/-- Documentation contribution: bind evidence to the exact declared context. -/
def matchesContext (p : Profile E) (r : Record E) : Bool :=
  decide (r.event.context = p.context ∧ r.profileContext = p.context)

theorem context_check_is_exact (p : Profile E) (r : Record E) :
    matchesContext p r = true ↔
      r.event.context = p.context ∧ r.profileContext = p.context := by
  simp [matchesContext]

/-- Evidence from a different release/specification/boundary/document key
cannot pass this context check. Adequacy of the keys remains external. -/
theorem stale_context_is_rejected (p : Profile E) (r : Record E)
    (h : r.event.context ≠ p.context) : matchesContext p r = false := by
  simp [matchesContext, h]


/-- Public document metadata only. `context.documentation` identifies its version;
`monitoringPlanVersion` names the plan referenced by that document. Neither field
proves document contents, authenticity, completeness or legal adequacy. -/
structure Documentation where
  context : Context
  monitoringPlanVersion : Nat
  deriving DecidableEq, Repr

/-- A document can support this record only in the current declared context. -/
def supportsRecord (p : Profile E) (d : Documentation) (r : Record E) : Bool :=
  decide (d.context = p.context) && matchesContext p r

theorem document_binding_is_exact (p : Profile E) (d : Documentation) (r : Record E) :
    supportsRecord p d r = true ↔
      d.context = p.context ∧ r.event.context = p.context ∧ r.profileContext = p.context := by
  simp [supportsRecord, matchesContext]

/-- Old/different document versions cannot justify evidence under the current
profile, even when the event itself has the current context. This is a consistency
check, not an assertion that old evidence loses its historical validity. -/
theorem stale_document_is_rejected (p : Profile E) (d : Documentation) (r : Record E)
    (h : d.context.documentation ≠ p.context.documentation) :
    supportsRecord p d r = false := by
  have hContext : d.context ≠ p.context := fun hEq => h (congrArg Context.documentation hEq)
  simp [supportsRecord, hContext]

end Art11

namespace Art12

/-- Automatic recording *in the reference transition*, not inferred from
faithfulness of the mathematical kernel. -/
theorem every_step_is_recorded (s : State E) (e : Event E)
    (request : Request) (ready : Bool) :
    capture s e request ready ∈ (advance s e request ready).history := by
  simp [advance]

theorem previous_records_are_preserved (s : State E) (e : Event E)
    (request : Request) (ready : Bool) (r : Record E)
    (h : r ∈ s.history) : r ∈ (advance s e request ready).history := by
  simp [advance, h]

variable {O : Type uO} [Category.{vO} O]

/-- Canonical connection to the existing kernel; no replacement kernel. -/
def standardEvent (K : ResponsibilityOS.Kernel.{uO, vO, uF, vF} O)
    {X Y : O} (f : X ⟶ Y) (context : Context)
    (createdAt retainUntil : Nat) (h : createdAt ≤ retainUntil) :
    Event (ResponsibilityOS.responsibilityCategory K) where
  context := context
  source := (ResponsibilityOS.standardTrace K).obj X
  target := (ResponsibilityOS.standardTrace K).obj Y
  trace := (ResponsibilityOS.standardTrace K).map f
  createdAt := createdAt
  retainUntil := retainUntil
  validWindow := h

/-- The evidence trace retains the supplied base operation. -/
theorem standard_event_keeps_operation
    (K : ResponsibilityOS.Kernel.{uO, vO, uF, vF} O)
    {X Y : O} (f : X ⟶ Y) (context : Context)
    (createdAt retainUntil : Nat) (h : createdAt ≤ retainUntil) :
    (standardEvent K f context createdAt retainUntil h).trace.base = f := by
  rfl

/-- Standard tracing preserves each distinction required by a supplied policy
on operations. This is not completeness of all evidence within each fiber. -/
theorem standard_trace_preserves_policy
    (K : ResponsibilityOS.Kernel.{uO, vO, uF, vF} O)
    (p : ResponsibilityOS.ObservationPolicy O) :
    ResponsibilityOS.PreservesPolicy (ResponsibilityOS.standardTrace K) p := by
  intro X Y f g hRelevant hEqual
  exact p.sound hRelevant
    ((ResponsibilityOS.standard_trace_is_faithful K).map_injective hEqual)

end Art12

namespace Art14

/-- Readiness is an externally supplied technical result. This theorem does
not identify a Boolean with a lawful or substantively safe decision. -/
theorem execution_requires_permission (halted ready : Bool) (request : Request)
    (h : gate halted ready request = .executed) :
    halted = false ∧ request = .allow ∧ ready = true := by
  cases halted <;> cases ready <;> cases request <;> simp_all [gate]

/-- Execution requires both technical readiness and the current context.
The expected context is stored in the same record for subsequent inspection. -/
theorem execution_requires_current_context (s : State E) (e : Event E)
    (request : Request) (ready : Bool)
    (h : (capture s e request ready).decision = .executed) :
    s.halted = false ∧ request = .allow ∧ ready = true ∧
      e.context = s.profile.context := by
  have hGate := execution_requires_permission s.halted
    (ready && decide (e.context = s.profile.context)) request h
  have hReady : ready = true ∧ e.context = s.profile.context := by
    simpa using hGate.2.2
  exact ⟨hGate.1, hGate.2.1, hReady.1, hReady.2⟩

/-- Logical stop is always effective, independently of readiness. Physical
safe stopping, response times, interfaces and human competence are not modeled. -/
theorem stop_always_halts (s : State E) (e : Event E) (ready : Bool) :
    (advance s e .stop ready).halted = true := by
  cases h : s.halted <;>
    simp [advance, capture, gate, Decision.isStopped, h]

theorem withhold_never_executes (s : State E) (e : Event E) (ready : Bool) :
    (capture s e .withhold ready).decision ≠ .executed := by
  cases h : s.halted <;> simp [capture, gate, h]

/-- No implicit restart exists in the reference transition. -/
theorem stopped_state_remains_stopped (s : State E) (e : Event E)
    (request : Request) (ready : Bool) (h : s.halted = true) :
    (advance s e request ready).halted = true := by
  simp [advance, capture, gate, Decision.isStopped, h]

end Art14

namespace Art19

/-- Retention contribution: a reference filter that cannot delete a record
before its externally determined deadline. A deadline may be extended upstream;
legal minimums, exceptions, control of logs and storage availability are external. -/
def pruneExpired (now : Nat) (history : List (Record E)) : List (Record E) :=
  history.filter (fun r => decide (now ≤ r.event.retainUntil))

theorem no_early_deletion (now : Nat) (history : List (Record E))
    (r : Record E) (hMem : r ∈ history)
    (hDeadline : now ≤ r.event.retainUntil) :
    r ∈ pruneExpired now history := by
  simp [pruneExpired, hMem, hDeadline]

/-- Recording and retention are connected, rather than two independent claims. -/
theorem fresh_record_survives_pruning (s : State E) (e : Event E)
    (request : Request) (ready : Bool) (now : Nat)
    (h : now ≤ e.retainUntil) :
    capture s e request ready ∈
      pruneExpired now (advance s e request ready).history := by
  exact no_early_deletion now _ _
    (Art12.every_step_is_recorded s e request ready) h

end Art19

namespace Art43

variable {V : Type uV} [Category.{vV} V]

/-- Assessment-support contribution: an exporter with a left inverse cannot
collapse policy-relevant evidence distinctions. The round-trip law must be
proved for the actual exporter; it is not assumed for arbitrary real software.
This is neither an executable replay theorem nor an Article 43 procedure. -/
theorem recoverable_export_preserves_policy
    (publish : E ⥤ V) (recover : V ⥤ E)
    (hRoundTrip : publish ⋙ recover = 𝟭 E)
    (p : ResponsibilityOS.ObservationPolicy E) :
    ResponsibilityOS.PreservesPolicy publish p := by
  have hFaithful : publish.Faithful :=
    ResponsibilityOS.IndexedAssurance.faithful_of_section
      recover publish hRoundTrip
  intro X Y f g hRelevant hEqual
  exact p.sound hRelevant (hFaithful.map_injective hEqual)

/-- Exporters need only preserve the selected policy. A left inverse above is
a sufficient construction, not a necessary condition or a legal requirement. -/
theorem policy_relevant_distinction_survives
    (publish : E ⥤ V) (p : ResponsibilityOS.ObservationPolicy E)
    (hPreserve : ResponsibilityOS.PreservesPolicy publish p)
    {X Y : E} {f g : X ⟶ Y} (hRelevant : p.relevant f g) :
    publish.map f ≠ publish.map g := by
  exact hPreserve hRelevant

variable {O : Type uO} [Category.{vO} O]

/-- Reuse of the kernel's structural backward-audit factorization.
Unique categorical factorization must not be called execution replay. -/
theorem backward_audit_factorization
    (K : ResponsibilityOS.Kernel.{uO, vO, uF, vF} O)
    {X Y Z : O} (f : X ⟶ Y) (k : Z ⟶ X)
    (b : K.Fiber Y) (c : K.Fiber Z)
    (h : (⟨Z, c⟩ : ResponsibilityOS.responsibilityCategory K) ⟶ ⟨Y, b⟩)
    (hBase : h.base = k ≫ f) :
    ∃! (δ : (⟨Z, c⟩ : ResponsibilityOS.responsibilityCategory K) ⟶
      ⟨X, (K.pull f).obj b⟩),
      δ.base = k ∧ δ ≫ ResponsibilityOS.IndexedAssurance.cartLift K f b = h := by
  exact ResponsibilityOS.backward_audit_factors_uniquely K f k b c h hBase

end Art43

namespace Art72

/-- A minimal, versioned monitoring plan. The check is supplied, not claimed to
identify all relevant risks. Unknown/insufficient evidence should return false. -/
structure MonitoringPlan (E : Type uE) [Category.{vE} E] where
  context : Context
  version : Nat
  check : Record E → Bool

/-- Positive classification requires a current document, its referenced plan,
a current event/profile binding, and a successful supplied check. A mismatched
plan or document fails closed even if `check` always returns true. -/
def passesPlan (p : Profile E) (d : Art11.Documentation)
    (plan : MonitoringPlan E) (r : Record E) : Bool :=
  decide (plan.context = p.context ∧ plan.version = d.monitoringPlanVersion) &&
    Art11.supportsRecord p d r && plan.check r

def normalRecords (p : Profile E) (d : Art11.Documentation) (plan : MonitoringPlan E)
    (history : List (Record E)) : List (Record E) :=
  history.filter (passesPlan p d plan)

def reviewRecords (p : Profile E) (d : Art11.Documentation) (plan : MonitoringPlan E)
    (history : List (Record E)) : List (Record E) :=
  history.filter (fun r => !(passesPlan p d plan r))

/-- Every supplied recorded item belongs to exactly one classification. `normal`
means this profile's checks passed, not that the real system is safe/compliant. -/
theorem monitoring_complete (p : Profile E) (d : Art11.Documentation)
    (plan : MonitoringPlan E) (history : List (Record E)) (r : Record E)
    (hMem : r ∈ history) :
    (r ∈ normalRecords p d plan history ∨ r ∈ reviewRecords p d plan history) ∧
      ¬ (r ∈ normalRecords p d plan history ∧ r ∈ reviewRecords p d plan history) := by
  cases h : passesPlan p d plan r <;> simp [normalRecords, reviewRecords, hMem, h]

/-- Unlike a membership-only claim, this also accounts for repeated occurrences.
It says nothing about real events absent from the supplied history. -/
theorem monitoring_preserves_occurrences (p : Profile E) (d : Art11.Documentation)
    (plan : MonitoringPlan E) (history : List (Record E)) :
    (normalRecords p d plan history).length + (reviewRecords p d plan history).length =
      history.length := by
  induction history with
  | nil => simp [normalRecords, reviewRecords]
  | cons r history ih =>
      cases h : passesPlan p d plan r <;>
        simpa [normalRecords, reviewRecords, h, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using congrArg Nat.succ ih

theorem failed_plan_check_is_reviewed (p : Profile E) (d : Art11.Documentation)
    (plan : MonitoringPlan E) (history : List (Record E)) (r : Record E)
    (hMem : r ∈ history) (hFail : plan.check r = false) :
    r ∈ reviewRecords p d plan history := by
  simp [reviewRecords, passesPlan, hMem, hFail]

/-- A plan version not referenced by the document cannot clear any item. -/
theorem unmatched_plan_flags_all (p : Profile E) (d : Art11.Documentation)
    (plan : MonitoringPlan E) (history : List (Record E))
    (h : plan.version ≠ d.monitoringPlanVersion) :
    normalRecords p d plan history = [] ∧ reviewRecords p d plan history = history := by
  simp [normalRecords, reviewRecords, passesPlan, h]

/-- Context changes require revalidation, not silent reuse of old documents. -/
theorem outdated_document_flags_all (p : Profile E) (d : Art11.Documentation)
    (plan : MonitoringPlan E) (history : List (Record E)) (h : d.context ≠ p.context) :
    normalRecords p d plan history = [] ∧ reviewRecords p d plan history = history := by
  simp [normalRecords, reviewRecords, passesPlan, Art11.supportsRecord, h]


/-- Monitoring contribution: select every recorded context mismatch or failed
supplied check. No claim that `check` covers all real risks or legal duties. -/
def reviewQueue (p : Profile E) (check : Record E → Bool)
    (history : List (Record E)) : List (Record E) :=
  history.filter (fun r => !(Art11.matchesContext p r && check r))

theorem failed_check_is_flagged (p : Profile E) (check : Record E → Bool)
    (history : List (Record E)) (r : Record E)
    (hMem : r ∈ history) (hFail : check r = false) :
    r ∈ reviewQueue p check history := by
  simp [reviewQueue, hMem, hFail]

theorem changed_context_is_flagged (p : Profile E) (check : Record E → Bool)
    (history : List (Record E)) (r : Record E)
    (hMem : r ∈ history) (hChange : r.event.context ≠ p.context) :
    r ∈ reviewQueue p check history := by
  simp [reviewQueue, Art11.matchesContext, hMem, hChange]

variable {O : Type uO} [Category.{vO} O]

/-- Structural composition support, not a market-monitoring plan. A composite
morphism need not determine its intermediate history; keep the event list too. -/
theorem standard_trace_composes
    (K : ResponsibilityOS.Kernel.{uO, vO, uF, vF} O)
    {X Y Z : O} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (ResponsibilityOS.standardTrace K).map (f ≫ g) =
      (ResponsibilityOS.standardTrace K).map f ≫
        (ResponsibilityOS.standardTrace K).map g := by
  exact (ResponsibilityOS.standardTrace K).map_comp f g

end Art72

/-- One captured record connects document/context binding, logging/retention,
permission, policy-preserving export, and versioned plan-based monitoring.
Document/event context and retention are explicit premises; plan mismatches are
NOT assumed away and cause review. The external export round-trip law remains
an explicit premise. This is not a theorem of legal compliance.

Instantiate E with `ResponsibilityOS.responsibilityCategory K` and use
`Art12.standardEvent`, or supply another justified evidence adapter. -/
theorem evidence_chain
    {V : Type uV} [Category.{vV} V]
    (s : State E) (e : Event E) (d : Art11.Documentation) (plan : Art72.MonitoringPlan E)
    (request : Request) (ready : Bool) (now : Nat)
    (hContext : e.context = s.profile.context) (hDocument : d.context = s.profile.context)
    (hDeadline : now ≤ e.retainUntil)
    (publish : E ⥤ V) (recover : V ⥤ E)
    (hRoundTrip : publish ⋙ recover = 𝟭 E) :
    Art11.supportsRecord s.profile d (capture s e request ready) = true ∧
    capture s e request ready ∈
      Art19.pruneExpired now (advance s e request ready).history ∧
    ((capture s e request ready).decision = .executed →
      s.halted = false ∧ request = .allow ∧ ready = true ∧
        e.context = s.profile.context) ∧
    ResponsibilityOS.PreservesPolicy publish s.profile.policy ∧
    ((capture s e request ready ∈ Art72.normalRecords s.profile d plan
        (Art19.pruneExpired now (advance s e request ready).history) ∨
      capture s e request ready ∈ Art72.reviewRecords s.profile d plan
        (Art19.pruneExpired now (advance s e request ready).history)) ∧
      ¬ (capture s e request ready ∈ Art72.normalRecords s.profile d plan
          (Art19.pruneExpired now (advance s e request ready).history) ∧
        capture s e request ready ∈ Art72.reviewRecords s.profile d plan
          (Art19.pruneExpired now (advance s e request ready).history))) ∧
    (plan.check (capture s e request ready) = false →
      capture s e request ready ∈ Art72.reviewRecords s.profile d plan
        (Art19.pruneExpired now (advance s e request ready).history)) := by
  have hRetained :=
    Art19.fresh_record_survives_pruning s e request ready now hDeadline
  refine ⟨?_, hRetained, ?_, ?_, ?_, ?_⟩
  · simp [Art11.supportsRecord, Art11.matchesContext, capture, hContext, hDocument]
  · intro hExecute
    exact Art14.execution_requires_current_context s e request ready hExecute
  · exact Art43.recoverable_export_preserves_policy publish recover hRoundTrip s.profile.policy
  · exact Art72.monitoring_complete s.profile d plan _ _ hRetained
  · intro hFail
    exact Art72.failed_plan_check_is_reviewed s.profile d plan _ _ hRetained hFail

namespace Examples

/-- A constructive positive witness, with an actually inhabited relevance
relation: the existing kernel's traceA/traceB example, not an empty policy. -/
theorem full_view_preserves_nonempty_trace_policy :
    ResponsibilityOS.PreservesPolicy
      (𝟭 ResponsibilityOS.CollapseCounterexample.EObj)
      ResponsibilityOS.CollapseCounterexample.tracePolicy ∧
    ResponsibilityOS.CollapseCounterexample.tracePolicy.relevant
      ResponsibilityOS.CollapseCounterexample.EHom.traceA
      ResponsibilityOS.CollapseCounterexample.EHom.traceB := by
  constructor
  · intro X Y f g hRelevant hEqual
    exact ResponsibilityOS.CollapseCounterexample.tracePolicy.sound hRelevant hEqual
  · exact ResponsibilityOS.CollapseCounterexample.trace_policy_relevant

/-- Negative witness: an operation-only view does not pass this trace policy. -/
theorem operation_only_view_fails :
    ¬ ResponsibilityOS.PreservesPolicy
      ResponsibilityOS.CollapseCounterexample.U
      ResponsibilityOS.CollapseCounterexample.tracePolicy := by
  exact ResponsibilityOS.CollapseCounterexample.U_does_not_preserve_trace_policy

end Examples
end EUAIActMapping
