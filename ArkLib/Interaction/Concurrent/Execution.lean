/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Concurrent.Process

/-!
# Finite executions of dynamic concurrent processes

This file explains what it means to execute a `Concurrent.Process` for finitely
many steps.

The important point is that one process step is itself a finite sequential
interaction episode. So a finite concurrent execution is not just a list of
atomic labels: at each residual state we record one complete sequential
transcript of the current step, then continue from the residual process state
selected by that transcript.

This file therefore provides two parallel views of finite execution:

* `Process.Trace`, the exact global execution history; and
* `Step.Observed` / `Process.ObservedTrace`, the local observations that one
  fixed party extracts from that history.

Because the API is phrased over `Concurrent.Process`, it applies uniformly to
all frontends that compile into the process core, including structural
concurrent syntax and state-indexed machines.
-/

universe u v w

namespace Interaction
namespace Concurrent

namespace Step

/--
`Observed me semantics tr` is the exact typed sequence of local observations
available to the fixed party `me` during one sequential step.

More concretely, suppose the current process step executes along transcript
`tr`. At each visited node of that transcript, the step semantics determines
what `me` is allowed to observe there, and `Observed` records exactly that
piece of local information before continuing to the next node.

So `Observed` is the step-local projection of the global transcript: it forgets
everything that `me` is not entitled to see, while preserving the exact local
observation type at every node.
-/
inductive Observed {Party : Type u} [DecidableEq Party] (me : Party) :
    {spec : Interaction.Spec.{w}} →
      Interaction.Spec.Decoration (StepContext Party) spec →
      Interaction.Spec.Transcript spec →
      Sort _ where
  | /-- The unique observed transcript of a completed sequential step. -/
    done :
      Observed (Party := Party) me (spec := .done) PUnit.unit PUnit.unit
  | /-- Extend an observed transcript by the local observation available at
    the current node. -/
    step
      {Moves : Type w}
      {rest : Moves → Interaction.Spec.{w}}
      {node : NodeSemantics Party Moves}
      {semantics : (x : Moves) →
        Interaction.Spec.Decoration (StepContext Party) (rest x)}
      {x : Moves}
      {tail : Interaction.Spec.Transcript (rest x)}
      (obs : (node.views me).ObsType)
      (restObs : Observed me (semantics x) tail) :
      Observed (spec := .node Moves rest) me
        (show Interaction.Spec.Decoration (StepContext Party) (.node Moves rest) from
          ⟨node, semantics⟩)
        (show Interaction.Spec.Transcript (.node Moves rest) from
          ⟨x, tail⟩)

namespace Observed

/--
The number of visited nodes recorded by an observed sequential transcript.
-/
def length {Party : Type u} [DecidableEq Party] {me : Party} :
    {spec : Interaction.Spec.{w}} →
      {semantics : Interaction.Spec.Decoration (StepContext Party) spec} →
      {tr : Interaction.Spec.Transcript spec} →
      Observed me semantics tr →
      Nat
  | .done, _, _, Observed.done => 0
  | .node _ _, _, _, Observed.step _ restObs => restObs.length.succ

/--
`ofTranscript me semantics tr` is the canonical observed sequential transcript
induced by the concrete global transcript `tr`.

It is obtained by replaying `tr` and, at each visited node, extracting the
observation that the local view for `me` exposes there.
-/
def ofTranscript {Party : Type u} [DecidableEq Party] (me : Party) :
    {spec : Interaction.Spec.{w}} →
      (semantics : Interaction.Spec.Decoration (StepContext Party) spec) →
      (tr : Interaction.Spec.Transcript spec) →
      Observed me semantics tr
  | .done, _, _ =>
      show Observed (Party := Party) me (spec := .done) PUnit.unit PUnit.unit from
        .done
  | .node _ _, ⟨node, semantics⟩, ⟨x, tail⟩ =>
      .step ((node.views me).obsOf x) (ofTranscript me (semantics x) tail)

end Observed

/--
`Observed me step tr` is the sequence of local observations exposed to `me`
while the step `step` executes along the transcript `tr`.

This is the most convenient step-level type when working with concrete process
steps rather than raw decorations.
-/
abbrev ObservedTranscript {Party : Type u} [DecidableEq Party] (me : Party)
    {P : Type v} (step : Step Party P) (tr : Interaction.Spec.Transcript step.spec) :=
  Observed me step.semantics tr

/--
`observe me step tr` is the canonical observed sequential transcript induced by
running `step` along `tr`.
-/
abbrev observe {Party : Type u} [DecidableEq Party] (me : Party)
    {P : Type v} (step : Step Party P) (tr : Interaction.Spec.Transcript step.spec) :
    ObservedTranscript me step tr :=
  Observed.ofTranscript me step.semantics tr

end Step

namespace Process

/--
`Trace process p` is a finite execution trace of the residual process state
`p`.

Each `step` constructor records one whole sequential transcript for the current
process step, then continues with the residual process selected by that
transcript. The `done` constructor is available only when the current step has
no complete transcripts at all, so a `Trace` represents a genuinely terminated
finite execution.

`Process.Trace` is therefore the global finite-history object for the dynamic
concurrent core: one element per process step, where each element remembers the
entire internal interaction episode that realized that step.
-/
inductive Trace {Party : Type u} (process : Process Party) :
    process.Proc → Sort _ where
  | /-- A finished execution of a residual process state whose current step has
    no complete transcripts. -/
    done {p : process.Proc} :
      ((process.step p).spec.Transcript → False) →
      Trace process p
  | /-- Execute one complete sequential step transcript and continue with the
    residual process state induced by that transcript. -/
    step {p : process.Proc}
      (tr : (process.step p).spec.Transcript) :
      Trace process ((process.step p).next tr) →
      Trace process p

namespace Trace

/--
The number of process steps recorded by a finite execution trace.
-/
def length {Party : Type u} {process : Process Party} :
    {p : process.Proc} → Process.Trace process p → Nat
  | _, .done _ => 0
  | _, .step _ tail => tail.length.succ

/--
`currentControllers trace` records the current controlling party of each
executed process step.

This sequence is computed from the concrete step transcripts themselves via
`Step.currentController?`, so it answers the operational question "who was in
charge of this step as it actually occurred?" rather than merely recording a
static owner of the process state.
-/
def currentControllers {Party : Type u} {process : Process Party} :
    {p : process.Proc} → Process.Trace process p → List (Option Party)
  | _, .done _ => []
  | p, .step tr tail =>
      (process.step p).currentController? tr ::
        currentControllers tail

/--
`controllerPaths trace` records the full controller path of each executed step
transcript.

Each list element explains the whole control stack that led to the chosen
transcript of that step, not just the final active controller.
-/
def controllerPaths {Party : Type u} {process : Process Party} :
    {p : process.Proc} → Process.Trace process p → List (List Party)
  | _, .done _ => []
  | p, .step tr tail =>
      (process.step p).controllerPath tr ::
        controllerPaths tail

/--
`events eventMap trace` records the external event label attached to each
process step transcript by the stable event map `eventMap`.

This is the finite event trace exposed by a labeled process.
-/
def events {Party : Type u} {process : Process Party} {Event : Type w}
    (eventMap : process.EventMap Event) :
    {p : process.Proc} → Process.Trace process p → List Event
  | _, .done _ => []
  | p, .step tr tail =>
      eventMap p tr :: events eventMap tail

/--
`tickets ticketMap trace` records the stable tickets attached to each process
step transcript by `ticketMap`.

These tickets are the stable obligation identifiers later used by fairness and
liveness statements.
-/
def tickets {Party : Type u} {process : Process Party} {Ticket : Type w}
    (ticketMap : process.Tickets Ticket) :
    {p : process.Proc} → Process.Trace process p → List Ticket
  | _, .done _ => []
  | p, .step tr tail =>
      ticketMap p tr :: tickets ticketMap tail

@[simp, grind =]
theorem length_done {Party : Type u} {process : Process Party}
    {p : process.Proc} (h : (process.step p).spec.Transcript → False) :
    length (.done h : Process.Trace process p) = 0 := rfl

@[simp, grind =]
theorem length_step {Party : Type u} {process : Process Party}
    {p : process.Proc}
    (tr : (process.step p).spec.Transcript)
    (tail : Process.Trace process ((process.step p).next tr)) :
    length (.step tr tail : Process.Trace process p) = tail.length.succ := rfl

end Trace

/--
`ObservedTrace me process trace` is the exact typed sequence of local
observations available to the fixed party `me` along the concrete process
execution trace `trace`.

At each process step, the head constructor stores the observed sequential
transcript induced by that step's global transcript, and the tail continues
with the residual process state. So `ObservedTrace` is the party-local view of
the global finite execution `trace`.
-/
inductive ObservedTrace {Party : Type u} [DecidableEq Party]
    (me : Party) (process : Process Party) :
    {p : process.Proc} → Process.Trace process p → Sort _ where
  | /-- The unique observed trace of a finished quiescent execution. -/
    done {p : process.Proc}
      {h : (process.step p).spec.Transcript → False} :
      ObservedTrace me process (.done h : Process.Trace process p)
  | /-- Extend an observed trace by the observed sequential transcript of the
    current step. -/
    step {p : process.Proc}
      {tr : (process.step p).spec.Transcript}
      {tail : Process.Trace process ((process.step p).next tr)}
      (obs : Step.ObservedTranscript me (process.step p) tr)
      (rest : ObservedTrace me process tail) :
      ObservedTrace me process (.step tr tail : Process.Trace process p)

namespace ObservedTrace

/--
The number of process steps recorded by an observed trace.

This agrees with the length of the underlying global trace.
-/
def length {Party : Type u} [DecidableEq Party]
    {me : Party} {process : Process Party} :
    {p : process.Proc} → {trace : Process.Trace process p} →
      ObservedTrace me process trace →
      Nat
  | _, .done _, .done => 0
  | _, .step _ _, .step _ rest => rest.length.succ

/--
`ofTrace me process trace` is the canonical observed process trace induced by
the concrete execution trace `trace`.

It is obtained by projecting each executed process step to the local
observations available to `me`.
-/
def ofTrace {Party : Type u} [DecidableEq Party]
    (me : Party) (process : Process Party) :
    {p : process.Proc} → (trace : Process.Trace process p) → ObservedTrace me process trace
  | _, .done _ => .done
  | p, .step tr tail =>
      .step
        (Step.observe me (process.step p) tr)
        (ofTrace me process tail)

@[simp, grind =]
theorem length_done {Party : Type u} [DecidableEq Party]
    {me : Party} {process : Process Party} {p : process.Proc}
    {h : (process.step p).spec.Transcript → False} :
    length (ObservedTrace.done (me := me) (process := process) (p := p) (h := h)) = 0 := rfl

@[simp, grind =]
theorem length_step {Party : Type u} [DecidableEq Party]
    {me : Party} {process : Process Party} {p : process.Proc}
    {tr : (process.step p).spec.Transcript}
    {tail : Process.Trace process ((process.step p).next tr)}
    (obs : Step.ObservedTranscript me (process.step p) tr)
    (rest : ObservedTrace me process tail) :
    length (.step obs rest : ObservedTrace me process
      (.step tr tail : Process.Trace process p)) = rest.length.succ := rfl

/--
The canonical observed process trace has the same number of process steps as
the underlying execution trace.
-/
theorem length_ofTrace {Party : Type u} [DecidableEq Party]
    {me : Party} (process : Process Party) :
    {p : process.Proc} → (trace : Process.Trace process p) →
      (ofTrace me process trace).length = trace.length
  | _, .done _ => rfl
  | _, .step _ tail => by
      simpa [ObservedTrace.ofTrace, ObservedTrace.length, Trace.length] using
        congrArg Nat.succ (length_ofTrace (me := me) process tail)

end ObservedTrace

end Process

end Concurrent
end Interaction
