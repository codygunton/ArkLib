/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Concurrent.Process

/-!
# Finite executions of dynamic concurrent processes

This file equips the dynamic `Concurrent.Process` core with finite executions
and their induced local observations.

The key shift from the earlier structural concurrent execution layer is:

* execution is now centered on `Concurrent.Process`, whose current step is a
  finite sequential interaction episode;
* a finite execution therefore consists of one complete sequential transcript
  per residual process state;
* controller paths and local observations are recovered from the nodewise
  semantics attached to each such step.

This means the current execution layer no longer depends on any particular
concurrent frontend. Structural trees, machines, and future Veil-style
frontends can all compile to `Process` and then reuse the same execution API.
-/

universe u v w

namespace Interaction
namespace Concurrent

namespace Step

/--
`Observed me semantics tr` is the exact typed sequence of local observations
available to the fixed party `me` along the sequential transcript `tr`.

The observation type is computed directly from the nodewise `LocalView`
metadata stored in `semantics`. At each visited node, the constructor records
the observation exposed there and then continues recursively through the chosen
transcript branch.

So this is the sequential-step analogue of a projected local trace: it records
what one participant actually learns while one process step executes.
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

/-- The number of visited nodes recorded by an observed sequential transcript. -/
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
induced by the concrete transcript `tr`.
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

Each constructor records one complete sequential step transcript:

* `done h` finishes the execution when the current step exposes no complete
  transcript at all;
* `step tr tail` executes the current step along transcript `tr` and then
  continues with a trace of the residual process state `next tr`.

So `Process.Trace` is the dynamic-process analogue of a sequential transcript,
but with one whole sequential interaction episode per execution step.
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

/-- The number of process steps recorded by a finite execution trace. -/
def length {Party : Type u} {process : Process Party} :
    {p : process.Proc} → Process.Trace process p → Nat
  | _, .done _ => 0
  | _, .step _ tail => tail.length.succ

/--
`currentControllers trace` records the current controlling party of each
executed process step.

This is computed from the concrete step transcript itself via
`Step.currentController?`. So, unlike the earlier tree-specific execution
layer, the current controller of a generic process step may depend on the
chosen step transcript.
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

Each list element is the path produced by `Step.controllerPath` for the
corresponding step transcript of the process execution.
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

These are the intended obligation identifiers for future fairness and liveness
layers.
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
transcript induced by that step's transcript. The tail then continues with the
residual process state.
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

/-- The number of executed process steps recorded by an observed trace. -/
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
