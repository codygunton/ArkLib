/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Concurrent.Execution

/-!
# Executable step policies for dynamic concurrent processes

This file adds a lightweight policy layer on top of finite executions of
`Concurrent.Process`.

The point of a policy here is operational rather than semantic in the liveness
sense: it describes which concrete step transcripts are allowed to occur in a
finite execution. So this layer is useful for expressing scheduler rules,
authorization filters, event allowlists, or ticket filters that can be checked
step by step.

The interface is phrased over the process-centered semantics rather than over a
particular concurrent frontend. A policy sees one complete sequential
transcript of the current process step and decides whether that step is
allowed.

This remains intentionally separate from fairness and liveness. Policies are
executable local constraints; fairness is an infinitary semantic assumption.
-/

universe u v w

namespace Interaction
namespace Concurrent
namespace Process

/--
`StepPolicy process` is an executable constraint on one complete process step.

A policy sees:

* the current residual process state `p`;
* the concrete sequential transcript `tr` chosen for the current step
  protocol `process.step p`.

It returns `true` when that step is allowed and `false` when it is forbidden.

So a `StepPolicy` is a step-level decision procedure, not a logical predicate
about whole runs.
-/
abbrev StepPolicy {Party : Type u} (process : Process Party) :=
  {p : process.Proc} → (process.step p).spec.Transcript → Bool

namespace StepPolicy

/--
The permissive policy that allows every step transcript.
-/
def top {Party : Type u} {process : Process Party} : StepPolicy process :=
  fun _ => true

/--
Conjunction of two step policies.

A step is allowed exactly when both component policies allow it.
-/
def inter {Party : Type u} {process : Process Party}
    (left right : StepPolicy process) : StepPolicy process :=
  fun tr => left tr && right tr

/--
`byController allow` constrains only the current controlling party of the
concrete step transcript.

If `(process.step p).currentController? tr = some controller`, the current step
is allowed exactly when `allow controller = true`. If the controller path of
that transcript is empty, the policy is vacuously satisfied.

This is the natural policy interface when one wants to constrain *who* is
allowed to control the current step, without inspecting the rest of the step.
-/
def byController {Party : Type u} {process : Process Party}
    (allow : Party → Bool) : StepPolicy process :=
  fun {p} tr =>
    match (process.step p).currentController? tr with
    | some controller => allow controller
    | none => true

/--
`byPath allow` constrains the full controller path of the concrete step
transcript.

This is the most natural policy interface when a process step is itself a
staged sequential interaction episode. For example, the policy may inspect a
root scheduler choice followed by a downstream payload owner.
-/
def byPath {Party : Type u} {process : Process Party}
    (allow : List Party → Bool) : StepPolicy process :=
  fun {p} tr => allow ((process.step p).controllerPath tr)

/--
`byEvent eventMap allow` constrains the stable event label induced by the
transcript-level event map `eventMap`.

This is the right interface when the process has already been given a
user-facing event view and policies should be expressed at that level.
-/
def byEvent {Party : Type u} {process : Process Party}
    {Event : Type w}
    (eventMap : process.EventMap Event)
    (allow : Event → Bool) : StepPolicy process :=
  fun {p} tr => allow (eventMap p tr)

/--
`byTicket ticketMap allow` constrains the stable ticket attached to each step
transcript by `ticketMap`.

This is useful when one wants executable constraints phrased in the same
stable obligation vocabulary later reused by fairness.
-/
def byTicket {Party : Type u} {process : Process Party}
    {Ticket : Type w}
    (ticketMap : process.Tickets Ticket)
    (allow : Ticket → Bool) : StepPolicy process :=
  fun {p} tr => allow (ticketMap p tr)

end StepPolicy

namespace Trace

/--
`respects policy trace` checks whether every step of the finite process
execution `trace` satisfies the executable step policy `policy`.

So `Trace.respects` is the finite-horizon notion of policy compliance.
-/
def respects {Party : Type u} {process : Process Party}
    (policy : StepPolicy process) :
    {p : process.Proc} → Trace process p → Bool
  | _, .done _ => true
  | _, .step tr tail => policy tr && respects policy tail

@[simp, grind =]
theorem respects_top {Party : Type u} {process : Process Party}
    {p : process.Proc} (trace : Trace process p) :
    respects StepPolicy.top trace = true := by
  induction trace with
  | done h => rfl
  | step tr tail ih =>
      simp [Trace.respects, StepPolicy.top, ih]

end Trace

end Process
end Concurrent
end Interaction
