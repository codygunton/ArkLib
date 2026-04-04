/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Concurrent.Execution

/-!
# Finite prefixes and infinite runs of dynamic concurrent processes

This file extends finite executions in the two directions needed for semantic
reasoning about ongoing concurrent behavior.

* `Process.Prefix` is the right notion of a finite initial segment of an
  execution. Unlike `Process.Trace`, it may stop at any residual process state,
  not only at a quiescent one.
* `Process.Run` is an infinite execution, represented by the residual process
  state at each time index together with the complete transcript chosen for the
  corresponding process step.

The distinction matters because fairness, liveness, and observational
equivalence reason about executions that continue forever. A terminating trace
is too restrictive to serve as the generic prefix object for that purpose, so
this file provides the dedicated bridge from finite executions to infinitary
semantics.
-/

universe u v w

namespace Interaction
namespace Concurrent
namespace Process

/--
`Prefix process p n` is a finite prefix of length `n` of an execution starting
from the residual process state `p`.

Unlike `Process.Trace`, a `Prefix` may stop at any residual state. This makes
it the correct finite prefix object for later infinite-run semantics.

Each `step` constructor records one complete sequential transcript of the
current process step and then continues with a shorter prefix of the induced
residual state.
-/
inductive Prefix {Party : Type u} (process : Process Party) :
    process.Proc → Nat → Sort _ where
  | /-- The empty execution prefix. -/
    nil {p : process.Proc} : Prefix process p 0
  | /-- Extend a finite prefix by one complete process step transcript. -/
    step {p : process.Proc} {n : Nat}
      (tr : (process.step p).spec.Transcript) :
      Prefix process ((process.step p).next tr) n →
      Prefix process p n.succ

namespace Prefix

/--
The sequence of current controlling parties exposed by a finite prefix.

This is the controller-level summary of the finite execution prefix.
-/
def currentControllers {Party : Type u} {process : Process Party} :
    {p : process.Proc} → {n : Nat} → Prefix process p n → List (Option Party)
  | _, _, .nil => []
  | p, _, .step tr tail =>
      (process.step p).currentController? tr :: currentControllers tail

/--
The sequence of full controller paths exposed by a finite prefix.
-/
def controllerPaths {Party : Type u} {process : Process Party} :
    {p : process.Proc} → {n : Nat} → Prefix process p n → List (List Party)
  | _, _, .nil => []
  | p, _, .step tr tail =>
      (process.step p).controllerPath tr :: controllerPaths tail

/--
The stable event labels attached to the executed steps of a finite prefix.
-/
def events {Party : Type u} {process : Process Party} {Event : Type w}
    (eventMap : process.EventMap Event) :
    {p : process.Proc} → {n : Nat} → Prefix process p n → List Event
  | _, _, .nil => []
  | p, _, .step tr tail =>
      eventMap p tr :: events eventMap tail

/--
The stable tickets attached to the executed steps of a finite prefix.
-/
def tickets {Party : Type u} {process : Process Party} {Ticket : Type w}
    (ticketMap : process.Tickets Ticket) :
    {p : process.Proc} → {n : Nat} → Prefix process p n → List Ticket
  | _, _, .nil => []
  | p, _, .step tr tail =>
      ticketMap p tr :: tickets ticketMap tail

/--
Forget the quiescence proof of a finite `Trace` and keep only its executed
prefix.

This is the canonical way to view a terminated finite execution as an ordinary
prefix that can later be compared with prefixes extracted from infinite runs.
-/
def ofTrace {Party : Type u} {process : Process Party} :
    {p : process.Proc} → (trace : Trace process p) → Prefix process p trace.length
  | _, .done _ => .nil
  | _, .step tr tail => .step tr (ofTrace tail)

@[simp, grind =]
theorem currentControllers_nil {Party : Type u} {process : Process Party}
    {p : process.Proc} :
    currentControllers (.nil : Prefix process p 0) = [] := rfl

@[simp, grind =]
theorem controllerPaths_nil {Party : Type u} {process : Process Party}
    {p : process.Proc} :
    controllerPaths (.nil : Prefix process p 0) = [] := rfl

@[simp, grind =]
theorem events_nil {Party : Type u} {process : Process Party}
    {Event : Type w} (eventMap : process.EventMap Event)
    {p : process.Proc} :
    events eventMap (.nil : Prefix process p 0) = [] := rfl

@[simp, grind =]
theorem tickets_nil {Party : Type u} {process : Process Party}
    {Ticket : Type w} (ticketMap : process.Tickets Ticket)
    {p : process.Proc} :
    tickets ticketMap (.nil : Prefix process p 0) = [] := rfl

end Prefix

/--
`Run process` is an infinite execution of the dynamic process `process`.

It is represented by:

* `state n`, the residual process state after `n` complete process steps;
* `transcript n`, the concrete transcript chosen for step `n`;
* `next_state`, which states that the residual state stream follows the
  process continuation exactly.

This is a continuation-based infinite semantics: the run does not introduce a
new operational state space of its own. It simply records how the residual
process state evolves when one complete process step is chosen at each time.
-/
structure Run {Party : Type u} (process : Process Party) where
  state : Nat → process.Proc
  transcript : (n : Nat) → (process.step (state n)).spec.Transcript
  next_state : ∀ n, state n.succ = (process.step (state n)).next (transcript n)

namespace Run

/--
The initial residual process state of a run.
-/
def initial {Party : Type u} {process : Process Party}
    (run : Run process) : process.Proc :=
  run.state 0

/--
The first complete process-step transcript of the run.

This is the step that carries the system from `run.initial` to `run.tail.initial`.
-/
def head {Party : Type u} {process : Process Party}
    (run : Run process) : (process.step run.initial).spec.Transcript := by
  simpa [Run.initial] using run.transcript 0

/--
The tail of a run after its first process step.

Operationally, `run.tail` is the same execution observed one process step
later.
-/
def tail {Party : Type u} {process : Process Party}
    (run : Run process) :
    Run process where
  state n := run.state n.succ
  transcript n := by
    simpa using run.transcript n.succ
  next_state n := by
    simpa using run.next_state n.succ

/--
The initial state of `run.tail` is exactly the residual state obtained by
executing `run.head`.
-/
theorem tail_initial {Party : Type u} {process : Process Party}
    (run : Run process) :
    run.tail.initial = (process.step run.initial).next run.head := by
  change run.state 1 = (process.step run.initial).next run.head
  simpa [Run.initial, Run.head] using run.next_state 0

/--
`take run n` is the length-`n` finite execution prefix of the infinite run
`run`.

This is the basic bridge from infinitary runs back to finite prefix reasoning.
-/
def take {Party : Type u} {process : Process Party}
    (run : Run process) : (n : Nat) → Prefix process run.initial n
  | 0 => .nil
  | n + 1 =>
      .step run.head (cast (by
        rw [run.tail_initial]) (run.tail.take n))

/--
The current controlling party of step `n` of a run, if any.
-/
def currentController? {Party : Type u} {process : Process Party}
    (run : Run process) (n : Nat) : Option Party :=
  (process.step (run.state n)).currentController? (run.transcript n)

/-- The current controlling parties exposed along the first `n` executed steps
of the run `run`. -/
def currentControllersUpTo {Party : Type u} {process : Process Party}
    (run : Run process) : Nat → List (Option Party)
  | 0 => []
  | n + 1 => run.currentController? 0 :: run.tail.currentControllersUpTo n

/--
The full controller path recorded by step `n` of a run.
-/
def controllerPath {Party : Type u} {process : Process Party}
    (run : Run process) (n : Nat) : List Party :=
  (process.step (run.state n)).controllerPath (run.transcript n)

/-- The full controller paths exposed along the first `n` executed steps of the
run `run`. -/
def controllerPathsUpTo {Party : Type u} {process : Process Party}
    (run : Run process) : Nat → List (List Party)
  | 0 => []
  | n + 1 => run.controllerPath 0 :: run.tail.controllerPathsUpTo n

/--
The stable event label attached to step `n` of a run.
-/
def event {Party : Type u} {process : Process Party}
    {Event : Type w} (eventMap : process.EventMap Event)
    (run : Run process) (n : Nat) : Event :=
  eventMap (run.state n) (run.transcript n)

/-- The stable event labels attached to the first `n` executed steps of the run
`run`. -/
def eventsUpTo {Party : Type u} {process : Process Party}
    {Event : Type w} (eventMap : process.EventMap Event)
    (run : Run process) : Nat → List Event
  | 0 => []
  | n + 1 => run.event eventMap 0 :: run.tail.eventsUpTo eventMap n

/--
The stable ticket attached to step `n` of a run.
-/
def ticket {Party : Type u} {process : Process Party}
    {Ticket : Type w} (ticketMap : process.Tickets Ticket)
    (run : Run process) (n : Nat) : Ticket :=
  ticketMap (run.state n) (run.transcript n)

/-- The stable tickets attached to the first `n` executed steps of the run
`run`. -/
def ticketsUpTo {Party : Type u} {process : Process Party}
    {Ticket : Type w} (ticketMap : process.Tickets Ticket)
    (run : Run process) : Nat → List Ticket
  | 0 => []
  | n + 1 => run.ticket ticketMap 0 :: run.tail.ticketsUpTo ticketMap n

@[simp, grind =]
theorem take_zero {Party : Type u} {process : Process Party}
    (run : Run process) :
    run.take 0 = Prefix.nil := rfl

@[simp, grind =]
theorem take_succ {Party : Type u} {process : Process Party}
    (run : Run process) (n : Nat) :
    run.take (n + 1) =
      Prefix.step run.head (cast (by rw [run.tail_initial]) (run.tail.take n)) := rfl

@[simp, grind =]
theorem currentControllersUpTo_zero {Party : Type u} {process : Process Party}
    (run : Run process) :
    run.currentControllersUpTo 0 = [] := rfl

@[simp, grind =]
theorem controllerPathsUpTo_zero {Party : Type u} {process : Process Party}
    (run : Run process) :
    run.controllerPathsUpTo 0 = [] := rfl

@[simp, grind =]
theorem eventsUpTo_zero {Party : Type u} {process : Process Party}
    {Event : Type w} (eventMap : process.EventMap Event)
    (run : Run process) :
    run.eventsUpTo eventMap 0 = [] := rfl

@[simp, grind =]
theorem ticketsUpTo_zero {Party : Type u} {process : Process Party}
    {Ticket : Type w} (ticketMap : process.Tickets Ticket)
    (run : Run process) :
    run.ticketsUpTo ticketMap 0 = [] := rfl

@[simp, grind =]
theorem currentControllersUpTo_succ {Party : Type u} {process : Process Party}
    (run : Run process) (n : Nat) :
    run.currentControllersUpTo (n + 1) =
      run.currentController? 0 :: run.tail.currentControllersUpTo n := rfl

@[simp, grind =]
theorem controllerPathsUpTo_succ {Party : Type u} {process : Process Party}
    (run : Run process) (n : Nat) :
    run.controllerPathsUpTo (n + 1) =
      run.controllerPath 0 :: run.tail.controllerPathsUpTo n := rfl

@[simp, grind =]
theorem eventsUpTo_succ {Party : Type u} {process : Process Party}
    {Event : Type w} (eventMap : process.EventMap Event)
    (run : Run process) (n : Nat) :
    run.eventsUpTo eventMap (n + 1) =
      run.event eventMap 0 :: run.tail.eventsUpTo eventMap n := rfl

@[simp, grind =]
theorem ticketsUpTo_succ {Party : Type u} {process : Process Party}
    {Ticket : Type w} (ticketMap : process.Tickets Ticket)
    (run : Run process) (n : Nat) :
    run.ticketsUpTo ticketMap (n + 1) =
      run.ticket ticketMap 0 :: run.tail.ticketsUpTo ticketMap n := rfl

end Run

end Process
end Concurrent
end Interaction
