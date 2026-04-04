/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Basic.Spec
import ArkLib.Interaction.Basic.Decoration
import ArkLib.Interaction.Multiparty.Core

/-!
# Dynamic concurrent processes

This file introduces the continuation-based semantic center for the concurrent
interaction layer.

The existing structural concurrent syntax in `Concurrent.Spec` is a very useful
source language: it provides a finite syntax of atomic nodes and binary `par`.
But it is still only one presentation of concurrency. A more general semantic
object is a **residual process** whose next global step is itself a finite
sequential interaction protocol.

That is the role of this file.

Main definitions:

* `NodeSemantics Party X` records, at one sequential interaction node with move
  space `X`, both:
  * the controller path contribution of each chosen move; and
  * the per-party local views of the node's chosen move.
* `Step Party P` is one finite sequential interaction episode whose completion
  yields the next residual process state `P`.
* `Process Party` is a continuation-based concurrent process: from any residual
  process state, it exposes one `Step`.
* `Process.System Party` adds standard verification predicates such as `init`
  and `safe`.

This design is deliberately more general than the structural tree frontend:
it supports cyclic or unbounded behavior by allowing the residual process state
type to be arbitrary, while still keeping the interaction layer continuation-
first and tree-based at each individual step.
-/

universe u v w

namespace Interaction
namespace Concurrent

/--
`NodeSemantics Party X` records the local semantic data attached to one
sequential interaction node whose move space is `X`.

It packages two orthogonal pieces of information:

* `controllers x` is the controller-path contribution associated to choosing
  the move `x : X`;
* `views` assigns to each party its local view of the chosen move `x : X`.

The controller-path contribution and the local views are intentionally stored
separately. Many natural systems align them so that the first controller in
`controllers x` has local view `active`, but this file does not force that
relationship definitionally.
Any desired coherence law can be imposed later as a separate well-formedness
predicate.
-/
structure NodeSemantics (Party : Type u) (X : Type w) where
  controllers : X → List Party := fun _ => []
  views : Party → Multiparty.LocalView X

/-- The realized node context of per-node controller and local-view metadata. -/
abbrev StepContext (Party : Type u) := fun X => NodeSemantics Party X

/--
`Step Party P` is one finite sequential interaction episode whose completion
produces the next residual process state `P`.

Fields:

* `spec` is the shape of the sequential interaction episode;
* `semantics` decorates that sequential tree by `NodeSemantics Party`, giving
  controller and local-view data at each node;
* `next` maps a complete transcript of that step to the next residual process
  state.

So a `Step` is not merely a one-node enabled-event interface. It may be a
whole finite interaction protocol in its own right, while still remaining
purely continuation-based.
-/
structure Step (Party : Type u) (P : Type v) where
  spec : Interaction.Spec.{w}
  semantics : Interaction.Spec.Decoration (StepContext Party) spec
  next : Interaction.Spec.Transcript spec → P

namespace Step

/--
`controllerPath step tr` is the sequence of recorded controllers along the
concrete transcript `tr` through the sequential step `step`.

At each visited node, the path contribution `node.controllers x` associated to
the chosen move `x` is prepended to the recursively computed tail path.
-/
def controllerPath {Party : Type u} {P : Type v} (step : Step Party P) :
    Interaction.Spec.Transcript step.spec → List Party := by
  let rec go :
      {spec : Interaction.Spec.{w}} →
      Interaction.Spec.Decoration (StepContext Party) spec →
      Interaction.Spec.Transcript spec →
      List Party
    | .done, _, _ => []
    | .node _ rest, ⟨node, restSemantics⟩, ⟨x, tail⟩ =>
        node.controllers x ++ go (restSemantics x) tail
  intro tr
  exact go step.semantics tr

/--
`currentController? step tr` is the first controller, if any, on the concrete
controller path exposed by the transcript `tr`.

Unlike the earlier tree-specific concurrent execution layer, the current
controller of a process step may in general depend on the chosen transcript of
that step protocol itself.
-/
def currentController? {Party : Type u} {P : Type v} (step : Step Party P)
    (tr : Interaction.Spec.Transcript step.spec) : Option Party :=
  step.controllerPath tr |>.head?
end Step

/--
`Process Party` is a continuation-based concurrent process with parties `Party`.

From any residual process state `p : Proc`, the process exposes exactly one
sequential interaction `step p`. Executing a complete transcript of that step
produces the next residual process state.

This is the dynamic semantic center for the concurrent interaction layer:
different frontends, such as state machines or structural parallel syntax,
can compile into `Process`.
-/
structure Process (Party : Type u) where
  Proc : Type v
  step : Proc → Step.{u, v, w} Party Proc

namespace Process

/-- A stable external event map for the step transcripts of a process. -/
abbrev EventMap {Party : Type u} (process : Process Party) (Event : Type w) :=
  (p : process.Proc) → Interaction.Spec.Transcript (process.step p).spec → Event

/-- A stable ticket map for the step transcripts of a process. Tickets are the
intended handle for future fairness and liveness layers. -/
abbrev Tickets {Party : Type u} (process : Process Party) (Ticket : Type w) :=
  (p : process.Proc) → Interaction.Spec.Transcript (process.step p).spec → Ticket

/--
`Process.Labeled` is a process equipped with a stable external event label for
each complete step transcript.
-/
structure Labeled (Party : Type u) where
  toProcess : Process Party
  Event : Type w
  event : toProcess.EventMap Event

/--
`Process.Ticketed` is a process equipped with a stable ticket for each complete
step transcript.

These tickets are the intended obligation identifiers for later fairness and
liveness layers.
-/
structure Ticketed (Party : Type u) where
  toProcess : Process Party
  Ticket : Type w
  ticket : toProcess.Tickets Ticket

/--
`Process.System` augments a process by the standard verification predicates used
throughout ArkLib and in transition-system-style frameworks such as Veil.

These predicates are intentionally metadata on top of the dynamic process
semantics:
* `init` marks initial residual states;
* `assumptions` records ambient assumptions;
* `safe` is the intended safety property;
* `inv` is the intended inductive invariant.
-/
structure System (Party : Type u) extends Process Party where
  init : Proc → Prop
  assumptions : Proc → Prop := fun _ => True
  safe : Proc → Prop := fun _ => True
  inv : Proc → Prop := fun _ => True

end Process
end Concurrent
end Interaction
