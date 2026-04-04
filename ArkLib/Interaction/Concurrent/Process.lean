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

This file introduces the semantic center of the concurrent `Interaction`
layer.

The structural syntax in `Concurrent.Spec` is a useful source language, but it
is not the only natural presentation of concurrency. Many systems are better
viewed as a **residual process** which, at any moment, exposes one finite
sequential interaction episode; completing that episode yields the next
residual process.

That is the viewpoint formalized here.

The file is organized in two levels:

* `StepOver Γ P` and `ProcessOver Γ` are the generic forms, parameterized by a
  realized node context `Γ`;
* `Step Party P` and `Process Party` are the closed-world specializations whose
  node metadata is exactly `NodeSemantics Party`.

So the intended reading is:

* a **step** is one finite local protocol episode,
* a **process** is an unbounded sequence of such steps obtained by
  continuation,
* and controller / observation metadata lives in a node context rather than
  being built into the process infrastructure itself.

This design stays continuation-first, but is more general than the structural
tree frontend: cyclic or unbounded behavior is represented by the residual
state type, while each individual step remains a finite `Interaction.Spec`.
-/

universe u v w w₂ w₃

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

/--
The closed-world node context used by the current concurrent semantics.

At a node with move space `X`, the context value is exactly the
`NodeSemantics Party X` describing:

* which parties are recorded as controllers of the chosen move, and
* what each party locally observes of that move.

This is the context whose specialization recovers the existing closed-world
`Step` / `Process` APIs.
-/
abbrev StepContext (Party : Type u) := fun X => NodeSemantics Party X

/--
`StepOver Γ P` is one finite sequential interaction episode whose nodes are
decorated by realized context `Γ`, and whose completion produces the next
residual process state `P`.

Fields:

* `spec` is the shape of the sequential interaction episode;
* `semantics` decorates that sequential tree by node-local context `Γ`;
* `next` maps a complete transcript of that episode to the next residual
  process state.

The important point is that a `StepOver` is **not** restricted to a single
atomic event. One concurrent step may itself be a short sequential protocol:
for example, a scheduler choice followed by a payload choice, or a small
request/response exchange treated as one logical concurrent transition.

So `StepOver` is the right object when the concurrency layer should expose
finite sequential structure inside each global step, rather than flattening
everything into atomic transitions.
-/
structure StepOver (Γ : Interaction.Spec.Node.Context.{w, w₂}) (P : Type v) where
  spec : Interaction.Spec.{w}
  semantics : Interaction.Spec.Decoration Γ spec
  next : Interaction.Spec.Transcript spec → P

/--
`ProcessOver Γ` is a continuation-based concurrent process whose current step
episodes are decorated by realized context `Γ`.

From any residual process state `p : Proc`, the process exposes exactly one
step protocol `step p : StepOver Γ Proc`. Running that step to completion
produces the next residual state.

So `ProcessOver` should be read as:

> a system whose behavior unfolds as a sequence of finite step protocols.

This is the generic semantic center for the concurrent layer. Structural
trees, flat machines, and future frontends can all compile into `ProcessOver`
by choosing an appropriate node-local context `Γ`.
-/
structure ProcessOver (Γ : Interaction.Spec.Node.Context.{w, w₂}) where
  Proc : Type v
  step : Proc → StepOver Γ Proc

namespace ProcessOver

/--
A stable external label for each complete step transcript of a process.

The point of an `EventMap` is to attach one comparison-friendly label to a
whole step, independently of how much internal sequential structure that step
contains.
-/
abbrev EventMap {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (process : ProcessOver.{v, w, w₂} Γ) (Event : Type w₃) :=
  (p : process.Proc) → Interaction.Spec.Transcript (process.step p).spec → Event

/--
A stable ticket for each complete step transcript of a process.

Tickets are the intended handles for fairness and liveness: instead of talking
about unstable frontier events whose types change from state to state, later
semantic layers can talk about these stable identifiers.
-/
abbrev Tickets {Γ : Interaction.Spec.Node.Context.{w, w₂}}
    (process : ProcessOver.{v, w, w₂} Γ) (Ticket : Type w₃) :=
  (p : process.Proc) → Interaction.Spec.Transcript (process.step p).spec → Ticket

end ProcessOver

/--
The closed-world specialization of `StepOver`.

Here the node context is fixed to `StepContext Party`, so every node carries
the usual controller-path and local-view data for that party universe.
-/
abbrev Step (Party : Type u) (P : Type v) :=
  StepOver (StepContext Party) P

namespace Step

/--
`controllerPath step tr` is the controller sequence exposed by the concrete
step transcript `tr`.

Every visited node contributes the controller list recorded for the chosen
move at that node. These per-node contributions are concatenated along the
whole step transcript.

So if a step internally consists of, say, "the scheduler chooses a branch,
then Alice chooses a payload", the controller path records both pieces in
order.
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
`currentController? step tr` is the head of the controller path exposed by the
concrete transcript `tr`, if such a controller exists.

This is the most immediate "who controlled this step?" projection. It is only
the first controller because one step may internally contain several
controlled subchoices.
-/
def currentController? {Party : Type u} {P : Type v} (step : Step Party P)
    (tr : Interaction.Spec.Transcript step.spec) : Option Party :=
  step.controllerPath tr |>.head?
end Step

namespace StepOver

/--
Closed-world controller-path projection for a `StepOver` specialized to
`StepContext Party`.

This bridge keeps the old dot-notation ergonomics after the `StepOver`
cutover: downstream closed-world code can still write
`(process.step p).controllerPath tr`.
-/
abbrev controllerPath {Party : Type u} {P : Type v}
    (step : StepOver (StepContext Party) P) :
    Interaction.Spec.Transcript step.spec → List Party :=
  Step.controllerPath step

/--
Closed-world current-controller projection for a `StepOver` specialized to
`StepContext Party`.
-/
abbrev currentController? {Party : Type u} {P : Type v}
    (step : StepOver (StepContext Party) P)
    (tr : Interaction.Spec.Transcript step.spec) : Option Party :=
  Step.currentController? step tr

end StepOver

/--
The closed-world specialization of `ProcessOver`.

This is the process type consumed by the current execution, run, observation,
refinement, fairness, and liveness layers.
-/
abbrev Process (Party : Type u) :=
  ProcessOver (StepContext Party)

namespace Process

/--
A stable external label for each complete closed-world process step.
-/
abbrev EventMap {Party : Type u} (process : Process Party) (Event : Type w₂) :=
  (p : process.Proc) → Interaction.Spec.Transcript (process.step p).spec → Event

/--
A stable ticket for each complete closed-world process step.
-/
abbrev Tickets {Party : Type u} (process : Process Party) (Ticket : Type w₂) :=
  (p : process.Proc) → Interaction.Spec.Transcript (process.step p).spec → Ticket

/--
`Process.Labeled` is a closed-world process together with a stable event label
for each complete step transcript.
-/
structure Labeled (Party : Type u) where
  toProcess : Process Party
  Event : Type w₂
  event : toProcess.EventMap Event

/--
`Process.Ticketed` is a closed-world process together with a stable ticket for
each complete step transcript.

These tickets are the obligation identifiers used later by the fairness and
liveness layers.
-/
structure Ticketed (Party : Type u) where
  toProcess : Process Party
  Ticket : Type w₂
  ticket : toProcess.Tickets Ticket

/--
`Process.System` augments a closed-world process by the standard verification
predicates used throughout ArkLib and in transition-system-style frameworks.

Its parent field `toProcess` is the dynamic semantics; the remaining fields are
verification metadata on top of that semantics:

* `init` marks initial residual states;
* `assumptions` records ambient assumptions on runs;
* `safe` is the intended state safety predicate;
* `inv` is the intended inductive invariant.

This keeps the semantic object and the proof obligations separate while still
bundling them in one place for refinement and liveness statements.
-/
structure System (Party : Type u) extends toProcess : ProcessOver (StepContext Party) where
  init : Proc → Prop
  assumptions : Proc → Prop := fun _ => True
  safe : Proc → Prop := fun _ => True
  inv : Proc → Prop := fun _ => True

end Process
end Concurrent
end Interaction
