/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Concurrent.Execution

/-!
# Executable scheduler policies for finite concurrent traces

This file adds a lightweight policy layer on top of finite concurrent traces.

The earlier concurrent modules already provide:

* `Trace S` — a finite scheduler linearization of frontier events;
* `Control` — who currently controls each scheduler or payload choice;
* `Current` — the current local view and current controller of the next step.

The present file packages one further notion:

* a `StepPolicy Party` is an executable Boolean constraint on the next frontier
  event, given the current residual control tree;
* `Trace.respects policy control trace` checks whether every step of the trace
  satisfies that policy.

This is the right finite analogue of scheduler constraints in the current
concurrent core. It intentionally stops short of a full fairness theory: true
fairness and liveness conditions are fundamentally about unbounded or infinite
executions, so they belong to a later recursive or coinductive extension of the
concurrent syntax rather than this finite tree-based layer.
-/

universe u

namespace Interaction
namespace Concurrent

/--
`StepPolicy Party` is an executable constraint on one concurrent frontier step.

A policy sees:

* the current residual concurrent spec through its indexed control tree
  `control : Control Party S`;
* the concrete frontier event `event : Front S` selected at that step.

It then returns `true` when that step is allowed and `false` when it is
forbidden.

The policy itself is intentionally local to one step. Whole-trace compliance is
defined later by `Trace.respects`.
-/
abbrev StepPolicy (Party : Type u) := {S : Spec} → Control Party S → Front S → Bool

namespace StepPolicy

/-- The permissive policy that allows every frontier step. -/
def top {Party : Type u} : StepPolicy Party := fun _ _ => true

/-- Conjunction of two step policies. A step is allowed iff both component
policies allow it. -/
def inter {Party : Type u} (left right : StepPolicy Party) : StepPolicy Party :=
  fun control event => left control event && right control event

/--
`byScheduler allow` constrains only the current scheduler, when a genuine
scheduler choice exists.

If `Current.scheduler? control = some s`, the current step is allowed exactly
when `allow s = true`. If there is no current scheduler, the policy is
vacuously satisfied.
-/
def byScheduler {Party : Type u} (allow : Party → Bool) : StepPolicy Party :=
  fun control _ =>
    match Current.scheduler? control with
    | some scheduler => allow scheduler
    | none => true

/--
`byController allow` constrains the current controller of progress, whether
that is a scheduler at a live `par` node or an atomic payload owner.

If `Current.controller? control = some p`, the current step is allowed exactly
when `allow p = true`. If there is no current controller, the policy is
vacuously satisfied.
-/
def byController {Party : Type u} (allow : Party → Bool) : StepPolicy Party :=
  fun control _ =>
    match Current.controller? control with
    | some controller => allow controller
    | none => true

/--
`scheduledEvent allow` constrains the concrete frontier event only when a
genuine scheduler choice exists.

This is useful for policies such as "whenever both sides are live, prefer the
left branch" or "scheduler `adv` may only pick delivery events with public
metadata satisfying some predicate".
-/
def scheduledEvent {Party : Type u}
    (allow : Party → {S : Spec} → Front S → Bool) : StepPolicy Party :=
  fun control event =>
    match Current.scheduler? control with
    | some scheduler => allow scheduler event
    | none => true

end StepPolicy

namespace Trace

/--
`respects policy control trace` checks whether every step of the finite trace
`trace` satisfies the executable step policy `policy`.

This is computed recursively over the trace:

* a quiescent finished trace always respects the policy;
* a step trace respects the policy iff the current event is allowed and the
  residual trace respects the policy under the residual control tree.
-/
def respects {Party : Type u} (policy : StepPolicy Party) :
    {S : Spec} → (control : Control Party S) → Trace S → Bool
  | _, _, .done _ => true
  | _, control, .step event tail =>
      policy control event &&
        respects policy (Control.residual control event) tail

@[simp, grind =]
theorem respects_top {Party : Type u} {S : Spec}
    (control : Control Party S) (trace : Trace S) :
    respects StepPolicy.top control trace = true := by
  induction trace with
  | done h => rfl
  | step event tail ih =>
      simp [Trace.respects, StepPolicy.top, ih]

end Trace

end Concurrent
end Interaction
