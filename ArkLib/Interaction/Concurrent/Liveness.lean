/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Concurrent.Fairness

/-!
# Safety and liveness predicates over concurrent runs

This file packages the semantic notions of safety and liveness that sit on top
of runs and fairness.

The goal is deliberately modest and foundational. Rather than introducing a
full temporal-logic syntax, the file defines:

* run predicates and state predicates;
* the basic temporal lifts of a state predicate along a run;
* admissibility, safety, and initiality for `Process.System`; and
* what it means for a system to satisfy a run property under a chosen fairness
  assumption.

This gives a clean semantic layer for later protocol-specific theorems without
committing the library to any one temporal-logic frontend.
-/

universe u v w

namespace Interaction
namespace Concurrent

namespace Process
namespace Run

/--
`Pred process` is the type of semantic properties of whole runs of `process`.
-/
abbrev Pred {Party : Type u} (process : Process Party) :=
  Process.Run process → Prop

/--
`StatePred process` is the type of predicates on residual process states.
-/
abbrev StatePred {Party : Type u} (process : Process Party) :=
  process.Proc → Prop

/-- `AlwaysState P run` means that the state predicate `P` holds at every state
of the run `run`. -/
def AlwaysState {Party : Type u} {process : Process Party}
    (P : StatePred process) (run : Process.Run process) : Prop :=
  ∀ n, P (run.state n)

/--
`EventuallyState P run` means that the run eventually reaches a state
satisfying `P`.
-/
def EventuallyState {Party : Type u} {process : Process Party}
    (P : StatePred process) (run : Process.Run process) : Prop :=
  ∃ n, P (run.state n)

/-- `InfinitelyOftenState P run` means that `P` holds at arbitrarily late
states of `run`. -/
def InfinitelyOftenState {Party : Type u} {process : Process Party}
    (P : StatePred process) (run : Process.Run process) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ P (run.state n)

/--
Monotonicity of `AlwaysState`.
-/
theorem alwaysState_mono {Party : Type u} {process : Process Party}
    {P Q : StatePred process}
    (himp : ∀ p, P p → Q p) :
    ∀ {run : Process.Run process}, AlwaysState P run → AlwaysState Q run := by
  intro run hP n
  exact himp _ (hP n)

/--
Monotonicity of `EventuallyState`.
-/
theorem eventuallyState_mono {Party : Type u} {process : Process Party}
    {P Q : StatePred process}
    (himp : ∀ p, P p → Q p) :
    ∀ {run : Process.Run process}, EventuallyState P run → EventuallyState Q run := by
  rintro run ⟨n, hP⟩
  exact ⟨n, himp _ hP⟩

/--
Monotonicity of `InfinitelyOftenState`.
-/
theorem infinitelyOftenState_mono {Party : Type u} {process : Process Party}
    {P Q : StatePred process}
    (himp : ∀ p, P p → Q p) :
    ∀ {run : Process.Run process},
      InfinitelyOftenState P run → InfinitelyOftenState Q run := by
  intro run hP N
  rcases hP N with ⟨n, hn, hPn⟩
  exact ⟨n, hn, himp _ hPn⟩

end Run

namespace System

/-- A run of `system` is admissible when the ambient assumptions hold at every
state along the run. -/
def Admissible {Party : Type u} (system : Process.System Party)
    (run : Process.Run system.toProcess) : Prop :=
  Process.Run.AlwaysState system.assumptions run

/-- A run of `system` is safe when the safety predicate holds at every state
along the run. -/
def Safe {Party : Type u} (system : Process.System Party)
    (run : Process.Run system.toProcess) : Prop :=
  Process.Run.AlwaysState system.safe run

/--
A run starts from an initial state when its first residual process state
satisfies `system.init`.
-/
def Initial {Party : Type u} (system : Process.System Party)
    (run : Process.Run system.toProcess) : Prop :=
  system.init run.initial

/--
`Satisfies system fairness property` means:
every initial admissible run of `system` that satisfies the fairness
assumption `fairness` also satisfies the run property `property`.

This is the top-level semantic judgment used by later protocol proofs.
-/
def Satisfies {Party : Type u} (system : Process.System Party)
    (fairness property : Process.Run.Pred system.toProcess) : Prop :=
  ∀ run : Process.Run system.toProcess,
    Initial system run →
      Admissible system run →
        fairness run →
          property run

/--
If a run is safe and every safe state satisfies `P`, then `P` holds at every
state along the run.

This is the basic way to derive invariant-style consequences from the system's
declared safety predicate.
-/
theorem alwaysState_of_safe {Party : Type u} (system : Process.System Party)
    {P : Process.Run.StatePred system.toProcess}
    (himp : ∀ p, system.safe p → P p) :
    ∀ {run : Process.Run system.toProcess},
      Safe system run → Process.Run.AlwaysState P run := by
  intro run hsafe n
  exact himp _ (hsafe n)

end System

end Process
end Concurrent
end Interaction
