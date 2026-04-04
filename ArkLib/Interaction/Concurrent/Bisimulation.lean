/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Concurrent.Refinement

/-!
# Bisimulation for dynamic concurrent processes

This file adds the symmetric refinement layer on top of
`Concurrent.Refinement.ForwardSimulation`.

`ForwardSimulation` is intentionally one-way: it shows that every behavior of
an implementation can be matched by some behavior of a specification. The
purpose of this file is to package the corresponding two-way notion used when
two systems should count as behaviorally equivalent rather than merely
implementing one another.

The construction is deliberately simple:

* a backward simulation is just a forward simulation with the two systems
  swapped;
* a bisimulation packages one simulation in each direction; and
* once both directions are available, safety results can be transported either
  way, provided the chosen fairness assumptions also transfer.

This keeps the equivalence layer aligned with the existing process-centered
refinement API rather than introducing a second semantic style.
-/

universe u v w

namespace Interaction
namespace Concurrent

namespace Observation
namespace Process
namespace TranscriptRel

/--
Reverse a transcript-matching relation by flipping its two transcript
arguments.

This is the basic step needed to reinterpret a forward step-matching condition
as a backward one.
-/
def reverse {Party : Type u}
    {left right : Process Party}
    (rel : TranscriptRel left right) :
    TranscriptRel right left :=
  fun trR trL => rel trL trR

end TranscriptRel
end Process
end Observation

namespace Refinement

/--
`ForwardSimulation.refl system matchStep` is the identity simulation on
`system`, provided that `matchStep` relates each transcript to itself.

This is the canonical witness that every system refines itself.
-/
def ForwardSimulation.refl {Party : Type u}
    (system : Process.System Party)
    (matchStep :
      Observation.Process.TranscriptRel system.toProcess system.toProcess :=
        Observation.Process.TranscriptRel.top)
    (hmatch :
      ∀ {p : system.Proc} (tr : (system.step p).spec.Transcript),
        matchStep tr tr) :
    ForwardSimulation system system matchStep where
  stateRel p q := p = q
  init p hp := ⟨p, hp, rfl⟩
  assumptions
    | rfl, h => h
  step
    | rfl, tr => ⟨tr, hmatch tr, rfl⟩
  safe
    | rfl, h => h

/--
`BackwardSimulation impl spec matchStep` is just a forward simulation from
`spec` to `impl`, with the transcript-matching relation reversed accordingly.

So "backward simulation" is only a change of viewpoint, not a second primitive
notion.
-/
abbrev BackwardSimulation {Party : Type u}
    (impl spec : Process.System Party)
    (matchStep :
      Observation.Process.TranscriptRel impl.toProcess spec.toProcess :=
        Observation.Process.TranscriptRel.top) :=
  ForwardSimulation spec impl (Observation.Process.TranscriptRel.reverse matchStep)

/--
`Bisimulation left right matchForth matchBack` packages one forward simulation
in each direction between `left` and `right`.

By default, the backward transcript-matching relation is the reversal of the
forward one.

This is the library's main process-level equivalence witness: each side can
match the other's executions while preserving the chosen step relation.
-/
structure Bisimulation {Party : Type u}
    (left right : Process.System Party)
    (matchForth :
      Observation.Process.TranscriptRel left.toProcess right.toProcess :=
        Observation.Process.TranscriptRel.top)
    (matchBack :
      Observation.Process.TranscriptRel right.toProcess left.toProcess :=
        Observation.Process.TranscriptRel.reverse matchForth) where
  forth : ForwardSimulation left right matchForth
  back : ForwardSimulation right left matchBack

namespace Bisimulation

/--
Swap the two sides of a bisimulation.

This is the symmetry principle for the packaged equivalence witness itself.
-/
def symm {Party : Type u}
    {left right : Process.System Party}
    {matchForth :
      Observation.Process.TranscriptRel left.toProcess right.toProcess}
    {matchBack :
      Observation.Process.TranscriptRel right.toProcess left.toProcess}
    (bisim : Bisimulation left right matchForth matchBack) :
    Bisimulation right left matchBack matchForth where
  forth := bisim.back
  back := bisim.forth

/--
The identity bisimulation on `system`, provided that both transcript relations
relate every transcript to itself.

This is the reflexivity principle for the packaged equivalence witness.
-/
def refl {Party : Type u}
    (system : Process.System Party)
    (matchForth :
      Observation.Process.TranscriptRel system.toProcess system.toProcess :=
        Observation.Process.TranscriptRel.top)
    (matchBack :
      Observation.Process.TranscriptRel system.toProcess system.toProcess :=
        Observation.Process.TranscriptRel.reverse matchForth)
    (hForth :
      ∀ {p : system.Proc} (tr : (system.step p).spec.Transcript),
        matchForth tr tr)
    (hBack :
      ∀ {p : system.Proc} (tr : (system.step p).spec.Transcript),
        matchBack tr tr) :
    Bisimulation system system matchForth matchBack where
  forth := ForwardSimulation.refl system matchForth hForth
  back := ForwardSimulation.refl system matchBack hBack

/--
Transport safety from the right system to the left system under a bisimulation,
assuming the chosen fairness predicates transfer along the forward direction.

This is the "use the right-hand system as the proof-oriented model" direction.
-/
theorem left_safe_of_satisfies {Party : Type u}
    {left right : Process.System Party}
    {matchForth :
      Observation.Process.TranscriptRel left.toProcess right.toProcess}
    {matchBack :
      Observation.Process.TranscriptRel right.toProcess left.toProcess}
    (bisim : Bisimulation left right matchForth matchBack)
    (fairLeft : Process.Run.Pred left.toProcess)
    (fairRight : Process.Run.Pred right.toProcess)
    (hfair :
      ∀ (run : Process.Run left.toProcess) {pRight : right.Proc},
        (hrel : bisim.forth.stateRel run.initial pRight) →
          fairLeft run → fairRight (bisim.forth.mapRun run hrel))
    (hright : Process.System.Satisfies right fairRight (Process.System.Safe right)) :
    Process.System.Satisfies left fairLeft (Process.System.Safe left) :=
  bisim.forth.safe_of_satisfies fairLeft fairRight hfair hright

/--
Transport safety from the left system to the right system under a bisimulation,
assuming the chosen fairness predicates transfer along the backward direction.

This is the same transport principle in the opposite direction.
-/
theorem right_safe_of_satisfies {Party : Type u}
    {left right : Process.System Party}
    {matchForth :
      Observation.Process.TranscriptRel left.toProcess right.toProcess}
    {matchBack :
      Observation.Process.TranscriptRel right.toProcess left.toProcess}
    (bisim : Bisimulation left right matchForth matchBack)
    (fairLeft : Process.Run.Pred left.toProcess)
    (fairRight : Process.Run.Pred right.toProcess)
    (hfair :
      ∀ (run : Process.Run right.toProcess) {pLeft : left.Proc},
        (hrel : bisim.back.stateRel run.initial pLeft) →
          fairRight run → fairLeft (bisim.back.mapRun run hrel))
    (hleft : Process.System.Satisfies left fairLeft (Process.System.Safe left)) :
    Process.System.Satisfies right fairRight (Process.System.Safe right) :=
  bisim.back.safe_of_satisfies fairRight fairLeft hfair hleft

/--
Safety under fairness assumptions is equivalent across a bisimulation when the
fairness assumptions themselves transfer in both directions.

So once fairness transport is established, either side of a bisimulation may be
used as the proof-oriented presentation of the protocol.
-/
theorem safe_iff_of_satisfies {Party : Type u}
    {left right : Process.System Party}
    {matchForth :
      Observation.Process.TranscriptRel left.toProcess right.toProcess}
    {matchBack :
      Observation.Process.TranscriptRel right.toProcess left.toProcess}
    (bisim : Bisimulation left right matchForth matchBack)
    (fairLeft : Process.Run.Pred left.toProcess)
    (fairRight : Process.Run.Pred right.toProcess)
    (hfairLeft :
      ∀ (run : Process.Run left.toProcess) {pRight : right.Proc},
        (hrel : bisim.forth.stateRel run.initial pRight) →
          fairLeft run → fairRight (bisim.forth.mapRun run hrel))
    (hfairRight :
      ∀ (run : Process.Run right.toProcess) {pLeft : left.Proc},
        (hrel : bisim.back.stateRel run.initial pLeft) →
          fairRight run → fairLeft (bisim.back.mapRun run hrel)) :
    Process.System.Satisfies left fairLeft (Process.System.Safe left) ↔
      Process.System.Satisfies right fairRight (Process.System.Safe right) := by
  constructor
  · exact bisim.right_safe_of_satisfies fairLeft fairRight hfairRight
  · exact bisim.left_safe_of_satisfies fairLeft fairRight hfairLeft

end Bisimulation

end Refinement
end Concurrent
end Interaction
