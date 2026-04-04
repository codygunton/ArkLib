/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Concurrent.Run

/-!
# Fairness of dynamic concurrent runs

This file adds the first fairness layer on top of `Concurrent.Process.Run`.

The key design choice is that fairness is phrased in terms of stable
`Tickets`, not raw frontier events. This matters because the concrete event
type available at one residual process state need not even be comparable with
the event type at a later state, while a ticket is meant to name the same
scheduling obligation across time and across different presentations of the
same protocol.

So the fairness notions here answer questions of the form:

* was a given obligation enabled at time `n`?
* was it the obligation actually chosen at time `n`?
* if it stays enabled, must it eventually fire?
* if it is enabled infinitely often, must it fire infinitely often?

This makes the fairness layer frontend-independent while still concrete enough
for later liveness theorems.
-/

universe u v w

namespace Interaction
namespace Concurrent

namespace Process
namespace Run

/--
`Always P` means that the temporal property `P` holds at every time index.
-/
def Always (P : Nat → Prop) : Prop := ∀ n, P n

/--
`Eventually P` means that `P` holds at some time index.
-/
def Eventually (P : Nat → Prop) : Prop := ∃ n, P n

/--
`EventuallyAlways P` means that from some time onward, `P` keeps holding
forever.
-/
def EventuallyAlways (P : Nat → Prop) : Prop :=
  ∃ N, ∀ n, N ≤ n → P n

/--
`InfinitelyOften P` means that `P` holds at arbitrarily late time indices.
-/
def InfinitelyOften (P : Nat → Prop) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ P n

theorem always_mono {P Q : Nat → Prop}
    (himp : ∀ n, P n → Q n) :
    Always P → Always Q := by
  intro hP n
  exact himp n (hP n)

theorem eventually_mono {P Q : Nat → Prop}
    (himp : ∀ n, P n → Q n) :
    Eventually P → Eventually Q := by
  rintro ⟨n, hP⟩
  exact ⟨n, himp n hP⟩

theorem eventuallyAlways_mono {P Q : Nat → Prop}
    (himp : ∀ n, P n → Q n) :
    EventuallyAlways P → EventuallyAlways Q := by
  rintro ⟨N, hP⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact himp n (hP n hn)

theorem infinitelyOften_mono {P Q : Nat → Prop}
    (himp : ∀ n, P n → Q n) :
    InfinitelyOften P → InfinitelyOften Q := by
  intro hP N
  rcases hP N with ⟨n, hn, hPn⟩
  exact ⟨n, hn, himp n hPn⟩

end Run

namespace Ticketed

/--
`enabledAt ticketed run ticket n` means that at time `n`, there exists some
complete transcript of the current process step whose stable ticket is
`ticket`.

This is the semantic notion of "the scheduler could choose obligation
`ticket` now".
-/
def enabledAt {Party : Type u} (ticketed : Process.Ticketed Party)
    (run : Process.Run ticketed.toProcess)
    (ticket : ticketed.Ticket) (n : Nat) : Prop :=
  ∃ tr : (ticketed.toProcess.step (run.state n)).spec.Transcript,
    ticketed.ticket (run.state n) tr = ticket

/--
`firedAt ticketed run ticket n` means that the actual transcript chosen by the
run at time `n` has stable ticket `ticket`.

This is the semantic notion of "obligation `ticket` was the one actually
served at time `n`".
-/
def firedAt {Party : Type u} (ticketed : Process.Ticketed Party)
    (run : Process.Run ticketed.toProcess)
    (ticket : ticketed.Ticket) (n : Nat) : Prop :=
  ticketed.ticket (run.state n) (run.transcript n) = ticket

/--
Weak fairness for one ticket:
if the ticket is continuously enabled from some point onward, then it is
eventually fired.

This is the standard justice-style condition for one stable scheduling
obligation.
-/
def WeakFairOn {Party : Type u} (ticketed : Process.Ticketed Party)
    (run : Process.Run ticketed.toProcess)
    (ticket : ticketed.Ticket) : Prop :=
  Process.Run.EventuallyAlways (enabledAt ticketed run ticket) →
    Process.Run.Eventually (firedAt ticketed run ticket)

/--
Strong fairness for one ticket:
if the ticket is enabled infinitely often, then it is fired infinitely often.

This is the standard compassion-style condition for one stable scheduling
obligation.
-/
def StrongFairOn {Party : Type u} (ticketed : Process.Ticketed Party)
    (run : Process.Run ticketed.toProcess)
    (ticket : ticketed.Ticket) : Prop :=
  Process.Run.InfinitelyOften (enabledAt ticketed run ticket) →
    Process.Run.InfinitelyOften (firedAt ticketed run ticket)

/--
A run is weakly fair when every ticket is weakly fair.
-/
def WeakFair {Party : Type u} (ticketed : Process.Ticketed Party)
    (run : Process.Run ticketed.toProcess) : Prop :=
  ∀ ticket, WeakFairOn ticketed run ticket

/--
A run is strongly fair when every ticket is strongly fair.
-/
def StrongFair {Party : Type u} (ticketed : Process.Ticketed Party)
    (run : Process.Run ticketed.toProcess) : Prop :=
  ∀ ticket, StrongFairOn ticketed run ticket

/--
The actually fired ticket at time `n` is always enabled at time `n`.

This is the sanity lemma connecting the two basic predicates.
-/
theorem fired_implies_enabled {Party : Type u} (ticketed : Process.Ticketed Party)
    (run : Process.Run ticketed.toProcess)
    (ticket : ticketed.Ticket) (n : Nat) :
    firedAt ticketed run ticket n → enabledAt ticketed run ticket n := by
  intro hfired
  exact ⟨run.transcript n, hfired⟩

end Ticketed

end Process
end Concurrent
end Interaction
