/- 
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Concurrent.Execution
import ArkLib.Interaction.Concurrent.Interleaving
import ArkLib.Interaction.Concurrent.Independence
import ArkLib.Interaction.Concurrent.Policy

/-!
# Concurrent interaction examples

This file gives small definitional examples for the current concurrent layer.

The examples are intentionally focused on:

* binary structural parallelism;
* frontier events and residuals;
* per-party observation profiles over concurrently live components.
* scheduler ownership versus atomic payload ownership;
* the combined current local view of the next frontier event.
* execution traces, controller paths, and observed local traces.
* interleaving equivalence under commuting independent steps.
* executable scheduler and controller policies over finite traces.

They are meant to exercise the current expressivity surface before later layers
such as fairness or richer execution semantics are added.
-/

universe u

namespace Interaction
namespace Concurrent
namespace Examples

/-- Three parties for the toy concurrent examples: two honest parties and a
network adversary. -/
inductive Party where
  | alice
  | bob
  | adv

deriving instance DecidableEq for Party

/-- One atomic message-delivery step whose payload is a pair of a public header
and a private payload bit. -/
def delivery : Spec :=
  .node (Nat × Bool) (fun _ => .done)

/-- A profile where Alice originates the payload, Bob sees the whole message,
and the adversary sees only the public header. -/
def deliveryProfile : Profile Party delivery :=
  .node (fun
      | .alice => .active
      | .bob => .observe
      | .adv => .quotient Nat Prod.fst)
    (fun _ => .done)

example : Profile.ObsType Party.alice deliveryProfile = (Nat × Bool) := rfl

example : Profile.ObsType Party.bob deliveryProfile = (Nat × Bool) := rfl

example : Profile.ObsType Party.adv deliveryProfile = Nat := rfl

example :
    Profile.observe Party.adv deliveryProfile (.move (3, true)) = (3 : Nat) := rfl

/-- A second atomic node that only Bob fully observes, while the adversary
learns nothing. -/
def ack : Spec :=
  .node Bool (fun _ => .done)

/-- Local observations for the acknowledgement node. -/
def ackProfile : Profile Party ack :=
  .node (fun
      | .alice => .hidden
      | .bob => .observe
      | .adv => .hidden)
    (fun _ => .done)

/-- A concurrent system where delivery and acknowledgement are both live. -/
def inFlight : Spec :=
  .par delivery ack

/-- The corresponding concurrent observation profile. -/
def inFlightProfile : Profile Party inFlight :=
  .par deliveryProfile ackProfile

/-- Control ownership for the delivery step: Alice chooses the payload. -/
def deliveryControl : Control Party delivery :=
  .node .alice (fun _ => .done)

/-- Control ownership for the acknowledgement step: Bob chooses the bit. -/
def ackControl : Control Party ack :=
  .node .bob (fun _ => .done)

/-- The adversary controls scheduling between the two concurrently live
subsystems, while Alice and Bob still control their respective atomic nodes. -/
def inFlightControl : Control Party inFlight :=
  .par .adv deliveryControl ackControl

example :
    Profile.ObsType Party.adv inFlightProfile = Sum Nat PUnit := rfl

example :
    Profile.ObsType Party.bob inFlightProfile = Sum (Nat × Bool) Bool := rfl

example :
    Profile.observe Party.adv inFlightProfile (.left (.move (5, false))) =
      (Sum.inl (α := Nat) (β := PUnit) 5) := rfl

example :
    Profile.observe Party.adv inFlightProfile (.right (.move true)) = Sum.inr PUnit.unit := rfl

example :
    Profile.residual inFlightProfile (.left (.move (7, true))) = .par .done ackProfile := rfl

example :
    Profile.residual inFlightProfile (.right (.move false)) = .par deliveryProfile .done := rfl

example : Control.scheduler? inFlightControl = some .adv := rfl

example : Control.current? inFlightControl = some .adv := rfl

example :
    Control.controllers inFlightControl (.left (.move (5, false))) = [.adv, .alice] := rfl

example :
    Control.controllers inFlightControl (.right (.move true)) = [.adv, .bob] := rfl

def afterDelivery : Control Party (.par .done ack) :=
  Control.residual inFlightControl (.left (.move (7, true)))

example : Control.scheduler? afterDelivery = none := rfl

example : Control.current? afterDelivery = some .bob := rfl

example : Control.controllers afterDelivery (.right (.move false)) = [.bob] := rfl

example : Current.controller? inFlightControl = some .adv := rfl

example : Current.scheduler? inFlightControl = some .adv := rfl

example :
    Current.view Party.adv inFlightControl inFlightProfile = Multiparty.LocalView.active := by
  rfl

example :
    Current.observe Party.adv inFlightControl inFlightProfile
      (Front.left (.move (5, false))) =
      (Front.left (.move (5, false))) := rfl

example :
    Current.observe Party.alice inFlightControl inFlightProfile (.left (.move (5, false))) =
      (show PLift (Sum (Nat × Bool) PUnit) from ⟨Sum.inl (5, false)⟩) := rfl

example :
    Current.observe Party.bob inFlightControl inFlightProfile (.right (.move true)) =
      (show PLift (Sum (Nat × Bool) Bool) from ⟨Sum.inr true⟩) := rfl

def afterDeliveryProfile : Profile Party (.par .done ack) :=
  Profile.residual inFlightProfile (.left (.move (7, true)))

example : Current.controller? afterDelivery = some .bob := rfl

example : Current.scheduler? afterDelivery = none := rfl

example :
    Current.view Party.bob afterDelivery afterDeliveryProfile = Multiparty.LocalView.active := by
  rfl

example :
    Current.view Party.adv afterDelivery afterDeliveryProfile = Multiparty.LocalView.hidden := by
  rfl

example :
    Current.observe Party.adv afterDelivery afterDeliveryProfile (.right (.move false)) =
      PUnit.unit := rfl

/-- A concrete trace where the adversary schedules delivery first and the
remaining acknowledgement second. -/
def deliveryThenAck : Trace inFlight :=
  .step (.left (.move (7, true)))
    (.step (.right (.move false)) (Trace.doneOfNotLive rfl))

example :
    Trace.currentControllers inFlightControl deliveryThenAck = [some .adv, some .bob] := rfl

example :
    Trace.schedulers inFlightControl deliveryThenAck = [some .adv, none] := rfl

example :
    Trace.controllerPaths inFlightControl deliveryThenAck = [[.adv, .alice], [.bob]] := rfl

example :
    ObservedTrace.ofTrace Party.adv inFlightControl inFlightProfile deliveryThenAck =
      .step (Front.left (.move (7, true)))
        (.step (show Current.ObsType Party.adv afterDelivery afterDeliveryProfile from PUnit.unit)
          .done) := rfl

example :
    ObservedTrace.ofTrace Party.alice inFlightControl inFlightProfile deliveryThenAck =
      .step (show PLift (Sum (Nat × Bool) PUnit) from ⟨Sum.inl (7, true)⟩)
        (.step (show Current.ObsType Party.alice afterDelivery afterDeliveryProfile from PUnit.unit)
          .done) := rfl

example :
    ObservedTrace.ofTrace Party.bob inFlightControl inFlightProfile deliveryThenAck =
      .step (show PLift (Sum (Nat × Bool) Bool) from ⟨Sum.inl (7, true)⟩)
        (.step (Front.right (.move false)) .done) := rfl

example :
    (ObservedTrace.ofTrace Party.bob inFlightControl inFlightProfile deliveryThenAck).length =
      2 := rfl

/-- A concrete trace where the adversary schedules the acknowledgement before
the delivery event. -/
def ackThenDelivery : Trace inFlight :=
  .step (.right (.move true))
    (.step (.left (.move (9, false))) (Trace.doneOfNotLive rfl))

def afterAck : Control Party (.par delivery .done) :=
  Control.residual inFlightControl (.right (.move true))

def afterAckProfile : Profile Party (.par delivery .done) :=
  Profile.residual inFlightProfile (.right (.move true))

example :
    Trace.currentControllers inFlightControl ackThenDelivery = [some .adv, some .alice] := rfl

example :
    Trace.schedulers inFlightControl ackThenDelivery = [some .adv, none] := rfl

example :
    Trace.controllerPaths inFlightControl ackThenDelivery = [[.adv, .bob], [.alice]] := rfl

example :
    ObservedTrace.ofTrace Party.adv inFlightControl inFlightProfile ackThenDelivery =
      .step (Front.right (.move true))
        (.step (show Current.ObsType Party.adv afterAck afterAckProfile from ⟨(9 : Nat)⟩)
          .done) := rfl

def deliveryEvent : Front inFlight :=
  .left (.move (4, true))

def ackEvent : Front inFlight :=
  .right (.move false)

def leftThenRight : Trace inFlight :=
  .step deliveryEvent
    (.step (Independent.afterLeft (Independent.left_right (.move (4, true)) (.move false)))
      (Trace.doneOfNotLive rfl))

def rightThenLeft : Trace inFlight :=
  .step ackEvent
    (.step (Independent.afterRight (Independent.left_right (.move (4, true)) (.move false)))
      (Trace.doneOfNotLive rfl))

example : Trace.Equiv leftThenRight rightThenLeft :=
  .swap (Independent.left_right (.move (4, true)) (.move false)) (Trace.doneOfNotLive rfl)

example :
    Trace.Equiv.length_eq
      (.swap (Independent.left_right (.move (4, true)) (.move false)) (Trace.doneOfNotLive rfl) :
        Trace.Equiv leftThenRight rightThenLeft) = rfl := rfl

/-- When both sides of a live `par` are available, prefer the left branch. -/
def preferLeft : StepPolicy Party
  | .par _ _, .par _ leftControl rightControl, event =>
      match leftControl.isLive, rightControl.isLive, event with
      | true, true, .left _ => true
      | true, true, .right _ => false
      | _, _, _ => true
  | _, _, _ => true

/-- When both sides of a live `par` are available, prefer the right branch. -/
def preferRight : StepPolicy Party
  | .par _ _, .par _ leftControl rightControl, event =>
      match leftControl.isLive, rightControl.isLive, event with
      | true, true, .left _ => false
      | true, true, .right _ => true
      | _, _, _ => true
  | _, _, _ => true

example : Trace.respects preferLeft inFlightControl deliveryThenAck = true := rfl

example : Trace.respects preferLeft inFlightControl ackThenDelivery = false := rfl

example : Trace.respects preferRight inFlightControl ackThenDelivery = true := rfl

example : Trace.respects preferRight inFlightControl deliveryThenAck = false := rfl

example :
    Trace.respects (StepPolicy.byScheduler (fun | .adv => true | _ => false))
      inFlightControl deliveryThenAck = true := rfl

example :
    Trace.respects (StepPolicy.byController (fun | .bob => false | _ => true))
      inFlightControl deliveryThenAck = false := rfl

example :
    Trace.respects (StepPolicy.byController (fun | .bob => false | _ => true))
      inFlightControl ackThenDelivery = true := rfl

/-- A three-way concurrent system used to illustrate recursive independence
inside one branch of a larger parallel spec. -/
def threeWay : Spec :=
  .par delivery (.par ack ack)

example :
    Independent
      (Front.left (right := ack) (.move (4, true)) : Front inFlight)
      (Front.right (left := delivery) (.move false)) :=
  .left_right (.move (4, true)) (.move false)

example :
    Independent.afterLeft
      (Independent.left_right
        (left := delivery) (right := ack) (.move (4, true)) (.move false)) =
      Front.right (.move false) := rfl

example :
    Independent.afterRight
      (Independent.left_right
        (left := delivery) (right := ack) (.move (4, true)) (.move false)) =
      Front.left (.move (4, true)) := rfl

example :
    Independent.diamond
      (Independent.left_right
        (left := delivery) (right := ack) (.move (4, true)) (.move false)) = rfl := rfl

example :
    Independent
      (Front.right (left := delivery) (Front.left (.move true)) : Front threeWay)
      (Front.right (left := delivery) (Front.right (.move false))) :=
  .right (.left_right (.move true) (.move false))

example :
    Independent.diamond
      (.right
        (Independent.left_right
          (left := ack) (right := ack) (.move true) (.move false)) :
        Independent
          (Front.right (left := delivery) (Front.left (.move true)) : Front threeWay)
          (Front.right (left := delivery) (Front.right (.move false)))) = rfl := rfl

end Examples
end Concurrent
end Interaction
