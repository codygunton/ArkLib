/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Core

/-!
# Hybrid Decoration and Query Handles

A `HybridDecoration` assigns an *optional* `OracleInterface` at each sender
node. Plain senders (`none`) pass through unchanged in BCS. Oracle senders
(`some oi`) carry queryable oracle messages.

## Main definitions

- `HybridDecoration` — `Role.Refine (fun X => Option (OracleInterface X))`.
- `HybridDecoration.QueryHandle` — index type for oracle queries along a
  transcript path. Only `some oi` sender nodes contribute query indices.
- `HybridDecoration.toOracleSpec` — the `OracleSpec` for querying oracle-sender
  messages along a given transcript path.
- `HybridDecoration.answerQuery` — answer oracle queries using transcript values.
- `HybridDecoration.ofOracleDecoration` — embed full `OracleDecoration`.
- `HybridDecoration.plain` — trivial decoration with no oracle senders.

## See also

- `Oracle/Core.lean` — the full `OracleDecoration` and its infrastructure
- `BCS/HybridSpec.lean` — the `HybridSpec` type and partial BCS transform
-/

universe u v

open OracleComp OracleSpec

namespace Interaction

/-- A hybrid decoration assigns an *optional* `OracleInterface` at each sender
node. `none` means plain metadata (sent in the clear, may shape the tree).
`some oi` means oracle message (queryable, will be committed by BCS).

Defined as `Role.Refine (fun X => Option (OracleInterface X))`. -/
abbrev HybridDecoration (spec : Spec) (roles : RoleDecoration spec) :=
  Interaction.Role.Refine (fun X => Option (OracleInterface X)) spec roles

namespace HybridDecoration

/-! ## Query handles and oracle spec -/

/-- Index type for oracle queries given a transcript path through a hybrid
decoration. Only oracle sender nodes contribute query indices (via `.inl`);
plain sender nodes are skipped, and the query handle recurses into the
subtree determined by the transcript. Receiver nodes recurse immediately. -/
def QueryHandle :
    (spec : Spec) → (roles : RoleDecoration spec) →
    HybridDecoration spec roles → Spec.Transcript spec → Type
  | .done, _, _, _ => Empty
  | .node _ rest, ⟨.sender, rRest⟩, ⟨none, hdRest⟩, ⟨x, trRest⟩ =>
      QueryHandle (rest x) (rRest x) (hdRest x) trRest
  | .node _ rest, ⟨.sender, rRest⟩, ⟨some oi, hdRest⟩, ⟨x, trRest⟩ =>
      oi.Query ⊕ QueryHandle (rest x) (rRest x) (hdRest x) trRest
  | .node _ rest, ⟨.receiver, rRest⟩, hdFn, ⟨x, trRest⟩ =>
      QueryHandle (rest x) (rRest x) (hdFn x) trRest

/-- The oracle specification for querying oracle-sender messages along a given
transcript path. Maps each `QueryHandle` to its response type. Plain sender
nodes do not contribute any queries. -/
def toOracleSpec :
    (spec : Spec) → (roles : RoleDecoration spec) →
    (hd : HybridDecoration spec roles) →
    (tr : Spec.Transcript spec) → OracleSpec (QueryHandle spec roles hd tr)
  | .done, _, _, _ => Empty.elim
  | .node _ rest, ⟨.sender, rRest⟩, ⟨none, hdRest⟩, ⟨x, trRest⟩ =>
      toOracleSpec (rest x) (rRest x) (hdRest x) trRest
  | .node _ rest, ⟨.sender, rRest⟩, ⟨some oi, hdRest⟩, ⟨x, trRest⟩ =>
    fun
    | .inl q => oi.toOC.spec q
    | .inr handle => toOracleSpec (rest x) (rRest x) (hdRest x) trRest handle
  | .node _ rest, ⟨.receiver, rRest⟩, hdFn, ⟨x, trRest⟩ =>
      toOracleSpec (rest x) (rRest x) (hdFn x) trRest

/-- Answer oracle queries using the message values from a transcript. At each
oracle sender node, the transcript provides the actual move `x : X`, which is
used as the message argument to `OracleInterface`'s implementation. Plain
sender nodes are skipped. -/
def answerQuery :
    (spec : Spec) → (roles : RoleDecoration spec) →
    (hd : HybridDecoration spec roles) →
    (tr : Spec.Transcript spec) →
    QueryImpl (toOracleSpec spec roles hd tr) Id
  | .done, _, _, _ => fun q => q.elim
  | .node _ rest, ⟨.sender, rRest⟩, ⟨none, hdRest⟩, ⟨x, trRest⟩ =>
      answerQuery (rest x) (rRest x) (hdRest x) trRest
  | .node _ rest, ⟨.sender, rRest⟩, ⟨some oi, hdRest⟩, ⟨x, trRest⟩ =>
    fun
    | .inl q => (oi.toOC.impl q).run x
    | .inr handle => answerQuery (rest x) (rRest x) (hdRest x) trRest handle
  | .node _ rest, ⟨.receiver, rRest⟩, hdFn, ⟨x, trRest⟩ =>
      answerQuery (rest x) (rRest x) (hdFn x) trRest

/-! ## Conversion from OracleDecoration -/

/-- Every `OracleDecoration` can be viewed as a `HybridDecoration` where all
sender nodes carry `some oi`. -/
def ofOracleDecoration :
    (spec : Spec) → (roles : RoleDecoration spec) →
    OracleDecoration spec roles → HybridDecoration spec roles
  | .done, _, _ => ⟨⟩
  | .node _ rest, ⟨.sender, rRest⟩, ⟨oi, odRest⟩ =>
      ⟨some oi, fun x => ofOracleDecoration (rest x) (rRest x) (odRest x)⟩
  | .node _ rest, ⟨.receiver, rRest⟩, odFn =>
      fun x => ofOracleDecoration (rest x) (rRest x) (odFn x)

/-- A trivial hybrid decoration where no sender carries an oracle interface. -/
def plain :
    (spec : Spec) → (roles : RoleDecoration spec) →
    HybridDecoration spec roles
  | .done, _ => ⟨⟩
  | .node _ rest, ⟨.sender, rRest⟩ =>
      ⟨none, fun x => plain (rest x) (rRest x)⟩
  | .node _ rest, ⟨.receiver, rRest⟩ =>
      fun x => plain (rest x) (rRest x)

end HybridDecoration

end Interaction
