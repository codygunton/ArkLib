/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Reduction
import ArkLib.OracleReduction.OracleInterface

/-!
# Hybrid Protocol Specification and Partial BCS Transform

A `HybridSpec` separates branching nodes (whose message value determines the
continuation) from pass-through nodes (whose continuation is structurally
constant). This captures the distinction between:

- **Plain senders and receivers** (`branch`): the protocol tree may depend on
  the message, because it is publicly visible.
- **Oracle senders** (`pass`): the protocol tree does not depend on the message,
  because it is hidden behind a commitment in BCS.

The key structural property: at `pass` nodes, the continuation `rest : HybridSpec`
does not depend on the message type `X`. This makes `Spec.Transcript rest.toSpec`
*definitionally* independent of the message value, eliminating the need for
`Classical.arbitrary`, propositional casts, or `restoreTranscript`.

## Partial BCS

The BCS transform is *selective*: at each `pass` node, a `CommitDeco` chooses
whether to commit (`some nc`) or leave the oracle message in the clear (`none`).
The full BCS is the special case where every `pass` node is `some`.

The **shared transcript** (`SharedTranscript`) depends on this selection:
committed oracle messages are dropped, non-committed ones are retained.
Output types must factor through `SharedTranscript`, ensuring compatibility
between the original and BCS-transformed protocols.

## Main definitions

### Core types
- `HybridSpec` — protocol spec with `done`, `branch`, and `pass` nodes.
- `HybridSpec.toSpec` — forgetful map to `Spec`.
- `HybridSpec.RoleDeco` — role assignment (branch nodes only; pass = sender).
- `HybridSpec.OracleDeco` — oracle interface assignment (pass nodes only).
- `HybridSpec.InvariantTranscript` — transcript dropping all oracle messages.

### BCS transform
- `NodeCommitment` — commitment configuration for a single message type.
- `HybridSpec.CommitDeco` — per-node commitment selection (`Option`).
- `HybridSpec.SharedTranscript` — transcript shared between original and BCS.
- `HybridSpec.bcsSpec` — BCS-transformed protocol spec.
- `HybridSpec.wrapWithCommitments` — transform prover strategy (no `sorry`).
- `HybridSpec.wrapWithCommitmentsExt` — extended version with oracle witness.
-/

universe u

open Interaction OracleComp OracleSpec

namespace Interaction

/-- A hybrid protocol specification with two kinds of nodes:
- `branch X rest`: the continuation depends on the message `x : X`.
  Used for plain senders (metadata) and receivers (challenges).
- `pass X rest`: the continuation is structurally constant.
  Used for oracle senders (committed messages).
- `done`: end of protocol. -/
inductive HybridSpec : Type 1 where
  | done : HybridSpec
  | branch (X : Type) (rest : X → HybridSpec) : HybridSpec
  | pass (X : Type) (rest : HybridSpec) : HybridSpec

/-- Configuration for committing to a single oracle message of type `X`.
The `commit` function produces both a commitment and a witness inside the
monad `m` (typically `OracleComp oSpec`). The `WitnessType` captures whatever
private state the prover retains for the opening phase (randomness, Merkle
paths, evaluation proofs, etc.). -/
structure NodeCommitment (m : Type → Type) (X : Type) where
  CommType : Type
  WitnessType : Type
  commit : X → m (CommType × WitnessType)

namespace HybridSpec

/-! ## Role and oracle decorations -/

/-- Role assignment for a `HybridSpec`. Only `branch` nodes carry a role
(`sender` or `receiver`). `pass` nodes are always sender (oracle sender),
so no annotation is stored. -/
def RoleDeco : HybridSpec → Type
  | .done => PUnit
  | .branch _ rest => Role × ((x : _) → RoleDeco (rest x))
  | .pass _ rest => RoleDeco rest

/-- Oracle interface assignment. `pass` nodes carry an `OracleInterface`
(defining the query-response structure). `branch` nodes just recurse. -/
def OracleDeco : HybridSpec → Type 1
  | .done => PUnit
  | .branch _ rest => (x : _) → OracleDeco (rest x)
  | .pass X rest => OracleInterface X × OracleDeco rest

/-! ## Forgetful map to Spec -/

/-- Convert a `HybridSpec` to a plain `Spec`. `pass` nodes become nodes
with *definitionally constant* continuation `fun _ => rest.toSpec`. -/
def toSpec : HybridSpec → Spec
  | .done => .done
  | .branch X rest => .node X (fun x => (rest x).toSpec)
  | .pass X rest => .node X (fun _ => rest.toSpec)

/-- Lift role decoration to `RoleDecoration` on `toSpec`. `pass` nodes
are always `.sender`. -/
def toSpecRoles : (hs : HybridSpec) → RoleDeco hs → RoleDecoration hs.toSpec
  | .done, _ => ⟨⟩
  | .branch _ rest, ⟨role, rRest⟩ => ⟨role, fun x => toSpecRoles (rest x) (rRest x)⟩
  | .pass _ rest, roles => ⟨.sender, fun _ => toSpecRoles rest roles⟩

/-! ## Invariant transcript -/

/-- The *invariant transcript* drops ALL oracle sender messages. This is
the minimal shared data between the original protocol and any BCS
variant (full or partial). -/
def InvariantTranscript : HybridSpec → Type
  | .done => PUnit
  | .branch X rest => (x : X) × InvariantTranscript (rest x)
  | .pass _ rest => InvariantTranscript rest

/-- Project a full transcript to the invariant transcript. -/
def projectInvariant :
    (hs : HybridSpec) → Spec.Transcript hs.toSpec → InvariantTranscript hs
  | .done, _ => ⟨⟩
  | .branch _ rest, ⟨x, tr⟩ => ⟨x, projectInvariant (rest x) tr⟩
  | .pass _ rest, ⟨_, tr⟩ => projectInvariant rest tr

/-! ## Partial BCS Transform -/

/-- Commitment selection: at each `pass` node, either `some nc` (commit
the oracle message using `nc`) or `none` (leave it in the clear).
At `branch` nodes, the selection is indexed by the message value
(since the subtree depends on it). -/
def CommitDeco (m : Type → Type) : HybridSpec → Type 1
  | .done => PUnit
  | .branch _ rest => (x : _) → CommitDeco m (rest x)
  | .pass X rest => Option (NodeCommitment m X) × CommitDeco m rest

/-- Shared transcript relative to a commitment selection. Committed oracle
messages are dropped; non-committed oracle messages are retained.

When all `pass` nodes are `some`, this reduces to `InvariantTranscript`.
When all are `none`, this is isomorphic to `Spec.Transcript hs.toSpec`. -/
def SharedTranscript {m : Type → Type} :
    (hs : HybridSpec) → CommitDeco m hs → Type
  | .done, _ => PUnit
  | .branch X rest, cdRest => (x : X) × SharedTranscript (rest x) (cdRest x)
  | .pass _ rest, ⟨some _, cdRest⟩ => SharedTranscript rest cdRest
  | .pass X rest, ⟨none, cdRest⟩ => X × SharedTranscript rest cdRest

/-- Project an original transcript to the shared transcript. -/
def projectShared {m : Type → Type} :
    (hs : HybridSpec) → (cd : CommitDeco m hs) →
    Spec.Transcript hs.toSpec → SharedTranscript hs cd
  | .done, _, _ => ⟨⟩
  | .branch _ rest, cdRest, ⟨x, tr⟩ =>
      ⟨x, projectShared (rest x) (cdRest x) tr⟩
  | .pass _ rest, ⟨some _, cdRest⟩, ⟨_, tr⟩ =>
      projectShared rest cdRest tr
  | .pass _ rest, ⟨none, cdRest⟩, ⟨x, tr⟩ =>
      ⟨x, projectShared rest cdRest tr⟩

section BCS
variable {m : Type → Type}

/-- BCS-transformed protocol spec. At committed `pass` nodes, the message
type is replaced by the commitment type. At non-committed `pass` nodes,
the original message type is preserved. -/
def bcsSpec :
    (hs : HybridSpec) → CommitDeco m hs → Spec.{0}
  | .done, _ => .done
  | .branch X rest, cdRest => .node X (fun x => bcsSpec (rest x) (cdRest x))
  | .pass _ rest, ⟨some nc, cdRest⟩ => .node nc.CommType (fun _ => bcsSpec rest cdRest)
  | .pass X rest, ⟨none, cdRest⟩ => .node X (fun _ => bcsSpec rest cdRest)

/-- BCS-transformed role decoration. All `pass` nodes remain sender. -/
def bcsRoles :
    (hs : HybridSpec) → RoleDeco hs → (cd : CommitDeco m hs) →
    RoleDecoration (hs.bcsSpec cd)
  | .done, _, _ => ⟨⟩
  | .branch _ rest, ⟨role, rRest⟩, cdRest =>
      ⟨role, fun x => bcsRoles (rest x) (rRest x) (cdRest x)⟩
  | .pass _ rest, roles, ⟨some _, cdRest⟩ =>
      ⟨.sender, fun _ => bcsRoles rest roles cdRest⟩
  | .pass _ rest, roles, ⟨none, cdRest⟩ =>
      ⟨.sender, fun _ => bcsRoles rest roles cdRest⟩

/-- Project a BCS transcript to the shared transcript. -/
def bcsProjectShared :
    (hs : HybridSpec) → (cd : CommitDeco m hs) →
    Spec.Transcript (hs.bcsSpec cd) → SharedTranscript hs cd
  | .done, _, _ => ⟨⟩
  | .branch _ rest, cdRest, ⟨x, tr⟩ =>
      ⟨x, bcsProjectShared (rest x) (cdRest x) tr⟩
  | .pass _ rest, ⟨some _, cdRest⟩, ⟨_, tr⟩ =>
      bcsProjectShared rest cdRest tr
  | .pass _ rest, ⟨none, cdRest⟩, ⟨x, tr⟩ =>
      ⟨x, bcsProjectShared rest cdRest tr⟩

variable [Monad m]

/-- Partial BCS prover wrapping. At committed `pass` nodes, the oracle
message is replaced by a commitment. At non-committed `pass` nodes,
the message passes through unchanged (and the output type may depend on it).

The output type must factor through `SharedTranscript hs cd`, ensuring
type compatibility between original and BCS strategies. This function
is fully computable with no `sorry` or `Classical.arbitrary`. -/
def wrapWithCommitments :
    (hs : HybridSpec) → (roles : RoleDeco hs) → (cd : CommitDeco m hs) →
    (OutType : SharedTranscript hs cd → Type) →
    Spec.Strategy.withRoles m hs.toSpec (hs.toSpecRoles roles)
      (fun tr => OutType (hs.projectShared cd tr)) →
    Spec.Strategy.withRoles m (hs.bcsSpec cd) (hs.bcsRoles roles cd)
      (fun tr => OutType (hs.bcsProjectShared cd tr))
  | .done, _, _, _, strategy => strategy
  | .branch _ rest, ⟨.sender, rRest⟩, cdRest, OutType, strategy => do
      let ⟨x, restStrategy⟩ ← strategy
      return ⟨x, wrapWithCommitments (rest x) (rRest x) (cdRest x)
        (fun st => OutType ⟨x, st⟩) restStrategy⟩
  | .branch _ rest, ⟨.receiver, rRest⟩, cdRest, OutType, strategy =>
      fun x => do
        let restStrategy ← strategy x
        return (wrapWithCommitments (rest x) (rRest x) (cdRest x)
          (fun st => OutType ⟨x, st⟩) restStrategy)
  | .pass _ rest, roles, ⟨some nc, cdRest⟩, OutType, strategy => do
      let ⟨x, restStrategy⟩ ← strategy
      let ⟨cm, _⟩ ← nc.commit x
      return ⟨cm, wrapWithCommitments rest roles cdRest OutType restStrategy⟩
  | .pass _ rest, roles, ⟨none, cdRest⟩, OutType, strategy => do
      let ⟨x, restStrategy⟩ ← strategy
      return ⟨x, wrapWithCommitments rest roles cdRest
        (fun st => OutType ⟨x, st⟩) restStrategy⟩

/-! ## Oracle Witness -/

/-- Oracle messages and commitment witnesses retained at committed `pass` nodes.
At each committed node, stores both the original oracle message `X` and the
commitment witness `nc.WitnessType` (needed for the opening phase).
Non-committed oracle messages are already visible in `SharedTranscript`
and don't need witnessing. -/
def OracleWitness :
    (hs : HybridSpec) → (cd : CommitDeco m hs) → SharedTranscript hs cd → Type
  | .done, _, _ => PUnit
  | .branch _ rest, cdRest, ⟨x, st⟩ => OracleWitness (rest x) (cdRest x) st
  | .pass X rest, ⟨some nc, cdRest⟩, st =>
      X × nc.WitnessType × OracleWitness rest cdRest st
  | .pass _ rest, ⟨none, cdRest⟩, ⟨_, st⟩ => OracleWitness rest cdRest st

/-- Extended partial BCS prover wrapping that also extracts committed oracle
messages as witness for the opening phase.

At committed `pass` nodes, the oracle message `x` is extracted and paired
into the witness via `Strategy.mapOutputWithRoles`. At non-committed `pass`
nodes, the message passes through and no witness entry is added. -/
def wrapWithCommitmentsExt :
    (hs : HybridSpec) → (roles : RoleDeco hs) → (cd : CommitDeco m hs) →
    (OutType : SharedTranscript hs cd → Type) →
    Spec.Strategy.withRoles m hs.toSpec (hs.toSpecRoles roles)
      (fun tr => OutType (hs.projectShared cd tr)) →
    Spec.Strategy.withRoles m (hs.bcsSpec cd) (hs.bcsRoles roles cd)
      (fun tr => OutType (hs.bcsProjectShared cd tr) ×
                 OracleWitness hs cd (hs.bcsProjectShared cd tr))
  | .done, _, _, _, strategy => (strategy, ⟨⟩)
  | .branch _ rest, ⟨.sender, rRest⟩, cdRest, OutType, strategy => do
      let ⟨x, restStrategy⟩ ← strategy
      return ⟨x, wrapWithCommitmentsExt (rest x) (rRest x) (cdRest x)
        (fun st => OutType ⟨x, st⟩) restStrategy⟩
  | .branch _ rest, ⟨.receiver, rRest⟩, cdRest, OutType, strategy =>
      fun x => do
        let restStrategy ← strategy x
        return (wrapWithCommitmentsExt (rest x) (rRest x) (cdRest x)
          (fun st => OutType ⟨x, st⟩) restStrategy)
  | .pass _ rest, roles, ⟨some nc, cdRest⟩, OutType, strategy => do
      let ⟨x, restStrategy⟩ ← strategy
      let ⟨cm, cwit⟩ ← nc.commit x
      let bcsRest := wrapWithCommitmentsExt rest roles cdRest OutType restStrategy
      return ⟨cm, Spec.Strategy.mapOutputWithRoles
        (fun _ ⟨out, owit⟩ => (out, x, cwit, owit)) bcsRest⟩
  | .pass _ rest, roles, ⟨none, cdRest⟩, OutType, strategy => do
      let ⟨x, restStrategy⟩ ← strategy
      return ⟨x, wrapWithCommitmentsExt rest roles cdRest
        (fun st => OutType ⟨x, st⟩) restStrategy⟩

end BCS

end HybridSpec

end Interaction
