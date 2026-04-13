/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.BCS.HybridSpec
import ArkLib.Interaction.BCS.HybridReduction
import ArkLib.CommitmentScheme.Basic

/-!
# BCS Verifier Decomposition and Public-Query Infrastructure

The BCS verifier is decomposed into three components:

1. **Challenger** (Phase 1): a `Counterpart.withMonads` on `bcsSpec` with
   restricted oracle access. Can query non-committed oracles but NOT committed
   ones. The restriction is enforced by `bcsHybridDeco`, which strips oracle
   interfaces from committed pass nodes.

2. **Query function** (Phase 2a): a deterministic function
   `SharedTranscript → OracleQueryDeco` producing queries to committed oracles.
   The "public query" property is encoded in the type: queries depend only on
   publicly visible data.

3. **Decision function** (Phase 2b): given the shared transcript and query
   responses, produces the verifier's output. Runs inside `OracleComp` with
   access to external oracles and non-committed oracle messages.

## Main definitions

### Bridge to HybridDecoration
- `HybridSpec.bcsHybridDeco` — converts `OracleDeco` on `HybridSpec` into a
  `HybridDecoration` on `bcsSpec`. Committed pass nodes get `none` (no oracle
  interface); non-committed pass nodes retain `some oi`.

### Query and response types
- `QueryBundle` — a finite collection of queries to a single oracle interface.
- `HybridSpec.OracleQueryDeco` — one `QueryBundle` per committed pass node.
- `HybridSpec.OracleResponseDeco` — matching responses for each query bundle.

### Opening infrastructure
- `HybridSpec.OpeningDeco` — per-committed-node opening protocol data, pairing
  each committed `NodeCommitment` with a `Commitment.Interaction.Opening`.

### Verifier decomposition
- `HybridSpec.PublicQueryVerifier` — the three-component decomposed verifier.

## See also

- `HybridSpec.lean` — the `HybridSpec` type, partial BCS prover transforms
- `HybridDecoration.lean` — `HybridDecoration`, `QueryHandle`, `toOracleSpec`
- `HybridReduction.lean` — `toMonadDecoration` for hybrid oracle access
-/

universe u

open Interaction OracleComp OracleSpec

namespace Interaction

/-! ## Query bundle -/

/-- A finite collection of queries to a single oracle interface. Bundles the
number of queries with a query-selection function. -/
structure QueryBundle {X : Type} (oi : OracleInterface X) where
  numQueries : ℕ
  queries : Fin numQueries → oi.Query

namespace HybridSpec

/-! ## Bridge: OracleDeco → HybridDecoration on bcsSpec -/

section BCSBridge
variable {m : Type → Type}

/-- Convert `OracleDeco` on a `HybridSpec` into a `HybridDecoration` on
`bcsSpec cd`. This is the bridge that enforces the public-query restriction
at the type level:
- Committed pass nodes → `none` (commitment type has no oracle interface)
- Non-committed pass nodes → `some oi` (retain oracle interface)
- Branch sender nodes → `none` (plain messages, no oracle interface)
- Branch receiver nodes → recurse -/
def bcsHybridDeco :
    (hs : HybridSpec) → (roles : RoleDeco hs) → (od : OracleDeco hs) →
    (cd : CommitDeco m hs) →
    HybridDecoration (hs.bcsSpec cd) (hs.bcsRoles roles cd)
  | .done, _, _, _ => ⟨⟩
  | .branch _ rest, ⟨.sender, rRest⟩, odRest, cdRest =>
      ⟨none, fun x => bcsHybridDeco (rest x) (rRest x) (odRest x) (cdRest x)⟩
  | .branch _ rest, ⟨.receiver, rRest⟩, odRest, cdRest =>
      fun x => bcsHybridDeco (rest x) (rRest x) (odRest x) (cdRest x)
  | .pass _ rest, roles, ⟨_oi, odRest⟩, ⟨some _nc, cdRest⟩ =>
      ⟨none, fun _ => bcsHybridDeco rest roles odRest cdRest⟩
  | .pass _ rest, roles, ⟨oi, odRest⟩, ⟨none, cdRest⟩ =>
      ⟨some oi, fun _ => bcsHybridDeco rest roles odRest cdRest⟩

end BCSBridge

/-! ## Oracle query and response decorations -/

section QueryResponse
variable {m : Type → Type}

/-- Oracle query decoration: one `QueryBundle` per committed pass node along
a `SharedTranscript`. At branch nodes, recurse into the subtree determined
by the message. At non-committed pass nodes, skip (the oracle is still in
the clear). -/
def OracleQueryDeco :
    (hs : HybridSpec) → (od : OracleDeco hs) → (cd : CommitDeco m hs) →
    SharedTranscript hs cd → Type
  | .done, _, _, _ => PUnit
  | .branch _ rest, odRest, cdRest, ⟨x, st⟩ =>
      OracleQueryDeco (rest x) (odRest x) (cdRest x) st
  | .pass _X rest, ⟨oi, odRest⟩, ⟨some _, cdRest⟩, st =>
      QueryBundle oi × OracleQueryDeco rest odRest cdRest st
  | .pass _ rest, ⟨_, odRest⟩, ⟨none, cdRest⟩, ⟨_, st⟩ =>
      OracleQueryDeco rest odRest cdRest st

/-- Oracle response decoration: for each committed pass node, a function
mapping each query in the `QueryBundle` to its response type. Mirrors
`OracleQueryDeco` structurally. -/
def OracleResponseDeco :
    (hs : HybridSpec) → (od : OracleDeco hs) → (cd : CommitDeco m hs) →
    (st : SharedTranscript hs cd) → OracleQueryDeco hs od cd st → Type
  | .done, _, _, _, _ => PUnit
  | .branch _ rest, odRest, cdRest, ⟨x, st⟩, qd =>
      OracleResponseDeco (rest x) (odRest x) (cdRest x) st qd
  | .pass _X rest, ⟨oi, odRest⟩, ⟨some _, cdRest⟩, st, ⟨qb, qdRest⟩ =>
      ((i : Fin qb.numQueries) → oi.Response (qb.queries i)) ×
      OracleResponseDeco rest odRest cdRest st qdRest
  | .pass _ rest, ⟨_, odRest⟩, ⟨none, cdRest⟩, ⟨_, st⟩, qd =>
      OracleResponseDeco rest odRest cdRest st qd

end QueryResponse

/-! ## Opening decoration -/

/-- Opening protocol data for each committed pass node. At committed nodes,
pairs the `NodeCommitment` with a `Commitment.Interaction.Opening` that
proves consistency of commitment openings. At non-committed pass nodes and
branch nodes, recurses structurally.

This decoration is the Phase 2 companion to `CommitDeco`. The prover-side
transforms (`wrapWithCommitments`, `wrapWithCommitmentsExt`) only need
`CommitDeco`; Phase 2 additionally requires `OpeningDeco`. -/
def OpeningDeco (m : Type → Type) :
    (hs : HybridSpec) → (od : OracleDeco hs) → CommitDeco m hs → Type 1
  | .done, _, _ => PUnit
  | .branch _ rest, odRest, cdRest =>
      (x : _) → OpeningDeco m (rest x) (odRest x) (cdRest x)
  | .pass X rest, ⟨oi, odRest⟩, ⟨some nc, cdRest⟩ =>
      @Commitment.Interaction.Opening m X nc.CommType nc.WitnessType oi ×
      OpeningDeco m rest odRest cdRest
  | .pass _ rest, ⟨_, odRest⟩, ⟨none, cdRest⟩ =>
      OpeningDeco m rest odRest cdRest

/-! ## Public-query verifier decomposition -/

/-- A BCS-compatible verifier decomposed into three components that together
express the "public query" property:

1. `challenger`: a `Counterpart.withMonads` on `bcsSpec` whose oracle access
   is restricted to non-committed oracles (via `bcsHybridDeco`). At receiver
   nodes, it can query external oracles (`oSpec`), input oracle statements
   (`[OStmtIn]ₒ`), and non-committed message oracles, but NOT committed ones.
   Public-coin verifiers are a special case where the challenger ignores all
   oracle access and samples challenges uniformly.

2. `queryFn`: a deterministic function producing queries to committed oracles
   from the `SharedTranscript`. The "public query" property is implicit in
   the type: queries can only depend on publicly visible data.

3. `decide`: given the shared transcript and query responses, produces the
   verifier's output. Runs inside `OracleComp` with full non-committed oracle
   access. This is the most general form. -/
structure PublicQueryVerifier {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [∀ i, OracleInterface.{0, 0} (OStmtIn i)]
    (hs : HybridSpec) (roles : RoleDeco hs)
    (od : OracleDeco hs) (cd : CommitDeco (OracleComp oSpec) hs)
    (StmtIn : Type) (StmtOut : SharedTranscript hs cd → Type) where
  challenger : StmtIn →
    Spec.Counterpart.withMonads (hs.bcsSpec cd) (hs.bcsRoles roles cd)
      (HybridDecoration.toMonadDecoration oSpec OStmtIn
        (hs.bcsSpec cd) (hs.bcsRoles roles cd) (hs.bcsHybridDeco roles od cd)
        (ιₐ := PEmpty) []ₒ)
      (fun _ => PUnit)
  queryFn : StmtIn → (st : SharedTranscript hs cd) →
    OracleQueryDeco hs od cd st
  decide : StmtIn → (bcsTr : Spec.Transcript (hs.bcsSpec cd)) →
    (qd : OracleQueryDeco hs od cd (hs.bcsProjectShared cd bcsTr)) →
    OracleResponseDeco hs od cd (hs.bcsProjectShared cd bcsTr) qd →
    OracleComp (oSpec + [OStmtIn]ₒ +
      HybridDecoration.toOracleSpec (hs.bcsSpec cd) (hs.bcsRoles roles cd)
        (hs.bcsHybridDeco roles od cd) bcsTr)
      (StmtOut (hs.bcsProjectShared cd bcsTr))

/-! ## Phase 1: BCS prover wrapping + challenger -/

section Phase1
variable {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
variable {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ i, OracleInterface.{0, 0} (OStmtIn i)]

/-- Phase 1 of BCS: the prover's strategy on `bcsSpec`, obtained from
`wrapWithCommitmentsExt`. Given an original prover strategy on `hs.toSpec`,
produces a strategy on `bcsSpec cd` whose output includes both the original
output and the `OracleWitness` (committed oracle messages + commitment
witnesses for Phase 2 openings).

This is a direct application of `wrapWithCommitmentsExt`. -/
def bcsPhase1Prover
    (hs : HybridSpec) (roles : RoleDeco hs) (cd : CommitDeco (OracleComp oSpec) hs)
    (OutType : SharedTranscript hs cd → Type) :
    Spec.Strategy.withRoles (OracleComp oSpec) hs.toSpec (hs.toSpecRoles roles)
      (fun tr => OutType (hs.projectShared cd tr)) →
    Spec.Strategy.withRoles (OracleComp oSpec) (hs.bcsSpec cd) (hs.bcsRoles roles cd)
      (fun tr => OutType (hs.bcsProjectShared cd tr) ×
                 OracleWitness hs cd (hs.bcsProjectShared cd tr)) :=
  hs.wrapWithCommitmentsExt roles cd OutType

/-- Phase 1 verifier: extract the `challenger` from a `PublicQueryVerifier`.
This is just projection, provided for symmetry with `bcsPhase1Prover`. -/
def bcsPhase1Verifier
    {hs : HybridSpec} {roles : RoleDeco hs} {od : OracleDeco hs}
    {cd : CommitDeco (OracleComp oSpec) hs}
    {StmtIn : Type} {StmtOut : SharedTranscript hs cd → Type}
    (pqv : PublicQueryVerifier oSpec OStmtIn hs roles od cd StmtIn StmtOut)
    (stmt : StmtIn) :=
  pqv.challenger stmt

end Phase1

/-! ## Phase 2: Opening protocol -/

section Phase2
variable {ι : Type} {oSpec : OracleSpec.{0, 0} ι}

/-- The opening protocol spec for Phase 2 of BCS. For each committed pass
node and each query in the `OracleQueryDeco`, composes the individual
opening `Interaction.Proof` specs from `OpeningDeco`.

The resulting spec is the interaction tree for all opening sub-protocols
chained together. -/
def openingSpec {m : Type → Type}
    (hs : HybridSpec) (od : OracleDeco hs) (cd : CommitDeco m hs)
    (_opDeco : OpeningDeco m hs od cd)
    (st : SharedTranscript hs cd) (qd : OracleQueryDeco hs od cd st) :
    Spec.{0} :=
  sorry

/-- Roles for the opening protocol spec. -/
def openingRoles {m : Type → Type}
    (hs : HybridSpec) (od : OracleDeco hs) (cd : CommitDeco m hs)
    (opDeco : OpeningDeco m hs od cd)
    (st : SharedTranscript hs cd) (qd : OracleQueryDeco hs od cd st) :
    RoleDecoration (openingSpec hs od cd opDeco st qd) :=
  sorry

/-- Phase 2 prover: uses the `OracleWitness` to answer verifier queries and
run opening protocols. For each committed oracle and each query, the prover
reveals the response and provides an opening proof via the `Opening.proof`
from `OpeningDeco`. -/
def bcsPhase2Prover
    (hs : HybridSpec) (od : OracleDeco hs) (cd : CommitDeco (OracleComp oSpec) hs)
    (opDeco : OpeningDeco (OracleComp oSpec) hs od cd)
    (st : SharedTranscript hs cd) (qd : OracleQueryDeco hs od cd st)
    (_wit : OracleWitness hs cd st) :
    OracleComp oSpec (Spec.Strategy.withRoles (OracleComp oSpec)
      (openingSpec hs od cd opDeco st qd) (openingRoles hs od cd opDeco st qd)
      (fun _ => OracleResponseDeco hs od cd st qd)) :=
  sorry

/-- Phase 2 verifier: checks the opening proofs. For each committed oracle
and each query, verifies that the prover's opening is consistent with the
commitment from Phase 1. -/
def bcsPhase2Verifier
    (hs : HybridSpec) (od : OracleDeco hs) (cd : CommitDeco (OracleComp oSpec) hs)
    (opDeco : OpeningDeco (OracleComp oSpec) hs od cd)
    (st : SharedTranscript hs cd) (qd : OracleQueryDeco hs od cd st) :
    Spec.Counterpart (OracleComp oSpec)
      (openingSpec hs od cd opDeco st qd) (openingRoles hs od cd opDeco st qd)
      (fun _ => OracleResponseDeco hs od cd st qd) :=
  sorry

end Phase2

end HybridSpec

end Interaction
