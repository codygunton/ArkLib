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

## Design resolution

The BCS verifier should not be represented as a single monolithic oracle
program over the original transcript. That representation is too permissive:
it can accidentally let hidden oracle-message values influence future protocol
shape or query selection.

Instead, the verifier surface is intentionally split. The phase-1 challenger
runs on `bcsSpec cd`, where committed oracle messages have already been
replaced by commitments and therefore have no oracle interface. The phase-2
query selector consumes only `SharedTranscript hs cd`, so every query to a
committed oracle is a public function of data visible in both the original and
BCS executions. The final decision receives only that shared transcript plus
the opened responses.

This makes the intended BCS side condition a type-level invariant: committed
oracle messages may affect opened responses and the final decision, but they do
not determine the interaction tree or the set of verifier queries.

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

/-- A BCS-compatible verifier decomposed into the three public-query phases.

This is the proposed representation for BCS-compatible oracle verifiers. The
split is deliberate:

1. `challenger`: a `Counterpart.withMonads` on `bcsSpec` whose oracle access
   is restricted to non-committed oracles (via `bcsHybridDeco`). At receiver
   nodes, it can query external oracles (`oSpec`), input oracle statements
   (`[OStmtIn]ₒ`), and non-committed message oracles, but NOT committed ones.
   Public-coin verifiers are a special case where the challenger ignores all
   oracle access and samples challenges uniformly.

2. `queryFn`: a deterministic function producing queries to committed oracles
   from the `SharedTranscript`. The "public query" property is implicit in
   the type: queries can only depend on data shared by the original and BCS
   executions.

3. `decide`: given the shared transcript and query responses, produces the
   verifier's output. Runs inside `OracleComp` with full non-committed oracle
   access.

In particular, there is no field that receives the original full transcript or
the hidden committed oracle messages. This prevents the two failure modes that
break BCS: branching on committed oracle values and choosing queries as a
function of committed oracle values. -/
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

/-! ### Commitment-opening bridge -/

/-- Statements for every commitment-opening subproof requested in Phase 2.

At a committed pass node, this records one statement for each query in the
`QueryBundle`: the commitment sent in the BCS transcript, the selected oracle
query, and the claimed response. This is the typed bridge from the BCS public
query layer to `Commitment.Interaction.Opening.proof`.

The compatibility Phase 2 scaffold below still sends the whole response
decoration as one message. The checked full Phase 2 surface later in this file
uses this decoration to run the corresponding opening verifier for every
requested query. -/
def OpeningStatementDeco {m : Type → Type} :
    (hs : HybridSpec) → (od : OracleDeco hs) → (cd : CommitDeco m hs) →
    (bcsTr : Spec.Transcript (hs.bcsSpec cd)) →
    (qd : OracleQueryDeco hs od cd (hs.bcsProjectShared cd bcsTr)) →
    OracleResponseDeco hs od cd (hs.bcsProjectShared cd bcsTr) qd → Type 1
  | .done, _, _, _, _, _ => PUnit
  | .branch _ rest, odRest, cdRest, ⟨x, tr⟩, qd, responses =>
      OpeningStatementDeco (rest x) (odRest x) (cdRest x) tr qd responses
  | .pass _ rest, ⟨oi, odRest⟩, ⟨some nc, cdRest⟩, ⟨_, tr⟩, ⟨qb, qdRest⟩,
      ⟨_, responsesRest⟩ =>
      ((i : Fin qb.numQueries) →
        nc.CommType × (q : oi.Query) × oi.Response q) ×
      OpeningStatementDeco rest odRest cdRest tr qdRest responsesRest
  | .pass _ rest, ⟨_, odRest⟩, ⟨none, cdRest⟩, ⟨_, tr⟩, qd, responses =>
      OpeningStatementDeco rest odRest cdRest tr qd responses

/-- Build the per-query commitment-opening statements from the BCS transcript,
query decoration, and claimed responses. -/
def openingStatements {m : Type → Type} :
    (hs : HybridSpec) → (od : OracleDeco hs) → (cd : CommitDeco m hs) →
    (bcsTr : Spec.Transcript (hs.bcsSpec cd)) →
    (qd : OracleQueryDeco hs od cd (hs.bcsProjectShared cd bcsTr)) →
    (responses : OracleResponseDeco hs od cd (hs.bcsProjectShared cd bcsTr) qd) →
    OpeningStatementDeco hs od cd bcsTr qd responses
  | .done, _, _, _, _, _ => ⟨⟩
  | .branch _ rest, odRest, cdRest, ⟨x, tr⟩, qd, responses =>
      openingStatements (rest x) (odRest x) (cdRest x) tr qd responses
  | .pass _ rest, ⟨_, odRest⟩, ⟨some _, cdRest⟩, ⟨cm, tr⟩, ⟨qb, qdRest⟩,
      ⟨responses, responsesRest⟩ =>
      (fun i => ⟨cm, qb.queries i, responses i⟩,
       openingStatements rest odRest cdRest tr qdRest responsesRest)
  | .pass _ rest, ⟨_, odRest⟩, ⟨none, cdRest⟩, ⟨_, tr⟩, qd, responses =>
      openingStatements rest odRest cdRest tr qd responses

/-- Witnesses for every commitment-opening subproof requested in Phase 2.
At a committed node, the same retained commitment witness is used for each
query against that committed oracle message. -/
def OpeningWitnessDeco {m : Type → Type} :
    (hs : HybridSpec) → (od : OracleDeco hs) → (cd : CommitDeco m hs) →
    (st : SharedTranscript hs cd) →
    OracleQueryDeco hs od cd st → Type 1
  | .done, _, _, _, _ => PUnit
  | .branch _ rest, odRest, cdRest, ⟨x, st⟩, qd =>
      OpeningWitnessDeco (rest x) (odRest x) (cdRest x) st qd
  | .pass _ rest, ⟨_, odRest⟩, ⟨some nc, cdRest⟩, st, ⟨qb, qdRest⟩ =>
      ((i : Fin qb.numQueries) → nc.WitnessType) ×
      OpeningWitnessDeco rest odRest cdRest st qdRest
  | .pass _ rest, ⟨_, odRest⟩, ⟨none, cdRest⟩, ⟨_, st⟩, qd =>
      OpeningWitnessDeco rest odRest cdRest st qd

/-- Extract the per-query commitment-opening witnesses from the Phase 1 oracle
witness retained by the honest prover. -/
def openingWitnessesFromOracleWitness {m : Type → Type} :
    (hs : HybridSpec) → (od : OracleDeco hs) → (cd : CommitDeco m hs) →
    (st : SharedTranscript hs cd) →
    (qd : OracleQueryDeco hs od cd st) → OracleWitness hs cd st →
    OpeningWitnessDeco hs od cd st qd
  | .done, _, _, _, _, _ => ⟨⟩
  | .branch _ rest, odRest, cdRest, ⟨x, st⟩, qd, wit =>
      openingWitnessesFromOracleWitness (rest x) (odRest x) (cdRest x) st qd wit
  | .pass _ rest, ⟨_, odRest⟩, ⟨some _, cdRest⟩, st, ⟨_, qdRest⟩,
      ⟨_, cwit, witRest⟩ =>
      (fun _ => cwit,
       openingWitnessesFromOracleWitness rest odRest cdRest st qdRest witRest)
  | .pass _ rest, ⟨_, odRest⟩, ⟨none, cdRest⟩, ⟨_, st⟩, qd, wit =>
      openingWitnessesFromOracleWitness rest odRest cdRest st qd wit

/-- Per-query opening prover strategies induced by `OpeningDeco`.

This is the executable prover-side bridge from the retained BCS opening
witnesses to the concrete `Commitment.Interaction.Opening.proof` objects. -/
def OpeningProverDeco {m : Type → Type} :
    (hs : HybridSpec) → (od : OracleDeco hs) → (cd : CommitDeco m hs) →
    (opDeco : OpeningDeco m hs od cd) →
    (bcsTr : Spec.Transcript (hs.bcsSpec cd)) →
    (qd : OracleQueryDeco hs od cd (hs.bcsProjectShared cd bcsTr)) →
    (responses : OracleResponseDeco hs od cd (hs.bcsProjectShared cd bcsTr) qd) →
    OpeningWitnessDeco hs od cd (hs.bcsProjectShared cd bcsTr) qd → Type 1
  | .done, _, _, _, _, _, _, _ => PUnit
  | .branch _ rest, odRest, cdRest, opRest, ⟨x, tr⟩, qd, responses, wits =>
      OpeningProverDeco (rest x) (odRest x) (cdRest x) (opRest x) tr qd responses wits
  | .pass _ rest, ⟨_, odRest⟩, ⟨some _, cdRest⟩, ⟨opening, opRest⟩,
      ⟨_, tr⟩, ⟨qb, qdRest⟩, ⟨_, responsesRest⟩, ⟨_, witsRest⟩ =>
      ((i : Fin qb.numQueries) →
        m (Spec.Strategy.withRoles m opening.spec opening.roles
          (fun _ => HonestProverOutput Bool PUnit))) ×
      OpeningProverDeco rest odRest cdRest opRest tr qdRest responsesRest witsRest
  | .pass _ rest, ⟨_, odRest⟩, ⟨none, cdRest⟩, opRest, ⟨_, tr⟩, qd, responses, wits =>
      OpeningProverDeco rest odRest cdRest opRest tr qd responses wits

/-- Instantiate the per-query opening prover strategies from `OpeningDeco`. -/
def openingProvers {m : Type → Type} :
    (hs : HybridSpec) → (od : OracleDeco hs) → (cd : CommitDeco m hs) →
    (opDeco : OpeningDeco m hs od cd) →
    (bcsTr : Spec.Transcript (hs.bcsSpec cd)) →
    (qd : OracleQueryDeco hs od cd (hs.bcsProjectShared cd bcsTr)) →
    (responses : OracleResponseDeco hs od cd (hs.bcsProjectShared cd bcsTr) qd) →
    (wits : OpeningWitnessDeco hs od cd (hs.bcsProjectShared cd bcsTr) qd) →
    OpeningProverDeco hs od cd opDeco bcsTr qd responses wits
  | .done, _, _, _, _, _, _, _ => ⟨⟩
  | .branch _ rest, odRest, cdRest, opRest, ⟨x, tr⟩, qd, responses, wits =>
      openingProvers (rest x) (odRest x) (cdRest x) (opRest x) tr qd responses wits
  | .pass _ rest, ⟨_, odRest⟩, ⟨some _, cdRest⟩, ⟨opening, opRest⟩,
      ⟨cm, tr⟩, ⟨qb, qdRest⟩, ⟨responses, responsesRest⟩, ⟨wits, witsRest⟩ =>
      (fun i => opening.proof.prover () ⟨cm, qb.queries i, responses i⟩ (wits i),
       openingProvers rest odRest cdRest opRest tr qdRest responsesRest witsRest)
  | .pass _ rest, ⟨_, odRest⟩, ⟨none, cdRest⟩, opRest, ⟨_, tr⟩, qd, responses, wits =>
      openingProvers rest odRest cdRest opRest tr qd responses wits

/-- Per-query opening verifier counterparts induced by `OpeningDeco`. -/
def OpeningVerifierDeco {m : Type → Type} :
    (hs : HybridSpec) → (od : OracleDeco hs) → (cd : CommitDeco m hs) →
    (opDeco : OpeningDeco m hs od cd) →
    (bcsTr : Spec.Transcript (hs.bcsSpec cd)) →
    (qd : OracleQueryDeco hs od cd (hs.bcsProjectShared cd bcsTr)) →
    OracleResponseDeco hs od cd (hs.bcsProjectShared cd bcsTr) qd → Type 1
  | .done, _, _, _, _, _, _ => PUnit
  | .branch _ rest, odRest, cdRest, opRest, ⟨x, tr⟩, qd, responses =>
      OpeningVerifierDeco (rest x) (odRest x) (cdRest x) (opRest x) tr qd responses
  | .pass _ rest, ⟨_, odRest⟩, ⟨some _, cdRest⟩, ⟨opening, opRest⟩,
      ⟨_, tr⟩, ⟨qb, qdRest⟩, ⟨_, responsesRest⟩ =>
      ((i : Fin qb.numQueries) →
        Spec.Counterpart m opening.spec opening.roles (fun _ => Bool)) ×
      OpeningVerifierDeco rest odRest cdRest opRest tr qdRest responsesRest
  | .pass _ rest, ⟨_, odRest⟩, ⟨none, cdRest⟩, opRest, ⟨_, tr⟩, qd, responses =>
      OpeningVerifierDeco rest odRest cdRest opRest tr qd responses

/-- Instantiate the per-query opening verifier counterparts from
`OpeningDeco` and the claimed query responses. -/
def openingVerifiers {m : Type → Type} :
    (hs : HybridSpec) → (od : OracleDeco hs) → (cd : CommitDeco m hs) →
    (opDeco : OpeningDeco m hs od cd) →
    (bcsTr : Spec.Transcript (hs.bcsSpec cd)) →
    (qd : OracleQueryDeco hs od cd (hs.bcsProjectShared cd bcsTr)) →
    (responses : OracleResponseDeco hs od cd (hs.bcsProjectShared cd bcsTr) qd) →
    OpeningVerifierDeco hs od cd opDeco bcsTr qd responses
  | .done, _, _, _, _, _, _ => ⟨⟩
  | .branch _ rest, odRest, cdRest, opRest, ⟨x, tr⟩, qd, responses =>
      openingVerifiers (rest x) (odRest x) (cdRest x) (opRest x) tr qd responses
  | .pass _ rest, ⟨_, odRest⟩, ⟨some _, cdRest⟩, ⟨opening, opRest⟩,
      ⟨cm, tr⟩, ⟨qb, qdRest⟩, ⟨responses, responsesRest⟩ =>
      (fun i => opening.proof.verifier () ⟨cm, qb.queries i, responses i⟩,
       openingVerifiers rest odRest cdRest opRest tr qdRest responsesRest)
  | .pass _ rest, ⟨_, odRest⟩, ⟨none, cdRest⟩, opRest, ⟨_, tr⟩, qd, responses =>
      openingVerifiers rest odRest cdRest opRest tr qd responses

/-! ### Composed opening-proof transcript shape -/

/-- Repeat an interaction spec `n` times sequentially. -/
def repeatSpec : Nat → Spec.{0} → Spec.{0}
  | 0, _ => .done
  | n + 1, spec => spec.append (fun _ => repeatSpec n spec)

/-- Roles for `repeatSpec`, obtained by repeating the same role decoration. -/
def repeatRoles :
    (n : Nat) → (spec : Spec.{0}) → RoleDecoration spec →
    RoleDecoration (repeatSpec n spec)
  | 0, _, _ => ⟨⟩
  | n + 1, spec, roles => roles.append (fun _ => repeatRoles n spec roles)

/-- The composed interaction tree containing every commitment-opening proof
requested by a Phase 2 query decoration, excluding the initial response
message. At each committed node, the opening proof protocol is repeated once
per query in the corresponding `QueryBundle`; the rest of the BCS tree is then
processed sequentially. -/
def openingProofSpec {m : Type → Type} :
    (hs : HybridSpec) → (od : OracleDeco hs) → (cd : CommitDeco m hs) →
    OpeningDeco m hs od cd →
    (bcsTr : Spec.Transcript (hs.bcsSpec cd)) →
    OracleQueryDeco hs od cd (hs.bcsProjectShared cd bcsTr) → Spec.{0}
  | .done, _, _, _, _, _ => .done
  | .branch _ rest, odRest, cdRest, opRest, ⟨x, tr⟩, qd =>
      openingProofSpec (rest x) (odRest x) (cdRest x) (opRest x) tr qd
  | .pass _ rest, ⟨_, odRest⟩, ⟨some _, cdRest⟩, ⟨opening, opRest⟩,
      ⟨_, tr⟩, ⟨qb, qdRest⟩ =>
      (repeatSpec qb.numQueries opening.spec).append
        (fun _ => openingProofSpec rest odRest cdRest opRest tr qdRest)
  | .pass _ rest, ⟨_, odRest⟩, ⟨none, cdRest⟩, opRest, ⟨_, tr⟩, qd =>
      openingProofSpec rest odRest cdRest opRest tr qd

/-- Roles for `openingProofSpec`. -/
def openingProofRoles {m : Type → Type} :
    (hs : HybridSpec) → (od : OracleDeco hs) → (cd : CommitDeco m hs) →
    (opDeco : OpeningDeco m hs od cd) →
    (bcsTr : Spec.Transcript (hs.bcsSpec cd)) →
    (qd : OracleQueryDeco hs od cd (hs.bcsProjectShared cd bcsTr)) →
    RoleDecoration (openingProofSpec hs od cd opDeco bcsTr qd)
  | .done, _, _, _, _, _ => ⟨⟩
  | .branch _ rest, odRest, cdRest, opRest, ⟨x, tr⟩, qd =>
      openingProofRoles (rest x) (odRest x) (cdRest x) (opRest x) tr qd
  | .pass _ rest, ⟨_, odRest⟩, ⟨some _, cdRest⟩, ⟨opening, opRest⟩,
      ⟨_, tr⟩, ⟨qb, qdRest⟩ =>
      (repeatRoles qb.numQueries opening.spec opening.roles).append
        (fun _ => openingProofRoles rest odRest cdRest opRest tr qdRest)
  | .pass _ rest, ⟨_, odRest⟩, ⟨none, cdRest⟩, opRest, ⟨_, tr⟩, qd =>
      openingProofRoles rest odRest cdRest opRest tr qd

/-- Full Phase 2 target shape: first send all claimed responses, then run the
composed opening subproof protocols determined by the actual BCS transcript.

This is separate from the one-message compatibility `openingSpec` scaffold so
callers can migrate deliberately. -/
def fullOpeningSpec {m : Type → Type}
    (hs : HybridSpec) (od : OracleDeco hs) (cd : CommitDeco m hs)
    (opDeco : OpeningDeco m hs od cd)
    (bcsTr : Spec.Transcript (hs.bcsSpec cd))
    (qd : OracleQueryDeco hs od cd (hs.bcsProjectShared cd bcsTr)) :
    Spec.{0} :=
  .node (OracleResponseDeco hs od cd (hs.bcsProjectShared cd bcsTr) qd)
    (fun _ => openingProofSpec hs od cd opDeco bcsTr qd)

/-- Roles for `fullOpeningSpec`: the prover first sends responses, then the
roles are those of the composed opening subproofs. -/
def fullOpeningRoles {m : Type → Type}
    (hs : HybridSpec) (od : OracleDeco hs) (cd : CommitDeco m hs)
    (opDeco : OpeningDeco m hs od cd)
    (bcsTr : Spec.Transcript (hs.bcsSpec cd))
    (qd : OracleQueryDeco hs od cd (hs.bcsProjectShared cd bcsTr)) :
    RoleDecoration (fullOpeningSpec hs od cd opDeco bcsTr qd) :=
  ⟨.sender, fun _ => openingProofRoles hs od cd opDeco bcsTr qd⟩

/-! ### Full opening-proof prover/verifier assembly -/

/-- Compose a finite family of prover strategies for repeated copies of the
same spec, ignoring each subproof's local output. -/
def repeatProverStrategies {m : Type → Type} [Monad m] :
    (n : Nat) → (spec : Spec.{0}) → (roles : RoleDecoration spec) →
    (Fin n → m (Spec.Strategy.withRoles m spec roles
      (fun _ => HonestProverOutput Bool PUnit))) →
    m (Spec.Strategy.withRoles m (repeatSpec n spec) (repeatRoles n spec roles)
      (fun _ => PUnit))
  | 0, _, _, _ => pure ⟨⟩
  | n + 1, spec, roles, provers => do
      let first ← provers ⟨0, Nat.succ_pos n⟩
      let firstUnit :=
        Spec.Strategy.mapOutputWithRoles (fun _ _ => PUnit.unit) first
      Spec.Strategy.compWithRolesFlat
        (s₂ := fun _ => repeatSpec n spec)
        (r₂ := fun _ => repeatRoles n spec roles)
        (Output := fun _ => PUnit)
        firstUnit
        (fun _ _ => repeatProverStrategies n spec roles (fun i => provers i.succ))

/-- Compose a finite family of verifier counterparts for repeated copies of
the same spec, ignoring each subproof's local verifier output. -/
def repeatVerifierCounterparts {m : Type → Type} [Monad m] :
    (n : Nat) → (spec : Spec.{0}) → (roles : RoleDecoration spec) →
    (Fin n → Spec.Counterpart m spec roles (fun _ => Bool)) →
    Spec.Counterpart m (repeatSpec n spec) (repeatRoles n spec roles)
      (fun _ => PUnit)
  | 0, _, _, _ => ⟨⟩
  | n + 1, spec, roles, verifiers =>
      let firstUnit :=
        Spec.Counterpart.mapOutput (fun _ _ => PUnit.unit)
          (verifiers ⟨0, Nat.succ_pos n⟩)
      Spec.Counterpart.appendFlat
        (s₂ := fun _ => repeatSpec n spec)
        (r₂ := fun _ => repeatRoles n spec roles)
        (Output₂ := fun _ => PUnit)
        firstUnit
        (fun _ _ => repeatVerifierCounterparts n spec roles (fun i => verifiers i.succ))

/-- Compose a finite family of verifier counterparts for repeated copies of
the same spec, conjoining their local Bool outputs. -/
def repeatVerifierCounterpartsAll {m : Type → Type} [Monad m] :
    (n : Nat) → (spec : Spec.{0}) → (roles : RoleDecoration spec) →
    (Fin n → Spec.Counterpart m spec roles (fun _ => Bool)) →
    Spec.Counterpart m (repeatSpec n spec) (repeatRoles n spec roles)
      (fun _ => Bool)
  | 0, _, _, _ => true
  | n + 1, spec, roles, verifiers =>
      Spec.Counterpart.appendFlat
        (s₂ := fun _ => repeatSpec n spec)
        (r₂ := fun _ => repeatRoles n spec roles)
        (Output₂ := fun _ => Bool)
        (verifiers ⟨0, Nat.succ_pos n⟩)
        (fun _ accepted =>
          Spec.Counterpart.mapOutput (fun _ restAccepted => accepted && restAccepted)
            (repeatVerifierCounterpartsAll n spec roles (fun i => verifiers i.succ)))

/-- Assemble the prover strategy for all opening subproofs after the response
message has already fixed the claimed responses. -/
def openingProofProver {m : Type → Type} [Monad m] :
    (hs : HybridSpec) → (od : OracleDeco hs) → (cd : CommitDeco m hs) →
    (opDeco : OpeningDeco m hs od cd) →
    (bcsTr : Spec.Transcript (hs.bcsSpec cd)) →
    (qd : OracleQueryDeco hs od cd (hs.bcsProjectShared cd bcsTr)) →
    (responses : OracleResponseDeco hs od cd (hs.bcsProjectShared cd bcsTr) qd) →
    (wits : OpeningWitnessDeco hs od cd (hs.bcsProjectShared cd bcsTr) qd) →
    m (Spec.Strategy.withRoles m (openingProofSpec hs od cd opDeco bcsTr qd)
      (openingProofRoles hs od cd opDeco bcsTr qd) (fun _ => PUnit))
  | .done, _, _, _, _, _, _, _ => pure ⟨⟩
  | .branch _ rest, odRest, cdRest, opRest, ⟨x, tr⟩, qd, responses, wits =>
      openingProofProver (rest x) (odRest x) (cdRest x) (opRest x) tr qd responses wits
  | .pass _ rest, ⟨_, odRest⟩, ⟨some _, cdRest⟩, ⟨opening, opRest⟩,
      ⟨cm, tr⟩, ⟨qb, qdRest⟩, ⟨responses, responsesRest⟩, ⟨wits, witsRest⟩ => do
      let pref ← repeatProverStrategies qb.numQueries opening.spec opening.roles
        (fun i => opening.proof.prover () ⟨cm, qb.queries i, responses i⟩ (wits i))
      Spec.Strategy.compWithRolesFlat
        (s₂ := fun _ => openingProofSpec rest odRest cdRest opRest tr qdRest)
        (r₂ := fun _ => openingProofRoles rest odRest cdRest opRest tr qdRest)
        (Output := fun _ => PUnit)
        pref
        (fun _ _ => openingProofProver rest odRest cdRest opRest tr qdRest responsesRest witsRest)
  | .pass _ rest, ⟨_, odRest⟩, ⟨none, cdRest⟩, opRest, ⟨_, tr⟩, qd, responses, wits =>
      openingProofProver rest odRest cdRest opRest tr qd responses wits

/-- Assemble the verifier counterpart for all opening subproofs after the
response message has already fixed the claimed responses. -/
def openingProofVerifier {m : Type → Type} [Monad m] :
    (hs : HybridSpec) → (od : OracleDeco hs) → (cd : CommitDeco m hs) →
    (opDeco : OpeningDeco m hs od cd) →
    (bcsTr : Spec.Transcript (hs.bcsSpec cd)) →
    (qd : OracleQueryDeco hs od cd (hs.bcsProjectShared cd bcsTr)) →
    (responses : OracleResponseDeco hs od cd (hs.bcsProjectShared cd bcsTr) qd) →
    Spec.Counterpart m (openingProofSpec hs od cd opDeco bcsTr qd)
      (openingProofRoles hs od cd opDeco bcsTr qd) (fun _ => PUnit)
  | .done, _, _, _, _, _, _ => ⟨⟩
  | .branch _ rest, odRest, cdRest, opRest, ⟨x, tr⟩, qd, responses =>
      openingProofVerifier (rest x) (odRest x) (cdRest x) (opRest x) tr qd responses
  | .pass _ rest, ⟨_, odRest⟩, ⟨some _, cdRest⟩, ⟨opening, opRest⟩,
      ⟨cm, tr⟩, ⟨qb, qdRest⟩, ⟨responses, responsesRest⟩ =>
      let pref := repeatVerifierCounterparts qb.numQueries opening.spec opening.roles
        (fun i => opening.proof.verifier () ⟨cm, qb.queries i, responses i⟩)
      Spec.Counterpart.appendFlat
        (s₂ := fun _ => openingProofSpec rest odRest cdRest opRest tr qdRest)
        (r₂ := fun _ => openingProofRoles rest odRest cdRest opRest tr qdRest)
        (Output₂ := fun _ => PUnit)
        pref
        (fun _ _ => openingProofVerifier rest odRest cdRest opRest tr qdRest responsesRest)
  | .pass _ rest, ⟨_, odRest⟩, ⟨none, cdRest⟩, opRest, ⟨_, tr⟩, qd, responses =>
      openingProofVerifier rest odRest cdRest opRest tr qd responses

/-- Assemble the verifier counterpart for all opening subproofs and conjoin
their local Bool outputs. -/
def openingProofVerifierAll {m : Type → Type} [Monad m] :
    (hs : HybridSpec) → (od : OracleDeco hs) → (cd : CommitDeco m hs) →
    (opDeco : OpeningDeco m hs od cd) →
    (bcsTr : Spec.Transcript (hs.bcsSpec cd)) →
    (qd : OracleQueryDeco hs od cd (hs.bcsProjectShared cd bcsTr)) →
    (responses : OracleResponseDeco hs od cd (hs.bcsProjectShared cd bcsTr) qd) →
    Spec.Counterpart m (openingProofSpec hs od cd opDeco bcsTr qd)
      (openingProofRoles hs od cd opDeco bcsTr qd) (fun _ => Bool)
  | .done, _, _, _, _, _, _ => true
  | .branch _ rest, odRest, cdRest, opRest, ⟨x, tr⟩, qd, responses =>
      openingProofVerifierAll (rest x) (odRest x) (cdRest x) (opRest x) tr qd responses
  | .pass _ rest, ⟨_, odRest⟩, ⟨some _, cdRest⟩, ⟨opening, opRest⟩,
      ⟨cm, tr⟩, ⟨qb, qdRest⟩, ⟨responses, responsesRest⟩ =>
      let pref := repeatVerifierCounterpartsAll qb.numQueries opening.spec opening.roles
        (fun i => opening.proof.verifier () ⟨cm, qb.queries i, responses i⟩)
      Spec.Counterpart.appendFlat
        (s₂ := fun _ => openingProofSpec rest odRest cdRest opRest tr qdRest)
        (r₂ := fun _ => openingProofRoles rest odRest cdRest opRest tr qdRest)
        (Output₂ := fun _ => Bool)
        pref
        (fun _ accepted =>
          Spec.Counterpart.mapOutput (fun _ restAccepted => accepted && restAccepted)
            (openingProofVerifierAll rest odRest cdRest opRest tr qdRest responsesRest))
  | .pass _ rest, ⟨_, odRest⟩, ⟨none, cdRest⟩, opRest, ⟨_, tr⟩, qd, responses =>
      openingProofVerifierAll rest odRest cdRest opRest tr qd responses

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
  .node (OracleResponseDeco hs od cd st qd) (fun _ => .done)

/-- Roles for the opening protocol spec. -/
def openingRoles {m : Type → Type}
    (hs : HybridSpec) (od : OracleDeco hs) (cd : CommitDeco m hs)
    (opDeco : OpeningDeco m hs od cd)
    (st : SharedTranscript hs cd) (qd : OracleQueryDeco hs od cd st) :
    RoleDecoration (openingSpec hs od cd opDeco st qd) :=
  ⟨.sender, fun _ => ⟨⟩⟩

/-- Answer committed oracle queries from the Phase 1 witness retained by the
honest prover. This is the executable payload carried by the minimal Phase 2
opening interaction below. -/
def answerCommittedQueriesFromWitness {m : Type → Type} :
    (hs : HybridSpec) → (od : OracleDeco hs) → (cd : CommitDeco m hs) →
    (st : SharedTranscript hs cd) →
    (qd : OracleQueryDeco hs od cd st) → OracleWitness hs cd st →
    OracleResponseDeco hs od cd st qd
  | .done, _, _, _, _, _ => ⟨⟩
  | .branch _ rest, odRest, cdRest, ⟨x, st⟩, qd, wit =>
      answerCommittedQueriesFromWitness (rest x) (odRest x) (cdRest x) st qd wit
  | .pass _ rest, ⟨_, odRest⟩, ⟨some _, cdRest⟩, st, ⟨qb, qdRest⟩, ⟨x, _, witRest⟩ =>
      (fun i => OracleInterface.answer x (qb.queries i),
       answerCommittedQueriesFromWitness rest odRest cdRest st qdRest witRest)
  | .pass _ rest, ⟨_, odRest⟩, ⟨none, cdRest⟩, ⟨_, st⟩, qd, wit =>
      answerCommittedQueriesFromWitness rest odRest cdRest st qd wit

/-- Full Phase 2 prover: send committed-oracle query responses, then run every
requested commitment-opening subproof. -/
def fullBcsPhase2Prover
    (hs : HybridSpec) (od : OracleDeco hs) (cd : CommitDeco (OracleComp oSpec) hs)
    (opDeco : OpeningDeco (OracleComp oSpec) hs od cd)
    (bcsTr : Spec.Transcript (hs.bcsSpec cd))
    (qd : OracleQueryDeco hs od cd (hs.bcsProjectShared cd bcsTr))
    (wit : OracleWitness hs cd (hs.bcsProjectShared cd bcsTr)) :
    OracleComp oSpec (Spec.Strategy.withRoles (OracleComp oSpec)
      (fullOpeningSpec hs od cd opDeco bcsTr qd)
      (fullOpeningRoles hs od cd opDeco bcsTr qd)
      (fun _ => OracleResponseDeco hs od cd (hs.bcsProjectShared cd bcsTr) qd)) := do
  let responses := answerCommittedQueriesFromWitness hs od cd (hs.bcsProjectShared cd bcsTr) qd wit
  let wits := openingWitnessesFromOracleWitness hs od cd (hs.bcsProjectShared cd bcsTr) qd wit
  let proofStrategy ← openingProofProver hs od cd opDeco bcsTr qd responses wits
  pure (pure ⟨responses,
    Spec.Strategy.mapOutputWithRoles (fun _ _ => responses) proofStrategy⟩)

/-- Full Phase 2 verifier: receive committed-oracle query responses, then run
every requested commitment-opening verifier and return the received responses
if all subprotocols complete. Individual opening proof outputs are currently
discarded by the transcript assembly layer; this definition wires the concrete
verifiers into the full Phase 2 interaction shape. -/
def fullBcsPhase2Verifier
    (hs : HybridSpec) (od : OracleDeco hs) (cd : CommitDeco (OracleComp oSpec) hs)
    (opDeco : OpeningDeco (OracleComp oSpec) hs od cd)
    (bcsTr : Spec.Transcript (hs.bcsSpec cd))
    (qd : OracleQueryDeco hs od cd (hs.bcsProjectShared cd bcsTr)) :
    Spec.Counterpart (OracleComp oSpec)
      (fullOpeningSpec hs od cd opDeco bcsTr qd)
      (fullOpeningRoles hs od cd opDeco bcsTr qd)
      (fun _ => OracleResponseDeco hs od cd (hs.bcsProjectShared cd bcsTr) qd) :=
  fun responses => pure <|
    Spec.Counterpart.mapOutput (fun _ _ => responses)
      (openingProofVerifier hs od cd opDeco bcsTr qd responses)

/-- Checked full Phase 2 prover. The honest prover returns `some responses`
after sending the committed-oracle query responses and running every requested
opening subproof. -/
def checkedFullBcsPhase2Prover
    (hs : HybridSpec) (od : OracleDeco hs) (cd : CommitDeco (OracleComp oSpec) hs)
    (opDeco : OpeningDeco (OracleComp oSpec) hs od cd)
    (bcsTr : Spec.Transcript (hs.bcsSpec cd))
    (qd : OracleQueryDeco hs od cd (hs.bcsProjectShared cd bcsTr))
    (wit : OracleWitness hs cd (hs.bcsProjectShared cd bcsTr)) :
    OracleComp oSpec (Spec.Strategy.withRoles (OracleComp oSpec)
      (fullOpeningSpec hs od cd opDeco bcsTr qd)
      (fullOpeningRoles hs od cd opDeco bcsTr qd)
      (fun _ => Option (OracleResponseDeco hs od cd (hs.bcsProjectShared cd bcsTr) qd))) := do
  let responses := answerCommittedQueriesFromWitness hs od cd (hs.bcsProjectShared cd bcsTr) qd wit
  let wits := openingWitnessesFromOracleWitness hs od cd (hs.bcsProjectShared cd bcsTr) qd wit
  let proofStrategy ← openingProofProver hs od cd opDeco bcsTr qd responses wits
  pure (pure ⟨responses,
    Spec.Strategy.mapOutputWithRoles (fun _ _ => some responses) proofStrategy⟩)

/-- Checked full Phase 2 verifier. It returns `some responses` exactly when all
opening subproof verifier outputs are `true`, and `none` otherwise. -/
def checkedFullBcsPhase2Verifier
    (hs : HybridSpec) (od : OracleDeco hs) (cd : CommitDeco (OracleComp oSpec) hs)
    (opDeco : OpeningDeco (OracleComp oSpec) hs od cd)
    (bcsTr : Spec.Transcript (hs.bcsSpec cd))
    (qd : OracleQueryDeco hs od cd (hs.bcsProjectShared cd bcsTr)) :
    Spec.Counterpart (OracleComp oSpec)
      (fullOpeningSpec hs od cd opDeco bcsTr qd)
      (fullOpeningRoles hs od cd opDeco bcsTr qd)
      (fun _ => Option (OracleResponseDeco hs od cd (hs.bcsProjectShared cd bcsTr) qd)) :=
  fun responses => pure <|
    Spec.Counterpart.mapOutput
      (fun _ accepted => if accepted then some responses else none)
      (openingProofVerifierAll hs od cd opDeco bcsTr qd responses)

/-- Phase 2 prover for the current minimal executable scaffold.

It uses the retained `OracleWitness` to answer every committed-oracle query.
The companion definitions `openingStatements` and
`openingWitnessesFromOracleWitness` expose the per-query commitment-opening
bridge that a fully checking Phase 2 verifier must run. -/
def bcsPhase2Prover
    (hs : HybridSpec) (od : OracleDeco hs) (cd : CommitDeco (OracleComp oSpec) hs)
    (opDeco : OpeningDeco (OracleComp oSpec) hs od cd)
    (st : SharedTranscript hs cd) (qd : OracleQueryDeco hs od cd st)
    (_wit : OracleWitness hs cd st) :
    OracleComp oSpec (Spec.Strategy.withRoles (OracleComp oSpec)
      (openingSpec hs od cd opDeco st qd) (openingRoles hs od cd opDeco st qd)
      (fun _ => OracleResponseDeco hs od cd st qd)) :=
  let responses := answerCommittedQueriesFromWitness hs od cd st qd _wit
  pure (pure ⟨responses, responses⟩)

/-- Phase 2 verifier for the current minimal executable scaffold.

It receives the response decoration and returns it unchanged. Full
commitment-opening verification should be implemented by threading a BCS
transcript through this phase and running the per-query statements produced by
`openingStatements` against the `OpeningDeco` proofs. -/
def bcsPhase2Verifier
    (hs : HybridSpec) (od : OracleDeco hs) (cd : CommitDeco (OracleComp oSpec) hs)
    (opDeco : OpeningDeco (OracleComp oSpec) hs od cd)
    (st : SharedTranscript hs cd) (qd : OracleQueryDeco hs od cd st) :
    Spec.Counterpart (OracleComp oSpec)
      (openingSpec hs od cd opDeco st qd) (openingRoles hs od cd opDeco st qd)
      (fun _ => OracleResponseDeco hs od cd st qd) :=
  fun responses => pure responses

end Phase2

end HybridSpec

end Interaction
